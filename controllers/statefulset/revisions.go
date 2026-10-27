package statefulset

import (
	"bytes"
	"encoding/json"
	"fmt"
	"kubernetes_model/apimodel"

	apps "k8s.io/api/apps/v1"
	v1 "k8s.io/api/core/v1"
	apierrors "k8s.io/apimachinery/pkg/api/errors"
	metav1 "k8s.io/apimachinery/pkg/apis/meta/v1"
	"k8s.io/apimachinery/pkg/labels"
	"k8s.io/apimachinery/pkg/runtime"
	"k8s.io/apimachinery/pkg/util/strategicpatch"
	"k8s.io/client-go/kubernetes/scheme"
	"k8s.io/kubernetes/pkg/api/legacyscheme"
	podutil "k8s.io/kubernetes/pkg/api/v1/pod"
	"k8s.io/kubernetes/pkg/controller/history"
)

// These helpers correspond to the vendored stateful_set_utils.go and
// stateful_set_control.go. Serialization, patching, defaulting and hashing use
// the same upstream libraries. History uses Raw bytes and never Object.
var patchCodec = scheme.Codecs.LegacyCodec(apps.SchemeGroupVersion)

func getPatch(set *apps.StatefulSet) ([]byte, error) {
	data, err := runtime.Encode(patchCodec, set)
	if err != nil {
		return nil, err
	}
	var raw map[string]interface{}
	if err := json.Unmarshal(data, &raw); err != nil {
		return nil, err
	}
	spec, ok := raw["spec"].(map[string]interface{})
	if !ok {
		return nil, fmt.Errorf("StatefulSet has no encoded spec")
	}
	template, ok := spec["template"].(map[string]interface{})
	if !ok {
		return nil, fmt.Errorf("StatefulSet has no encoded template")
	}
	template["$patch"] = "replace"
	return json.Marshal(map[string]interface{}{"spec": map[string]interface{}{"template": template}})
}

func newRevision(set *apps.StatefulSet, number int64, collisionCount *int32) (*apps.ControllerRevision, error) {
	patch, err := getPatch(set)
	if err != nil {
		return nil, err
	}
	revision, err := history.NewControllerRevision(set, apps.SchemeGroupVersion.WithKind("StatefulSet"), set.Spec.Template.Labels, runtime.RawExtension{Raw: patch}, number, collisionCount)
	if err != nil {
		return nil, err
	}
	revision.Annotations = map[string]string{}
	for key, value := range set.Annotations {
		revision.Annotations[key] = value
	}
	return revision, nil
}

func applyRevision(set *apps.StatefulSet, revision *apps.ControllerRevision) (*apps.StatefulSet, error) {
	if revision.Data.Object != nil {
		return nil, fmt.Errorf("ControllerRevision Object representation is unsupported; expected Raw bytes")
	}
	data, err := runtime.Encode(patchCodec, set)
	if err != nil {
		return nil, err
	}
	patched, err := strategicpatch.StrategicMergePatch(data, revision.Data.Raw, &apps.StatefulSet{})
	if err != nil {
		return nil, err
	}
	restored := &apps.StatefulSet{}
	if err := json.Unmarshal(patched, restored); err != nil {
		return nil, err
	}
	return restored, nil
}

func revisionOwnedBy(set *apps.StatefulSet, revision *apps.ControllerRevision) bool {
	owner := metav1.GetControllerOf(revision)
	return revision.Namespace == set.Namespace && owner != nil && owner.UID == set.UID && owner.Kind == "StatefulSet" && owner.APIVersion == apps.SchemeGroupVersion.String()
}

func listRevisions(set *apps.StatefulSet) ([]*apps.ControllerRevision, error) {
	all, err := apimodel.ModelState.ControllerRevisionList(set.Namespace, labels.Everything())
	if err != nil {
		return nil, err
	}
	revisions := []*apps.ControllerRevision{}
	for _, revision := range all {
		if revisionOwnedBy(set, revision) {
			revisions = append(revisions, revision)
		}
	}
	history.SortControllerRevisions(revisions)
	return revisions, nil
}

// Semantic revision comparison is enabled in the vendored default feature
// configuration. Default the restored template before comparing it with the
// proposed patch; the optional upstream LRU cache is omitted.
func setMatchesLatestExistingRevision(set *apps.StatefulSet, proposed, latest *apps.ControllerRevision) bool {
	restored, err := applyRevision(set, latest)
	if err != nil {
		return false
	}
	legacyscheme.Scheme.Default(restored)
	reconstructed, err := newRevision(restored, -1, nil)
	return err == nil && history.EqualRevision(proposed, reconstructed)
}

func createRevision(set *apps.StatefulSet, revision *apps.ControllerRevision, collisionCount *int32) (*apps.ControllerRevision, error) {
	clone := revision.DeepCopy()
	for {
		hash := history.HashControllerRevision(revision, collisionCount)
		clone.Name = history.ControllerRevisionName(set.Name, hash)
		created, err := apimodel.ModelState.ControllerRevisionCreate(set.Namespace, clone)
		if !apierrors.IsAlreadyExists(err) {
			return created, err
		}
		exists, err := apimodel.ModelState.ControllerRevisionGet(set.Namespace, clone.Name)
		if err != nil {
			return nil, err
		}
		// Ownership is checked as well as payload: a set recreated with the same
		// name must never reuse the old UID's history, even for an equal template.
		if revisionOwnedBy(set, exists) && exists.Data.Object == nil && bytes.Equal(exists.Data.Raw, clone.Data.Raw) {
			return exists, nil
		}
		if *collisionCount == int32(1<<31-1) {
			return nil, fmt.Errorf("ControllerRevision collision count exhausted")
		}
		*collisionCount++
	}
}

func getStatefulSetRevisions(set *apps.StatefulSet, revisions []*apps.ControllerRevision) (*apps.ControllerRevision, *apps.ControllerRevision, int32, error) {
	history.SortControllerRevisions(revisions)
	collisionCount := int32(0)
	if set.Status.CollisionCount != nil {
		collisionCount = *set.Status.CollisionCount
	}
	next := int64(1)
	if len(revisions) > 0 {
		if revisions[len(revisions)-1].Revision == int64(1<<63-1) {
			return nil, nil, collisionCount, fmt.Errorf("ControllerRevision number exhausted")
		}
		next = revisions[len(revisions)-1].Revision + 1
	}
	update, err := newRevision(set, next, &collisionCount)
	if err != nil {
		return nil, nil, collisionCount, err
	}
	equal := history.FindEqualRevisions(revisions, update)
	if len(equal) > 0 && history.EqualRevision(revisions[len(revisions)-1], equal[len(equal)-1]) {
		update = revisions[len(revisions)-1]
	} else if len(equal) > 0 {
		rollback := equal[len(equal)-1].DeepCopy()
		rollback.Revision = next
		// Optimistic RV validation rejects concurrent history edits. A later sync
		// relists and retries instead of writing a stale snapshot over them.
		update, err = apimodel.ModelState.ControllerRevisionUpdate(set.Namespace, rollback)
	} else if len(revisions) > 0 && setMatchesLatestExistingRevision(set, update, revisions[len(revisions)-1]) {
		update = revisions[len(revisions)-1]
	} else {
		update, err = createRevision(set, update, &collisionCount)
	}
	if err != nil {
		return nil, nil, collisionCount, err
	}
	current := update
	for _, revision := range revisions {
		if revision.Name == set.Status.CurrentRevision {
			current = revision
			break
		}
	}
	return current, update, collisionCount, nil
}

func setPodRevision(pod *v1.Pod, revision string) {
	if pod.Labels == nil {
		pod.Labels = map[string]string{}
	}
	pod.Labels[apps.StatefulSetRevisionLabel] = revision
}
func getPodRevision(pod *v1.Pod) string {
	return pod.Labels[apps.StatefulSetRevisionLabel]
}
func podRevisionMatches(pod *v1.Pod, revision string) bool {
	return getPodRevision(pod) == revision
}

func newVersionedStatefulSetPod(currentSet, updateSet *apps.StatefulSet, currentRevision, updateRevision string, ordinal int) (*v1.Pod, error) {
	selected := updateSet
	revision := updateRevision
	if currentSet.Spec.UpdateStrategy.Type == apps.RollingUpdateStatefulSetStrategyType &&
		((currentSet.Spec.UpdateStrategy.RollingUpdate == nil && ordinal < int(currentSet.Status.CurrentReplicas)) ||
			(currentSet.Spec.UpdateStrategy.RollingUpdate != nil && ordinal < partitionOf(currentSet))) {
		selected = currentSet
		revision = currentRevision
	}
	pod, err := newStatefulSetPod(selected, ordinal)
	if err != nil {
		return nil, err
	}
	setPodRevision(pod, revision)
	return pod, nil
}

func partitionOf(set *apps.StatefulSet) int {
	if set.Spec.UpdateStrategy.RollingUpdate != nil && set.Spec.UpdateStrategy.RollingUpdate.Partition != nil {
		return int(*set.Spec.UpdateStrategy.RollingUpdate.Partition)
	}
	return 0
}
func isRunningAndReady(pod *v1.Pod) bool {
	return pod.Status.Phase == v1.PodRunning && podutil.IsPodReady(pod)
}
func isAvailable(set *apps.StatefulSet, pod *v1.Pod) bool {
	return podutil.IsPodAvailable(pod, set.Spec.MinReadySeconds, metav1.Now()) && !isTerminating(pod)
}

func updateRevisionStatus(set *apps.StatefulSet, pods []*v1.Pod, current, update *apps.ControllerRevision, collisionCount int32) error {
	status := apps.StatefulSetStatus{
		ObservedGeneration: set.Generation, CurrentRevision: current.Name, UpdateRevision: update.Name, CollisionCount: &collisionCount,
	}
	for _, pod := range pods {
		if pod.Status.Phase != "" {
			status.Replicas++
		}
		if isRunningAndReady(pod) {
			status.ReadyReplicas++
		}
		if isRunningAndReady(pod) && podutil.IsPodAvailable(pod, set.Spec.MinReadySeconds, metav1.Now()) {
			status.AvailableReplicas++
		}
		if pod.Status.Phase != "" && !isTerminating(pod) {
			if getPodRevision(pod) == current.Name {
				status.CurrentReplicas++
			}
			if getPodRevision(pod) == update.Name {
				status.UpdatedReplicas++
			}
		}
	}
	if set.Spec.UpdateStrategy.Type == apps.RollingUpdateStatefulSetStrategyType &&
		int(status.UpdatedReplicas) == replicasOf(set) && int(status.ReadyReplicas) == replicasOf(set) && int(status.Replicas) == replicasOf(set) {
		status.CurrentReplicas = status.UpdatedReplicas
		status.CurrentRevision = status.UpdateRevision
	}
	// Compare represented fields explicitly; keep unrelated status conditions.
	status.Conditions = set.Status.Conditions
	if set.Status.ObservedGeneration == status.ObservedGeneration && set.Status.Replicas == status.Replicas &&
		set.Status.ReadyReplicas == status.ReadyReplicas && set.Status.AvailableReplicas == status.AvailableReplicas &&
		set.Status.CurrentReplicas == status.CurrentReplicas && set.Status.UpdatedReplicas == status.UpdatedReplicas &&
		set.Status.CurrentRevision == status.CurrentRevision && set.Status.UpdateRevision == status.UpdateRevision &&
		set.Status.CollisionCount != nil && *set.Status.CollisionCount == collisionCount {
		return nil
	}
	copy := set.DeepCopy()
	copy.Status = status
	_, err := apimodel.ModelState.StatefulSetUpdateStatus(set.Namespace, copy)
	return err
}

func truncateHistory(set *apps.StatefulSet, pods []*v1.Pod, revisions []*apps.ControllerRevision, current, update *apps.ControllerRevision) error {
	live := map[string]bool{current.Name: true, update.Name: true}
	for _, pod := range pods {
		live[getPodRevision(pod)] = true
	}
	old := []*apps.ControllerRevision{}
	for _, revision := range revisions {
		if !live[revision.Name] {
			old = append(old, revision)
		}
	}
	history.SortControllerRevisions(old)
	limit := 10
	if set.Spec.RevisionHistoryLimit != nil {
		limit = int(*set.Spec.RevisionHistoryLimit)
	}
	for i := 0; i < len(old)-limit; i++ {
		err := apimodel.ModelState.ControllerRevisionDelete(set.Namespace, old[i].Name, commonDeleteRevisionOptions(old[i]))
		if err != nil && !apierrors.IsNotFound(err) {
			return err
		}
	}
	return nil
}

func commonDeleteRevisionOptions(revision *apps.ControllerRevision) metav1.DeleteOptions {
	uid := revision.UID
	return metav1.DeleteOptions{Preconditions: &metav1.Preconditions{UID: &uid}}
}
