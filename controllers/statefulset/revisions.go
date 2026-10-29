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
	"k8s.io/apimachinery/pkg/runtime"
	"k8s.io/apimachinery/pkg/util/strategicpatch"
	utilfeature "k8s.io/apiserver/pkg/util/feature"
	"k8s.io/client-go/kubernetes/scheme"
	"k8s.io/kubernetes/pkg/api/legacyscheme"
	"k8s.io/kubernetes/pkg/controller/history"
	"k8s.io/kubernetes/pkg/features"
)

// These helpers correspond to the vendored stateful_set_utils.go and
// stateful_set_control.go. Serialization, patching, defaulting and hashing use
// the same upstream libraries. New snapshots are encoded as Raw bytes.
func getPatch(set *apps.StatefulSet) ([]byte, error) {
	data, err := runtime.Encode(scheme.Codecs.LegacyCodec(apps.SchemeGroupVersion), set)
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
	data, err := runtime.Encode(scheme.Codecs.LegacyCodec(apps.SchemeGroupVersion), set)
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
	return revision.Namespace == set.Namespace && owner != nil && owner.UID == set.UID
}

func listRevisions(set *apps.StatefulSet) ([]*apps.ControllerRevision, error) {
	selector, err := metav1.LabelSelectorAsSelector(set.Spec.Selector)
	if err != nil {
		return nil, err
	}
	all, err := apimodel.ModelState.ControllerRevisionList(set.Namespace, selector)
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

// Follow upstream semantic comparison without its optional equality cache.
// Default the restored template before comparing it with the proposed patch.
func setMatchesLatestExistingRevision(set *apps.StatefulSet, proposed, latest *apps.ControllerRevision) bool {
	if !utilfeature.DefaultFeatureGate.Enabled(features.StatefulSetSemanticRevisionComparison) {
		return false
	}
	restored, err := applyRevision(set, latest)
	if err != nil {
		return false
	}
	legacyscheme.Scheme.Default(restored)
	reconstructed, err := newRevision(restored, -1, nil)
	return err == nil && history.EqualRevision(proposed, reconstructed)
}

func createRevision(set *apps.StatefulSet, revision *apps.ControllerRevision, collisionCount *int32) (*apps.ControllerRevision, error) {
	if collisionCount == nil {
		return nil, fmt.Errorf("collisionCount should not be nil")
	}
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
		// Match upstream: equal Raw payloads can be reused without changing ownership.
		if bytes.Equal(exists.Data.Raw, clone.Data.Raw) {
			return exists, nil
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

func newVersionedStatefulSetPod(set *apps.StatefulSet, revision string, ordinal int) (*v1.Pod, error) {
	pod, err := newStatefulSetPod(set, ordinal)
	if err != nil {
		return nil, err
	}
	setPodRevision(pod, revision)
	return pod, nil
}

// Maintain only revision bookkeeping; leave other StatefulSet status fields
// unchanged. Completion here means every desired Pod carries the update label.
func updateRevisionStatus(set *apps.StatefulSet, pods []*v1.Pod, current, update *apps.ControllerRevision, collisionCount int32) error {
	currentRevision := current.Name
	complete := true
	for ordinal := 0; ordinal <= endOrdinalOf(set); ordinal++ {
		pod := findPodByOrdinal(set, pods, ordinal)
		if pod == nil || isTerminating(pod) || !podRevisionMatches(pod, update.Name) {
			complete = false
			break
		}
	}
	if complete {
		currentRevision = update.Name
	}
	if set.Status.CurrentRevision == currentRevision && set.Status.UpdateRevision == update.Name &&
		set.Status.CollisionCount != nil && *set.Status.CollisionCount == collisionCount {
		return nil
	}
	copy := set.DeepCopy()
	copy.Status.CurrentRevision = currentRevision
	copy.Status.UpdateRevision = update.Name
	copy.Status.CollisionCount = &collisionCount
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
	if limit < 0 {
		return nil
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
