package statefulset

import (
	"controllers/common"
	"kubernetes_model/apimodel"
	"strconv"
	"strings"

	apps "k8s.io/api/apps/v1"
	v1 "k8s.io/api/core/v1"
	apierrors "k8s.io/apimachinery/pkg/api/errors"
	metav1 "k8s.io/apimachinery/pkg/apis/meta/v1"
	"k8s.io/kubernetes/pkg/controller"
)

// A simplified statefulset controller. The following features are not included:
// * adoption and general selector-based release
// * custom start ordinals, PodManagementPolicy, and UpdateStrategy policy details
// * general status accounting (only revision bookkeeping is maintained)
// * concurrent creation/deletion
// * PVC retention policy owner reference updates

func replicasOf(set *apps.StatefulSet) int {
	if set.Spec.Replicas == nil {
		return 1
	}
	return int(*set.Spec.Replicas)
}

func endOrdinalOf(set *apps.StatefulSet) int {
	return replicasOf(set) - 1
}

func podName(setName string, ordinal int) string {
	return setName + "-" + strconv.Itoa(ordinal)
}

func claimName(setName, claimTemplateName string, ordinal int) string {
	return claimTemplateName + "-" + setName + "-" + strconv.Itoa(ordinal)
}

func parentNameAndOrdinal(podName string) (string, int) {
	idx := strings.LastIndex(podName, "-")
	if idx < 0 {
		return "", -1
	}
	ordinal, err := strconv.ParseInt(podName[idx+1:], 10, 32)
	if err != nil {
		return "", -1
	}
	return podName[:idx], int(ordinal)
}

func ordinalOf(podName string) int {
	_, ordinal := parentNameAndOrdinal(podName)
	return ordinal
}

func isMemberOf(setName, name string) bool {
	parent, ordinal := parentNameAndOrdinal(name)
	// As upstream requires, reject noncanonical names such as "web-01".
	return parent == setName && ordinal >= 0 && name == podName(setName, ordinal)
}

func filterPodsForStatefulSet(set *apps.StatefulSet, pods []*v1.Pod) []*v1.Pod {
	result := []*v1.Pod{}
	for _, pod := range pods {
		if isMemberOf(set.Name, pod.Name) {
			result = append(result, pod)
		}
	}
	return result
}

func releasePod(set *apps.StatefulSet, pod *v1.Pod) error {
	updatedPod := pod.DeepCopy()
	ownerReferences := []metav1.OwnerReference{}
	released := false
	for _, ownerReference := range updatedPod.OwnerReferences {
		// Upstream releases a Pod with a strategic-merge deletion keyed by the
		// owner's UID, preserving owner references with other UIDs:
		// https://github.com/kubernetes/kubernetes/blob/release-1.34/pkg/controller/controller_ref_manager.go
		if ownerReference.UID == set.UID {
			released = true
			continue
		}
		ownerReferences = append(ownerReferences, ownerReference)
	}
	if !released {
		return nil
	}
	updatedPod.OwnerReferences = ownerReferences
	_, err := apimodel.ModelState.PodUpdateTx(updatedPod.Namespace, updatedPod)
	if apierrors.IsNotFound(err) {
		return nil
	}
	return err
}

func releasePodsWithBadNames(set *apps.StatefulSet, pods []*v1.Pod) error {
	for _, pod := range pods {
		if isMemberOf(set.Name, pod.Name) {
			continue
		}
		if err := releasePod(set, pod); err != nil {
			return err
		}
	}
	return nil
}

func podInOrdinalRange(set *apps.StatefulSet, podName string) bool {
	ordinal := ordinalOf(podName)
	return ordinal >= 0 && ordinal <= endOrdinalOf(set)
}

func isTerminating(pod *v1.Pod) bool {
	return pod.DeletionTimestamp != nil
}

// initIdentity initializes both the mutable and immutable parts of a
// StatefulSet Pod's identity. Kubernetes upstream deliberately sets Hostname
// and Subdomain only during initial Pod creation:
// https://github.com/kubernetes/kubernetes/blob/master/pkg/controller/statefulset/stateful_set_utils.go
func initIdentity(set *apps.StatefulSet, pod *v1.Pod) {
	updateIdentity(set, pod)
	pod.Spec.Hostname = pod.Name
	pod.Spec.Subdomain = set.Spec.ServiceName
}

func updateIdentity(set *apps.StatefulSet, pod *v1.Pod) {
	ordinal := ordinalOf(pod.Name)
	pod.Name = podName(set.Name, ordinal)
	pod.Namespace = set.Namespace
	if pod.Labels == nil {
		pod.Labels = map[string]string{}
	}
	pod.Labels[apps.StatefulSetPodNameLabel] = pod.Name
	pod.Labels[apps.PodIndexLabel] = strconv.Itoa(ordinal)
}

func identityMatches(set *apps.StatefulSet, pod *v1.Pod) bool {
	return isMemberOf(set.Name, pod.Name) &&
		pod.Namespace == set.Namespace &&
		pod.Labels[apps.StatefulSetPodNameLabel] == pod.Name &&
		pod.Labels[apps.PodIndexLabel] == strconv.Itoa(ordinalOf(pod.Name))
}

func volumeClaimTemplatesByName(set *apps.StatefulSet) map[string]v1.PersistentVolumeClaim {
	claimTemplates := make(map[string]v1.PersistentVolumeClaim, len(set.Spec.VolumeClaimTemplates))
	for _, claimTemplate := range set.Spec.VolumeClaimTemplates {
		claimTemplates[claimTemplate.Name] = claimTemplate
	}
	return claimTemplates
}

// initStorage initializes the immutable volume list of a newly created
// StatefulSet Pod. Upstream performs the same initialization before creation:
// https://github.com/kubernetes/kubernetes/blob/master/pkg/controller/statefulset/stateful_set_utils.go
func initStorage(set *apps.StatefulSet, pod *v1.Pod) {
	ordinal := ordinalOf(pod.Name)
	currentVolumes := pod.Spec.Volumes
	newVolumes := []v1.Volume{}
	claimTemplates := volumeClaimTemplatesByName(set)

	for name, claim := range claimTemplates {
		newVolumes = append(newVolumes, v1.Volume{
			Name: name,
			VolumeSource: v1.VolumeSource{
				PersistentVolumeClaim: &v1.PersistentVolumeClaimVolumeSource{
					ClaimName: claimName(set.Name, claim.Name, ordinal),
				},
			},
		})
	}

	for _, volume := range currentVolumes {
		if _, ok := claimTemplates[volume.Name]; !ok {
			newVolumes = append(newVolumes, volume)
		}
	}

	pod.Spec.Volumes = newVolumes
}

func storageMatches(set *apps.StatefulSet, pod *v1.Pod) bool {
	ordinal := ordinalOf(pod.Name)
	if ordinal < 0 {
		return false
	}

	volumes := make(map[string]v1.Volume, len(pod.Spec.Volumes))
	for _, volume := range pod.Spec.Volumes {
		volumes[volume.Name] = volume
	}

	for name, claim := range volumeClaimTemplatesByName(set) {
		volume, found := volumes[name]
		if !found ||
			volume.VolumeSource.PersistentVolumeClaim == nil ||
			volume.VolumeSource.PersistentVolumeClaim.ClaimName != claimName(set.Name, claim.Name, ordinal) {
			return false
		}
	}

	return true
}

func newStatefulSetPod(set *apps.StatefulSet, ordinal int) (*v1.Pod, error) {
	pod, err := controller.GetPodFromTemplate(&set.Spec.Template, set, metav1.NewControllerRef(set, apps.SchemeGroupVersion.WithKind("StatefulSet")))
	if err != nil {
		return nil, err
	}
	pod.Name = podName(set.Name, ordinal)
	initIdentity(set, pod)
	initStorage(set, pod)
	return pod, nil
}

func newPersistentVolumeClaim(set *apps.StatefulSet, pod *v1.Pod, claimTemplate *v1.PersistentVolumeClaim) *v1.PersistentVolumeClaim {
	claim := claimTemplate.DeepCopy()
	claim.Name = claimName(set.Name, claim.Name, ordinalOf(pod.Name))
	claim.Namespace = set.Namespace
	// Keep owner references nil to simplify the reasoning.
	claim.OwnerReferences = nil
	if claim.Labels == nil {
		claim.Labels = map[string]string{}
	}
	if set.Spec.Selector != nil {
		for key, value := range set.Spec.Selector.MatchLabels {
			claim.Labels[key] = value
		}
	}
	return claim
}

func createPersistentVolumeClaim(set *apps.StatefulSet, pod *v1.Pod, claimTemplate *v1.PersistentVolumeClaim) error {
	claim := newPersistentVolumeClaim(set, pod, claimTemplate)
	_, err := apimodel.ModelState.PersistentVolumeClaimGet(claim.Namespace, claim.Name)
	if apierrors.IsNotFound(err) {
		_, err = apimodel.ModelState.PersistentVolumeClaimCreate(claim.Namespace, claim)
		if err != nil && !apierrors.IsAlreadyExists(err) {
			return err
		}
		return nil
	}
	return err
}

func createPersistentVolumeClaims(set *apps.StatefulSet, pod *v1.Pod) error {
	for _, claimTemplate := range volumeClaimTemplatesByName(set) {
		if err := createPersistentVolumeClaim(set, pod, &claimTemplate); err != nil {
			return err
		}
	}
	return nil
}

func createStatefulPod(set *apps.StatefulSet, pod *v1.Pod) error {
	if err := createPersistentVolumeClaims(set, pod); err != nil {
		return err
	}
	_, err := apimodel.ModelState.PodCreate(set.Namespace, pod)
	if apierrors.IsAlreadyExists(err) {
		return nil
	}
	return err
}

func updateStatefulPod(set *apps.StatefulSet, pod *v1.Pod) error {
	if identityMatches(set, pod) {
		return nil
	}

	updatedPod := pod.DeepCopy()
	updateIdentity(set, updatedPod)
	_, err := apimodel.ModelState.PodUpdateTx(updatedPod.Namespace, updatedPod)
	return err
}

func deletePod(pod *v1.Pod) error {
	uid := pod.ObjectMeta.GetUID()
	err := apimodel.ModelState.PodDelete(pod.Namespace, pod.Name, common.NewDeleteOptionsWithUID(uid))
	if err != nil && !apierrors.IsNotFound(err) {
		return err
	}
	return nil
}

func findPodByOrdinal(set *apps.StatefulSet, pods []*v1.Pod, ordinal int) *v1.Pod {
	for _, pod := range pods {
		parent, podOrdinal := parentNameAndOrdinal(pod.Name)
		if parent == set.Name && podOrdinal == ordinal {
			return pod
		}
	}
	return nil
}

func firstCondemnedPod(set *apps.StatefulSet, pods []*v1.Pod) *v1.Pod {
	var condemned *v1.Pod
	for _, pod := range pods {
		ordinal := ordinalOf(pod.Name)
		if ordinal < 0 || podInOrdinalRange(set, pod.Name) {
			continue
		}
		if condemned == nil || ordinal > ordinalOf(condemned.Name) {
			condemned = pod
		}
	}
	return condemned
}

// Detect outdated Pods by their creation revision, rather than comparing live
// PodSpecs that may differ because of defaulting, admission, or scheduling.
func largestOutdatedPod(set *apps.StatefulSet, pods []*v1.Pod, revision string) *v1.Pod {
	for ordinal := endOrdinalOf(set); ordinal >= 0; ordinal-- {
		pod := findPodByOrdinal(set, pods, ordinal)
		if pod != nil && !podRevisionMatches(pod, revision) {
			return pod
		}
	}
	return nil
}

// reconcileDesiredPods returns true only after every desired Pod has been
// processed. A false result without an error tells the caller to stop this
// reconciliation after creating a missing Pod or observing a terminating Pod.
func reconcileDesiredPods(set, updateSet *apps.StatefulSet, pods []*v1.Pod, updateRevision string) (bool, error) {
	end := endOrdinalOf(set)

	for ordinal := 0; ordinal <= end; ordinal++ {
		pod := findPodByOrdinal(set, pods, ordinal)
		if pod == nil {
			newPod, err := newVersionedStatefulSetPod(updateSet, updateRevision, ordinal)
			if err != nil {
				return false, err
			}
			if err := createStatefulPod(set, newPod); err != nil {
				return false, err
			}
			return false, nil
		}

		if isTerminating(pod) {
			return false, nil
		}

		if err := createPersistentVolumeClaims(set, pod); err != nil {
			return false, err
		}

		if err := updateStatefulPod(set, pod); err != nil {
			return false, err
		}
	}

	return true, nil
}

// reconcileCondemnedPod returns true when there is no condemned Pod and
// reconciliation may continue. After observing or deleting one condemned Pod,
// the caller stops this reconciliation and waits for the next observed state.
func reconcileCondemnedPod(set *apps.StatefulSet, pods []*v1.Pod) (bool, error) {
	condemned := firstCondemnedPod(set, pods)
	if condemned == nil {
		return true, nil
	}
	if isTerminating(condemned) {
		return false, nil
	}
	if err := deletePod(condemned); err != nil {
		return false, err
	}
	return false, nil
}

func reconcileOutdatedPod(set *apps.StatefulSet, pods []*v1.Pod, revision string) error {
	outdated := largestOutdatedPod(set, pods, revision)
	if outdated == nil {
		return nil
	}
	if isTerminating(outdated) {
		return nil
	}
	return deletePod(outdated)
}

func reconcileReplicas(set, updateSet *apps.StatefulSet, pods []*v1.Pod, updateRevision string) error {
	continueReconcile, err := reconcileDesiredPods(set, updateSet, pods, updateRevision)
	if err != nil || !continueReconcile {
		return err
	}

	continueReconcile, err = reconcileCondemnedPod(set, pods)
	if err != nil || !continueReconcile {
		return err
	}

	return reconcileOutdatedPod(set, pods, updateRevision)
}

func syncStatefulSet(namespace, name string) error {
	set, err := apimodel.ModelState.StatefulSetGet(namespace, name)
	if apierrors.IsNotFound(err) {
		return nil
	}
	if err != nil {
		return err
	}

	allPods, err := common.FilterPodsByOwner(&set.ObjectMeta, "StatefulSet")
	if err != nil {
		return err
	}

	if set.DeletionTimestamp != nil {
		return nil
	}

	if err := releasePodsWithBadNames(set, allPods); err != nil {
		return err
	}

	pods := filterPodsForStatefulSet(set, allPods)
	revisions, err := listRevisions(set)
	if err != nil {
		return err
	}
	current, update, collisionCount, err := getStatefulSetRevisions(set, revisions)
	if err != nil {
		return err
	}
	updateSet, err := applyRevision(set, update)
	if err != nil {
		return err
	}
	reconcileErr := reconcileReplicas(set, updateSet, pods, update.Name)
	statusErr := updateRevisionStatus(set, pods, current, update, collisionCount)
	historyErr := truncateHistory(set, pods, revisions, current, update)
	if reconcileErr != nil {
		return reconcileErr
	}
	if statusErr != nil {
		return statusErr
	}
	return historyErr
}
