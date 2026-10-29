package statefulset

import (
	"context"
	"controllers/common"
	"reflect"
	"strconv"
	"strings"

	apps "k8s.io/api/apps/v1"
	v1 "k8s.io/api/core/v1"
	apierrors "k8s.io/apimachinery/pkg/api/errors"
	metav1 "k8s.io/apimachinery/pkg/apis/meta/v1"
	clientset "k8s.io/client-go/kubernetes"
	appslisters "k8s.io/client-go/listers/apps/v1"
	corelisters "k8s.io/client-go/listers/core/v1"
	"k8s.io/client-go/tools/cache"
	"k8s.io/kubernetes/pkg/controller"
)

// A simplified statefulset controller. The following features are not included:
// * adoption
// * managing status
// * ControllerRevision history and rolling updates
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

// releasePod removes this StatefulSet's owner references from a copy of the Pod.
func releasePod(ctx context.Context, kubeClient *clientset.Clientset, set *apps.StatefulSet, pod *v1.Pod) error {
	updatedPod := pod.DeepCopy()
	ownerReferences := []metav1.OwnerReference{}
	released := false
	for _, ownerReference := range updatedPod.OwnerReferences {
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
	var updateOptions metav1.UpdateOptions
	_, err := kubeClient.CoreV1().Pods(updatedPod.Namespace).Update(ctx, updatedPod, updateOptions)
	if apierrors.IsNotFound(err) {
		return nil
	}
	return err
}

func releasePodsWithBadNames(ctx context.Context, kubeClient *clientset.Clientset, set *apps.StatefulSet, pods []*v1.Pod) error {
	for _, pod := range pods {
		if isMemberOf(set.Name, pod.Name) {
			continue
		}
		if err := releasePod(ctx, kubeClient, set, pod); err != nil {
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
	parent, ordinal := parentNameAndOrdinal(pod.Name)
	return ordinal >= 0 &&
		parent == set.Name &&
		pod.Name == podName(set.Name, ordinal) &&
		pod.Namespace == set.Namespace &&
		pod.Labels[apps.StatefulSetPodNameLabel] == pod.Name &&
		pod.Labels[apps.PodIndexLabel] == strconv.Itoa(ordinal)
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

func createPersistentVolumeClaim(ctx context.Context, kubeClient *clientset.Clientset, claimLister corelisters.PersistentVolumeClaimLister, set *apps.StatefulSet, pod *v1.Pod, claimTemplate *v1.PersistentVolumeClaim) error {
	claim := newPersistentVolumeClaim(set, pod, claimTemplate)
	_, err := claimLister.PersistentVolumeClaims(claim.Namespace).Get(claim.Name)
	if apierrors.IsNotFound(err) {
		var createOptions metav1.CreateOptions
		_, err = kubeClient.CoreV1().PersistentVolumeClaims(claim.Namespace).Create(ctx, claim, createOptions)
		if err != nil && !apierrors.IsAlreadyExists(err) {
			return err
		}
		return nil
	}
	return err
}

func createPersistentVolumeClaims(ctx context.Context, kubeClient *clientset.Clientset, claimLister corelisters.PersistentVolumeClaimLister, set *apps.StatefulSet, pod *v1.Pod) error {
	for _, claimTemplate := range volumeClaimTemplatesByName(set) {
		if err := createPersistentVolumeClaim(ctx, kubeClient, claimLister, set, pod, &claimTemplate); err != nil {
			return err
		}
	}
	return nil
}

func createStatefulPod(ctx context.Context, kubeClient *clientset.Clientset, claimLister corelisters.PersistentVolumeClaimLister, set *apps.StatefulSet, pod *v1.Pod) error {
	if err := createPersistentVolumeClaims(ctx, kubeClient, claimLister, set, pod); err != nil {
		return err
	}
	var createOptions metav1.CreateOptions
	_, err := kubeClient.CoreV1().Pods(set.Namespace).Create(ctx, pod, createOptions)
	if apierrors.IsAlreadyExists(err) {
		return nil
	}
	return err
}

func updateStatefulPod(ctx context.Context, kubeClient *clientset.Clientset, set *apps.StatefulSet, pod *v1.Pod) error {
	if identityMatches(set, pod) {
		return nil
	}

	updatedPod := pod.DeepCopy()
	updateIdentity(set, updatedPod)
	var updateOptions metav1.UpdateOptions
	_, err := kubeClient.CoreV1().Pods(updatedPod.Namespace).Update(ctx, updatedPod, updateOptions)
	return err
}

func deletePod(ctx context.Context, kubeClient *clientset.Clientset, pod *v1.Pod) error {
	// Upstream StatefulPodControl deletes by name without UID preconditions.
	err := kubeClient.CoreV1().Pods(pod.Namespace).Delete(ctx, pod.Name, metav1.DeleteOptions{})
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

func withoutStatefulSetFields(spec v1.PodSpec) v1.PodSpec {
	spec.Volumes = nil
	spec.Hostname = ""
	spec.Subdomain = ""
	return spec
}

func podSpecMatches(set *apps.StatefulSet, pod *v1.Pod) bool {
	// Hostname, Subdomain, and Volumes cannot be repaired through the normal
	// Pod update API. Detect a mismatch here so reconciliation replaces the
	// Pod instead. Upstream initializes these fields for newly created Pods in
	// stateful_set_utils.go:
	// https://github.com/kubernetes/kubernetes/blob/master/pkg/controller/statefulset/stateful_set_utils.go
	// See also Kubernetes Pod update validation:
	// https://github.com/kubernetes/kubernetes/blob/master/pkg/apis/core/validation/validation.go
	if pod.Spec.Hostname != pod.Name ||
		pod.Spec.Subdomain != set.Spec.ServiceName ||
		!storageMatches(set, pod) {
		return false
	}
	// Copy both sides before comparison: Quantity.DeepCopy can normalize an
	// empty internal big.Int buffer without changing its words or API value.
	podSpec := withoutStatefulSetFields(*pod.Spec.DeepCopy())
	templateSpec := withoutStatefulSetFields(*set.Spec.Template.Spec.DeepCopy())
	// TODO: Use ControllerRevision labels to detect outdated Pods, as upstream
	// does. Full-spec equality can reject a freshly created Pod because of
	// API-server defaults and admission mutations, or later scheduler changes.
	return reflect.DeepEqual(podSpec, templateSpec)
}

func largestOutdatedPod(set *apps.StatefulSet, pods []*v1.Pod) *v1.Pod {
	for ordinal := endOrdinalOf(set); ordinal >= 0; ordinal-- {
		pod := findPodByOrdinal(set, pods, ordinal)
		if pod != nil && !podSpecMatches(set, pod) {
			return pod
		}
	}
	return nil
}

// reconcileDesiredPods returns true only after every desired Pod has been
// processed. A false result without an error tells the caller to stop this
// reconciliation after creating a missing Pod or observing a terminating Pod.
func reconcileDesiredPods(ctx context.Context, kubeClient *clientset.Clientset, claimLister corelisters.PersistentVolumeClaimLister, set *apps.StatefulSet, pods []*v1.Pod) (bool, error) {
	end := endOrdinalOf(set)

	for ordinal := 0; ordinal <= end; ordinal++ {
		pod := findPodByOrdinal(set, pods, ordinal)
		if pod == nil {
			newPod, err := newStatefulSetPod(set, ordinal)
			if err != nil {
				return false, err
			}
			if err := createStatefulPod(ctx, kubeClient, claimLister, set, newPod); err != nil {
				return false, err
			}
			return false, nil
		}

		if isTerminating(pod) {
			return false, nil
		}

		if err := createPersistentVolumeClaims(ctx, kubeClient, claimLister, set, pod); err != nil {
			return false, err
		}

		if err := updateStatefulPod(ctx, kubeClient, set, pod); err != nil {
			return false, err
		}
	}

	return true, nil
}

// reconcileCondemnedPod returns true when there is no condemned Pod and
// reconciliation may continue. After observing or deleting one condemned Pod,
// the caller stops this reconciliation and waits for the next observed state.
func reconcileCondemnedPod(ctx context.Context, kubeClient *clientset.Clientset, set *apps.StatefulSet, pods []*v1.Pod) (bool, error) {
	condemned := firstCondemnedPod(set, pods)
	if condemned == nil {
		return true, nil
	}
	if isTerminating(condemned) {
		return false, nil
	}
	if err := deletePod(ctx, kubeClient, condemned); err != nil {
		return false, err
	}
	return false, nil
}

func reconcileOutdatedPod(ctx context.Context, kubeClient *clientset.Clientset, set *apps.StatefulSet, pods []*v1.Pod) error {
	outdated := largestOutdatedPod(set, pods)
	if outdated == nil {
		return nil
	}
	if isTerminating(outdated) {
		return nil
	}
	return deletePod(ctx, kubeClient, outdated)
}

func reconcileReplicas(ctx context.Context, kubeClient *clientset.Clientset, claimLister corelisters.PersistentVolumeClaimLister, set *apps.StatefulSet, pods []*v1.Pod) error {
	continueReconcile, err := reconcileDesiredPods(ctx, kubeClient, claimLister, set, pods)
	if err != nil || !continueReconcile {
		return err
	}

	continueReconcile, err = reconcileCondemnedPod(ctx, kubeClient, set, pods)
	if err != nil || !continueReconcile {
		return err
	}

	return reconcileOutdatedPod(ctx, kubeClient, set, pods)
}

func syncStatefulSet(ctx context.Context, kubeClient *clientset.Clientset, setLister appslisters.StatefulSetLister, claimLister corelisters.PersistentVolumeClaimLister, podIndexer cache.Indexer, namespace, name string) error {
	set, err := setLister.StatefulSets(namespace).Get(name)
	if apierrors.IsNotFound(err) {
		return nil
	}
	if err != nil {
		return err
	}

	allPods, err := common.FilterPodsByOwner(podIndexer, &set.ObjectMeta, "StatefulSet")
	if err != nil {
		return err
	}

	if set.DeletionTimestamp != nil {
		return nil
	}

	if err := releasePodsWithBadNames(ctx, kubeClient, set, allPods); err != nil {
		return err
	}

	return reconcileReplicas(ctx, kubeClient, claimLister, set, filterPodsForStatefulSet(set, allPods))
}
