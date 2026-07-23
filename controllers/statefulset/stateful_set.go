package statefulset

import (
	"controllers/common"
	"kubernetes_model/apimodel"
	"reflect"
	"strconv"
	"strings"

	apps "k8s.io/api/apps/v1"
	v1 "k8s.io/api/core/v1"
	apierrors "k8s.io/apimachinery/pkg/api/errors"
	metav1 "k8s.io/apimachinery/pkg/apis/meta/v1"
	"k8s.io/kubernetes/pkg/controller"
)

// A simplified statefulset controller. The following features are not included:
// * adoption and release
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

func releasePod(set *apps.StatefulSet, pod *v1.Pod) error {
	updatedPod := pod.DeepCopy()
	ownerReferences := []metav1.OwnerReference{}
	released := false
	for _, ownerReference := range updatedPod.OwnerReferences {
		isController := ownerReference.Controller != nil && *ownerReference.Controller
		if isController && ownerReference.UID == set.UID {
			released = true
			continue
		}
		ownerReferences = append(ownerReferences, ownerReference)
	}
	if !released {
		return nil
	}
	updatedPod.OwnerReferences = ownerReferences
	_, err := apimodel.ModelState.PodUpdate(updatedPod.Namespace, updatedPod)
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

func updateIdentity(set *apps.StatefulSet, pod *v1.Pod) {
	ordinal := ordinalOf(pod.Name)
	pod.Name = podName(set.Name, ordinal)
	pod.Namespace = set.Namespace
	pod.Spec.Hostname = pod.Name
	pod.Spec.Subdomain = set.Spec.ServiceName
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
		pod.Spec.Hostname == pod.Name &&
		pod.Spec.Subdomain == set.Spec.ServiceName &&
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

func updateStorage(set *apps.StatefulSet, pod *v1.Pod) {
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
	updateIdentity(set, pod)
	updateStorage(set, pod)
	return pod, nil
}

func newPersistentVolumeClaim(set *apps.StatefulSet, pod *v1.Pod, claimTemplate *v1.PersistentVolumeClaim) *v1.PersistentVolumeClaim {
	claim := claimTemplate.DeepCopy()
	claim.Name = claimName(set.Name, claim.Name, ordinalOf(pod.Name))
	claim.Namespace = set.Namespace
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
	if identityMatches(set, pod) && storageMatches(set, pod) {
		return nil
	}

	updatedPod := pod.DeepCopy()
	if !identityMatches(set, updatedPod) {
		updateIdentity(set, updatedPod)
	}
	if !storageMatches(set, updatedPod) {
		updateStorage(set, updatedPod)
	}
	_, err := apimodel.ModelState.PodUpdate(updatedPod.Namespace, updatedPod)
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

func withoutStatefulSetFields(spec v1.PodSpec) v1.PodSpec {
	spec.Volumes = nil
	spec.Hostname = ""
	spec.Subdomain = ""
	return spec
}

func podSpecMatches(set *apps.StatefulSet, pod *v1.Pod) bool {
	podSpec := withoutStatefulSetFields(pod.Spec)
	templateSpec := withoutStatefulSetFields(set.Spec.Template.Spec)
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

func reconcileReplicas(set *apps.StatefulSet, pods []*v1.Pod) error {
	end := endOrdinalOf(set)

	for ordinal := 0; ordinal <= end; ordinal++ {
		pod := findPodByOrdinal(set, pods, ordinal)
		if pod == nil {
			newPod, err := newStatefulSetPod(set, ordinal)
			if err != nil {
				return err
			}
			if err := createStatefulPod(set, newPod); err != nil {
				return err
			}
			return nil
		}

		if isTerminating(pod) {
			return nil
		}

		if err := createPersistentVolumeClaims(set, pod); err != nil {
			return err
		}

		if err := updateStatefulPod(set, pod); err != nil {
			return err
		}
	}

	if condemned := firstCondemnedPod(set, pods); condemned != nil {
		if isTerminating(condemned) {
			return nil
		}
		if err := deletePod(condemned); err != nil {
			return err
		}
		return nil
	}

	if outdated := largestOutdatedPod(set, pods); outdated != nil {
		if isTerminating(outdated) {
			return nil
		}
		return deletePod(outdated)
	}

	return nil
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

	return reconcileReplicas(set, filterPodsForStatefulSet(set, allPods))
}
