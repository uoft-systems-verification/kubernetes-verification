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

var controllerKind = apps.SchemeGroupVersion.WithKind("StatefulSet")

func replicasOf(set *apps.StatefulSet) int {
	if set.Spec.Replicas == nil {
		return 1
	}
	return int(*set.Spec.Replicas)
}

func endOrdinalOf(set *apps.StatefulSet) int {
	return replicasOf(set) - 1
}

func podName(set *apps.StatefulSet, ordinal int) string {
	return set.Name + "-" + strconv.Itoa(ordinal)
}

func claimName(set *apps.StatefulSet, claim *v1.PersistentVolumeClaim, ordinal int) string {
	return claim.Name + "-" + set.Name + "-" + strconv.Itoa(ordinal)
}

func parentNameAndOrdinal(pod *v1.Pod) (string, int) {
	idx := strings.LastIndex(pod.Name, "-")
	if idx < 0 {
		return "", -1
	}
	ordinal, err := strconv.ParseInt(pod.Name[idx+1:], 10, 32)
	if err != nil {
		return "", -1
	}
	return pod.Name[:idx], int(ordinal)
}

func ordinalOf(pod *v1.Pod) int {
	_, ordinal := parentNameAndOrdinal(pod)
	return ordinal
}

func isMemberOf(set *apps.StatefulSet, pod *v1.Pod) bool {
	parent, ordinal := parentNameAndOrdinal(pod)
	return parent == set.Name && ordinal >= 0 && pod.Name == podName(set, ordinal)
}

func filterPodsForStatefulSet(set *apps.StatefulSet, pods []*v1.Pod) []*v1.Pod {
	result := []*v1.Pod{}
	for _, pod := range pods {
		if isMemberOf(set, pod) {
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
		if isMemberOf(set, pod) {
			continue
		}
		if err := releasePod(set, pod); err != nil {
			return err
		}
	}
	return nil
}

func podInOrdinalRange(set *apps.StatefulSet, pod *v1.Pod) bool {
	ordinal := ordinalOf(pod)
	return ordinal >= 0 && ordinal <= endOrdinalOf(set)
}

func updateIdentity(set *apps.StatefulSet, pod *v1.Pod) {
	ordinal := ordinalOf(pod)
	pod.Name = podName(set, ordinal)
	pod.Namespace = set.Namespace
	pod.Spec.Hostname = pod.Name
	pod.Spec.Subdomain = set.Spec.ServiceName
	if pod.Labels == nil {
		pod.Labels = map[string]string{}
	}
	pod.Labels[apps.StatefulSetPodNameLabel] = pod.Name
	pod.Labels[apps.PodIndexLabel] = strconv.Itoa(ordinal)
}

func volumeClaimTemplatesByName(set *apps.StatefulSet) map[string]v1.PersistentVolumeClaim {
	claimTemplates := make(map[string]v1.PersistentVolumeClaim, len(set.Spec.VolumeClaimTemplates))
	for _, claimTemplate := range set.Spec.VolumeClaimTemplates {
		claimTemplates[claimTemplate.Name] = claimTemplate
	}
	return claimTemplates
}

func updateStorage(set *apps.StatefulSet, pod *v1.Pod) {
	ordinal := ordinalOf(pod)
	currentVolumes := pod.Spec.Volumes
	newVolumes := []v1.Volume{}
	claimTemplates := volumeClaimTemplatesByName(set)

	for name, claim := range claimTemplates {
		newVolumes = append(newVolumes, v1.Volume{
			Name: name,
			VolumeSource: v1.VolumeSource{
				PersistentVolumeClaim: &v1.PersistentVolumeClaimVolumeSource{
					ClaimName: claimName(set, &claim, ordinal),
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

func newStatefulSetPod(set *apps.StatefulSet, ordinal int) (*v1.Pod, error) {
	pod, err := controller.GetPodFromTemplate(&set.Spec.Template, set, metav1.NewControllerRef(set, controllerKind))
	if err != nil {
		return nil, err
	}
	pod.Name = podName(set, ordinal)
	updateIdentity(set, pod)
	updateStorage(set, pod)
	return pod, nil
}

func newPersistentVolumeClaim(set *apps.StatefulSet, pod *v1.Pod, claimTemplate *v1.PersistentVolumeClaim) *v1.PersistentVolumeClaim {
	claim := claimTemplate.DeepCopy()
	claim.Name = claimName(set, claim, ordinalOf(pod))
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

func createPersistentVolumeClaims(set *apps.StatefulSet, pod *v1.Pod) error {
	for _, claimTemplate := range volumeClaimTemplatesByName(set) {
		claim := newPersistentVolumeClaim(set, pod, &claimTemplate)
		_, err := apimodel.ModelState.PersistentVolumeClaimGet(claim.Namespace, claim.Name)
		if apierrors.IsNotFound(err) {
			_, err = apimodel.ModelState.PersistentVolumeClaimCreate(claim.Namespace, claim)
			if err != nil && !apierrors.IsAlreadyExists(err) {
				return err
			}
			continue
		}
		if err != nil {
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
	updatedPod := pod.DeepCopy()
	updateIdentity(set, updatedPod)
	updateStorage(set, updatedPod)
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
		parent, podOrdinal := parentNameAndOrdinal(pod)
		if parent == set.Name && podOrdinal == ordinal {
			return pod
		}
	}
	return nil
}

func firstCondemnedPod(set *apps.StatefulSet, pods []*v1.Pod) *v1.Pod {
	var condemned *v1.Pod
	for _, pod := range pods {
		ordinal := ordinalOf(pod)
		if ordinal < 0 || podInOrdinalRange(set, pod) {
			continue
		}
		if condemned == nil || ordinal > ordinalOf(condemned) {
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

func samePod(pod, other *v1.Pod) bool {
	return other != nil && pod.Namespace == other.Namespace && pod.Name == other.Name
}

func withoutPod(pods []*v1.Pod, target *v1.Pod) []*v1.Pod {
	result := []*v1.Pod{}
	for _, pod := range pods {
		if samePod(pod, target) {
			continue
		}
		result = append(result, pod)
	}
	return result
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
			continue
		}

		if err := createPersistentVolumeClaims(set, pod); err != nil {
			return err
		}

		if err := updateStatefulPod(set, pod); err != nil {
			return err
		}
	}

	for condemned := firstCondemnedPod(set, pods); condemned != nil; condemned = firstCondemnedPod(set, pods) {
		if condemned.DeletionTimestamp != nil {
			pods = withoutPod(pods, condemned)
			continue
		}
		if err := deletePod(condemned); err != nil {
			return err
		}
		pods = withoutPod(pods, condemned)
	}

	if outdated := largestOutdatedPod(set, pods); outdated != nil {
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
