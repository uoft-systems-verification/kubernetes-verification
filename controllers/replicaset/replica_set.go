package replicaset

import (
	"kubernetes_model/apimodel"

	apps "k8s.io/api/apps/v1"
	v1 "k8s.io/api/core/v1"
	apierrors "k8s.io/apimachinery/pkg/api/errors"
	metav1 "k8s.io/apimachinery/pkg/apis/meta/v1"
	"k8s.io/kubernetes/pkg/controller"
)

// A highly simplified replicaset controller. The following features are removed:
// * adoption and release
// * managing status
// * concurrent creation/deletion
// * sort before deletion

var state *apimodel.State

func init() {
	state = apimodel.NewState()
}

func CreatePod(namespace string, template *v1.PodTemplateSpec, controllerObject *apps.ReplicaSet, controllerRef *metav1.OwnerReference) error {
	pod, err := controller.GetPodFromTemplate(template, controllerObject, controllerRef)
	if err != nil {
		return err
	}
	_, err = state.PodCreate(namespace, pod)
	return err
}

func FilterPodsByOwner(owner *metav1.ObjectMeta, ownerKind string) ([]*v1.Pod, error) {
	result := []*v1.Pod{}
	key := controller.PodControllerIndexKey(owner.Namespace, &metav1.OwnerReference{Name: owner.Name, Kind: ownerKind, UID: owner.UID})
	pods, err := state.ByIndex("Pod", controller.PodControllerIndex, key)
	if err != nil {
		return nil, err
	}
	for _, obj := range pods {
		pod, ok := obj.(*v1.Pod)
		if !ok {
			continue
		}
		result = append(result, pod)
	}
	return result, nil
}

func IsPodActive(p *v1.Pod) bool {
	return p.DeletionTimestamp == nil
}

func FilterActivePods(pods []*v1.Pod) []*v1.Pod {
	var result []*v1.Pod
	for _, p := range pods {
		if IsPodActive(p) {
			result = append(result, p)
		}
	}
	return result
}

func manageReplicas(activePods []*v1.Pod, rs *apps.ReplicaSet) error {
	diff := len(activePods) - int(*(rs.Spec.Replicas))
	if diff < 0 {
		diff *= -1
		for i := 0; i < diff; i++ {
			pod, err := controller.GetPodFromTemplate(&rs.Spec.Template, rs, metav1.NewControllerRef(rs, apps.SchemeGroupVersion.WithKind("ReplicaSet")))
			if err != nil {
				return err
			}
			_, err = state.PodCreate(rs.Namespace, pod)
			if err != nil {
				return err
			}
		}
	} else if diff > 0 {
		podsToDelete := activePods[:diff]
		for _, pod := range podsToDelete {
			if err := state.PodDelete(rs.Namespace, pod.Name); err != nil {
				if !apierrors.IsNotFound(err) {
					return err
				}
			}
		}
	}

	return nil
}

func syncReplicaSet(namespace, name string) error {
	rs, err := state.ReplicaSetGet(namespace, name)
	if apierrors.IsNotFound(err) {
		return nil
	}
	if err != nil {
		return err
	}

	allRSPods, err := FilterPodsByOwner(&rs.ObjectMeta, "ReplicaSet")
	if err != nil {
		return err
	}

	allActivePods := FilterActivePods(allRSPods)

	var manageReplicasErr error
	if rs.DeletionTimestamp == nil {
		manageReplicasErr = manageReplicas(allActivePods, rs)
	}

	return manageReplicasErr
}
