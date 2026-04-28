package common

import (
	"kubernetes_model/apimodel"

	v1 "k8s.io/api/core/v1"
	metav1 "k8s.io/apimachinery/pkg/apis/meta/v1"
	"k8s.io/apimachinery/pkg/types"
	"k8s.io/kubernetes/pkg/controller"
)

var State *apimodel.State

func init() {
	State = apimodel.NewState()
}

func NewDeleteOptionsWithUID(uid types.UID) metav1.DeleteOptions {
	return metav1.DeleteOptions{
		Preconditions: &metav1.Preconditions{UID: &uid},
	}
}

func FilterActivePods(pods []*v1.Pod) []*v1.Pod {
	var result []*v1.Pod
	for _, p := range pods {
		if p.DeletionTimestamp == nil {
			result = append(result, p)
		}
	}
	return result
}

func FilterPodsByOwner(owner *metav1.ObjectMeta, ownerKind string) ([]*v1.Pod, error) {
	result := []*v1.Pod{}
	key := controller.PodControllerIndexKey(owner.Namespace, &metav1.OwnerReference{Name: owner.Name, Kind: ownerKind, UID: owner.UID})
	pods, err := State.ByIndex("Pod", controller.PodControllerIndex, key)
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
