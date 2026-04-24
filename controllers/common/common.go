package common

import (
	"kubernetes_model/apimodel"

	v1 "k8s.io/api/core/v1"
	metav1 "k8s.io/apimachinery/pkg/apis/meta/v1"
	"k8s.io/kubernetes/pkg/controller"
)

var State *apimodel.State

func init() {
	State = apimodel.NewState()
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
