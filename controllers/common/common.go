package common

import (
	v1 "k8s.io/api/core/v1"
	metav1 "k8s.io/apimachinery/pkg/apis/meta/v1"
	"k8s.io/apimachinery/pkg/types"
	"k8s.io/client-go/tools/cache"
	"k8s.io/kubernetes/pkg/controller"
)

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

// FilterPodsByOwner reads controlled Pods from the informer index. Orphans are
// omitted because adoption is outside the simplified controllers' scope.
func FilterPodsByOwner(podIndexer cache.Indexer, owner *metav1.ObjectMeta, ownerKind string) ([]*v1.Pod, error) {
	result := []*v1.Pod{}
	key := controller.PodControllerIndexKey(owner.Namespace, &metav1.OwnerReference{Name: owner.Name, Kind: ownerKind, UID: owner.UID})
	pods, err := podIndexer.ByIndex(controller.PodControllerIndex, key)
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
