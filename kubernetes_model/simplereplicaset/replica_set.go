package simplereplicaset

import (
	"context"
	"fmt"
	"kubernetes_model/simpleapiserver"
	"sort"

	apps "k8s.io/api/apps/v1"
	v1 "k8s.io/api/core/v1"
	apierrors "k8s.io/apimachinery/pkg/api/errors"
	metav1 "k8s.io/apimachinery/pkg/apis/meta/v1"
	"k8s.io/apimachinery/pkg/labels"
	"k8s.io/apimachinery/pkg/types"
	"k8s.io/client-go/tools/cache"
	"k8s.io/klog/v2"
	"k8s.io/kubernetes/pkg/controller"
)

func CreatePod(ctx context.Context, namespace string, template *v1.PodTemplateSpec, controllerObject *apps.ReplicaSet, controllerRef *metav1.OwnerReference) error {
	pod, err := controller.GetPodFromTemplate(template, controllerObject, controllerRef)
	if err != nil {
		return err
	}
	if len(labels.Set(pod.Labels)) == 0 {
		return fmt.Errorf("unable to create pods, no labels")
	}
	_, err = simpleapiserver.PodCreate(namespace, pod)
	return err
}

func FilterPodsByOwner(owner *metav1.ObjectMeta) ([]*v1.Pod, error) {
	result := []*v1.Pod{}
	// Iterate over two keys:
	// - the UID of the owner, which identifies Pods that are controlled by the owner
	// - the OrphanPodIndexKey, which identifies orphaned Pods in the owner's namespace and might be adopted by the owner later
	for _, key := range []string{string(owner.UID), simpleapiserver.OrphanPodIndexKeyForNamespace(owner.Namespace)} {
		pods, err := simpleapiserver.ByIndex("Pod", simpleapiserver.PodControllerUIDIndex, key)
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
	}
	return result, nil
}

func getReplicaSetsWithSameController(logger klog.Logger, rs *apps.ReplicaSet) []*apps.ReplicaSet {
	controllerRef := metav1.GetControllerOf(rs)
	if controllerRef == nil {
		return nil
	}

	objects, err := simpleapiserver.ByIndex("ReplicaSet", simpleapiserver.ControllerUIDIndex, string(controllerRef.UID))
	if err != nil {
		return nil
	}
	relatedRSs := make([]*apps.ReplicaSet, 0, len(objects))
	for _, obj := range objects {
		relatedRSs = append(relatedRSs, obj.(*apps.ReplicaSet))
	}

	return relatedRSs
}

// manageReplicas checks and updates replicas for the given ReplicaSet.
// Does NOT modify <activePods>.
// It will requeue the replica set in case of an error while creating/deleting pods.
func manageReplicas(ctx context.Context, activePods []*v1.Pod, rs *apps.ReplicaSet) error {
	diff := len(activePods) - int(*(rs.Spec.Replicas))
	_, err := controller.KeyFunc(rs)
	if err != nil {
		return nil
	}
	logger := klog.FromContext(ctx)
	if diff < 0 {
		diff *= -1
		for i := 0; i < diff; i++ {
			err := CreatePod(ctx, rs.Namespace, &rs.Spec.Template, rs, metav1.NewControllerRef(rs, apps.SchemeGroupVersion.WithKind("ReplicaSet")))
			if err != nil {
				return err
			}
		}
	} else if diff > 0 {
		relatedPods, _ := getIndirectlyRelatedPods(logger, rs)
		// Choose which Pods to delete, preferring those in earlier phases of startup.
		podsToDelete := getPodsToDelete(activePods, relatedPods, diff)
		for _, pod := range podsToDelete {
			if err := simpleapiserver.PodDelete(rs.Namespace, pod.Name); err != nil {
				if !apierrors.IsNotFound(err) {
					return err
				}
			}
		}
	}

	return nil
}

// syncReplicaSet will sync the ReplicaSet with the given key if it has had its expectations fulfilled,
// meaning it did not expect to see any more of its pods created or deleted. This function is not meant to be
// invoked concurrently with the same key.
func syncReplicaSet(ctx context.Context, key string) error {
	logger := klog.FromContext(ctx)

	namespace, name, err := cache.SplitMetaNamespaceKey(key)
	if err != nil {
		return err
	}
	rs, err := simpleapiserver.ReplicaSetGet(namespace, name)
	if apierrors.IsNotFound(err) {
		return nil
	}
	if err != nil {
		return err
	}

	// List all pods indexed to RS UID and Orphan pods
	allRSPods, err := FilterPodsByOwner(&rs.ObjectMeta)
	if err != nil {
		return err
	}

	// NOTE: activePods and terminatingPods are pointing to objects from cache - if you need to
	// modify them, you need to copy it first.
	allActivePods := controller.FilterActivePods(logger, allRSPods)

	var manageReplicasErr error
	if rs.DeletionTimestamp == nil {
		manageReplicasErr = manageReplicas(ctx, allActivePods, rs)
	}

	return manageReplicasErr
}

// getIndirectlyRelatedPods returns all pods that are owned by any ReplicaSet
// that is owned by the given ReplicaSet's owner.
func getIndirectlyRelatedPods(logger klog.Logger, rs *apps.ReplicaSet) ([]*v1.Pod, error) {
	var relatedPods []*v1.Pod
	seen := make(map[types.UID]*apps.ReplicaSet)
	for _, relatedRS := range getReplicaSetsWithSameController(logger, rs) {
		selector, err := metav1.LabelSelectorAsSelector(relatedRS.Spec.Selector)
		if err != nil {
			// This object has an invalid selector, it does not match any pods
			continue
		}
		pods, err := simpleapiserver.PodList(relatedRS.Namespace, selector)
		if err != nil {
			return nil, err
		}
		for _, pod := range pods {
			if _, found := seen[pod.UID]; found {
				continue
			}
			seen[pod.UID] = relatedRS
			relatedPods = append(relatedPods, pod)
		}
	}
	return relatedPods, nil
}

func getPodsRankedByRelatedPodsOnSameNode(podsToRank, relatedPods []*v1.Pod) controller.ActivePodsWithRanks {
	podsOnNode := make(map[string]int)
	for _, pod := range relatedPods {
		if controller.IsPodActive(pod) {
			podsOnNode[pod.Spec.NodeName]++
		}
	}
	ranks := make([]int, len(podsToRank))
	for i, pod := range podsToRank {
		ranks[i] = podsOnNode[pod.Spec.NodeName]
	}
	return controller.ActivePodsWithRanks{Pods: podsToRank, Rank: ranks, Now: metav1.Now()}
}

func getPodsToDelete(filteredPods, relatedPods []*v1.Pod, diff int) []*v1.Pod {
	// No need to sort pods if we are about to delete all of them.
	// diff will always be <= len(filteredPods), so not need to handle > case.
	if diff < len(filteredPods) {
		podsWithRanks := getPodsRankedByRelatedPodsOnSameNode(filteredPods, relatedPods)
		sort.Sort(podsWithRanks)
	}
	return filteredPods[:diff]
}
