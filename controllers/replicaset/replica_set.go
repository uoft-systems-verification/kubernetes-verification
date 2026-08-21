package replicaset

import (
	"controllers/common"
	"kubernetes_model/apimodel"
	"sort"

	apps "k8s.io/api/apps/v1"
	v1 "k8s.io/api/core/v1"
	apierrors "k8s.io/apimachinery/pkg/api/errors"
	metav1 "k8s.io/apimachinery/pkg/apis/meta/v1"
	"k8s.io/apimachinery/pkg/labels"
	"k8s.io/apimachinery/pkg/types"
	"k8s.io/kubernetes/pkg/controller"
)

// A simplified replicaset controller. The following features are not included:
// * adoption and release
// * managing status
// * concurrent creation/deletion

// getReplicaSetsWithSameController returns the ReplicaSets in rs's namespace
// that have the same controller owner as rs.
func getReplicaSetsWithSameController(rs *apps.ReplicaSet) ([]*apps.ReplicaSet, error) {
	controllerRef := metav1.GetControllerOf(rs)
	if controllerRef == nil {
		return nil, nil
	}

	replicaSets, err := apimodel.ModelState.ReplicaSetList(rs.Namespace, labels.Everything())
	if err != nil {
		return nil, err
	}
	relatedReplicaSets := make([]*apps.ReplicaSet, 0, len(replicaSets))
	for _, relatedRS := range replicaSets {
		relatedControllerRef := metav1.GetControllerOf(relatedRS)
		if relatedControllerRef != nil && relatedControllerRef.UID == controllerRef.UID {
			relatedReplicaSets = append(relatedReplicaSets, relatedRS)
		}
	}
	return relatedReplicaSets, nil
}

// getIndirectlyRelatedPods returns all pods that are owned by a ReplicaSet
// with the same controller owner as rs.
func getIndirectlyRelatedPods(rs *apps.ReplicaSet) ([]*v1.Pod, error) {
	relatedReplicaSets, err := getReplicaSetsWithSameController(rs)
	if err != nil {
		return nil, err
	}

	relatedPods := []*v1.Pod{}
	seen := make(map[types.UID]*apps.ReplicaSet)
	for _, relatedRS := range relatedReplicaSets {
		selector, err := metav1.LabelSelectorAsSelector(relatedRS.Spec.Selector)
		if err != nil {
			// An invalid selector does not match any pods.
			continue
		}
		pods, err := apimodel.ModelState.PodList(relatedRS.Namespace, selector)
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

func getPodsToDelete(filteredPods, relatedPods []*v1.Pod, diff int) []*v1.Pod {
	// diff is always at most len(filteredPods), and sorting is unnecessary when
	// every filtered pod will be deleted.
	if diff < len(filteredPods) {
		podsWithRanks := getPodsRankedByRelatedPodsOnSameNode(filteredPods, relatedPods)
		sort.Sort(podsWithRanks)
	}
	return filteredPods[:diff]
}

// getPodsRankedByRelatedPodsOnSameNode ranks each pod by the number of active
// related pods colocated on its node.
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

func manageReplicas(activePods []*v1.Pod, rs *apps.ReplicaSet) error {
	diff := len(activePods) - int(*(rs.Spec.Replicas))
	if diff < 0 {
		diff *= -1
		for i := 0; i < diff; i++ {
			pod, err := controller.GetPodFromTemplate(&rs.Spec.Template, rs, metav1.NewControllerRef(rs, apps.SchemeGroupVersion.WithKind("ReplicaSet")))
			if err != nil {
				return err
			}
			_, err = apimodel.ModelState.PodCreate(rs.ObjectMeta.GetNamespace(), pod)
			if err != nil {
				return err
			}
		}
	} else if diff > 0 {
		relatedPods, err := getIndirectlyRelatedPods(rs)
		if err != nil {
			return err
		}
		podsToDelete := getPodsToDelete(activePods, relatedPods, diff)
		for _, pod := range podsToDelete {
			uid := pod.ObjectMeta.GetUID()
			if err := apimodel.ModelState.PodDelete(pod.ObjectMeta.GetNamespace(), pod.ObjectMeta.GetName(), common.NewDeleteOptionsWithUID(uid)); err != nil {
				if !apierrors.IsNotFound(err) {
					return err
				}
			}
		}
	}

	return nil
}

func syncReplicaSet(namespace, name string) error {
	rs, err := apimodel.ModelState.ReplicaSetGet(namespace, name)
	if apierrors.IsNotFound(err) {
		return nil
	}
	if err != nil {
		return err
	}

	allRSPods, err := common.FilterPodsByOwner(&rs.ObjectMeta, "ReplicaSet")
	if err != nil {
		return err
	}

	allActivePods := common.FilterActivePods(allRSPods)

	var manageReplicasErr error
	if rs.DeletionTimestamp == nil {
		manageReplicasErr = manageReplicas(allActivePods, rs)
	}

	return manageReplicasErr
}
