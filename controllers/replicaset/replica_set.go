package replicaset

import (
	"context"
	"controllers/common"
	"kubernetes_model/apimodel"
	"sort"
	"sync"

	apps "k8s.io/api/apps/v1"
	v1 "k8s.io/api/core/v1"
	apierrors "k8s.io/apimachinery/pkg/api/errors"
	metav1 "k8s.io/apimachinery/pkg/apis/meta/v1"
	"k8s.io/apimachinery/pkg/types"
	clientset "k8s.io/client-go/kubernetes"
	appslisters "k8s.io/client-go/listers/apps/v1"
	"k8s.io/kubernetes/pkg/controller"
)

// A simplified replicaset controller. The following features are not included:
// * adoption and release
// * managing status
// * concurrent creation/deletion

// getReplicaSetsWithSameController returns a list of ReplicaSets with the same
// owner as the given ReplicaSet.
func getReplicaSetsWithSameController(rs *apps.ReplicaSet) []*apps.ReplicaSet {
	controllerRef := metav1.GetControllerOf(rs)
	if controllerRef == nil {
		return nil
	}

	objects, err := apimodel.ModelState.ByIndex("ReplicaSet", "controllerUID", string(controllerRef.UID))
	if err != nil {
		return nil
	}
	relatedReplicaSets := make([]*apps.ReplicaSet, 0, len(objects))
	for _, obj := range objects {
		relatedReplicaSets = append(relatedReplicaSets, obj.(*apps.ReplicaSet))
	}
	return relatedReplicaSets
}

// getIndirectlyRelatedPods returns all pods that are owned by a ReplicaSet
// with the same controller owner as rs.
func getIndirectlyRelatedPods(rs *apps.ReplicaSet) ([]*v1.Pod, error) {
	relatedPods := []*v1.Pod{}
	// `seen` works as a `Set` to keep track of pods that have already been considered (Like fingerprints in model checker).
	seen := make(map[types.UID]*apps.ReplicaSet)
	for _, relatedRS := range getReplicaSetsWithSameController(rs) {
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
		// Only count active pods on the node.
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

func manageReplicas(ctx context.Context, kubeClient *clientset.Clientset, activePods []*v1.Pod, rs *apps.ReplicaSet) error {
	diff := len(activePods) - int(*(rs.Spec.Replicas))
	if diff < 0 {
		diff *= -1
		// Batch the pod creates. Batch sizes start at SlowStartInitialBatchSize
		// and double with each successful iteration in a kind of "slow start".
		// This handles attempts to start large numbers of pods that would
		// likely all fail with the same error. For example a project with a
		// low quota that attempts to create a large number of pods will be
		// prevented from spamming the API service with the pod create requests
		// after one of its pods fails.  Conveniently, this also prevents the
		// event spam that those failures would generate.
		_, err := slowStartBatch(diff, controller.SlowStartInitialBatchSize, func() error {
			// Create Pod according to the ReplicaSet's template.
			pod, err := controller.GetPodFromTemplate(&rs.Spec.Template, rs, metav1.NewControllerRef(rs, apps.SchemeGroupVersion.WithKind("ReplicaSet")))
			if err != nil {
				return err
			}
			var createOptions metav1.CreateOptions
			// API request to create the pod, which is different from retriving information locally.
			_, err = kubeClient.CoreV1().Pods(rs.ObjectMeta.GetNamespace()).Create(ctx, pod, createOptions)
			return err
		})
		return err
	} else if diff > 0 {
		relatedPods, err := getIndirectlyRelatedPods(rs)
		if err != nil {
			return err
		}
		// Choose which Pods to delete, preferring those in earlier phases of startup.
		podsToDelete := getPodsToDelete(activePods, relatedPods, diff)

		errCh := make(chan error, diff)
		var wg sync.WaitGroup
		wg.Add(diff)
		for _, pod := range podsToDelete {
			go func(targetPod *v1.Pod) {
				defer wg.Done()
				uid := targetPod.ObjectMeta.GetUID()
				if err := kubeClient.CoreV1().Pods(targetPod.ObjectMeta.GetNamespace()).Delete(ctx, targetPod.ObjectMeta.GetName(), common.NewDeleteOptionsWithUID(uid)); err != nil {
					if !apierrors.IsNotFound(err) {
						errCh <- err
					}
				}
			}(pod)
		}
		wg.Wait()

		select {
		case err := <-errCh:
			// all errors have been reported before and they're likely to be the same, so we'll only return the first one we hit.
			if err != nil {
				return err
			}
		default:
		}
	}

	return nil
}

// slowStartBatch tries to call the provided function a total of 'count' times,
// starting slow to check for errors, then speeding up if calls succeed.
//
// It groups the calls into batches, starting with a group of initialBatchSize.
// Within each batch, it may call the function multiple times concurrently.
//
// If a whole batch succeeds, the next batch may get exponentially larger.
// If there are any failures in a batch, all remaining batches are skipped
// after waiting for the current batch to complete.
//
// It returns the number of successful calls to the function.
func slowStartBatch(count int, initialBatchSize int, fn func() error) (int, error) {
	remaining := count
	successes := 0
	for batchSize := min(remaining, initialBatchSize); batchSize > 0; batchSize = min(2*batchSize, remaining) {
		errCh := make(chan error, batchSize)
		var wg sync.WaitGroup
		wg.Add(batchSize)
		for i := 0; i < batchSize; i++ {
			go func() {
				defer wg.Done()
				if err := fn(); err != nil {
					errCh <- err
				}
			}()
		}
		wg.Wait()
		curSuccesses := batchSize - len(errCh)
		successes += curSuccesses
		if len(errCh) > 0 {
			return successes, <-errCh
		}
		remaining -= batchSize
	}
	return successes, nil
}

func syncReplicaSet(ctx context.Context, kubeClient *clientset.Clientset, rsLister appslisters.ReplicaSetLister, namespace, name string) error {
	// use <namespace, name> localize a unique ReplicaSet
	rs, err := rsLister.ReplicaSets(namespace).Get(name)
	if apierrors.IsNotFound(err) {
		return nil
	}
	if err != nil {
		return err
	}

	// allRSPods, err := common.FilterPodsByOwner(&((*rs).ObjectMeta), "ReplicaSet")
	allRSPods, err := common.FilterPodsByOwner(&rs.ObjectMeta, "ReplicaSet")
	if err != nil {
		return err
	}

	allActivePods := common.FilterActivePods(allRSPods)

	var manageReplicasErr error
	if rs.DeletionTimestamp == nil {
		manageReplicasErr = manageReplicas(ctx, kubeClient, allActivePods, rs)
	}

	return manageReplicasErr
}
