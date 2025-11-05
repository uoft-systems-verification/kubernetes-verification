package simplereplicaset

import (
	"context"
	"fmt"
	"kubernetes_model/simpleapiserver"
	"sort"
	"sync"

	apps "k8s.io/api/apps/v1"
	v1 "k8s.io/api/core/v1"
	apierrors "k8s.io/apimachinery/pkg/api/errors"
	metav1 "k8s.io/apimachinery/pkg/apis/meta/v1"
	"k8s.io/apimachinery/pkg/labels"
	"k8s.io/apimachinery/pkg/runtime/schema"
	"k8s.io/apimachinery/pkg/types"
	utilruntime "k8s.io/apimachinery/pkg/util/runtime"
	"k8s.io/client-go/tools/cache"
	"k8s.io/klog/v2"
	"k8s.io/kubernetes/pkg/controller"
)

// ReplicaSetController is responsible for synchronizing ReplicaSet objects stored
// in the system with actual running pods.
type ReplicaSetController struct {
	// GroupVersionKind indicates the controller type.
	// Different instances of this struct may handle different GVKs.
	// For example, this struct can be used (with adapters) to handle ReplicationController.
	schema.GroupVersionKind

	// A ReplicaSet is temporarily suspended after creating/deleting these many replicas.
	// It resumes normal action after observing the watch events for them.
	burstReplicas int
}

func validateControllerRef(controllerRef *metav1.OwnerReference) error {
	if controllerRef == nil {
		return fmt.Errorf("controllerRef is nil")
	}
	if len(controllerRef.APIVersion) == 0 {
		return fmt.Errorf("controllerRef has empty APIVersion")
	}
	if len(controllerRef.Kind) == 0 {
		return fmt.Errorf("controllerRef has empty Kind")
	}
	if controllerRef.Controller == nil || !*controllerRef.Controller {
		return fmt.Errorf("controllerRef.Controller is not set to true")
	}
	if controllerRef.BlockOwnerDeletion == nil || !*controllerRef.BlockOwnerDeletion {
		return fmt.Errorf("controllerRef.BlockOwnerDeletion is not set")
	}
	return nil
}

func CreatePods(ctx context.Context, namespace string, template *v1.PodTemplateSpec, controllerObject *apps.ReplicaSet, controllerRef *metav1.OwnerReference) error {
	return CreatePodsWithGenerateName(ctx, namespace, template, controllerObject, controllerRef, "")
}

func CreatePodsWithGenerateName(ctx context.Context, namespace string, template *v1.PodTemplateSpec, controllerObject *apps.ReplicaSet, controllerRef *metav1.OwnerReference, generateName string) error {
	if err := validateControllerRef(controllerRef); err != nil {
		return err
	}
	pod, err := controller.GetPodFromTemplate(template, controllerObject, controllerRef)
	if err != nil {
		return err
	}
	if len(generateName) > 0 {
		pod.ObjectMeta.GenerateName = generateName
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
				utilruntime.HandleError(fmt.Errorf("unexpected object type in pod indexer: %v", obj))
				continue
			}
			result = append(result, pod)
		}
	}
	return result, nil
}

func (rsc *ReplicaSetController) getReplicaSetsWithSameController(logger klog.Logger, rs *apps.ReplicaSet) []*apps.ReplicaSet {
	controllerRef := metav1.GetControllerOf(rs)
	if controllerRef == nil {
		utilruntime.HandleError(fmt.Errorf("ReplicaSet has no controller: %v", rs))
		return nil
	}

	objects, err := simpleapiserver.ByIndex("ReplicaSet", simpleapiserver.ControllerUIDIndex, string(controllerRef.UID))
	if err != nil {
		utilruntime.HandleError(err)
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
func (rsc *ReplicaSetController) manageReplicas(ctx context.Context, activePods []*v1.Pod, rs *apps.ReplicaSet) error {
	diff := len(activePods) - int(*(rs.Spec.Replicas))
	_, err := controller.KeyFunc(rs)
	if err != nil {
		utilruntime.HandleError(fmt.Errorf("couldn't get key for %v %#v: %v", rsc.Kind, rs, err))
		return nil
	}
	logger := klog.FromContext(ctx)
	if diff < 0 {
		diff *= -1
		if diff > rsc.burstReplicas {
			diff = rsc.burstReplicas
		}
		// TODO: Track UIDs of creates just like deletes. The problem currently
		// is we'd need to wait on the result of a create to record the pod's
		// UID, which would require locking *across* the create, which will turn
		// into a performance bottleneck. We should generate a UID for the pod
		// beforehand and store it via ExpectCreations.
		logger.V(2).Info("Too few replicas", "replicaSet", klog.KObj(rs), "need", *(rs.Spec.Replicas), "creating", diff)
		// Batch the pod creates. Batch sizes start at SlowStartInitialBatchSize
		// and double with each successful iteration in a kind of "slow start".
		// This handles attempts to start large numbers of pods that would
		// likely all fail with the same error. For example a project with a
		// low quota that attempts to create a large number of pods will be
		// prevented from spamming the API service with the pod create requests
		// after one of its pods fails.  Conveniently, this also prevents the
		// event spam that those failures would generate.
		_, err := slowStartBatch(diff, controller.SlowStartInitialBatchSize, func() error {
			err := CreatePods(ctx, rs.Namespace, &rs.Spec.Template, rs, metav1.NewControllerRef(rs, rsc.GroupVersionKind))
			if err != nil {
				if apierrors.HasStatusCause(err, v1.NamespaceTerminatingCause) {
					// if the namespace is being terminated, we don't have to do
					// anything because any creation will fail
					return nil
				}
			}
			return err
		})

		return err
	} else if diff > 0 {
		if diff > rsc.burstReplicas {
			diff = rsc.burstReplicas
		}
		logger.V(2).Info("Too many replicas", "replicaSet", klog.KObj(rs), "need", *(rs.Spec.Replicas), "deleting", diff)

		relatedPods, err := rsc.getIndirectlyRelatedPods(logger, rs)
		utilruntime.HandleError(err)

		// Choose which Pods to delete, preferring those in earlier phases of startup.
		podsToDelete := getPodsToDelete(activePods, relatedPods, diff)

		errCh := make(chan error, diff)
		var wg sync.WaitGroup
		wg.Add(diff)
		for _, pod := range podsToDelete {
			go func(targetPod *v1.Pod) {
				defer wg.Done()
				if err := simpleapiserver.PodDelete(rs.Namespace, targetPod.Name); err != nil {
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

// syncReplicaSet will sync the ReplicaSet with the given key if it has had its expectations fulfilled,
// meaning it did not expect to see any more of its pods created or deleted. This function is not meant to be
// invoked concurrently with the same key.
func (rsc *ReplicaSetController) syncReplicaSet(ctx context.Context, key string) error {
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
		manageReplicasErr = rsc.manageReplicas(ctx, allActivePods, rs)
	}

	return manageReplicasErr
}

// goose doesn't support Go's built-in min with final type int, so we define our own int
func min(a, b int) int {
	if a <= b {
		return a
	} else {
		return b
	}
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

// getIndirectlyRelatedPods returns all pods that are owned by any ReplicaSet
// that is owned by the given ReplicaSet's owner.
func (rsc *ReplicaSetController) getIndirectlyRelatedPods(logger klog.Logger, rs *apps.ReplicaSet) ([]*v1.Pod, error) {
	var relatedPods []*v1.Pod
	seen := make(map[types.UID]*apps.ReplicaSet)
	for _, relatedRS := range rsc.getReplicaSetsWithSameController(logger, rs) {
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
			if otherRS, found := seen[pod.UID]; found {
				logger.V(5).Info("Pod is owned by both", "pod", klog.KObj(pod), "kind", rsc.Kind, "replicaSets", klog.KObjSlice([]klog.KMetadata{otherRS, relatedRS}))
				continue
			}
			seen[pod.UID] = relatedRS
			relatedPods = append(relatedPods, pod)
		}
	}
	logger.V(4).Info("Found related pods", "kind", rsc.Kind, "replicaSet", klog.KObj(rs), "pods", klog.KObjSlice(relatedPods))
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
