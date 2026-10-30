package replicaset

import (
	"context"
	"controllers/common"
	"errors"
	"kubernetes_model/apimodel"
	"sort"
	"sync"

	apps "k8s.io/api/apps/v1"
	v1 "k8s.io/api/core/v1"
	apierrors "k8s.io/apimachinery/pkg/api/errors"
	metav1 "k8s.io/apimachinery/pkg/apis/meta/v1"
	"k8s.io/apimachinery/pkg/labels"
	"k8s.io/apimachinery/pkg/runtime/schema"
	"k8s.io/apimachinery/pkg/types"
	utilerrors "k8s.io/apimachinery/pkg/util/errors"
	utilfeature "k8s.io/apiserver/pkg/util/feature"
	clientset "k8s.io/client-go/kubernetes"
	appslisters "k8s.io/client-go/listers/apps/v1"
	// "k8s.io/klog/v2"
	"k8s.io/kubernetes/pkg/controller"
	upstreamrs "k8s.io/kubernetes/pkg/controller/replicaset"
	"k8s.io/kubernetes/pkg/features"
	"k8s.io/utils/clock"
)

// A simplified replicaset controller. The following features are not included:
// * expectations, informers and the work queue
// * scheduling the next availability check

const (
	// The number of times we retry updating a ReplicaSet's status.
	statusUpdateRetries = 1
)

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

func manageReplicas(ctx context.Context, kubeClient *clientset.Clientset, burstReplicas int, activePods []*v1.Pod, rs *apps.ReplicaSet) error {
	diff := len(activePods) - int(*(rs.Spec.Replicas))
	if diff < 0 {
		diff *= -1
		if diff > burstReplicas {
			diff = burstReplicas
		}
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
			// Kept for consistency with upstream, but vacuous under verification: the
			// API model's Create never returns an error, so this branch is never
			// taken in the proofs and HasStatusCause needs no specification.
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
		if diff > burstReplicas {
			diff = burstReplicas
		}

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

func syncReplicaSet(ctx context.Context, kubeClient *clientset.Clientset, rsLister appslisters.ReplicaSetLister, burstReplicas int, rscClock clock.PassiveClock, controllerFeatures upstreamrs.ReplicaSetControllerFeatures, namespace, name string) error {
	// Logging never affects the verified behavior, so the logger is omitted.
	// logger := klog.FromContext(ctx)
	// use <namespace, name> localize a unique ReplicaSet
	rs, err := rsLister.ReplicaSets(namespace).Get(name)
	if apierrors.IsNotFound(err) {
		return nil
	}
	if err != nil {
		return err
	}

	selector, err := metav1.LabelSelectorAsSelector(rs.Spec.Selector)
	if err != nil {
		// Upstream also reports the error with utilruntime.HandleError.
		return nil
	}

	// List all pods indexed to RS UID and Orphan pods
	allRSPods, err := common.FilterPodsByOwner(&rs.ObjectMeta, "ReplicaSet", true)
	if err != nil {
		return err
	}

	// NOTE: activePods and terminatingPods are pointing to objects from cache - if you need to
	// modify them, you need to copy it first.
	allActivePods := common.FilterActivePods(allRSPods)
	activePods, err := claimPods(ctx, kubeClient, rs, selector, allActivePods)
	if err != nil {
		return err
	}

	var terminatingPods []*v1.Pod
	if utilfeature.DefaultFeatureGate.Enabled(features.DeploymentReplicaSetTerminatingReplicas) && controllerFeatures.EnableStatusTerminatingReplicas {
		allTerminatingPods := controller.FilterTerminatingPods(allRSPods)
		terminatingPods = controller.FilterClaimedPods(rs, selector, allTerminatingPods)
	}

	var manageReplicasErr error
	if rs.DeletionTimestamp == nil {
		manageReplicasErr = manageReplicas(ctx, kubeClient, burstReplicas, activePods, rs)
	}
	rs = rs.DeepCopy()
	// Keep one time for status and the future next-availability-check calculation.
	now := rscClock.Now()
	newStatus := calculateStatus(rs, activePods, terminatingPods, manageReplicasErr, controllerFeatures, now)

	// Always updates status as pods come up or die. The updated object will also
	// be used when availability requeue scheduling is added.
	_, err = updateReplicaSetStatus(kubeClient.AppsV1().ReplicaSets(rs.Namespace), rs, newStatus)
	if err != nil {
		return err
	}

	return manageReplicasErr
}

// claimPods is upstream's ReplicaSetController.claimPods. Its getObject
// function reports a different UID with errors.New instead of fmt.Errorf, and
// the manager takes no podControl (see PodControllerRefManager).
func claimPods(ctx context.Context, kubeClient *clientset.Clientset, rs *apps.ReplicaSet, selector labels.Selector, filteredPods []*v1.Pod) ([]*v1.Pod, error) {
	// If any adoptions are attempted, we should first recheck for deletion with
	// an uncached quorum read sometime after listing Pods (see #42639).
	canAdoptFunc := RecheckDeletionTimestamp(func(ctx context.Context) (metav1.Object, error) {
		fresh, err := kubeClient.AppsV1().ReplicaSets(rs.Namespace).Get(ctx, rs.Name, metav1.GetOptions{})
		if err != nil {
			return nil, err
		}
		if fresh.UID != rs.UID {
			return nil, errors.New("original ReplicaSet is gone")
		}
		return fresh, nil
	})
	cm := NewPodControllerRefManager(rs, selector, apps.SchemeGroupVersion.WithKind("ReplicaSet"), canAdoptFunc)
	return cm.ClaimPods(ctx, filteredPods)
}

// RecheckDeletionTimestamp returns a CanAdopt() function to recheck deletion.
//
// The CanAdopt() function calls getObject() to fetch the latest value,
// and denies adoption attempts if that object has a non-nil DeletionTimestamp.
//
// This is upstream's controller.RecheckDeletionTimestamp with errors.New in
// place of fmt.Errorf, whose Perennial specification is admitted. Like
// upstream's "%v", errors.New keeps a NotFound error from getObject from
// reaching ClaimObject, which would ignore it as a NotFound Pod.
func RecheckDeletionTimestamp(getObject func(context.Context) (metav1.Object, error)) func(context.Context) error {
	return func(ctx context.Context) error {
		obj, err := getObject(ctx)
		if err != nil {
			return errors.New("can't recheck DeletionTimestamp")
		}
		if obj.GetDeletionTimestamp() != nil {
			return errors.New("object has just been deleted")
		}
		return nil
	}
}

// PodControllerRefManager is upstream's controller.PodControllerRefManager,
// built on upstream's BaseControllerRefManager. It has no podControl, because
// AdoptPod and ReleasePod update a copy of the Pod with PodUpdateTx instead of
// sending upstream's strategic-merge patch with podControl.PatchPod.
// PodUpdateTx has a Rocq specification, while the model's PodPatch has none
// and takes JSON bytes. Unlike the patch, the update overwrites changes made
// to the Pod since it was listed, including another controller's adoption, and
// it retries forever if the Pod was deleted and recreated under the same name.
// It also has no finalizers, which the ReplicaSet controller does not use.
type PodControllerRefManager struct {
	controller.BaseControllerRefManager
	controllerKind schema.GroupVersionKind
}

// NewPodControllerRefManager returns a PodControllerRefManager that exposes
// methods to manage the controllerRef of pods.
//
// The CanAdopt() function can be used to perform a potentially expensive check
// (such as a live GET from the API server) prior to the first adoption.
// It will only be called (at most once) if an adoption is actually attempted.
// If CanAdopt() returns a non-nil error, all adoptions will fail.
//
// NOTE: Once CanAdopt() is called, it will not be called again by the same
// PodControllerRefManager instance. Create a new instance if it makes
// sense to check CanAdopt() again (e.g. in a different sync pass).
func NewPodControllerRefManager(
	controllerObject metav1.Object,
	selector labels.Selector,
	controllerKind schema.GroupVersionKind,
	canAdopt func(ctx context.Context) error,
) *PodControllerRefManager {
	return &PodControllerRefManager{
		BaseControllerRefManager: controller.BaseControllerRefManager{
			Controller:   controllerObject,
			Selector:     selector,
			CanAdoptFunc: canAdopt,
		},
		controllerKind: controllerKind,
	}
}

// ClaimPods tries to take ownership of a list of Pods.
//
// It will reconcile the following:
//   - Adopt orphans if the selector matches.
//   - Release owned objects if the selector no longer matches.
//
// Optional: If one or more filters are specified, a Pod will only be claimed if
// all filters return true.
//
// A non-nil error is returned if some form of reconciliation was attempted and
// failed. Usually, controllers should try again later in case reconciliation
// is still needed.
//
// If the error is nil, either the reconciliation succeeded, or no
// reconciliation was necessary. The list of Pods that you now own is returned.
func (m *PodControllerRefManager) ClaimPods(ctx context.Context, pods []*v1.Pod, filters ...func(*v1.Pod) bool) ([]*v1.Pod, error) {
	var claimed []*v1.Pod
	var errlist []error

	match := func(obj metav1.Object) bool {
		pod := obj.(*v1.Pod)
		// Check selector first so filters only run on potentially matching Pods.
		if !m.Selector.Matches(labels.Set(pod.Labels)) {
			return false
		}
		for _, filter := range filters {
			if !filter(pod) {
				return false
			}
		}
		return true
	}
	adopt := func(ctx context.Context, obj metav1.Object) error {
		return m.AdoptPod(ctx, obj.(*v1.Pod))
	}
	release := func(ctx context.Context, obj metav1.Object) error {
		return m.ReleasePod(ctx, obj.(*v1.Pod))
	}

	for _, pod := range pods {
		ok, err := m.ClaimObject(ctx, pod, match, adopt, release)
		if err != nil {
			errlist = append(errlist, err)
			continue
		}
		if ok {
			claimed = append(claimed, pod)
		}
	}
	return claimed, utilerrors.NewAggregate(errlist)
}

// AdoptPod updates the pod to take control of it. It returns the error if the
// update fails. Upstream's patch merges the controller reference into the owner
// references by UID; here any reference with the controller's UID is removed
// and the controller reference is appended, so only its position can differ.
// Upstream wraps the CanAdopt error with fmt.Errorf; errors.New likewise
// returns an error that is never NotFound.
func (m *PodControllerRefManager) AdoptPod(ctx context.Context, pod *v1.Pod) error {
	if err := m.CanAdopt(ctx); err != nil {
		return errors.New("can't adopt Pod")
	}
	updatedPod := pod.DeepCopy()
	updatedPod.OwnerReferences = append(withoutOwnerReferences(updatedPod.OwnerReferences, m.Controller.GetUID()),
		*metav1.NewControllerRef(m.Controller, m.controllerKind))
	_, err := apimodel.ModelState.PodUpdateTx(updatedPod.Namespace, updatedPod)
	return err
}

// ReleasePod updates the pod to free it from the control of the controller.
// It returns the error if the update fails. 404 and 422 errors are ignored.
func (m *PodControllerRefManager) ReleasePod(ctx context.Context, pod *v1.Pod) error {
	// Logging never affects the verified behavior, so the logger is omitted.
	updatedPod := pod.DeepCopy()
	updatedPod.OwnerReferences = withoutOwnerReferences(updatedPod.OwnerReferences, m.Controller.GetUID())
	_, err := apimodel.ModelState.PodUpdateTx(updatedPod.Namespace, updatedPod)
	if err != nil {
		if apierrors.IsNotFound(err) {
			// If the pod no longer exists, ignore it.
			return nil
		}
		if apierrors.IsInvalid(err) {
			// Upstream's patch fails with Invalid when the pod has no owner
			// reference or was deleted and recreated. PodUpdateTx fails with
			// Invalid only when validation rejects the copy; the pod stays
			// owned, and the next sync tries to release it again.
			return nil
		}
	}
	return err
}

// withoutOwnerReferences returns ownerReferences without the references to uid.
func withoutOwnerReferences(ownerReferences []metav1.OwnerReference, uid types.UID) []metav1.OwnerReference {
	result := []metav1.OwnerReference{}
	for _, ownerReference := range ownerReferences {
		if ownerReference.UID != uid {
			result = append(result, ownerReference)
		}
	}
	return result
}
