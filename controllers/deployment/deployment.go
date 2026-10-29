package deployment

import (
	"context"

	apps "k8s.io/api/apps/v1"
	apierrors "k8s.io/apimachinery/pkg/api/errors"
	metav1 "k8s.io/apimachinery/pkg/apis/meta/v1"
	"k8s.io/apimachinery/pkg/labels"
	clientset "k8s.io/client-go/kubernetes"
	appslisters "k8s.io/client-go/listers/apps/v1"
	"k8s.io/kubernetes/pkg/controller"
	deploymentutil "k8s.io/kubernetes/pkg/controller/deployment/util"
	labelsutil "k8s.io/kubernetes/pkg/util/labels"
)

// A simplified deployment controller. The following features are not included:
// * adoption and release (ControllerRef reconciliation)
// * managing status and deployment conditions
// * rollback and paused deployments
// * rollout pacing: maxSurge, maxUnavailable, and the rollout strategy are
//   ignored entirely
// * proportional scaling and desired/max-replicas annotations
// * revision history, revision annotations, and old-ReplicaSet cleanup
// * hash-collision handling (a name clash is assumed to be the same template)
// * concurrent creation/deletion
//
// Without pacing, a sync moves straight to the desired state: the new
// ReplicaSet is scaled directly to the deployment's replica count and every old
// ReplicaSet is scaled directly to zero. Pod availability is therefore never
// consulted, which also sidesteps the fact that the simplified ReplicaSet
// controller never writes status.

func replicasOf(d *apps.Deployment) int32 {
	if d.Spec.Replicas == nil {
		return 1
	}
	return *d.Spec.Replicas
}

func replicasOfRS(rs *apps.ReplicaSet) int32 {
	if rs == nil || rs.Spec.Replicas == nil {
		return 0
	}
	return *rs.Spec.Replicas
}

// findNewReplicaSet returns the new RS this given deployment targets (the one
// with the same pod template), as upstream's FindNewReplicaSet does.
//
// TODO: upstream's FindNewReplicaSet first sorts rsList with
// sort.Sort(controller.ReplicaSetsByCreationTimestamp(rsList)) (oldest first,
// ties by name) and so deterministically picks the oldest match. Here the first
// match in list order is taken. Adding the sort needs translations of
// metav1.Time.Before/Equal, time.Time.Before/Equal, and
// ReplicaSetsByCreationTimestamp, plus a spec for sort.Sort, none of which
// exist yet.
func findNewReplicaSet(deployment *apps.Deployment, rsList []*apps.ReplicaSet) *apps.ReplicaSet {
	for i := range rsList {
		if deploymentutil.EqualIgnoreHash(&rsList[i].Spec.Template, &deployment.Spec.Template) {
			return rsList[i]
		}
	}
	// new ReplicaSet does not exist.
	return nil
}

// findOldReplicaSets returns the old replica sets targeted by the given
// Deployment, with the given slice of RSes, as upstream's FindOldReplicaSets
// does.
//
// TODO: upstream returns two slices, (requiredRSs, allRSs), where requiredRSs
// keeps only the old ReplicaSets with *rs.Spec.Replicas != 0. Only allRSs is
// returned here; rollout discards requiredRSs, just as upstream's
// getAllReplicaSetsAndSyncRevision does. Computing it dereferences
// rs.Spec.Replicas, which upstream relies on API defaulting to make non-nil;
// the model does not default it, so the spec would need that as a
// precondition.
func findOldReplicaSets(deployment *apps.Deployment, rsList []*apps.ReplicaSet) []*apps.ReplicaSet {
	var allRSs []*apps.ReplicaSet
	newRS := findNewReplicaSet(deployment, rsList)
	for _, rs := range rsList {
		// Filter out new replica set
		if newRS != nil && rs.UID == newRS.UID {
			continue
		}
		allRSs = append(allRSs, rs)
	}
	return allRSs
}

// scaleReplicaSet sets a ReplicaSet's replica count. It is a no-op (and reports
// scaled=false) when the count already matches.
//
// TODO: upstream's scaleReplicaSet (pkg/controller/deployment/sync.go) also
// takes the deployment, keeps the desired/max-replicas annotations up to date
// (and updates when only they differ), and records a ScalingReplicaSet event.
// This controller models neither annotations nor events. Upstream also reads
// and writes *rs.Spec.Replicas directly, relying on API defaulting to make it
// non-nil; here replicasOfRS treats nil as 0 and the copy gets a fresh pointer.
func scaleReplicaSet(ctx context.Context, kubeClient *clientset.Clientset, rs *apps.ReplicaSet, newScale int32) (bool, *apps.ReplicaSet, error) {
	if replicasOfRS(rs) == newScale {
		return false, rs, nil
	}
	rsCopy := rs.DeepCopy()
	rsCopy.Spec.Replicas = &newScale
	var updateOptions metav1.UpdateOptions
	updated, err := kubeClient.AppsV1().ReplicaSets(rsCopy.Namespace).Update(ctx, rsCopy, updateOptions)
	if err != nil {
		return false, rs, err
	}
	return true, updated, nil
}

// getNewReplicaSet returns the deployment's new ReplicaSet, creating it with a
// deterministic name and the deployment's replica count if it does not exist.
func getNewReplicaSet(ctx context.Context, kubeClient *clientset.Clientset, rsLister appslisters.ReplicaSetLister, d *apps.Deployment, rsList []*apps.ReplicaSet) (*apps.ReplicaSet, error) {
	existingNewRS := findNewReplicaSet(d, rsList)
	if existingNewRS != nil {
		return existingNewRS, nil
	}

	newRSTemplate := *d.Spec.Template.DeepCopy()
	podTemplateSpecHash := controller.ComputeHash(&newRSTemplate, nil)
	newRSTemplate.Labels = labelsutil.CloneAndAddLabel(d.Spec.Template.Labels, apps.DefaultDeploymentUniqueLabelKey, podTemplateSpecHash)
	newRSSelector := labelsutil.CloneSelectorAndAddLabel(d.Spec.Selector, apps.DefaultDeploymentUniqueLabelKey, podTemplateSpecHash)

	replicas := replicasOf(d)
	newRS := &apps.ReplicaSet{
		ObjectMeta: metav1.ObjectMeta{
			Name:            d.Name + "-" + podTemplateSpecHash,
			Namespace:       d.Namespace,
			OwnerReferences: []metav1.OwnerReference{*metav1.NewControllerRef(d, apps.SchemeGroupVersion.WithKind("Deployment"))},
			Labels:          newRSTemplate.Labels,
		},
		Spec: apps.ReplicaSetSpec{
			Replicas:        &replicas,
			MinReadySeconds: d.Spec.MinReadySeconds,
			Selector:        newRSSelector,
			Template:        newRSTemplate,
		},
	}

	var createOptions metav1.CreateOptions
	createdRS, err := kubeClient.AppsV1().ReplicaSets(d.Namespace).Create(ctx, newRS, createOptions)
	if apierrors.IsAlreadyExists(err) {
		// No-collision assumption: a ReplicaSet with this deterministic name
		// already holds the same template. Read it from the lister, as upstream
		// does after AlreadyExists (and return its error if the cache lags).
		return rsLister.ReplicaSets(newRS.Namespace).Get(newRS.Name)
	}
	if err != nil {
		return nil, err
	}
	return createdRS, nil
}

// reconcileNewReplicaSet scales the new ReplicaSet to the deployment's desired
// replica count.
func reconcileNewReplicaSet(ctx context.Context, kubeClient *clientset.Clientset, newRS *apps.ReplicaSet, d *apps.Deployment) (bool, error) {
	scaled, _, err := scaleReplicaSet(ctx, kubeClient, newRS, replicasOf(d))
	return scaled, err
}

// reconcileOldReplicaSets scales every old ReplicaSet down to zero.
func reconcileOldReplicaSets(ctx context.Context, kubeClient *clientset.Clientset, oldRSs []*apps.ReplicaSet) (bool, error) {
	scaledDown := false
	for _, rs := range oldRSs {
		scaled, _, err := scaleReplicaSet(ctx, kubeClient, rs, 0)
		if err != nil {
			return scaledDown, err
		}
		if scaled {
			scaledDown = true
		}
	}
	return scaledDown, nil
}

// rollout performs one reconciliation step of a rollout.
func rollout(ctx context.Context, kubeClient *clientset.Clientset, rsLister appslisters.ReplicaSetLister, d *apps.Deployment, rsList []*apps.ReplicaSet) error {
	oldRSs := findOldReplicaSets(d, rsList)
	newRS, err := getNewReplicaSet(ctx, kubeClient, rsLister, d, rsList)
	if err != nil {
		return err
	}

	_, err = reconcileNewReplicaSet(ctx, kubeClient, newRS, d)
	if err != nil {
		return err
	}

	_, err = reconcileOldReplicaSets(ctx, kubeClient, oldRSs)
	return err
}

// filterReplicaSetsByOwner returns the ReplicaSets in the deployment's namespace
// whose controller reference points at the deployment.
func filterReplicaSetsByOwner(rsLister appslisters.ReplicaSetLister, d *apps.Deployment) ([]*apps.ReplicaSet, error) {
	all, err := rsLister.ReplicaSets(d.Namespace).List(labels.Everything())
	if err != nil {
		return nil, err
	}
	result := []*apps.ReplicaSet{}
	for _, rs := range all {
		ref := metav1.GetControllerOf(rs)
		if ref != nil && ref.UID == d.UID {
			result = append(result, rs)
		}
	}
	return result, nil
}

func syncDeployment(ctx context.Context, kubeClient *clientset.Clientset, dLister appslisters.DeploymentLister, rsLister appslisters.ReplicaSetLister, namespace, name string) error {
	d, err := dLister.Deployments(namespace).Get(name)
	if apierrors.IsNotFound(err) {
		return nil
	}
	if err != nil {
		return err
	}

	rsList, err := filterReplicaSetsByOwner(rsLister, d)
	if err != nil {
		return err
	}

	if d.DeletionTimestamp != nil {
		return nil
	}

	return rollout(ctx, kubeClient, rsLister, d, rsList)
}
