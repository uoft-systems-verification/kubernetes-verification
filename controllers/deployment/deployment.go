package deployment

import (
	"reflect"

	"kubernetes_model/apimodel"

	apps "k8s.io/api/apps/v1"
	v1 "k8s.io/api/core/v1"
	apierrors "k8s.io/apimachinery/pkg/api/errors"
	metav1 "k8s.io/apimachinery/pkg/apis/meta/v1"
	"k8s.io/apimachinery/pkg/labels"
	"k8s.io/kubernetes/pkg/controller"
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

const deploymentUniqueLabelKey = "pod-template-hash"

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

// equalIgnoreHash reports whether two pod templates are equal ignoring the
// pod-template-hash label.
func equalIgnoreHash(template1, template2 *v1.PodTemplateSpec) bool {
	t1 := template1.DeepCopy()
	t2 := template2.DeepCopy()
	delete(t1.Labels, deploymentUniqueLabelKey)
	delete(t2.Labels, deploymentUniqueLabelKey)
	return reflect.DeepEqual(t1, t2)
}

// findNewReplicaSet returns the ReplicaSet whose template matches the
// deployment's (ignoring the hash label). Under the no-collision assumption at
// most one such ReplicaSet exists.
func findNewReplicaSet(d *apps.Deployment, rsList []*apps.ReplicaSet) *apps.ReplicaSet {
	for _, rs := range rsList {
		if equalIgnoreHash(&rs.Spec.Template, &d.Spec.Template) {
			return rs
		}
	}
	return nil
}

// findOldReplicaSets returns every ReplicaSet other than newRS.
func findOldReplicaSets(rsList []*apps.ReplicaSet, newRS *apps.ReplicaSet) []*apps.ReplicaSet {
	old := []*apps.ReplicaSet{}
	for _, rs := range rsList {
		if newRS != nil && rs.UID == newRS.UID {
			continue
		}
		old = append(old, rs)
	}
	return old
}

func cloneAndAddLabel(existing map[string]string, key, value string) map[string]string {
	result := map[string]string{}
	for k, v := range existing {
		result[k] = v
	}
	result[key] = value
	return result
}

func cloneSelectorAndAddLabel(selector *metav1.LabelSelector, key, value string) *metav1.LabelSelector {
	newSelector := selector.DeepCopy()
	if newSelector.MatchLabels == nil {
		newSelector.MatchLabels = map[string]string{}
	}
	newSelector.MatchLabels[key] = value
	return newSelector
}

// scaleReplicaSet sets a ReplicaSet's replica count. It is a no-op (and reports
// scaled=false) when the count already matches.
func scaleReplicaSet(rs *apps.ReplicaSet, newScale int32) (bool, *apps.ReplicaSet, error) {
	if replicasOfRS(rs) == newScale {
		return false, rs, nil
	}
	rsCopy := rs.DeepCopy()
	rsCopy.Spec.Replicas = &newScale
	updated, err := apimodel.ModelState.ReplicaSetUpdate(rsCopy.Namespace, rsCopy)
	if err != nil {
		return false, rs, err
	}
	return true, updated, nil
}

// getNewReplicaSet returns the deployment's new ReplicaSet, creating it with a
// deterministic name and the deployment's replica count if it does not exist.
func getNewReplicaSet(d *apps.Deployment, rsList []*apps.ReplicaSet) (*apps.ReplicaSet, error) {
	existingNewRS := findNewReplicaSet(d, rsList)
	if existingNewRS != nil {
		return existingNewRS, nil
	}

	newRSTemplate := *d.Spec.Template.DeepCopy()
	podTemplateSpecHash := controller.ComputeHash(&newRSTemplate, nil)
	newRSTemplate.Labels = cloneAndAddLabel(d.Spec.Template.Labels, deploymentUniqueLabelKey, podTemplateSpecHash)
	newRSSelector := cloneSelectorAndAddLabel(d.Spec.Selector, deploymentUniqueLabelKey, podTemplateSpecHash)

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

	createdRS, err := apimodel.ModelState.ReplicaSetCreate(d.Namespace, newRS)
	if apierrors.IsAlreadyExists(err) {
		// No-collision assumption: a ReplicaSet with this deterministic name
		// already holds the same template, so adopt it.
		return apimodel.ModelState.ReplicaSetGet(d.Namespace, newRS.Name)
	}
	if err != nil {
		return nil, err
	}
	return createdRS, nil
}

// reconcileNewReplicaSet scales the new ReplicaSet to the deployment's desired
// replica count.
func reconcileNewReplicaSet(newRS *apps.ReplicaSet, d *apps.Deployment) (bool, error) {
	scaled, _, err := scaleReplicaSet(newRS, replicasOf(d))
	return scaled, err
}

// reconcileOldReplicaSets scales every old ReplicaSet down to zero.
func reconcileOldReplicaSets(oldRSs []*apps.ReplicaSet) (bool, error) {
	scaledDown := false
	for _, rs := range oldRSs {
		scaled, _, err := scaleReplicaSet(rs, 0)
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
func rollout(d *apps.Deployment, rsList []*apps.ReplicaSet) error {
	newRS, err := getNewReplicaSet(d, rsList)
	if err != nil {
		return err
	}
	oldRSs := findOldReplicaSets(rsList, newRS)

	_, err = reconcileNewReplicaSet(newRS, d)
	if err != nil {
		return err
	}

	_, err = reconcileOldReplicaSets(oldRSs)
	return err
}

// filterReplicaSetsByOwner returns the ReplicaSets in the deployment's namespace
// whose controller reference points at the deployment.
func filterReplicaSetsByOwner(d *apps.Deployment) ([]*apps.ReplicaSet, error) {
	all, err := apimodel.ModelState.ReplicaSetList(d.Namespace, labels.Everything())
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

func syncDeployment(namespace, name string) error {
	d, err := apimodel.ModelState.DeploymentGet(namespace, name)
	if apierrors.IsNotFound(err) {
		return nil
	}
	if err != nil {
		return err
	}

	rsList, err := filterReplicaSetsByOwner(d)
	if err != nil {
		return err
	}

	if d.DeletionTimestamp != nil {
		return nil
	}

	return rollout(d, rsList)
}
