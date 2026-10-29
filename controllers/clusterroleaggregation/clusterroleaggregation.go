package clusterroleaggregation

import (
	"context"
	"sort"

	rbacv1 "k8s.io/api/rbac/v1"
	"k8s.io/apimachinery/pkg/api/equality"
	apierrors "k8s.io/apimachinery/pkg/api/errors"
	metav1 "k8s.io/apimachinery/pkg/apis/meta/v1"
	clientset "k8s.io/client-go/kubernetes"
	rbaclisters "k8s.io/client-go/listers/rbac/v1"
)

// A simplified clusterroleaggregation controller. The following features are not included:
// * informer event handling and workqueue scheduling
// * cache-key parsing and controller worker lifecycle
// * server-side apply (writes use upstream's Update fallback)
//
// Reads come from the ClusterRole lister and writes go through client-go.
// Selectors are processed in order, matching ClusterRoles are sorted by name
// within each selector, the aggregating ClusterRole itself is excluded, duplicate
// PolicyRules are removed, and the ClusterRole is updated only when its rules differ
// from the desired rules.

func syncClusterRole(ctx context.Context, kubeClient *clientset.Clientset, clusterRoleLister rbaclisters.ClusterRoleLister, name string) error {
	sharedClusterRole, err := clusterRoleLister.Get(name)
	if apierrors.IsNotFound(err) {
		return nil
	}
	if err != nil {
		return err
	}
	if sharedClusterRole.AggregationRule == nil {
		return nil
	}

	newPolicyRules := []rbacv1.PolicyRule{}

	for i := range sharedClusterRole.AggregationRule.ClusterRoleSelectors {
		selector := sharedClusterRole.AggregationRule.ClusterRoleSelectors[i]
		runtimeLabelSelector, err := metav1.LabelSelectorAsSelector(&selector)
		if err != nil {
			return err
		}
		clusterRoles, err := clusterRoleLister.List(runtimeLabelSelector)
		if err != nil {
			return err
		}
		sort.Sort(byName(clusterRoles))

		for i := range clusterRoles {
			if clusterRoles[i].Name == sharedClusterRole.Name {
				continue
			}
			for j := range clusterRoles[i].Rules {
				currRule := clusterRoles[i].Rules[j]
				if !ruleExists(newPolicyRules, currRule) {
					newPolicyRules = append(newPolicyRules, currRule)
				}
			}
		}
	}

	if equality.Semantic.DeepEqual(newPolicyRules, sharedClusterRole.Rules) {
		return nil
	}

	updated := sharedClusterRole.DeepCopy()
	updated.Rules = newPolicyRules

	var updateOptions metav1.UpdateOptions
	_, err = kubeClient.RbacV1().ClusterRoles().Update(ctx, updated, updateOptions)
	return err
}

type byName []*rbacv1.ClusterRole

func (r byName) Len() int {
	return len(r)
}

func (r byName) Less(i, j int) bool {
	return r[i].Name < r[j].Name
}

func (r byName) Swap(i, j int) {
	r[i], r[j] = r[j], r[i]
}

func ruleExists(rules []rbacv1.PolicyRule, rule rbacv1.PolicyRule) bool {
	for i := range rules {
		if equality.Semantic.DeepEqual(rules[i], rule) {
			return true
		}
	}
	return false
}
