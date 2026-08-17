package clusterroleaggregation

import (
	"testing"

	"kubernetes_model/apimodel"

	rbacv1 "k8s.io/api/rbac/v1"
	"k8s.io/apimachinery/pkg/api/equality"
	metav1 "k8s.io/apimachinery/pkg/apis/meta/v1"
)

func resetModelState(t *testing.T) {
	t.Helper()
	oldState := apimodel.ModelState
	apimodel.ModelState = apimodel.NewState()
	t.Cleanup(func() {
		apimodel.ModelState = oldState
	})
}

func createClusterRole(t *testing.T, clusterRole *rbacv1.ClusterRole) *rbacv1.ClusterRole {
	t.Helper()
	created, err := apimodel.ModelState.ClusterRoleCreate(clusterRole)
	if err != nil {
		t.Fatalf("create ClusterRole %q: %v", clusterRole.Name, err)
	}
	return created
}

func policyRule(verb string) rbacv1.PolicyRule {
	return rbacv1.PolicyRule{
		Verbs:     []string{verb},
		APIGroups: []string{""},
		Resources: []string{"pods"},
	}
}

func aggregationRule(selectors ...metav1.LabelSelector) *rbacv1.AggregationRule {
	return &rbacv1.AggregationRule{ClusterRoleSelectors: selectors}
}

func getClusterRole(t *testing.T, name string) *rbacv1.ClusterRole {
	t.Helper()
	clusterRole, err := apimodel.ModelState.ClusterRoleGet(name)
	if err != nil {
		t.Fatalf("get ClusterRole %q: %v", name, err)
	}
	return clusterRole
}

func TestSyncClusterRoleHappyPath(t *testing.T) {
	resetModelState(t)
	rule := policyRule("get")
	createClusterRole(t, &rbacv1.ClusterRole{
		ObjectMeta: metav1.ObjectMeta{Name: "target"},
		AggregationRule: aggregationRule(metav1.LabelSelector{
			MatchLabels: map[string]string{"aggregate": "true"},
		}),
	})
	createClusterRole(t, &rbacv1.ClusterRole{
		ObjectMeta: metav1.ObjectMeta{
			Name:   "source",
			Labels: map[string]string{"aggregate": "true"},
		},
		Rules: []rbacv1.PolicyRule{rule},
	})

	if err := syncClusterRole("target"); err != nil {
		t.Fatalf("syncClusterRole: %v", err)
	}
	if got := getClusterRole(t, "target").Rules; !equality.Semantic.DeepEqual(got, []rbacv1.PolicyRule{rule}) {
		t.Fatalf("rules = %#v, want %#v", got, []rbacv1.PolicyRule{rule})
	}
}

func TestSyncClusterRoleExcludesSelf(t *testing.T) {
	resetModelState(t)
	createClusterRole(t, &rbacv1.ClusterRole{
		ObjectMeta: metav1.ObjectMeta{
			Name:   "target",
			Labels: map[string]string{"aggregate": "true"},
		},
		AggregationRule: aggregationRule(metav1.LabelSelector{
			MatchLabels: map[string]string{"aggregate": "true"},
		}),
		Rules: []rbacv1.PolicyRule{policyRule("get")},
	})

	if err := syncClusterRole("target"); err != nil {
		t.Fatalf("syncClusterRole: %v", err)
	}
	if got := getClusterRole(t, "target").Rules; len(got) != 0 {
		t.Fatalf("rules = %#v, want no rules", got)
	}
}

func TestSyncClusterRoleDeduplicatesRules(t *testing.T) {
	resetModelState(t)
	rule := policyRule("get")
	createClusterRole(t, &rbacv1.ClusterRole{
		ObjectMeta: metav1.ObjectMeta{Name: "target"},
		AggregationRule: aggregationRule(metav1.LabelSelector{
			MatchLabels: map[string]string{"aggregate": "true"},
		}),
	})
	for _, name := range []string{"source-a", "source-b"} {
		createClusterRole(t, &rbacv1.ClusterRole{
			ObjectMeta: metav1.ObjectMeta{
				Name:   name,
				Labels: map[string]string{"aggregate": "true"},
			},
			Rules: []rbacv1.PolicyRule{rule},
		})
	}

	if err := syncClusterRole("target"); err != nil {
		t.Fatalf("syncClusterRole: %v", err)
	}
	if got := getClusterRole(t, "target").Rules; !equality.Semantic.DeepEqual(got, []rbacv1.PolicyRule{rule}) {
		t.Fatalf("rules = %#v, want one copy of %#v", got, rule)
	}
}

func TestSyncClusterRolePreservesSelectorThenNameOrder(t *testing.T) {
	resetModelState(t)
	getRule := policyRule("get")
	listRule := policyRule("list")
	watchRule := policyRule("watch")
	createClusterRole(t, &rbacv1.ClusterRole{
		ObjectMeta: metav1.ObjectMeta{Name: "target"},
		AggregationRule: aggregationRule(
			metav1.LabelSelector{MatchLabels: map[string]string{"group": "first"}},
			metav1.LabelSelector{MatchLabels: map[string]string{"group": "second"}},
		),
	})
	for _, clusterRole := range []*rbacv1.ClusterRole{
		{ObjectMeta: metav1.ObjectMeta{Name: "z-first", Labels: map[string]string{"group": "first"}}, Rules: []rbacv1.PolicyRule{listRule}},
		{ObjectMeta: metav1.ObjectMeta{Name: "a-first", Labels: map[string]string{"group": "first"}}, Rules: []rbacv1.PolicyRule{getRule}},
		{ObjectMeta: metav1.ObjectMeta{Name: "0-second", Labels: map[string]string{"group": "second"}}, Rules: []rbacv1.PolicyRule{watchRule}},
	} {
		createClusterRole(t, clusterRole)
	}

	if err := syncClusterRole("target"); err != nil {
		t.Fatalf("syncClusterRole: %v", err)
	}
	want := []rbacv1.PolicyRule{getRule, listRule, watchRule}
	if got := getClusterRole(t, "target").Rules; !equality.Semantic.DeepEqual(got, want) {
		t.Fatalf("rules = %#v, want selector order with per-selector name sorting: %#v", got, want)
	}
}

func TestSyncClusterRoleNoOpWhenRulesMatch(t *testing.T) {
	resetModelState(t)
	rule := policyRule("get")
	createClusterRole(t, &rbacv1.ClusterRole{
		ObjectMeta: metav1.ObjectMeta{Name: "target"},
		AggregationRule: aggregationRule(metav1.LabelSelector{
			MatchLabels: map[string]string{"aggregate": "true"},
		}),
		Rules: []rbacv1.PolicyRule{rule},
	})
	createClusterRole(t, &rbacv1.ClusterRole{
		ObjectMeta: metav1.ObjectMeta{Name: "source", Labels: map[string]string{"aggregate": "true"}},
		Rules:      []rbacv1.PolicyRule{rule},
	})
	before := getClusterRole(t, "target")

	if err := syncClusterRole("target"); err != nil {
		t.Fatalf("syncClusterRole: %v", err)
	}
	after := getClusterRole(t, "target")
	if !equality.Semantic.DeepEqual(after.Rules, before.Rules) {
		t.Fatalf("rules changed from %#v to %#v", before.Rules, after.Rules)
	}
	if after.ResourceVersion != before.ResourceVersion {
		t.Fatalf("resourceVersion changed from %q to %q on a no-op sync", before.ResourceVersion, after.ResourceVersion)
	}
}

func TestSyncClusterRoleNilAggregationRule(t *testing.T) {
	resetModelState(t)
	rules := []rbacv1.PolicyRule{policyRule("get")}
	createClusterRole(t, &rbacv1.ClusterRole{
		ObjectMeta: metav1.ObjectMeta{Name: "target"},
		Rules:      rules,
	})
	before := getClusterRole(t, "target")

	if err := syncClusterRole("target"); err != nil {
		t.Fatalf("syncClusterRole: %v", err)
	}
	after := getClusterRole(t, "target")
	if !equality.Semantic.DeepEqual(after.Rules, rules) {
		t.Fatalf("rules = %#v, want %#v", after.Rules, rules)
	}
	if after.ResourceVersion != before.ResourceVersion {
		t.Fatalf("resourceVersion changed from %q to %q with nil aggregationRule", before.ResourceVersion, after.ResourceVersion)
	}
}
