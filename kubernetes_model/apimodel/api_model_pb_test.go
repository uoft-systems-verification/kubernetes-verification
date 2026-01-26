package apimodel

import (
	"context"
	"os"
	"strings"
	"testing"
	"time"

	appsv1 "k8s.io/api/apps/v1"
	corev1 "k8s.io/api/core/v1"
	metav1 "k8s.io/apimachinery/pkg/apis/meta/v1"
	"pgregory.net/rapid"

	"kubernetes_model/pbtesting/comparators"
	"kubernetes_model/pbtesting/generators"
	"kubernetes_model/pbtesting/testserver"
)

// Global test server (initialized once per test run)
var globalTestServer *testserver.TestServer

// setupTestServer initializes the test server.
// By default, uses envtest (API server + etcd only, no controllers).
// Set USE_EXTERNAL_CLUSTER=1 to use an existing cluster via KUBECONFIG.
func setupTestServer(t *testing.T) *testserver.TestServer {
	if globalTestServer != nil {
		return globalTestServer
	}

	useExternal := os.Getenv("USE_EXTERNAL_CLUSTER") == "1"

	server, err := testserver.NewTestServer(testserver.Config{
		Namespace:          "pbt",
		UseExternalCluster: useExternal,
	})
	if err != nil {
		t.Fatalf("Failed to create test server: %v", err)
	}

	// Register cleanup to stop the server when tests finish
	t.Cleanup(func() {
		if globalTestServer != nil {
			_ = globalTestServer.Stop()
			globalTestServer = nil
		}
	})

	globalTestServer = server
	return server
}

// ObjectType represents the type of Kubernetes object to test.
type ObjectType int

const (
	ObjectTypePod ObjectType = iota
	ObjectTypeReplicaSet
)

// TestPBTCreate tests whether the model's Create conforms to real Kubernetes
// API's Create.
//
// The test uses Kubernetes envtest to set up the actual Kubernetes API server
// and etcd without running any controller.
//
// The model state and real API state are reused across iterations, so state
// accumulates over time. This tests that both handle growing state correctly,
// including AlreadyExists errors when names collide.
//
// Run with: KUBEBUILDER_ASSETS=... go test -v ./apimodel -run TestPBTCreate -rapid.checks=100
func TestPBTCreate(t *testing.T) {
	server := setupTestServer(t)

	ctx := context.Background()

	// Clean up before test to start with empty state
	if err := server.Cleanup(ctx); err != nil {
		t.Logf("Warning: cleanup failed: %v", err)
	}
	time.Sleep(100 * time.Millisecond)

	state := NewState()
	namespace := server.Namespace()

	rapid.Check(t, func(rt *rapid.T) {
		objType := ObjectType(rapid.IntRange(0, 1).Draw(rt, "objectType"))

		switch objType {
		case ObjectTypePod:
			var podGen *rapid.Generator[*corev1.Pod]
			genType := rapid.IntRange(0, 2).Draw(rt, "podGenType")
			switch genType {
			case 0:
				podGen = generators.MinimalPodGen()
			case 1:
				podGen = generators.ComprehensivePodGen()
			case 2:
				podGen = generators.InvalidPodGen()
			}

			testCreate(rt, ctx, state, server, namespace,
				podGen,
				"Pod",
				func(p *corev1.Pod) *corev1.Pod { return p.DeepCopy() },
				func(ns, name string) (interface{}, error) { return state.PodGet(ns, name) },
				func(ctx context.Context, p *corev1.Pod) (*corev1.Pod, error) { return server.CreatePod(ctx, p) },
				func(ctx context.Context, name string) (*corev1.Pod, error) { return server.GetPod(ctx, name) },
			)
		case ObjectTypeReplicaSet:
			var rsGen *rapid.Generator[*appsv1.ReplicaSet]
			genType := rapid.IntRange(0, 2).Draw(rt, "rsGenType")
			switch genType {
			case 0:
				rsGen = generators.MinimalReplicaSetGen()
			case 1:
				rsGen = generators.ComprehensiveReplicaSetGen()
			case 2:
				rsGen = generators.InvalidReplicaSetGen()
			}

			testCreate(rt, ctx, state, server, namespace,
				rsGen,
				"ReplicaSet",
				func(rs *appsv1.ReplicaSet) *appsv1.ReplicaSet { return rs.DeepCopy() },
				func(ns, name string) (interface{}, error) { return state.ReplicaSetGet(ns, name) },
				func(ctx context.Context, rs *appsv1.ReplicaSet) (*appsv1.ReplicaSet, error) {
					return server.CreateReplicaSet(ctx, rs)
				},
				func(ctx context.Context, name string) (*appsv1.ReplicaSet, error) {
					return server.GetReplicaSet(ctx, name)
				},
			)
		}
	})

	if err := server.Cleanup(ctx); err != nil {
		t.Logf("Warning: final cleanup failed: %v", err)
	}
}

// testCreate is a generic test helper for Create and Get operations.
// T must implement metav1.Object for metadata access (GetName, SetNamespace).
func testCreate[T metav1.Object](
	rt *rapid.T,
	ctx context.Context,
	state *State,
	server *testserver.TestServer,
	namespace string,
	gen *rapid.Generator[T],
	kind string,
	deepCopy func(T) T,
	modelGet func(namespace, name string) (interface{}, error),
	realCreate func(ctx context.Context, obj T) (T, error),
	realGet func(ctx context.Context, name string) (T, error),
) {
	obj := gen.Draw(rt, strings.ToLower(kind))

	modelObj := deepCopy(obj)
	modelObj.SetNamespace(namespace)

	realObj := deepCopy(obj)
	realObj.SetNamespace(namespace)

	name := obj.GetName()

	// Create in model
	modelCreateResult, modelCreateErr := state.objCreate2(kind, namespace, modelObj)

	// Create in real API
	realCreateResult, realCreateErr := realCreate(ctx, realObj)

	createComparison := comparators.CompareCreateResults(
		modelCreateResult, modelCreateErr,
		realCreateResult, realCreateErr,
	)
	if !createComparison.Match {
		rt.Fatalf("%s Create mismatch for %s:\n%v", kind, name, createComparison.Differences)
	}

	// If both succeeded, compare Get responses
	if modelCreateErr == nil && realCreateErr == nil {
		// Get from model
		modelGetResult, modelGetErr := modelGet(namespace, name)

		// Get from real API
		realGetResult, realGetErr := realGet(ctx, name)

		getComparison := comparators.CompareCreateResults(
			modelGetResult, modelGetErr,
			realGetResult, realGetErr,
		)
		if !getComparison.Match {
			rt.Fatalf("%s Get mismatch for %s:\n%v", kind, name, getComparison.Differences)
		}
	}
}
