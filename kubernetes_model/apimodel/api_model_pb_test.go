package apimodel

import (
	"context"
	"encoding/json"
	"os"
	"testing"

	appsv1 "k8s.io/api/apps/v1"
	corev1 "k8s.io/api/core/v1"
	apierrors "k8s.io/apimachinery/pkg/api/errors"
	metav1 "k8s.io/apimachinery/pkg/apis/meta/v1"
	"k8s.io/apimachinery/pkg/types"
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

// TestPBTCreateDelete tests whether the model's Create and Delete operations conform
// to real Kubernetes API behavior.
//
// Run with:
//
//	export KUBEBUILDER_ASSETS="$(setup-envtest use 1.34.0 -p path)"
//	go test -v ./apimodel -run TestPBTCreateDelete -rapid.checks=10000
func TestPBTCreateDelete(t *testing.T) {
	server := setupTestServer(t)
	ctx := context.Background()

	// Clean up before test to start with empty state
	if err := server.Cleanup(ctx); err != nil {
		t.Logf("Warning: cleanup failed: %v", err)
	}

	state := NewState()
	namespace := "pbt"

	// Track existing objects (should match between model and real API)
	existingObjects := make(map[KKey]bool)

	rapid.Check(t, func(rt *rapid.T) {
		// Weighted operation selection: favor Create early to build up state
		createWeight := 0.5
		if len(existingObjects) < 5 {
			createWeight = 0.8
		}
		shouldCreate := rapid.Float64Range(0, 1).Draw(rt, "shouldCreate") < createWeight

		if shouldCreate {
			kind := rapid.SampledFrom([]string{"Pod", "ReplicaSet"}).Draw(rt, "kind")

			switch kind {
			case "Pod":
				genType := rapid.IntRange(0, 2).Draw(rt, "podGenType")
				var podGen *rapid.Generator[*corev1.Pod]
				switch genType {
				case 0:
					podGen = generators.MinimalPodGen()
				case 1:
					podGen = generators.ComprehensivePodGen()
				case 2:
					podGen = generators.InvalidPodGen()
				}

				testCreate(rt, ctx, state, server, namespace, existingObjects,
					podGen,
					"Pod",
					func(p *corev1.Pod) *corev1.Pod { return p.DeepCopy() },
					func(ns string, obj *corev1.Pod) (*corev1.Pod, error) { return state.PodCreate2(ns, obj) },
					func(ctx context.Context, obj *corev1.Pod) (*corev1.Pod, error) { return server.CreatePod(ctx, obj) },
					func(ns, name string) (interface{}, error) { return state.PodGet(ns, name) },
					func(ctx context.Context, name string) (*corev1.Pod, error) { return server.GetPod(ctx, name) },
				)

			case "ReplicaSet":
				genType := rapid.IntRange(0, 2).Draw(rt, "rsGenType")
				var rsGen *rapid.Generator[*appsv1.ReplicaSet]
				switch genType {
				case 0:
					rsGen = generators.MinimalReplicaSetGen()
				case 1:
					rsGen = generators.ComprehensiveReplicaSetGen()
				case 2:
					rsGen = generators.InvalidReplicaSetGen()
				}

				testCreate(rt, ctx, state, server, namespace, existingObjects,
					rsGen,
					"ReplicaSet",
					func(rs *appsv1.ReplicaSet) *appsv1.ReplicaSet { return rs.DeepCopy() },
					func(ns string, obj *appsv1.ReplicaSet) (*appsv1.ReplicaSet, error) {
						return state.ReplicaSetCreate2(ns, obj)
					},
					func(ctx context.Context, obj *appsv1.ReplicaSet) (*appsv1.ReplicaSet, error) {
						return server.CreateReplicaSet(ctx, obj)
					},
					func(ns, name string) (interface{}, error) { return state.ReplicaSetGet(ns, name) },
					func(ctx context.Context, name string) (*appsv1.ReplicaSet, error) {
						return server.GetReplicaSet(ctx, name)
					},
				)
			}
		} else {
			kind := rapid.SampledFrom([]string{"Pod", "ReplicaSet"}).Draw(rt, "kind")

			switch kind {
			case "Pod":
				testDelete(
					rt, ctx, state, server, namespace, existingObjects,
					"Pod",
					state.PodGet,
					server.GetPod,
					state.PodDelete2,
					server.DeletePod,
				)

			case "ReplicaSet":
				testDelete(
					rt, ctx, state, server, namespace, existingObjects,
					"ReplicaSet",
					state.ReplicaSetGet,
					server.GetReplicaSet,
					state.ReplicaSetDelete2,
					server.DeleteReplicaSet,
				)
			}
		}
	})

	if err := server.Cleanup(ctx); err != nil {
		t.Logf("Warning: final cleanup failed: %v", err)
	}
}

func testCreate[T metav1.Object](
	rt *rapid.T,
	ctx context.Context,
	state *State,
	server *testserver.TestServer,
	namespace string,
	existingObjects map[KKey]bool,
	gen *rapid.Generator[T],
	kind string,
	deepCopy func(T) T,
	modelCreate func(namespace string, obj T) (T, error),
	realCreate func(ctx context.Context, obj T) (T, error),
	modelGet func(namespace, name string) (interface{}, error),
	realGet func(ctx context.Context, name string) (T, error),
) {
	// Generate and create object
	obj := gen.Draw(rt, kind)
	obj.SetNamespace(namespace)
	name := obj.GetName()

	// Create copies for model and real API
	modelObj := deepCopy(obj)
	realObj := deepCopy(obj)

	// Create in both model and real API
	modelCreated, modelErr := modelCreate(namespace, modelObj)
	realCreated, realErr := realCreate(ctx, realObj)

	// Compare Create results
	match, diffs := comparators.CompareErrors(modelErr, realErr, false)
	if !match {
		rt.Fatalf("%s Create error mismatch for %s:\n%v", kind, name, diffs)
	}

	// Only compare objects if both operations succeeded
	if modelErr == nil {
		match, diffs = comparators.CompareObjects(modelCreated, realCreated)
		if !match {
			rt.Fatalf("%s Create result mismatch for %s:\n%v", kind, name, diffs)
		}
	}

	// Get object to verify state
	modelGetResult, modelGetErr := modelGet(namespace, name)
	realGetResult, realGetErr := realGet(ctx, name)

	match, diffs = comparators.CompareErrors(modelGetErr, realGetErr, false)
	if !match {
		rt.Fatalf("%s Get error mismatch for %s:\n%v", kind, name, diffs)
	}

	// Only compare objects if both operations succeeded
	if modelGetErr == nil {
		match, diffs = comparators.CompareObjects(modelGetResult, realGetResult)
		if !match {
			rt.Fatalf("%s Get result mismatch for %s:\n%v", kind, name, diffs)
		}
	}

	// Update existingObjects
	key := KKey{Kind: kind, Namespace: namespace, Name: name}
	if modelGetErr == nil {
		existingObjects[key] = true
	}
}

func testDelete[T metav1.Object](
	rt *rapid.T,
	ctx context.Context,
	state *State,
	server *testserver.TestServer,
	namespace string,
	existingObjects map[KKey]bool,
	kind string,
	modelGet func(namespace, name string) (T, error),
	realGet func(ctx context.Context, name string) (T, error),
	modelDelete func(namespace, name string, options metav1.DeleteOptions) error,
	realDelete func(ctx context.Context, name string, options metav1.DeleteOptions) error,
) {
	var targetKey KKey

	if rapid.Bool().Draw(rt, "deleteExisting") {
		// Pick random existing object of this kind
		keys := make([]KKey, 0)
		for k := range existingObjects {
			if k.Kind == kind {
				keys = append(keys, k)
			}
		}
		if len(keys) == 0 {
			// No objects of this kind exist, generate non-existent name
			targetKey = KKey{
				Kind:      kind,
				Namespace: namespace,
				Name:      rapid.StringMatching(`nonexist-[a-z0-9]{5}`).Draw(rt, "name"),
			}
		} else {
			idx := rapid.IntRange(0, len(keys)-1).Draw(rt, "targetIdx")
			targetKey = keys[idx]
			rt.Logf("Deleting existing %s: %s (from %d candidates)", kind, targetKey.Name, len(keys))
		}
	} else {
		// Generate non-existent name
		targetKey = KKey{
			Kind:      kind,
			Namespace: namespace,
			Name:      rapid.StringMatching(`nonexist-[a-z0-9]{5}`).Draw(rt, "name"),
		}
	}

	// Get object first to retrieve UID and ResourceVersion for preconditions
	preDeleteModelGet, preDeleteModelGetErr := modelGet(namespace, targetKey.Name)
	preDeleteRealGet, preDeleteRealGetErr := realGet(ctx, targetKey.Name)

	// Compare pre-delete Get results
	match, diffs := comparators.CompareErrors(preDeleteModelGetErr, preDeleteRealGetErr, false)
	if !match {
		rt.Fatalf("%s Get error before Delete mismatch for %s:\n%v", kind, targetKey.Name, diffs)
	}

	// Only compare objects if both operations succeeded
	if preDeleteModelGetErr == nil {
		match, diffs = comparators.CompareObjects(preDeleteModelGet, preDeleteRealGet)
		if !match {
			rt.Fatalf("%s Get result before Delete mismatch for %s:\n%v", kind, targetKey.Name, diffs)
		}
	}

	// Extract UID and ResourceVersion from model Get result and real API Get result
	var modelUID, modelRV string
	var realUID, realRV string
	if preDeleteModelGetErr == nil && preDeleteRealGetErr == nil {
		modelUID = string(preDeleteModelGet.GetUID())
		modelRV = preDeleteModelGet.GetResourceVersion()
		realUID = string(preDeleteRealGet.GetUID())
		realRV = preDeleteRealGet.GetResourceVersion()
		rt.Logf("Extracted from model Get: UID=%s, RV=%s", modelUID, modelRV)
		rt.Logf("Extracted from real Get: UID=%s, RV=%s", realUID, realRV)
	}

	// Generate preconditions
	modelOptions, realOptions := generatePreconditions(rt, modelUID, modelRV, realUID, realRV)

	// Assert that model and real options have consistent structure
	// (both should have same nil/non-nil pattern for preconditions and fields)
	modelHasPreconditions := modelOptions.Preconditions != nil
	realHasPreconditions := realOptions.Preconditions != nil
	if modelHasPreconditions != realHasPreconditions {
		rt.Fatalf("Preconditions consistency check failed: model has preconditions=%v, real has preconditions=%v",
			modelHasPreconditions, realHasPreconditions)
	}

	if modelHasPreconditions {
		// Check UID consistency
		modelHasUID := modelOptions.Preconditions.UID != nil
		realHasUID := realOptions.Preconditions.UID != nil
		if modelHasUID != realHasUID {
			rt.Fatalf("UID precondition consistency check failed: model has UID=%v, real has UID=%v",
				modelHasUID, realHasUID)
		}

		// Check ResourceVersion consistency
		modelHasRV := modelOptions.Preconditions.ResourceVersion != nil
		realHasRV := realOptions.Preconditions.ResourceVersion != nil
		if modelHasRV != realHasRV {
			rt.Fatalf("ResourceVersion precondition consistency check failed: model has RV=%v, real has RV=%v",
				modelHasRV, realHasRV)
		}

		// Check UID empty string consistency
		if modelHasUID {
			modelUIDEmpty := *modelOptions.Preconditions.UID == ""
			realUIDEmpty := *realOptions.Preconditions.UID == ""
			if modelUIDEmpty != realUIDEmpty {
				rt.Fatalf("UID empty string consistency check failed: model UID empty=%v, real UID empty=%v",
					modelUIDEmpty, realUIDEmpty)
			}
		}

		// Check ResourceVersion empty string consistency
		if modelHasRV {
			modelRVEmpty := *modelOptions.Preconditions.ResourceVersion == ""
			realRVEmpty := *realOptions.Preconditions.ResourceVersion == ""
			if modelRVEmpty != realRVEmpty {
				rt.Fatalf("ResourceVersion empty string consistency check failed: model RV empty=%v (value=%q), real RV empty=%v (value=%q)",
					modelRVEmpty, *modelOptions.Preconditions.ResourceVersion,
					realRVEmpty, *realOptions.Preconditions.ResourceVersion)
			}
		}
	}

	// Delete from both model and real API
	modelErr := modelDelete(namespace, targetKey.Name, modelOptions)
	realErr := realDelete(ctx, targetKey.Name, realOptions)

	// Compare Delete results
	match, diffs = comparators.CompareErrors(modelErr, realErr, false)
	if !match {
		// Format objects as JSON for better readability
		modelGetJSON, _ := json.MarshalIndent(preDeleteModelGet, "    ", "  ")
		realGetJSON, _ := json.MarshalIndent(preDeleteRealGet, "    ", "  ")

		rt.Fatalf("%s Delete mismatch for %s:\n%v\n"+
			"Pre-Delete Get:\n"+
			"  Model Get error: %v\n"+
			"  Real Get error: %v\n"+
			"  Model Get result:\n    %s\n"+
			"  Real Get result:\n    %s\n"+
			"Delete options:\n"+
			"  Model options: %+v\n"+
			"  Real options: %+v\n"+
			"Delete errors:\n"+
			"  Model Delete error: %v\n"+
			"  Real Delete error: %v",
			kind, targetKey.Name, diffs,
			preDeleteModelGetErr, preDeleteRealGetErr,
			string(modelGetJSON), string(realGetJSON),
			modelOptions, realOptions,
			modelErr, realErr)
	}

	// Get object to verify state after Delete
	modelGet2, modelGetErr := modelGet(namespace, targetKey.Name)
	realGet2, realGetErr := realGet(ctx, targetKey.Name)

	match, diffs = comparators.CompareErrors(modelGetErr, realGetErr, false)
	if !match {
		rt.Fatalf("%s Get error after Delete mismatch for %s:\n%v", kind, targetKey.Name, diffs)
	}

	// Only compare objects if both operations succeeded
	if modelGetErr == nil {
		match, diffs = comparators.CompareObjects(modelGet2, realGet2)
		if !match {
			rt.Fatalf("%s Get result after Delete mismatch for %s:\n%v", kind, targetKey.Name, diffs)
		}
	}

	// Update existingObjects
	if modelGetErr == nil {
		// Object still exists (has DeletionTimestamp or finalizers)
		existingObjects[targetKey] = true
	} else if apierrors.IsNotFound(modelGetErr) {
		// Object was deleted
		delete(existingObjects, targetKey)
	}
}

func generatePreconditions(rt *rapid.T, modelUID, modelRV, realUID, realRV string) (metav1.DeleteOptions, metav1.DeleteOptions) {
	// Generate base DeleteOptions (GracePeriod and PropagationPolicy)
	baseOptions := metav1.DeleteOptions{}
	if rapid.Bool().Draw(rt, "setBaseOption") {
		if rapid.Bool().Draw(rt, "hasGracePeriod") {
			gracePeriod := rapid.Int64Range(0, 30).Draw(rt, "gracePeriod")
			baseOptions.GracePeriodSeconds = &gracePeriod
		}

		if rapid.Bool().Draw(rt, "hasPropagationPolicy") {
			policy := rapid.SampledFrom([]metav1.DeletionPropagation{
				metav1.DeletePropagationOrphan,
				metav1.DeletePropagationBackground,
				metav1.DeletePropagationForeground,
			}).Draw(rt, "propagationPolicy")
			baseOptions.PropagationPolicy = &policy
		}
	}

	// Generate preconditions consistently for model and real API
	return addPreconditions(rt, baseOptions, modelUID, modelRV, realUID, realRV)
}

// addPreconditions adds preconditions to the base DeleteOptions for both model and real API.
// The decision of what preconditions to set is made once and applied consistently to both,
// but the actual UID/RV values differ (model uses modelUID/modelRV, real uses realUID/realRV).
func addPreconditions(rt *rapid.T, baseOptions metav1.DeleteOptions, modelUID, modelRV, realUID, realRV string) (metav1.DeleteOptions, metav1.DeleteOptions) {
	// Create independent copies of pointer fields to avoid aliasing
	var modelGracePeriod, realGracePeriod *int64
	if baseOptions.GracePeriodSeconds != nil {
		modelCopy := *baseOptions.GracePeriodSeconds
		realCopy := *baseOptions.GracePeriodSeconds
		modelGracePeriod = &modelCopy
		realGracePeriod = &realCopy
	}

	var modelPolicy, realPolicy *metav1.DeletionPropagation
	if baseOptions.PropagationPolicy != nil {
		modelCopy := *baseOptions.PropagationPolicy
		realCopy := *baseOptions.PropagationPolicy
		modelPolicy = &modelCopy
		realPolicy = &realCopy
	}

	modelOpts := metav1.DeleteOptions{
		GracePeriodSeconds: modelGracePeriod,
		PropagationPolicy:  modelPolicy,
		Preconditions:      &metav1.Preconditions{},
	}
	realOpts := metav1.DeleteOptions{
		GracePeriodSeconds: realGracePeriod,
		PropagationPolicy:  realPolicy,
		Preconditions:      &metav1.Preconditions{},
	}

	if rapid.Bool().Draw(rt, "setUIDPrecondition") {
		convertedModelUID := types.UID(modelUID)
		modelOpts.Preconditions.UID = &convertedModelUID
		convertedRealUID := types.UID(realUID)
		realOpts.Preconditions.UID = &convertedRealUID
	} else if rapid.Bool().Draw(rt, "corruptUID") {
		// Create separate variables to avoid pointer aliasing
		modelWrongUID := types.UID("corrupted-uid")
		realWrongUID := types.UID("corrupted-uid")
		modelOpts.Preconditions.UID = &modelWrongUID
		realOpts.Preconditions.UID = &realWrongUID
	}

	if rapid.Bool().Draw(rt, "setRVPrecondition") {
		modelRVCopy := modelRV
		realRVCopy := realRV
		modelOpts.Preconditions.ResourceVersion = &modelRVCopy
		realOpts.Preconditions.ResourceVersion = &realRVCopy
	} else if rapid.Bool().Draw(rt, "corruptRV") {
		// Create separate variables to avoid pointer aliasing
		modelWrongRV := "corrupted-rv"
		realWrongRV := "corrupted-rv"
		modelOpts.Preconditions.ResourceVersion = &modelWrongRV
		realOpts.Preconditions.ResourceVersion = &realWrongRV
	}

	return modelOpts, realOpts
}
