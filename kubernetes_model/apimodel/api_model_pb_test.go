package apimodel

import (
	"context"
	"encoding/json"
	"fmt"
	"os"
	"testing"

	appsv1 "k8s.io/api/apps/v1"
	corev1 "k8s.io/api/core/v1"
	apierrors "k8s.io/apimachinery/pkg/api/errors"
	metav1 "k8s.io/apimachinery/pkg/apis/meta/v1"
	"k8s.io/apimachinery/pkg/types"
	"pgregory.net/rapid"

	"kubernetes_model/apimodel/pbtesting/comparators"
	"kubernetes_model/apimodel/pbtesting/generators"
	"kubernetes_model/apimodel/pbtesting/testserver"
)

// setupTestServer initializes the test server.
// By default, uses envtest (API server + etcd only, no controllers).
// Set USE_EXTERNAL_CLUSTER=1 to use an existing cluster via KUBECONFIG.
func setupTestServer(t *testing.T) *testserver.TestServer {
	useExternal := os.Getenv("USE_EXTERNAL_CLUSTER") == "1"

	server, err := testserver.NewTestServer(testserver.Config{
		Namespace:          "pbt",
		UseExternalCluster: useExternal,
	})
	if err != nil {
		t.Fatalf("Failed to create test server: %v", err)
	}

	return server
}

// teardownServer stops the test server
func teardownServer(t *testing.T, server *testserver.TestServer) {
	server.Stop()
}

type opStats struct {
	attempts   int
	successes  int
	rejections int
}

type pbtStats struct {
	create opStats
	update opStats
	delete opStats
}

type createMode int
type updateMode int
type deleteMode int

const (
	createModeValid createMode = iota
	createModeInvalid
)

const (
	updateModeValid updateMode = iota
	updateModeInvalid
)

const (
	deleteModeValid deleteMode = iota
	deleteModeInvalid
)

func (s *pbtStats) recordCreate(err error) {
	s.create.attempts++
	if err == nil {
		s.create.successes++
	} else {
		s.create.rejections++
	}
}

func (s *pbtStats) recordUpdate(err error) {
	s.update.attempts++
	if err == nil {
		s.update.successes++
	} else {
		s.update.rejections++
	}
}

func (s *pbtStats) recordDelete(err error) {
	s.delete.attempts++
	if err == nil {
		s.delete.successes++
	} else {
		s.delete.rejections++
	}
}

// TestPBT tests whether the model's Create, Update, and Delete operations conform
// to real Kubernetes API behavior.
//
// Run with:
//
//	export KUBEBUILDER_ASSETS="$(setup-envtest use 1.34.0 -p path)"
//	go test -v ./apimodel -run TestPBT -rapid.checks=10000
func TestPBT(t *testing.T) {
	stats := &pbtStats{}
	t.Cleanup(func() {
		t.Logf("PBT stats: create attempts=%d successes=%d rejections=%d | update attempts=%d successes=%d rejections=%d | delete attempts=%d successes=%d rejections=%d",
			stats.create.attempts, stats.create.successes, stats.create.rejections,
			stats.update.attempts, stats.update.successes, stats.update.rejections,
			stats.delete.attempts, stats.delete.successes, stats.delete.rejections,
		)
	})

	rapid.Check(t, func(rt *rapid.T) {
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

		for range 10000 {
			// Weighted operation selection: favor Create early to build up state.
			createWeight := 0.4
			updateWeight := 0.3
			if len(existingObjects) < 5 {
				createWeight = 0.7
				updateWeight = 0.15
			}
			opRoll := rapid.Float64Range(0, 1).Draw(rt, "operationRoll")

			switch {
			case opRoll < createWeight:
				kind := rapid.SampledFrom([]string{"Pod", "ReplicaSet"}).Draw(rt, "kind")

				switch kind {
				case "Pod":
					testCreate(rt, ctx, state, server, namespace, existingObjects,
						stats,
						"Pod",
						func(rt *rapid.T) *corev1.Pod {
							switch rapid.IntRange(0, 1).Draw(rt, "validPodGenType") {
							case 0:
								return generators.MinimalPodGen().Draw(rt, "validPod")
							default:
								return generators.ComprehensivePodGen().Draw(rt, "validPod")
							}
						},
						func(rt *rapid.T) *corev1.Pod {
							return generators.InvalidPodGen().Draw(rt, "invalidPod")
						},
						func(p *corev1.Pod) *corev1.Pod { return p.DeepCopy() },
						func(ns string, obj *corev1.Pod) (*corev1.Pod, error) { return state.PodCreate2(ns, obj) },
						func(ctx context.Context, obj *corev1.Pod) (*corev1.Pod, error) { return server.CreatePod(ctx, obj) },
						func(ns, name string) (interface{}, error) { return state.PodGet(ns, name) },
						func(ctx context.Context, name string) (*corev1.Pod, error) { return server.GetPod(ctx, name) },
					)

				case "ReplicaSet":
					testCreate(rt, ctx, state, server, namespace, existingObjects,
						stats,
						"ReplicaSet",
						func(rt *rapid.T) *appsv1.ReplicaSet {
							switch rapid.IntRange(0, 1).Draw(rt, "validRSGenType") {
							case 0:
								return generators.MinimalReplicaSetGen().Draw(rt, "validReplicaSet")
							default:
								return generators.ComprehensiveReplicaSetGen().Draw(rt, "validReplicaSet")
							}
						},
						func(rt *rapid.T) *appsv1.ReplicaSet {
							return generators.InvalidReplicaSetGen().Draw(rt, "invalidReplicaSet")
						},
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
			case opRoll < createWeight+updateWeight:
				kind := rapid.SampledFrom([]string{"Pod", "ReplicaSet"}).Draw(rt, "kind")

				switch kind {
				case "Pod":
					testUpdate(
						rt, ctx, state, server, namespace, existingObjects, stats,
						"Pod",
						func(ns, name string) (*corev1.Pod, error) { return state.PodGet(ns, name) },
						func(ctx context.Context, name string) (*corev1.Pod, error) { return server.GetPod(ctx, name) },
						func(ns string, obj *corev1.Pod) (*corev1.Pod, error) { return state.PodUpdate2(ns, obj) },
						func(ctx context.Context, obj *corev1.Pod) (*corev1.Pod, error) { return server.UpdatePod(ctx, obj) },
						func(p *corev1.Pod) *corev1.Pod { return p.DeepCopy() },
						func(name, namespace string) *corev1.Pod {
							pod := generators.MinimalPodGen().Example()
							pod.Name = name
							pod.Namespace = namespace
							return pod
						},
						generators.ComprehensivePodMut,
					)

				case "ReplicaSet":
					testUpdate(
						rt, ctx, state, server, namespace, existingObjects, stats,
						"ReplicaSet",
						func(ns, name string) (*appsv1.ReplicaSet, error) { return state.ReplicaSetGet(ns, name) },
						func(ctx context.Context, name string) (*appsv1.ReplicaSet, error) {
							return server.GetReplicaSet(ctx, name)
						},
						func(ns string, obj *appsv1.ReplicaSet) (*appsv1.ReplicaSet, error) {
							return state.ReplicaSetUpdate2(ns, obj)
						},
						func(ctx context.Context, obj *appsv1.ReplicaSet) (*appsv1.ReplicaSet, error) {
							return server.UpdateReplicaSet(ctx, obj)
						},
						func(rs *appsv1.ReplicaSet) *appsv1.ReplicaSet { return rs.DeepCopy() },
						func(name, namespace string) *appsv1.ReplicaSet {
							rs := generators.MinimalReplicaSetGen().Example()
							rs.Name = name
							rs.Namespace = namespace
							return rs
						},
						generators.ComprehensiveReplicaSetMut,
					)
				}
			default:
				kind := rapid.SampledFrom([]string{"Pod", "ReplicaSet"}).Draw(rt, "kind")

				switch kind {
				case "Pod":
					testDelete(
						rt, ctx, state, server, namespace, existingObjects, stats,
						"Pod",
						state.PodGet,
						server.GetPod,
						state.PodDelete2,
						server.DeletePod,
					)

				case "ReplicaSet":
					testDelete(
						rt, ctx, state, server, namespace, existingObjects, stats,
						"ReplicaSet",
						state.ReplicaSetGet,
						server.GetReplicaSet,
						state.ReplicaSetDelete2,
						server.DeleteReplicaSet,
					)
				}
			}
		}

		if err := server.Cleanup(ctx); err != nil {
			t.Logf("Warning: final cleanup failed: %v", err)
		}

		teardownServer(t, server)
	})

}

func testCreate[T metav1.Object](
	rt *rapid.T,
	ctx context.Context,
	state *State,
	server *testserver.TestServer,
	namespace string,
	existingObjects map[KKey]bool,
	stats *pbtStats,
	kind string,
	drawValid func(*rapid.T) T,
	drawInvalid func(*rapid.T) T,
	deepCopy func(T) T,
	modelCreate func(namespace string, obj T) (T, error),
	realCreate func(ctx context.Context, obj T) (T, error),
	modelGet func(namespace, name string) (interface{}, error),
	realGet func(ctx context.Context, name string) (T, error),
) {
	keys := make([]KKey, 0)
	for k := range existingObjects {
		if k.Kind == kind {
			keys = append(keys, k)
		}
	}

	// First choose between:
	// - a valid create that should allocate a fresh object
	// - an invalid create that should be rejected because the object is bad or already exists
	mode := createModeInvalid
	if rapid.IntRange(0, 9).Draw(rt, "createModeRoll") < 7 {
		mode = createModeValid
	}

	var obj T
	switch mode {
	case createModeValid:
		obj = drawValid(rt)
		obj.SetName(freshCreateName(rt, kind, namespace, existingObjects))
	case createModeInvalid:
		// Invalid mode covers both "name already exists" and "object itself is invalid".
		if len(keys) > 0 && rapid.Bool().Draw(rt, "invalidCreateUsesExistingName") {
			obj = drawValid(rt)
			targetKey := keys[rapid.IntRange(0, len(keys)-1).Draw(rt, "createExistingTargetIdx")]
			obj.SetName(targetKey.Name)
			rt.Logf("Creating existing %s in invalid mode: %s (from %d candidates)", kind, targetKey.Name, len(keys))
		} else {
			obj = drawInvalid(rt)
			// Keep the name fresh here so the failure is caused by the object's contents,
			// not by colliding with something already stored.
			obj.SetName(freshCreateName(rt, kind, namespace, existingObjects))
		}
	}

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

	stats.recordCreate(modelErr)
}

func freshCreateName(rt *rapid.T, kind, namespace string, existingObjects map[KKey]bool) string {
	base := rapid.StringMatching(`[a-z][a-z0-9]{4,8}`).Draw(rt, "createFreshName")
	name := base
	for suffix := 0; existingObjects[KKey{Kind: kind, Namespace: namespace, Name: name}]; suffix++ {
		name = fmt.Sprintf("%s-%d", base, suffix)
	}
	return name
}

func testUpdate[T metav1.Object](
	rt *rapid.T,
	ctx context.Context,
	state *State,
	server *testserver.TestServer,
	namespace string,
	existingObjects map[KKey]bool,
	stats *pbtStats,
	kind string,
	modelGet func(namespace, name string) (T, error),
	realGet func(ctx context.Context, name string) (T, error),
	modelUpdate func(namespace string, obj T) (T, error),
	realUpdate func(ctx context.Context, obj T) (T, error),
	deepCopy func(T) T,
	buildMissing func(name, namespace string) T,
	prepareUpdate func(rt *rapid.T, modelObj, realObj T, exists, valid bool),
) {
	var targetKey KKey
	keys := make([]KKey, 0)
	for k := range existingObjects {
		if k.Kind == kind {
			keys = append(keys, k)
		}
	}

	// First choose between:
	// - a valid read-modify-write update we expect to succeed
	// - an invalid update that should be rejected or not found
	mode := updateModeInvalid
	if rapid.IntRange(0, 9).Draw(rt, "updateModeRoll") < 7 {
		mode = updateModeValid
	}

	switch mode {
	case updateModeValid:
		if len(keys) == 0 {
			// A valid update needs a stored object to modify. If none exist for this
			// kind, fall back to the invalid missing-object path for this iteration.
			mode = updateModeInvalid
		} else {
			idx := rapid.IntRange(0, len(keys)-1).Draw(rt, "updateTargetIdx")
			targetKey = keys[idx]
			rt.Logf("Updating existing %s in valid mode: %s (from %d candidates)", kind, targetKey.Name, len(keys))
		}
	}

	if mode == updateModeInvalid {
		// Invalid mode covers both "object does not exist" and "stored object exists
		// but the update itself is malformed/immutable".
		if len(keys) > 0 && rapid.Bool().Draw(rt, "invalidUpdateTargetsExisting") {
			idx := rapid.IntRange(0, len(keys)-1).Draw(rt, "updateTargetIdx")
			targetKey = keys[idx]
			rt.Logf("Updating existing %s in invalid mode: %s (from %d candidates)", kind, targetKey.Name, len(keys))
		} else {
			targetKey = KKey{
				Kind:      kind,
				Namespace: namespace,
				Name:      rapid.StringMatching(`nonexist-[a-z0-9]{5}`).Draw(rt, "updateName"),
			}
		}
	}

	// Check both systems before mutating anything. This determines whether we are
	// exercising a read-modify-write update or an update against a missing object.
	preUpdateModelGet, preUpdateModelGetErr := modelGet(namespace, targetKey.Name)
	preUpdateRealGet, preUpdateRealGetErr := realGet(ctx, targetKey.Name)

	match, diffs := comparators.CompareErrors(preUpdateModelGetErr, preUpdateRealGetErr, false)
	if !match {
		rt.Fatalf("%s Get error before Update mismatch for %s:\n%v", kind, targetKey.Name, diffs)
	}

	exists := preUpdateModelGetErr == nil && preUpdateRealGetErr == nil
	if exists {
		match, diffs = comparators.CompareObjects(preUpdateModelGet, preUpdateRealGet)
		if !match {
			rt.Fatalf("%s Get result before Update mismatch for %s:\n%v", kind, targetKey.Name, diffs)
		}
	}

	var modelUpdateObj, realUpdateObj T
	if exists {
		// Existing-object updates start from the stored object so the mutator can
		// perturb server-managed fields like resourceVersion, UID, status, etc.
		modelUpdateObj = deepCopy(preUpdateModelGet)
		realUpdateObj = deepCopy(preUpdateRealGet)
	} else {
		// Missing-object updates start from a fresh minimal object with the chosen
		// name/namespace, then the mutator applies the same logical changes.
		modelUpdateObj = buildMissing(targetKey.Name, namespace)
		realUpdateObj = buildMissing(targetKey.Name, namespace)
	}

	prepareUpdate(rt, modelUpdateObj, realUpdateObj, exists, mode == updateModeValid)

	modelUpdated, modelErr := modelUpdate(namespace, modelUpdateObj)
	realUpdated, realErr := realUpdate(ctx, realUpdateObj)

	match, diffs = comparators.CompareErrors(modelErr, realErr, false)
	if !match {
		modelInputJSON, _ := json.MarshalIndent(modelUpdateObj, "    ", "  ")
		realInputJSON, _ := json.MarshalIndent(realUpdateObj, "    ", "  ")

		rt.Fatalf("%s Update mismatch for %s:\n%v\n"+
			"Pre-Update Get:\n"+
			"  Model Get error: %v\n"+
			"  Real Get error: %v\n"+
			"Update objects:\n"+
			"  Model Update input:\n    %s\n"+
			"  Real Update input:\n    %s\n"+
			"Update errors:\n"+
			"  Model Update error: %v\n"+
			"  Real Update error: %v",
			kind, targetKey.Name, diffs,
			preUpdateModelGetErr, preUpdateRealGetErr,
			string(modelInputJSON), string(realInputJSON),
			modelErr, realErr)
	}

	if modelErr == nil {
		match, diffs = comparators.CompareObjects(modelUpdated, realUpdated)
		if !match {
			rt.Fatalf("%s Update result mismatch for %s:\n%v", kind, targetKey.Name, diffs)
		}
	}

	// Re-read after update because the object may have been persisted, rejected,
	// or removed entirely by update-side effects such as clearing finalizers.
	modelGet2, modelGetErr := modelGet(namespace, targetKey.Name)
	realGet2, realGetErr := realGet(ctx, targetKey.Name)

	match, diffs = comparators.CompareErrors(modelGetErr, realGetErr, false)
	if !match {
		rt.Fatalf("%s Get error after Update mismatch for %s:\n%v", kind, targetKey.Name, diffs)
	}

	if modelGetErr == nil {
		match, diffs = comparators.CompareObjects(modelGet2, realGet2)
		if !match {
			rt.Fatalf("%s Get result after Update mismatch for %s:\n%v", kind, targetKey.Name, diffs)
		}
		existingObjects[targetKey] = true
	} else if apierrors.IsNotFound(modelGetErr) {
		delete(existingObjects, targetKey)
	}

	stats.recordUpdate(modelErr)
}

func testDelete[T metav1.Object](
	rt *rapid.T,
	ctx context.Context,
	state *State,
	server *testserver.TestServer,
	namespace string,
	existingObjects map[KKey]bool,
	stats *pbtStats,
	kind string,
	modelGet func(namespace, name string) (T, error),
	realGet func(ctx context.Context, name string) (T, error),
	modelDelete func(namespace, name string, options metav1.DeleteOptions) error,
	realDelete func(ctx context.Context, name string, options metav1.DeleteOptions) error,
) {
	var targetKey KKey
	keys := make([]KKey, 0)
	for k := range existingObjects {
		if k.Kind == kind {
			keys = append(keys, k)
		}
	}

	// First choose between:
	// - a valid delete we expect to be accepted
	// - an invalid delete that should be rejected or not found
	mode := deleteModeInvalid
	if rapid.IntRange(0, 9).Draw(rt, "deleteModeRoll") < 7 {
		mode = deleteModeValid
	}

	switch mode {
	case deleteModeValid:
		if len(keys) == 0 {
			// A valid delete needs a stored object. Fall back to the invalid
			// missing-object path if none of this kind are tracked.
			mode = deleteModeInvalid
		} else {
			idx := rapid.IntRange(0, len(keys)-1).Draw(rt, "targetIdx")
			targetKey = keys[idx]
			rt.Logf("Deleting existing %s in valid mode: %s (from %d candidates)", kind, targetKey.Name, len(keys))
		}
	}

	if mode == deleteModeInvalid {
		// Invalid mode covers both "delete a missing object" and "delete an
		// existing object with bad preconditions".
		if len(keys) > 0 && rapid.Bool().Draw(rt, "invalidDeleteTargetsExisting") {
			idx := rapid.IntRange(0, len(keys)-1).Draw(rt, "targetIdx")
			targetKey = keys[idx]
			rt.Logf("Deleting existing %s in invalid mode: %s (from %d candidates)", kind, targetKey.Name, len(keys))
		} else {
			targetKey = KKey{
				Kind:      kind,
				Namespace: namespace,
				Name:      rapid.StringMatching(`nonexist-[a-z0-9]{5}`).Draw(rt, "name"),
			}
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

	// Generate options in either a valid mode (accepted delete) or invalid mode
	// (bad preconditions or deleting a missing object).
	modelOptions, realOptions := generateDeleteOptions(rt, modelUID, modelRV, realUID, realRV, mode == deleteModeValid, preDeleteModelGetErr == nil)

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

	stats.recordDelete(modelErr)
}

func generateBaseDeleteOptions(rt *rapid.T) metav1.DeleteOptions {
	// Generate shared DeleteOptions fields that should not change success/failure mode.
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

	return baseOptions
}

func copyDeleteOptions(baseOptions metav1.DeleteOptions) (metav1.DeleteOptions, metav1.DeleteOptions) {
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
	}
	realOpts := metav1.DeleteOptions{
		GracePeriodSeconds: realGracePeriod,
		PropagationPolicy:  realPolicy,
	}

	return modelOpts, realOpts
}

func generateDeleteOptions(rt *rapid.T, modelUID, modelRV, realUID, realRV string, valid, exists bool) (metav1.DeleteOptions, metav1.DeleteOptions) {
	baseOptions := generateBaseDeleteOptions(rt)
	modelOpts, realOpts := copyDeleteOptions(baseOptions)

	if valid {
		// Valid delete mode targets an existing object and avoids bad preconditions.
		// Occasionally keep a correct UID precondition to exercise that success path.
		if exists && rapid.Bool().Draw(rt, "validDeleteUsesUIDPrecondition") {
			modelOpts.Preconditions = &metav1.Preconditions{}
			realOpts.Preconditions = &metav1.Preconditions{}
			convertedModelUID := types.UID(modelUID)
			convertedRealUID := types.UID(realUID)
			modelOpts.Preconditions.UID = &convertedModelUID
			realOpts.Preconditions.UID = &convertedRealUID
		}
		return modelOpts, realOpts
	}

	// Missing-object deletes are already invalid without additional preconditions.
	if !exists {
		return modelOpts, realOpts
	}

	modelOpts.Preconditions = &metav1.Preconditions{}
	realOpts.Preconditions = &metav1.Preconditions{}

	// Invalid delete mode uses a single bad precondition on an existing object.
	if rapid.Bool().Draw(rt, "invalidDeleteUsesBadUID") {
		modelWrongUID := types.UID("corrupted-uid")
		realWrongUID := types.UID("corrupted-uid")
		modelOpts.Preconditions.UID = &modelWrongUID
		realOpts.Preconditions.UID = &realWrongUID
		return modelOpts, realOpts
	}

	if rapid.Bool().Draw(rt, "invalidDeleteUsesBadRV") {
		modelWrongRV := "corrupted-rv"
		realWrongRV := "corrupted-rv"
		modelOpts.Preconditions.ResourceVersion = &modelWrongRV
		realOpts.Preconditions.ResourceVersion = &realWrongRV
		return modelOpts, realOpts
	}

	// Fallback so invalid existing-object deletes always carry one bad precondition.
	modelWrongUID := types.UID("corrupted-uid")
	realWrongUID := types.UID("corrupted-uid")
	modelOpts.Preconditions.UID = &modelWrongUID
	realOpts.Preconditions.UID = &realWrongUID
	return modelOpts, realOpts
}
