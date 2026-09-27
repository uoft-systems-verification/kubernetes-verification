package replicaset

import (
	"errors"
	"reflect"
	"testing"
	"time"

	apps "k8s.io/api/apps/v1"
	v1 "k8s.io/api/core/v1"
	apierrors "k8s.io/apimachinery/pkg/api/errors"
	metav1 "k8s.io/apimachinery/pkg/apis/meta/v1"
	"k8s.io/apimachinery/pkg/runtime"
	"k8s.io/apimachinery/pkg/runtime/schema"
	utilfeature "k8s.io/apiserver/pkg/util/feature"
	"k8s.io/client-go/kubernetes/fake"
	clienttesting "k8s.io/client-go/testing"
	featuregatetesting "k8s.io/component-base/featuregate/testing"
	"k8s.io/kubernetes/pkg/features"
	"k8s.io/utils/ptr"
)

func statusTestReplicaSet() *apps.ReplicaSet {
	return &apps.ReplicaSet{
		ObjectMeta: metav1.ObjectMeta{Name: "rs", Namespace: "default", Generation: 5, ResourceVersion: "1"},
		Spec: apps.ReplicaSetSpec{
			Replicas: ptr.To(int32(3)), MinReadySeconds: 10,
			Template: v1.PodTemplateSpec{ObjectMeta: metav1.ObjectMeta{Labels: map[string]string{"app": "test"}}},
		},
		Status: apps.ReplicaSetStatus{Replicas: 2, ObservedGeneration: 4},
	}
}

func TestCalculateStatusSnapshot(t *testing.T) {
	now := time.Unix(1000, 0)
	pod := func(labels map[string]string, ready v1.ConditionStatus, since time.Time) *v1.Pod {
		return &v1.Pod{
			ObjectMeta: metav1.ObjectMeta{Labels: labels},
			Status: v1.PodStatus{Conditions: []v1.PodCondition{{
				Type: v1.PodReady, Status: ready, LastTransitionTime: metav1.NewTime(since),
			}}},
		}
	}
	active := []*v1.Pod{
		// Exactly minReadySeconds is available; one second short is not.
		pod(map[string]string{"app": "test", "extra": "label"}, v1.ConditionTrue, now.Add(-10*time.Second)),
		pod(map[string]string{"app": "test"}, v1.ConditionTrue, now.Add(-9*time.Second)),
		pod(map[string]string{"app": "other"}, v1.ConditionFalse, now),
	}
	for _, tc := range []struct {
		name       string
		gate       bool
		controller bool
	}{
		{"enabled", true, true},
		{"gate disabled", false, true},
		{"controller disabled", true, false},
	} {
		t.Run(tc.name, func(t *testing.T) {
			featuregatetesting.SetFeatureGateDuringTest(t, utilfeature.DefaultFeatureGate, features.DeploymentReplicaSetTerminatingReplicas, tc.gate)
			rs := statusTestReplicaSet()
			// The desired count intentionally differs from the observed snapshot.
			rs.Spec.Replicas = ptr.To(int32(4))
			got := calculateStatus(rs, active, []*v1.Pod{{}, {}}, nil,
				ReplicaSetControllerFeatures{EnableStatusTerminatingReplicas: tc.controller}, now)
			if got.Replicas != 3 || got.FullyLabeledReplicas != 2 || got.ReadyReplicas != 2 || got.AvailableReplicas != 1 {
				t.Fatalf("unexpected snapshot counts: %+v", got)
			}
			if got.ObservedGeneration != 4 {
				t.Fatal("calculateStatus must leave observed generation to the update helper")
			}
			if tc.gate && tc.controller {
				if got.TerminatingReplicas == nil || *got.TerminatingReplicas != 2 {
					t.Fatalf("unexpected terminating replicas: %v", got.TerminatingReplicas)
				}
			} else if got.TerminatingReplicas != nil {
				t.Fatal("disabled terminating replicas must be nil")
			}
		})
	}
}

func TestCalculateStatusFailureConditions(t *testing.T) {
	rs := statusTestReplicaSet()
	other := NewReplicaSetCondition("Other", v1.ConditionTrue, "Existing", "keep")
	rs.Status.Conditions = []apps.ReplicaSetCondition{other}
	err := errors.New("create failed")
	got := calculateStatus(rs, nil, nil, err, DefaultReplicaSetControllerFeatures(), time.Now())
	failure := GetCondition(got, apps.ReplicaSetReplicaFailure)
	if failure == nil || failure.Reason != "FailedCreate" || failure.Message != err.Error() {
		t.Fatalf("missing failure condition: %+v", got.Conditions)
	}
	if !reflect.DeepEqual(rs.Status.Conditions, []apps.ReplicaSetCondition{other}) {
		t.Fatal("calculation changed the original conditions")
	}
	rs.Status = got
	got = calculateStatus(rs, nil, nil, nil, DefaultReplicaSetControllerFeatures(), time.Now())
	if !reflect.DeepEqual(got.Conditions, []apps.ReplicaSetCondition{other}) {
		t.Fatalf("successful management did not remove only the failure condition: %+v", got.Conditions)
	}
}

func TestUpdateReplicaSetStatusNoOp(t *testing.T) {
	rs := statusTestReplicaSet()
	rs.Status.ObservedGeneration = rs.Generation
	client := fake.NewSimpleClientset()
	got, err := updateReplicaSetStatus(client.AppsV1().ReplicaSets(rs.Namespace), rs, rs.Status)
	if err != nil || got != rs || len(client.Actions()) != 0 {
		t.Fatalf("no-op issued a request: result=%p err=%v actions=%v", got, err, client.Actions())
	}
}

func TestUpdateReplicaSetStatusRetry(t *testing.T) {
	for _, mode := range []string{"success", "get failure", "retry exhausted"} {
		t.Run(mode, func(t *testing.T) {
			rs := statusTestReplicaSet()
			original := rs.DeepCopy()
			newStatus := rs.Status
			newStatus.Replicas = 3
			client := fake.NewSimpleClientset()
			conflict := apierrors.NewConflict(schema.GroupResource{Group: "apps", Resource: "replicasets"}, rs.Name, errors.New("stale version"))
			getErr := errors.New("get failed")
			lastErr := errors.New("second update failed")
			updates, gets := 0, 0
			client.PrependReactor("update", "replicasets", func(action clienttesting.Action) (bool, runtime.Object, error) {
				updates++
				if action.GetSubresource() != "status" {
					t.Fatal("ordinary update used instead of status update")
				}
				submitted := action.(clienttesting.UpdateAction).GetObject().(*apps.ReplicaSet)
				if submitted.Status.ObservedGeneration != original.Generation || submitted.Status.Replicas != 3 {
					t.Fatalf("wrong submitted status: %+v", submitted.Status)
				}
				if updates == 1 {
					return true, nil, conflict
				}
				if submitted.ResourceVersion != "2" || submitted.Generation != 6 {
					t.Fatalf("retry did not use the fetched object: %+v", submitted.ObjectMeta)
				}
				if mode == "retry exhausted" {
					return true, nil, lastErr
				}
				return true, submitted.DeepCopy(), nil
			})
			client.PrependReactor("get", "replicasets", func(action clienttesting.Action) (bool, runtime.Object, error) {
				gets++
				if mode == "get failure" {
					return true, nil, getErr
				}
				fresh := original.DeepCopy()
				fresh.Generation, fresh.ResourceVersion = 6, "2"
				return true, fresh, nil
			})
			got, err := updateReplicaSetStatus(client.AppsV1().ReplicaSets(rs.Namespace), rs.DeepCopy(), newStatus)
			wantUpdates := 2
			switch mode {
			case "success":
				if err != nil || got == nil || got.Status.ObservedGeneration != 5 {
					t.Fatalf("retry result: got=%v err=%v", got, err)
				}
			case "get failure":
				wantUpdates = 1
				if got != nil || err != getErr {
					t.Fatalf("GET error did not take precedence: got=%v err=%v", got, err)
				}
			case "retry exhausted":
				if got != nil || err != lastErr {
					t.Fatalf("last update error not returned: got=%v err=%v", got, err)
				}
			}
			if updates != wantUpdates || gets != 1 {
				t.Fatalf("unexpected retry counts: updates=%d gets=%d", updates, gets)
			}
			if !reflect.DeepEqual(rs, original) {
				t.Fatal("update mutated the original snapshot instead of its deep copy")
			}
		})
	}
}
