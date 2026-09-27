package replicaset

import (
	"context"
	"encoding/json"
	"io"
	"kubernetes_model/apimodel"
	"net/http"
	"reflect"
	"strings"
	"testing"
	"time"

	apps "k8s.io/api/apps/v1"
	apierrors "k8s.io/apimachinery/pkg/api/errors"
	metav1 "k8s.io/apimachinery/pkg/apis/meta/v1"
	"k8s.io/client-go/kubernetes"
	appslisters "k8s.io/client-go/listers/apps/v1"
	"k8s.io/client-go/rest"
	"k8s.io/client-go/tools/cache"
	"k8s.io/utils/ptr"
)

type statusRoundTripper func(*http.Request) (*http.Response, error)

func (f statusRoundTripper) RoundTrip(r *http.Request) (*http.Response, error) { return f(r) }

type statusClock struct {
	now   time.Time
	calls int
}

func (c *statusClock) Now() time.Time                  { c.calls++; return c.now }
func (c *statusClock) Since(t time.Time) time.Duration { return c.now.Sub(t) }

func TestSyncReplicaSetStatus(t *testing.T) {
	for _, tc := range []struct {
		name            string
		managementFails bool
		statusFails     bool
	}{
		{"success", false, false},
		{"status failure", false, true},
		{"management failure", true, false},
		{"both failures", true, true},
	} {
		t.Run(tc.name, func(t *testing.T) {
			oldState := apimodel.ModelState
			apimodel.ModelState = apimodel.NewState()
			t.Cleanup(func() { apimodel.ModelState = oldState })
			rs := statusTestReplicaSet()
			rs.UID = "rs-uid"
			rs.Spec.Replicas = ptr.To(int32(0))
			if tc.managementFails {
				rs.Spec.Replicas = ptr.To(int32(1))
			}
			original := rs.DeepCopy()
			indexer := cache.NewIndexer(cache.MetaNamespaceKeyFunc, cache.Indexers{})
			if err := indexer.Add(rs); err != nil {
				t.Fatal(err)
			}
			creates, updates, gets := 0, 0, 0
			transport := statusRoundTripper(func(req *http.Request) (*http.Response, error) {
				code := http.StatusOK
				var body any
				switch {
				case req.Method == http.MethodPost && strings.HasSuffix(req.URL.Path, "/pods"):
					creates++
					code = http.StatusForbidden
					body = metav1.Status{Status: metav1.StatusFailure, Reason: metav1.StatusReasonForbidden, Code: int32(code), Message: "pod creation failed"}
				case req.Method == http.MethodPut && strings.HasSuffix(req.URL.Path, "/replicasets/rs/status"):
					updates++
					var submitted apps.ReplicaSet
					if err := json.NewDecoder(req.Body).Decode(&submitted); err != nil {
						t.Fatal(err)
					}
					if submitted.Status.Replicas != 0 || submitted.Status.ObservedGeneration != original.Generation {
						t.Fatalf("wrong submitted snapshot status: %+v", submitted.Status)
					}
					if tc.managementFails && GetCondition(submitted.Status, apps.ReplicaSetReplicaFailure) == nil {
						t.Fatal("management failure was not included in status")
					}
					body = &submitted
					if tc.statusFails {
						code = http.StatusUnprocessableEntity
						body = metav1.Status{Status: metav1.StatusFailure, Reason: metav1.StatusReasonInvalid, Code: int32(code), Message: "status update failed"}
					}
				case req.Method == http.MethodGet && strings.HasSuffix(req.URL.Path, "/replicasets/rs"):
					gets++
					body = original
				default:
					t.Fatalf("unexpected API request: %s %s", req.Method, req.URL.Path)
				}
				data, err := json.Marshal(body)
				if err != nil {
					t.Fatal(err)
				}
				return &http.Response{StatusCode: code, Header: http.Header{"Content-Type": {"application/json"}}, Body: io.NopCloser(strings.NewReader(string(data)))}, nil
			})
			client, err := kubernetes.NewForConfigAndClient(&rest.Config{
				Host:          "http://replicaset.test",
				ContentConfig: rest.ContentConfig{ContentType: "application/json", AcceptContentTypes: "application/json"},
			}, &http.Client{Transport: transport})
			if err != nil {
				t.Fatal(err)
			}
			clk := &statusClock{now: time.Unix(1000, 0)}
			err = syncReplicaSet(context.Background(), client, appslisters.NewReplicaSetLister(indexer), BurstReplicas,
				clk, DefaultReplicaSetControllerFeatures(), rs.Namespace, rs.Name)
			switch {
			case tc.statusFails:
				if !apierrors.IsInvalid(err) {
					t.Fatalf("status error did not take precedence: %v", err)
				}
			case tc.managementFails:
				if !apierrors.IsForbidden(err) {
					t.Fatalf("management error not returned: %v", err)
				}
			default:
				if err != nil {
					t.Fatal(err)
				}
			}
			wantCreates, wantUpdates, wantGets := 0, 1, 0
			if tc.managementFails {
				wantCreates = 1
			}
			if tc.statusFails {
				wantUpdates, wantGets = 2, 1
			}
			if creates != wantCreates || updates != wantUpdates || gets != wantGets || clk.calls != 1 {
				t.Fatalf("wrong calls: creates=%d updates=%d gets=%d clock=%d", creates, updates, gets, clk.calls)
			}
			if !reflect.DeepEqual(rs, original) {
				t.Fatal("sync mutated the lister's ReplicaSet")
			}
		})
	}
}
