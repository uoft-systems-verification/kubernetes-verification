package serviceaccount

import (
	"sync"
	"testing"

	"kubernetes_model/apimodel"

	v1 "k8s.io/api/core/v1"
	metav1 "k8s.io/apimachinery/pkg/apis/meta/v1"
)

func TestSyncNamespaceCreatesDefaultServiceAccount(t *testing.T) {
	apimodel.ModelState = apimodel.NewState()

	if err := syncNamespace("test"); err != nil {
		t.Fatalf("syncNamespace: %v", err)
	}

	serviceAccount, err := apimodel.ModelState.ServiceAccountGet("test", defaultServiceAccountName)
	if err != nil {
		t.Fatalf("ServiceAccountGet: %v", err)
	}
	if serviceAccount.Name != defaultServiceAccountName {
		t.Fatalf("expected name %q, got %q", defaultServiceAccountName, serviceAccount.Name)
	}
	if serviceAccount.Namespace != "test" {
		t.Fatalf("expected namespace %q, got %q", "test", serviceAccount.Namespace)
	}
}

func TestSyncNamespaceIsIdempotent(t *testing.T) {
	apimodel.ModelState = apimodel.NewState()

	if err := syncNamespace("test"); err != nil {
		t.Fatalf("first syncNamespace: %v", err)
	}
	first, err := apimodel.ModelState.ServiceAccountGet("test", defaultServiceAccountName)
	if err != nil {
		t.Fatalf("first ServiceAccountGet: %v", err)
	}

	if err := syncNamespace("test"); err != nil {
		t.Fatalf("second syncNamespace: %v", err)
	}
	second, err := apimodel.ModelState.ServiceAccountGet("test", defaultServiceAccountName)
	if err != nil {
		t.Fatalf("second ServiceAccountGet: %v", err)
	}

	if first.UID != second.UID {
		t.Fatalf("idempotent sync replaced ServiceAccount: first UID %q, second UID %q", first.UID, second.UID)
	}
	if first.ResourceVersion != second.ResourceVersion {
		t.Fatalf("idempotent sync updated ServiceAccount: first resourceVersion %q, second %q", first.ResourceVersion, second.ResourceVersion)
	}
}

func TestSyncNamespacePreservesExistingServiceAccount(t *testing.T) {
	apimodel.ModelState = apimodel.NewState()

	existing, err := apimodel.ModelState.ServiceAccountCreate("test", &v1.ServiceAccount{
		ObjectMeta: metav1.ObjectMeta{
			Name:      defaultServiceAccountName,
			Namespace: "test",
			Labels:    map[string]string{"managed-by": "user"},
		},
	})
	if err != nil {
		t.Fatalf("ServiceAccountCreate: %v", err)
	}

	if err := syncNamespace("test"); err != nil {
		t.Fatalf("syncNamespace: %v", err)
	}
	after, err := apimodel.ModelState.ServiceAccountGet("test", defaultServiceAccountName)
	if err != nil {
		t.Fatalf("ServiceAccountGet: %v", err)
	}

	if after.UID != existing.UID {
		t.Fatalf("sync replaced existing ServiceAccount: before UID %q, after UID %q", existing.UID, after.UID)
	}
	if after.Labels["managed-by"] != "user" {
		t.Fatalf("sync modified existing labels: %#v", after.Labels)
	}
}

func TestSyncNamespaceToleratesConcurrentCreation(t *testing.T) {
	apimodel.ModelState = apimodel.NewState()

	const reconciles = 20
	errs := make(chan error, reconciles)
	var wg sync.WaitGroup
	for range reconciles {
		wg.Add(1)
		go func() {
			defer wg.Done()
			errs <- syncNamespace("test")
		}()
	}
	wg.Wait()
	close(errs)

	for err := range errs {
		if err != nil {
			t.Fatalf("syncNamespace: %v", err)
		}
	}
	if _, err := apimodel.ModelState.ServiceAccountGet("test", defaultServiceAccountName); err != nil {
		t.Fatalf("ServiceAccountGet: %v", err)
	}
}
