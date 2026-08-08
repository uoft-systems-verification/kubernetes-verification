package serviceaccount

import (
	"kubernetes_model/apimodel"

	v1 "k8s.io/api/core/v1"
	apierrors "k8s.io/apimachinery/pkg/api/errors"
	metav1 "k8s.io/apimachinery/pkg/apis/meta/v1"
)

// A simplified serviceaccount controller. The following features are not included:
// * namespace lookup; callers pass the current namespace object
// * controller construction; the managed service accounts are listed below
// * creation error aggregation; the first error is returned
// * event handling and workqueue retry

var serviceAccountsToEnsure = []v1.ServiceAccount{
	{ObjectMeta: metav1.ObjectMeta{Name: "default"}},
}

// syncNamespace ensures that an active namespace has each configured ServiceAccount.
// A nil namespace represents a namespace that is no longer present.
func syncNamespace(namespace *v1.Namespace) error {
	if namespace == nil || namespace.Status.Phase != v1.NamespaceActive {
		return nil
	}

	for _, serviceAccount := range serviceAccountsToEnsure {
		_, err := apimodel.ModelState.ServiceAccountGet(namespace.Name, serviceAccount.Name)
		if err == nil {
			continue
		}
		if !apierrors.IsNotFound(err) {
			return err
		}

		serviceAccount.Namespace = namespace.Name
		_, err = apimodel.ModelState.ServiceAccountCreate(namespace.Name, &serviceAccount)
		if apierrors.IsAlreadyExists(err) {
			continue
		}
		if err != nil {
			return err
		}
	}
	return nil
}
