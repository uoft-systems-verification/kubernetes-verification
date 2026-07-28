package serviceaccount

import (
	"kubernetes_model/apimodel"

	v1 "k8s.io/api/core/v1"
	apierrors "k8s.io/apimachinery/pkg/api/errors"
	metav1 "k8s.io/apimachinery/pkg/apis/meta/v1"
)

// A simplified serviceaccount controller. The following features are not included:
// * namespace lookup and phase checks; callers only enqueue active namespaces
// * configurable managed service accounts; only "default" is managed
// * event handling and workqueue retry

const defaultServiceAccountName = "default"

// syncNamespace ensures that an active namespace has its default ServiceAccount.
func syncNamespace(namespace string) error {
	_, err := apimodel.ModelState.ServiceAccountGet(namespace, defaultServiceAccountName)
	if err == nil {
		return nil
	}
	if !apierrors.IsNotFound(err) {
		return err
	}

	serviceAccount := &v1.ServiceAccount{
		ObjectMeta: metav1.ObjectMeta{
			Name:      defaultServiceAccountName,
			Namespace: namespace,
		},
	}

	_, err = apimodel.ModelState.ServiceAccountCreate(namespace, serviceAccount)
	if apierrors.IsAlreadyExists(err) {
		return nil
	}
	return err
}
