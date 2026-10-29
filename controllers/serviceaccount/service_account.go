package serviceaccount

import (
	"context"

	v1 "k8s.io/api/core/v1"
	apierrors "k8s.io/apimachinery/pkg/api/errors"
	metav1 "k8s.io/apimachinery/pkg/apis/meta/v1"
	clientset "k8s.io/client-go/kubernetes"
	corelisters "k8s.io/client-go/listers/core/v1"
)

// A simplified serviceaccount controller. The following features are not included:
// * controller construction; the managed service accounts are listed below
// * creation error aggregation; the first error is returned
// * event handling and workqueue retry

var serviceAccountsToEnsure = []v1.ServiceAccount{
	{ObjectMeta: metav1.ObjectMeta{Name: "default"}},
}

// syncNamespace ensures that an active namespace has each configured ServiceAccount.
func syncNamespace(ctx context.Context, kubeClient *clientset.Clientset, nsLister corelisters.NamespaceLister, saLister corelisters.ServiceAccountLister, key string) error {
	namespace, err := nsLister.Get(key)
	if apierrors.IsNotFound(err) {
		return nil
	}
	if err != nil {
		return err
	}
	if namespace.Status.Phase != v1.NamespaceActive {
		return nil
	}

	for _, serviceAccount := range serviceAccountsToEnsure {
		_, err := saLister.ServiceAccounts(namespace.Name).Get(serviceAccount.Name)
		if err == nil {
			continue
		}
		if !apierrors.IsNotFound(err) {
			return err
		}

		serviceAccount.Namespace = namespace.Name
		var createOptions metav1.CreateOptions
		_, err = kubeClient.CoreV1().ServiceAccounts(namespace.Name).Create(ctx, &serviceAccount, createOptions)
		if apierrors.IsAlreadyExists(err) {
			continue
		}
		if err != nil {
			return err
		}
	}
	return nil
}
