package wrapper

import (
	"context"
	"fmt"

	"kubernetes_model/apimodel"

	appsv1 "k8s.io/api/apps/v1"
	corev1 "k8s.io/api/core/v1"
	metav1 "k8s.io/apimachinery/pkg/apis/meta/v1"
	"k8s.io/apimachinery/pkg/runtime"
)

type objectWithMeta interface {
	runtime.Object
	metav1.Object
}

// Client is a local stand-in for client-go's gentype.Client.
type Client[T objectWithMeta] struct {
	namespace string
}

func NewClient[T objectWithMeta](namespace string) *Client[T] {
	return &Client[T]{
		namespace: namespace,
	}
}

func (c *Client[T]) Create(ctx context.Context, obj T, opts metav1.CreateOptions) (T, error) {
	var zero T

	switch typed := any(obj).(type) {
	case *corev1.Pod:
		created, err := apimodel.ModelState.PodCreate(c.namespace, typed)
		if err != nil {
			return zero, err
		}
		return any(created).(T), nil
	case *appsv1.ReplicaSet:
		created, err := apimodel.ModelState.ReplicaSetCreate(c.namespace, typed)
		if err != nil {
			return zero, err
		}
		return any(created).(T), nil
	default:
		return zero, fmt.Errorf("create unsupported object type %T", obj)
	}
}
