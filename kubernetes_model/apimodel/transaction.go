package apimodel

import (
	"fmt"

	corev1 "k8s.io/api/core/v1"
	apierrors "k8s.io/apimachinery/pkg/api/errors"
	"k8s.io/apimachinery/pkg/api/meta"
	metav1 "k8s.io/apimachinery/pkg/apis/meta/v1"
	"k8s.io/apiserver/pkg/registry/rest"
)

func preconditionUIDMismatch(options metav1.DeleteOptions, metadata metav1.Object) bool {
	return options.Preconditions != nil && options.Preconditions.UID != nil && *options.Preconditions.UID != metadata.GetUID()
}

func setPreconditionResourceVersion(options *metav1.DeleteOptions, metadata metav1.Object) {
	rv := metadata.GetResourceVersion()
	if options.Preconditions == nil {
		options.Preconditions = &metav1.Preconditions{}
	}
	options.Preconditions.ResourceVersion = &rv
}

func (s *State) deleteTx(key KKey, options metav1.DeleteOptions) error {
	for {
		optionsCopy := *options.DeepCopy()

		obj, err := s.get(key)
		if err != nil {
			return err
		}

		metadata, err := meta.Accessor(obj)
		if err != nil {
			return fmt.Errorf("failed to access object metadata: %w", err)
		}

		if preconditionUIDMismatch(optionsCopy, metadata) {
			return newPreconditionUIDConflictError(
				key.Kind,
				metadata.GetName(),
				string(*optionsCopy.Preconditions.UID),
				string(metadata.GetUID()),
			)
		}

		setPreconditionResourceVersion(&optionsCopy, metadata)

		err = s.delete(key, optionsCopy)
		if apierrors.IsConflict(err) {
			continue
		}
		return err
	}
}

func (s *State) updateTx(kind, namespace string, obj interface{}) (interface{}, error) {
	for {
		objCopy := deepCopy(obj)
		metadata, err := meta.Accessor(objCopy)
		if err != nil {
			return nil, fmt.Errorf("failed to access object metadata: %w", err)
		}

		if err = rest.EnsureObjectNamespaceMatchesRequestNamespace(namespace, metadata); err != nil {
			return nil, err
		}

		name := metadata.GetName()
		if name == "" {
			return nil, apierrors.NewBadRequest(fmt.Sprintf("object of kind %q must specify a name for update", kind))
		}

		key := KKey{
			Kind:      kind,
			Name:      name,
			Namespace: namespace,
		}

		existingObj, err := s.get(key)
		if err != nil {
			return nil, err
		}

		existingMetadata, err := meta.Accessor(existingObj)
		if err != nil {
			return nil, fmt.Errorf("failed to access existing object metadata: %w", err)
		}

		metadata.SetResourceVersion(existingMetadata.GetResourceVersion())

		updatedObj, err := s.update(kind, namespace, objCopy)
		if apierrors.IsConflict(err) {
			continue
		}
		return updatedObj, err
	}
}

func (s *State) PodUpdateTx(namespace string, pod *corev1.Pod) (*corev1.Pod, error) {
	obj, err := s.updateTx("Pod", namespace, pod)
	if err != nil {
		return nil, err
	}

	updatedPod, ok := obj.(*corev1.Pod)
	if !ok {
		return nil, fmt.Errorf("transactional update returned unexpected type %T", obj)
	}

	return updatedPod, nil
}

func (s *State) updateStatusTx(kind, namespace string, obj interface{}) (interface{}, error) {
	for {
		objCopy := deepCopy(obj)
		metadata, err := meta.Accessor(objCopy)
		if err != nil {
			return nil, fmt.Errorf("failed to access object metadata: %w", err)
		}

		if err = rest.EnsureObjectNamespaceMatchesRequestNamespace(namespace, metadata); err != nil {
			return nil, err
		}

		name := metadata.GetName()
		if name == "" {
			return nil, apierrors.NewBadRequest(fmt.Sprintf("object of kind %q must specify a name for status update", kind))
		}

		key := KKey{
			Kind:      kind,
			Name:      name,
			Namespace: namespace,
		}

		existingObj, err := s.get(key)
		if err != nil {
			return nil, err
		}

		existingMetadata, err := meta.Accessor(existingObj)
		if err != nil {
			return nil, fmt.Errorf("failed to access existing object metadata: %w", err)
		}

		metadata.SetResourceVersion(existingMetadata.GetResourceVersion())

		updatedObj, err := s.updateStatus(kind, namespace, objCopy)
		if apierrors.IsConflict(err) {
			continue
		}
		return updatedObj, err
	}
}
