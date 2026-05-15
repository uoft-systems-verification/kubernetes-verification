package apimodel

import (
	"fmt"

	apierrors "k8s.io/apimachinery/pkg/api/errors"
	"k8s.io/apimachinery/pkg/api/meta"
	metav1 "k8s.io/apimachinery/pkg/apis/meta/v1"
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
