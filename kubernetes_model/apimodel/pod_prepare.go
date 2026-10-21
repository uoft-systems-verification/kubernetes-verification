package apimodel

import (
	corev1 "k8s.io/api/core/v1"
	"k8s.io/kubernetes/pkg/api/legacyscheme"
)

// PreviewPodCreate returns the object produced by the model's create-time
// defaulting, mutating admission, and REST preparation, without validating or
// storing it. This lets controllers compare specs independently of metadata
// validation (for example Pod-template finalizers). The input is left unchanged.
func PreviewPodCreate(pod *corev1.Pod) (*corev1.Pod, error) {
	prepared := pod.DeepCopy()
	legacy, err := prepareForCreate(prepared)
	if err != nil {
		return nil, err
	}
	if err := legacyscheme.Scheme.Convert(legacy, prepared, nil); err != nil {
		return nil, err
	}
	return prepared, nil
}
