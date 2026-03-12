package generators

import (
	"fmt"

	appsv1 "k8s.io/api/apps/v1"
	corev1 "k8s.io/api/core/v1"
	"k8s.io/apimachinery/pkg/api/resource"
	metav1 "k8s.io/apimachinery/pkg/apis/meta/v1"
	"pgregory.net/rapid"
)

// MinimalReplicaSetGen generates minimal valid ReplicaSets.
func MinimalReplicaSetGen() *rapid.Generator[*appsv1.ReplicaSet] {
	return rapid.Custom(func(t *rapid.T) *appsv1.ReplicaSet {
		name := rapid.StringMatching(`[a-z][a-z0-9]{0,10}`).Draw(t, "name")
		appLabel := rapid.StringMatching(`[a-z][a-z0-9]{0,10}`).Draw(t, "appLabel")
		containerName := rapid.StringMatching(`[a-z][a-z0-9]{0,10}`).Draw(t, "containerName")
		replicas := int32(rapid.IntRange(0, 5).Draw(t, "replicas"))

		labels := map[string]string{"app": appLabel}

		return &appsv1.ReplicaSet{
			ObjectMeta: metav1.ObjectMeta{
				Name:      name,
				Namespace: "default",
			},
			Spec: appsv1.ReplicaSetSpec{
				Replicas: &replicas,
				Selector: &metav1.LabelSelector{
					MatchLabels: labels,
				},
				Template: corev1.PodTemplateSpec{
					ObjectMeta: metav1.ObjectMeta{
						Labels: labels,
					},
					Spec: corev1.PodSpec{
						Containers: []corev1.Container{{
							Name:  containerName,
							Image: "nginx:latest",
						}},
					},
				},
			},
		}
	})
}

// ComprehensiveReplicaSetMut mutates a pair of ReplicaSet update inputs in the same way.
//
// This split follows the normal ReplicaSet update path in Kubernetes release-1.34:
// - ValidateReplicaSetUpdate: https://github.com/kubernetes/kubernetes/blob/release-1.34/pkg/apis/apps/validation/validation.go#L763-L768
// - rsStrategy.PrepareForUpdate: https://github.com/kubernetes/kubernetes/blob/release-1.34/pkg/registry/apps/replicaset/strategy.go#L89-L106
func ComprehensiveReplicaSetMut(rt *rapid.T, modelRS, realRS *appsv1.ReplicaSet, exists, valid bool) {
	metadataInvalid := ObjectMetaMut(rt, modelRS, realRS, exists, valid)

	if valid {
		mutateAllowedReplicaSetUpdateFields(rt, modelRS, realRS, exists)
		return
	}

	if !exists || metadataInvalid {
		// The update already has a single clear rejection cause. Keep the spec/template
		// mutations on the normal update path to avoid obscuring it.
		mutateAllowedReplicaSetUpdateFields(rt, modelRS, realRS, exists)
		return
	}

	mutateAllowedReplicaSetUpdateFields(rt, modelRS, realRS, exists)
	mutateImmutableReplicaSetUpdateFields(rt, modelRS, realRS)
}

func mutateAllowedReplicaSetUpdateFields(rt *rapid.T, modelRS, realRS *appsv1.ReplicaSet, exists bool) {
	replicas := int32(rapid.IntRange(0, 5).Draw(rt, "updateRSReplicas"))
	if exists && modelRS.Spec.Replicas != nil && replicas == *modelRS.Spec.Replicas {
		replicas = (replicas + 1) % 6
	}
	modelRS.Spec.Replicas = &replicas
	realRS.Spec.Replicas = &replicas

	if rapid.Bool().Draw(rt, "updateRSMinReadySeconds") {
		minReadySeconds := int32(rapid.IntRange(0, 30).Draw(rt, "updateRSMinReadySecondsValue"))
		modelRS.Spec.MinReadySeconds = minReadySeconds
		realRS.Spec.MinReadySeconds = minReadySeconds
	}

	templateLabelKey := rapid.StringMatching(`[a-z][a-z0-9]{0,8}`).Draw(rt, "updateRSTemplateLabelKey")
	if modelRS.Spec.Selector != nil {
		if _, ok := modelRS.Spec.Selector.MatchLabels[templateLabelKey]; ok {
			templateLabelKey = "extra-update"
		}
	}
	templateLabelValue := rapid.StringMatching(`[a-z][a-z0-9-]{0,8}`).Draw(rt, "updateRSTemplateLabelValue")
	if modelRS.Spec.Template.Labels == nil {
		modelRS.Spec.Template.Labels = map[string]string{}
	}
	if realRS.Spec.Template.Labels == nil {
		realRS.Spec.Template.Labels = map[string]string{}
	}
	modelRS.Spec.Template.Labels[templateLabelKey] = templateLabelValue
	realRS.Spec.Template.Labels[templateLabelKey] = templateLabelValue

	mutateReplicaSetTemplateContainerImages(rt, modelRS.Spec.Template.Spec.Containers, realRS.Spec.Template.Spec.Containers)

	if len(modelRS.Spec.Template.Spec.Containers) > 0 && len(realRS.Spec.Template.Spec.Containers) > 0 &&
		rapid.Bool().Draw(rt, "updateRSTemplateEnv") {
		envName := rapid.StringMatching(`[A-Z][A-Z0-9_]{1,8}`).Draw(rt, "updateRSTemplateEnvName")
		envValue := rapid.StringMatching(`[a-z0-9-]{1,8}`).Draw(rt, "updateRSTemplateEnvValue")
		modelRS.Spec.Template.Spec.Containers[0].Env = append(modelRS.Spec.Template.Spec.Containers[0].Env, corev1.EnvVar{Name: envName, Value: envValue})
		realRS.Spec.Template.Spec.Containers[0].Env = append(realRS.Spec.Template.Spec.Containers[0].Env, corev1.EnvVar{Name: envName, Value: envValue})
	}

	if rapid.Bool().Draw(rt, "updateRSTemplateAnnotation") {
		annotationKey := rapid.StringMatching(`[a-z][a-z0-9]{0,8}`).Draw(rt, "updateRSTemplateAnnotationKey")
		annotationValue := rapid.StringMatching(`[a-z][a-z0-9-]{0,8}`).Draw(rt, "updateRSTemplateAnnotationValue")
		if modelRS.Spec.Template.Annotations == nil {
			modelRS.Spec.Template.Annotations = map[string]string{}
		}
		if realRS.Spec.Template.Annotations == nil {
			realRS.Spec.Template.Annotations = map[string]string{}
		}
		modelRS.Spec.Template.Annotations[annotationKey] = annotationValue
		realRS.Spec.Template.Annotations[annotationKey] = annotationValue
	}

	if rapid.Bool().Draw(rt, "updateRSTemplateNodeSelector") {
		nodeSelectorKey := rapid.StringMatching(`[a-z][a-z0-9]{0,8}`).Draw(rt, "updateRSTemplateNodeSelectorKey")
		nodeSelectorValue := rapid.StringMatching(`[a-z][a-z0-9-]{0,8}`).Draw(rt, "updateRSTemplateNodeSelectorValue")
		modelRS.Spec.Template.Spec.NodeSelector = map[string]string{nodeSelectorKey: nodeSelectorValue}
		realRS.Spec.Template.Spec.NodeSelector = map[string]string{nodeSelectorKey: nodeSelectorValue}
	}
}

func mutateReplicaSetTemplateContainerImages(rt *rapid.T, modelContainers, realContainers []corev1.Container) {
	for i := range modelContainers {
		if i >= len(realContainers) {
			break
		}

		image := rapid.SampledFrom([]string{
			"nginx:1.25",
			"nginx:1.27",
			"busybox:1.36",
			"alpine:3.19",
		}).Draw(rt, fmt.Sprintf("updateRSImage%d", i))
		if image == modelContainers[i].Image {
			image = "redis:7"
		}
		modelContainers[i].Image = image
		realContainers[i].Image = image
	}
}

func mutateImmutableReplicaSetUpdateFields(rt *rapid.T, modelRS, realRS *appsv1.ReplicaSet) {
	selectorValue := rapid.StringMatching(`[a-z][a-z0-9-]{2,8}`).Draw(rt, "updateRSSelectorValue")
	modelRS.Spec.Selector = &metav1.LabelSelector{
		MatchLabels: map[string]string{"app": selectorValue},
	}
	realRS.Spec.Selector = &metav1.LabelSelector{
		MatchLabels: map[string]string{"app": selectorValue},
	}

	if modelRS.Spec.Template.Labels == nil {
		modelRS.Spec.Template.Labels = map[string]string{}
	}
	if realRS.Spec.Template.Labels == nil {
		realRS.Spec.Template.Labels = map[string]string{}
	}
	modelRS.Spec.Template.Labels["app"] = selectorValue
	realRS.Spec.Template.Labels["app"] = selectorValue

	statusReplicas := int32(rapid.IntRange(0, 5).Draw(rt, "updateRSStatusReplicas"))
	readyReplicas := int32(rapid.IntRange(0, int(statusReplicas)).Draw(rt, "updateRSReadyReplicas"))
	availableReplicas := int32(rapid.IntRange(0, int(readyReplicas)).Draw(rt, "updateRSAvailableReplicas"))
	observedGeneration := int64(rapid.IntRange(1, 10).Draw(rt, "updateRSObservedGeneration"))
	modelRS.Status.Replicas = statusReplicas
	modelRS.Status.ReadyReplicas = readyReplicas
	modelRS.Status.AvailableReplicas = availableReplicas
	modelRS.Status.ObservedGeneration = observedGeneration
	realRS.Status.Replicas = statusReplicas
	realRS.Status.ReadyReplicas = readyReplicas
	realRS.Status.AvailableReplicas = availableReplicas
	realRS.Status.ObservedGeneration = observedGeneration
}

// ComprehensiveReplicaSetGen generates ReplicaSets with many randomized fields.
// This exercises more of the API surface area and defaulting logic.
func ComprehensiveReplicaSetGen() *rapid.Generator[*appsv1.ReplicaSet] {
	return rapid.Custom(func(t *rapid.T) *appsv1.ReplicaSet {
		name := rapid.StringMatching(`[a-z][a-z0-9]{0,10}`).Draw(t, "name")
		appLabel := rapid.StringMatching(`[a-z][a-z0-9]{0,10}`).Draw(t, "appLabel")
		containerName := rapid.StringMatching(`[a-z][a-z0-9]{0,10}`).Draw(t, "containerName")
		replicas := int32(rapid.IntRange(0, 5).Draw(t, "replicas"))

		labels := map[string]string{"app": appLabel}

		// Randomize additional labels
		if rapid.Bool().Draw(t, "hasExtraLabels") {
			numLabels := rapid.IntRange(1, 2).Draw(t, "numLabels")
			for i := 0; i < numLabels; i++ {
				key := rapid.StringMatching(`[a-z][a-z0-9]{0,8}`).Draw(t, fmt.Sprintf("labelKey%d", i))
				val := rapid.StringMatching(`[a-z][a-z0-9]{0,8}`).Draw(t, fmt.Sprintf("labelVal%d", i))
				labels[key] = val
			}
		}

		// Randomize annotations
		annotations := map[string]string{}
		if rapid.Bool().Draw(t, "hasAnnotations") {
			numAnnotations := rapid.IntRange(1, 2).Draw(t, "numAnnotations")
			for i := 0; i < numAnnotations; i++ {
				key := rapid.StringMatching(`[a-z][a-z0-9]{0,8}`).Draw(t, fmt.Sprintf("annoKey%d", i))
				val := rapid.StringMatching(`[a-z][a-z0-9-]{0,20}`).Draw(t, fmt.Sprintf("annoVal%d", i))
				annotations[key] = val
			}
		}

		// Build container with randomized fields
		container := corev1.Container{
			Name:  containerName,
			Image: "nginx:latest",
		}

		// Randomize container resources
		if rapid.Bool().Draw(t, "hasResources") {
			container.Resources = corev1.ResourceRequirements{
				Requests: corev1.ResourceList{
					corev1.ResourceCPU:    resource.MustParse(fmt.Sprintf("%dm", rapid.IntRange(10, 500).Draw(t, "cpuRequest"))),
					corev1.ResourceMemory: resource.MustParse(fmt.Sprintf("%dMi", rapid.IntRange(16, 256).Draw(t, "memRequest"))),
				},
			}
		}

		// Randomize environment variables
		if rapid.Bool().Draw(t, "hasEnv") {
			numEnvVars := rapid.IntRange(1, 2).Draw(t, "numEnvVars")
			container.Env = make([]corev1.EnvVar, numEnvVars)
			for i := 0; i < numEnvVars; i++ {
				container.Env[i] = corev1.EnvVar{
					Name:  rapid.StringMatching(`[A-Z][A-Z0-9_]{0,8}`).Draw(t, fmt.Sprintf("envName%d", i)),
					Value: rapid.StringMatching(`[a-z0-9]{0,10}`).Draw(t, fmt.Sprintf("envVal%d", i)),
				}
			}
		}

		// Build pod template spec
		templateSpec := corev1.PodTemplateSpec{
			ObjectMeta: metav1.ObjectMeta{
				Labels: labels,
			},
			Spec: corev1.PodSpec{
				Containers: []corev1.Container{container},
			},
		}

		// Randomize pod restart policy
		if rapid.Bool().Draw(t, "hasRestartPolicy") {
			templateSpec.Spec.RestartPolicy = rapid.SampledFrom([]corev1.RestartPolicy{
				corev1.RestartPolicyAlways,
				corev1.RestartPolicyOnFailure,
			}).Draw(t, "restartPolicy")
		}

		// Randomize DNS policy
		if rapid.Bool().Draw(t, "hasDNSPolicy") {
			templateSpec.Spec.DNSPolicy = rapid.SampledFrom([]corev1.DNSPolicy{
				corev1.DNSClusterFirst,
				corev1.DNSDefault,
			}).Draw(t, "dnsPolicy")
		}

		// Build ReplicaSet spec
		spec := appsv1.ReplicaSetSpec{
			Replicas: &replicas,
			Selector: &metav1.LabelSelector{
				MatchLabels: map[string]string{"app": appLabel},
			},
			Template: templateSpec,
		}

		// Randomize minReadySeconds
		if rapid.Bool().Draw(t, "hasMinReadySeconds") {
			spec.MinReadySeconds = int32(rapid.IntRange(0, 30).Draw(t, "minReadySeconds"))
		}

		meta := metav1.ObjectMeta{
			Name:      name,
			Namespace: "default",
			Labels:    labels,
		}
		if len(annotations) > 0 {
			meta.Annotations = annotations
		}

		return &appsv1.ReplicaSet{
			ObjectMeta: meta,
			Spec:       spec,
		}
	})
}

// InvalidReplicaSetGen generates known-invalid ReplicaSets for testing validation.
func InvalidReplicaSetGen() *rapid.Generator[*appsv1.ReplicaSet] {
	return rapid.Custom(func(t *rapid.T) *appsv1.ReplicaSet {
		invalidType := rapid.IntRange(0, 3).Draw(t, "invalidType")

		switch invalidType {
		case 0:
			// Selector doesn't match template labels
			return &appsv1.ReplicaSet{
				ObjectMeta: metav1.ObjectMeta{
					Name:      "test-rs",
					Namespace: "default",
				},
				Spec: appsv1.ReplicaSetSpec{
					Replicas: int32Ptr(1),
					Selector: &metav1.LabelSelector{
						MatchLabels: map[string]string{"app": "foo"},
					},
					Template: corev1.PodTemplateSpec{
						ObjectMeta: metav1.ObjectMeta{
							Labels: map[string]string{"app": "bar"}, // Doesn't match selector
						},
						Spec: corev1.PodSpec{
							Containers: []corev1.Container{{
								Name:  "container",
								Image: "nginx:latest",
							}},
						},
					},
				},
			}
		case 1:
			// Missing selector
			return &appsv1.ReplicaSet{
				ObjectMeta: metav1.ObjectMeta{
					Name:      "test-rs",
					Namespace: "default",
				},
				Spec: appsv1.ReplicaSetSpec{
					Replicas: int32Ptr(1),
					Template: corev1.PodTemplateSpec{
						ObjectMeta: metav1.ObjectMeta{
							Labels: map[string]string{"app": "test"},
						},
						Spec: corev1.PodSpec{
							Containers: []corev1.Container{{
								Name:  "container",
								Image: "nginx:latest",
							}},
						},
					},
				},
			}
		case 2:
			// Negative replicas
			return &appsv1.ReplicaSet{
				ObjectMeta: metav1.ObjectMeta{
					Name:      "test-rs",
					Namespace: "default",
				},
				Spec: appsv1.ReplicaSetSpec{
					Replicas: int32Ptr(-1),
					Selector: &metav1.LabelSelector{
						MatchLabels: map[string]string{"app": "test"},
					},
					Template: corev1.PodTemplateSpec{
						ObjectMeta: metav1.ObjectMeta{
							Labels: map[string]string{"app": "test"},
						},
						Spec: corev1.PodSpec{
							Containers: []corev1.Container{{
								Name:  "container",
								Image: "nginx:latest",
							}},
						},
					},
				},
			}
		default:
			// Invalid name
			return &appsv1.ReplicaSet{
				ObjectMeta: metav1.ObjectMeta{
					Name:      "INVALID_NAME",
					Namespace: "default",
				},
				Spec: appsv1.ReplicaSetSpec{
					Replicas: int32Ptr(1),
					Selector: &metav1.LabelSelector{
						MatchLabels: map[string]string{"app": "test"},
					},
					Template: corev1.PodTemplateSpec{
						ObjectMeta: metav1.ObjectMeta{
							Labels: map[string]string{"app": "test"},
						},
						Spec: corev1.PodSpec{
							Containers: []corev1.Container{{
								Name:  "container",
								Image: "nginx:latest",
							}},
						},
					},
				},
			}
		}
	})
}

func int32Ptr(i int32) *int32 {
	return &i
}
