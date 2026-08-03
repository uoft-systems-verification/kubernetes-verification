package generators

import (
	"fmt"

	appsv1 "k8s.io/api/apps/v1"
	corev1 "k8s.io/api/core/v1"
	"k8s.io/apimachinery/pkg/api/resource"
	metav1 "k8s.io/apimachinery/pkg/apis/meta/v1"
	"k8s.io/apimachinery/pkg/util/intstr"
	"pgregory.net/rapid"
)

// MinimalDeploymentGen generates minimal valid Deployments.
func MinimalDeploymentGen() *rapid.Generator[*appsv1.Deployment] {
	return rapid.Custom(func(t *rapid.T) *appsv1.Deployment {
		name := rapid.StringMatching(`[a-z][a-z0-9]{0,10}`).Draw(t, "name")
		appLabel := rapid.StringMatching(`[a-z][a-z0-9]{0,10}`).Draw(t, "appLabel")
		containerName := rapid.StringMatching(`[a-z][a-z0-9]{0,10}`).Draw(t, "containerName")
		replicas := int32(rapid.IntRange(0, 5).Draw(t, "replicas"))

		labels := map[string]string{"app": appLabel}

		return &appsv1.Deployment{
			ObjectMeta: metav1.ObjectMeta{
				Name:      name,
				Namespace: "default",
			},
			Spec: appsv1.DeploymentSpec{
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

// deploymentStrategyGen randomizes the deployment rollout strategy, staying within
// what ValidateDeploymentStrategy accepts (Recreate must not carry a rollingUpdate
// block; rolling maxSurge/maxUnavailable must not both resolve to zero).
func deploymentStrategyGen(t *rapid.T) appsv1.DeploymentStrategy {
	if rapid.Bool().Draw(t, "strategyRecreate") {
		return appsv1.DeploymentStrategy{Type: appsv1.RecreateDeploymentStrategyType}
	}

	strategy := appsv1.DeploymentStrategy{Type: appsv1.RollingUpdateDeploymentStrategyType}
	if rapid.Bool().Draw(t, "hasRollingUpdateBlock") {
		var maxSurge, maxUnavailable intstr.IntOrString
		if rapid.Bool().Draw(t, "maxSurgeIsPercent") {
			maxSurge = intstr.FromString(fmt.Sprintf("%d%%", rapid.IntRange(1, 100).Draw(t, "maxSurgePercent")))
		} else {
			maxSurge = intstr.FromInt32(int32(rapid.IntRange(0, 3).Draw(t, "maxSurgeInt")))
		}
		if rapid.Bool().Draw(t, "maxUnavailableIsPercent") {
			maxUnavailable = intstr.FromString(fmt.Sprintf("%d%%", rapid.IntRange(1, 100).Draw(t, "maxUnavailablePercent")))
		} else {
			maxUnavailable = intstr.FromInt32(int32(rapid.IntRange(0, 3).Draw(t, "maxUnavailableInt")))
		}
		// Both explicitly zero is rejected by validation.
		if maxSurge == intstr.FromInt32(0) && maxUnavailable == intstr.FromInt32(0) {
			maxUnavailable = intstr.FromInt32(1)
		}
		strategy.RollingUpdate = &appsv1.RollingUpdateDeployment{
			MaxSurge:       &maxSurge,
			MaxUnavailable: &maxUnavailable,
		}
	}
	return strategy
}

// ComprehensiveDeploymentGen generates Deployments with many randomized fields.
// This exercises more of the API surface area and defaulting logic.
func ComprehensiveDeploymentGen() *rapid.Generator[*appsv1.Deployment] {
	return rapid.Custom(func(t *rapid.T) *appsv1.Deployment {
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

		// Build pod template spec. Deployment templates must use RestartPolicy=Always,
		// so unlike the ReplicaSet generator we never randomize it.
		templateSpec := corev1.PodTemplateSpec{
			ObjectMeta: metav1.ObjectMeta{
				Labels: labels,
			},
			Spec: corev1.PodSpec{
				Containers: []corev1.Container{container},
			},
		}

		// Randomize DNS policy
		if rapid.Bool().Draw(t, "hasDNSPolicy") {
			templateSpec.Spec.DNSPolicy = rapid.SampledFrom([]corev1.DNSPolicy{
				corev1.DNSClusterFirst,
				corev1.DNSDefault,
			}).Draw(t, "dnsPolicy")
		}

		// Build Deployment spec
		spec := appsv1.DeploymentSpec{
			Replicas: &replicas,
			Selector: &metav1.LabelSelector{
				MatchLabels: map[string]string{"app": appLabel},
			},
			Template: templateSpec,
			Strategy: deploymentStrategyGen(t),
		}

		// Randomize minReadySeconds (progressDeadlineSeconds defaults to 600 and must
		// stay greater than minReadySeconds)
		if rapid.Bool().Draw(t, "hasMinReadySeconds") {
			spec.MinReadySeconds = int32(rapid.IntRange(0, 30).Draw(t, "minReadySeconds"))
		}

		// Randomize revisionHistoryLimit
		if rapid.Bool().Draw(t, "hasRevisionHistoryLimit") {
			revisionHistoryLimit := int32(rapid.IntRange(0, 10).Draw(t, "revisionHistoryLimit"))
			spec.RevisionHistoryLimit = &revisionHistoryLimit
		}

		// Randomize progressDeadlineSeconds (must be greater than minReadySeconds)
		if rapid.Bool().Draw(t, "hasProgressDeadlineSeconds") {
			progressDeadlineSeconds := int32(rapid.IntRange(60, 600).Draw(t, "progressDeadlineSeconds"))
			spec.ProgressDeadlineSeconds = &progressDeadlineSeconds
		}

		// Randomize paused
		if rapid.Bool().Draw(t, "hasPaused") {
			spec.Paused = rapid.Bool().Draw(t, "paused")
		}

		meta := metav1.ObjectMeta{
			Name:      name,
			Namespace: "default",
			Labels:    labels,
		}
		if len(annotations) > 0 {
			meta.Annotations = annotations
		}

		return &appsv1.Deployment{
			ObjectMeta: meta,
			Spec:       spec,
		}
	})
}

// InvalidDeploymentGen generates known-invalid Deployments for testing validation.
func InvalidDeploymentGen() *rapid.Generator[*appsv1.Deployment] {
	return rapid.Custom(func(t *rapid.T) *appsv1.Deployment {
		validTemplate := func(labels map[string]string) corev1.PodTemplateSpec {
			return corev1.PodTemplateSpec{
				ObjectMeta: metav1.ObjectMeta{
					Labels: labels,
				},
				Spec: corev1.PodSpec{
					Containers: []corev1.Container{{
						Name:  "container",
						Image: "nginx:latest",
					}},
				},
			}
		}

		invalidType := rapid.IntRange(0, 4).Draw(t, "invalidType")

		switch invalidType {
		case 0:
			// Selector doesn't match template labels
			return &appsv1.Deployment{
				ObjectMeta: metav1.ObjectMeta{
					Name:      "test-deployment",
					Namespace: "default",
				},
				Spec: appsv1.DeploymentSpec{
					Replicas: int32Ptr(1),
					Selector: &metav1.LabelSelector{
						MatchLabels: map[string]string{"app": "foo"},
					},
					Template: validTemplate(map[string]string{"app": "bar"}), // Doesn't match selector
				},
			}
		case 1:
			// Missing selector
			return &appsv1.Deployment{
				ObjectMeta: metav1.ObjectMeta{
					Name:      "test-deployment",
					Namespace: "default",
				},
				Spec: appsv1.DeploymentSpec{
					Replicas: int32Ptr(1),
					Template: validTemplate(map[string]string{"app": "test"}),
				},
			}
		case 2:
			// Negative replicas
			return &appsv1.Deployment{
				ObjectMeta: metav1.ObjectMeta{
					Name:      "test-deployment",
					Namespace: "default",
				},
				Spec: appsv1.DeploymentSpec{
					Replicas: int32Ptr(-1),
					Selector: &metav1.LabelSelector{
						MatchLabels: map[string]string{"app": "test"},
					},
					Template: validTemplate(map[string]string{"app": "test"}),
				},
			}
		case 3:
			// Recreate strategy must not carry a rollingUpdate block
			maxSurge := intstr.FromInt32(1)
			maxUnavailable := intstr.FromInt32(1)
			return &appsv1.Deployment{
				ObjectMeta: metav1.ObjectMeta{
					Name:      "test-deployment",
					Namespace: "default",
				},
				Spec: appsv1.DeploymentSpec{
					Replicas: int32Ptr(1),
					Selector: &metav1.LabelSelector{
						MatchLabels: map[string]string{"app": "test"},
					},
					Template: validTemplate(map[string]string{"app": "test"}),
					Strategy: appsv1.DeploymentStrategy{
						Type: appsv1.RecreateDeploymentStrategyType,
						RollingUpdate: &appsv1.RollingUpdateDeployment{
							MaxSurge:       &maxSurge,
							MaxUnavailable: &maxUnavailable,
						},
					},
				},
			}
		default:
			// Invalid name
			return &appsv1.Deployment{
				ObjectMeta: metav1.ObjectMeta{
					Name:      "INVALID_NAME",
					Namespace: "default",
				},
				Spec: appsv1.DeploymentSpec{
					Replicas: int32Ptr(1),
					Selector: &metav1.LabelSelector{
						MatchLabels: map[string]string{"app": "test"},
					},
					Template: validTemplate(map[string]string{"app": "test"}),
				},
			}
		}
	})
}

// ComprehensiveDeploymentMut mutates a pair of Deployment update inputs in the same way.
//
// This split follows the normal Deployment update path in Kubernetes release-1.34:
// - ValidateDeploymentUpdate: https://github.com/kubernetes/kubernetes/blob/release-1.34/pkg/apis/apps/validation/validation.go#L708-L716
// - deploymentStrategy.PrepareForUpdate: https://github.com/kubernetes/kubernetes/blob/release-1.34/pkg/registry/apps/deployment/strategy.go#L83-L106
func ComprehensiveDeploymentMut(rt *rapid.T, modelD, realD *appsv1.Deployment, exists, valid bool) {
	metadataInvalid := ObjectMetaMut(rt, modelD, realD, exists, valid)

	if valid {
		mutateAllowedDeploymentUpdateFields(rt, modelD, realD, exists)
		return
	}

	if !exists || metadataInvalid {
		// The update already has a single clear rejection cause. Keep the spec/template
		// mutations on the normal update path to avoid obscuring it.
		mutateAllowedDeploymentUpdateFields(rt, modelD, realD, exists)
		return
	}

	mutateAllowedDeploymentUpdateFields(rt, modelD, realD, exists)
	mutateImmutableDeploymentUpdateFields(rt, modelD, realD)
}

// ComprehensiveDeploymentStatusMut mutates a pair of Deployment status update inputs in the same way.
func ComprehensiveDeploymentStatusMut(rt *rapid.T, modelD, realD *appsv1.Deployment, exists, valid bool) {
	metadataInvalid := ObjectMetaMut(rt, modelD, realD, exists, valid)

	if valid {
		mutateAllowedDeploymentStatusFields(rt, modelD, realD)
		return
	}

	if !exists || metadataInvalid {
		mutateAllowedDeploymentStatusFields(rt, modelD, realD)
		return
	}

	mutateInvalidDeploymentStatusFields(modelD, realD)
}

func mutateAllowedDeploymentUpdateFields(rt *rapid.T, modelD, realD *appsv1.Deployment, exists bool) {
	replicas := int32(rapid.IntRange(0, 5).Draw(rt, "updateDeploymentReplicas"))
	if exists && modelD.Spec.Replicas != nil && replicas == *modelD.Spec.Replicas {
		replicas = (replicas + 1) % 6
	}
	modelD.Spec.Replicas = &replicas
	realD.Spec.Replicas = &replicas

	if rapid.Bool().Draw(rt, "updateDeploymentMinReadySeconds") {
		minReadySeconds := int32(rapid.IntRange(0, 30).Draw(rt, "updateDeploymentMinReadySecondsValue"))
		modelD.Spec.MinReadySeconds = minReadySeconds
		realD.Spec.MinReadySeconds = minReadySeconds
	}

	if rapid.Bool().Draw(rt, "updateDeploymentStrategy") {
		strategy := deploymentStrategyGen(rt)
		modelD.Spec.Strategy = *strategy.DeepCopy()
		realD.Spec.Strategy = *strategy.DeepCopy()
	}

	if rapid.Bool().Draw(rt, "updateDeploymentPaused") {
		paused := rapid.Bool().Draw(rt, "updateDeploymentPausedValue")
		modelD.Spec.Paused = paused
		realD.Spec.Paused = paused
	}

	templateLabelKey := rapid.StringMatching(`[a-z][a-z0-9]{0,8}`).Draw(rt, "updateDeploymentTemplateLabelKey")
	if modelD.Spec.Selector != nil {
		if _, ok := modelD.Spec.Selector.MatchLabels[templateLabelKey]; ok {
			templateLabelKey = "extra-update"
		}
	}
	templateLabelValue := rapid.StringMatching(`[a-z][a-z0-9-]{0,8}`).Draw(rt, "updateDeploymentTemplateLabelValue")
	if modelD.Spec.Template.Labels == nil {
		modelD.Spec.Template.Labels = map[string]string{}
	}
	if realD.Spec.Template.Labels == nil {
		realD.Spec.Template.Labels = map[string]string{}
	}
	modelD.Spec.Template.Labels[templateLabelKey] = templateLabelValue
	realD.Spec.Template.Labels[templateLabelKey] = templateLabelValue

	mutateReplicaSetTemplateContainerImages(rt, modelD.Spec.Template.Spec.Containers, realD.Spec.Template.Spec.Containers)

	if len(modelD.Spec.Template.Spec.Containers) > 0 && len(realD.Spec.Template.Spec.Containers) > 0 &&
		rapid.Bool().Draw(rt, "updateDeploymentTemplateEnv") {
		envName := rapid.StringMatching(`[A-Z][A-Z0-9_]{1,8}`).Draw(rt, "updateDeploymentTemplateEnvName")
		envValue := rapid.StringMatching(`[a-z0-9-]{1,8}`).Draw(rt, "updateDeploymentTemplateEnvValue")
		modelD.Spec.Template.Spec.Containers[0].Env = append(modelD.Spec.Template.Spec.Containers[0].Env, corev1.EnvVar{Name: envName, Value: envValue})
		realD.Spec.Template.Spec.Containers[0].Env = append(realD.Spec.Template.Spec.Containers[0].Env, corev1.EnvVar{Name: envName, Value: envValue})
	}

	if rapid.Bool().Draw(rt, "updateDeploymentTemplateAnnotation") {
		annotationKey := rapid.StringMatching(`[a-z][a-z0-9]{0,8}`).Draw(rt, "updateDeploymentTemplateAnnotationKey")
		annotationValue := rapid.StringMatching(`[a-z][a-z0-9-]{0,8}`).Draw(rt, "updateDeploymentTemplateAnnotationValue")
		if modelD.Spec.Template.Annotations == nil {
			modelD.Spec.Template.Annotations = map[string]string{}
		}
		if realD.Spec.Template.Annotations == nil {
			realD.Spec.Template.Annotations = map[string]string{}
		}
		modelD.Spec.Template.Annotations[annotationKey] = annotationValue
		realD.Spec.Template.Annotations[annotationKey] = annotationValue
	}

	if rapid.Bool().Draw(rt, "updateDeploymentTemplateNodeSelector") {
		nodeSelectorKey := rapid.StringMatching(`[a-z][a-z0-9]{0,8}`).Draw(rt, "updateDeploymentTemplateNodeSelectorKey")
		nodeSelectorValue := rapid.StringMatching(`[a-z][a-z0-9-]{0,8}`).Draw(rt, "updateDeploymentTemplateNodeSelectorValue")
		modelD.Spec.Template.Spec.NodeSelector = map[string]string{nodeSelectorKey: nodeSelectorValue}
		realD.Spec.Template.Spec.NodeSelector = map[string]string{nodeSelectorKey: nodeSelectorValue}
	}
}

func mutateImmutableDeploymentUpdateFields(rt *rapid.T, modelD, realD *appsv1.Deployment) {
	selectorValue := rapid.StringMatching(`[a-z][a-z0-9-]{2,8}`).Draw(rt, "updateDeploymentSelectorValue")
	modelD.Spec.Selector = &metav1.LabelSelector{
		MatchLabels: map[string]string{"app": selectorValue},
	}
	realD.Spec.Selector = &metav1.LabelSelector{
		MatchLabels: map[string]string{"app": selectorValue},
	}

	if modelD.Spec.Template.Labels == nil {
		modelD.Spec.Template.Labels = map[string]string{}
	}
	if realD.Spec.Template.Labels == nil {
		realD.Spec.Template.Labels = map[string]string{}
	}
	modelD.Spec.Template.Labels["app"] = selectorValue
	realD.Spec.Template.Labels["app"] = selectorValue
}

func mutateAllowedDeploymentStatusFields(rt *rapid.T, modelD, realD *appsv1.Deployment) {
	replicas := int32(rapid.IntRange(0, 5).Draw(rt, "updateDeploymentStatusReplicas"))
	updatedReplicas := int32(rapid.IntRange(0, int(replicas)).Draw(rt, "updateDeploymentStatusUpdatedReplicas"))
	readyReplicas := int32(rapid.IntRange(0, int(replicas)).Draw(rt, "updateDeploymentStatusReadyReplicas"))
	availableReplicas := int32(rapid.IntRange(0, int(readyReplicas)).Draw(rt, "updateDeploymentStatusAvailableReplicas"))
	unavailableReplicas := int32(rapid.IntRange(0, 5).Draw(rt, "updateDeploymentStatusUnavailableReplicas"))
	observedGeneration := int64(rapid.IntRange(0, 10).Draw(rt, "updateDeploymentStatusObservedGeneration"))

	modelD.Status.Replicas = replicas
	modelD.Status.UpdatedReplicas = updatedReplicas
	modelD.Status.ReadyReplicas = readyReplicas
	modelD.Status.AvailableReplicas = availableReplicas
	modelD.Status.UnavailableReplicas = unavailableReplicas
	modelD.Status.ObservedGeneration = observedGeneration
	realD.Status.Replicas = replicas
	realD.Status.UpdatedReplicas = updatedReplicas
	realD.Status.ReadyReplicas = readyReplicas
	realD.Status.AvailableReplicas = availableReplicas
	realD.Status.UnavailableReplicas = unavailableReplicas
	realD.Status.ObservedGeneration = observedGeneration
}

func mutateInvalidDeploymentStatusFields(modelD, realD *appsv1.Deployment) {
	modelD.Status.Replicas = -1
	realD.Status.Replicas = -1
}
