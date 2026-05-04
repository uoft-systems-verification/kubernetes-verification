package generators

import (
	"fmt"

	corev1 "k8s.io/api/core/v1"
	"k8s.io/apimachinery/pkg/api/resource"
	metav1 "k8s.io/apimachinery/pkg/apis/meta/v1"
	"pgregory.net/rapid"
)

// MinimalPodGen generates minimal valid pods for debugging.
func MinimalPodGen() *rapid.Generator[*corev1.Pod] {
	return rapid.Custom(func(t *rapid.T) *corev1.Pod {
		name := rapid.StringMatching(`[a-z][a-z0-9]{0,10}`).Draw(t, "name")
		containerName := rapid.StringMatching(`[a-z][a-z0-9]{0,10}`).Draw(t, "containerName")
		image := rapid.SampledFrom([]string{
			"nginx:latest",
			"busybox:1.36",
			"alpine:3.19",
			"redis:7",
		}).Draw(t, "image")

		return &corev1.Pod{
			ObjectMeta: metav1.ObjectMeta{
				Name:      name,
				Namespace: "default",
			},
			Spec: corev1.PodSpec{
				Containers: []corev1.Container{{
					Name:  containerName,
					Image: image,
				}},
			},
		}
	})
}

// ComprehensivePodMut mutates a pair of Pod update inputs in the same way.
//
// This split follows the normal Pod update path in Kubernetes release-1.34:
// - ValidatePodUpdate: https://github.com/kubernetes/kubernetes/blob/release-1.34/pkg/apis/core/validation/validation.go#L5573-L5664
// - podStrategy.PrepareForUpdate: https://github.com/kubernetes/kubernetes/blob/release-1.34/pkg/registry/core/pod/strategy.go#L103-L108
func ComprehensivePodMut(rt *rapid.T, modelPod, realPod *corev1.Pod, exists, valid bool) {
	metadataInvalid := ObjectMetaMut(rt, modelPod, realPod, exists, valid)

	if valid {
		mutateAllowedPodSpecFields(rt, modelPod, realPod)
		return
	}

	if !exists || metadataInvalid {
		// The update is already invalid because the object is missing or metadata was
		// corrupted. Keep the spec on a normal update path so the rejection cause stays simple.
		mutateAllowedPodSpecFields(rt, modelPod, realPod)
		return
	}

	mutateAllowedPodSpecFields(rt, modelPod, realPod)
	mutateImmutablePodUpdateFields(rt, modelPod, realPod)
}

// ComprehensivePodStatusMut mutates a pair of Pod status update inputs in the same way.
func ComprehensivePodStatusMut(rt *rapid.T, modelPod, realPod *corev1.Pod, exists, valid bool) {
	metadataInvalid := ObjectMetaMut(rt, modelPod, realPod, exists, valid)

	if valid {
		mutateAllowedPodStatusFields(rt, modelPod, realPod)
		return
	}

	if !exists || metadataInvalid {
		mutateAllowedPodStatusFields(rt, modelPod, realPod)
		return
	}

	mutateInvalidPodStatusFields(modelPod, realPod)
}

func mutateAllowedPodSpecFields(rt *rapid.T, modelPod, realPod *corev1.Pod) {
	mutatePodContainerImages(rt, modelPod.Spec.Containers, realPod.Spec.Containers, "updatePodContainerImage")
	mutatePodContainerImages(rt, modelPod.Spec.InitContainers, realPod.Spec.InitContainers, "updatePodInitContainerImage")

	if rapid.Bool().Draw(rt, "updatePodActiveDeadlineSeconds") {
		var seconds int64
		if modelPod.Spec.ActiveDeadlineSeconds == nil {
			seconds = int64(rapid.IntRange(1, 300).Draw(rt, "updatePodActiveDeadlineValue"))
		} else {
			oldSeconds := *modelPod.Spec.ActiveDeadlineSeconds
			if oldSeconds <= 0 {
				seconds = 0
			} else {
				seconds = int64(rapid.IntRange(0, int(oldSeconds)).Draw(rt, "updatePodActiveDeadlineValue"))
				if seconds == oldSeconds {
					seconds = oldSeconds - 1
				}
			}
		}
		modelPod.Spec.ActiveDeadlineSeconds = &seconds
		realPod.Spec.ActiveDeadlineSeconds = &seconds
	}

	if rapid.Bool().Draw(rt, "updatePodAddToleration") {
		toleration := corev1.Toleration{
			Key:      rapid.SampledFrom([]string{"example.com/not-ready", "example.com/drain", "example.com/spot"}).Draw(rt, "updatePodTolerationKey"),
			Operator: corev1.TolerationOpExists,
			Effect:   corev1.TaintEffectNoSchedule,
		}
		modelPod.Spec.Tolerations = append(modelPod.Spec.Tolerations, toleration)
		realPod.Spec.Tolerations = append(realPod.Spec.Tolerations, toleration)
	}

	if len(modelPod.Spec.SchedulingGates) > 0 && len(realPod.Spec.SchedulingGates) > 0 &&
		rapid.Bool().Draw(rt, "updatePodDeleteSchedulingGate") {
		idx := rapid.IntRange(0, len(modelPod.Spec.SchedulingGates)-1).Draw(rt, "updatePodSchedulingGateIdx")
		modelPod.Spec.SchedulingGates = append(modelPod.Spec.SchedulingGates[:idx], modelPod.Spec.SchedulingGates[idx+1:]...)
		realPod.Spec.SchedulingGates = append(realPod.Spec.SchedulingGates[:idx], realPod.Spec.SchedulingGates[idx+1:]...)
	}

	if modelPod.Spec.TerminationGracePeriodSeconds != nil &&
		realPod.Spec.TerminationGracePeriodSeconds != nil &&
		*modelPod.Spec.TerminationGracePeriodSeconds < 0 &&
		rapid.Bool().Draw(rt, "updatePodNegativeTerminationGracePeriod") {
		one := int64(1)
		modelPod.Spec.TerminationGracePeriodSeconds = &one
		realPod.Spec.TerminationGracePeriodSeconds = &one
	}
}

func mutateAllowedPodStatusFields(rt *rapid.T, modelPod, realPod *corev1.Pod) {
	phase := rapid.SampledFrom([]corev1.PodPhase{
		corev1.PodPending,
		corev1.PodRunning,
		corev1.PodSucceeded,
		corev1.PodFailed,
		corev1.PodUnknown,
	}).Draw(rt, "updatePodStatusPhase")
	modelPod.Status.Phase = phase
	realPod.Status.Phase = phase

	observedGeneration := int64(rapid.IntRange(0, 10).Draw(rt, "updatePodStatusObservedGeneration"))
	modelPod.Status.ObservedGeneration = observedGeneration
	realPod.Status.ObservedGeneration = observedGeneration

	reason := rapid.SampledFrom([]string{"Scheduled", "Running", "Completed"}).Draw(rt, "updatePodStatusReason")
	message := rapid.SampledFrom([]string{"pod scheduled", "containers running", "completed"}).Draw(rt, "updatePodStatusMessage")
	modelPod.Status.Reason = reason
	modelPod.Status.Message = message
	realPod.Status.Reason = reason
	realPod.Status.Message = message
}

func mutateInvalidPodStatusFields(modelPod, realPod *corev1.Pod) {
	modelPod.Status.ObservedGeneration = -1
	realPod.Status.ObservedGeneration = -1
}

func mutatePodContainerImages(rt *rapid.T, modelContainers, realContainers []corev1.Container, drawPrefix string) {
	for i := range modelContainers {
		if i >= len(realContainers) {
			break
		}

		image := rapid.SampledFrom([]string{
			"nginx:1.25",
			"nginx:1.27",
			"busybox:1.36",
			"alpine:3.19",
		}).Draw(rt, fmt.Sprintf("%s%d", drawPrefix, i))
		if image == modelContainers[i].Image {
			image = "redis:7"
		}
		modelContainers[i].Image = image
		realContainers[i].Image = image
	}
}

func mutateImmutablePodUpdateFields(rt *rapid.T, modelPod, realPod *corev1.Pod) {
	restartPolicy := corev1.RestartPolicyNever
	if modelPod.Spec.RestartPolicy == corev1.RestartPolicyNever {
		restartPolicy = corev1.RestartPolicyOnFailure
	}
	modelPod.Spec.RestartPolicy = restartPolicy
	realPod.Spec.RestartPolicy = restartPolicy

	dnsPolicy := corev1.DNSDefault
	if modelPod.Spec.DNSPolicy == corev1.DNSDefault {
		dnsPolicy = corev1.DNSClusterFirst
	}
	modelPod.Spec.DNSPolicy = dnsPolicy
	realPod.Spec.DNSPolicy = dnsPolicy

	serviceAccount := rapid.StringMatching(`[a-z][a-z0-9]{2,8}`).Draw(rt, "updatePodServiceAccount")
	if serviceAccount == modelPod.Spec.ServiceAccountName {
		serviceAccount = "otheraccount"
	}
	modelPod.Spec.ServiceAccountName = serviceAccount
	realPod.Spec.ServiceAccountName = serviceAccount

	schedulerName := rapid.StringMatching(`[a-z][a-z0-9-]{2,12}`).Draw(rt, "updatePodSchedulerName")
	if schedulerName == modelPod.Spec.SchedulerName {
		schedulerName = "other-scheduler"
	}
	modelPod.Spec.SchedulerName = schedulerName
	realPod.Spec.SchedulerName = schedulerName

	nodeSelectorKey := rapid.StringMatching(`[a-z][a-z0-9]{0,8}`).Draw(rt, "updatePodNodeSelectorKey")
	nodeSelectorValue := rapid.StringMatching(`[a-z][a-z0-9-]{0,8}`).Draw(rt, "updatePodNodeSelectorValue")
	modelPod.Spec.NodeSelector = map[string]string{nodeSelectorKey: nodeSelectorValue}
	realPod.Spec.NodeSelector = map[string]string{nodeSelectorKey: nodeSelectorValue}

	terminationGracePeriodSeconds := int64(rapid.IntRange(1, 120).Draw(rt, "updatePodTerminationGracePeriod"))
	if modelPod.Spec.TerminationGracePeriodSeconds != nil &&
		terminationGracePeriodSeconds == *modelPod.Spec.TerminationGracePeriodSeconds {
		terminationGracePeriodSeconds++
	}
	modelPod.Spec.TerminationGracePeriodSeconds = &terminationGracePeriodSeconds
	realPod.Spec.TerminationGracePeriodSeconds = &terminationGracePeriodSeconds

	if len(modelPod.Spec.Containers) > 0 && len(realPod.Spec.Containers) > 0 {
		command := []string{
			rapid.SampledFrom([]string{"sleep", "sh", "echo"}).Draw(rt, "updatePodCommand"),
			rapid.SampledFrom([]string{"1", "60", "hello"}).Draw(rt, "updatePodCommandArg"),
		}
		modelPod.Spec.Containers[0].Command = command
		realPod.Spec.Containers[0].Command = command

		envName := rapid.StringMatching(`[A-Z][A-Z0-9_]{1,8}`).Draw(rt, "updatePodEnvName")
		envValue := rapid.StringMatching(`[a-z0-9-]{1,8}`).Draw(rt, "updatePodEnvValue")
		modelPod.Spec.Containers[0].Env = append(modelPod.Spec.Containers[0].Env, corev1.EnvVar{Name: envName, Value: envValue})
		realPod.Spec.Containers[0].Env = append(realPod.Spec.Containers[0].Env, corev1.EnvVar{Name: envName, Value: envValue})
	}

	pullSecretName := rapid.StringMatching(`[a-z][a-z0-9-]{2,10}`).Draw(rt, "updatePodImagePullSecret")
	modelPod.Spec.ImagePullSecrets = append(modelPod.Spec.ImagePullSecrets, corev1.LocalObjectReference{Name: pullSecretName})
	realPod.Spec.ImagePullSecrets = append(realPod.Spec.ImagePullSecrets, corev1.LocalObjectReference{Name: pullSecretName})

	volumeName := rapid.StringMatching(`[a-z][a-z0-9-]{2,10}`).Draw(rt, "updatePodVolumeName")
	volume := corev1.Volume{
		Name: volumeName,
		VolumeSource: corev1.VolumeSource{
			EmptyDir: &corev1.EmptyDirVolumeSource{},
		},
	}
	modelPod.Spec.Volumes = append(modelPod.Spec.Volumes, volume)
	realPod.Spec.Volumes = append(realPod.Spec.Volumes, volume)

	modelPod.Status.Phase = corev1.PodRunning
	realPod.Status.Phase = corev1.PodRunning
}

// ComprehensivePodGen generates pods with many randomized fields.
// This exercises more of the API surface area and defaulting logic.
func ComprehensivePodGen() *rapid.Generator[*corev1.Pod] {
	return rapid.Custom(func(t *rapid.T) *corev1.Pod {
		name := rapid.StringMatching(`[a-z][a-z0-9]{0,10}`).Draw(t, "name")
		containerName := rapid.StringMatching(`[a-z][a-z0-9]{0,10}`).Draw(t, "containerName")
		image := rapid.SampledFrom([]string{
			"nginx:latest",
			"nginx:1.25",
			"busybox:1.36",
			"alpine:3.19",
			"redis:7",
		}).Draw(t, "image")

		// Randomize labels
		labels := map[string]string{}
		if rapid.Bool().Draw(t, "hasLabels") {
			numLabels := rapid.IntRange(1, 3).Draw(t, "numLabels")
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

		// Container with randomized fields
		container := corev1.Container{
			Name:  containerName,
			Image: image,
		}

		// Randomize container resources
		if rapid.Bool().Draw(t, "hasResources") {
			container.Resources = corev1.ResourceRequirements{
				Requests: corev1.ResourceList{
					corev1.ResourceCPU:    resource.MustParse(fmt.Sprintf("%dm", rapid.IntRange(10, 1000).Draw(t, "cpuRequest"))),
					corev1.ResourceMemory: resource.MustParse(fmt.Sprintf("%dMi", rapid.IntRange(16, 512).Draw(t, "memRequest"))),
				},
			}
			if rapid.Bool().Draw(t, "hasLimits") {
				cpuReq := rapid.IntRange(10, 1000).Draw(t, "cpuRequest")
				memReq := rapid.IntRange(16, 512).Draw(t, "memRequest")
				container.Resources.Limits = corev1.ResourceList{
					corev1.ResourceCPU:    resource.MustParse(fmt.Sprintf("%dm", cpuReq*2)),
					corev1.ResourceMemory: resource.MustParse(fmt.Sprintf("%dMi", memReq*2)),
				}
			}
		}

		// Randomize environment variables
		if rapid.Bool().Draw(t, "hasEnv") {
			numEnvVars := rapid.IntRange(1, 3).Draw(t, "numEnvVars")
			container.Env = make([]corev1.EnvVar, numEnvVars)
			for i := 0; i < numEnvVars; i++ {
				container.Env[i] = corev1.EnvVar{
					Name:  rapid.StringMatching(`[A-Z][A-Z0-9_]{0,8}`).Draw(t, fmt.Sprintf("envName%d", i)),
					Value: rapid.StringMatching(`[a-z0-9]{0,10}`).Draw(t, fmt.Sprintf("envVal%d", i)),
				}
			}
		}

		// Build the pod spec
		spec := corev1.PodSpec{
			Containers: []corev1.Container{container},
		}

		// Randomize restart policy
		if rapid.Bool().Draw(t, "hasRestartPolicy") {
			spec.RestartPolicy = rapid.SampledFrom([]corev1.RestartPolicy{
				corev1.RestartPolicyAlways,
				corev1.RestartPolicyOnFailure,
				corev1.RestartPolicyNever,
			}).Draw(t, "restartPolicy")
		}

		// Randomize DNS policy (exclude DNSNone as it requires dnsConfig)
		if rapid.Bool().Draw(t, "hasDNSPolicy") {
			spec.DNSPolicy = rapid.SampledFrom([]corev1.DNSPolicy{
				corev1.DNSClusterFirst,
				corev1.DNSClusterFirstWithHostNet,
				corev1.DNSDefault,
			}).Draw(t, "dnsPolicy")
		}

		// Randomize termination grace period
		if rapid.Bool().Draw(t, "hasTerminationGracePeriod") {
			tgps := int64(rapid.IntRange(0, 60).Draw(t, "terminationGracePeriod"))
			spec.TerminationGracePeriodSeconds = &tgps
		}

		// Randomize node selector
		if rapid.Bool().Draw(t, "hasNodeSelector") {
			spec.NodeSelector = map[string]string{
				"disktype": rapid.SampledFrom([]string{"ssd", "hdd"}).Draw(t, "disktype"),
			}
		}

		// Randomize service account
		if rapid.Bool().Draw(t, "hasServiceAccount") {
			spec.ServiceAccountName = rapid.StringMatching(`[a-z][a-z0-9]{0,8}`).Draw(t, "serviceAccount")
		}

		// Randomize scheduler name (only use default-scheduler as it's the only one that exists in envtest)
		if rapid.Bool().Draw(t, "hasSchedulerName") {
			spec.SchedulerName = "default-scheduler"
		}

		// Note: Priority is not randomized because it requires PriorityClass objects to exist,
		// which are not available in envtest by default.

		pod := &corev1.Pod{
			ObjectMeta: metav1.ObjectMeta{
				Name:        name,
				Namespace:   "default",
				Labels:      labels,
				Annotations: annotations,
			},
			Spec: spec,
		}

		return pod
	})
}

// InvalidPodGen generates known-invalid pods for testing validation.
// These are cases that the model's validation should definitely reject.
func InvalidPodGen() *rapid.Generator[*corev1.Pod] {
	return rapid.Custom(func(t *rapid.T) *corev1.Pod {
		invalidType := rapid.IntRange(0, 3).Draw(t, "invalidType")

		switch invalidType {
		case 0:
			// Missing container name - validation requires name
			return &corev1.Pod{
				ObjectMeta: metav1.ObjectMeta{
					Name:      "test-pod",
					Namespace: "default",
				},
				Spec: corev1.PodSpec{
					Containers: []corev1.Container{{
						Image: "nginx:latest",
					}},
				},
			}
		case 1:
			// Empty containers - validation requires at least one container
			return &corev1.Pod{
				ObjectMeta: metav1.ObjectMeta{
					Name:      "test-pod",
					Namespace: "default",
				},
				Spec: corev1.PodSpec{
					Containers: []corev1.Container{},
				},
			}
		case 2:
			// Empty image - validation requires image
			return &corev1.Pod{
				ObjectMeta: metav1.ObjectMeta{
					Name:      "test-pod",
					Namespace: "default",
				},
				Spec: corev1.PodSpec{
					Containers: []corev1.Container{{
						Name:  "container",
						Image: "",
					}},
				},
			}
		default:
			// Invalid DNS name (uppercase) - validation rejects this
			return &corev1.Pod{
				ObjectMeta: metav1.ObjectMeta{
					Name:      "INVALID-NAME",
					Namespace: "default",
				},
				Spec: corev1.PodSpec{
					Containers: []corev1.Container{{
						Name:  "container",
						Image: "nginx:latest",
					}},
				},
			}
		}
	})
}
