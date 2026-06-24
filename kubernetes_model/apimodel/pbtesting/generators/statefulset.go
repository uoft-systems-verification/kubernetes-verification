package generators

import (
	appsv1 "k8s.io/api/apps/v1"
	corev1 "k8s.io/api/core/v1"
	"k8s.io/apimachinery/pkg/api/resource"
	metav1 "k8s.io/apimachinery/pkg/apis/meta/v1"
	"pgregory.net/rapid"
)

// MinimalStatefulSetGen generates minimal valid StatefulSets.
func MinimalStatefulSetGen() *rapid.Generator[*appsv1.StatefulSet] {
	return rapid.Custom(func(t *rapid.T) *appsv1.StatefulSet {
		name := rapid.StringMatching(`[a-z][a-z0-9]{0,10}`).Draw(t, "name")
		appLabel := rapid.StringMatching(`[a-z][a-z0-9]{0,10}`).Draw(t, "appLabel")
		containerName := rapid.StringMatching(`[a-z][a-z0-9]{0,10}`).Draw(t, "containerName")
		replicas := int32(rapid.IntRange(0, 5).Draw(t, "replicas"))
		labels := map[string]string{"app": appLabel}

		return &appsv1.StatefulSet{
			ObjectMeta: metav1.ObjectMeta{
				Name:      name,
				Namespace: "default",
			},
			Spec: appsv1.StatefulSetSpec{
				Replicas: &replicas,
				Selector: &metav1.LabelSelector{
					MatchLabels: labels,
				},
				Template: corev1.PodTemplateSpec{
					ObjectMeta: metav1.ObjectMeta{
						Labels: labels,
					},
					Spec: corev1.PodSpec{
						RestartPolicy: corev1.RestartPolicyAlways,
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

// ComprehensiveStatefulSetGen generates valid StatefulSets with a few randomized fields.
func ComprehensiveStatefulSetGen() *rapid.Generator[*appsv1.StatefulSet] {
	return rapid.Custom(func(t *rapid.T) *appsv1.StatefulSet {
		sts := MinimalStatefulSetGen().Draw(t, "minimalStatefulSet")

		if rapid.Bool().Draw(t, "hasSTSServiceName") {
			sts.Spec.ServiceName = rapid.StringMatching(`[a-z][a-z0-9-]{0,12}`).Draw(t, "stsServiceName")
		}

		if rapid.Bool().Draw(t, "hasSTSMinReadySeconds") {
			sts.Spec.MinReadySeconds = int32(rapid.IntRange(0, 30).Draw(t, "stsMinReadySeconds"))
		}

		if rapid.Bool().Draw(t, "hasSTSVolumeClaimTemplate") {
			claimName := rapid.StringMatching(`[a-z][a-z0-9]{0,8}`).Draw(t, "stsClaimName")
			sts.Spec.Template.Spec.Containers[0].VolumeMounts = []corev1.VolumeMount{{
				Name:      claimName,
				MountPath: "/data",
			}}
			sts.Spec.VolumeClaimTemplates = []corev1.PersistentVolumeClaim{{
				ObjectMeta: metav1.ObjectMeta{
					Name: claimName,
				},
				Spec: corev1.PersistentVolumeClaimSpec{
					AccessModes: []corev1.PersistentVolumeAccessMode{corev1.ReadWriteOnce},
					Resources: corev1.VolumeResourceRequirements{
						Requests: corev1.ResourceList{
							corev1.ResourceStorage: resource.MustParse("1Gi"),
						},
					},
				},
			}}
		}

		return sts
	})
}

// InvalidStatefulSetGen generates known-invalid StatefulSets for testing validation.
func InvalidStatefulSetGen() *rapid.Generator[*appsv1.StatefulSet] {
	return rapid.Custom(func(t *rapid.T) *appsv1.StatefulSet {
		invalidType := rapid.IntRange(0, 3).Draw(t, "invalidStatefulSetType")
		sts := MinimalStatefulSetGen().Draw(t, "invalidStatefulSetBase")

		switch invalidType {
		case 0:
			sts.Spec.Selector = nil
		case 1:
			selectorValue := "other"
			if sts.Spec.Template.Labels["app"] == selectorValue {
				selectorValue = "other2"
			}
			sts.Spec.Selector = &metav1.LabelSelector{MatchLabels: map[string]string{"app": selectorValue}}
		case 2:
			sts.Spec.Replicas = int32Ptr(-1)
		default:
			sts.Name = "INVALID_NAME"
		}

		return sts
	})
}

// ComprehensiveStatefulSetMut mutates a pair of StatefulSet update inputs in the same way.
func ComprehensiveStatefulSetMut(rt *rapid.T, modelSTS, realSTS *appsv1.StatefulSet, exists, valid bool) {
	metadataInvalid := ObjectMetaMut(rt, modelSTS, realSTS, exists, valid)

	if valid {
		mutateAllowedStatefulSetUpdateFields(rt, modelSTS, realSTS)
		return
	}

	if !exists || metadataInvalid {
		mutateAllowedStatefulSetUpdateFields(rt, modelSTS, realSTS)
		return
	}

	mutateAllowedStatefulSetUpdateFields(rt, modelSTS, realSTS)
	modelSTS.Spec.ServiceName = "changed-service"
	realSTS.Spec.ServiceName = "changed-service"
}

// ComprehensiveStatefulSetStatusMut mutates a pair of StatefulSet status update inputs in the same way.
func ComprehensiveStatefulSetStatusMut(rt *rapid.T, modelSTS, realSTS *appsv1.StatefulSet, exists, valid bool) {
	metadataInvalid := ObjectMetaMut(rt, modelSTS, realSTS, exists, valid)

	if valid || !exists || metadataInvalid {
		mutateAllowedStatefulSetStatusFields(rt, modelSTS, realSTS)
		return
	}

	modelSTS.Status.Replicas = 1
	modelSTS.Status.ReadyReplicas = 2
	realSTS.Status.Replicas = 1
	realSTS.Status.ReadyReplicas = 2
}

func mutateAllowedStatefulSetUpdateFields(rt *rapid.T, modelSTS, realSTS *appsv1.StatefulSet) {
	replicas := int32(rapid.IntRange(0, 5).Draw(rt, "updateSTSReplicas"))
	modelSTS.Spec.Replicas = &replicas
	realSTS.Spec.Replicas = &replicas

	if len(modelSTS.Spec.Template.Spec.Containers) > 0 && len(realSTS.Spec.Template.Spec.Containers) > 0 {
		image := rapid.SampledFrom([]string{
			"nginx:1.25",
			"nginx:1.27",
			"busybox:1.36",
			"alpine:3.19",
		}).Draw(rt, "updateSTSImage")
		modelSTS.Spec.Template.Spec.Containers[0].Image = image
		realSTS.Spec.Template.Spec.Containers[0].Image = image
	}

	if rapid.Bool().Draw(rt, "updateSTSMinReadySeconds") {
		minReadySeconds := int32(rapid.IntRange(0, 30).Draw(rt, "updateSTSMinReadySecondsValue"))
		modelSTS.Spec.MinReadySeconds = minReadySeconds
		realSTS.Spec.MinReadySeconds = minReadySeconds
	}
}

func mutateAllowedStatefulSetStatusFields(rt *rapid.T, modelSTS, realSTS *appsv1.StatefulSet) {
	replicas := int32(rapid.IntRange(0, 5).Draw(rt, "updateSTSStatusReplicas"))
	readyReplicas := int32(rapid.IntRange(0, int(replicas)).Draw(rt, "updateSTSStatusReadyReplicas"))
	currentReplicas := int32(rapid.IntRange(0, int(replicas)).Draw(rt, "updateSTSStatusCurrentReplicas"))
	updatedReplicas := int32(rapid.IntRange(0, int(replicas)).Draw(rt, "updateSTSStatusUpdatedReplicas"))
	availableReplicas := int32(rapid.IntRange(0, int(readyReplicas)).Draw(rt, "updateSTSStatusAvailableReplicas"))
	observedGeneration := int64(rapid.IntRange(0, 10).Draw(rt, "updateSTSStatusObservedGeneration"))

	modelSTS.Status.Replicas = replicas
	modelSTS.Status.ReadyReplicas = readyReplicas
	modelSTS.Status.CurrentReplicas = currentReplicas
	modelSTS.Status.UpdatedReplicas = updatedReplicas
	modelSTS.Status.AvailableReplicas = availableReplicas
	modelSTS.Status.ObservedGeneration = observedGeneration
	realSTS.Status.Replicas = replicas
	realSTS.Status.ReadyReplicas = readyReplicas
	realSTS.Status.CurrentReplicas = currentReplicas
	realSTS.Status.UpdatedReplicas = updatedReplicas
	realSTS.Status.AvailableReplicas = availableReplicas
	realSTS.Status.ObservedGeneration = observedGeneration

	if rapid.Bool().Draw(rt, "updateSTSCollisionCount") {
		collisionCount := int32(rapid.IntRange(0, 5).Draw(rt, "updateSTSCollisionCountValue"))
		modelSTS.Status.CollisionCount = &collisionCount
		realSTS.Status.CollisionCount = &collisionCount
	}
}
