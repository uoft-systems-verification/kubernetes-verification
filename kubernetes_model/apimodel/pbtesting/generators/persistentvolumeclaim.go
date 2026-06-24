package generators

import (
	"fmt"

	corev1 "k8s.io/api/core/v1"
	"k8s.io/apimachinery/pkg/api/resource"
	metav1 "k8s.io/apimachinery/pkg/apis/meta/v1"
	"pgregory.net/rapid"
)

// MinimalPersistentVolumeClaimGen generates minimal valid PersistentVolumeClaims.
func MinimalPersistentVolumeClaimGen() *rapid.Generator[*corev1.PersistentVolumeClaim] {
	return rapid.Custom(func(t *rapid.T) *corev1.PersistentVolumeClaim {
		name := rapid.StringMatching(`[a-z][a-z0-9]{0,10}`).Draw(t, "name")
		return &corev1.PersistentVolumeClaim{
			ObjectMeta: metav1.ObjectMeta{
				Name:      name,
				Namespace: "default",
			},
			Spec: corev1.PersistentVolumeClaimSpec{
				AccessModes: []corev1.PersistentVolumeAccessMode{corev1.ReadWriteOnce},
				Resources: corev1.VolumeResourceRequirements{
					Requests: corev1.ResourceList{
						corev1.ResourceStorage: resource.MustParse("1Gi"),
					},
				},
			},
		}
	})
}

// ComprehensivePersistentVolumeClaimGen generates valid PVCs with a few randomized fields.
func ComprehensivePersistentVolumeClaimGen() *rapid.Generator[*corev1.PersistentVolumeClaim] {
	return rapid.Custom(func(t *rapid.T) *corev1.PersistentVolumeClaim {
		pvc := MinimalPersistentVolumeClaimGen().Draw(t, "minimalPVC")
		sizeGi := rapid.IntRange(1, 16).Draw(t, "storageGi")
		pvc.Spec.Resources.Requests[corev1.ResourceStorage] = resource.MustParse(fmt.Sprintf("%dGi", sizeGi))

		if rapid.Bool().Draw(t, "hasPVCLabels") {
			pvc.Labels = map[string]string{
				"app": rapid.StringMatching(`[a-z][a-z0-9]{0,8}`).Draw(t, "pvcLabel"),
			}
		}

		if rapid.Bool().Draw(t, "hasPVCStorageClass") {
			storageClassName := rapid.StringMatching(`[a-z][a-z0-9-]{0,12}`).Draw(t, "storageClassName")
			pvc.Spec.StorageClassName = &storageClassName
		}

		if rapid.Bool().Draw(t, "hasPVCVolumeMode") {
			mode := rapid.SampledFrom([]corev1.PersistentVolumeMode{
				corev1.PersistentVolumeFilesystem,
				corev1.PersistentVolumeBlock,
			}).Draw(t, "volumeMode")
			pvc.Spec.VolumeMode = &mode
		}

		return pvc
	})
}

// InvalidPersistentVolumeClaimGen generates known-invalid PVCs for testing validation.
func InvalidPersistentVolumeClaimGen() *rapid.Generator[*corev1.PersistentVolumeClaim] {
	return rapid.Custom(func(t *rapid.T) *corev1.PersistentVolumeClaim {
		invalidType := rapid.IntRange(0, 3).Draw(t, "invalidPVCType")
		pvc := MinimalPersistentVolumeClaimGen().Draw(t, "invalidPVCBase")

		switch invalidType {
		case 0:
			pvc.Spec.AccessModes = nil
		case 1:
			pvc.Spec.Resources.Requests = nil
		case 2:
			pvc.Spec.Resources.Requests[corev1.ResourceStorage] = resource.MustParse("-1Gi")
		default:
			pvc.Name = "INVALID_NAME"
		}

		return pvc
	})
}

// ComprehensivePersistentVolumeClaimMut mutates a pair of PVC update inputs in the same way.
func ComprehensivePersistentVolumeClaimMut(rt *rapid.T, modelPVC, realPVC *corev1.PersistentVolumeClaim, exists, valid bool) {
	metadataInvalid := ObjectMetaMut(rt, modelPVC, realPVC, exists, valid)
	if valid || !exists || metadataInvalid {
		return
	}

	accessMode := corev1.ReadOnlyMany
	modelPVC.Spec.AccessModes = []corev1.PersistentVolumeAccessMode{accessMode}
	realPVC.Spec.AccessModes = []corev1.PersistentVolumeAccessMode{accessMode}
}

// ComprehensivePersistentVolumeClaimStatusMut mutates a pair of PVC status update inputs in the same way.
func ComprehensivePersistentVolumeClaimStatusMut(rt *rapid.T, modelPVC, realPVC *corev1.PersistentVolumeClaim, exists, valid bool) {
	metadataInvalid := ObjectMetaMut(rt, modelPVC, realPVC, exists, valid)
	if valid || !exists || metadataInvalid {
		mutateAllowedPersistentVolumeClaimStatusFields(rt, modelPVC, realPVC)
		return
	}

	modelPVC.Status.Capacity = corev1.ResourceList{
		corev1.ResourceStorage: resource.MustParse("-1Gi"),
	}
	realPVC.Status.Capacity = corev1.ResourceList{
		corev1.ResourceStorage: resource.MustParse("-1Gi"),
	}
}

func mutateAllowedPersistentVolumeClaimStatusFields(rt *rapid.T, modelPVC, realPVC *corev1.PersistentVolumeClaim) {
	sizeGi := rapid.IntRange(1, 16).Draw(rt, "pvcStatusStorageGi")
	capacity := corev1.ResourceList{
		corev1.ResourceStorage: resource.MustParse(fmt.Sprintf("%dGi", sizeGi)),
	}
	phase := rapid.SampledFrom([]corev1.PersistentVolumeClaimPhase{
		corev1.ClaimPending,
		corev1.ClaimBound,
		corev1.ClaimLost,
	}).Draw(rt, "pvcStatusPhase")

	modelPVC.Status.Capacity = capacity
	modelPVC.Status.Phase = phase
	realPVC.Status.Capacity = capacity
	realPVC.Status.Phase = phase
}
