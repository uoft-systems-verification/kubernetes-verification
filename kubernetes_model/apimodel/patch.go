package apimodel

import (
	"encoding/json"
	"fmt"
	"net/http"

	jsonpatch "gopkg.in/evanphx/json-patch.v4"
	appsv1 "k8s.io/api/apps/v1"
	corev1 "k8s.io/api/core/v1"
	rbacv1 "k8s.io/api/rbac/v1"
	apierrors "k8s.io/apimachinery/pkg/api/errors"
	"k8s.io/apimachinery/pkg/api/meta"
	"k8s.io/apimachinery/pkg/runtime"
	"k8s.io/apimachinery/pkg/runtime/schema"
	"k8s.io/apimachinery/pkg/types"
	"k8s.io/apimachinery/pkg/util/mergepatch"
	"k8s.io/apimachinery/pkg/util/strategicpatch"
	"k8s.io/apimachinery/pkg/util/validation/field"
	"k8s.io/kubernetes/pkg/api/legacyscheme"
)

// patch models non-apply PATCH requests with default PatchOptions. Application
// and validation are atomic with respect to other model operations. The result
// follows the ordinary or status update strategy, including defaulting, UID/RV
// preconditions, generation changes, and deletion after finalizer removal.
// Reference: staging/src/k8s.io/apiserver/pkg/endpoints/handlers/patch.go.
func (s *State) patch(kind, namespace, name string, patchType types.PatchType, data []byte, subresources ...string) (interface{}, error) {
	s.mu.Lock()
	defer s.mu.Unlock()
	if patchType != types.JSONPatchType && patchType != types.MergePatchType && patchType != types.StrategicMergePatchType {
		return nil, apierrors.NewGenericServerResponse(http.StatusUnsupportedMediaType, "PATCH", schema.GroupResource{Resource: kind}, name, "unsupported patch type", 0, false)
	}
	status := len(subresources) == 1 && subresources[0] == "status"
	if len(subresources) > 0 && !status {
		return nil, apierrors.NewNotFound(schema.GroupResource{Resource: kind}, name)
	}
	existing, ok := s.m[KKey{Kind: kind, Namespace: namespace, Name: name}]
	if !ok {
		return nil, apierrors.NewNotFound(schema.GroupResource{Resource: kind}, name)
	}
	// Upstream installs /status as a separate storage endpoint. In the model,
	// the status strategy registry determines whether that endpoint exists.
	if status {
		legacy, err := convertVersionedToLegacy(existing)
		if err != nil {
			return nil, err
		}
		if _, err := statusUpdateStrategyForLegacyObject(legacy); err != nil {
			return nil, apierrors.NewNotFound(schema.GroupResource{Resource: kind}, name)
		}
	}
	obj, err := applyPatchToObject(existing.(runtime.Object), patchType, data, name)
	if err != nil {
		return nil, err
	}
	metadata, err := meta.Accessor(obj)
	if err != nil {
		return nil, err
	}
	if metadata.GetName() != name {
		return nil, apierrors.NewBadRequest(fmt.Sprintf("the name of the object (%s) does not match the name on the URL (%s)", metadata.GetName(), name))
	}

	if status {
		return s.updateStatusLocked(kind, namespace, obj, false)
	}
	return s.updateLocked(kind, namespace, obj, false)
}

// applyPatchToObject handles the versioned wire representation and decoding.
// The caller validates patchType and holds the state lock through persistence.
func applyPatchToObject(existing runtime.Object, patchType types.PatchType, data []byte, name string) (runtime.Object, error) {
	// The API server patches the versioned wire representation, which includes
	// kind and apiVersion even though stored/client objects may omit TypeMeta.
	gvks, _, err := legacyscheme.Scheme.ObjectKinds(existing)
	if err != nil {
		return nil, err
	}
	// Stored objects use concrete external types, each registered at one GVK.
	// Fail explicitly rather than guessing if a future type has several versions.
	if len(gvks) != 1 {
		return nil, fmt.Errorf("expected one registered GVK for %T, got %v", existing, gvks)
	}
	codec := legacyscheme.Codecs.LegacyCodec(gvks[0].GroupVersion())
	original, err := runtime.Encode(codec, existing)
	if err != nil {
		return nil, err
	}
	var patched []byte
	switch patchType {
	case types.JSONPatchType:
		patch, decodeErr := jsonpatch.DecodePatch(data)
		if decodeErr != nil {
			return nil, apierrors.NewBadRequest(decodeErr.Error())
		}
		if len(patch) > 10000 {
			return nil, apierrors.NewRequestEntityTooLargeError("too many JSON patch operations")
		}
		patched, err = patch.Apply(original)
		if err != nil {
			return nil, apierrors.NewGenericServerResponse(http.StatusUnprocessableEntity, "", schema.GroupResource{}, "", err.Error(), 0, false)
		}
	case types.MergePatchType:
		patched, err = jsonpatch.MergePatch(original, data)
	case types.StrategicMergePatchType:
		patched, err = strategicpatch.StrategicMergePatch(original, data, existing)
	}
	if err != nil {
		if err == mergepatch.ErrNoListOfLists || err == mergepatch.ErrPatchContentNotMatchRetainKeys {
			return nil, apierrors.NewGenericServerResponse(http.StatusUnprocessableEntity, "", schema.GroupResource{}, "", err.Error(), 0, false)
		}
		return nil, apierrors.NewBadRequest(err.Error())
	}
	obj, err := legacyscheme.Scheme.New(gvks[0])
	if err != nil {
		return nil, err
	}
	// Strategic merge is unmarshaled into the known schema directly; JSON
	// and merge patches go through the API version decoder instead.
	if patchType == types.StrategicMergePatchType {
		err = json.Unmarshal(patched, obj)
	} else {
		err = runtime.DecodeInto(codec, patched, obj)
	}
	if err != nil {
		return nil, apierrors.NewInvalid(schema.GroupKind{}, name, field.ErrorList{field.Invalid(field.NewPath("patch"), string(patched), err.Error())})
	}
	// TypeMeta describes the wire format, not the persisted object.
	obj.GetObjectKind().SetGroupVersionKind(existing.GetObjectKind().GroupVersionKind())
	return obj, nil
}

// PodPatch applies a patch to the named object, optionally to its status subresource.
func (s *State) PodPatch(namespace, name string, patchType types.PatchType, data []byte, subresources ...string) (*corev1.Pod, error) {
	obj, err := s.patch("Pod", namespace, name, patchType, data, subresources...)
	if err != nil {
		return nil, err
	}
	return obj.(*corev1.Pod), nil
}

// PersistentVolumeClaimPatch applies a patch to the named object, optionally to its status subresource.
func (s *State) PersistentVolumeClaimPatch(namespace, name string, patchType types.PatchType, data []byte, subresources ...string) (*corev1.PersistentVolumeClaim, error) {
	obj, err := s.patch("PersistentVolumeClaim", namespace, name, patchType, data, subresources...)
	if err != nil {
		return nil, err
	}
	return obj.(*corev1.PersistentVolumeClaim), nil
}

// ReplicaSetPatch applies a patch to the named object, optionally to its status subresource.
func (s *State) ReplicaSetPatch(namespace, name string, patchType types.PatchType, data []byte, subresources ...string) (*appsv1.ReplicaSet, error) {
	obj, err := s.patch("ReplicaSet", namespace, name, patchType, data, subresources...)
	if err != nil {
		return nil, err
	}
	return obj.(*appsv1.ReplicaSet), nil
}

// StatefulSetPatch applies a patch to the named object, optionally to its status subresource.
func (s *State) StatefulSetPatch(namespace, name string, patchType types.PatchType, data []byte, subresources ...string) (*appsv1.StatefulSet, error) {
	obj, err := s.patch("StatefulSet", namespace, name, patchType, data, subresources...)
	if err != nil {
		return nil, err
	}
	return obj.(*appsv1.StatefulSet), nil
}

// DeploymentPatch applies a patch to the named object, optionally to its status subresource.
func (s *State) DeploymentPatch(namespace, name string, patchType types.PatchType, data []byte, subresources ...string) (*appsv1.Deployment, error) {
	obj, err := s.patch("Deployment", namespace, name, patchType, data, subresources...)
	if err != nil {
		return nil, err
	}
	return obj.(*appsv1.Deployment), nil
}

// ServiceAccountPatch applies a patch to the named object, optionally to its status subresource.
func (s *State) ServiceAccountPatch(namespace, name string, patchType types.PatchType, data []byte, subresources ...string) (*corev1.ServiceAccount, error) {
	obj, err := s.patch("ServiceAccount", namespace, name, patchType, data, subresources...)
	if err != nil {
		return nil, err
	}
	return obj.(*corev1.ServiceAccount), nil
}

// ClusterRolePatch applies a patch to the named object, optionally to its status subresource.
func (s *State) ClusterRolePatch(name string, patchType types.PatchType, data []byte, subresources ...string) (*rbacv1.ClusterRole, error) {
	obj, err := s.patch("ClusterRole", "", name, patchType, data, subresources...)
	if err != nil {
		return nil, err
	}
	return obj.(*rbacv1.ClusterRole), nil
}

// ControllerRevisionPatch applies a patch; status subresource requests are rejected.
func (s *State) ControllerRevisionPatch(namespace, name string, patchType types.PatchType, data []byte, subresources ...string) (*appsv1.ControllerRevision, error) {
	obj, err := s.patch("ControllerRevision", namespace, name, patchType, data, subresources...)
	if err != nil {
		return nil, err
	}
	return obj.(*appsv1.ControllerRevision), nil
}
