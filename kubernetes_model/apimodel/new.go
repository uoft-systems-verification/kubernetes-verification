package apimodel

import (
	"context"
	"fmt"
	"math/rand"
	"strconv"
	"time"

	appsv1 "k8s.io/api/apps/v1"
	corev1 "k8s.io/api/core/v1"
	v1 "k8s.io/api/core/v1"
	"k8s.io/apimachinery/pkg/api/errors"
	"k8s.io/apimachinery/pkg/api/meta"
	apivalidation "k8s.io/apimachinery/pkg/api/validation"
	metav1 "k8s.io/apimachinery/pkg/apis/meta/v1"
	"k8s.io/apimachinery/pkg/runtime"
	"k8s.io/apimachinery/pkg/runtime/schema"
	"k8s.io/apimachinery/pkg/types"
	"k8s.io/apimachinery/pkg/util/uuid"
	"k8s.io/apimachinery/pkg/util/validation/field"
	genericapirequest "k8s.io/apiserver/pkg/endpoints/request"
	genericregistry "k8s.io/apiserver/pkg/registry/generic/registry"
	"k8s.io/apiserver/pkg/registry/rest"
	"k8s.io/kubernetes/pkg/api/legacyscheme"
	"k8s.io/kubernetes/pkg/apis/apps"
	appsv1defaults "k8s.io/kubernetes/pkg/apis/apps/v1"
	"k8s.io/kubernetes/pkg/apis/core"
	corev1defaults "k8s.io/kubernetes/pkg/apis/core/v1"
	rsstrategy "k8s.io/kubernetes/pkg/registry/apps/replicaset"
	podstrategy "k8s.io/kubernetes/pkg/registry/core/pod"

	// This blank import runs init() which registers conversion functions between
	// external types (appsv1.ReplicaSet) and internal types (apps.ReplicaSet) in legacyscheme.
	// Without this, legacyscheme.Scheme.Convert() fails with "unknown conversion" for ReplicaSets.
	_ "k8s.io/kubernetes/pkg/apis/apps/install"
)

func (s *State) get(key KKey) (interface{}, error) {
	s.mu.Lock()
	defer s.mu.Unlock()

	item, exists := s.m[key]
	if exists {
		return deepCopy(item), nil
	} else {
		return nil, errors.NewNotFound(schema.GroupResource{Resource: key.Kind}, key.Name)
	}
}

func randomSuffix(n int) string {
	nameRand := rand.New(rand.NewSource(time.Now().UnixNano()))
	randomSuffixChars := []byte("bcdfghjklmnpqrstvwxz2456789")
	b := make([]byte, n)
	for i := range b {
		b[i] = randomSuffixChars[nameRand.Intn(len(randomSuffixChars))]
	}
	return string(b)
}

func (s *State) generateNewName(kind, namespace, generateName string) string {
	for {
		name := generateName + randomSuffix(5)
		key := KKey{
			Kind:      kind,
			Name:      name,
			Namespace: namespace,
		}
		if _, exists := s.m[key]; !exists {
			return name
		}
	}
}

func (s *State) generateNewUIDAndUpdate() types.UID {
	for {
		uid := uuid.NewUUID()
		if _, exists := s.usedUID[uid]; !exists {
			s.usedUID[uid] = struct{}{}
			return uid
		}
	}
}

func (s *State) generateNewRVAndUpdate() string {
	for {
		rv := strconv.FormatInt(rand.Int63(), 10)
		if _, exists := s.usedRV[rv]; !exists {
			s.usedRV[rv] = struct{}{}
			return rv
		}
	}
}

// validateObjectMeta validates the ObjectMeta fields using generic Kubernetes validation.
// This matches the API server's generic metadata validation that happens in BeforeCreate.
func validateObjectMeta(metadata metav1.Object, kind string) error {
	// For now, we assume all resources are namespaced (Pod, ReplicaSet, etc.)
	// Cluster-scoped resources like Node, Namespace would set requiresNamespace = false
	requiresNamespace := true

	// Validate using the generic Kubernetes metadata validator
	// This validates: Name, Namespace, Labels, Annotations, OwnerReferences, Finalizers, etc.
	if errs := apivalidation.ValidateObjectMetaAccessor(
		metadata,
		requiresNamespace,
		apivalidation.NameIsDNSSubdomain, // Name must be a valid DNS subdomain
		field.NewPath("metadata"),
	); len(errs) > 0 {
		return errors.NewInvalid(
			schema.GroupKind{Kind: kind},
			metadata.GetName(),
			errs,
		)
	}

	return nil
}

// applyDefaultTolerationSeconds implements the DefaultTolerationSeconds admission controller.
// It adds default tolerations for node.kubernetes.io/not-ready:NoExecute and
// node.kubernetes.io/unreachable:NoExecute with 300s toleration seconds.
// Reference: https://github.com/kubernetes/kubernetes/blob/release-1.34/plugin/pkg/admission/defaulttolerationseconds/admission.go
func applyDefaultTolerationSeconds(pod *core.Pod) {
	defaultNotReadyTolerationSeconds := int64(300)
	defaultUnreachableTolerationSeconds := int64(300)

	tolerations := pod.Spec.Tolerations

	// Check if pod already tolerates node.kubernetes.io/not-ready:NoExecute
	toleratesNodeNotReady := false
	for _, toleration := range tolerations {
		// Matches if key is "node.kubernetes.io/not-ready" (or empty, meaning all keys)
		// AND effect is NoExecute (or empty, meaning all effects)
		if (toleration.Key == v1.TaintNodeNotReady || len(toleration.Key) == 0) &&
			(toleration.Effect == core.TaintEffectNoExecute || len(toleration.Effect) == 0) {
			toleratesNodeNotReady = true
			break
		}
	}

	// Check if pod already tolerates node.kubernetes.io/unreachable:NoExecute
	toleratesNodeUnreachable := false
	for _, toleration := range tolerations {
		if (toleration.Key == v1.TaintNodeUnreachable || len(toleration.Key) == 0) &&
			(toleration.Effect == core.TaintEffectNoExecute || len(toleration.Effect) == 0) {
			toleratesNodeUnreachable = true
			break
		}
	}

	// Add default tolerations if not already present
	if !toleratesNodeNotReady {
		pod.Spec.Tolerations = append(pod.Spec.Tolerations, core.Toleration{
			Key:               v1.TaintNodeNotReady,
			Operator:          core.TolerationOpExists,
			Effect:            core.TaintEffectNoExecute,
			TolerationSeconds: &defaultNotReadyTolerationSeconds,
		})
	}

	if !toleratesNodeUnreachable {
		pod.Spec.Tolerations = append(pod.Spec.Tolerations, core.Toleration{
			Key:               v1.TaintNodeUnreachable,
			Operator:          core.TolerationOpExists,
			Effect:            core.TaintEffectNoExecute,
			TolerationSeconds: &defaultUnreachableTolerationSeconds,
		})
	}
}

// applyPriorityAdmission implements the Priority admission controller.
// It sets pod.Spec.Priority and pod.Spec.PreemptionPolicy based on PriorityClassName.
// Since this model doesn't store PriorityClass objects, we use a simplified implementation:
// - If no PriorityClassName is specified, use default priority 0 with PreemptLowerPriority policy
// - If PriorityClassName is specified, we cannot look it up (not implemented), so we skip
// Reference: https://github.com/kubernetes/kubernetes/blob/release-1.34/plugin/pkg/admission/priority/admission.go
func applyPriorityAdmission(pod *core.Pod) {
	// Only set priority if not already set by user and no PriorityClassName specified
	// This matches the real behavior when no default PriorityClass exists
	if pod.Spec.Priority == nil && len(pod.Spec.PriorityClassName) == 0 {
		// Default priority when no PriorityClass exists is 0
		// Reference: pkg/apis/scheduling/types.go: DefaultPriorityWhenNoDefaultClassExists = 0
		defaultPriority := int32(0)
		pod.Spec.Priority = &defaultPriority

		// Default preemption policy is PreemptLowerPriority
		defaultPreemptionPolicy := core.PreemptLowerPriority
		pod.Spec.PreemptionPolicy = &defaultPreemptionPolicy
	}

	// Note: If PriorityClassName is specified, the real admission controller would look up
	// the PriorityClass object and set Priority/PreemptionPolicy from it. We skip this
	// because the model doesn't implement PriorityClass storage yet.
}

// convertVersionedToLegacy converts supported external/versioned API objects
// to their internal Kubernetes representations.
func convertVersionedToLegacy(obj interface{}) (interface{}, error) {
	switch typed := obj.(type) {
	case *corev1.Pod:
		internalPod := &core.Pod{}
		if err := legacyscheme.Scheme.Convert(typed, internalPod, nil); err != nil {
			return nil, errors.NewBadRequest(fmt.Sprintf("failed to convert v1.Pod to internal Pod: %v", err))
		}
		return internalPod, nil
	case *appsv1.ReplicaSet:
		internalRS := &apps.ReplicaSet{}
		if err := legacyscheme.Scheme.Convert(typed, internalRS, nil); err != nil {
			return nil, errors.NewBadRequest(fmt.Sprintf("failed to convert appsv1.ReplicaSet to internal ReplicaSet: %v", err))
		}
		return internalRS, nil
	default:
		return nil, fmt.Errorf("unsupported versioned object type for conversion: %T", obj)
	}
}

// applySchemaDefaults applies schema-based defaults to the object.
// This matches the API server's defaulting behavior that happens during decoding.
// These defaults are applied BEFORE PrepareForCreate and validation.
func applySchemaDefaults(obj interface{}) error {
	switch typed := obj.(type) {
	case *corev1.Pod:
		// SetObjectDefaults_Pod recursively applies all defaults:
		// - PodSpec defaults (DNSPolicy, RestartPolicy, TerminationGracePeriodSeconds, etc.)
		// - Container defaults (ImagePullPolicy, TerminationMessagePolicy, etc.)
		// - Volume defaults, Probe defaults, etc.
		corev1defaults.SetObjectDefaults_Pod(typed)
	case *appsv1.ReplicaSet:
		// SetObjectDefaults_ReplicaSet recursively applies all defaults:
		// - ReplicaSet.Spec.Replicas defaults to 1
		// - Pod template defaults (same as Pod)
		appsv1defaults.SetObjectDefaults_ReplicaSet(typed)
	default:
		return fmt.Errorf("unsupported object type for schema defaults: %T", obj)
	}
	return nil
}

func applyStrategyPrepareForCreate(obj interface{}) error {
	ctx := context.Background()
	switch typed := obj.(type) {
	case *core.Pod:
		podstrategy.Strategy.PrepareForCreate(ctx, typed)
	case *apps.ReplicaSet:
		rsstrategy.Strategy.PrepareForCreate(ctx, typed)
	default:
		return fmt.Errorf("unsupported object type for strategy and validation: %T", obj)
	}
	return nil
}

func applyAdmissionMutate(obj interface{}) error {
	switch typed := obj.(type) {
	case *core.Pod:
		// Apply admission controller mutations (these run after PrepareForCreate in real k8s)
		// Note: ServiceAccount admission controller is NOT enabled in envtest, so we don't apply it here.
		// A full Kubernetes cluster would set ServiceAccountName="default" if empty, but envtest doesn't.
		applyDefaultTolerationSeconds(typed)
		applyPriorityAdmission(typed)
	case *apps.ReplicaSet:
		return nil
	default:
		return fmt.Errorf("unsupported object type for strategy and validation: %T", obj)
	}
	return nil
}

// applyAdmissionMutateForUpdate mirrors the mutating admission plugins that affect the
// normal Pod/ReplicaSet update path.
// References:
// - https://github.com/kubernetes/kubernetes/blob/release-1.34/staging/src/k8s.io/apiserver/pkg/endpoints/handlers/update.go#L169-L189
// - https://github.com/kubernetes/kubernetes/blob/release-1.34/plugin/pkg/admission/defaulttolerationseconds/admission.go#L107-L145
// - https://github.com/kubernetes/kubernetes/blob/release-1.34/plugin/pkg/admission/priority/admission.go#L136-L158
func applyAdmissionMutateForUpdate(obj, oldObj interface{}) error {
	switch typed := obj.(type) {
	case *core.Pod:
		oldPod, ok := oldObj.(*core.Pod)
		if !ok {
			return fmt.Errorf("expected *core.Pod for old object, got %T", oldObj)
		}

		applyDefaultTolerationSeconds(typed)

		// Priority admission preserves the stored values on update when the client omits them.
		if typed.Spec.Priority == nil && oldPod.Spec.Priority != nil {
			priority := *oldPod.Spec.Priority
			typed.Spec.Priority = &priority
		}
		if typed.Spec.PreemptionPolicy == nil && oldPod.Spec.PreemptionPolicy != nil {
			policy := *oldPod.Spec.PreemptionPolicy
			typed.Spec.PreemptionPolicy = &policy
		}
	case *apps.ReplicaSet:
		return nil
	default:
		return fmt.Errorf("unsupported object type for update admission mutation: %T", obj)
	}
	return nil
}

func applyAdmissionValidate(obj interface{}) error {
	switch obj.(type) {
	case *core.Pod:
		// The built-in admission plugins this model currently mirrors for Pod create/update are:
		// - DefaultTolerationSeconds: mutation only, no Validate method
		// - Priority: its Validate method applies to PriorityClass objects, not Pods
		// So there is no additional Pod admission validation to run here.
		return nil
	case *apps.ReplicaSet:
		// This model does not mirror any ReplicaSet-specific validating admission plugins.
		return nil
	default:
		return fmt.Errorf("unsupported object type for admission validation: %T", obj)
	}
}

func allowUnconditionalUpdate(kind string) (bool, error) {
	switch kind {
	case "Pod", "ReplicaSet":
		// Both Pod and ReplicaSet strategies return true from AllowUnconditionalUpdate() in release-1.34.
		// References:
		// - https://github.com/kubernetes/kubernetes/blob/release-1.34/pkg/registry/core/pod/strategy.go#L157-L159
		// - https://github.com/kubernetes/kubernetes/blob/release-1.34/pkg/registry/apps/replicaset/strategy.go#L159-L160
		return true, nil
	default:
		return false, fmt.Errorf("unsupported kind for update: %s", kind)
	}
}

func malformedUpdateResourceVersionError(err error) error {
	return &errors.StatusError{ErrStatus: metav1.Status{
		Status:  metav1.StatusFailure,
		Code:    500,
		Message: err.Error(),
	}}
}

func updateStrategyForLegacyObject(obj interface{}) (rest.RESTUpdateStrategy, error) {
	switch obj.(type) {
	case *core.Pod:
		return podstrategy.Strategy, nil
	case *apps.ReplicaSet:
		return rsstrategy.Strategy, nil
	default:
		return nil, fmt.Errorf("unsupported object type for update strategy: %T", obj)
	}
}

func applyStrategyValidate(obj interface{}, name string) error {
	ctx := context.Background()
	switch typed := obj.(type) {
	case *core.Pod:
		if errs := podstrategy.Strategy.Validate(ctx, typed); len(errs) > 0 {
			return errors.NewInvalid(schema.GroupKind{Group: "", Kind: "Pod"}, name, errs)
		}
	case *apps.ReplicaSet:
		if errs := rsstrategy.Strategy.Validate(ctx, typed); len(errs) > 0 {
			return errors.NewInvalid(schema.GroupKind{Group: "apps", Kind: "ReplicaSet"}, name, errs)
		}
	default:
		return fmt.Errorf("unsupported object type for strategy and validation: %T", obj)
	}
	return nil
}

func applyStrategyCanonicalize(obj interface{}) error {
	switch typed := obj.(type) {
	case *core.Pod:
		podstrategy.Strategy.Canonicalize(typed)
	case *apps.ReplicaSet:
		rsstrategy.Strategy.Canonicalize(typed)
	default:
		return fmt.Errorf("unsupported object type for strategy and validation: %T", obj)
	}
	return nil
}

// applyValidationAndDefaultingOnUpdate models the decode/defaulting/admission/storage
// pipeline for a regular Kubernetes update, but intentionally skips UpdateOptions.
// References:
// - https://github.com/kubernetes/kubernetes/blob/release-1.34/staging/src/k8s.io/apiserver/pkg/endpoints/handlers/update.go#L113-L220
// - https://github.com/kubernetes/kubernetes/blob/release-1.34/staging/src/k8s.io/apiserver/pkg/registry/rest/update.go#L107-L165
// - https://github.com/kubernetes/kubernetes/blob/release-1.34/staging/src/k8s.io/apiserver/pkg/registry/generic/registry/store.go#L753-L770
func applyValidationAndDefaultingOnUpdate(newObj, oldObj interface{}, namespace string) error {
	// Decoder defaulting happens before mutating admission and BeforeUpdate in the real API.
	if err := applySchemaDefaults(newObj); err != nil {
		return err
	}

	legacyNewObj, err := convertVersionedToLegacy(newObj)
	if err != nil {
		return err
	}
	legacyOldObj, err := convertVersionedToLegacy(oldObj)
	if err != nil {
		return err
	}

	if err := applyAdmissionMutateForUpdate(legacyNewObj, legacyOldObj); err != nil {
		return err
	}

	newRuntimeObj, ok := legacyNewObj.(runtime.Object)
	if !ok {
		return fmt.Errorf("updated object does not implement runtime.Object: %T", legacyNewObj)
	}
	oldRuntimeObj, ok := legacyOldObj.(runtime.Object)
	if !ok {
		return fmt.Errorf("existing object does not implement runtime.Object: %T", legacyOldObj)
	}

	strategy, err := updateStrategyForLegacyObject(legacyNewObj)
	if err != nil {
		return err
	}

	ctx := genericapirequest.WithNamespace(genericapirequest.NewContext(), namespace)
	if err := rest.BeforeUpdate(strategy, ctx, newRuntimeObj, oldRuntimeObj); err != nil {
		return err
	}

	// This model currently mirrors no additional validating admission for Pod/ReplicaSet updates.
	if err := applyAdmissionValidate(legacyNewObj); err != nil {
		return err
	}

	if err := legacyscheme.Scheme.Convert(legacyNewObj, newObj, nil); err != nil {
		return errors.NewBadRequest(fmt.Sprintf("failed to convert internal updated object back to versioned object: %v", err))
	}
	return nil
}

func applyValidationAndDefaulting(obj interface{}, name string) error {
	// This applies OpenAPI schema defaults like DNSPolicy=ClusterFirst, RestartPolicy=Always, etc.
	// In real k8s, this happens in the decoder before the handler even sees the object.
	// We do it here because we don't have a full decode pipeline.
	// Reference: https://github.com/kubernetes/kubernetes/blob/release-1.34/staging/src/k8s.io/apiserver/pkg/endpoints/handlers/create.go#L127
	if err := applySchemaDefaults(obj); err != nil {
		return err
	}
	legacyObj, err := convertVersionedToLegacy(obj)
	if err != nil {
		return err
	}

	// Apply mutating admission.
	// In real k8s, this runs in the create handler before storage create:
	// Reference: https://github.com/kubernetes/kubernetes/blob/release-1.34/staging/src/k8s.io/apiserver/pkg/endpoints/handlers/create.go#L202-L206
	if err := applyAdmissionMutate(legacyObj); err != nil {
		return err
	}

	// Apply the strategy's PrepareForCreate hook.
	// This is part of rest.BeforeCreate in the storage layer:
	// Reference: https://github.com/kubernetes/kubernetes/blob/release-1.34/staging/src/k8s.io/apiserver/pkg/registry/rest/create.go#L120
	if err := applyStrategyPrepareForCreate(legacyObj); err != nil {
		return err
	}

	// Apply the strategy's custom validation.
	// Note: generic metadata validation from rest.BeforeCreate is handled separately.
	// Reference: https://github.com/kubernetes/kubernetes/blob/release-1.34/staging/src/k8s.io/apiserver/pkg/registry/rest/create.go#L122-L124
	if err := applyStrategyValidate(legacyObj, name); err != nil {
		return err
	}

	// Canonicalize the object after validation, matching rest.BeforeCreate.
	// Reference: https://github.com/kubernetes/kubernetes/blob/release-1.34/staging/src/k8s.io/apiserver/pkg/registry/rest/create.go#L137
	if err := applyStrategyCanonicalize(legacyObj); err != nil {
		return err
	}

	// Apply validating admission after BeforeCreate has produced a fully formed object.
	// Reference: https://github.com/kubernetes/kubernetes/blob/release-1.34/staging/src/k8s.io/apiserver/pkg/registry/generic/registry/store.go#L504-L510
	if err := applyAdmissionValidate(legacyObj); err != nil {
		return err
	}

	// Model-specific: write the final internal object back into the caller's
	// original versioned object pointer.
	if err := legacyscheme.Scheme.Convert(legacyObj, obj, nil); err != nil {
		return errors.NewBadRequest(fmt.Sprintf("failed to convert internal object back to versioned object: %v", err))
	}
	return nil
}

func (s *State) create(kind, namespace string, obj interface{}) (interface{}, error) {
	s.mu.Lock()
	defer s.mu.Unlock()

	objCopy := deepCopy(obj)

	metadata, err := meta.Accessor(objCopy)
	if err != nil {
		return nil, fmt.Errorf("failed to access object metadata: %w", err)
	}

	// Reference: https://github.com/kubernetes/kubernetes/blob/release-1.34/staging/src/k8s.io/apiserver/pkg/endpoints/handlers/create.go#L171
	rest.WipeObjectMetaSystemFields(metadata)

	// Reference: https://github.com/kubernetes/kubernetes/blob/release-1.34/staging/src/k8s.io/apiserver/pkg/endpoints/handlers/create.go#L175
	if err = rest.EnsureObjectNamespaceMatchesRequestNamespace(namespace, metadata); err != nil {
		return nil, err
	}

	// Reference: https://github.com/kubernetes/kubernetes/blob/release-1.34/staging/src/k8s.io/apiserver/pkg/registry/generic/registry/store.go#L484
	// We don't directly call rest.FillObjectMetaSystemFields(metadata) here because we want to prove the generated UID is never used before
	metadata.SetCreationTimestamp(metav1.Now())
	metadata.SetUID(s.generateNewUIDAndUpdate())

	// Reference: https://github.com/kubernetes/kubernetes/blob/release-1.34/staging/src/k8s.io/apiserver/pkg/registry/generic/registry/store.go#L485-L487
	name := metadata.GetName()
	generateName := metadata.GetGenerateName()
	if name == "" {
		if generateName == "" {
			return nil, fmt.Errorf("object of kind %q must specify a name or generateName", kind)
		}
		name = s.generateNewName(kind, namespace, generateName)
		metadata.SetName(name)
	}

	if err = applyValidationAndDefaulting(objCopy, name); err != nil {
		return nil, err
	}

	// Reference: https://github.com/kubernetes/kubernetes/blob/release-1.34/staging/src/k8s.io/apiserver/pkg/registry/rest/create.go#L129-L131
	if err = validateObjectMeta(metadata, kind); err != nil {
		return nil, err
	}

	// The storage layer returns AlreadyExists error if the key already exists in etcd
	key := KKey{
		Kind:      kind,
		Name:      name,
		Namespace: namespace,
	}
	if _, exists := s.m[key]; exists {
		return nil, errors.NewAlreadyExists(schema.GroupResource{Resource: kind}, name)
	}

	metadata.SetResourceVersion(s.generateNewRVAndUpdate())

	s.m[key] = objCopy

	return deepCopy(objCopy), nil
}

// update models the ordinary storage update path for Kubernetes resources, excluding
// UpdateOptions and create-on-update.
// References:
// - https://github.com/kubernetes/kubernetes/blob/release-1.34/staging/src/k8s.io/apiserver/pkg/registry/generic/registry/store.go#L652-L777
// - https://github.com/kubernetes/kubernetes/blob/release-1.34/staging/src/k8s.io/apimachinery/pkg/api/validation/objectmeta.go#L233-L260
func (s *State) update(kind, namespace string, obj interface{}) (interface{}, error) {
	s.mu.Lock()
	defer s.mu.Unlock()

	objCopy := deepCopy(obj)

	metadata, err := meta.Accessor(objCopy)
	if err != nil {
		return nil, fmt.Errorf("failed to access object metadata: %w", err)
	}

	if err := rest.EnsureObjectNamespaceMatchesRequestNamespace(namespace, metadata); err != nil {
		return nil, err
	}

	name := metadata.GetName()
	if name == "" {
		return nil, errors.NewBadRequest(fmt.Sprintf("object of kind %q must specify a name for update", kind))
	}

	key := KKey{
		Kind:      kind,
		Name:      name,
		Namespace: namespace,
	}

	existingObj, exists := s.m[key]
	if !exists {
		return nil, errors.NewNotFound(schema.GroupResource{Resource: kind}, name)
	}

	existingObjCopy := deepCopy(existingObj)
	existingMetadata, err := meta.Accessor(existingObjCopy)
	if err != nil {
		return nil, fmt.Errorf("failed to access existing object metadata: %w", err)
	}

	// A non-empty UID on the incoming object acts like a storage precondition in the real update path.
	if uid := metadata.GetUID(); len(uid) > 0 && uid != existingMetadata.GetUID() {
		return nil, errors.NewConflict(
			schema.GroupResource{Resource: kind},
			name,
			fmt.Errorf("UID mismatch: expected %q, got %q", existingMetadata.GetUID(), uid),
		)
	}

	allowUnconditional, err := allowUnconditionalUpdate(kind)
	if err != nil {
		return nil, err
	}

	// Store.Update copies the live resourceVersion onto the object when the strategy allows
	// unconditional update and the client omitted metadata.resourceVersion.
	if metadata.GetResourceVersion() == "" {
		if !allowUnconditional {
			return nil, errors.NewInvalid(
				schema.GroupKind{Kind: kind},
				name,
				field.ErrorList{field.Invalid(field.NewPath("metadata").Child("resourceVersion"), metadata.GetResourceVersion(), "must be specified for an update")},
			)
		}
		metadata.SetResourceVersion(existingMetadata.GetResourceVersion())
	} else {
		// The generic store asks the storage versioner to parse the non-empty incoming
		// resourceVersion before optimistic-lock comparison. A malformed value therefore
		// fails before it can become a normal stale-resourceVersion conflict.
		// Reference: https://github.com/kubernetes/kubernetes/blob/release-1.34/staging/src/k8s.io/apiserver/pkg/registry/generic/registry/store.go#L659-L666
		if _, err := strconv.ParseUint(metadata.GetResourceVersion(), 10, 64); err != nil {
			return nil, malformedUpdateResourceVersionError(err)
		}
	}

	if metadata.GetResourceVersion() != existingMetadata.GetResourceVersion() {
		return nil, errors.NewConflict(
			schema.GroupResource{Resource: kind},
			name,
			fmt.Errorf("resourceVersion mismatch: expected %q, got %q", existingMetadata.GetResourceVersion(), metadata.GetResourceVersion()),
		)
	}

	if err := applyValidationAndDefaultingOnUpdate(objCopy, existingObjCopy, namespace); err != nil {
		return nil, err
	}

	// The apiserver deletes objects during update when they are already deleting and the update
	// removes the last finalizer.
	// Reference: https://github.com/kubernetes/kubernetes/blob/release-1.34/staging/src/k8s.io/apiserver/pkg/registry/generic/registry/store.go#L565-L583
	if genericregistry.ShouldDeleteDuringUpdate(context.Background(), "", objCopy.(runtime.Object), existingObjCopy.(runtime.Object)) {
		delete(s.m, key)
		return deepCopy(objCopy), nil
	}

	metadata, err = meta.Accessor(objCopy)
	if err != nil {
		return nil, fmt.Errorf("failed to access updated object metadata: %w", err)
	}
	metadata.SetResourceVersion(s.generateNewRVAndUpdate())

	s.m[key] = objCopy
	return deepCopy(objCopy), nil
}

// shouldOrphanDependents determines if the orphan finalizer should be set based on DeleteOptions.
// Reference: https://github.com/kubernetes/kubernetes/blob/release-1.34/staging/src/k8s.io/apiserver/pkg/registry/generic/registry/store.go#L888-L925
func shouldOrphanDependents(metadata metav1.Object, options *metav1.DeleteOptions) bool {
	// If PropagationPolicy is set, it takes highest priority
	if options != nil && options.PropagationPolicy != nil {
		switch *options.PropagationPolicy {
		case metav1.DeletePropagationOrphan:
			return true
		case metav1.DeletePropagationBackground, metav1.DeletePropagationForeground:
			return false
		}
	}

	// Check if finalizer already exists in the object
	finalizers := metadata.GetFinalizers()
	for _, f := range finalizers {
		switch f {
		case metav1.FinalizerOrphanDependents:
			return true
		case metav1.FinalizerDeleteDependents:
			return false
		}
	}

	// Default: don't orphan (use background deletion)
	return false
}

// shouldDeleteDependents determines if the foreground deletion finalizer should be set based on DeleteOptions.
// Reference: https://github.com/kubernetes/kubernetes/blob/release-1.34/staging/src/k8s.io/apiserver/pkg/registry/generic/registry/store.go#L927-L966
func shouldDeleteDependents(metadata metav1.Object, options *metav1.DeleteOptions) bool {
	// If PropagationPolicy is set, it takes highest priority
	if options != nil && options.PropagationPolicy != nil {
		switch *options.PropagationPolicy {
		case metav1.DeletePropagationForeground:
			return true
		case metav1.DeletePropagationBackground, metav1.DeletePropagationOrphan:
			return false
		}
	}

	// Check if finalizer already exists in the object
	finalizers := metadata.GetFinalizers()
	for _, f := range finalizers {
		switch f {
		case metav1.FinalizerDeleteDependents:
			return true
		case metav1.FinalizerOrphanDependents:
			return false
		}
	}

	// Default: don't delete in foreground
	return false
}

// deletionFinalizersForGarbageCollection determines which finalizers should be set for garbage collection.
// It returns whether the finalizer list needs updating and the new finalizer list.
// Reference: https://github.com/kubernetes/kubernetes/blob/release-1.34/staging/src/k8s.io/apiserver/pkg/registry/generic/registry/store.go#L976-L1005
func (s *State) deletionFinalizersForGarbageCollection(
	metadata metav1.Object,
	options *metav1.DeleteOptions,
	ownerUID types.UID,
) (bool, []string) {
	shouldOrphan := shouldOrphanDependents(metadata, options)
	shouldDeleteInForeground := shouldDeleteDependents(metadata, options)

	// Start with existing finalizers, but remove GC-related ones
	// (we'll add them back if needed)
	newFinalizers := []string{}
	for _, f := range metadata.GetFinalizers() {
		if f == metav1.FinalizerOrphanDependents || f == metav1.FinalizerDeleteDependents {
			continue
		}
		newFinalizers = append(newFinalizers, f)
	}

	// Add GC finalizers based on policy
	if shouldOrphan {
		newFinalizers = append(newFinalizers, metav1.FinalizerOrphanDependents)
	}
	if shouldDeleteInForeground {
		// Add foreground deletion finalizer unconditionally if policy is Foreground
		// The garbage collector will later remove it after processing dependents
		newFinalizers = append(newFinalizers, metav1.FinalizerDeleteDependents)
	}

	// Check if finalizers changed
	oldFinalizers := metadata.GetFinalizers()
	if len(oldFinalizers) != len(newFinalizers) {
		return true, newFinalizers
	}

	// Check if same set of finalizers (order doesn't matter for this check)
	oldSet := make(map[string]bool)
	for _, f := range oldFinalizers {
		oldSet[f] = true
	}
	for _, f := range newFinalizers {
		if !oldSet[f] {
			return true, newFinalizers
		}
	}

	return false, oldFinalizers
}

// validateDeletePreconditions checks if the preconditions in DeleteOptions match the object's metadata.
// Returns a Conflict error if preconditions don't match.
// Reference: https://github.com/kubernetes/kubernetes/blob/release-1.34/staging/src/k8s.io/apiserver/pkg/registry/rest/delete.go (BeforeDelete)
func validateDeletePreconditions(metadata metav1.Object, options *metav1.DeleteOptions, kind string) error {
	if options.Preconditions == nil {
		return nil
	}

	// Check UID precondition
	if options.Preconditions.UID != nil {
		if *options.Preconditions.UID != metadata.GetUID() {
			return errors.NewConflict(
				schema.GroupResource{Resource: kind},
				metadata.GetName(),
				fmt.Errorf("the UID in the precondition (%s) does not match the UID in record (%s). The object might have been deleted and then recreated",
					*options.Preconditions.UID, metadata.GetUID()))
		}
	}

	// Check ResourceVersion precondition
	if options.Preconditions.ResourceVersion != nil {
		if *options.Preconditions.ResourceVersion != metadata.GetResourceVersion() {
			return errors.NewConflict(
				schema.GroupResource{Resource: kind},
				metadata.GetName(),
				fmt.Errorf("the ResourceVersion in the precondition (%s) does not match the ResourceVersion in record (%s). The object might have been modified",
					*options.Preconditions.ResourceVersion, metadata.GetResourceVersion()))
		}
	}

	return nil
}

// checkGracefulDelete calls strategy-specific graceful delete logic.
// Returns (graceful, pendingGraceful, error).
// Reference: https://github.com/kubernetes/kubernetes/blob/release-1.34/pkg/registry/core/pod/strategy.go#L162-L191
func checkGracefulDelete(kind string, obj interface{}, options *metav1.DeleteOptions) (bool, bool, error) {
	ctx := context.Background()

	// Negative grace periods are treated as 1s
	if options.GracePeriodSeconds != nil && *options.GracePeriodSeconds < 0 {
		period := int64(1)
		options.GracePeriodSeconds = &period
	}

	switch kind {
	case "Pod":
		pod, ok := obj.(*corev1.Pod)
		if !ok {
			return false, false, fmt.Errorf("expected *corev1.Pod for kind Pod, got %T", obj)
		}

		// Convert to internal type for strategy
		internalPod := &core.Pod{}
		if err := legacyscheme.Scheme.Convert(pod, internalPod, nil); err != nil {
			return false, false, err
		}

		// Call pod strategy's CheckGracefulDelete
		graceful := podstrategy.Strategy.CheckGracefulDelete(ctx, internalPod, options)

		// Check if already pending graceful deletion
		pendingGraceful := internalPod.DeletionTimestamp != nil

		// Convert back to external type
		if err := legacyscheme.Scheme.Convert(internalPod, pod, nil); err != nil {
			return false, false, err
		}

		return graceful, pendingGraceful, nil

	case "ReplicaSet":
		// ReplicaSets don't support graceful deletion
		return false, false, nil

	default:
		return false, false, fmt.Errorf("unsupported kind: %s", kind)
	}
}

// updateForGracefulDeletionAndFinalizers sets DeletionTimestamp and DeletionGracePeriodSeconds,
// updates finalizers, assigns a fresh resource version, and stores the updated object.
// Returns the updated object and whether to delete immediately.
// Reference: https://github.com/kubernetes/kubernetes/blob/release-1.34/staging/src/k8s.io/apiserver/pkg/registry/generic/registry/store.go#L1044-L1129
func (s *State) updateForGracefulDeletionAndFinalizers(
	key KKey,
	obj interface{},
	metadata metav1.Object,
	options *metav1.DeleteOptions,
	graceful bool,
	finalizersChanged bool,
) (interface{}, bool, error) {
	pendingFinalizers := len(metadata.GetFinalizers()) != 0

	// Track if this is the first time setting DeletionTimestamp
	firstGracefulDeletion := metadata.GetDeletionTimestamp() == nil

	// Set DeletionTimestamp if not already set
	if firstGracefulDeletion {
		now := metav1.Now()
		metadata.SetDeletionTimestamp(&now)
	}

	// Set DeletionGracePeriodSeconds
	// Reference: https://github.com/kubernetes/kubernetes/blob/release-1.34/staging/src/k8s.io/apiserver/pkg/registry/generic/registry/store.go#L1028
	gracePeriod := int64(0)
	if graceful && options.GracePeriodSeconds != nil {
		// For resources that support graceful deletion, use the specified grace period
		gracePeriod = *options.GracePeriodSeconds
		metadata.SetDeletionGracePeriodSeconds(options.GracePeriodSeconds)
	} else if graceful {
		// For graceful resources with no grace period specified, use 0
		metadata.SetDeletionGracePeriodSeconds(&gracePeriod)
	} else if pendingFinalizers {
		// For resources that don't support graceful deletion (like ReplicaSets),
		// if there are finalizers, set DeletionGracePeriodSeconds to 0.
		// This matches markAsDeleting behavior in Kubernetes.
		metadata.SetDeletionGracePeriodSeconds(&gracePeriod)
	}

	// Increment generation when setting DeletionTimestamp for the first time
	// Reference: https://github.com/kubernetes/kubernetes/blob/release-1.34/staging/src/k8s.io/apiserver/pkg/registry/rest/delete.go#L166-L172
	// For graceful deletion: increment when first setting DeletionTimestamp
	// For non-graceful deletion with finalizers: increment in markAsDeleting
	// Reference: https://github.com/kubernetes/kubernetes/blob/release-1.34/staging/src/k8s.io/apiserver/pkg/registry/generic/registry/store.go#L1016-L1020
	if firstGracefulDeletion && metadata.GetGeneration() > 0 {
		if graceful {
			// Graceful deletion: increment generation when first setting DeletionTimestamp
			metadata.SetGeneration(metadata.GetGeneration() + 1)
		} else if pendingFinalizers {
			// Non-graceful deletion with finalizers: increment generation (matches markAsDeleting)
			metadata.SetGeneration(metadata.GetGeneration() + 1)
		}
	}

	// Increment resource version (object was updated)
	s.resourceVersionCounter++
	metadata.SetResourceVersion(strconv.FormatInt(s.resourceVersionCounter, 10))

	// Store the updated object
	s.m[key] = obj

	// Determine if we should delete immediately:
	// - If there are pending finalizers, never delete immediately
	// - If grace period > 0, never delete immediately
	// - Otherwise, delete immediately (grace period is 0 and no finalizers)
	deleteImmediately := !pendingFinalizers && gracePeriod == 0

	return deepCopy(obj), deleteImmediately, nil
}

// - TODO:
//   - DeleteCollection (bulk delete with label selectors)
//   - Admission webhooks for delete validation
//   - ResourceQuota updates on deletion
func (s *State) delete(key KKey, options metav1.DeleteOptions) error {
	s.mu.Lock()
	defer s.mu.Unlock()

	// 1. Get existing object
	obj, exists := s.m[key]
	if !exists {
		return errors.NewNotFound(schema.GroupResource{Resource: key.Kind}, key.Name)
	}

	objCopy := deepCopy(obj)
	metadata, err := meta.Accessor(objCopy)
	if err != nil {
		return fmt.Errorf("failed to access object metadata: %w", err)
	}

	// 2. Validate preconditions (UID, ResourceVersion)
	if err := validateDeletePreconditions(metadata, &options, key.Kind); err != nil {
		return err
	}

	// 3. Call strategy's CheckGracefulDelete
	graceful, pendingGraceful, err := checkGracefulDelete(key.Kind, objCopy, &options)
	if err != nil {
		return err
	}

	// 4. Update GC finalizers based on PropagationPolicy (Phase C1)
	// Reference: https://github.com/kubernetes/kubernetes/blob/release-1.34/staging/src/k8s.io/apiserver/pkg/registry/generic/registry/store.go#L1172-L1176
	shouldUpdateFinalizers, newFinalizers := s.deletionFinalizersForGarbageCollection(metadata, &options, metadata.GetUID())
	if shouldUpdateFinalizers {
		metadata.SetFinalizers(newFinalizers)
	}

	// If already pending graceful deletion and no finalizer updates needed, just return success
	// (the deletion timestamp was already set in a previous delete call)
	// Note: We still allow updating finalizers on already-deleting objects to match real API behavior
	if pendingGraceful && !shouldUpdateFinalizers {
		return nil
	}

	// 5. Check for finalizers
	pendingFinalizers := len(metadata.GetFinalizers()) != 0

	// 6. Graceful deletion or finalizers? Update object and possibly delete immediately
	// Reference: https://github.com/kubernetes/kubernetes/blob/release-1.34/staging/src/k8s.io/apiserver/pkg/registry/generic/registry/store.go#L1174
	if graceful || pendingFinalizers || shouldUpdateFinalizers {
		_, deleteImmediately, err := s.updateForGracefulDeletionAndFinalizers(key, objCopy, metadata, &options, graceful, shouldUpdateFinalizers)
		if err != nil {
			return err
		}

		// If delete immediately (grace period is 0 and no finalizers), remove from storage
		if deleteImmediately {
			delete(s.m, key)
		}

		return nil
	}

	// 7. Delete immediately (no graceful deletion needed)
	delete(s.m, key)

	return nil
}

// PodDelete2 deletes a Pod with full DeleteOptions support, including preconditions,
// graceful deletion, and finalizer handling. Returns the deleted (or updated) Pod object.
// PodCreate2 creates a Pod using create, which includes admission controller logic.
func (s *State) PodCreate2(namespace string, pod *corev1.Pod) (*corev1.Pod, error) {
	obj, err := s.create("Pod", namespace, pod)
	if err != nil {
		return nil, err
	}

	createdPod, ok := obj.(*corev1.Pod)
	if !ok {
		return nil, fmt.Errorf("create returned unexpected type %T", obj)
	}

	return createdPod, nil
}

// ReplicaSetCreate2 creates a ReplicaSet using create, which includes admission controller logic.
func (s *State) ReplicaSetCreate2(namespace string, rs *appsv1.ReplicaSet) (*appsv1.ReplicaSet, error) {
	obj, err := s.create("ReplicaSet", namespace, rs)
	if err != nil {
		return nil, err
	}

	createdRS, ok := obj.(*appsv1.ReplicaSet)
	if !ok {
		return nil, fmt.Errorf("create returned unexpected type %T", obj)
	}

	return createdRS, nil
}

// PodUpdate2 updates a Pod using the richer storage/update model.
func (s *State) PodUpdate2(namespace string, pod *corev1.Pod) (*corev1.Pod, error) {
	obj, err := s.update("Pod", namespace, pod)
	if err != nil {
		return nil, err
	}

	updatedPod, ok := obj.(*corev1.Pod)
	if !ok {
		return nil, fmt.Errorf("update returned unexpected type %T", obj)
	}

	return updatedPod, nil
}

// ReplicaSetUpdate2 updates a ReplicaSet using the richer storage/update model.
func (s *State) ReplicaSetUpdate2(namespace string, rs *appsv1.ReplicaSet) (*appsv1.ReplicaSet, error) {
	obj, err := s.update("ReplicaSet", namespace, rs)
	if err != nil {
		return nil, err
	}

	updatedRS, ok := obj.(*appsv1.ReplicaSet)
	if !ok {
		return nil, fmt.Errorf("update returned unexpected type %T", obj)
	}

	return updatedRS, nil
}

// PodDelete2 deletes a Pod with full DeleteOptions support, including graceful deletion.
func (s *State) PodDelete2(namespace, name string, options metav1.DeleteOptions) error {
	key := KKey{Kind: "Pod", Namespace: namespace, Name: name}
	return s.delete(key, options)
}

// ReplicaSetDelete2 deletes a ReplicaSet with full DeleteOptions support.
// ReplicaSets don't support graceful deletion but do support finalizers and preconditions.
func (s *State) ReplicaSetDelete2(namespace, name string, options metav1.DeleteOptions) error {
	key := KKey{Kind: "ReplicaSet", Namespace: namespace, Name: name}
	return s.delete(key, options)
}
