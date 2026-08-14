package apimodel

import (
	"context"
	"fmt"
	"math/rand"
	"reflect"
	"strconv"
	"sync"
	"time"

	appsv1 "k8s.io/api/apps/v1"
	corev1 "k8s.io/api/core/v1"
	v1 "k8s.io/api/core/v1"
	"k8s.io/apimachinery/pkg/api/errors"
	"k8s.io/apimachinery/pkg/api/meta"
	apivalidation "k8s.io/apimachinery/pkg/api/validation"
	metav1 "k8s.io/apimachinery/pkg/apis/meta/v1"
	metav1validation "k8s.io/apimachinery/pkg/apis/meta/v1/validation"
	"k8s.io/apimachinery/pkg/labels"
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
	"k8s.io/kubernetes/pkg/controller"
	deploymentstrategy "k8s.io/kubernetes/pkg/registry/apps/deployment"
	rsstrategy "k8s.io/kubernetes/pkg/registry/apps/replicaset"
	stsstrategy "k8s.io/kubernetes/pkg/registry/apps/statefulset"
	pvcstrategy "k8s.io/kubernetes/pkg/registry/core/persistentvolumeclaim"
	podstrategy "k8s.io/kubernetes/pkg/registry/core/pod"

	_ "k8s.io/kubernetes/pkg/apis/apps/install"
)

// What's missing in this model:
//
// (1) Patch (JSON Patch, Merge Patch, Strategic Merge Patch)
//
// (2) Transition validation during Update: validate that state transitions are valid (e.g., Phase changes)
//
// (3) API options, e.g., CreateOption / UpdateOptions
//     Reference: https://github.com/kubernetes/kubernetes/blob/release-1.34/staging/src/k8s.io/apimachinery/pkg/apis/meta/v1/types.go#L579
//
// (4) Admission webhooks and admission plugins
//     - Validating webhooks: https://github.com/kubernetes/kubernetes/blob/release-1.34/staging/src/k8s.io/apiserver/pkg/admission/plugin/webhook/validating/plugin.go
//     - Mutating webhooks: https://github.com/kubernetes/kubernetes/blob/release-1.34/staging/src/k8s.io/apiserver/pkg/admission/plugin/webhook/mutating/plugin.go
//     - Built-in plugins: https://github.com/kubernetes/kubernetes/blob/release-1.34/pkg/kubeapiserver/admission/exclusion/resources.go
//
// (5) Warnings collection - Collects warnings during create/update (non-fatal issues)
//     Reference: https://github.com/kubernetes/kubernetes/blob/release-1.34/staging/src/k8s.io/apiserver/pkg/registry/rest/create.go#L133 (WarningsOnCreate)
//
// (6) BeginCreate/FinishCreate/AfterCreate hooks
//     Reference: https://github.com/kubernetes/kubernetes/blob/release-1.34/staging/src/k8s.io/apiserver/pkg/registry/generic/registry/store.go#L490-L499
//     Reference: https://github.com/kubernetes/kubernetes/blob/release-1.34/staging/src/k8s.io/apiserver/pkg/registry/generic/registry/store.go#L551-L553

type State struct {
	m                      map[KKey]interface{}
	usedUID                map[types.UID]struct{}
	usedRV                 map[string]struct{}
	resourceVersionCounter int64
	mu                     *sync.Mutex
}

var ModelState = NewState()

type KKey struct {
	Kind      string
	Name      string
	Namespace string
}

func NewState() *State {
	return &State{
		m:                      make(map[KKey]interface{}),
		usedUID:                make(map[types.UID]struct{}),
		usedRV:                 make(map[string]struct{}),
		resourceVersionCounter: 0,
		mu:                     new(sync.Mutex),
	}
}

func deepCopy(obj interface{}) interface{} {
	switch o := obj.(type) {
	case *corev1.Pod:
		return o.DeepCopy()
	case *corev1.PersistentVolumeClaim:
		return o.DeepCopy()
	case *appsv1.ReplicaSet:
		return o.DeepCopy()
	case *appsv1.StatefulSet:
		return o.DeepCopy()
	case *appsv1.Deployment:
		return o.DeepCopy()
	default:
		panic(fmt.Sprintf("copyObject: unsupported type %T", obj))
	}
}

func (s *State) objListLocked(kind, namespace string) (items []interface{}) {
	for key, val := range s.m {
		if kind == key.Kind {
			if namespace == metav1.NamespaceAll || namespace == key.Namespace {
				items = append(items, deepCopy(val))
			}
		}
	}
	return items
}

func (s *State) objList(kind, namespace string) (items []interface{}) {
	s.mu.Lock()
	defer s.mu.Unlock()

	return s.objListLocked(kind, namespace)
}

func filterByLabelSelector(items []interface{}, selector labels.Selector) ([]interface{}, error) {
	var filtered_items []interface{}
	for _, val := range items {
		metadata, err := meta.Accessor(val)
		if err != nil {
			return filtered_items, err
		}
		if selector.Matches(labels.Set(metadata.GetLabels())) {
			filtered_items = append(filtered_items, val)
		}
	}
	return filtered_items, nil
}

func (s *State) objListBySelector(kind, namespace string, selector labels.Selector) ([]interface{}, error) {
	return filterByLabelSelector(s.objList(kind, namespace), selector)
}

func index_of(indexName string, obj interface{}) ([]string, error) {
	if indexName == controller.PodControllerIndex {
		pod, ok := obj.(*v1.Pod)
		if !ok {
			return nil, nil
		}
		// Get the ControllerRef of the Pod to check if it's managed by a controller.
		// Index with a non-nil controller (indicating an owned pod) or a nil controller (indicating an orphan pod).
		return []string{controller.PodControllerIndexKey(pod.Namespace, metav1.GetControllerOf(pod))}, nil
	} else {
		return nil, fmt.Errorf("index %q does not exist", indexName)
	}
}

// Returned value must be treated as read-only.
func (s *State) Index(kind, indexName string, obj interface{}) ([]interface{}, error) {
	s.mu.Lock()
	defer s.mu.Unlock()

	indexedValues, err := index_of(indexName, obj)
	if err != nil {
		return nil, err
	}

	if len(indexedValues) == 0 {
		return nil, nil
	}

	indexedValueSet := make(map[string]struct{}, len(indexedValues))
	for _, v := range indexedValues {
		indexedValueSet[v] = struct{}{}
	}

	var items []interface{}
	for _, val := range s.objListLocked(kind, metav1.NamespaceAll) {
		values, err := index_of(indexName, val)
		if err != nil {
			return nil, err
		}
		for _, v := range values {
			if _, match := indexedValueSet[v]; match {
				items = append(items, val)
				break
			}
		}
	}
	return items, nil
}

// Returned value must be treated as read-only.
func (s *State) ByIndex(kind, indexName, indexedValue string) ([]interface{}, error) {
	s.mu.Lock()
	defer s.mu.Unlock()

	var items []interface{}
	listed := s.objListLocked(kind, metav1.NamespaceAll)
	for _, val := range listed {
		values, err := index_of(indexName, val)
		if err != nil {
			return nil, err
		}
		for _, v := range values {
			if v == indexedValue {
				items = append(items, val)
				break
			}
		}
	}
	return items, nil
}

func (s *State) get(key KKey) (interface{}, error) {
	s.mu.Lock()
	defer s.mu.Unlock()

	item, exists := s.m[key]
	if exists {
		return deepCopy(item), nil
	} else {
		return nil, errors.NewNotFound(
			schema.GroupResource{Resource: key.Kind}, key.Name)
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
	case *corev1.PersistentVolumeClaim:
		internalPVC := &core.PersistentVolumeClaim{}
		if err := legacyscheme.Scheme.Convert(typed, internalPVC, nil); err != nil {
			return nil, errors.NewBadRequest(fmt.Sprintf("failed to convert v1.PersistentVolumeClaim to internal PersistentVolumeClaim: %v", err))
		}
		return internalPVC, nil
	case *appsv1.ReplicaSet:
		internalRS := &apps.ReplicaSet{}
		if err := legacyscheme.Scheme.Convert(typed, internalRS, nil); err != nil {
			return nil, errors.NewBadRequest(fmt.Sprintf("failed to convert appsv1.ReplicaSet to internal ReplicaSet: %v", err))
		}
		return internalRS, nil
	case *appsv1.StatefulSet:
		internalSTS := &apps.StatefulSet{}
		if err := legacyscheme.Scheme.Convert(typed, internalSTS, nil); err != nil {
			return nil, errors.NewBadRequest(fmt.Sprintf("failed to convert appsv1.StatefulSet to internal StatefulSet: %v", err))
		}
		return internalSTS, nil
	case *appsv1.Deployment:
		internalDeployment := &apps.Deployment{}
		if err := legacyscheme.Scheme.Convert(typed, internalDeployment, nil); err != nil {
			return nil, errors.NewBadRequest(fmt.Sprintf("failed to convert appsv1.Deployment to internal Deployment: %v", err))
		}
		return internalDeployment, nil
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
	case *corev1.PersistentVolumeClaim:
		corev1defaults.SetObjectDefaults_PersistentVolumeClaim(typed)
	case *appsv1.ReplicaSet:
		// SetObjectDefaults_ReplicaSet recursively applies all defaults:
		// - ReplicaSet.Spec.Replicas defaults to 1
		// - Pod template defaults (same as Pod)
		appsv1defaults.SetObjectDefaults_ReplicaSet(typed)
	case *appsv1.StatefulSet:
		appsv1defaults.SetObjectDefaults_StatefulSet(typed)
	case *appsv1.Deployment:
		appsv1defaults.SetObjectDefaults_Deployment(typed)
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
	case *core.PersistentVolumeClaim:
		pvcstrategy.Strategy.PrepareForCreate(ctx, typed)
	case *apps.ReplicaSet:
		rsstrategy.Strategy.PrepareForCreate(ctx, typed)
	case *apps.StatefulSet:
		stsstrategy.Strategy.PrepareForCreate(ctx, typed)
	case *apps.Deployment:
		deploymentstrategy.Strategy.PrepareForCreate(ctx, typed)
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
	case *core.PersistentVolumeClaim:
		applyPersistentVolumeClaimProtectionAdmission(typed)
	case *apps.ReplicaSet:
		return nil
	case *apps.StatefulSet:
		return nil
	case *apps.Deployment:
		return nil
	default:
		return fmt.Errorf("unsupported object type for strategy and validation: %T", obj)
	}
	return nil
}

// applyPersistentVolumeClaimProtectionAdmission mirrors the built-in
// StorageObjectInUseProtection admission plugin. Envtest enables this plugin on
// PVC creates, and the finalizer affects later delete behavior, so the model
// needs to store it rather than treating it as ignorable metadata.
func applyPersistentVolumeClaimProtectionAdmission(pvc *core.PersistentVolumeClaim) {
	const pvcProtectionFinalizer = "kubernetes.io/pvc-protection"
	for _, finalizer := range pvc.Finalizers {
		if finalizer == pvcProtectionFinalizer {
			return
		}
	}
	pvc.Finalizers = append(pvc.Finalizers, pvcProtectionFinalizer)
}

// applyPostPrepareCreateDefaults restores server-owned create defaults that are
// lost when a REST strategy clears user-controlled fields. PVC create defaulting
// initially sets status.phase=Pending, then the PVC strategy clears Status; the
// API server still stores and returns a created PVC with Pending phase.
func applyPostPrepareCreateDefaults(obj interface{}) error {
	switch typed := obj.(type) {
	case *core.Pod:
		return nil
	case *core.PersistentVolumeClaim:
		if typed.Status.Phase == "" {
			typed.Status.Phase = core.ClaimPending
		}
	case *apps.ReplicaSet:
		return nil
	case *apps.StatefulSet:
		return nil
	case *apps.Deployment:
		return nil
	default:
		return fmt.Errorf("unsupported object type for post-prepare create defaults: %T", obj)
	}
	return nil
}

// normalizeVersionedObject removes conversion artifacts after converting an
// internal object back to its external API type. In particular, Kubernetes does
// not store TypeMeta on StatefulSet volumeClaimTemplates, while the internal to
// external conversion can materialize kind/apiVersion on those embedded PVCs.
func normalizeVersionedObject(obj interface{}) {
	switch typed := obj.(type) {
	case *appsv1.StatefulSet:
		for i := range typed.Spec.VolumeClaimTemplates {
			typed.Spec.VolumeClaimTemplates[i].TypeMeta = metav1.TypeMeta{}
		}
	}
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
	case *core.PersistentVolumeClaim:
		return nil
	case *apps.ReplicaSet:
		return nil
	case *apps.StatefulSet:
		return nil
	case *apps.Deployment:
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
	case *core.PersistentVolumeClaim:
		// This model does not mirror any PVC-specific validating admission plugins.
		return nil
	case *apps.ReplicaSet:
		// This model does not mirror any ReplicaSet-specific validating admission plugins.
		return nil
	case *apps.StatefulSet:
		// This model does not mirror any StatefulSet-specific validating admission plugins.
		return nil
	case *apps.Deployment:
		// This model does not mirror any Deployment-specific validating admission plugins.
		return nil
	default:
		return fmt.Errorf("unsupported object type for admission validation: %T", obj)
	}
}

func allowUnconditionalUpdate(kind string) (bool, error) {
	switch kind {
	case "Pod", "PersistentVolumeClaim", "ReplicaSet", "StatefulSet", "Deployment":
		// These strategies return true from AllowUnconditionalUpdate() in release-1.34.
		// References:
		// - https://github.com/kubernetes/kubernetes/blob/release-1.34/pkg/registry/core/pod/strategy.go#L157-L159
		// - https://github.com/kubernetes/kubernetes/blob/release-1.34/pkg/registry/core/persistentvolumeclaim/strategy.go#L134-L136
		// - https://github.com/kubernetes/kubernetes/blob/release-1.34/pkg/registry/apps/replicaset/strategy.go#L159-L160
		// - https://github.com/kubernetes/kubernetes/blob/release-1.34/pkg/registry/apps/statefulset/strategy.go#L191-L193
		// - https://github.com/kubernetes/kubernetes/blob/release-1.34/pkg/registry/apps/deployment/strategy.go#L148-L150
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

func parseResourceVersion(resourceVersion string) (uint64, error) {
	return strconv.ParseUint(resourceVersion, 10, 64)
}

func updateStrategyForLegacyObject(obj interface{}) (rest.RESTUpdateStrategy, error) {
	switch obj.(type) {
	case *core.Pod:
		return podstrategy.Strategy, nil
	case *core.PersistentVolumeClaim:
		return pvcstrategy.Strategy, nil
	case *apps.ReplicaSet:
		return rsstrategy.Strategy, nil
	case *apps.StatefulSet:
		return stsstrategy.Strategy, nil
	case *apps.Deployment:
		return deploymentstrategy.Strategy, nil
	default:
		return nil, fmt.Errorf("unsupported object type for update strategy: %T", obj)
	}
}

func statusUpdateStrategyForLegacyObject(obj interface{}) (rest.RESTUpdateStrategy, error) {
	switch obj.(type) {
	case *core.Pod:
		return podstrategy.StatusStrategy, nil
	case *core.PersistentVolumeClaim:
		return pvcstrategy.StatusStrategy, nil
	case *apps.ReplicaSet:
		return rsstrategy.StatusStrategy, nil
	case *apps.StatefulSet:
		return stsstrategy.StatusStrategy, nil
	case *apps.Deployment:
		return deploymentstrategy.StatusStrategy, nil
	default:
		return nil, fmt.Errorf("unsupported object type for status update strategy: %T", obj)
	}
}

func applyStrategyValidate(obj interface{}, name string) error {
	ctx := context.Background()
	switch typed := obj.(type) {
	case *core.Pod:
		if errs := podstrategy.Strategy.Validate(ctx, typed); len(errs) > 0 {
			return errors.NewInvalid(schema.GroupKind{Group: "", Kind: "Pod"}, name, errs)
		}
	case *core.PersistentVolumeClaim:
		if errs := pvcstrategy.Strategy.Validate(ctx, typed); len(errs) > 0 {
			return errors.NewInvalid(schema.GroupKind{Group: "", Kind: "PersistentVolumeClaim"}, name, errs)
		}
	case *apps.ReplicaSet:
		if errs := rsstrategy.Strategy.Validate(ctx, typed); len(errs) > 0 {
			return errors.NewInvalid(schema.GroupKind{Group: "apps", Kind: "ReplicaSet"}, name, errs)
		}
	case *apps.StatefulSet:
		if errs := stsstrategy.Strategy.Validate(ctx, typed); len(errs) > 0 {
			return errors.NewInvalid(schema.GroupKind{Group: "apps", Kind: "StatefulSet"}, name, errs)
		}
	case *apps.Deployment:
		if errs := deploymentstrategy.Strategy.Validate(ctx, typed); len(errs) > 0 {
			return errors.NewInvalid(schema.GroupKind{Group: "apps", Kind: "Deployment"}, name, errs)
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
	case *core.PersistentVolumeClaim:
		pvcstrategy.Strategy.Canonicalize(typed)
	case *apps.ReplicaSet:
		rsstrategy.Strategy.Canonicalize(typed)
	case *apps.StatefulSet:
		stsstrategy.Strategy.Canonicalize(typed)
	case *apps.Deployment:
		deploymentstrategy.Strategy.Canonicalize(typed)
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
	normalizeVersionedObject(newObj)
	return nil
}

// applyValidationAndDefaultingOnStatusUpdate models the decode/defaulting/storage
// pipeline for a Kubernetes status subresource update. Status REST stores use the
// same generic update path with a status-specific update strategy.
// References:
// - https://github.com/kubernetes/kubernetes/blob/release-1.34/pkg/registry/core/pod/storage/storage.go#L101-L103
// - https://github.com/kubernetes/kubernetes/blob/release-1.34/pkg/registry/apps/replicaset/storage/storage.go#L107-L109
// - https://github.com/kubernetes/kubernetes/blob/release-1.34/staging/src/k8s.io/apiserver/pkg/registry/rest/update.go#L107-L165
func applyValidationAndDefaultingOnStatusUpdate(newObj, oldObj interface{}, namespace string) error {
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

	newRuntimeObj, ok := legacyNewObj.(runtime.Object)
	if !ok {
		return fmt.Errorf("updated object does not implement runtime.Object: %T", legacyNewObj)
	}
	oldRuntimeObj, ok := legacyOldObj.(runtime.Object)
	if !ok {
		return fmt.Errorf("existing object does not implement runtime.Object: %T", legacyOldObj)
	}

	strategy, err := statusUpdateStrategyForLegacyObject(legacyNewObj)
	if err != nil {
		return err
	}

	ctx := genericapirequest.WithNamespace(genericapirequest.NewContext(), namespace)
	if err := rest.BeforeUpdate(strategy, ctx, newRuntimeObj, oldRuntimeObj); err != nil {
		return err
	}

	if err := applyAdmissionValidate(legacyNewObj); err != nil {
		return err
	}

	if err := legacyscheme.Scheme.Convert(legacyNewObj, newObj, nil); err != nil {
		return errors.NewBadRequest(fmt.Sprintf("failed to convert internal status-updated object back to versioned object: %v", err))
	}
	normalizeVersionedObject(newObj)
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

	if err := applyPostPrepareCreateDefaults(legacyObj); err != nil {
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
	normalizeVersionedObject(obj)
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

	if err = rest.EnsureObjectNamespaceMatchesRequestNamespace(namespace, metadata); err != nil {
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
	if uid := metadata.GetUID(); uid != "" && uid != existingMetadata.GetUID() {
		return nil, newUpdateUIDConflictError(kind, name, existingMetadata.GetUID(), uid)
	}

	rv := metadata.GetResourceVersion()
	existingRv := existingMetadata.GetResourceVersion()
	// Store.Update copies the live resourceVersion onto the object when the strategy allows
	// unconditional update and the client omitted metadata.resourceVersion.
	if rv == "" {
		allowUnconditional, err := allowUnconditionalUpdate(kind)
		if err != nil {
			return nil, err
		}

		if !allowUnconditional {
			return nil, errors.NewInvalid(
				schema.GroupKind{Kind: kind},
				name,
				field.ErrorList{field.Invalid(field.NewPath("metadata").Child("resourceVersion"), rv, "must be specified for an update")},
			)
		}
		metadata.SetResourceVersion(existingRv)
	} else {
		// The generic store asks the storage versioner to parse the non-empty incoming
		// resourceVersion before optimistic-lock comparison. A malformed value therefore
		// fails before it can become a normal stale-resourceVersion conflict.
		// Reference: https://github.com/kubernetes/kubernetes/blob/release-1.34/staging/src/k8s.io/apiserver/pkg/registry/generic/registry/store.go#L659-L666
		if _, err = parseResourceVersion(rv); err != nil {
			return nil, malformedUpdateResourceVersionError(err)
		}
	}

	rv = metadata.GetResourceVersion()
	if rv != existingRv {
		return nil, newUpdateResourceVersionConflictError(kind, name, existingRv, rv)
	}

	if err = applyValidationAndDefaultingOnUpdate(objCopy, existingObjCopy, namespace); err != nil {
		return nil, err
	}

	// The apiserver deletes objects during update when they are already deleting and the update
	// removes the last finalizer.
	// Reference: https://github.com/kubernetes/kubernetes/blob/release-1.34/staging/src/k8s.io/apiserver/pkg/registry/generic/registry/store.go#L565-L583
	if shouldDeleteDuringUpdate(objCopy, existingObjCopy) {
		delete(s.m, key)
		return objCopy, nil
	}

	// The storage layer avoids writing no-op updates, so resourceVersion is preserved when the
	// final storage object is unchanged.
	// Reference: https://github.com/kubernetes/kubernetes/blob/release-1.34/staging/src/k8s.io/apiserver/pkg/storage/etcd3/store.go#L539-L562
	if storageObjectDeepEqual(objCopy, existingObjCopy) {
		return existingObjCopy, nil
	}

	metadata.SetResourceVersion(s.generateNewRVAndUpdate())

	s.m[key] = objCopy
	return deepCopy(objCopy), nil
}

func (s *State) updateStatus(kind, namespace string, obj interface{}) (interface{}, error) {
	s.mu.Lock()
	defer s.mu.Unlock()

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
		return nil, errors.NewBadRequest(fmt.Sprintf("object of kind %q must specify a name for status update", kind))
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

	if uid := metadata.GetUID(); uid != "" && uid != existingMetadata.GetUID() {
		return nil, newUpdateUIDConflictError(kind, name, existingMetadata.GetUID(), uid)
	}

	rv := metadata.GetResourceVersion()
	existingRv := existingMetadata.GetResourceVersion()
	if rv == "" {
		allowUnconditional, err := allowUnconditionalUpdate(kind)
		if err != nil {
			return nil, err
		}

		if !allowUnconditional {
			return nil, errors.NewInvalid(
				schema.GroupKind{Kind: kind},
				name,
				field.ErrorList{field.Invalid(field.NewPath("metadata").Child("resourceVersion"), rv, "must be specified for an update")},
			)
		}
		metadata.SetResourceVersion(existingRv)
	} else {
		if _, err = parseResourceVersion(rv); err != nil {
			return nil, malformedUpdateResourceVersionError(err)
		}
	}

	rv = metadata.GetResourceVersion()
	if rv != existingRv {
		return nil, newUpdateResourceVersionConflictError(kind, name, existingRv, rv)
	}

	if err = applyValidationAndDefaultingOnStatusUpdate(objCopy, existingObjCopy, namespace); err != nil {
		return nil, err
	}

	if shouldDeleteDuringUpdate(objCopy, existingObjCopy) {
		delete(s.m, key)
		return objCopy, nil
	}

	if storageObjectDeepEqual(objCopy, existingObjCopy) {
		return existingObjCopy, nil
	}

	metadata.SetResourceVersion(s.generateNewRVAndUpdate())

	s.m[key] = objCopy
	return deepCopy(objCopy), nil
}

// shouldOrphanDependents determines if the orphan finalizer should be set based on DeleteOptions.
// Reference: https://github.com/kubernetes/kubernetes/blob/release-1.34/staging/src/k8s.io/apiserver/pkg/registry/generic/registry/store.go#L888-L925
func shouldOrphanDependents(metadata metav1.Object, options *metav1.DeleteOptions) bool {
	// If an explicit orphan request was set at deletion time, it has highest priority.
	// Reference: https://github.com/kubernetes/kubernetes/blob/release-1.34/staging/src/k8s.io/apiserver/pkg/registry/generic/registry/store.go#L897-L900
	if options != nil && options.OrphanDependents != nil {
		return *options.OrphanDependents
	}

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
	// An explicit orphan request disables foreground deletion finalization.
	// Reference: https://github.com/kubernetes/kubernetes/blob/release-1.34/staging/src/k8s.io/apiserver/pkg/registry/generic/registry/store.go#L939-L943
	if options != nil && options.OrphanDependents != nil {
		return false
	}

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
func deletionFinalizersForGarbageCollection(metadata metav1.Object, options *metav1.DeleteOptions) (bool, []string) {
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

func newPreconditionUIDConflictError(kind string, name string, preconditionUID string, uid string) error {
	return errors.NewConflict(
		schema.GroupResource{Resource: kind},
		name,
		fmt.Errorf("the UID in the precondition (%s) does not match the UID in record (%s). The object might have been deleted and then recreated",
			preconditionUID, uid))
}

func newUpdateUIDConflictError(kind string, name string, existingUID types.UID, uid types.UID) error {
	return errors.NewConflict(
		schema.GroupResource{Resource: kind},
		name,
		fmt.Errorf("UID mismatch: expected %q, got %q", existingUID, uid),
	)
}

func newUpdateResourceVersionConflictError(kind string, name string, existingResourceVersion string, resourceVersion string) error {
	return errors.NewConflict(
		schema.GroupResource{Resource: kind},
		name,
		fmt.Errorf("resourceVersion mismatch: expected %q, got %q", existingResourceVersion, resourceVersion),
	)
}

func newPreconditionRVConflictError(kind string, name string, preconditionRV string, rv string) error {
	return errors.NewConflict(
		schema.GroupResource{Resource: kind},
		name,
		fmt.Errorf("the ResourceVersion in the precondition (%s) does not match the ResourceVersion in record (%s). The object might have been modified",
			preconditionRV, rv))
}

// validateDeleteOptions checks structural DeleteOptions validation that upstream performs in BeforeDelete.
// Reference: https://github.com/kubernetes/kubernetes/blob/release-1.34/staging/src/k8s.io/apiserver/pkg/registry/rest/delete.go#L80-L81
func validateDeleteOptions(options *metav1.DeleteOptions) error {
	if errs := metav1validation.ValidateDeleteOptions(options); len(errs) > 0 {
		return errors.NewInvalid(
			schema.GroupKind{Group: metav1.GroupName, Kind: "DeleteOptions"},
			"",
			errs,
		)
	}
	return nil
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
			return newPreconditionUIDConflictError(kind, metadata.GetName(),
				string(*options.Preconditions.UID), string(metadata.GetUID()))
		}
	}

	// Check ResourceVersion precondition
	if options.Preconditions.ResourceVersion != nil {
		if *options.Preconditions.ResourceVersion != metadata.GetResourceVersion() {
			return newPreconditionRVConflictError(kind, metadata.GetName(),
				string(*options.Preconditions.ResourceVersion), string(metadata.GetResourceVersion()))
		}
	}

	return nil
}

// checkGracefulDelete calls strategy-specific graceful delete logic.
// Returns (graceful, pendingGraceful, error).
// Reference: https://github.com/kubernetes/kubernetes/blob/release-1.34/pkg/registry/core/pod/strategy.go#L162-L191
func checkGracefulDelete(obj interface{}, options *metav1.DeleteOptions) (bool, bool, error) {
	ctx := context.Background()

	// Negative grace periods are treated as 1s.
	if options.GracePeriodSeconds != nil && *options.GracePeriodSeconds < 0 {
		period := int64(1)
		options.GracePeriodSeconds = &period
	}

	metadata, err := meta.Accessor(obj)
	if err != nil {
		return false, false, fmt.Errorf("failed to access object metadata: %w", err)
	}

	// Existing negative grace periods are normalized to 1s before any already-deleting logic.
	// Reference: https://github.com/kubernetes/kubernetes/blob/release-1.34/staging/src/k8s.io/apiserver/pkg/registry/rest/delete.go#L97-L99
	if currentGracePeriod := metadata.GetDeletionGracePeriodSeconds(); currentGracePeriod != nil && *currentGracePeriod < 0 {
		period := int64(1)
		metadata.SetDeletionGracePeriodSeconds(&period)
	}

	// If deletion is already pending, a repeated delete may only shorten the
	// remaining grace period. This mirrors the already-deleting branch in
	// apiserver/pkg/registry/rest.BeforeDelete.
	// Reference: https://github.com/kubernetes/kubernetes/blob/release-1.34/staging/src/k8s.io/apiserver/pkg/registry/rest/delete.go#L107-L151
	if metadata.GetDeletionTimestamp() != nil {
		currentGracePeriod := metadata.GetDeletionGracePeriodSeconds()
		if currentGracePeriod == nil || *currentGracePeriod == 0 {
			return false, false, nil
		}
		if options.GracePeriodSeconds != nil {
			period := *options.GracePeriodSeconds
			if period >= *currentGracePeriod {
				return false, true, nil
			}

			newDeletionTimestamp := metav1.NewTime(
				metadata.GetDeletionTimestamp().Add(-1 * time.Second * time.Duration(*currentGracePeriod)).
					Add(time.Second * time.Duration(period)),
			)
			now := metav1.Now()
			if newDeletionTimestamp.Before(&now) {
				newDeletionTimestamp = now
				if period != 0 {
					// Preserve the "still graceful" behavior when the remaining grace
					// period has already elapsed.
					period = 1
				}
			}
			metadata.SetDeletionTimestamp(&newDeletionTimestamp)
			metadata.SetDeletionGracePeriodSeconds(&period)
			return true, false, nil
		}

		options.GracePeriodSeconds = currentGracePeriod
		return false, true, nil
	}

	switch typed := obj.(type) {
	case *corev1.Pod:
		// Convert to internal type for strategy
		internalPod := &core.Pod{}
		if err := legacyscheme.Scheme.Convert(typed, internalPod, nil); err != nil {
			return false, false, err
		}

		// Call pod strategy's CheckGracefulDelete
		graceful := podstrategy.Strategy.CheckGracefulDelete(ctx, internalPod, options)

		// Check if already pending graceful deletion
		pendingGraceful := internalPod.DeletionTimestamp != nil

		// Convert back to external type
		if err := legacyscheme.Scheme.Convert(internalPod, typed, nil); err != nil {
			return false, false, err
		}

		return graceful, pendingGraceful, nil

	case *appsv1.ReplicaSet:
		// ReplicaSets don't support graceful deletion
		return false, false, nil
	case *corev1.PersistentVolumeClaim:
		// PersistentVolumeClaims don't support graceful deletion
		return false, false, nil
	case *appsv1.StatefulSet:
		// StatefulSets don't support graceful deletion
		return false, false, nil
	case *appsv1.Deployment:
		// Deployments don't support graceful deletion
		return false, false, nil

	default:
		return false, false, fmt.Errorf("unsupported object type for graceful delete: %T", obj)
	}
}

// storageObjectDeepEqual approximates upstream's "did the storage operation actually change the
// stored object?" check, but it is not exactly the same logic.
//
// Upstream relies on the storage-layer GuaranteedUpdate / no-op-update behavior to decide whether
// an update is persisted and therefore whether resourceVersion advances; it does not compare the
// in-memory objects with a single reflect.DeepEqual-style helper in the registry layer.
//
// This model uses reflect.DeepEqual as a simple in-memory approximation because the model has no
// storage codec / transformer layer. It clears fields that the storage versioner clears before
// encoding, which keeps no-op decisions from being affected by request-only resourceVersion or
// selfLink differences. This can still diverge from upstream in edge cases where storage
// normalization or Go representation details affect equality.
func storageObjectDeepEqual(obj1 interface{}, obj2 interface{}) bool {
	obj1Copy := deepCopy(obj1)
	obj2Copy := deepCopy(obj2)

	for _, obj := range []interface{}{obj1Copy, obj2Copy} {
		metadata, err := meta.Accessor(obj)
		if err != nil {
			return false
		}
		metadata.SetResourceVersion("")
		metadata.SetSelfLink("")
	}

	return reflect.DeepEqual(obj1Copy, obj2Copy)
}

func shouldDeleteDuringUpdate(objCopy, existingObjCopy interface{}) bool {
	return genericregistry.ShouldDeleteDuringUpdate(context.Background(), "", objCopy.(runtime.Object), existingObjCopy.(runtime.Object))
}

// deletionTimestampForDelete computes the initial DeletionTimestamp written by the delete path.
// Graceful deletion uses now+gracePeriod; non-graceful deletion with finalizers uses "now",
// mirroring markAsDeleting in upstream storage.
// Reference: https://github.com/kubernetes/kubernetes/blob/release-1.34/staging/src/k8s.io/apiserver/pkg/registry/rest/delete.go#L163-L165
// Reference: https://github.com/kubernetes/kubernetes/blob/release-1.34/staging/src/k8s.io/apiserver/pkg/registry/generic/registry/store.go#L1022-L1028
func deletionTimestampForDelete(graceful bool, gracePeriod int64) *metav1.Time {
	if graceful {
		requestedDeletionTimestamp := metav1.NewTime(
			metav1.Now().Add(time.Second * time.Duration(gracePeriod)),
		)
		return &requestedDeletionTimestamp
	}

	now := metav1.Now()
	return &now
}

func (s *State) delete(key KKey, options metav1.DeleteOptions) error {
	s.mu.Lock()
	defer s.mu.Unlock()

	options = *options.DeepCopy()

	// Get existing object
	obj, exists := s.m[key]
	if !exists {
		return errors.NewNotFound(schema.GroupResource{Resource: key.Kind}, key.Name)
	}

	objCopy := deepCopy(obj)
	metadata, err := meta.Accessor(objCopy)
	if err != nil {
		return fmt.Errorf("failed to access object metadata: %w", err)
	}

	// Validate DeleteOptions the same way rest.BeforeDelete does.
	// Reference: https://github.com/kubernetes/kubernetes/blob/release-1.34/staging/src/k8s.io/apiserver/pkg/registry/rest/delete.go#L80-L81
	if err := validateDeleteOptions(&options); err != nil {
		return err
	}

	// Validate preconditions (UID, ResourceVersion)
	// Reference: https://github.com/kubernetes/kubernetes/blob/release-1.34/staging/src/k8s.io/apiserver/pkg/registry/rest/delete.go#L83-L91
	if err = validateDeletePreconditions(metadata, &options, key.Kind); err != nil {
		return err
	}

	// Call strategy's CheckGracefulDelete
	// Reference: https://github.com/kubernetes/kubernetes/blob/release-1.34/staging/src/k8s.io/apiserver/pkg/registry/rest/delete.go#L154-L174
	graceful, pendingGraceful, err := checkGracefulDelete(objCopy, &options)
	if err != nil {
		return err
	}

	// Once graceful deletion is pending, repeated deletes can only shorten the remaining grace
	// period. For objects already marked deleting with zero grace period, the apiserver still
	// allows PropagationPolicy / OrphanDependents to update GC finalizers.
	// References:
	// - https://github.com/kubernetes/kubernetes/blob/release-1.34/staging/src/k8s.io/apiserver/pkg/registry/generic/registry/store.go#L1062-L1069
	// - https://github.com/kubernetes/kubernetes/blob/release-1.34/staging/src/k8s.io/apiserver/pkg/registry/generic/registry/store.go#L1074-L1084
	if pendingGraceful {
		return nil
	}

	// Recompute GC finalizers for every non-pending delete, including repeated deletes on objects
	// that already have DeletionTimestamp set with zero grace period.
	// Reference: https://github.com/kubernetes/kubernetes/blob/release-1.34/staging/src/k8s.io/apiserver/pkg/registry/generic/registry/store.go#L1074-L1084
	shouldUpdateFinalizers, newFinalizers := deletionFinalizersForGarbageCollection(metadata, &options)

	if shouldUpdateFinalizers {
		metadata.SetFinalizers(newFinalizers)
	}

	gracePeriod := int64(0)
	if graceful && options.GracePeriodSeconds != nil {
		// For resources that support graceful deletion, use the specified grace period.
		gracePeriod = *options.GracePeriodSeconds
	}

	if len(metadata.GetFinalizers()) == 0 && gracePeriod == 0 {
		delete(s.m, key)
		return nil
	}

	currentGracePeriod := metadata.GetDeletionGracePeriodSeconds()
	if currentGracePeriod == nil || *currentGracePeriod != gracePeriod {
		metadata.SetDeletionGracePeriodSeconds(&gracePeriod)
	}

	// Track if this is the first time setting DeletionTimestamp.
	if metadata.GetDeletionTimestamp() == nil {
		// Set DeletionTimestamp if not already set.
		metadata.SetDeletionTimestamp(deletionTimestampForDelete(graceful, gracePeriod))
		// Increment generation when setting DeletionTimestamp for the first time.
		// Reference: https://github.com/kubernetes/kubernetes/blob/release-1.34/staging/src/k8s.io/apiserver/pkg/registry/rest/delete.go#L166-L172
		// For graceful deletion: increment when first setting DeletionTimestamp.
		// For non-graceful deletion with finalizers: increment in markAsDeleting.
		// Reference: https://github.com/kubernetes/kubernetes/blob/release-1.34/staging/src/k8s.io/apiserver/pkg/registry/generic/registry/store.go#L1016-L1020
		if metadata.GetGeneration() > 0 {
			metadata.SetGeneration(metadata.GetGeneration() + 1)
		}
	}

	// Real Kubernetes only advances resourceVersion when the delete path writes a changed
	// object back to storage; no-op delete updates preserve the stored RV.
	if !storageObjectDeepEqual(objCopy, obj) {
		// Assign a fresh resource version for the metadata update.
		metadata.SetResourceVersion(s.generateNewRVAndUpdate())

		// Store the updated object.
		s.m[key] = objCopy
	}
	return nil
}

// Returned value must be treated as read-only.
func (s *State) PodGet(namespace, name string) (*corev1.Pod, error) {
	return s.PodMutGet(namespace, name)
}

func (s *State) PodMutGet(namespace, name string) (*corev1.Pod, error) {
	key := KKey{
		Kind:      "Pod",
		Namespace: namespace,
		Name:      name,
	}

	obj, err := s.get(key)
	if err != nil {
		return nil, err
	}

	pod, ok := obj.(*corev1.Pod)
	if !ok {
		// This should never happen
		return nil, fmt.Errorf("state entry for pod %s/%s is not a *v1.Pod", namespace, name)
	}

	return pod, nil
}

// Returned value must be treated as read-only.
func (s *State) PodList(namespace string, selector labels.Selector) ([]*corev1.Pod, error) {
	return s.PodMutList(namespace, selector)
}

func (s *State) PodMutList(namespace string, selector labels.Selector) ([]*corev1.Pod, error) {
	objs, err := s.objListBySelector("Pod", namespace, selector)
	if err != nil {
		return nil, err
	}

	pods := make([]*corev1.Pod, 0, len(objs))
	for _, obj := range objs {
		pod, ok := obj.(*corev1.Pod)
		if !ok {
			return nil, fmt.Errorf("state entry is not a *v1.Pod")
		}
		pods = append(pods, pod)
	}

	return pods, nil
}

func (s *State) PodCreate(namespace string, pod *corev1.Pod) (*corev1.Pod, error) {
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

func (s *State) PodUpdate(namespace string, pod *corev1.Pod) (*corev1.Pod, error) {
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

func (s *State) PodUpdateStatus(namespace string, pod *corev1.Pod) (*corev1.Pod, error) {
	obj, err := s.updateStatus("Pod", namespace, pod)
	if err != nil {
		return nil, err
	}

	updatedPod, ok := obj.(*corev1.Pod)
	if !ok {
		return nil, fmt.Errorf("status update returned unexpected type %T", obj)
	}

	return updatedPod, nil
}

func (s *State) PodDelete(namespace, name string, options metav1.DeleteOptions) error {
	key := KKey{
		Kind:      "Pod",
		Namespace: namespace,
		Name:      name,
	}

	return s.delete(key, options)
}

// Returned value must be treated as read-only.
func (s *State) ReplicaSetGet(namespace, name string) (*appsv1.ReplicaSet, error) {
	return s.ReplicaSetMutGet(namespace, name)
}

func (s *State) ReplicaSetMutGet(namespace, name string) (*appsv1.ReplicaSet, error) {
	key := KKey{
		Kind:      "ReplicaSet",
		Namespace: namespace,
		Name:      name,
	}

	obj, err := s.get(key)
	if err != nil {
		return nil, err
	}

	rs, ok := obj.(*appsv1.ReplicaSet)
	if !ok {
		// This should never happen
		return nil, fmt.Errorf("state entry for replicaset %s/%s is not a *v1.ReplicaSet", namespace, name)
	}

	return rs, nil
}

// Returned value must be treated as read-only.
func (s *State) ReplicaSetList(namespace string, selector labels.Selector) ([]*appsv1.ReplicaSet, error) {
	return s.ReplicaSetMutList(namespace, selector)
}

func (s *State) ReplicaSetMutList(namespace string, selector labels.Selector) ([]*appsv1.ReplicaSet, error) {
	objs, err := s.objListBySelector("ReplicaSet", namespace, selector)
	if err != nil {
		return nil, err
	}

	rss := make([]*appsv1.ReplicaSet, 0, len(objs))
	for _, obj := range objs {
		rs, ok := obj.(*appsv1.ReplicaSet)
		if !ok {
			return nil, fmt.Errorf("state entry is not a *v1.ReplicaSet")
		}
		rss = append(rss, rs)
	}

	return rss, nil
}

func (s *State) ReplicaSetCreate(namespace string, rs *appsv1.ReplicaSet) (*appsv1.ReplicaSet, error) {
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

func (s *State) ReplicaSetUpdate(namespace string, rs *appsv1.ReplicaSet) (*appsv1.ReplicaSet, error) {
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

func (s *State) ReplicaSetUpdateStatus(namespace string, rs *appsv1.ReplicaSet) (*appsv1.ReplicaSet, error) {
	obj, err := s.updateStatus("ReplicaSet", namespace, rs)
	if err != nil {
		return nil, err
	}

	updatedRS, ok := obj.(*appsv1.ReplicaSet)
	if !ok {
		return nil, fmt.Errorf("status update returned unexpected type %T", obj)
	}

	return updatedRS, nil
}

func (s *State) ReplicaSetDelete(namespace, name string, options metav1.DeleteOptions) error {
	key := KKey{Kind: "ReplicaSet", Namespace: namespace, Name: name}
	return s.delete(key, options)
}

// Returned value must be treated as read-only.
func (s *State) PersistentVolumeClaimGet(namespace, name string) (*corev1.PersistentVolumeClaim, error) {
	return s.PersistentVolumeClaimMutGet(namespace, name)
}

func (s *State) PersistentVolumeClaimMutGet(namespace, name string) (*corev1.PersistentVolumeClaim, error) {
	key := KKey{
		Kind:      "PersistentVolumeClaim",
		Namespace: namespace,
		Name:      name,
	}

	obj, err := s.get(key)
	if err != nil {
		return nil, err
	}

	pvc, ok := obj.(*corev1.PersistentVolumeClaim)
	if !ok {
		// This should never happen
		return nil, fmt.Errorf("state entry for persistentvolumeclaim %s/%s is not a *v1.PersistentVolumeClaim", namespace, name)
	}

	return pvc, nil
}

// Returned value must be treated as read-only.
func (s *State) PersistentVolumeClaimList(namespace string, selector labels.Selector) ([]*corev1.PersistentVolumeClaim, error) {
	return s.PersistentVolumeClaimMutList(namespace, selector)
}

func (s *State) PersistentVolumeClaimMutList(namespace string, selector labels.Selector) ([]*corev1.PersistentVolumeClaim, error) {
	objs, err := s.objListBySelector("PersistentVolumeClaim", namespace, selector)
	if err != nil {
		return nil, err
	}

	claims := make([]*corev1.PersistentVolumeClaim, 0, len(objs))
	for _, obj := range objs {
		claim, ok := obj.(*corev1.PersistentVolumeClaim)
		if !ok {
			return nil, fmt.Errorf("state entry is not a *v1.PersistentVolumeClaim")
		}
		claims = append(claims, claim)
	}

	return claims, nil
}

func (s *State) PersistentVolumeClaimCreate(namespace string, pvc *corev1.PersistentVolumeClaim) (*corev1.PersistentVolumeClaim, error) {
	obj, err := s.create("PersistentVolumeClaim", namespace, pvc)
	if err != nil {
		return nil, err
	}

	createdPVC, ok := obj.(*corev1.PersistentVolumeClaim)
	if !ok {
		return nil, fmt.Errorf("create returned unexpected type %T", obj)
	}

	return createdPVC, nil
}

func (s *State) PersistentVolumeClaimUpdate(namespace string, pvc *corev1.PersistentVolumeClaim) (*corev1.PersistentVolumeClaim, error) {
	obj, err := s.update("PersistentVolumeClaim", namespace, pvc)
	if err != nil {
		return nil, err
	}

	updatedPVC, ok := obj.(*corev1.PersistentVolumeClaim)
	if !ok {
		return nil, fmt.Errorf("update returned unexpected type %T", obj)
	}

	return updatedPVC, nil
}

func (s *State) PersistentVolumeClaimUpdateStatus(namespace string, pvc *corev1.PersistentVolumeClaim) (*corev1.PersistentVolumeClaim, error) {
	obj, err := s.updateStatus("PersistentVolumeClaim", namespace, pvc)
	if err != nil {
		return nil, err
	}

	updatedPVC, ok := obj.(*corev1.PersistentVolumeClaim)
	if !ok {
		return nil, fmt.Errorf("status update returned unexpected type %T", obj)
	}

	return updatedPVC, nil
}

func (s *State) PersistentVolumeClaimDelete(namespace, name string, options metav1.DeleteOptions) error {
	key := KKey{Kind: "PersistentVolumeClaim", Namespace: namespace, Name: name}
	return s.delete(key, options)
}

// Returned value must be treated as read-only.
func (s *State) StatefulSetGet(namespace, name string) (*appsv1.StatefulSet, error) {
	return s.StatefulSetMutGet(namespace, name)
}

func (s *State) StatefulSetMutGet(namespace, name string) (*appsv1.StatefulSet, error) {
	key := KKey{
		Kind:      "StatefulSet",
		Namespace: namespace,
		Name:      name,
	}

	obj, err := s.get(key)
	if err != nil {
		return nil, err
	}

	ss, ok := obj.(*appsv1.StatefulSet)
	if !ok {
		// This should never happen
		return nil, fmt.Errorf("state entry for statefulset %s/%s is not a *v1.StatefulSet", namespace, name)
	}

	return ss, nil
}

// Returned value must be treated as read-only.
func (s *State) StatefulSetList(namespace string, selector labels.Selector) ([]*appsv1.StatefulSet, error) {
	return s.StatefulSetMutList(namespace, selector)
}

func (s *State) StatefulSetMutList(namespace string, selector labels.Selector) ([]*appsv1.StatefulSet, error) {
	objs, err := s.objListBySelector("StatefulSet", namespace, selector)
	if err != nil {
		return nil, err
	}

	sets := make([]*appsv1.StatefulSet, 0, len(objs))
	for _, obj := range objs {
		set, ok := obj.(*appsv1.StatefulSet)
		if !ok {
			return nil, fmt.Errorf("state entry is not a *v1.StatefulSet")
		}
		sets = append(sets, set)
	}

	return sets, nil
}

func (s *State) StatefulSetCreate(namespace string, ss *appsv1.StatefulSet) (*appsv1.StatefulSet, error) {
	obj, err := s.create("StatefulSet", namespace, ss)
	if err != nil {
		return nil, err
	}

	createdSS, ok := obj.(*appsv1.StatefulSet)
	if !ok {
		return nil, fmt.Errorf("create returned unexpected type %T", obj)
	}

	return createdSS, nil
}

func (s *State) StatefulSetUpdate(namespace string, ss *appsv1.StatefulSet) (*appsv1.StatefulSet, error) {
	obj, err := s.update("StatefulSet", namespace, ss)
	if err != nil {
		return nil, err
	}

	updatedSS, ok := obj.(*appsv1.StatefulSet)
	if !ok {
		return nil, fmt.Errorf("update returned unexpected type %T", obj)
	}

	return updatedSS, nil
}

func (s *State) StatefulSetUpdateStatus(namespace string, ss *appsv1.StatefulSet) (*appsv1.StatefulSet, error) {
	obj, err := s.updateStatus("StatefulSet", namespace, ss)
	if err != nil {
		return nil, err
	}

	updatedSS, ok := obj.(*appsv1.StatefulSet)
	if !ok {
		return nil, fmt.Errorf("status update returned unexpected type %T", obj)
	}

	return updatedSS, nil
}

func (s *State) StatefulSetDelete(namespace, name string, options metav1.DeleteOptions) error {
	key := KKey{Kind: "StatefulSet", Namespace: namespace, Name: name}
	return s.delete(key, options)
}

// Returned value must be treated as read-only.
func (s *State) DeploymentGet(namespace, name string) (*appsv1.Deployment, error) {
	return s.DeploymentMutGet(namespace, name)
}

func (s *State) DeploymentMutGet(namespace, name string) (*appsv1.Deployment, error) {
	key := KKey{
		Kind:      "Deployment",
		Namespace: namespace,
		Name:      name,
	}

	obj, err := s.get(key)
	if err != nil {
		return nil, errors.NewNotFound(appsv1.Resource("deployment"), name)
	}

	d, ok := obj.(*appsv1.Deployment)
	if !ok {
		// This should never happen
		return nil, fmt.Errorf("state entry for deployment %s/%s is not a *v1.Deployment", namespace, name)
	}

	return d, nil
}

// Returned value must be treated as read-only.
func (s *State) DeploymentList(namespace string, selector labels.Selector) ([]*appsv1.Deployment, error) {
	return s.DeploymentMutList(namespace, selector)
}

func (s *State) DeploymentMutList(namespace string, selector labels.Selector) ([]*appsv1.Deployment, error) {
	objs, err := s.objListBySelector("Deployment", namespace, selector)
	if err != nil {
		return nil, err
	}

	deployments := make([]*appsv1.Deployment, 0, len(objs))
	for _, obj := range objs {
		d, ok := obj.(*appsv1.Deployment)
		if !ok {
			return nil, fmt.Errorf("state entry is not a *v1.Deployment")
		}
		deployments = append(deployments, d)
	}

	return deployments, nil
}

func (s *State) DeploymentCreate(namespace string, d *appsv1.Deployment) (*appsv1.Deployment, error) {
	obj, err := s.create("Deployment", namespace, d)
	if err != nil {
		return nil, err
	}

	createdDeployment, ok := obj.(*appsv1.Deployment)
	if !ok {
		return nil, fmt.Errorf("create returned unexpected type %T", obj)
	}

	return createdDeployment, nil
}

func (s *State) DeploymentUpdate(namespace string, d *appsv1.Deployment) (*appsv1.Deployment, error) {
	obj, err := s.update("Deployment", namespace, d)
	if err != nil {
		return nil, err
	}

	updatedDeployment, ok := obj.(*appsv1.Deployment)
	if !ok {
		return nil, fmt.Errorf("update returned unexpected type %T", obj)
	}

	return updatedDeployment, nil
}

func (s *State) DeploymentUpdateStatus(namespace string, d *appsv1.Deployment) (*appsv1.Deployment, error) {
	obj, err := s.updateStatus("Deployment", namespace, d)
	if err != nil {
		return nil, err
	}

	updatedDeployment, ok := obj.(*appsv1.Deployment)
	if !ok {
		return nil, fmt.Errorf("status update returned unexpected type %T", obj)
	}

	return updatedDeployment, nil
}

func (s *State) DeploymentDelete(namespace, name string, options metav1.DeleteOptions) error {
	key := KKey{Kind: "Deployment", Namespace: namespace, Name: name}
	return s.delete(key, options)
}
