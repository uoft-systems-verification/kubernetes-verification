package simple

import (
	"fmt"
	"math/rand"
	"strconv"
	"sync"
	"time"

	appsv1 "k8s.io/api/apps/v1"
	corev1 "k8s.io/api/core/v1"
	v1 "k8s.io/api/core/v1"
	"k8s.io/apimachinery/pkg/api/errors"
	"k8s.io/apimachinery/pkg/api/meta"
	metav1 "k8s.io/apimachinery/pkg/apis/meta/v1"
	"k8s.io/apimachinery/pkg/labels"
	"k8s.io/apimachinery/pkg/runtime/schema"
	"k8s.io/apimachinery/pkg/types"
	"k8s.io/apimachinery/pkg/util/uuid"
	"k8s.io/kubernetes/pkg/controller"
)

// What's missing in this model:
//
// (1) UpdateStatus
//
// (2) Patch (JSON Patch, Merge Patch, Strategic Merge Patch)
//
// (3) Transition validation during Update: validate that state transitions are valid (e.g., Phase changes)
//
// (4) API options, e.g., CreateOption / UpdateOptions
//     Reference: https://github.com/kubernetes/kubernetes/blob/release-1.34/staging/src/k8s.io/apimachinery/pkg/apis/meta/v1/types.go#L579
//
// (5) Admission webhooks and admission plugins
//     - Validating webhooks: https://github.com/kubernetes/kubernetes/blob/release-1.34/staging/src/k8s.io/apiserver/pkg/admission/plugin/webhook/validating/plugin.go
//     - Mutating webhooks: https://github.com/kubernetes/kubernetes/blob/release-1.34/staging/src/k8s.io/apiserver/pkg/admission/plugin/webhook/mutating/plugin.go
//     - Built-in plugins: https://github.com/kubernetes/kubernetes/blob/release-1.34/pkg/kubeapiserver/admission/exclusion/resources.go
//
// (6) Warnings collection - Collects warnings during create/update (non-fatal issues)
//     Reference: https://github.com/kubernetes/kubernetes/blob/release-1.34/staging/src/k8s.io/apiserver/pkg/registry/rest/create.go#L133 (WarningsOnCreate)
//
// (7) BeginCreate/FinishCreate/AfterCreate hooks
//     Reference: https://github.com/kubernetes/kubernetes/blob/release-1.34/staging/src/k8s.io/apiserver/pkg/registry/generic/registry/store.go#L490-L499
//     Reference: https://github.com/kubernetes/kubernetes/blob/release-1.34/staging/src/k8s.io/apiserver/pkg/registry/generic/registry/store.go#L551-L553

type State struct {
	m                      map[KKey]interface{}
	usedUID                map[types.UID]struct{}
	usedRV                 map[string]struct{}
	resourceVersionCounter int64
	mu                     *sync.Mutex
}

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
	case *appsv1.ReplicaSet:
		return o.DeepCopy()
	default:
		panic(fmt.Sprintf("copyObject: unsupported type %T", obj))
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

func (s *State) objGet(key KKey) (interface{}, bool) {
	s.mu.Lock()
	defer s.mu.Unlock()

	item, exists := s.m[key]
	if exists {
		return deepCopy(item), exists
	} else {
		return nil, exists
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

// objCreate is the simple implementation that doesn't perform validation
// or resource-specific initialization.
func (s *State) objCreate(kind, namespace string, obj interface{}) (interface{}, error) {
	s.mu.Lock()
	defer s.mu.Unlock()

	objCopy := deepCopy(obj)
	metadata, err := meta.Accessor(objCopy)
	if err != nil {
		return nil, fmt.Errorf("failed to access object metadata: %w", err)
	}

	metadata.SetNamespace(namespace)

	name := metadata.GetName()
	generateName := metadata.GetGenerateName()

	if name == "" {
		if generateName == "" {
			return nil, fmt.Errorf("object of kind %q must specify a name or generateName", kind)
		}
		name = s.generateNewName(kind, namespace, generateName)
		metadata.SetName(name)
	}

	key := KKey{
		Kind:      kind,
		Name:      name,
		Namespace: namespace,
	}

	if _, exists := s.m[key]; exists {
		return nil, errors.NewAlreadyExists(schema.GroupResource{Resource: kind}, name)
	}

	newUID := s.generateNewUIDAndUpdate()
	metadata.SetUID(types.UID(newUID))

	s.resourceVersionCounter++
	metadata.SetResourceVersion(strconv.FormatInt(s.resourceVersionCounter, 10))

	s.m[key] = objCopy
	return deepCopy(objCopy), nil
}

func (s *State) objUpdate(kind, namespace string, obj interface{}) (interface{}, error) {
	s.mu.Lock()
	defer s.mu.Unlock()

	objCopy := deepCopy(obj)
	metadata, err := meta.Accessor(objCopy)
	if err != nil {
		return nil, fmt.Errorf("failed to access object metadata: %w", err)
	}

	name := metadata.GetName()
	if name == "" {
		return nil, fmt.Errorf("object of kind %q must specify a name for update", kind)
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

	existingMetadata, err := meta.Accessor(existingObj)
	if err != nil {
		return nil, fmt.Errorf("failed to access existing object metadata: %w", err)
	}

	uid := metadata.GetUID()
	existingUid := existingMetadata.GetUID()
	if uid != existingUid {
		return nil, errors.NewConflict(schema.GroupResource{Resource: kind}, name, fmt.Errorf("UID mismatch: expected %q, got %q", existingUid, uid))
	}

	rv := metadata.GetResourceVersion()
	existingRv := existingMetadata.GetResourceVersion()
	if metadata.GetResourceVersion() != existingMetadata.GetResourceVersion() {
		return nil, errors.NewConflict(schema.GroupResource{Resource: kind}, name, fmt.Errorf("resourceVersion mismatch: expected %q, got %q", existingRv, rv))
	}

	s.resourceVersionCounter++
	metadata.SetResourceVersion(strconv.FormatInt(s.resourceVersionCounter, 10))

	s.m[key] = objCopy
	return deepCopy(objCopy), nil
}

func (s *State) objDelete(key KKey) error {
	s.mu.Lock()
	defer s.mu.Unlock()

	obj, exists := s.m[key]
	if !exists {
		return errors.NewNotFound(schema.GroupResource{Resource: key.Kind}, key.Name)
	}

	metadata, err := meta.Accessor(obj)
	if err != nil {
		return fmt.Errorf("failed to access object metadata: %w", err)
	}

	if len(metadata.GetFinalizers()) > 0 {
		if metadata.GetDeletionTimestamp() == nil {
			now := metav1.Now()
			metadata.SetDeletionTimestamp(&now)
			s.resourceVersionCounter++
			metadata.SetResourceVersion(strconv.FormatInt(s.resourceVersionCounter, 10))
		}
		return nil
	}

	delete(s.m, key)
	return nil
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

	obj, exists := s.objGet(key)
	if !exists {
		return nil, errors.NewNotFound(corev1.Resource("pod"), name)
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
	obj, err := s.objCreate("Pod", namespace, pod)
	if err != nil {
		return nil, err
	}

	pod, ok := obj.(*corev1.Pod)
	if !ok {
		// This should never happen
		return nil, fmt.Errorf("state entry is not a *v1.Pod")
	}

	return pod, err
}

func (s *State) PodUpdate(namespace string, pod *corev1.Pod) (*corev1.Pod, error) {
	obj, err := s.objUpdate("Pod", namespace, pod)
	if err != nil {
		return nil, err
	}

	pod, ok := obj.(*corev1.Pod)
	if !ok {
		// This should never happen
		return nil, fmt.Errorf("state entry is not a *v1.Pod")
	}

	return pod, err
}

func (s *State) PodDelete(namespace, name string) error {
	key := KKey{
		Kind:      "Pod",
		Namespace: namespace,
		Name:      name,
	}

	return s.objDelete(key)
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

	obj, exists := s.objGet(key)
	if !exists {
		return nil, errors.NewNotFound(appsv1.Resource("replicaset"), name)
	}

	rs, ok := obj.(*appsv1.ReplicaSet)
	if !ok {
		// This should never happen
		return nil, fmt.Errorf("state entry for replicaset %s/%s is not a *v1.ReplicaSet", namespace, name)
	}

	return rs, nil
}
