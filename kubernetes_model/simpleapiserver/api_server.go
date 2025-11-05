package simpleapiserver

import (
	"fmt"
	"math/rand"
	"strconv"
	"sync"
	"time"

	corev1 "k8s.io/api/core/v1"
	"k8s.io/apimachinery/pkg/api/errors"
	"k8s.io/apimachinery/pkg/api/meta"
	metav1 "k8s.io/apimachinery/pkg/apis/meta/v1"
	"k8s.io/apimachinery/pkg/labels"
	"k8s.io/apimachinery/pkg/runtime/schema"
	"k8s.io/apimachinery/pkg/types"
)

// What's missing in this model:
// (1) state validation and transition validation
// (2) update-then-delete: if a to-be-delete object is updated to remove all its finalizers, then it will be deleted
// (3) API options, e.g., CreateOption, DeleteOption.
// (4) object initialization when created
// (5) Patch
// (6) UpdateStatus

type KKey struct {
	Kind      string
	Name      string
	Namespace string
}

type IndexFunc func(obj interface{}) ([]string, error)

type Indexers map[string]IndexFunc

const (
	NamespaceIndex        = "namespace"
	PodControllerUIDIndex = "podControllerUID"
	OrphanPodIndexKey     = "_ORPHAN_POD"
)

type State struct {
	m                      map[KKey]interface{}
	uidCounter             int64
	resourceVersionCounter int64
	indexer                Indexers
}

var (
	stateMu  sync.Mutex
	state    State
	nameRand = rand.New(rand.NewSource(time.Now().UnixNano()))
)

func init() {
	Init()
}

func namespaceIndex(obj interface{}) ([]string, error) {
	metaObj, err := meta.Accessor(obj)
	if err != nil {
		return []string{""}, fmt.Errorf("object has no meta: %v", err)
	}
	return []string{metaObj.GetNamespace()}, nil
}

func podControllerUIDIndex(obj interface{}) ([]string, error) {
	pod, ok := obj.(*corev1.Pod)
	if !ok {
		return nil, nil
	}
	if ref := metav1.GetControllerOf(pod); ref != nil {
		return []string{string(ref.UID)}, nil
	}
	return []string{OrphanPodIndexKeyForNamespace(pod.Namespace)}, nil
}

func Init() {
	stateMu.Lock()
	defer stateMu.Unlock()

	state.m = make(map[KKey]interface{})
	state.uidCounter = 0
	state.resourceVersionCounter = 0
	// indexer is used for filtering, e.g., by object owner
	state.indexer = Indexers{
		NamespaceIndex:        namespaceIndex,
		PodControllerUIDIndex: podControllerUIDIndex,
	}
}

func OrphanPodIndexKeyForNamespace(namespace string) string {
	return OrphanPodIndexKey + "/" + namespace
}

func Get(key KKey) (interface{}, bool) {
	stateMu.Lock()
	defer stateMu.Unlock()

	item, exists := state.m[key]
	return item, exists
}

func List(kind, namespace string) (items []interface{}) {
	stateMu.Lock()
	defer stateMu.Unlock()

	for key, val := range state.m {
		if kind == key.Kind {
			if namespace == metav1.NamespaceAll || namespace == key.Namespace {
				items = append(items, val)
			}
		}
	}
	return items
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

func ListBySelector(kind, namespace string, selector labels.Selector) ([]interface{}, error) {
	return filterByLabelSelector(List(kind, namespace), selector)
}

func Index(kind, indexName string, obj interface{}) ([]interface{}, error) {
	indexFunc, ok := state.indexer[indexName]
	if !ok {
		return nil, fmt.Errorf("index %q does not exist", indexName)
	}

	indexedValues, err := indexFunc(obj)
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
	for _, val := range List(kind, metav1.NamespaceAll) {
		values, err := indexFunc(val)
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

func ByIndex(kind, indexName, indexedValue string) ([]interface{}, error) {
	indexFunc, ok := state.indexer[indexName]
	if !ok {
		return nil, fmt.Errorf("index %q does not exist", indexName)
	}

	var items []interface{}
	for _, val := range List(kind, metav1.NamespaceAll) {
		values, err := indexFunc(val)
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

func randomSuffix(n int) string {
	const randomSuffixChars string = "abcdefghijklmnopqrstuvwxyz0123456789"
	b := make([]byte, n)
	for i := range b {
		b[i] = randomSuffixChars[nameRand.Intn(len(randomSuffixChars))]
	}
	return string(b)
}

func Create(kind, namespace string, obj interface{}) (interface{}, error) {
	metadata, err := meta.Accessor(obj)
	if err != nil {
		return nil, fmt.Errorf("failed to access object metadata: %w", err)
	}

	name := metadata.GetName()
	generateName := metadata.GetGenerateName()

	stateMu.Lock()
	defer stateMu.Unlock()

	if name == "" {
		if generateName == "" {
			return nil, fmt.Errorf("object of kind %q must specify a name or generateName", kind)
		}
		for {
			name = generateName + randomSuffix(5)
			key := KKey{
				Kind:      kind,
				Name:      name,
				Namespace: namespace,
			}
			if _, exists := state.m[key]; !exists {
				metadata.SetName(name)
				break
			}
		}
	}

	key := KKey{
		Kind:      kind,
		Name:      name,
		Namespace: namespace,
	}

	if _, exists := state.m[key]; exists {
		return nil, errors.NewAlreadyExists(schema.GroupResource{Resource: kind}, name)
	}

	state.uidCounter++
	metadata.SetUID(types.UID(fmt.Sprintf("uid-%d", state.uidCounter)))

	state.resourceVersionCounter++
	metadata.SetResourceVersion(strconv.FormatInt(state.resourceVersionCounter, 10))

	state.m[key] = obj

	return obj, nil
}

func Update(kind, namespace string, obj interface{}) (interface{}, error) {
	metadata, err := meta.Accessor(obj)
	if err != nil {
		return nil, fmt.Errorf("failed to access object metadata: %w", err)
	}

	name := metadata.GetName()
	if name == "" {
		return nil, fmt.Errorf("object of kind %q must specify a name for update", kind)
	}

	stateMu.Lock()
	defer stateMu.Unlock()

	key := KKey{
		Kind:      kind,
		Name:      name,
		Namespace: namespace,
	}

	existingObj, exists := state.m[key]
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

	state.resourceVersionCounter++
	metadata.SetResourceVersion(strconv.FormatInt(state.resourceVersionCounter, 10))

	state.m[key] = obj

	return obj, nil
}

func Delete(key KKey) error {
	stateMu.Lock()
	defer stateMu.Unlock()

	obj, exists := state.m[key]
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
			state.resourceVersionCounter++
			metadata.SetResourceVersion(strconv.FormatInt(state.resourceVersionCounter, 10))
		}
		state.m[key] = obj
		return nil
	}

	delete(state.m, key)
	return nil
}

func PodGet(namespace, name string) (*corev1.Pod, error) {
	key := KKey{
		Kind:      "Pod",
		Namespace: namespace,
		Name:      name,
	}

	obj, exists := Get(key)
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

func PodDelete(namespace, name string) error {
	key := KKey{
		Kind:      "Pod",
		Namespace: namespace,
		Name:      name,
	}

	return Delete(key)
}
