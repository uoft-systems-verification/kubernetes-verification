package model

import (
	"testing"

	corev1 "k8s.io/api/core/v1"
	apierrors "k8s.io/apimachinery/pkg/api/errors"
	metav1 "k8s.io/apimachinery/pkg/apis/meta/v1"
	"k8s.io/apimachinery/pkg/labels"
	"k8s.io/apimachinery/pkg/types"
)

func resetStateForTest(t *testing.T) {
	t.Helper()

	stateMu.Lock()
	defer stateMu.Unlock()

	state.m = make(map[KKey]interface{})
	state.uidCounter = 0
	state.resourceVersionCounter = 0
}

func TestCreateGetAndList(t *testing.T) {
	resetStateForTest(t)

	pod := &corev1.Pod{
		ObjectMeta: metav1.ObjectMeta{
			Name:      "pod-1",
			Namespace: "default",
			Labels:    map[string]string{"app": "demo"},
		},
	}

	obj, err := Create("Pod", "default", pod)
	if err != nil {
		t.Fatalf("Create returned error: %v", err)
	}
	created := obj.(*corev1.Pod)
	if created.UID == "" {
		t.Fatalf("expected UID to be set on created pod")
	}
	if created.ResourceVersion != "1" {
		t.Fatalf("expected resourceVersion 1, got %s", created.ResourceVersion)
	}

	key := KKey{Kind: "Pod", Namespace: "default", Name: "pod-1"}
	stored, exists := Get(key)
	if !exists {
		t.Fatalf("expected pod to exist in state")
	}
	if stored != created {
		t.Fatalf("Get returned different object pointer")
	}

	list := List("Pod", "default")
	if len(list) != 1 {
		t.Fatalf("expected 1 pod in list, got %d", len(list))
	}
	if list[0] != created {
		t.Fatalf("List returned unexpected object")
	}
}

func TestListBySelector(t *testing.T) {
	resetStateForTest(t)

	makePod := func(name string, labels map[string]string) *corev1.Pod {
		return &corev1.Pod{
			ObjectMeta: metav1.ObjectMeta{
				Name:      name,
				Namespace: "default",
				Labels:    labels,
			},
		}
	}

	if _, err := Create("Pod", "default", makePod("pod-a", map[string]string{"app": "demo", "tier": "backend"})); err != nil {
		t.Fatalf("Create returned error: %v", err)
	}
	if _, err := Create("Pod", "default", makePod("pod-b", map[string]string{"app": "demo", "tier": "frontend"})); err != nil {
		t.Fatalf("Create returned error: %v", err)
	}
	if _, err := Create("Pod", "default", makePod("pod-c", map[string]string{"app": "other"})); err != nil {
		t.Fatalf("Create returned error: %v", err)
	}

	selector, err := labels.Parse("app=demo,tier=backend")
	if err != nil {
		t.Fatalf("failed to parse selector: %v", err)
	}
	items, err := ListBySelector("Pod", "default", selector)
	if err != nil {
		t.Fatalf("ListBySelector returned error: %v", err)
	}
	if len(items) != 1 {
		t.Fatalf("expected exactly 1 pod matching selector, got %d", len(items))
	}
	if pod := items[0].(*corev1.Pod); pod.Name != "pod-a" {
		t.Fatalf("expected pod-a, got %s", pod.Name)
	}

	selector, err = labels.Parse("app=demo")
	if err != nil {
		t.Fatalf("failed to parse selector: %v", err)
	}
	items, err = ListBySelector("Pod", "default", selector)
	if err != nil {
		t.Fatalf("ListBySelector returned error: %v", err)
	}
	if len(items) != 2 {
		t.Fatalf("expected 2 pods with app=demo, got %d", len(items))
	}
	found := map[string]bool{}
	for _, item := range items {
		found[item.(*corev1.Pod).Name] = true
	}
	if !found["pod-a"] || !found["pod-b"] {
		t.Fatalf("expected pods pod-a and pod-b, got %#v", found)
	}
}

func TestCreateWithGenerateName(t *testing.T) {
	resetStateForTest(t)

	pod := &corev1.Pod{
		ObjectMeta: metav1.ObjectMeta{
			GenerateName: "generated-",
			Namespace:    "default",
		},
	}

	obj, err := Create("Pod", "default", pod)
	if err != nil {
		t.Fatalf("Create returned error: %v", err)
	}
	created := obj.(*corev1.Pod)
	if created.Name == "" {
		t.Fatalf("expected generated name to be assigned")
	}
	if got, want := created.Name[:len("generated-")], "generated-"; got != want {
		t.Fatalf("expected generated name prefix %q, got %q", want, got)
	}
}

func TestUpdate(t *testing.T) {
	resetStateForTest(t)

	pod := &corev1.Pod{
		ObjectMeta: metav1.ObjectMeta{
			Name:      "pod-1",
			Namespace: "default",
			Labels:    map[string]string{"app": "demo"},
		},
	}
	obj, err := Create("Pod", "default", pod)
	if err != nil {
		t.Fatalf("Create returned error: %v", err)
	}
	created := obj.(*corev1.Pod)

	updated := created.DeepCopy()
	updated.Labels["version"] = "v2"

	obj, err = Update("Pod", "default", updated)
	if err != nil {
		t.Fatalf("Update returned error: %v", err)
	}
	updatedPod := obj.(*corev1.Pod)
	if updatedPod.ResourceVersion != "2" {
		t.Fatalf("expected resourceVersion 2 after update, got %s", updatedPod.ResourceVersion)
	}
	if updatedPod.Labels["version"] != "v2" {
		t.Fatalf("expected updated label to be persisted")
	}
}

func TestUpdateConflict(t *testing.T) {
	resetStateForTest(t)

	pod := &corev1.Pod{
		ObjectMeta: metav1.ObjectMeta{
			Name:      "pod-1",
			Namespace: "default",
		},
	}
	obj, err := Create("Pod", "default", pod)
	if err != nil {
		t.Fatalf("Create returned error: %v", err)
	}
	created := obj.(*corev1.Pod)

	conflicting := created.DeepCopy()
	conflicting.SetResourceVersion("999")

	_, err = Update("Pod", "default", conflicting)
	if err == nil {
		t.Fatalf("expected conflict error on outdated update")
	}
	if !apierrors.IsConflict(err) {
		t.Fatalf("expected conflict error, got %v", err)
	}
}

func TestDeleteWithoutFinalizers(t *testing.T) {
	resetStateForTest(t)

	pod := &corev1.Pod{
		ObjectMeta: metav1.ObjectMeta{
			Name:      "pod-1",
			Namespace: "default",
		},
	}
	if _, err := Create("Pod", "default", pod); err != nil {
		t.Fatalf("Create returned error: %v", err)
	}

	key := KKey{Kind: "Pod", Namespace: "default", Name: "pod-1"}
	if err := Delete(key); err != nil {
		t.Fatalf("Delete returned error: %v", err)
	}

	if _, exists := Get(key); exists {
		t.Fatalf("expected pod to be removed after delete without finalizers")
	}
}

func TestDeleteWithFinalizers(t *testing.T) {
	resetStateForTest(t)

	pod := &corev1.Pod{
		ObjectMeta: metav1.ObjectMeta{
			Name:       "pod-1",
			Namespace:  "default",
			Finalizers: []string{"cleanup"},
		},
	}
	obj, err := Create("Pod", "default", pod)
	if err != nil {
		t.Fatalf("Create returned error: %v", err)
	}
	created := obj.(*corev1.Pod)
	originalRV := created.ResourceVersion

	key := KKey{Kind: "Pod", Namespace: "default", Name: "pod-1"}
	if err := Delete(key); err != nil {
		t.Fatalf("Delete returned error: %v", err)
	}

	stored, exists := Get(key)
	if !exists {
		t.Fatalf("expected pod to remain due to finalizer")
	}
	storedPod := stored.(*corev1.Pod)
	if storedPod.DeletionTimestamp == nil {
		t.Fatalf("expected deletion timestamp to be set when finalizers present")
	}
	if storedPod.ResourceVersion == originalRV {
		t.Fatalf("expected resourceVersion to change after delete with finalizers")
	}
}

func TestIndexAndByIndexWithNamespace(t *testing.T) {
	resetStateForTest(t)

	makePod := func(name, namespace string) *corev1.Pod {
		return &corev1.Pod{
			ObjectMeta: metav1.ObjectMeta{
				Name:      name,
				Namespace: namespace,
			},
		}
	}

	if _, err := Create("Pod", "default", makePod("pod-a", "default")); err != nil {
		t.Fatalf("Create returned error: %v", err)
	}
	if _, err := Create("Pod", "kube-system", makePod("pod-b", "kube-system")); err != nil {
		t.Fatalf("Create returned error: %v", err)
	}

	seed := &metav1.ObjectMeta{Namespace: "default"}
	items, err := Index("Pod", NamespaceIndex, seed)
	if err != nil {
		t.Fatalf("Index returned error: %v", err)
	}
	if len(items) != 1 {
		t.Fatalf("expected exactly 1 pod in index result, got %d", len(items))
	}
	pod := items[0].(*corev1.Pod)
	if pod.Namespace != "default" {
		t.Fatalf("expected pod from default namespace, got %s", pod.Namespace)
	}

	byIndexItems, err := ByIndex("Pod", NamespaceIndex, "kube-system")
	if err != nil {
		t.Fatalf("ByIndex returned error: %v", err)
	}
	if len(byIndexItems) != 1 {
		t.Fatalf("expected exactly 1 pod from kube-system, got %d", len(byIndexItems))
	}
	if kubePod := byIndexItems[0].(*corev1.Pod); kubePod.Namespace != "kube-system" {
		t.Fatalf("expected kube-system pod, got %s", kubePod.Namespace)
	}
}

func TestIndexAndByIndexWithControllerUID(t *testing.T) {
	resetStateForTest(t)

	controllerUID := types.UID("controller-uid")
	controllerUID2 := types.UID("controller-uid2")
	controller := true
	ownerRef := metav1.OwnerReference{
		UID:        controllerUID,
		Controller: &controller,
	}
	ownerRef2 := metav1.OwnerReference{
		UID:        controllerUID2,
		Controller: &controller,
	}
	ownerRef3 := metav1.OwnerReference{
		UID: controllerUID2,
	}
	podWithControllerOwner := &corev1.Pod{
		ObjectMeta: metav1.ObjectMeta{
			Name:            "pod-controller-owned",
			Namespace:       "default",
			OwnerReferences: []metav1.OwnerReference{ownerRef},
		},
	}
	podWithControllerOwner2 := &corev1.Pod{
		ObjectMeta: metav1.ObjectMeta{
			Name:            "pod-controller-owned2",
			Namespace:       "default",
			OwnerReferences: []metav1.OwnerReference{ownerRef2},
		},
	}
	podWithOwner := &corev1.Pod{
		ObjectMeta: metav1.ObjectMeta{
			Name:            "pod-owned",
			Namespace:       "default",
			OwnerReferences: []metav1.OwnerReference{ownerRef3},
		},
	}
	podOrphan := &corev1.Pod{
		ObjectMeta: metav1.ObjectMeta{
			Name:      "pod-orphan",
			Namespace: "default",
		},
	}

	if _, err := Create("Pod", "default", podWithControllerOwner); err != nil {
		t.Fatalf("Create returned error: %v", err)
	}
	if _, err := Create("Pod", "default", podWithControllerOwner2); err != nil {
		t.Fatalf("Create returned error: %v", err)
	}
	if _, err := Create("Pod", "default", podWithOwner); err != nil {
		t.Fatalf("Create returned error: %v", err)
	}
	if _, err := Create("Pod", "default", podOrphan); err != nil {
		t.Fatalf("Create returned error: %v", err)
	}

	items, err := Index("Pod", PodControllerUIDIndex, podWithControllerOwner)
	if err != nil {
		t.Fatalf("Index returned error: %v", err)
	}
	if len(items) != 1 {
		t.Fatalf("expected 1 pod owned by controller, got %d", len(items))
	}
	if pod := items[0].(*corev1.Pod); pod.Name != "pod-controller-owned" {
		t.Fatalf("expected pod-owned, got %s", pod.Name)
	}

	items, err = Index("Pod", PodControllerUIDIndex, podWithControllerOwner2)
	if err != nil {
		t.Fatalf("Index returned error: %v", err)
	}
	if len(items) != 1 {
		t.Fatalf("expected 1 pod owned by controller2, got %d", len(items))
	}
	if pod := items[0].(*corev1.Pod); pod.Name != "pod-controller-owned2" {
		t.Fatalf("expected pod-owned, got %s", pod.Name)
	}

	items, err = Index("Pod", PodControllerUIDIndex, podWithOwner)
	if err != nil {
		t.Fatalf("Index returned error: %v", err)
	}
	if len(items) != 2 {
		t.Fatalf("expected 2 orphan pods, got %d", len(items))
	}
	found := map[string]bool{}
	for _, item := range items {
		found[item.(*corev1.Pod).Name] = true
	}
	if !found["pod-orphan"] || !found["pod-owned"] {
		t.Fatalf("expected pods pod-orphan and pod-owned, got names %#v", found)
	}

	items, err = Index("Pod", PodControllerUIDIndex, podOrphan)
	if err != nil {
		t.Fatalf("Index returned error: %v", err)
	}
	if len(items) != 2 {
		t.Fatalf("expected 2 orphan pods, got %d", len(items))
	}
	found = map[string]bool{}
	for _, item := range items {
		found[item.(*corev1.Pod).Name] = true
	}
	if !found["pod-orphan"] || !found["pod-owned"] {
		t.Fatalf("expected pods pod-orphan and pod-owned, got names %#v", found)
	}

	byOwner, err := ByIndex("Pod", PodControllerUIDIndex, string(controllerUID))
	if err != nil {
		t.Fatalf("ByIndex returned error: %v", err)
	}
	if len(byOwner) != 1 || byOwner[0].(*corev1.Pod).Name != "pod-controller-owned" {
		t.Fatalf("ByIndex should return pod-owned, got %#v", byOwner)
	}

	orphanKey := OrphanPodIndexKeyForNamespace("default")
	orphanPods, err := ByIndex("Pod", PodControllerUIDIndex, orphanKey)
	if err != nil {
		t.Fatalf("ByIndex returned error: %v", err)
	}
	if len(orphanPods) != 2 {
		t.Fatalf("expected 2 pods for orphan index, got %d", len(orphanPods))
	}

	found = map[string]bool{}
	for _, item := range orphanPods {
		found[item.(*corev1.Pod).Name] = true
	}
	if !found["pod-orphan"] || !found["pod-owned"] {
		t.Fatalf("expected pods pod-orphan and pod-owned, got %#v", orphanPods)
	}
}
