package apimodel

import (
	"reflect"
	"testing"

	appsv1 "k8s.io/api/apps/v1"
	corev1 "k8s.io/api/core/v1"
	metav1 "k8s.io/apimachinery/pkg/apis/meta/v1"
)

const daemonSetTemplateGeneration = "deprecated.daemonset.template.generation"

func daemonSetTestInput() *appsv1.DaemonSet {
	return &appsv1.DaemonSet{
		ObjectMeta: metav1.ObjectMeta{Name: "daemon", Namespace: "default"},
		Spec: appsv1.DaemonSetSpec{
			Selector: &metav1.LabelSelector{MatchLabels: map[string]string{"app": "daemon"}},
			Template: corev1.PodTemplateSpec{
				ObjectMeta: metav1.ObjectMeta{Labels: map[string]string{"app": "daemon"}},
				Spec:       corev1.PodSpec{Containers: []corev1.Container{{Name: "worker", Image: "worker:v1"}}},
			},
		},
		Status: appsv1.DaemonSetStatus{NumberReady: 99},
	}
}

func TestDaemonSetObjectLifecycle(t *testing.T) {
	s := NewState()
	input := daemonSetTestInput()
	obj, err := s.create("DaemonSet", "default", input)
	if err != nil {
		t.Fatal(err)
	}
	created := obj.(*appsv1.DaemonSet)
	rolling := created.Spec.UpdateStrategy.RollingUpdate
	if created.Generation != 1 || created.Annotations[daemonSetTemplateGeneration] != "1" ||
		!reflect.DeepEqual(created.Status, appsv1.DaemonSetStatus{}) {
		t.Fatalf("create preparation: generation=%d annotations=%v status=%+v", created.Generation, created.Annotations, created.Status)
	}
	if created.Spec.UpdateStrategy.Type != appsv1.RollingUpdateDaemonSetStrategyType || rolling == nil ||
		rolling.MaxUnavailable == nil || rolling.MaxUnavailable.IntVal != 1 ||
		rolling.MaxSurge == nil || rolling.MaxSurge.IntVal != 0 ||
		created.Spec.RevisionHistoryLimit == nil || *created.Spec.RevisionHistoryLimit != 10 {
		t.Fatalf("missing DaemonSet defaults: %+v", created.Spec)
	}
	if input.Status.NumberReady != 99 || input.Spec.UpdateStrategy.Type != "" || input.UID != "" {
		t.Fatal("create mutated the caller's object")
	}

	request := created.DeepCopy()
	request.ResourceVersion = "" // The DaemonSet strategy allows unconditional updates.
	request.Spec.Template.Spec.Containers[0].Image = "worker:v2"
	request.Status.NumberReady = 42
	obj, err = s.update("DaemonSet", "default", request)
	if err != nil {
		t.Fatal(err)
	}
	updated := obj.(*appsv1.DaemonSet)
	if updated.Generation != 2 || updated.Annotations[daemonSetTemplateGeneration] != "2" || updated.Status.NumberReady != 0 {
		t.Fatalf("ordinary update preparation: generation=%d annotations=%v status=%+v", updated.Generation, updated.Annotations, updated.Status)
	}

	request = updated.DeepCopy()
	request.Spec.MinReadySeconds = 999
	request.Status.CurrentNumberScheduled = 3
	request.Status.DesiredNumberScheduled = 3
	request.Status.NumberReady = 2
	count := int32(1)
	request.Status.CollisionCount = &count
	obj, err = s.updateStatus("DaemonSet", "default", request)
	if err != nil {
		t.Fatal(err)
	}
	statusUpdated := obj.(*appsv1.DaemonSet)
	if statusUpdated.Spec.MinReadySeconds != updated.Spec.MinReadySeconds || statusUpdated.Status.NumberReady != 2 ||
		statusUpdated.Generation != updated.Generation || statusUpdated.Annotations[daemonSetTemplateGeneration] != "2" {
		t.Fatalf("status update did not preserve spec/generation: %+v", statusUpdated)
	}

	request = statusUpdated.DeepCopy()
	zero := int32(0)
	request.Status.CollisionCount = &zero
	if _, err := s.updateStatus("DaemonSet", "default", request); err == nil {
		t.Fatal("accepted a decreasing collision count")
	}
	request = statusUpdated.DeepCopy()
	request.Spec.Selector.MatchLabels["app"] = "other"
	request.Spec.Template.Labels["app"] = "other"
	if _, err := s.update("DaemonSet", "default", request); err == nil {
		t.Fatal("accepted a selector change")
	}

	key := KKey{Kind: "DaemonSet", Namespace: "default", Name: "daemon"}
	got, err := s.get(key)
	if err != nil {
		t.Fatal(err)
	}
	got.(*appsv1.DaemonSet).Spec.Template.Labels["app"] = "mutated-copy"
	again, err := s.get(key)
	if err != nil || again.(*appsv1.DaemonSet).Spec.Template.Labels["app"] != "daemon" {
		t.Fatal("get did not preserve independent stored data", err)
	}
	if err := s.delete(key, metav1.DeleteOptions{}); err != nil {
		t.Fatal(err)
	}
}

func TestDaemonSetRejectsMalformedTemplateGeneration(t *testing.T) {
	input := daemonSetTestInput()
	input.Annotations = map[string]string{daemonSetTemplateGeneration: "not-an-int64"}
	if _, err := NewState().create("DaemonSet", "default", input); err == nil {
		t.Fatal("accepted a malformed template-generation annotation")
	}
}
