package statefulset

import (
	"kubernetes_model/apimodel"
	"reflect"
	"testing"

	"gopkg.in/inf.v0"
	appsv1 "k8s.io/api/apps/v1"
	corev1 "k8s.io/api/core/v1"
	"k8s.io/apimachinery/pkg/api/resource"
	metav1 "k8s.io/apimachinery/pkg/apis/meta/v1"
)

func TestPodSpecMatchesCreatedPod(t *testing.T) {
	set := &appsv1.StatefulSet{
		ObjectMeta: metav1.ObjectMeta{Name: "example", Namespace: "test", UID: "set-uid"},
		Spec: appsv1.StatefulSetSpec{
			ServiceName: "example-service",
			Selector:    &metav1.LabelSelector{MatchLabels: map[string]string{"app": "example"}},
			Template: corev1.PodTemplateSpec{
				ObjectMeta: metav1.ObjectMeta{Labels: map[string]string{"app": "example"}},
				Spec: corev1.PodSpec{
					SchedulingGates: []corev1.PodSchedulingGate{{Name: "example"}},
					Containers: []corev1.Container{{Name: "main", Image: "example:v1",
						Resources: corev1.ResourceRequirements{Requests: corev1.ResourceList{
							corev1.ResourceMemory: *resource.NewDecimalQuantity(*inf.NewDec(0, 0), resource.DecimalSI),
						}},
					}},
					Affinity: &corev1.Affinity{PodAffinity: &corev1.PodAffinity{
						RequiredDuringSchedulingIgnoredDuringExecution: []corev1.PodAffinityTerm{{
							TopologyKey:    "kubernetes.io/hostname",
							LabelSelector:  &metav1.LabelSelector{},
							MatchLabelKeys: []string{"app"},
						}},
					}},
				},
			},
		},
	}
	request, err := newStatefulSetPod(set, 0)
	if err != nil {
		t.Fatal(err)
	}
	pod, err := apimodel.NewState().PodCreate(set.Namespace, request)
	if err != nil {
		t.Fatal(err)
	}
	if reflect.DeepEqual(pod.Spec, request.Spec) {
		t.Fatal("test requires create-time defaults to change the spec")
	}
	setBefore, podBefore := set.DeepCopy(), pod.DeepCopy()
	if !podSpecMatches(set, pod) || !podSpecMatches(set, pod) {
		t.Fatal("a freshly created Pod must match, including after repeated checks")
	}
	if !reflect.DeepEqual(set, setBefore) || !reflect.DeepEqual(pod, podBefore) {
		t.Fatal("checking a Pod changed the template or the stored Pod")
	}
	bufferOnly := pod.DeepCopy()
	quantity := bufferOnly.Spec.Containers[0].Resources.Requests[corev1.ResourceMemory]
	quantity.AsDec().SetUnscaled(1)
	quantity.AsDec().SetUnscaled(0)
	bufferOnly.Spec.Containers[0].Resources.Requests[corev1.ResourceMemory] = quantity
	if reflect.DeepEqual(bufferOnly.Spec, pod.Spec) {
		t.Fatal("test requires distinct internal representations of the same quantity")
	}
	if !podSpecMatches(set, bufferOnly) {
		t.Fatal("an empty internal quantity buffer must not make a Pod outdated")
	}
	if quantity.AsDec().UnscaledBig().Bits() == nil {
		t.Fatal("checking a Pod changed its internal quantity buffer")
	}
	metadataOnly := set.DeepCopy()
	metadataOnly.Spec.Template.Finalizers = []string{"bad finalizer"}
	if !podSpecMatches(metadataOnly, pod) {
		t.Fatal("spec matching must not validate unrelated template finalizers")
	}
	changed := pod.DeepCopy()
	changed.Spec.Containers[0].Image = "example:v2"
	if podSpecMatches(set, changed) {
		t.Fatal("a changed nested container field must not match")
	}
}
