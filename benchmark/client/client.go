package client

import (
	"kubernetes_model/apimodel"

	corev1 "k8s.io/api/core/v1"
	metav1 "k8s.io/apimachinery/pkg/apis/meta/v1"
)

func CreateThenDeletePods(state *apimodel.State, pods []*corev1.Pod) error {
	createdPodKeys := make([]apimodel.KKey, 0, len(pods))
	for _, pod := range pods {
		podToCreate := pod.DeepCopy()
		podToCreate.Name = ""

		createdPod, err := state.PodCreate(podToCreate.Namespace, podToCreate)
		if err != nil {
			return err
		}
		createdPodKeys = append(createdPodKeys, apimodel.KKey{
			Kind:      "Pod",
			Namespace: createdPod.Namespace,
			Name:      createdPod.Name,
		})
	}

	createdPods := make([]*corev1.Pod, 0, len(createdPodKeys))
	for _, key := range createdPodKeys {
		pod, err := state.PodGet(key.Namespace, key.Name)
		if err != nil {
			return err
		}
		createdPods = append(createdPods, pod)
	}

	for _, pod := range createdPods {
		uid := pod.UID
		resourceVersion := pod.ResourceVersion
		options := metav1.DeleteOptions{
			Preconditions: &metav1.Preconditions{
				UID:             &uid,
				ResourceVersion: &resourceVersion,
			},
		}
		if err := state.PodDelete(pod.Namespace, pod.Name, options); err != nil {
			return err
		}
	}

	return nil
}
