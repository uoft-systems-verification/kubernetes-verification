package simplereplicaset

import (
	"fmt"
	"kubernetes_model/apimodel"

	apps "k8s.io/api/apps/v1"
	v1 "k8s.io/api/core/v1"
	apierrors "k8s.io/apimachinery/pkg/api/errors"
	metav1 "k8s.io/apimachinery/pkg/apis/meta/v1"
	"k8s.io/apimachinery/pkg/labels"
	"k8s.io/kubernetes/pkg/controller"
)

// A highly simplified replicaset controller. The following features are removed:
// * adoption and release
// * managing status
// * concurrent creation/deletion
// * sort before deletion

func CreatePod(namespace string, template *v1.PodTemplateSpec, controllerObject *apps.ReplicaSet, controllerRef *metav1.OwnerReference) error {
	pod, err := controller.GetPodFromTemplate(template, controllerObject, controllerRef)
	if err != nil {
		return err
	}
	if len(labels.Set(pod.Labels)) == 0 {
		return fmt.Errorf("unable to create pods, no labels")
	}
	_, err = apimodel.PodCreate(namespace, pod)
	return err
}

func FilterPodsByOwner(owner *metav1.ObjectMeta) ([]*v1.Pod, error) {
	result := []*v1.Pod{}
	pods, err := apimodel.ByIndex("Pod", apimodel.PodControllerUIDIndex, string(owner.UID))
	if err != nil {
		return nil, err
	}
	for _, obj := range pods {
		pod, ok := obj.(*v1.Pod)
		if !ok {
			continue
		}
		result = append(result, pod)
	}
	return result, nil
}

func IsPodActive(p *v1.Pod) bool {
	return v1.PodSucceeded != p.Status.Phase &&
		v1.PodFailed != p.Status.Phase &&
		p.DeletionTimestamp == nil
}

func FilterActivePods(pods []*v1.Pod) []*v1.Pod {
	var result []*v1.Pod
	for _, p := range pods {
		if IsPodActive(p) {
			result = append(result, p)
		}
	}
	return result
}

func manageReplicas(activePods []*v1.Pod, rs *apps.ReplicaSet) error {
	diff := len(activePods) - int(*(rs.Spec.Replicas))
	_, err := controller.KeyFunc(rs)
	if err != nil {
		return nil
	}
	if diff < 0 {
		diff *= -1
		for i := 0; i < diff; i++ {
			err := CreatePod(rs.Namespace, &rs.Spec.Template, rs, metav1.NewControllerRef(rs, apps.SchemeGroupVersion.WithKind("ReplicaSet")))
			if err != nil {
				return err
			}
		}
	} else if diff > 0 {
		podsToDelete := activePods[:diff]
		for _, pod := range podsToDelete {
			if err := apimodel.PodDelete(rs.Namespace, pod.Name); err != nil {
				if !apierrors.IsNotFound(err) {
					return err
				}
			}
		}
	}

	return nil
}

func syncReplicaSet(namespace, name string) error {
	rs, err := apimodel.ReplicaSetGet(namespace, name)
	if apierrors.IsNotFound(err) {
		return nil
	}
	if err != nil {
		return err
	}

	allRSPods, err := FilterPodsByOwner(&rs.ObjectMeta)
	if err != nil {
		return err
	}

	allActivePods := FilterActivePods(allRSPods)

	var manageReplicasErr error
	if rs.DeletionTimestamp == nil {
		manageReplicasErr = manageReplicas(allActivePods, rs)
	}

	return manageReplicasErr
}
