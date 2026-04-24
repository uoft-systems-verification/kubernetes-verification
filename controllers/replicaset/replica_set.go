package replicaset

import (
	"controllers/common"

	apps "k8s.io/api/apps/v1"
	v1 "k8s.io/api/core/v1"
	apierrors "k8s.io/apimachinery/pkg/api/errors"
	metav1 "k8s.io/apimachinery/pkg/apis/meta/v1"
	"k8s.io/kubernetes/pkg/controller"
)

// A simplified replicaset controller. The following features are not included:
// * adoption and release
// * managing status
// * concurrent creation/deletion
// * sort before deletion

func manageReplicas(activePods []*v1.Pod, rs *apps.ReplicaSet) error {
	diff := len(activePods) - int(*(rs.Spec.Replicas))
	if diff < 0 {
		diff *= -1
		for i := 0; i < diff; i++ {
			pod, err := controller.GetPodFromTemplate(&rs.Spec.Template, rs, metav1.NewControllerRef(rs, apps.SchemeGroupVersion.WithKind("ReplicaSet")))
			if err != nil {
				return err
			}
			_, err = common.State.PodCreate(rs.Namespace, pod)
			if err != nil {
				return err
			}
		}
	} else if diff > 0 {
		podsToDelete := activePods[:diff]
		for _, pod := range podsToDelete {
			if err := common.State.PodDelete(rs.Namespace, pod.Name, metav1.DeleteOptions{}); err != nil {
				if !apierrors.IsNotFound(err) {
					return err
				}
			}
		}
	}

	return nil
}

func syncReplicaSet(namespace, name string) error {
	rs, err := common.State.ReplicaSetGet(namespace, name)
	if apierrors.IsNotFound(err) {
		return nil
	}
	if err != nil {
		return err
	}

	allRSPods, err := common.FilterPodsByOwner(&rs.ObjectMeta, "ReplicaSet")
	if err != nil {
		return err
	}

	allActivePods := common.FilterActivePods(allRSPods)

	var manageReplicasErr error
	if rs.DeletionTimestamp == nil {
		manageReplicasErr = manageReplicas(allActivePods, rs)
	}

	return manageReplicasErr
}
