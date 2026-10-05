/*
Copyright 2016 The Kubernetes Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    http://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
*/

// If you make changes to this file, you should also make the corresponding change in ReplicationController.

package replicaset

import (
	"context"
	// "fmt"
	"reflect"
	"time"

	// "k8s.io/klog/v2"

	apps "k8s.io/api/apps/v1"
	v1 "k8s.io/api/core/v1"
	metav1 "k8s.io/apimachinery/pkg/apis/meta/v1"
	"k8s.io/apimachinery/pkg/labels"
	utilfeature "k8s.io/apiserver/pkg/util/feature"
	appsclient "k8s.io/client-go/kubernetes/typed/apps/v1"
	podutil "k8s.io/kubernetes/pkg/api/v1/pod"
	"k8s.io/kubernetes/pkg/features"
	// The condition helpers are identical upstream; only calculateStatus and
	// updateReplicaSetStatus (unexported, and adapted for Goose) are copied here.
	upstreamrs "k8s.io/kubernetes/pkg/controller/replicaset"
	"k8s.io/utils/ptr"
)

// updateReplicaSetStatus attempts to update the Status.Replicas of the given ReplicaSet, with a single GET/PUT retry.
// Logging never affects the verified behavior, so the logger parameter and the
// log statement below are commented out. The controllerFeatures parameter is
// removed as well: upstream reads it only to build the terminating-replicas part
// of that log message, so without logging it is unused.
// func updateReplicaSetStatus(logger klog.Logger, c appsclient.ReplicaSetInterface, rs *apps.ReplicaSet, newStatus apps.ReplicaSetStatus, controllerFeatures ReplicaSetControllerFeatures) (*apps.ReplicaSet, error) {
func updateReplicaSetStatus(c appsclient.ReplicaSetInterface, rs *apps.ReplicaSet, newStatus apps.ReplicaSetStatus) (*apps.ReplicaSet, error) {
	// This is the steady state. It happens when the ReplicaSet doesn't have any expectations, since
	// we do a periodic relist every 30s. If the generations differ but the replicas are
	// the same, a caller might've resized to the same replica count.
	if rs.Status.Replicas == newStatus.Replicas &&
		rs.Status.FullyLabeledReplicas == newStatus.FullyLabeledReplicas &&
		rs.Status.ReadyReplicas == newStatus.ReadyReplicas &&
		rs.Status.AvailableReplicas == newStatus.AvailableReplicas &&
		ptr.Equal(rs.Status.TerminatingReplicas, newStatus.TerminatingReplicas) &&
		rs.Generation == rs.Status.ObservedGeneration &&
		reflect.DeepEqual(rs.Status.Conditions, newStatus.Conditions) {
		return rs, nil
	}

	// Save the generation number we acted on, otherwise we might wrongfully indicate
	// that we've seen a spec update when we retry.
	// TODO: This can clobber an update if we allow multiple agents to write to the
	// same status.
	newStatus.ObservedGeneration = rs.Generation

	var getErr, updateErr error
	var updatedRS *apps.ReplicaSet
	// Zero-valued option variables instead of composite literals: Goose models
	// these option structs abstractly, so only their zero values are available.
	var updateOptions metav1.UpdateOptions
	var getOptions metav1.GetOptions
	// The loop variable is not named rs: Goose evaluates the initializer after
	// binding the new variable, so `rs := rs` would read the fresh nil pointer.
	for i, current := 0, rs; ; i++ {
		// terminatingReplicasUpdateInfo := ""
		// if utilfeature.DefaultFeatureGate.Enabled(features.DeploymentReplicaSetTerminatingReplicas) && controllerFeatures.EnableStatusTerminatingReplicas {
		// 	terminatingReplicasUpdateInfo = fmt.Sprintf("terminatingReplicas %s->%s, ", derefInt32ToStr(current.Status.TerminatingReplicas), derefInt32ToStr(newStatus.TerminatingReplicas))
		// }
		// logger.V(4).Info(fmt.Sprintf("Updating status for %v: %s/%s, ", current.Kind, current.Namespace, current.Name) +
		// 	fmt.Sprintf("replicas %d->%d (need %d), ", current.Status.Replicas, newStatus.Replicas, *(current.Spec.Replicas)) +
		// 	fmt.Sprintf("fullyLabeledReplicas %d->%d, ", current.Status.FullyLabeledReplicas, newStatus.FullyLabeledReplicas) +
		// 	fmt.Sprintf("readyReplicas %d->%d, ", current.Status.ReadyReplicas, newStatus.ReadyReplicas) +
		// 	fmt.Sprintf("availableReplicas %d->%d, ", current.Status.AvailableReplicas, newStatus.AvailableReplicas) +
		// 	terminatingReplicasUpdateInfo +
		// 	fmt.Sprintf("sequence No: %v->%v", current.Status.ObservedGeneration, newStatus.ObservedGeneration))

		current.Status = newStatus
		updatedRS, updateErr = c.UpdateStatus(context.TODO(), current, updateOptions)
		if updateErr == nil {
			return updatedRS, nil
		}
		// Stop retrying if we exceed statusUpdateRetries - the replicaSet will be requeued with a rate limit.
		if i >= statusUpdateRetries {
			break
		}
		// Update the ReplicaSet with the latest resource version for the next poll
		if current, getErr = c.Get(context.TODO(), current.Name, getOptions); getErr != nil {
			// If the GET fails we can't trust status.Replicas anymore. This error
			// is bound to be more interesting than the update failure.
			return nil, getErr
		}
	}

	return nil, updateErr
}

func calculateStatus(rs *apps.ReplicaSet, activePods []*v1.Pod, terminatingPods []*v1.Pod, manageReplicasErr error, controllerFeatures upstreamrs.ReplicaSetControllerFeatures, now time.Time) apps.ReplicaSetStatus {
	newStatus := rs.Status
	// Count the number of pods that have labels matching the labels of the pod
	// template of the replica set, the matching pods may have more
	// labels than are in the template. Because the label of podTemplateSpec is
	// a superset of the selector of the replica set, so the possible
	// matching pods must be part of the activePods.
	fullyLabeledReplicasCount := 0
	readyReplicasCount := 0
	availableReplicasCount := 0
	templateLabel := labels.Set(rs.Spec.Template.Labels).AsSelectorPreValidated()
	for _, pod := range activePods {
		if templateLabel.Matches(labels.Set(pod.Labels)) {
			fullyLabeledReplicasCount++
		}
		if podutil.IsPodReady(pod) {
			readyReplicasCount++
			if podutil.IsPodAvailable(pod, rs.Spec.MinReadySeconds, metav1.Time{Time: now}) {
				availableReplicasCount++
			}
		}
	}

	var terminatingReplicasCount *int32
	if utilfeature.DefaultFeatureGate.Enabled(features.DeploymentReplicaSetTerminatingReplicas) && controllerFeatures.EnableStatusTerminatingReplicas {
		terminatingReplicasCount = ptr.To(int32(len(terminatingPods)))
	}

	failureCond := upstreamrs.GetCondition(rs.Status, apps.ReplicaSetReplicaFailure)
	if manageReplicasErr != nil && failureCond == nil {
		var reason string
		if diff := len(activePods) - int(*(rs.Spec.Replicas)); diff < 0 {
			reason = "FailedCreate"
		} else if diff > 0 {
			reason = "FailedDelete"
		}
		cond := upstreamrs.NewReplicaSetCondition(apps.ReplicaSetReplicaFailure, v1.ConditionTrue, reason, manageReplicasErr.Error())
		upstreamrs.SetCondition(&newStatus, cond)
	} else if manageReplicasErr == nil && failureCond != nil {
		upstreamrs.RemoveCondition(&newStatus, apps.ReplicaSetReplicaFailure)
	}

	newStatus.Replicas = int32(len(activePods))
	newStatus.FullyLabeledReplicas = int32(fullyLabeledReplicasCount)
	newStatus.ReadyReplicas = int32(readyReplicasCount)
	newStatus.AvailableReplicas = int32(availableReplicasCount)
	newStatus.TerminatingReplicas = terminatingReplicasCount
	return newStatus
}
