package comparators

import (
	"bytes"
	"encoding/json"
	"errors"
	"fmt"
	"reflect"
	"sort"

	appsv1 "k8s.io/api/apps/v1"
	corev1 "k8s.io/api/core/v1"
	"k8s.io/apimachinery/pkg/api/equality"
	apierrors "k8s.io/apimachinery/pkg/api/errors"
	"k8s.io/apimachinery/pkg/api/meta"
	metav1 "k8s.io/apimachinery/pkg/apis/meta/v1"
)

// CompareErrors compares two errors with configurable leniency.
func CompareErrors(modelErr, realErr error, lenient bool) (bool, []string) {
	var diffs []string
	if modelErr == nil && realErr == nil {
		return true, diffs
	} else if modelErr == nil || realErr == nil {
		diffs = append(diffs, fmt.Sprintf("nil-error mismatch: model=%v, real=%v", modelErr, realErr))
		return false, diffs
	}

	var modelStatus apierrors.APIStatus
	var realStatus apierrors.APIStatus

	modelIsAPIStatus := errors.As(modelErr, &modelStatus)
	realIsAPIStatus := errors.As(realErr, &realStatus)

	if !modelIsAPIStatus || !realIsAPIStatus {
		// At least one is not an API error - just check if both are errors
		diffs = append(diffs, fmt.Sprintf("non-API error type: model=%v, real=%v", modelErr, realErr))
		return false, diffs
	}

	modelReason := modelStatus.Status().Reason
	realReason := realStatus.Status().Reason

	if lenient {
		// In lenient mode, both being validation-related errors is good enough
		// (BadRequest, Invalid, Forbidden are all "rejection" types)
		modelIsRejection := isRejectionReason(modelReason)
		realIsRejection := isRejectionReason(realReason)
		if modelIsRejection != realIsRejection {
			diffs = append(diffs, fmt.Sprintf(
				"error type mismatch: model=%s (rejection=%v), real=%s (rejection=%v)",
				modelReason, modelIsRejection, realReason, realIsRejection))
			return false, diffs
		}
		return true, diffs
	}

	// Strict mode: require exact reason match
	if modelReason != realReason {
		diffs = append(diffs, fmt.Sprintf(
			"error reason mismatch: model=%s, real=%s",
			modelReason, realReason))
		return false, diffs
	}

	// For Invalid errors, compare field paths
	if modelReason == metav1.StatusReasonInvalid {
		match, validationDiffs := compareValidationErrors(modelStatus, realStatus)
		diffs = append(diffs, validationDiffs...)
		return match, diffs
	}

	return true, diffs
}

// isRejectionReason returns true if the reason indicates the request was rejected
// (validation failed, forbidden, bad request, etc.)
func isRejectionReason(reason metav1.StatusReason) bool {
	switch reason {
	case metav1.StatusReasonInvalid,
		metav1.StatusReasonBadRequest,
		metav1.StatusReasonForbidden,
		metav1.StatusReasonNotAcceptable:
		return true
	default:
		return false
	}
}

// compareValidationErrors compares the field paths in validation errors.
func compareValidationErrors(modelStatus, realStatus apierrors.APIStatus) (bool, []string) {
	var diffs []string
	modelDetails := modelStatus.Status().Details
	realDetails := realStatus.Status().Details

	if modelDetails == nil && realDetails == nil {
		return true, diffs
	}
	if modelDetails == nil || realDetails == nil {
		diffs = append(diffs, fmt.Sprintf(
			"error details mismatch: model=%v, real=%v", modelDetails, realDetails))
		return false, diffs
	}

	// Extract field paths from causes
	modelFields := extractFieldPaths(modelDetails.Causes)
	realFields := extractFieldPaths(realDetails.Causes)

	// Sort for comparison
	sort.Strings(modelFields)
	sort.Strings(realFields)

	if !reflect.DeepEqual(modelFields, realFields) {
		diffs = append(diffs, fmt.Sprintf(
			"validation field paths mismatch:\n  model: %v\n  real:  %v",
			modelFields, realFields))
		return false, diffs
	}

	return true, diffs
}

// extractFieldPaths extracts field paths from status causes.
func extractFieldPaths(causes []metav1.StatusCause) []string {
	paths := make([]string, 0, len(causes))
	for _, cause := range causes {
		if cause.Field != "" {
			paths = append(paths, cause.Field)
		}
	}
	return paths
}

// CompareObjects compares two objects, ignoring server-assigned fields.
func CompareObjects(modelObj, realObj interface{}) (bool, []string) {
	var diffs []string

	if modelObj == nil && realObj == nil {
		return true, diffs
	} else if modelObj == nil || realObj == nil {
		diffs = append(diffs, fmt.Sprintf("nil-interface mismatch: model=%T, real=%T", modelObj, realObj))
		return false, diffs
	}

	// Check if the underlying values are nil pointers
	// (Go allows nil typed pointers to be non-nil interfaces)
	modelVal := reflect.ValueOf(modelObj)
	realVal := reflect.ValueOf(realObj)

	modelIsNil := modelVal.Kind() == reflect.Ptr && modelVal.IsNil()
	realIsNil := realVal.Kind() == reflect.Ptr && realVal.IsNil()

	if modelIsNil && realIsNil {
		return true, diffs
	} else if modelIsNil || realIsNil {
		diffs = append(diffs, fmt.Sprintf("nil pointer mismatch: model=%T (isNil=%v), real=%T (isNil=%v)",
			modelObj, modelIsNil, realObj, realIsNil))
		return false, diffs
	}

	// First, verify both objects have consistent metadata field presence
	match, metadataDiffs := compareMetadata(modelObj, realObj)
	if !match {
		return false, metadataDiffs
	}

	// Deep copy both objects
	modelCopy := deepCopyAndClear(modelObj)
	realCopy := deepCopyAndClear(realObj)

	if modelCopy == nil || realCopy == nil {
		diffs = append(diffs, fmt.Sprintf(
			"failed to copy objects: model=%T, real=%T", modelObj, realObj))
		return false, diffs
	}

	// Use Semantic.DeepEqual which correctly handles pointer values and all Kubernetes types.
	// This is the same comparison method used within Kubernetes itself.
	if !equality.Semantic.DeepEqual(modelCopy, realCopy) {
		// Objects differ - generate detailed debugging information using JSON
		diffs = append(diffs, describeObjectDifferencesWithJSON(modelCopy, realCopy))
		return false, diffs
	}
	return true, diffs
}

// describeObjectDifferencesWithJSON generates detailed diff information by comparing JSON representations.
// This provides clear, human-readable output showing exactly what differs between the objects.
func describeObjectDifferencesWithJSON(modelObj, realObj interface{}) string {
	// Try JSON marshaling for detailed diff
	modelJSON, modelErr := json.Marshal(modelObj)
	realJSON, realErr := json.Marshal(realObj)

	if modelErr == nil && realErr == nil && !bytes.Equal(modelJSON, realJSON) {
		// Find the first differing position
		diffPos := -1
		minLen := len(modelJSON)
		if len(realJSON) < minLen {
			minLen = len(realJSON)
		}
		for i := 0; i < minLen; i++ {
			if modelJSON[i] != realJSON[i] {
				diffPos = i
				break
			}
		}

		// Extract a window around the difference
		var diffContext string
		if diffPos >= 0 {
			start := diffPos - 50
			if start < 0 {
				start = 0
			}
			end := diffPos + 50
			modelEnd := end
			if modelEnd > len(modelJSON) {
				modelEnd = len(modelJSON)
			}
			realEnd := end
			if realEnd > len(realJSON) {
				realEnd = len(realJSON)
			}

			diffContext = fmt.Sprintf("\nFirst difference at byte %d:\nModel: ...%s...\nReal:  ...%s...",
				diffPos, string(modelJSON[start:modelEnd]), string(realJSON[start:realEnd]))
		} else if len(modelJSON) != len(realJSON) {
			diffContext = fmt.Sprintf("\nJSON length differs: model=%d, real=%d", len(modelJSON), len(realJSON))
		}

		return fmt.Sprintf("objects differ (Semantic.DeepEqual returned false)%s\nFull model JSON: %s\nFull real JSON: %s",
			diffContext, string(modelJSON), string(realJSON))
	}

	// Fallback to basic description if JSON marshaling fails
	return describeObjectDifferences(modelObj, realObj)
}

// compareMetadata checks that both model and real API set the same metadata fields.
// Returns true if consistent, false if inconsistent (with differences appended to diffs).
func compareMetadata(modelObj, realObj interface{}) (bool, []string) {
	var diffs []string

	modelAccessor, err := meta.Accessor(modelObj)
	if err != nil {
		diffs = append(diffs, fmt.Sprintf("failed to access model metadata: %v", err))
		return false, diffs
	}

	realAccessor, err := meta.Accessor(realObj)
	if err != nil {
		diffs = append(diffs, fmt.Sprintf("failed to access real metadata: %v", err))
		return false, diffs
	}

	consistent := true

	// Check UID: both should be empty or both should be non-empty
	modelHasUID := modelAccessor.GetUID() != ""
	realHasUID := realAccessor.GetUID() != ""
	if !modelHasUID || !realHasUID {
		diffs = append(diffs, fmt.Sprintf(
			"metadata.uid is empty: model has UID=%v, real has UID=%v",
			modelHasUID, realHasUID))
		consistent = false
	}

	// Check ResourceVersion: both should be non-empty
	modelHasRV := modelAccessor.GetResourceVersion() != ""
	realHasRV := realAccessor.GetResourceVersion() != ""
	if !modelHasRV || !realHasRV {
		diffs = append(diffs, fmt.Sprintf(
			"metadata.resourceVersion is empty: model has RV=%v, real has RV=%v",
			modelHasRV, realHasRV))
		consistent = false
	}

	// Check CreationTimestamp: both should be zero or both should be non-zero
	modelHasCreation := !modelAccessor.GetCreationTimestamp().Time.IsZero()
	realHasCreation := !realAccessor.GetCreationTimestamp().Time.IsZero()
	if modelHasCreation != realHasCreation {
		diffs = append(diffs, fmt.Sprintf(
			"metadata.creationTimestamp presence mismatch: model has timestamp=%v, real has timestamp=%v",
			modelHasCreation, realHasCreation))
		consistent = false
	}

	// Check DeletionTimestamp: both should be nil or both should be non-nil
	modelHasDeletion := modelAccessor.GetDeletionTimestamp() != nil
	realHasDeletion := realAccessor.GetDeletionTimestamp() != nil
	if modelHasDeletion != realHasDeletion {
		diffs = append(diffs, fmt.Sprintf(
			"metadata.deletionTimestamp presence mismatch: model has timestamp=%v, real has timestamp=%v",
			modelHasDeletion, realHasDeletion))
		consistent = false
	}

	return consistent, diffs
}

// deepCopyAndClear creates a deep copy and clears server-assigned fields.
func deepCopyAndClear(obj interface{}) interface{} {
	switch o := obj.(type) {
	case *corev1.Pod:
		copy := o.DeepCopy()
		clearServerAssignedFields(copy)
		return copy
	case *corev1.PersistentVolumeClaim:
		copy := o.DeepCopy()
		clearServerAssignedFields(copy)
		return copy
	case *appsv1.ReplicaSet:
		copy := o.DeepCopy()
		clearServerAssignedFields(copy)
		return copy
	case *appsv1.StatefulSet:
		copy := o.DeepCopy()
		clearServerAssignedFields(copy)
		return copy
	case *appsv1.Deployment:
		copy := o.DeepCopy()
		clearServerAssignedFields(copy)
		return copy
	default:
		return nil
	}
}

// clearServerAssignedFields clears fields that are assigned by the server.
// This includes both API server-assigned fields and admission controller defaults.
func clearServerAssignedFields(obj interface{}) {
	accessor, err := meta.Accessor(obj)
	if err != nil {
		return
	}

	// Clear metadata fields that differ between model and real API
	accessor.SetUID("")
	accessor.SetResourceVersion("")
	accessor.SetCreationTimestamp(metav1.Time{})
	accessor.SetDeletionTimestamp(nil)
	accessor.SetManagedFields(nil)
	accessor.SetSelfLink("")
}

// describeObjectDifferences describes the differences between two objects.
func describeObjectDifferences(model, real interface{}) string {
	modelPod, modelIsPod := model.(*corev1.Pod)
	realPod, realIsPod := real.(*corev1.Pod)

	if modelIsPod && realIsPod {
		return describePodDifferences(modelPod, realPod)
	}

	modelRS, modelIsRS := model.(*appsv1.ReplicaSet)
	realRS, realIsRS := real.(*appsv1.ReplicaSet)

	if modelIsRS && realIsRS {
		return describeReplicaSetDifferences(modelRS, realRS)
	}

	modelAccessor, _ := meta.Accessor(model)
	realAccessor, _ := meta.Accessor(real)

	if modelAccessor != nil && realAccessor != nil {
		return fmt.Sprintf(
			"objects differ:\n  model name=%s, namespace=%s\n  real name=%s, namespace=%s",
			modelAccessor.GetName(), modelAccessor.GetNamespace(),
			realAccessor.GetName(), realAccessor.GetNamespace())
	}

	return fmt.Sprintf("objects differ: model=%+v, real=%+v", model, real)
}

// describePodDifferences provides detailed diff for Pod objects.
func describePodDifferences(model, real *corev1.Pod) string {
	var diffs []string

	// Metadata differences
	if model.Name != real.Name {
		diffs = append(diffs, fmt.Sprintf("name: model=%s, real=%s", model.Name, real.Name))
	}
	if model.Namespace != real.Namespace {
		diffs = append(diffs, fmt.Sprintf("namespace: model=%s, real=%s", model.Namespace, real.Namespace))
	}
	if model.Generation != real.Generation {
		diffs = append(diffs, fmt.Sprintf("generation: model=%d, real=%d", model.Generation, real.Generation))
	}

	// Spec differences
	if model.Spec.DNSPolicy != real.Spec.DNSPolicy {
		diffs = append(diffs, fmt.Sprintf("spec.dnsPolicy: model=%s, real=%s", model.Spec.DNSPolicy, real.Spec.DNSPolicy))
	}
	if model.Spec.RestartPolicy != real.Spec.RestartPolicy {
		diffs = append(diffs, fmt.Sprintf("spec.restartPolicy: model=%s, real=%s", model.Spec.RestartPolicy, real.Spec.RestartPolicy))
	}
	if model.Spec.SchedulerName != real.Spec.SchedulerName {
		diffs = append(diffs, fmt.Sprintf("spec.schedulerName: model=%s, real=%s", model.Spec.SchedulerName, real.Spec.SchedulerName))
	}
	if model.Spec.ServiceAccountName != real.Spec.ServiceAccountName {
		diffs = append(diffs, fmt.Sprintf("spec.serviceAccountName: model=%s, real=%s", model.Spec.ServiceAccountName, real.Spec.ServiceAccountName))
	}

	// TerminationGracePeriodSeconds
	var modelTGPS, realTGPS int64 = -1, -1
	if model.Spec.TerminationGracePeriodSeconds != nil {
		modelTGPS = *model.Spec.TerminationGracePeriodSeconds
	}
	if real.Spec.TerminationGracePeriodSeconds != nil {
		realTGPS = *real.Spec.TerminationGracePeriodSeconds
	}
	if modelTGPS != realTGPS {
		diffs = append(diffs, fmt.Sprintf("spec.terminationGracePeriodSeconds: model=%d, real=%d", modelTGPS, realTGPS))
	}

	// Container differences
	if len(model.Spec.Containers) != len(real.Spec.Containers) {
		diffs = append(diffs, fmt.Sprintf("containers count: model=%d, real=%d",
			len(model.Spec.Containers), len(real.Spec.Containers)))
	} else if len(model.Spec.Containers) > 0 {
		mc := model.Spec.Containers[0]
		rc := real.Spec.Containers[0]
		if mc.Name != rc.Name {
			diffs = append(diffs, fmt.Sprintf("container[0].name: model=%s, real=%s", mc.Name, rc.Name))
		}
		if mc.Image != rc.Image {
			diffs = append(diffs, fmt.Sprintf("container[0].image: model=%s, real=%s", mc.Image, rc.Image))
		}
		if mc.ImagePullPolicy != rc.ImagePullPolicy {
			diffs = append(diffs, fmt.Sprintf("container[0].imagePullPolicy: model=%s, real=%s", mc.ImagePullPolicy, rc.ImagePullPolicy))
		}
		if mc.TerminationMessagePath != rc.TerminationMessagePath {
			diffs = append(diffs, fmt.Sprintf("container[0].terminationMessagePath: model=%s, real=%s", mc.TerminationMessagePath, rc.TerminationMessagePath))
		}
		if mc.TerminationMessagePolicy != rc.TerminationMessagePolicy {
			diffs = append(diffs, fmt.Sprintf("container[0].terminationMessagePolicy: model=%s, real=%s", mc.TerminationMessagePolicy, rc.TerminationMessagePolicy))
		}
	}

	// EnableServiceLinks
	var modelESL, realESL bool = false, false
	if model.Spec.EnableServiceLinks != nil {
		modelESL = *model.Spec.EnableServiceLinks
	}
	if real.Spec.EnableServiceLinks != nil {
		realESL = *real.Spec.EnableServiceLinks
	}
	if modelESL != realESL {
		diffs = append(diffs, fmt.Sprintf("spec.enableServiceLinks: model=%v, real=%v", modelESL, realESL))
	}

	if len(diffs) == 0 {
		return fmt.Sprintf("pods differ (no obvious field diff found)\n  model.spec=%+v\n  real.spec=%+v",
			model.Spec, real.Spec)
	}

	return fmt.Sprintf("pod differences:\n  %s", joinStrings(diffs, "\n  "))
}

// describeReplicaSetDifferences provides detailed diff for ReplicaSet objects.
func describeReplicaSetDifferences(model, real *appsv1.ReplicaSet) string {
	var diffs []string

	// Metadata differences
	if model.Name != real.Name {
		diffs = append(diffs, fmt.Sprintf("name: model=%s, real=%s", model.Name, real.Name))
	}
	if model.Namespace != real.Namespace {
		diffs = append(diffs, fmt.Sprintf("namespace: model=%s, real=%s", model.Namespace, real.Namespace))
	}
	if model.Generation != real.Generation {
		diffs = append(diffs, fmt.Sprintf("generation: model=%d, real=%d", model.Generation, real.Generation))
	}

	// Spec.Replicas
	var modelReplicas, realReplicas int32 = 1, 1
	if model.Spec.Replicas != nil {
		modelReplicas = *model.Spec.Replicas
	}
	if real.Spec.Replicas != nil {
		realReplicas = *real.Spec.Replicas
	}
	if modelReplicas != realReplicas {
		diffs = append(diffs, fmt.Sprintf("spec.replicas: model=%d, real=%d", modelReplicas, realReplicas))
	}

	// Spec.Selector
	if !reflect.DeepEqual(model.Spec.Selector, real.Spec.Selector) {
		diffs = append(diffs, fmt.Sprintf("spec.selector differs: model=%+v, real=%+v", model.Spec.Selector, real.Spec.Selector))
	}

	// Template differences (compare some key fields)
	if !reflect.DeepEqual(model.Spec.Template.Labels, real.Spec.Template.Labels) {
		diffs = append(diffs, fmt.Sprintf("spec.template.labels differs"))
	}

	if len(diffs) == 0 {
		return fmt.Sprintf("replicasets differ (no obvious field diff found)\n  model.spec=%+v\n  real.spec=%+v",
			model.Spec, real.Spec)
	}

	return fmt.Sprintf("replicaset differences:\n  %s", joinStrings(diffs, "\n  "))
}

func joinStrings(strs []string, sep string) string {
	if len(strs) == 0 {
		return ""
	}
	result := strs[0]
	for i := 1; i < len(strs); i++ {
		result += sep + strs[i]
	}
	return result
}
