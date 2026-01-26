package comparators

import (
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

// ComparisonResult holds the result of comparing model and real API responses.
type ComparisonResult struct {
	Match       bool
	Differences []string
}

// CompareCreateResults compares the results of Create operations from model and real API.
// This uses strict comparison - error reasons must match exactly.
func CompareCreateResults(
	modelObj interface{}, modelErr error,
	realObj interface{}, realErr error,
) ComparisonResult {
	return compareCreateResultsWithMode(modelObj, modelErr, realObj, realErr, false)
}

// CompareCreateResultsLenient compares results with lenient error matching.
// Only checks that both accept or both reject, without requiring exact error reasons.
func CompareCreateResultsLenient(
	modelObj interface{}, modelErr error,
	realObj interface{}, realErr error,
) ComparisonResult {
	return compareCreateResultsWithMode(modelObj, modelErr, realObj, realErr, true)
}

func compareCreateResultsWithMode(
	modelObj interface{}, modelErr error,
	realObj interface{}, realErr error,
	lenient bool,
) ComparisonResult {
	result := ComparisonResult{Match: true}

	// Compare error states
	modelIsErr := modelErr != nil
	realIsErr := realErr != nil

	if modelIsErr != realIsErr {
		result.Match = false
		result.Differences = append(result.Differences,
			fmt.Sprintf("error state mismatch: model_err=%v, real_err=%v", modelErr, realErr))
		return result
	}

	// If both errors, compare error types
	if modelIsErr && realIsErr {
		if !compareErrorsWithMode(modelErr, realErr, &result.Differences, lenient) {
			result.Match = false
		}
		return result
	}

	// Both succeeded - compare objects (ignoring server-assigned fields)
	if !compareObjects(modelObj, realObj, &result.Differences) {
		result.Match = false
	}
	return result
}

// compareErrorsWithMode compares errors with configurable leniency.
// If lenient=true, only checks that both are errors (doesn't require same reason).
func compareErrorsWithMode(modelErr, realErr error, diffs *[]string, lenient bool) bool {
	var modelStatus apierrors.APIStatus
	var realStatus apierrors.APIStatus

	modelIsAPIStatus := errors.As(modelErr, &modelStatus)
	realIsAPIStatus := errors.As(realErr, &realStatus)

	if !modelIsAPIStatus || !realIsAPIStatus {
		// At least one is not an API error - just check if both are errors
		*diffs = append(*diffs, fmt.Sprintf("non-API error type: model=%T, real=%T", modelErr, realErr))
		return lenient // In lenient mode, both being errors is good enough
	}

	modelReason := modelStatus.Status().Reason
	realReason := realStatus.Status().Reason

	if lenient {
		// In lenient mode, both being validation-related errors is good enough
		// (BadRequest, Invalid, Forbidden are all "rejection" types)
		modelIsRejection := isRejectionReason(modelReason)
		realIsRejection := isRejectionReason(realReason)
		if modelIsRejection != realIsRejection {
			*diffs = append(*diffs, fmt.Sprintf(
				"error type mismatch: model=%s (rejection=%v), real=%s (rejection=%v)",
				modelReason, modelIsRejection, realReason, realIsRejection))
			return false
		}
		return true
	}

	// Strict mode: require exact reason match
	if modelReason != realReason {
		*diffs = append(*diffs, fmt.Sprintf(
			"error reason mismatch: model=%s, real=%s",
			modelReason, realReason))
		return false
	}

	// For Invalid errors, compare field paths
	if modelReason == metav1.StatusReasonInvalid {
		return compareValidationErrors(modelStatus, realStatus, diffs)
	}

	return true
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
func compareValidationErrors(modelStatus, realStatus apierrors.APIStatus, diffs *[]string) bool {
	modelDetails := modelStatus.Status().Details
	realDetails := realStatus.Status().Details

	if modelDetails == nil && realDetails == nil {
		return true
	}
	if modelDetails == nil || realDetails == nil {
		*diffs = append(*diffs, fmt.Sprintf(
			"error details mismatch: model=%v, real=%v", modelDetails, realDetails))
		return false
	}

	// Extract field paths from causes
	modelFields := extractFieldPaths(modelDetails.Causes)
	realFields := extractFieldPaths(realDetails.Causes)

	// Sort for comparison
	sort.Strings(modelFields)
	sort.Strings(realFields)

	if !reflect.DeepEqual(modelFields, realFields) {
		*diffs = append(*diffs, fmt.Sprintf(
			"validation field paths mismatch:\n  model: %v\n  real:  %v",
			modelFields, realFields))
		return false
	}

	return true
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

// compareObjects compares two Kubernetes objects, ignoring server-assigned fields.
func compareObjects(modelObj, realObj interface{}, diffs *[]string) bool {
	// First, verify both objects have consistent metadata field presence
	if !compareMetadata(modelObj, realObj, diffs) {
		return false
	}

	// Deep copy both objects
	modelCopy := deepCopyAndClear(modelObj)
	realCopy := deepCopyAndClear(realObj)

	if modelCopy == nil || realCopy == nil {
		*diffs = append(*diffs, fmt.Sprintf(
			"failed to copy objects: model=%T, real=%T", modelObj, realObj))
		return false
	}

	// Use Semantic.DeepEqual which correctly handles pointer values
	// (treats equal values as equal even if pointer addresses differ)
	if !equality.Semantic.DeepEqual(modelCopy, realCopy) {
		*diffs = append(*diffs, describeObjectDifferences(modelCopy, realCopy))
		return false
	}
	return true
}

// compareMetadata checks that both model and real API set the same metadata fields.
// Returns true if consistent, false if inconsistent (with differences appended to diffs).
func compareMetadata(modelObj, realObj interface{}, diffs *[]string) bool {
	modelAccessor, err := meta.Accessor(modelObj)
	if err != nil {
		*diffs = append(*diffs, fmt.Sprintf("failed to access model metadata: %v", err))
		return false
	}

	realAccessor, err := meta.Accessor(realObj)
	if err != nil {
		*diffs = append(*diffs, fmt.Sprintf("failed to access real metadata: %v", err))
		return false
	}

	consistent := true

	// Check UID: both should be empty or both should be non-empty
	modelHasUID := modelAccessor.GetUID() != ""
	realHasUID := realAccessor.GetUID() != ""
	if modelHasUID != realHasUID {
		*diffs = append(*diffs, fmt.Sprintf(
			"metadata.uid presence mismatch: model has UID=%v, real has UID=%v",
			modelHasUID, realHasUID))
		consistent = false
	}

	// Check ResourceVersion: both should be empty or both should be non-empty
	modelHasRV := modelAccessor.GetResourceVersion() != ""
	realHasRV := realAccessor.GetResourceVersion() != ""
	if modelHasRV != realHasRV {
		*diffs = append(*diffs, fmt.Sprintf(
			"metadata.resourceVersion presence mismatch: model has RV=%v, real has RV=%v",
			modelHasRV, realHasRV))
		consistent = false
	}

	// Check CreationTimestamp: both should be zero or both should be non-zero
	modelHasCreation := !modelAccessor.GetCreationTimestamp().Time.IsZero()
	realHasCreation := !realAccessor.GetCreationTimestamp().Time.IsZero()
	if modelHasCreation != realHasCreation {
		*diffs = append(*diffs, fmt.Sprintf(
			"metadata.creationTimestamp presence mismatch: model has timestamp=%v, real has timestamp=%v",
			modelHasCreation, realHasCreation))
		consistent = false
	}

	// Check DeletionTimestamp: both should be nil or both should be non-nil
	modelHasDeletion := modelAccessor.GetDeletionTimestamp() != nil
	realHasDeletion := realAccessor.GetDeletionTimestamp() != nil
	if modelHasDeletion != realHasDeletion {
		*diffs = append(*diffs, fmt.Sprintf(
			"metadata.deletionTimestamp presence mismatch: model has timestamp=%v, real has timestamp=%v",
			modelHasDeletion, realHasDeletion))
		consistent = false
	}

	return consistent
}

// deepCopyAndClear creates a deep copy and clears server-assigned fields.
func deepCopyAndClear(obj interface{}) interface{} {
	switch o := obj.(type) {
	case *corev1.Pod:
		copy := o.DeepCopy()
		clearServerAssignedFields(copy)
		return copy
	case *appsv1.ReplicaSet:
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
	accessor.SetGeneration(0)
	accessor.SetManagedFields(nil)
	accessor.SetSelfLink("")

	// Clear type-specific fields
	switch o := obj.(type) {
	case *corev1.Pod:
		// Clear status (always differs)
		o.Status = corev1.PodStatus{}

		// Clear admission controller defaults that model doesn't implement:
		// - DefaultTolerationSeconds admission controller adds tolerations
		// - Priority admission controller adds priority
		o.Spec.Tolerations = nil
		o.Spec.Priority = nil
		o.Spec.PreemptionPolicy = nil

		// ServiceAccount admission controller may set these
		o.Spec.DeprecatedServiceAccount = ""

	case *appsv1.ReplicaSet:
		o.Status = appsv1.ReplicaSetStatus{}
	}
}

// describeObjectDifferences describes the differences between two objects.
func describeObjectDifferences(model, real interface{}) string {
	modelPod, modelIsPod := model.(*corev1.Pod)
	realPod, realIsPod := real.(*corev1.Pod)

	if modelIsPod && realIsPod {
		return describePodDifferences(modelPod, realPod)
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
