package generators

import (
	metav1 "k8s.io/apimachinery/pkg/apis/meta/v1"
	"k8s.io/apimachinery/pkg/types"
	"pgregory.net/rapid"
)

// ObjectMetaMut mutates shared ObjectMeta fields for update tests.
//
// valid=true keeps the update on a success path:
// - existing objects keep or omit UID/resourceVersion in ways the apiserver accepts
// - missing objects omit both fields
//
// valid=false chooses a single metadata-level rejection cause for existing objects.
// It returns true when it introduced such a metadata rejection cause, so callers can
// avoid layering an additional immutable-field rejection on top.
func ObjectMetaMut(rt *rapid.T, modelObj, realObj metav1.Object, exists, valid bool) bool {
	labelKey := rapid.StringMatching(`[a-z][a-z0-9]{0,8}`).Draw(rt, "updateLabelKey")
	labelValue := rapid.StringMatching(`[a-z][a-z0-9-]{0,8}`).Draw(rt, "updateLabelValue")
	modelLabels := modelObj.GetLabels()
	if modelLabels == nil {
		modelLabels = map[string]string{}
	}
	realLabels := realObj.GetLabels()
	if realLabels == nil {
		realLabels = map[string]string{}
	}
	modelLabels[labelKey] = labelValue
	realLabels[labelKey] = labelValue
	modelObj.SetLabels(modelLabels)
	realObj.SetLabels(realLabels)

	annotationKey := rapid.StringMatching(`[a-z][a-z0-9]{0,8}`).Draw(rt, "updateAnnotationKey")
	annotationValue := rapid.StringMatching(`[a-z][a-z0-9-]{0,16}`).Draw(rt, "updateAnnotationValue")
	modelAnnotations := modelObj.GetAnnotations()
	if modelAnnotations == nil {
		modelAnnotations = map[string]string{}
	}
	realAnnotations := realObj.GetAnnotations()
	if realAnnotations == nil {
		realAnnotations = map[string]string{}
	}
	modelAnnotations[annotationKey] = annotationValue
	realAnnotations[annotationKey] = annotationValue
	modelObj.SetAnnotations(modelAnnotations)
	realObj.SetAnnotations(realAnnotations)

	if !exists {
		modelObj.SetUID("")
		modelObj.SetResourceVersion("")
		realObj.SetUID("")
		realObj.SetResourceVersion("")
		return false
	}

	if valid {
		if rapid.Bool().Draw(rt, "validUpdateUIDOmit") {
			modelObj.SetUID("")
			realObj.SetUID("")
		}

		if rapid.Bool().Draw(rt, "validUpdateRVOmit") {
			modelObj.SetResourceVersion("")
			realObj.SetResourceVersion("")
		}

		return false
	}

	if rapid.Bool().Draw(rt, "invalidUpdateUsesBadUID") {
		wrongUID := types.UID("corrupted-uid")
		modelObj.SetUID(wrongUID)
		realObj.SetUID(wrongUID)
		return true
	}

	modelObj.SetResourceVersion("corrupted-rv")
	realObj.SetResourceVersion("corrupted-rv")
	return true
}
