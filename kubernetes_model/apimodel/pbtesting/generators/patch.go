package generators

import (
	"encoding/json"

	"k8s.io/apimachinery/pkg/types"
	"pgregory.net/rapid"
)

// Patch is a request body and its content type and optional subresource.
type Patch struct {
	Type         types.PatchType
	Data         []byte
	Subresources []string
}

// PatchGen generates metadata, spec, and status patches for the selected kind.
// Invalid requests perturb labels, resourceVersion, name, or replica count.
// A resource may ignore an unknown spec field, just as it does for updates.
func PatchGen(kind string, valid bool) *rapid.Generator[Patch] {
	return rapid.Custom(func(rt *rapid.T) Patch {
		pt := rapid.SampledFrom([]types.PatchType{types.JSONPatchType, types.MergePatchType, types.StrategicMergePatchType}).Draw(rt, "patchType")
		modes := []int{0, 1, 2, 3, 7, 8, 9, 10, 11, 12}
		if !valid {
			modes = []int{4, 5, 6, 9}
		}
		if kind == "ControllerRevision" && valid {
			modes = []int{0, 1, 2, 3, 7, 10, 11, 12}
		}
		mode := rapid.SampledFrom(modes).Draw(rt, "patchCase")
		var document interface{}
		var subs []string
		metadata := map[string]interface{}{}
		document = map[string]interface{}{"metadata": metadata}
		path := "/metadata/annotations"
		var value interface{}
		switch mode {
		case 0, 1, 2, 3:
			value = map[string]string{"pbt-patch": rapid.StringMatching(`[a-z]{1,8}`).Draw(rt, "patchValue")}
			metadata["annotations"] = value
		case 4:
			path = "/metadata/labels"
			value = map[string]string{"bad key": "invalid"}
			metadata["labels"] = value
		case 5:
			path = "/metadata/resourceVersion"
			value = "1"
			metadata["resourceVersion"] = value
		case 6:
			path = "/metadata/name"
			value = "wrong-patch-name"
			metadata["name"] = value
		case 7:
			path = "/metadata/finalizers"
			value = []string{"example.com/pbt-patch"}
			metadata["finalizers"] = value
		case 8:
			subs = []string{"status"}
			path = "/status"
			value = map[string]interface{}{"observedGeneration": 2}
			if kind == "Pod" {
				value = map[string]interface{}{"phase": "Running"}
			}
			if kind == "PersistentVolumeClaim" {
				value = map[string]interface{}{"phase": "Pending"}
			}
			document = map[string]interface{}{"status": value}
		case 9:
			path = "/spec/replicas"
			if valid {
				value = rapid.Int32Range(0, 5).Draw(rt, "patchReplicas")
			} else {
				value = int32(-1)
			}
			document = map[string]interface{}{"spec": map[string]interface{}{"replicas": value}}
		case 10:
			document = map[string]interface{}{}
		case 12:
			path = "/metadata/ownerReferences"
			value = []map[string]interface{}{{"apiVersion": "apps/v1", "kind": "ReplicaSet", "name": "patch-owner", "uid": "patch-owner-uid", "controller": true}}
			metadata["ownerReferences"] = value
		case 11:
			document = map[string]interface{}{"metadata": map[string]interface{}{"annotations": nil}}
			value = nil
		}
		if pt == types.JSONPatchType {
			document = []map[string]interface{}{{"op": "add", "path": path, "value": value}}
			if mode == 10 {
				document = []map[string]interface{}{}
			}
		}
		data, err := json.Marshal(document)
		if err != nil {
			rt.Fatal(err)
		}
		return Patch{Type: pt, Data: data, Subresources: subs}
	})
}
