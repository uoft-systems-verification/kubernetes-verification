package generators

import (
	apps "k8s.io/api/apps/v1"
	metav1 "k8s.io/apimachinery/pkg/apis/meta/v1"
	"k8s.io/apimachinery/pkg/runtime"
	"pgregory.net/rapid"
)

// ControllerRevision payloads are JSON objects on the wire, with Object=nil.
func MinimalControllerRevisionGen() *rapid.Generator[*apps.ControllerRevision] {
	return rapid.Custom(func(t *rapid.T) *apps.ControllerRevision {
		return &apps.ControllerRevision{
			ObjectMeta: metav1.ObjectMeta{Name: rapid.StringMatching(`[a-z][a-z0-9]{0,10}`).Draw(t, "name"), Namespace: "default"},
			Data:       runtime.RawExtension{Raw: []byte(`{"spec":{"template":{"metadata":{},"spec":{"containers":[]}}}}`)},
			Revision:   rapid.Int64Range(0, 100).Draw(t, "revision"),
		}
	})
}
func ComprehensiveControllerRevisionGen() *rapid.Generator[*apps.ControllerRevision] {
	return rapid.Custom(func(t *rapid.T) *apps.ControllerRevision {
		r := MinimalControllerRevisionGen().Draw(t, "revisionObject")
		r.Labels = map[string]string{"app": rapid.StringMatching(`[a-z]{1,10}`).Draw(t, "app")}
		r.Annotations = map[string]string{"note": rapid.String().Draw(t, "note")}
		if rapid.Bool().Draw(t, "emptyPayload") {
			r.Data.Raw = []byte(`{}`)
		}
		return r
	})
}
func InvalidControllerRevisionGen() *rapid.Generator[*apps.ControllerRevision] {
	return rapid.Custom(func(t *rapid.T) *apps.ControllerRevision {
		r := MinimalControllerRevisionGen().Draw(t, "revisionObject")
		switch rapid.IntRange(0, 5).Draw(t, "invalidRevision") {
		case 0:
			r.Revision = -1
		case 1:
			r.Data.Raw = nil
		case 2:
			r.Data.Raw = []byte(`null`)
		case 3:
			r.Data.Raw = []byte(`[]`)
		case 4:
			r.Data.Raw = []byte(`1`)
		case 5:
			r.Name = "INVALID!"
		}
		return r
	})
}
func ComprehensiveControllerRevisionMut(t *rapid.T, model, real *apps.ControllerRevision, exists, valid bool) {
	if valid {
		n := rapid.Int64Range(0, 1000).Draw(t, "revisionNumber")
		model.Revision = n
		real.Revision = n
	} else {
		switch rapid.IntRange(0, 2).Draw(t, "invalidRevisionUpdate") {
		case 0:
			model.Revision = -1
			real.Revision = -1
		case 1:
			model.Data = runtime.RawExtension{Raw: []byte(`{"changed":true}`)}
			real.Data = *model.Data.DeepCopy()
		case 2:
			model.ResourceVersion = "999999999999999999"
			real.ResourceVersion = model.ResourceVersion
		}
	}
}
