From New.generatedviews Require Export typemeta.
From New.proof Require Import prelude empty_ffi.
From New.object_specs Require Export common.

(* TypeMeta is optional on typed Kubernetes objects returned by the API server.
   When kind or apiVersion is present, it must agree with the concrete type;
   omitted fields remain valid. The concrete [kind] argument still has to be a
   kind supported by this model. *)
Definition valid_typemeta kind tm : Prop :=
  (tm.(v1.TypeMeta.Kind') = ""%go ∨ kind = tm.(v1.TypeMeta.Kind')) ∧
  valid_kind kind ∧
  (tm.(v1.TypeMeta.APIVersion') = ""%go ∨
    valid_api_version kind tm.(v1.TypeMeta.APIVersion')).

(* TypeMeta on a create request may omit [kind] and/or [apiVersion]: the JSON
   decoder fills each missing GVK field from the REST endpoint's default GVK.
   An explicitly incompatible kind does not match that typed object and fails
   during decoding/conversion, while an incompatible group/version is rejected
   by the create handler before resource validation:
   https://github.com/kubernetes/kubernetes/blob/release-1.34/staging/src/k8s.io/apimachinery/pkg/runtime/serializer/json/json.go#L115-L127
   https://github.com/kubernetes/kubernetes/blob/release-1.34/staging/src/k8s.io/apimachinery/pkg/runtime/serializer/json/json.go#L164-L205
   https://github.com/kubernetes/kubernetes/blob/release-1.34/staging/src/k8s.io/apiserver/pkg/endpoints/handlers/create.go#L116-L147

   The same omission rule applies to typed objects returned by Kubernetes;
   [valid_typemeta] additionally records that [kind] is supported by the model. *)
Definition valid_create_typemeta kind tm : Prop :=
  (tm.(v1.TypeMeta.Kind') = ""%go ∨ kind = tm.(v1.TypeMeta.Kind')) ∧
  (tm.(v1.TypeMeta.APIVersion') = ""%go ∨
    valid_api_version kind tm.(v1.TypeMeta.APIVersion')).

Lemma zero_typemeta_valid_create kind :
  valid_create_typemeta kind (zero_val v1.TypeMeta.t).
Proof. split; left; done. Qed.

Lemma valid_typemeta_valid_create_typemeta kind tm :
  valid_typemeta kind tm →
  valid_create_typemeta kind tm.
Proof.
  unfold valid_typemeta, valid_create_typemeta.
  intros (Hkind & _ & Hapi_version).
  split; done.
Qed.

Module TypeMetaV.
Include TypeMetaView.TypeMetaV.

Definition valid (kind : go_string) (meta : t) : Prop := valid_typemeta kind meta.
Definition valid_create (kind : go_string) (meta : t) : Prop := valid_create_typemeta kind meta.

End TypeMetaV.
