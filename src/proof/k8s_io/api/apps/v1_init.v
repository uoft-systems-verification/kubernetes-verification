Require Export New.generatedproof.k8s_io.api.apps.v1.
From New.proof Require Import proof_prelude.
From New.proof.k8s_io.api.core Require Export v1_init.


Section proof.
Context `{hG: heapGS Σ} `{!ffi_semantics _ _}.
Context {sem : go.Semantics} {package_sem : code.k8s_io.api.apps.v1.v1.Assumptions}.
Collection W := sem + package_sem.

Definition is_initialized : iProp Σ :=
  ∃ (gv: schema.GroupVersion.t),
    "#HglobalSchemeGroupVersion" ∷
      (global_addr code.k8s_io.api.apps.v1.v1.SchemeGroupVersion) ↦□ gv ∗
    "%HSchemeGroupVersion_Group" ∷ ⌜ gv.(schema.GroupVersion.Group') = "apps"%go ⌝ ∗
    "%HSchemeGroupVersion_Version" ∷ ⌜ gv.(schema.GroupVersion.Version') = "v1"%go ⌝.

#[global] Instance : IsPkgInit (iProp Σ)
    code.k8s_io.api.apps.v1.pkg_id.v1 :=
  define_is_pkg_init is_initialized.
#[global] Instance : GetIsPkgInitWf (iProp Σ) code.k8s_io.api.apps.v1.pkg_id.v1 := build_get_is_pkg_init_wf.

(* TODO: Prove [wp_initialize'] showing that the generated apps/v1 package
initializer establishes [is_initialized]. The generated initializer currently
calls opaque initializers for untranslated globals, as well as the core/v1,
meta/v1, and schema package initializers, so those calls first need proved
specifications (or their implementations need to be translated). *)

End proof.
