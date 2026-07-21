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

End proof.
