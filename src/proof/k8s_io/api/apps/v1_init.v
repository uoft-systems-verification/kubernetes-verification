Require Export New.generatedproof.k8s_io.api.apps.v1.
From New.proof.k8s_io.api.core Require Export v1_init.


Section proof.
Context `{hG: heapGS Σ} `{!ffi_semantics _ _} {go_ctx: GoContext}.

(* TODO: carry the globals in IsPkgInit *)
(* Definition is_initialized : iProp Σ :=
  ∃ (gv: schema.GroupVersion.t),
    "#HglobalSchemeGroupVersion" ∷ (global_addr v1.SchemeGroupVersion) ↦□ gv ∗
    "%HSchemeGroupVersion_Group" ∷ ⌜ gv.(schema.GroupVersion.Group') = "apps"%go ⌝ ∗
    "%HSchemeGroupVersion_Version" ∷ ⌜ gv.(schema.GroupVersion.Version') = "v1"%go ⌝. *)

#[global] Instance : IsPkgInit code.k8s_io.api.apps.v1.v1 := define_is_pkg_init True%I.
#[global] Instance : GetIsPkgInitWf code.k8s_io.api.apps.v1.v1 := build_get_is_pkg_init_wf.

End proof.
