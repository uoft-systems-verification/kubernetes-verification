From New.proof.k8s_io.api.apps Require Export v1_init.
From New.proof.k8s_io.apimachinery.pkg.runtime Require Export schema.

From New.proof Require Import prelude empty_ffi.
From New.proof.kubernetes_types Require Import prelude.

Section proof.
Context `{hG: !heapGS Σ} `{!ffi_semantics _ _}.
Context {sem : go.Semantics} {schema_sem : schema.Assumptions}.
Collection W := sem + schema_sem.

Lemma wp_SchemeGroupVersion__WithKind kind :
  {{{ "#Hinit" ∷ is_pkg_init code.k8s_io.api.apps.v1.pkg_id.v1 }}}
    (global_addr code.k8s_io.api.apps.v1.v1.SchemeGroupVersion) @!
      (go.PointerType schema.GroupVersion) @! "WithKind" #kind
  {{{ gvk, RET #gvk;
      ⌜ gvk.(schema.GroupVersionKind.Group') = "apps"%go ∧
        gvk.(schema.GroupVersionKind.Version') = "v1"%go ∧
        gvk.(schema.GroupVersionKind.Kind') = kind ⌝
  }}}.
Proof using hG schema_sem sem Σ.
  wp_start as "H". iNamed "H".
  iDestruct (is_pkg_init_access with "Hinit") as "Happs_init".
  simpl.
  iDestruct "Happs_init" as (gv)
    "(#Hglobal_gv & %HSchemeGroupVersion_Group &
      %HSchemeGroupVersion_Version)".
  wp_pures.
  wp_load.
  wp_pures.
  iDestruct (is_pkg_init_unfold_deps with "Hinit") as
    "(_ & _ & #Hschema_init & _)".
  wp_apply (schema.wp_GroupVersion__WithKind with "[$Hschema_init]").
  iIntros (gvk) "%Hgvk".
  destruct Hgvk as (Hgroup & Hversion & Hkind).
  iApply "HΦ". iPureIntro.
  rewrite Hgroup Hversion HSchemeGroupVersion_Group
    HSchemeGroupVersion_Version.
  done.
Qed.

End proof.
