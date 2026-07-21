From New.proof.k8s_io.api.apps Require Export v1_init.
From New.proof.k8s_io.apimachinery.pkg.runtime Require Export schema.

From New.proof Require Import prelude empty_ffi.
From New.proof.kubernetes_types Require Import prelude.

Section proof.
Context `{hG: !heapGS Σ} `{!ffi_semantics _ _}.
Context {sem : go.Semantics} {schema_sem : schema.Assumptions}.
Collection W := sem + schema_sem.

Lemma wp_SchemeGroupVersion__WithKind gv kind :
  {{{ "#Hschema_init" ∷ is_pkg_init schema ∗
      "#Hglobal_gv" ∷
        (global_addr code.k8s_io.api.apps.v1.v1.SchemeGroupVersion) ↦□ gv
  }}}
    (global_addr code.k8s_io.api.apps.v1.v1.SchemeGroupVersion) @!
      (go.PointerType schema.GroupVersion) @! "WithKind" #kind
  {{{ gvk, RET #gvk;
      ⌜ gvk.(schema.GroupVersionKind.Group') =
          gv.(schema.GroupVersion.Group') ∧
        gvk.(schema.GroupVersionKind.Version') =
          gv.(schema.GroupVersion.Version') ∧
        gvk.(schema.GroupVersionKind.Kind') = kind ⌝
  }}}.
Proof using hG schema_sem sem Σ.
  wp_start as "H". iNamed "H".
  wp_pures.
  wp_load.
  wp_pures.
  by wp_apply (schema.wp_GroupVersion__WithKind with "[$Hschema_init]").
Qed.

End proof.
