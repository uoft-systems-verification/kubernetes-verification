From New.proof.k8s_io.apimachinery.pkg.runtime Require Export schema_init.
From New.proof Require Import prelude empty_ffi.

Section proof.
Context `{hG: !heapGS Σ} `{!ffi_semantics _ _}.
Context {sem : go.Semantics} {package_sem : schema.Assumptions}.
Collection W := sem + package_sem.
Set Default Proof Using "W".

Lemma wp_GroupVersion__WithKind (gv: schema.GroupVersion.t) kind:
  {{{ is_pkg_init schema }}}
    gv @! schema.GroupVersion @! "WithKind" #kind
  {{{ gvk, RET #gvk;
      ⌜ gvk.(schema.GroupVersionKind.Group') = gv.(schema.GroupVersion.Group') ∧
        gvk.(schema.GroupVersionKind.Version') = gv.(schema.GroupVersion.Version') ∧
        gvk.(schema.GroupVersionKind.Kind') = kind ⌝
  }}}.
Proof. wp_start. wp_auto. wp_end. Qed.

End proof.
