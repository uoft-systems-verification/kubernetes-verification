From New.proof Require Import prelude empty_ffi.
From New.proof.k8s_io.apimachinery.pkg.util Require Export validation_init.
From New.proof.kubernetes_types Require Import common.

Section proof.
Context `{hG: !heapGS Σ} `{!ffi_semantics _ _}.
Context {sem : go.Semantics} {package_sem : validation.Assumptions}.
Local Set Default Proof Using "All".

(** Trusted regexp-backed interface.  The returned messages remain abstract;
    callers only depend on whether validation succeeded. *)
Lemma wp_IsQualifiedName value :
  {{{ is_pkg_init validation }}}
    @! validation.IsQualifiedName #value
  {{{ sl (errs : list go_string), RET #sl;
      sl ↦* errs ∗
      ⌜ errs = [] ↔ valid_label_name value ⌝
  }}}.
Proof. Admitted.

(** Trusted regexp-backed interface; see [wp_IsQualifiedName]. *)
Lemma wp_IsValidLabelValue value :
  {{{ is_pkg_init validation }}}
    @! validation.IsValidLabelValue #value
  {{{ sl (errs : list go_string), RET #sl;
      sl ↦* errs ∗
      ⌜ errs = [] ↔ valid_label_value value ⌝
  }}}.
Proof. Admitted.

End proof.
