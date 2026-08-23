From New.proof Require Import prelude empty_ffi.
From New.proof.k8s_io.apimachinery.pkg.util.validation Require Export field_init.

Section proof.
Context `{hG: !heapGS Σ} `{!ffi_semantics _ _}.
Context {sem : go.Semantics} {package_sem : field.Assumptions}.
Local Set Default Proof Using "All".

(** These weak path specifications deliberately hide path formatting.  A nil
    option list produces the nil root path, and both methods accept a nil
    parent in the Go implementation. *)
Lemma wp_ToPath_nil :
  {{{ is_pkg_init field }}}
    @! field.ToPath #slice.nil
  {{{ RET #null; True }}}.
Proof. Admitted.

Lemma wp_Path__Child (p : loc) (name : go_string) :
  {{{ is_pkg_init field }}}
    p @! (go.PointerType field.Path) @! "Child" #name #slice.nil
  {{{ (child : loc), RET #child; True }}}.
Proof. Admitted.

Lemma wp_Path__Index (p : loc) (index : w64) :
  {{{ is_pkg_init field }}}
    p @! (go.PointerType field.Path) @! "Index" #index
  {{{ (child : loc), RET #child; True }}}.
Proof. Admitted.

(** The success path of [labels.NewRequirement] never appends an error, so it
    only needs the zero-value case of [ErrorList.ToAggregate]. *)
Lemma wp_ErrorList__ToAggregate_nil (errors_l : loc) :
  {{{ is_pkg_init field ∗ errors_l ↦ (zero_val field.ErrorList.t) }}}
    errors_l @! (go.PointerType field.ErrorList) @! "ToAggregate" #()
  {{{ RET #interface.nil;
      errors_l ↦ (zero_val field.ErrorList.t)
  }}}.
Proof. Admitted.

End proof.
