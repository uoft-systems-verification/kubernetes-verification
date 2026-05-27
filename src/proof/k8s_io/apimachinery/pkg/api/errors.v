From New.proof.k8s_io.apimachinery.pkg.api Require Export errors_init.
From New.proof Require Import prelude empty_ffi.
From New.proof.kubernetes_model Require Import errors.
Require Import New.code.errors.

(* Keep these qualified: the stdlib package and Kubernetes API package are
   both named [errors], and unqualified [errors.Assumptions] can resolve to the
   stdlib package after [New.code.errors] is imported. *)
Module api_errors_pkg := code.k8s_io.apimachinery.pkg.api.errors.pkg_id.
Module api_errors := code.k8s_io.apimachinery.pkg.api.errors.errors.
Module std_errors := code.errors.errors.

Section proof.
Context `{hG: !heapGS Σ} `{!ffi_semantics _ _}.
Context {sem : go.Semantics}.
Context `{!std_errors.Assumptions}.
Local Set Default Proof Using "All".

Lemma wp_IsNotFound_nil err:
  {{{ is_pkg_init api_errors_pkg.errors ∗
      ⌜ err = interface.nil ⌝
  }}}
    @! api_errors.IsNotFound #err
  {{{ RET (#false);
    True%I
  }}}.
Proof.
Admitted.

Lemma wp_IsConflict_nil err:
  {{{ is_pkg_init api_errors_pkg.errors ∗
      ⌜ err = interface.nil ⌝
  }}}
    @! api_errors.IsConflict #err
  {{{ RET (#false);
    True%I
  }}}.
Proof.
Admitted.

Lemma wp_IsConflict_conflict err:
  {{{ is_pkg_init api_errors_pkg.errors ∗
      ⌜ conflict_error err ⌝
  }}}
    @! api_errors.IsConflict #err
  {{{ RET (#true);
    True%I
  }}}.
Proof.
Admitted.

Lemma wp_IsConflict_nil_cont err Φ :
  err = interface.nil →
  is_pkg_init api_errors_pkg.errors -∗
  ▷ (True -∗ Φ #false) -∗
  WP @! api_errors.IsConflict #err {{ Φ }}.
Proof.
  iIntros (?) "#Hinit HΦ".
  wp_apply (wp_IsConflict_nil with "[$Hinit]").
  { done. }
  iApply "HΦ". done.
Qed.

Lemma wp_IsConflict_conflict_cont err Φ :
  conflict_error err →
  is_pkg_init api_errors_pkg.errors -∗
  ▷ (True -∗ Φ #true) -∗
  WP @! api_errors.IsConflict #err {{ Φ }}.
Proof.
  iIntros (?) "#Hinit HΦ".
  wp_apply (wp_IsConflict_conflict with "[$Hinit]").
  { done. }
  iApply "HΦ". done.
Qed.

End proof.
