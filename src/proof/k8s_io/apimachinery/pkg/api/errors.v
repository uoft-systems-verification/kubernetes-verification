From New.proof.k8s_io.apimachinery.pkg.api Require Export errors_init.
From New.proof.k8s_io.apimachinery.pkg.runtime Require Import schema_init.
From New.proof Require Import prelude empty_ffi.

(* [StatusError] and the Kubernetes API error helpers are external to the
   executable model.  These predicates record the semantic classes exposed by
   the corresponding Kubernetes error classifiers, independently of the
   physical StatusError encoding. *)
Axiom conflict_error: interface.t → Prop.
Axiom conflict_error_dec: ∀ err, Decision (conflict_error err).
Global Existing Instance conflict_error_dec.
Axiom conflict_error_not_nil:
  ∀ err, conflict_error err → err ≠ interface.nil.

Axiom not_found_error: interface.t → Prop.
Axiom not_found_error_dec: ∀ err, Decision (not_found_error err).
Global Existing Instance not_found_error_dec.
Axiom not_found_error_not_nil:
  ∀ err, not_found_error err → err ≠ interface.nil.

Lemma conflict_error_nil : ¬ conflict_error interface.nil.
Proof.
  intros Hconflict.
  apply (conflict_error_not_nil interface.nil Hconflict).
  done.
Qed.

Lemma not_found_error_nil : ¬ not_found_error interface.nil.
Proof.
  intros Hnot_found.
  apply (not_found_error_not_nil interface.nil Hnot_found).
  done.
Qed.

(* Keep the package modules qualified to distinguish them from this proof
   file's unqualified semantic predicates. *)
Module api_errors_pkg := code.k8s_io.apimachinery.pkg.api.errors.pkg_id.
Module api_errors := code.k8s_io.apimachinery.pkg.api.errors.errors.

Section proof.
Context `{hG: !heapGS Σ} `{!ffi_semantics _ _}.
Context {sem : go.Semantics}.
Local Set Default Proof Using "All".

Lemma wp_IsNotFound err:
  {{{ is_pkg_init api_errors_pkg.errors }}}
    @! api_errors.IsNotFound #err
  {{{ RET (#(bool_decide (not_found_error err)));
      True%I
  }}}.
Proof.
Admitted.

Lemma wp_IsConflict err:
  {{{ is_pkg_init api_errors_pkg.errors }}}
    @! api_errors.IsConflict #err
  {{{ RET (#(bool_decide (conflict_error err)));
      True%I
  }}}.
Proof.
Admitted.

(* Trusted boundary for the untranslated Kubernetes StatusError
   representation and constructor. *)
Lemma wp_NewNotFound (resource : schema.GroupResource.t) (name : go_string) :
  {{{ is_pkg_init api_errors_pkg.errors }}}
    @! api_errors.NewNotFound #resource #name
  {{{ (err_l : loc), RET #err_l;
      ⌜ not_found_error
          (interface.mk_ok (go.PointerType api_errors.StatusError) #err_l) ⌝
  }}}.
Proof.
Admitted.

(* Trusted boundary for the untranslated Kubernetes StatusError
   representation and constructor. *)
Lemma wp_NewConflict (resource : schema.GroupResource.t) (name : go_string)
    (cause : error.t) :
  {{{ is_pkg_init api_errors_pkg.errors }}}
    @! api_errors.NewConflict #resource #name #cause
  {{{ (err_l : loc), RET #err_l;
      ⌜ conflict_error
          (interface.mk_ok (go.PointerType api_errors.StatusError) #err_l) ⌝
  }}}.
Proof.
Admitted.

End proof.
