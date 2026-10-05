From New.proof Require Import prelude empty_ffi.
From New.proof.k8s_io.utils Require Export ptr_init.

Section proof.
Context `{hG: !heapGS Σ} `{!ffi_semantics _ _}.
Context {sem : go.Semantics} {package_sem : ptr.Assumptions}.
Collection W := sem + package_sem.

(* An optional pointer such as [*int32]: a readable cell or nil. *)
Definition opt_ptr_rep {V} `{!TypedPointsto (Σ:=Σ) V} (p : loc) (o : option V) dq : iProp Σ :=
  match o with
  | Some v => p ↦{dq} v
  | None => ⌜ p = null ⌝
  end.

#[global] Instance opt_ptr_rep_persistent {V} `{!TypedPointsto (Σ:=Σ) V} p (o : option V) :
  Persistent (opt_ptr_rep p o DfracDiscarded).
Proof. rewrite /opt_ptr_rep. destruct o; apply _. Qed.

(* [Equal] is generic, but stepping its final comparison needs a concrete
   comparable type, so the spec is stated per element type. *)
Lemma wp_Equal_int32 (a b : loc) (oa ob : option w32) dqa dqb :
  {{{ opt_ptr_rep a oa dqa ∗ opt_ptr_rep b ob dqb }}}
    #(functions ptr.Equal [go.int32]) #a #b
  {{{ (r : bool), RET #r; opt_ptr_rep a oa dqa ∗ opt_ptr_rep b ob dqb }}}.
Proof using W.
  iIntros (Φ) "[Ha Hb] HΦ".
  wp_func_call. rewrite /ptr.Equalⁱᵐᵖˡ. wp_call. wp_auto.
  destruct oa as [na|]; destruct ob as [nb|]; rewrite /opt_ptr_rep.
  - iDestruct (typed_pointsto_not_null with "Ha") as %Ha.
    iDestruct (typed_pointsto_not_null with "Hb") as %Hb.
    rewrite (bool_decide_false (a = null)) // (bool_decide_false (b = null)) //.
    wp_auto. rewrite (bool_decide_false (a = null)) //. wp_auto. iApply "HΦ". iFrame.
  - iDestruct "Hb" as %->. iDestruct (typed_pointsto_not_null with "Ha") as %Ha.
    rewrite (bool_decide_false (a = null)) // (bool_decide_true (null = null)) //.
    wp_auto. iApply "HΦ". iFrame. done.
  - iDestruct "Ha" as %->. iDestruct (typed_pointsto_not_null with "Hb") as %Hb.
    rewrite (bool_decide_false (b = null)) // (bool_decide_true (null = null)) //.
    wp_auto. iApply "HΦ". iFrame. done.
  - iDestruct "Ha" as %->. iDestruct "Hb" as %->.
    rewrite (bool_decide_true (null = null)) //.
    wp_auto. iApply "HΦ". done.
Qed.

End proof.
