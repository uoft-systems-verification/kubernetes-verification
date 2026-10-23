From New.proof Require Import prelude empty_ffi.
From Ltac2 Require Import Ltac2.
Set Default Proof Mode "Classic".
Import environments.

(** Pure execution with an unchanged proof-mode context. The usual rule
    searches every hypothesis for laters at every step, which is expensive
    for recursive ownership predicates and large atomic-update contracts. *)
Section steps.
Context `{ffi_sem: ffi_semantics} `{!ffi_interp ffi} `{!gooseGlobalGS Σ, !gooseLocalGS Σ}.
Context {go_gctx : GoGlobalContext}.

Lemma tac_wp_pure_keep K e1 {e2 φ} (Hwp : PureWp φ e1 e2) Δ s E Φ :
  φ →
  envs_entails Δ (WP (fill K e2) @ s; E {{ Φ }}) →
  envs_entails Δ (WP (fill K e1) @ s; E {{ Φ }}).
Proof.
  rewrite envs_entails_unseal => Hφ HΔ.
  rewrite HΔ. iIntros "H". iApply Hwp; first done.
  iNext. iIntros "_". iExact "H".
Qed.
End steps.

Ltac2 wp_pure_keep_visit e k :=
  let pure_wp := orelse (fun () => '(ltac:(tc_solve) : PureWp _ $e _))
                       (fun _ => Control.zero Walk_expr_more) in
  eapply (tac_wp_pure_keep $k $e $pure_wp) >
    [ltac1:(try done) |
     ltac1:(reduction.pm_prettify; simpl subst'; simpl fill)].

Ltac2 wp_pure_keep () :=
  lazy_match! goal with
  | [ |- envs_entails _ (wp _ _ (Val _) _) ] => ltac1:(iApply wp_value)
  | [ |- envs_entails _ (wp _ _ ?e _) ] =>
      wp_walk_unwrap (fun () => walk_expr e wp_pure_keep_visit) "wp_pure_keep: no pure step"
  | [ |- _ ] => Control.backtrack_tactic_failure "wp_pure_keep: not a WP"
  end.

Tactic Notation "wp_pure_keep" := ltac2:(Control.enter wp_pure_keep).
Tactic Notation "wp_pures_keep" := repeat (wp_pure_keep; []).

(** Opt-in variant of [wp_auto]. Existing hypotheses keep their laters;
    use [wp_auto], [wp_pures], or [iNext] when those laters must be removed.
    Load, store, allocation, and unused-points-to handling are unchanged. *)
Ltac2 wp_auto_keep () :=
  progress (repeat (first [wp_pure_keep () | wp_load () | wp_store () | wp_alloc_auto () |
                          ltac1:(progress wp_clear_unused_pointsto)])).

Tactic Notation "wp_auto_keep" := ltac2:(Control.enter wp_auto_keep).
