From New.proof Require Import prelude empty_ffi.
From New.golang.theory Require Import auto.
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

(** [wp_apply] runs [wp_auto] even when the surrounding proof uses
    [wp_auto_keep]. Use the same application and introduction machinery, but
    keep existing laters during the automatic execution after the call.
    This is opt-in: importing this file does not change [wp_apply].
    [as] and [--no-auto] work as usual; generating later credits requires
    the ordinary [wp_apply --lc]. *)
Tactic Notation "wp_apply_keep" open_constr(lem) tactic1_list(ps) :=
  let f := ltac2:(lem ps_raw |-
    let run_auto := Ref.ref wp_apply_auto_default in
    let as_clause := Ref.ref None in
    let ps := Option.get (Ltac1.to_list ps_raw) in
    List.iter (fun p =>
      match catch_wp_param (fun () => Ltac1.run p) with
      | RunAuto b => Ref.set run_auto b
      | AsClause cl => Ref.set as_clause (Some cl)
      | GenLc _ =>
          Control.throw (Invalid_argument
            (Some (Message.of_string "Use wp_apply --lc to generate later credits")))
      end
    ) ps;
    wp_apply lem false 0 (Ref.get as_clause);
    if Ref.get run_auto then focus_last (try (wp_auto_keep ())) else ()
  ) in
  f lem ps.

(** Loop and branch tactics also invoke [wp_auto] internally. Keep the same
    control-flow rules and Boolean simplifications without stripping laters. *)
Ltac wp_for_keep_cleanup :=
  try wp_auto_keep;
  cleanup_bool_decide;
  try wp_auto_keep.

Tactic Notation "wp_for_keep" :=
  loop.wp_for_core; wp_for_keep_cleanup.
Tactic Notation "wp_for_keep" constr(hyp) :=
  loop.wp_for_core; iNamed hyp; wp_for_keep_cleanup.

Ltac wp_if_destruct_keep :=
  lazymatch goal with
  | |- environments.envs_entails _ ?g =>
      match g with
      | context[bool_decide ?b] =>
          destruct (bool_decide_reflect b); subst;
          wp_pures_keep;
          cleanup_bool_decide;
          try wp_auto_keep;
          cleanup_bool_decide
      | context[@into_val _ _ bool ?b] =>
          is_var b; destruct b;
          cleanup_bool_decide;
          try wp_auto_keep;
          cleanup_bool_decide
      | context[@into_val _ _ bool (negb ?b)] =>
          is_var b; destruct b;
          cleanup_bool_decide;
          try wp_auto_keep;
          cleanup_bool_decide
      end
  end.
