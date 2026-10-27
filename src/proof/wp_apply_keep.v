From New.proof Require Export wp_keep.
From New.golang.theory Require Import auto.
From Ltac2 Require Import Ltac2.
Set Default Proof Mode "Classic".

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
