From New.proof Require Import prelude empty_ffi.
From New.proof.kubernetes_model Require Export common.

(* Lightweight infrastructure shared by the Delete variants and updates
   whose success path may remove an object. *)

Section proof.
Context `{hG: !heapGS Σ} `{!ffi_semantics _ _}.
Context {sem : go.Semantics} {package_sem : apimodel.Assumptions}.
Local Set Default Proof Using "All".

Definition delete_preconditions_match (options : DeleteOptionsV.t) (m : ObjectMetaV.t) : Prop :=
  match options.(DeleteOptionsV.Preconditions') with
  | None => True
  | Some preconditions =>
      (match preconditions.(PreconditionsV.UID') with
       | Some uid => uid = m.(ObjectMetaV.UID')
       | None => True
       end) ∧
      (match preconditions.(PreconditionsV.ResourceVersion') with
       | Some rv => rv = m.(ObjectMetaV.ResourceVersion')
       | None => True
       end)
  end.

#[global] Instance delete_preconditions_match_dec options m :
  Decision (delete_preconditions_match options m).
Proof.
  unfold delete_preconditions_match.
  destruct options.(DeleteOptionsV.Preconditions') as [preconditions|].
  - destruct preconditions.(PreconditionsV.UID') as [uid|];
      destruct preconditions.(PreconditionsV.ResourceVersion') as [rv|];
      simpl.
    + destruct (decide (uid = m.(ObjectMetaV.UID'))) as [Huid|Huid];
        destruct (decide (rv = m.(ObjectMetaV.ResourceVersion'))) as [Hrv|Hrv].
      * left. split; assumption.
      * right. intros [_ Hrv']. contradiction.
      * right. intros [Huid' _]. contradiction.
      * right. intros [Huid' _]. contradiction.
    + destruct (decide (uid = m.(ObjectMetaV.UID'))) as [Huid|Huid].
      * left. split; [assumption|done].
      * right. intros [Huid' _]. contradiction.
    + destruct (decide (rv = m.(ObjectMetaV.ResourceVersion'))) as [Hrv|Hrv].
      * left. split; [done|assumption].
      * right. intros [_ Hrv']. contradiction.
    + left. done.
  - left. done.
Qed.

(* [ValidateDeleteOptions] is part of the untranslated Kubernetes validation
   package.  [DeleteOptionsV.valid] is its pure-model counterpart. *)
Axiom ErrorList_underlying_slice :
  field.ErrorList ↓u go.SliceType (go.PointerType field.Error).
#[local] Existing Instance ErrorList_underlying_slice.

Axiom wp_ValidateDeleteOptions_valid : ∀ l options dq,
  {{{ is_pkg_init apimodel ∗
      DeleteOptionsV.deepown_l l options dq ∗
      ⌜ DeleteOptionsV.valid options ⌝
  }}}
    @! v1_validation.ValidateDeleteOptions #l
  {{{ (errs : field.ErrorList.t), RET #errs;
      ⌜ (#errs : val) = #slice.nil ⌝ ∗
      DeleteOptionsV.deepown_l l options dq
  }}}.

Lemma wp_validateDeleteOptions l options dq :
  {{{ is_pkg_init apimodel ∗
      "Hdeepown_l" ∷ DeleteOptionsV.deepown_l l options dq ∗
      "%Hvalid" ∷ ⌜ DeleteOptionsV.valid options ⌝
  }}}
    @! apimodel.validateDeleteOptions #l
  {{{ RET #interface.nil;
      DeleteOptionsV.deepown_l l options dq
  }}}.
Proof.
  wp_start as "H".
  iNamed "H".
  wp_auto.
  wp_apply (wp_ValidateDeleteOptions_valid with "[$Hdeepown_l]").
  { iFrame "#". done. }
  iIntros (errs) "(%Herrs_nil & Hdeepown_l)".
  wp_auto.
  rewrite Herrs_nil.
  wp_auto.
  iApply "HΦ".
  iFrame.
Qed.

Lemma wp_validateDeletePreconditions i l m options_l options dq (kind : go_string) :
  {{{ is_pkg_init apimodel ∗
      "%Hi" ∷ ⌜ i = interface.mk (go.PointerType v1.ObjectMeta) #l ⌝ ∗
      "Hdeepown_m_l" ∷ ObjectMetaV.deepown_l l m dq ∗
      "Hdeepown_options_l" ∷ DeleteOptionsV.deepown_l options_l options dq
  }}}
    @! apimodel.validateDeletePreconditions #(interface.ok i) #options_l #kind
  {{{ err, RET #err;
      ⌜ delete_preconditions_match options m ∧ err = interface.nil
        ∨
        ¬ delete_preconditions_match options m ∧
          err ≠ interface.nil ∧
          conflict_error err ⌝ ∗
      ObjectMetaV.deepown_l l m dq ∗
      DeleteOptionsV.deepown_l options_l options dq
  }}}.
Proof.
  wp_start as "H".
  iNamed "H". subst i.
  iDestruct "Hdeepown_options_l" as (options_c) "[Hoptions_l Hdeepown_options]".
  iNamed "Hdeepown_options".
  destruct options.(DeleteOptionsV.Preconditions') as [preconditions|]
    eqn:Hpreconditions.
  - iDestruct "Hdeepown_preconditions_some" as (preconditions_c)
      "[Hpreconditions_l Hdeepown_preconditions]".
    iNamed "Hdeepown_preconditions".
    assert (v1.DeleteOptions.Preconditions' options_c ≠ null)
      as Hpreconditions_not_null.
    { intros Hnull.
      apply (proj1 Hdeepown_preconditions_none) in Hnull.
      congruence. }
    assert (bool_decide
      (v1.DeleteOptions.Preconditions' options_c = null) = false)
      as Hpreconditions_nonnull_decide.
    { apply bool_decide_false. done. }
    wp_auto.
    rewrite Hpreconditions_nonnull_decide /=.
    wp_auto.
    destruct preconditions.(PreconditionsV.UID') as [uid|] eqn:Huid.
    + iDestruct "Hdeepown_uid_some" as (uid_c) "[Huid_l ->]".
      assert (v1.Preconditions.UID' preconditions_c ≠ null)
        as Huid_not_null.
      { intros Hnull.
        apply (proj1 Hdeepown_uid_none) in Hnull.
        congruence. }
      assert (bool_decide (v1.Preconditions.UID' preconditions_c = null) = false)
        as Huid_nonnull_decide.
      { apply bool_decide_false. done. }
      rewrite Huid_nonnull_decide /=.
      wp_auto.
      wp_apply (v1.wp_GetUID_deepown with "[$Hdeepown_m_l]").
      iIntros "Hdeepown_m_l".
      wp_auto.
      wp_if_destruct.
      * iAssert ((match preconditions.(PreconditionsV.UID') with
          | Some uid' => ∃ uid_c',
              v1.Preconditions.UID' preconditions_c ↦{dq} uid_c' ∗
              ⌜ uid_c' = uid' ⌝
          | None => True
          end)%I) with "[Huid_l]" as "Hdeepown_uid_some".
        { rewrite Huid /=. iExists m.(ObjectMetaV.UID'). iFrame. done. }
        destruct preconditions.(PreconditionsV.ResourceVersion') as [rv|]
          eqn:Hrv.
        -- iDestruct "Hdeepown_resourceversion_some" as (rv_c) "[Hrv_l ->]".
           assert (v1.Preconditions.ResourceVersion' preconditions_c ≠ null)
             as Hrv_not_null.
           { intros Hnull.
             apply (proj1 Hdeepown_resourceversion_none) in Hnull.
             congruence. }
           assert (bool_decide
             (v1.Preconditions.ResourceVersion' preconditions_c = null) = false)
             as Hrv_nonnull_decide.
           { apply bool_decide_false. done. }
           rewrite Hrv_nonnull_decide /=.
           wp_auto.
           wp_apply (v1.wp_GetResourceVersion_deepown with "[$Hdeepown_m_l]").
           iIntros "Hdeepown_m_l".
           wp_auto.
           wp_if_destruct.
           ++ iAssert ((match preconditions.(PreconditionsV.ResourceVersion') with
                | Some rv' => ∃ rv_c',
                    v1.Preconditions.ResourceVersion' preconditions_c ↦{dq} rv_c' ∗
                    ⌜ rv_c' = rv' ⌝
                | None => True
                end)%I) with "[Hrv_l]" as "Hdeepown_resourceversion_some".
              { rewrite Hrv /=.
                iExists m.(ObjectMetaV.ResourceVersion'). iFrame. done. }
              iAssert (PreconditionsV.deepown preconditions_c preconditions dq)
                with "[Hdeepown_uid_some Hdeepown_resourceversion_some]"
                as "Hdeepown_preconditions".
              { rewrite /PreconditionsV.deepown Huid Hrv /=.
                iFrame. iPureIntro. done. }
              iAssert ((match options.(DeleteOptionsV.Preconditions') with
                | Some preconditions' => ∃ preconditions_c',
                    v1.DeleteOptions.Preconditions' options_c ↦{dq} preconditions_c' ∗
                    PreconditionsV.deepown preconditions_c' preconditions' dq
                | None => True
                end)%I) with "[Hpreconditions_l Hdeepown_preconditions]"
                as "Hdeepown_preconditions_some".
              { rewrite Hpreconditions /=.
                iExists preconditions_c. iFrame. }
              iAssert (DeleteOptionsV.deepown options_c options dq)
                with "[Hdeepown_graceperiodseconds_some Hdeepown_preconditions_some Hdeepown_orphandependents_some Hdeepown_propagationpolicy_some]"
                as "Hdeepown_options".
              { rewrite /DeleteOptionsV.deepown Hpreconditions /=.
                iFrame. iPureIntro. done. }
              iApply "HΦ". iFrame. iPureIntro.
              left. split; [|done].
              rewrite /delete_preconditions_match Hpreconditions Huid Hrv /=.
              done.
           ++ wp_apply (v1.wp_GetName_deepown with "[$Hdeepown_m_l]").
              iIntros "Hdeepown_m_l".
              wp_auto.
              wp_apply (v1.wp_GetResourceVersion_deepown with "[$Hdeepown_m_l]").
              iIntros "Hdeepown_m_l".
              wp_auto.
              wp_apply wp_newPreconditionRVConflictError.
              iIntros (err) "%Hconflict".
              wp_auto.
              iAssert ((match preconditions.(PreconditionsV.ResourceVersion') with
                | Some rv' => ∃ rv_c',
                    v1.Preconditions.ResourceVersion' preconditions_c ↦{dq} rv_c' ∗
                    ⌜ rv_c' = rv' ⌝
                | None => True
                end)%I) with "[Hrv_l]" as "Hdeepown_resourceversion_some".
              { rewrite Hrv /=. iExists rv. iFrame. done. }
              iAssert (PreconditionsV.deepown preconditions_c preconditions dq)
                with "[Hdeepown_uid_some Hdeepown_resourceversion_some]"
                as "Hdeepown_preconditions".
              { rewrite /PreconditionsV.deepown Huid Hrv /=.
                iFrame. iPureIntro. done. }
              iAssert ((match options.(DeleteOptionsV.Preconditions') with
                | Some preconditions' => ∃ preconditions_c',
                    v1.DeleteOptions.Preconditions' options_c ↦{dq} preconditions_c' ∗
                    PreconditionsV.deepown preconditions_c' preconditions' dq
                | None => True
                end)%I) with "[Hpreconditions_l Hdeepown_preconditions]"
                as "Hdeepown_preconditions_some".
              { rewrite Hpreconditions /=.
                iExists preconditions_c. iFrame. }
              iAssert (DeleteOptionsV.deepown options_c options dq)
                with "[Hdeepown_graceperiodseconds_some Hdeepown_preconditions_some Hdeepown_orphandependents_some Hdeepown_propagationpolicy_some]"
                as "Hdeepown_options".
              { rewrite /DeleteOptionsV.deepown Hpreconditions /=.
                iFrame. iPureIntro. done. }
              iApply "HΦ". iFrame. iPureIntro.
              right. split.
              { rewrite /delete_preconditions_match Hpreconditions Huid Hrv /=.
                intuition. }
              split; [exact (conflict_error_not_nil err Hconflict)|done].
        -- assert (v1.Preconditions.ResourceVersion' preconditions_c = null)
             as Hrv_null.
           { apply (proj2 Hdeepown_resourceversion_none). done. }
           assert (bool_decide
             (v1.Preconditions.ResourceVersion' preconditions_c = null) = true)
             as Hrv_null_decide.
           { apply bool_decide_true. done. }
           rewrite Hrv_null_decide /=.
           wp_auto.
           iAssert (PreconditionsV.deepown preconditions_c preconditions dq)
             with "[Hdeepown_uid_some Hdeepown_resourceversion_some]"
             as "Hdeepown_preconditions".
           { rewrite /PreconditionsV.deepown Huid Hrv /=.
             iFrame. iPureIntro. done. }
           iAssert ((match options.(DeleteOptionsV.Preconditions') with
             | Some preconditions' => ∃ preconditions_c',
                 v1.DeleteOptions.Preconditions' options_c ↦{dq} preconditions_c' ∗
                 PreconditionsV.deepown preconditions_c' preconditions' dq
             | None => True
             end)%I) with "[Hpreconditions_l Hdeepown_preconditions]"
             as "Hdeepown_preconditions_some".
           { rewrite Hpreconditions /=.
             iExists preconditions_c. iFrame. }
           iAssert (DeleteOptionsV.deepown options_c options dq)
             with "[Hdeepown_graceperiodseconds_some Hdeepown_preconditions_some Hdeepown_orphandependents_some Hdeepown_propagationpolicy_some]"
             as "Hdeepown_options".
           { rewrite /DeleteOptionsV.deepown Hpreconditions /=.
             iFrame. iPureIntro. done. }
           iApply "HΦ". iFrame. iPureIntro.
           left. split; [|done].
           rewrite /delete_preconditions_match Hpreconditions Huid Hrv /=.
           done.
      * wp_apply (v1.wp_GetName_deepown with "[$Hdeepown_m_l]").
        iIntros "Hdeepown_m_l".
        wp_auto.
        wp_apply (v1.wp_GetUID_deepown with "[$Hdeepown_m_l]").
        iIntros "Hdeepown_m_l".
        wp_auto.
        wp_apply wp_newPreconditionUIDConflictError.
        iIntros (err) "%Hconflict".
        wp_auto.
        iAssert ((match preconditions.(PreconditionsV.UID') with
          | Some uid' => ∃ uid_c',
              v1.Preconditions.UID' preconditions_c ↦{dq} uid_c' ∗
              ⌜ uid_c' = uid' ⌝
          | None => True
          end)%I) with "[Huid_l]" as "Hdeepown_uid_some".
        { rewrite Huid /=. iExists uid. iFrame. done. }
        iAssert (PreconditionsV.deepown preconditions_c preconditions dq)
          with "[Hdeepown_uid_some Hdeepown_resourceversion_some]"
          as "Hdeepown_preconditions".
        { rewrite /PreconditionsV.deepown Huid /=.
          iFrame. iPureIntro. done. }
        iAssert ((match options.(DeleteOptionsV.Preconditions') with
          | Some preconditions' => ∃ preconditions_c',
              v1.DeleteOptions.Preconditions' options_c ↦{dq} preconditions_c' ∗
              PreconditionsV.deepown preconditions_c' preconditions' dq
          | None => True
          end)%I) with "[Hpreconditions_l Hdeepown_preconditions]"
          as "Hdeepown_preconditions_some".
        { rewrite Hpreconditions /=.
          iExists preconditions_c. iFrame. }
        iAssert (DeleteOptionsV.deepown options_c options dq)
          with "[Hdeepown_graceperiodseconds_some Hdeepown_preconditions_some Hdeepown_orphandependents_some Hdeepown_propagationpolicy_some]"
          as "Hdeepown_options".
        { rewrite /DeleteOptionsV.deepown Hpreconditions /=.
          iFrame. iPureIntro. done. }
        iApply "HΦ". iFrame. iPureIntro.
        right. split.
        { rewrite /delete_preconditions_match Hpreconditions Huid /=.
          intros [Huid_match _]. done. }
        split; [exact (conflict_error_not_nil err Hconflict)|done].
    + assert (v1.Preconditions.UID' preconditions_c = null) as Huid_null.
      { apply (proj2 Hdeepown_uid_none). done. }
      assert (bool_decide (v1.Preconditions.UID' preconditions_c = null) = true)
        as Huid_null_decide.
      { apply bool_decide_true. done. }
      rewrite Huid_null_decide /=.
      wp_auto.
      destruct preconditions.(PreconditionsV.ResourceVersion') as [rv|]
        eqn:Hrv.
      * iDestruct "Hdeepown_resourceversion_some" as (rv_c) "[Hrv_l ->]".
        assert (v1.Preconditions.ResourceVersion' preconditions_c ≠ null)
          as Hrv_not_null.
        { intros Hnull.
          apply (proj1 Hdeepown_resourceversion_none) in Hnull.
          congruence. }
        assert (bool_decide
          (v1.Preconditions.ResourceVersion' preconditions_c = null) = false)
          as Hrv_nonnull_decide.
        { apply bool_decide_false. done. }
        rewrite Hrv_nonnull_decide /=.
        wp_auto.
        wp_apply (v1.wp_GetResourceVersion_deepown with "[$Hdeepown_m_l]").
        iIntros "Hdeepown_m_l".
        wp_auto.
        wp_if_destruct.
        -- iAssert ((match preconditions.(PreconditionsV.ResourceVersion') with
             | Some rv' => ∃ rv_c',
                 v1.Preconditions.ResourceVersion' preconditions_c ↦{dq} rv_c' ∗
                 ⌜ rv_c' = rv' ⌝
             | None => True
             end)%I) with "[Hrv_l]" as "Hdeepown_resourceversion_some".
           { rewrite Hrv /=.
             iExists m.(ObjectMetaV.ResourceVersion'). iFrame. done. }
           iAssert (PreconditionsV.deepown preconditions_c preconditions dq)
             with "[Hdeepown_uid_some Hdeepown_resourceversion_some]"
             as "Hdeepown_preconditions".
           { rewrite /PreconditionsV.deepown Huid Hrv /=.
             iFrame. iPureIntro. done. }
           iAssert ((match options.(DeleteOptionsV.Preconditions') with
             | Some preconditions' => ∃ preconditions_c',
                 v1.DeleteOptions.Preconditions' options_c ↦{dq} preconditions_c' ∗
                 PreconditionsV.deepown preconditions_c' preconditions' dq
             | None => True
             end)%I) with "[Hpreconditions_l Hdeepown_preconditions]"
             as "Hdeepown_preconditions_some".
           { rewrite Hpreconditions /=.
             iExists preconditions_c. iFrame. }
           iAssert (DeleteOptionsV.deepown options_c options dq)
             with "[Hdeepown_graceperiodseconds_some Hdeepown_preconditions_some Hdeepown_orphandependents_some Hdeepown_propagationpolicy_some]"
             as "Hdeepown_options".
           { rewrite /DeleteOptionsV.deepown Hpreconditions /=.
             iFrame. iPureIntro. done. }
           iApply "HΦ". iFrame. iPureIntro.
           left. split; [|done].
           rewrite /delete_preconditions_match Hpreconditions Huid Hrv /=.
           done.
        -- wp_apply (v1.wp_GetName_deepown with "[$Hdeepown_m_l]").
           iIntros "Hdeepown_m_l".
           wp_auto.
           wp_apply (v1.wp_GetResourceVersion_deepown with "[$Hdeepown_m_l]").
           iIntros "Hdeepown_m_l".
           wp_auto.
           wp_apply wp_newPreconditionRVConflictError.
           iIntros (err) "%Hconflict".
           wp_auto.
           iAssert ((match preconditions.(PreconditionsV.ResourceVersion') with
             | Some rv' => ∃ rv_c',
                 v1.Preconditions.ResourceVersion' preconditions_c ↦{dq} rv_c' ∗
                 ⌜ rv_c' = rv' ⌝
             | None => True
             end)%I) with "[Hrv_l]" as "Hdeepown_resourceversion_some".
           { rewrite Hrv /=. iExists rv. iFrame. done. }
           iAssert (PreconditionsV.deepown preconditions_c preconditions dq)
             with "[Hdeepown_uid_some Hdeepown_resourceversion_some]"
             as "Hdeepown_preconditions".
           { rewrite /PreconditionsV.deepown Huid Hrv /=.
             iFrame. iPureIntro. done. }
           iAssert ((match options.(DeleteOptionsV.Preconditions') with
             | Some preconditions' => ∃ preconditions_c',
                 v1.DeleteOptions.Preconditions' options_c ↦{dq} preconditions_c' ∗
                 PreconditionsV.deepown preconditions_c' preconditions' dq
             | None => True
             end)%I) with "[Hpreconditions_l Hdeepown_preconditions]"
             as "Hdeepown_preconditions_some".
           { rewrite Hpreconditions /=.
             iExists preconditions_c. iFrame. }
           iAssert (DeleteOptionsV.deepown options_c options dq)
             with "[Hdeepown_graceperiodseconds_some Hdeepown_preconditions_some Hdeepown_orphandependents_some Hdeepown_propagationpolicy_some]"
             as "Hdeepown_options".
           { rewrite /DeleteOptionsV.deepown Hpreconditions /=.
             iFrame. iPureIntro. done. }
           iApply "HΦ". iFrame. iPureIntro.
           right. split.
           { rewrite /delete_preconditions_match Hpreconditions Huid Hrv /=.
             intuition. }
           split; [exact (conflict_error_not_nil err Hconflict)|done].
      * assert (v1.Preconditions.ResourceVersion' preconditions_c = null)
          as Hrv_null.
        { apply (proj2 Hdeepown_resourceversion_none). done. }
        assert (bool_decide
          (v1.Preconditions.ResourceVersion' preconditions_c = null) = true)
          as Hrv_null_decide.
        { apply bool_decide_true. done. }
        rewrite Hrv_null_decide /=.
        wp_auto.
        iAssert (PreconditionsV.deepown preconditions_c preconditions dq)
          with "[Hdeepown_uid_some Hdeepown_resourceversion_some]"
          as "Hdeepown_preconditions".
        { rewrite /PreconditionsV.deepown Huid Hrv /=.
          iFrame. iPureIntro. done. }
        iAssert ((match options.(DeleteOptionsV.Preconditions') with
          | Some preconditions' => ∃ preconditions_c',
              v1.DeleteOptions.Preconditions' options_c ↦{dq} preconditions_c' ∗
              PreconditionsV.deepown preconditions_c' preconditions' dq
          | None => True
          end)%I) with "[Hpreconditions_l Hdeepown_preconditions]"
          as "Hdeepown_preconditions_some".
        { rewrite Hpreconditions /=.
          iExists preconditions_c. iFrame. }
        iAssert (DeleteOptionsV.deepown options_c options dq)
          with "[Hdeepown_graceperiodseconds_some Hdeepown_preconditions_some Hdeepown_orphandependents_some Hdeepown_propagationpolicy_some]"
          as "Hdeepown_options".
        { rewrite /DeleteOptionsV.deepown Hpreconditions /=.
          iFrame. iPureIntro. done. }
        iApply "HΦ". iFrame. iPureIntro.
        left. split; [|done].
        rewrite /delete_preconditions_match Hpreconditions Huid Hrv /=.
        done.
  - assert (v1.DeleteOptions.Preconditions' options_c = null)
      as Hpreconditions_null.
    { apply (proj2 Hdeepown_preconditions_none). done. }
    assert (bool_decide
      (v1.DeleteOptions.Preconditions' options_c = null) = true)
      as Hpreconditions_null_decide.
    { apply bool_decide_true. done. }
    wp_auto.
    rewrite Hpreconditions_null_decide /=.
    wp_auto.
    iAssert (DeleteOptionsV.deepown options_c options dq)
      with "[Hdeepown_graceperiodseconds_some Hdeepown_preconditions_some Hdeepown_orphandependents_some Hdeepown_propagationpolicy_some]"
      as "Hdeepown_options".
    { rewrite /DeleteOptionsV.deepown Hpreconditions /=.
      iFrame. iPureIntro. done. }
    iApply "HΦ". iFrame. iPureIntro.
    left. split; [rewrite /delete_preconditions_match Hpreconditions /=; done|done].
Qed.

(* delete_graceful and delete_pending_graceful abstract the result of checkGracefulDelete *)
Axiom delete_graceful : KObjectV.t -> DeleteOptionsV.t -> bool.
Axiom delete_pending_graceful : KObjectV.t -> bool.
Axiom delete_new_grace_period_seconds : KObjectV.t -> DeleteOptionsV.t -> option w64.

Lemma wp_checkGracefulDelete i l o options_l options :
  {{{ is_pkg_init apimodel ∗
      "%Hvalid_i" ∷ ⌜ KObjectV.valid_interface i l o ⌝ ∗
      "Hdeepown_l" ∷ KObjectV.deepown_l l o 1 ∗
      "Hdeepown_options_l" ∷ DeleteOptionsV.deepown_l options_l options 1
  }}}
    @! apimodel.checkGracefulDelete #(interface.ok i) #options_l
  {{{ graceful pendingGraceful options',
      RET (#graceful, #pendingGraceful, #interface.nil);
      KObjectV.deepown_l l o 1 ∗
      DeleteOptionsV.deepown_l options_l options' 1 ∗
      ⌜ pendingGraceful = true → (KObjectV.objectmeta o).(ObjectMetaV.DeletionTimestamp') ≠ None ⌝ ∗
      ⌜ graceful = delete_graceful o options ⌝ ∗
      ⌜ pendingGraceful = delete_pending_graceful o ⌝ ∗
      ⌜ options' = (options <| DeleteOptionsV.GracePeriodSeconds' := delete_new_grace_period_seconds o options |>) ⌝
  }}}.
Proof.
Admitted.

Definition delete_orphan_finalizer : go_string := "orphan"%go.
Definition delete_foreground_finalizer : go_string := "foregroundDeletion"%go.

(* [true] selects orphan deletion and [false] selects foreground deletion. *)
Fixpoint delete_existing_gc_policy (finalizers : list go_string) : option bool :=
  match finalizers with
  | [] => None
  | finalizer :: finalizers =>
      if decide (finalizer = delete_orphan_finalizer) then Some true
      else if decide (finalizer = delete_foreground_finalizer) then Some false
      else delete_existing_gc_policy finalizers
  end.

Definition delete_gc_policy (m : ObjectMetaV.t) (options : DeleteOptionsV.t) :
    option bool :=
  match options.(DeleteOptionsV.OrphanDependents') with
  | Some true => Some true
  | Some false => None
  | None =>
      match options.(DeleteOptionsV.PropagationPolicy') with
      | Some policy =>
          if decide (policy = "Orphan"%go) then Some true
          else if decide (policy = "Foreground"%go) then Some false
          else if decide (policy = "Background"%go) then None
          else delete_existing_gc_policy (default [] m.(ObjectMetaV.Finalizers'))
      | None => delete_existing_gc_policy (default [] m.(ObjectMetaV.Finalizers'))
      end
  end.

Definition delete_should_orphan_dependents m options : bool :=
  match delete_gc_policy m options with Some true => true | _ => false end.

Definition delete_should_delete_dependents m options : bool :=
  match delete_gc_policy m options with Some false => true | _ => false end.

Definition delete_finalizers_for_gc m options : list go_string :=
  filter
    (fun finalizer =>
      finalizer ≠ delete_orphan_finalizer ∧
      finalizer ≠ delete_foreground_finalizer)
    (default [] m.(ObjectMetaV.Finalizers')) ++
  (if delete_should_orphan_dependents m options
   then [delete_orphan_finalizer] else []) ++
  (if delete_should_delete_dependents m options
   then [delete_foreground_finalizer] else []).

Definition delete_finalizers_changed (old new : list go_string) : Prop :=
  length old ≠ length new ∨ Exists (fun finalizer => finalizer ∉ old) new.

#[global] Instance delete_finalizers_changed_dec old new :
  Decision (delete_finalizers_changed old new) := _.

Definition delete_should_update_finalizers m options : bool :=
  bool_decide (delete_finalizers_changed
    (default [] m.(ObjectMetaV.Finalizers'))
    (delete_finalizers_for_gc m options)).

Definition delete_new_finalizers m options : option (list go_string) :=
  if delete_should_update_finalizers m options
  then Some (delete_finalizers_for_gc m options)
  else m.(ObjectMetaV.Finalizers').

Transparent w8_word_instance.

Lemma delete_orphan_finalizer_valid :
  valid_label_name delete_orphan_finalizer.
Proof.
  left. split; last done.
  rewrite /delete_orphan_finalizer /qualified_name_syntax /=.
  repeat lazymatch goal with | |- _ ∧ _ => split end.
  all: lazymatch goal with
       | |- label_extended_character _ => left
       | |- label_alphanumeric _ => idtac
       end.
  all: unfold label_alphanumeric;
    first [left; cbn; lia | right; left; cbn; lia | right; right; cbn; lia].
Qed.

Lemma delete_foreground_finalizer_valid :
  valid_label_name delete_foreground_finalizer.
Proof.
  left. split; last done.
  rewrite /delete_foreground_finalizer /qualified_name_syntax /=.
  repeat lazymatch goal with | |- _ ∧ _ => split end.
  all: lazymatch goal with
       | |- label_extended_character _ => left
       | |- label_alphanumeric _ => idtac
       end.
  all: unfold label_alphanumeric;
    first [left; cbn; lia | right; left; cbn; lia | right; right; cbn; lia].
Qed.

Lemma delete_gc_finalizers_distinct :
  delete_orphan_finalizer ≠ delete_foreground_finalizer.
Proof. intros Heq. inversion Heq. Qed.

Opaque w8_word_instance.

Lemma delete_finalizers_for_gc_valid m options :
  valid_finalizers m.(ObjectMetaV.Finalizers') →
  valid_finalizers (Some (delete_finalizers_for_gc m options)).
Proof.
  intros Hvalid.
  destruct m.(ObjectMetaV.Finalizers') as [old|] eqn:Hold;
    rewrite /valid_finalizers /= in Hvalid |- *.
  - rewrite /delete_finalizers_for_gc Hold /= !Forall_app.
    clear Hold.
    split; [|split].
    + induction old as [|finalizer finalizers IH]; first constructor.
      inversion Hvalid as [|? ? Hname Hnames]; subst.
      rewrite filter_cons.
      destruct (decide
        (finalizer ≠ delete_orphan_finalizer ∧
         finalizer ≠ delete_foreground_finalizer)); simpl.
      * constructor; [exact Hname|]. exact (IH Hnames).
      * exact (IH Hnames).
    + rewrite /delete_should_orphan_dependents.
      destruct (delete_gc_policy m options) as [[|]|]; simpl.
      * constructor; [exact delete_orphan_finalizer_valid|constructor].
      * constructor.
      * constructor.
    + rewrite /delete_should_delete_dependents.
      destruct (delete_gc_policy m options) as [[|]|]; simpl.
      * constructor.
      * constructor; [exact delete_foreground_finalizer_valid|constructor].
      * constructor.
  - rewrite /delete_finalizers_for_gc Hold /= !Forall_app.
    split.
    + rewrite /delete_should_orphan_dependents.
      destruct (delete_gc_policy m options) as [[|]|]; simpl.
      * constructor; [exact delete_orphan_finalizer_valid|constructor].
      * constructor.
      * constructor.
    + rewrite /delete_should_delete_dependents.
      destruct (delete_gc_policy m options) as [[|]|]; simpl.
      * constructor.
      * constructor; [exact delete_foreground_finalizer_valid|constructor].
      * constructor.
Qed.

Lemma delete_new_finalizers_valid m options :
  valid_finalizers m.(ObjectMetaV.Finalizers') →
  valid_finalizers (delete_new_finalizers m options).
Proof.
  intros Hvalid. rewrite /delete_new_finalizers.
  destruct delete_should_update_finalizers.
  - by apply delete_finalizers_for_gc_valid.
  - exact Hvalid.
Qed.

Lemma delete_finalizer_set_lookup (finalizers : list go_string) finalizer :
  default false
    ((list_to_map ((fun finalizer => (finalizer, true)) <$> finalizers) :
      gmap go_string bool) !! finalizer) =
  bool_decide (finalizer ∈ finalizers).
Proof.
  induction finalizers as [|head finalizers IH].
  - rewrite fmap_nil list_to_map_nil lookup_empty /=. done.
  - rewrite fmap_cons list_to_map_cons.
    destruct (decide (head = finalizer)) as [->|Hneq].
    + rewrite lookup_insert_eq /=. symmetry.
      apply bool_decide_eq_true_2. by left.
    + assert ((<[head := true]>
          (list_to_map ((fun finalizer => (finalizer, true)) <$> finalizers) :
            gmap go_string bool)) !! finalizer =
        (list_to_map ((fun finalizer => (finalizer, true)) <$> finalizers) :
          gmap go_string bool) !! finalizer) as Hlookup.
      { apply lookup_insert_ne. exact Hneq. }
      rewrite Hlookup.
      simpl. rewrite IH.
      apply bool_decide_ext. split.
      * by right.
      * intros Hmember. apply elem_of_cons in Hmember as [Heq|Hin].
        -- exfalso. apply Hneq. by symmetry.
        -- exact Hin.
Qed.

Lemma wp_shouldOrphanDependents metadata_i metadata_l m options_l options dq :
  {{{ is_pkg_init apimodel ∗
      "%Hmetadata" ∷ ⌜ metadata_i = interface.mk (go.PointerType v1.ObjectMeta) #metadata_l ⌝ ∗
      "Hdeepown_m_l" ∷ ObjectMetaV.deepown_l metadata_l m dq ∗
      "Hdeepown_options_l" ∷ DeleteOptionsV.deepown_l options_l options dq
  }}}
    @! apimodel.shouldOrphanDependents #(interface.ok metadata_i) #options_l
  {{{ should_orphan, RET #should_orphan;
      ⌜ should_orphan = delete_should_orphan_dependents m options ⌝ ∗
      ObjectMetaV.deepown_l metadata_l m dq ∗
      DeleteOptionsV.deepown_l options_l options dq
  }}}.
Proof.
  wp_start as "H". iNamed "H". subst metadata_i.
  iDestruct "Hdeepown_options_l" as (options_c) "[Hoptions_l Hoptions]".
  iDestruct (typed_pointsto_not_null with "Hoptions_l") as %Hoptions_l_not_null.
  assert (bool_decide (options_l = null) = false) as Hoptions_nonnull_decide.
  { apply bool_decide_false. done. }
  iNamed "Hoptions".
  destruct options.(DeleteOptionsV.OrphanDependents') as [orphan|] eqn:Horphan.
  - iDestruct "Hdeepown_orphandependents_some" as (orphan_c) "[Horphan_l ->]".
    iDestruct (typed_pointsto_not_null with "Horphan_l") as %Horphan_l_not_null.
    assert (bool_decide
      (v1.DeleteOptions.OrphanDependents' options_c = null) = false)
      as Horphan_nonnull_decide.
    { apply bool_decide_false. done. }
    wp_auto. rewrite Hoptions_nonnull_decide /=. wp_auto.
    rewrite Horphan_nonnull_decide /=. wp_auto.
    iAssert (DeleteOptionsV.deepown options_c options dq)
      with "[Hdeepown_graceperiodseconds_some Hdeepown_preconditions_some
        Horphan_l Hdeepown_propagationpolicy_some]" as "Hoptions".
    { rewrite /DeleteOptionsV.deepown Horphan /=. iFrame.
      iFrame "%"; try (iPureIntro; done). }
    iApply ("HΦ" $! orphan). iFrame. iPureIntro.
    rewrite /delete_should_orphan_dependents /delete_gc_policy Horphan /=.
    by destruct orphan.
  - assert (v1.DeleteOptions.OrphanDependents' options_c = null) as Horphan_null.
    { apply (proj2 Hdeepown_orphandependents_none). done. }
    assert (bool_decide
      (v1.DeleteOptions.OrphanDependents' options_c = null) = true)
      as Horphan_null_decide.
    { apply bool_decide_true. done. }
    wp_auto. rewrite Hoptions_nonnull_decide /=. wp_auto.
    rewrite Horphan_null_decide /=. wp_auto.
    destruct options.(DeleteOptionsV.PropagationPolicy') as [policy|] eqn:Hpolicy.
    + iDestruct "Hdeepown_propagationpolicy_some" as (policy_c) "[Hpolicy_l ->]".
      iDestruct (typed_pointsto_not_null with "Hpolicy_l") as %Hpolicy_l_not_null.
      assert (bool_decide
        (v1.DeleteOptions.PropagationPolicy' options_c = null) = false)
        as Hpolicy_nonnull_decide.
      { apply bool_decide_false. done. }
      rewrite Hoptions_nonnull_decide /=. wp_auto.
      rewrite Hpolicy_nonnull_decide /=. wp_auto.
      iAssert (DeleteOptionsV.deepown options_c options dq)
        with "[Hdeepown_graceperiodseconds_some Hdeepown_preconditions_some
          Hpolicy_l]" as "Hoptions".
      { rewrite /DeleteOptionsV.deepown Horphan Hpolicy /=. iFrame.
        iFrame "%"; try (iPureIntro; done). }
      wp_if_destruct.
      * iApply ("HΦ" $! true). iFrame. iPureIntro.
        rewrite /delete_should_orphan_dependents /delete_gc_policy Horphan Hpolicy /=.
        repeat case_decide; done.
      * wp_if_destruct.
        -- iApply ("HΦ" $! false). iFrame. iPureIntro.
           rewrite /delete_should_orphan_dependents /delete_gc_policy Horphan Hpolicy /=.
           repeat case_decide; done.
        -- wp_if_destruct.
           { iApply ("HΦ" $! false). iFrame. iPureIntro.
             rewrite /delete_should_orphan_dependents /delete_gc_policy
               Horphan Hpolicy /=.
             repeat case_decide; done. }
           { assert (delete_should_orphan_dependents m options =
              match delete_existing_gc_policy
                (default [] m.(ObjectMetaV.Finalizers')) with
              | Some true => true
              | _ => false
             end) as Hshould_fallback.
           { rewrite /delete_should_orphan_dependents /delete_gc_policy
               Horphan Hpolicy /=.
             repeat case_decide; try congruence; done. }
           iDestruct "Hdeepown_m_l" as (metadata_c) "[Hmetadata_l Hmetadata]".
           wp_bind.
           wp_apply (v1.wp_GetFinalizers metadata_l metadata_c dq
             with "[$Hmetadata_l]") as "Hmetadata_l".
           set (sl := metadata_c.(v1.ObjectMeta.Finalizers')).
           iNamed "Hmetadata".
           destruct m.(ObjectMetaV.Finalizers') as [finalizers|] eqn:Hfinalizers.
           ++ iDestruct "Hdeepown_finalizers_some" as (cfinalizers) "[Hsl ->]".
              iAssert ((sl ↦*{dq} finalizers -∗
                ObjectMetaV.deepown_l metadata_l m dq)%I)
                with "[Hmetadata_l Hdeepown_creationtimestamp
                  Hdeepown_deletiontimestamp_some
                  Hdeepown_deletiongraceperiodseconds_some Hdeepown_labels_some
                  Hdeepown_annotations_some Hdeepown_ownerreferences_some
                  Hdeepown_managedfields_some]" as "Hrestore_m".
              { iIntros "Hsl". iExists metadata_c. iFrame.
                rewrite /ObjectMetaV.deepown Hfinalizers /=. iFrame.
                iFrame "%"; try (iPureIntro; done). }
              iDestruct (own_slice_len with "Hsl") as %[Hsl_len _].
              iDestruct (own_slice_wf with "Hsl") as %Hsl_wf.
              set I := (∃ (i : w64) (f : go_string),
                "Hi" ∷ i_ptr ↦ i ∗
                "Hf" ∷ f_ptr ↦ f ∗
                "Hsl" ∷ sl ↦*{dq} finalizers ∗
                "%Hi_bounds" ∷ ⌜ 0 ≤ sint.Z i ≤ sint.Z sl.(slice.len) ⌝ ∗
                "%Hscan" ∷ ⌜ delete_existing_gc_policy
                  (drop (sint.nat i) finalizers) =
                  delete_existing_gc_policy finalizers ⌝)%I.
              iAssert I with "[i f Hsl]" as "Hloop".
              { iExists (W64 0), (zero_val go_string). iFrame.
                iPureIntro. split; [word|done]. }
              wp_for "Hloop". wp_if_destruct.
              ** destruct (decide (0 ≤ sint.Z i < sint.Z sl.(slice.len)))
                   as [_|Hbounds]; last word.
                 destruct (lookup_lt_is_Some_2 finalizers (sint.nat i))
                   as [current Hcurrent_lookup].
                 { rewrite Hsl_len. word. }
                 wp_apply (wp_load_slice_index with "[$Hsl]"); [word|done|].
                 iIntros "Hsl". wp_auto.
                 assert (drop (sint.nat i) finalizers =
                   current :: drop (S (sint.nat i)) finalizers) as Hdrop.
                 { apply drop_S. exact Hcurrent_lookup. }
                 wp_if_destruct.
                 --- iApply wp_for_post_return.
                     rewrite return_val_unseal /return_val_def.
                     rewrite exception_do_unseal /exception_do_def. wp_auto.
                     rewrite exception_seq_unseal /exception.exception_seq_def. wp_auto.
                     iPoseProof ("Hrestore_m" with "Hsl") as "Hdeepown_m_l".
                     iApply ("HΦ" $! true). iFrame. iPureIntro.
                     rewrite Hdrop /= in Hscan.
                     rewrite Hshould_fallback /= -Hscan. done.
                 --- wp_if_destruct.
                     +++ iApply wp_for_post_return.
                         rewrite return_val_unseal /return_val_def.
                         rewrite exception_do_unseal /exception_do_def. wp_auto.
                         rewrite exception_seq_unseal /exception.exception_seq_def. wp_auto.
                         iPoseProof ("Hrestore_m" with "Hsl") as "Hdeepown_m_l".
                         iApply ("HΦ" $! false). iFrame. iPureIntro.
                         rewrite Hshould_fallback /=.
                         rewrite Hdrop /= in Hscan.
                         rewrite -Hscan.
                         done.
                     +++ iApply wp_for_post_do. wp_auto.
                         iAssert I with "[Hi Hf Hsl]" as "Hloop".
                         { iExists (word.add i (W64 1)), current. iFrame.
                           iPureIntro. split; [word|].
                           assert (current ≠ delete_orphan_finalizer) as Hnot_orphan.
                           { rewrite /delete_orphan_finalizer. congruence. }
                           assert (current ≠ delete_foreground_finalizer) as Hnot_foreground.
                           { rewrite /delete_foreground_finalizer. congruence. }
                           rewrite Hdrop /= in Hscan.
                           repeat case_decide; try contradiction.
                           assert (sint.nat (word.add i (W64 1)) =
                             S (sint.nat i)) as -> by word.
                           exact Hscan. }
                         iFrame.
              ** assert (sint.nat i = length finalizers) as Hi_end.
                 { rewrite Hsl_len. word. }
                 rewrite Hi_end drop_all in Hscan.
                 iPoseProof ("Hrestore_m" with "Hsl") as "Hdeepown_m_l".
                 iApply ("HΦ" $! false). iFrame. iPureIntro.
                 rewrite Hshould_fallback /= -Hscan. done.
           ++ assert (sl = slice.nil) as ->.
              { apply (proj2 Hdeepown_finalizers_none). done. }
              iAssert (ObjectMetaV.deepown_l metadata_l m dq)
                with "[Hmetadata_l Hdeepown_creationtimestamp
                  Hdeepown_deletiontimestamp_some
                  Hdeepown_deletiongraceperiodseconds_some Hdeepown_labels_some
                  Hdeepown_annotations_some Hdeepown_ownerreferences_some
                  Hdeepown_managedfields_some]" as "Hdeepown_m_l".
              { iExists metadata_c. iFrame.
                rewrite /ObjectMetaV.deepown Hfinalizers /=. iFrame.
                iFrame "%"; try (iPureIntro; done). }
              set I_nil := ("Hi" ∷ i_ptr ↦ (W64 0) ∗
                "Hf" ∷ f_ptr ↦ (zero_val go_string))%I.
              iAssert I_nil with "[i f]" as "Hloop"; first iFrame.
              wp_for "Hloop". wp_if_destruct; first word.
              iApply ("HΦ" $! false). iFrame. iPureIntro.
              rewrite Hshould_fallback /=. done. }
    + assert (v1.DeleteOptions.PropagationPolicy' options_c = null) as Hpolicy_null.
      { apply (proj2 Hdeepown_propagationpolicy_none). done. }
      assert (bool_decide
        (v1.DeleteOptions.PropagationPolicy' options_c = null) = true)
        as Hpolicy_null_decide.
      { apply bool_decide_true. done. }
      rewrite Hoptions_nonnull_decide /=. wp_auto.
      rewrite Hpolicy_null_decide /=. wp_auto.
      iAssert (DeleteOptionsV.deepown options_c options dq)
        with "[Hdeepown_graceperiodseconds_some Hdeepown_preconditions_some]"
        as "Hoptions".
      { rewrite /DeleteOptionsV.deepown Horphan Hpolicy /=. iFrame.
        iFrame "%"; try (iPureIntro; done). }
      assert (delete_should_orphan_dependents m options =
        match delete_existing_gc_policy
          (default [] m.(ObjectMetaV.Finalizers')) with
        | Some true => true
        | _ => false
        end) as Hshould_fallback.
      { rewrite /delete_should_orphan_dependents /delete_gc_policy
          Horphan Hpolicy /=. done. }
      iDestruct "Hdeepown_m_l" as (metadata_c) "[Hmetadata_l Hmetadata]".
      wp_bind.
      wp_apply (v1.wp_GetFinalizers metadata_l metadata_c dq
        with "[$Hmetadata_l]") as "Hmetadata_l".
      set (sl := metadata_c.(v1.ObjectMeta.Finalizers')).
      iNamed "Hmetadata".
      destruct m.(ObjectMetaV.Finalizers') as [finalizers|] eqn:Hfinalizers.
      * iDestruct "Hdeepown_finalizers_some" as (cfinalizers) "[Hsl ->]".
        iAssert ((sl ↦*{dq} finalizers -∗
          ObjectMetaV.deepown_l metadata_l m dq)%I)
          with "[Hmetadata_l Hdeepown_creationtimestamp
            Hdeepown_deletiontimestamp_some
            Hdeepown_deletiongraceperiodseconds_some Hdeepown_labels_some
            Hdeepown_annotations_some Hdeepown_ownerreferences_some
            Hdeepown_managedfields_some]" as "Hrestore_m".
        { iIntros "Hsl". iExists metadata_c. iFrame.
          rewrite /ObjectMetaV.deepown Hfinalizers /=. iFrame.
          iFrame "%"; try (iPureIntro; done). }
        iDestruct (own_slice_len with "Hsl") as %[Hsl_len _].
        iDestruct (own_slice_wf with "Hsl") as %Hsl_wf.
        set I := (∃ (i : w64) (f : go_string),
          "Hi" ∷ i_ptr ↦ i ∗
          "Hf" ∷ f_ptr ↦ f ∗
          "Hsl" ∷ sl ↦*{dq} finalizers ∗
          "%Hi_bounds" ∷ ⌜ 0 ≤ sint.Z i ≤ sint.Z sl.(slice.len) ⌝ ∗
          "%Hscan" ∷ ⌜ delete_existing_gc_policy
            (drop (sint.nat i) finalizers) =
            delete_existing_gc_policy finalizers ⌝)%I.
        iAssert I with "[i f Hsl]" as "Hloop".
        { iExists (W64 0), (zero_val go_string). iFrame.
          iPureIntro. split; [word|done]. }
        wp_for "Hloop". wp_if_destruct.
        -- destruct (decide (0 ≤ sint.Z i < sint.Z sl.(slice.len)))
             as [_|Hbounds]; last word.
           destruct (lookup_lt_is_Some_2 finalizers (sint.nat i))
             as [current Hcurrent_lookup].
           { rewrite Hsl_len. word. }
           wp_apply (wp_load_slice_index with "[$Hsl]"); [word|done|].
           iIntros "Hsl". wp_auto.
           assert (drop (sint.nat i) finalizers =
             current :: drop (S (sint.nat i)) finalizers) as Hdrop.
           { apply drop_S. exact Hcurrent_lookup. }
           wp_if_destruct.
           ++ iApply wp_for_post_return.
              rewrite return_val_unseal /return_val_def.
              rewrite exception_do_unseal /exception_do_def. wp_auto.
              rewrite exception_seq_unseal /exception.exception_seq_def. wp_auto.
              iPoseProof ("Hrestore_m" with "Hsl") as "Hdeepown_m_l".
              iApply ("HΦ" $! true). iFrame. iPureIntro.
              rewrite Hshould_fallback /=.
              rewrite Hdrop /= in Hscan.
              rewrite -Hscan.
              done.
           ++ wp_if_destruct.
              ** iApply wp_for_post_return.
                 rewrite return_val_unseal /return_val_def.
                 rewrite exception_do_unseal /exception_do_def. wp_auto.
                 rewrite exception_seq_unseal /exception.exception_seq_def. wp_auto.
                 iPoseProof ("Hrestore_m" with "Hsl") as "Hdeepown_m_l".
                 iApply ("HΦ" $! false). iFrame. iPureIntro.
                 rewrite Hshould_fallback /=.
                 rewrite Hdrop /= in Hscan.
                 rewrite -Hscan.
                 done.
              ** iApply wp_for_post_do. wp_auto.
                 iAssert I with "[Hi Hf Hsl]" as "Hloop".
                 { iExists (word.add i (W64 1)), current. iFrame.
                   iPureIntro. split; [word|].
                   assert (current ≠ delete_orphan_finalizer) as Hnot_orphan.
                   { rewrite /delete_orphan_finalizer. congruence. }
                   assert (current ≠ delete_foreground_finalizer) as Hnot_foreground.
                   { rewrite /delete_foreground_finalizer. congruence. }
                   rewrite Hdrop /= in Hscan.
                   repeat case_decide; try contradiction.
                   assert (sint.nat (word.add i (W64 1)) =
                     S (sint.nat i)) as -> by word.
                   exact Hscan. }
                 iFrame.
        -- assert (sint.nat i = length finalizers) as Hi_end.
           { rewrite Hsl_len. word. }
           rewrite Hi_end drop_all in Hscan.
           iPoseProof ("Hrestore_m" with "Hsl") as "Hdeepown_m_l".
           iApply ("HΦ" $! false). iFrame. iPureIntro.
           rewrite Hshould_fallback /= -Hscan. done.
      * assert (sl = slice.nil) as ->.
        { apply (proj2 Hdeepown_finalizers_none). done. }
        iAssert (ObjectMetaV.deepown_l metadata_l m dq)
          with "[Hmetadata_l Hdeepown_creationtimestamp
            Hdeepown_deletiontimestamp_some
            Hdeepown_deletiongraceperiodseconds_some Hdeepown_labels_some
            Hdeepown_annotations_some Hdeepown_ownerreferences_some
            Hdeepown_managedfields_some]" as "Hdeepown_m_l".
        { iExists metadata_c. iFrame.
          rewrite /ObjectMetaV.deepown Hfinalizers /=. iFrame.
          iFrame "%"; try (iPureIntro; done). }
        set I_nil := ("Hi" ∷ i_ptr ↦ (W64 0) ∗
          "Hf" ∷ f_ptr ↦ (zero_val go_string))%I.
        iAssert I_nil with "[i f]" as "Hloop"; first iFrame.
        wp_for "Hloop". wp_if_destruct; first word.
        iApply ("HΦ" $! false). iFrame. iPureIntro.
        rewrite Hshould_fallback /=. done.
Qed.

Lemma wp_shouldDeleteDependents metadata_i metadata_l m options_l options dq :
  {{{ is_pkg_init apimodel ∗
      "%Hmetadata" ∷ ⌜ metadata_i = interface.mk (go.PointerType v1.ObjectMeta) #metadata_l ⌝ ∗
      "Hdeepown_m_l" ∷ ObjectMetaV.deepown_l metadata_l m dq ∗
      "Hdeepown_options_l" ∷ DeleteOptionsV.deepown_l options_l options dq
  }}}
    @! apimodel.shouldDeleteDependents #(interface.ok metadata_i) #options_l
  {{{ should_delete, RET #should_delete;
      ⌜ should_delete = delete_should_delete_dependents m options ⌝ ∗
      ObjectMetaV.deepown_l metadata_l m dq ∗
      DeleteOptionsV.deepown_l options_l options dq
  }}}.
Proof.
  wp_start as "H". iNamed "H". subst metadata_i.
  iDestruct "Hdeepown_options_l" as (options_c) "[Hoptions_l Hoptions]".
  iDestruct (typed_pointsto_not_null with "Hoptions_l") as %Hoptions_l_not_null.
  assert (bool_decide (options_l = null) = false) as Hoptions_nonnull_decide.
  { apply bool_decide_false. done. }
  iNamed "Hoptions".
  destruct options.(DeleteOptionsV.OrphanDependents') as [orphan|] eqn:Horphan.
  - iDestruct "Hdeepown_orphandependents_some" as (orphan_c) "[Horphan_l ->]".
    iDestruct (typed_pointsto_not_null with "Horphan_l") as %Horphan_l_not_null.
    assert (bool_decide
      (v1.DeleteOptions.OrphanDependents' options_c = null) = false)
      as Horphan_nonnull_decide.
    { apply bool_decide_false. done. }
    wp_auto. rewrite Hoptions_nonnull_decide /=. wp_auto.
    rewrite Horphan_nonnull_decide /=. wp_auto.
    iAssert (DeleteOptionsV.deepown options_c options dq)
      with "[Hdeepown_graceperiodseconds_some Hdeepown_preconditions_some
        Horphan_l Hdeepown_propagationpolicy_some]" as "Hoptions".
    { rewrite /DeleteOptionsV.deepown Horphan /=. iFrame.
      iFrame "%"; try (iPureIntro; done). }
    iApply ("HΦ" $! false). iFrame. iPureIntro.
    rewrite /delete_should_delete_dependents /delete_gc_policy Horphan /=.
    by destruct orphan.
  - assert (v1.DeleteOptions.OrphanDependents' options_c = null) as Horphan_null.
    { apply (proj2 Hdeepown_orphandependents_none). done. }
    assert (bool_decide
      (v1.DeleteOptions.OrphanDependents' options_c = null) = true)
      as Horphan_null_decide.
    { apply bool_decide_true. done. }
    wp_auto. rewrite Hoptions_nonnull_decide /=. wp_auto.
    rewrite Horphan_null_decide /=. wp_auto.
    destruct options.(DeleteOptionsV.PropagationPolicy') as [policy|] eqn:Hpolicy.
    + iDestruct "Hdeepown_propagationpolicy_some" as (policy_c) "[Hpolicy_l ->]".
      iDestruct (typed_pointsto_not_null with "Hpolicy_l") as %Hpolicy_l_not_null.
      assert (bool_decide
        (v1.DeleteOptions.PropagationPolicy' options_c = null) = false)
        as Hpolicy_nonnull_decide.
      { apply bool_decide_false. done. }
      rewrite Hoptions_nonnull_decide /=. wp_auto.
      rewrite Hpolicy_nonnull_decide /=. wp_auto.
      iAssert (DeleteOptionsV.deepown options_c options dq)
        with "[Hdeepown_graceperiodseconds_some Hdeepown_preconditions_some
          Hpolicy_l]" as "Hoptions".
      { rewrite /DeleteOptionsV.deepown Horphan Hpolicy /=. iFrame.
        iFrame "%"; try (iPureIntro; done). }
      wp_if_destruct.
      * iApply ("HΦ" $! true). iFrame. iPureIntro.
        rewrite /delete_should_delete_dependents /delete_gc_policy Horphan Hpolicy /=.
        repeat case_decide; done.
      * wp_if_destruct.
        -- iApply ("HΦ" $! false). iFrame. iPureIntro.
           rewrite /delete_should_delete_dependents /delete_gc_policy Horphan Hpolicy /=.
           repeat case_decide; done.
        -- wp_if_destruct.
           { iApply ("HΦ" $! false). iFrame. iPureIntro.
             rewrite /delete_should_delete_dependents /delete_gc_policy
               Horphan Hpolicy /=.
             repeat case_decide; done. }
           { assert (delete_should_delete_dependents m options =
              match delete_existing_gc_policy
                (default [] m.(ObjectMetaV.Finalizers')) with
              | Some false => true
              | _ => false
             end) as Hshould_fallback.
           { rewrite /delete_should_delete_dependents /delete_gc_policy
               Horphan Hpolicy /=.
             repeat case_decide; try congruence; done. }
           iDestruct "Hdeepown_m_l" as (metadata_c) "[Hmetadata_l Hmetadata]".
           wp_bind.
           wp_apply (v1.wp_GetFinalizers metadata_l metadata_c dq
             with "[$Hmetadata_l]") as "Hmetadata_l".
           set (sl := metadata_c.(v1.ObjectMeta.Finalizers')).
           iNamed "Hmetadata".
           destruct m.(ObjectMetaV.Finalizers') as [finalizers|] eqn:Hfinalizers.
           ++ iDestruct "Hdeepown_finalizers_some" as (cfinalizers) "[Hsl ->]".
              iAssert ((sl ↦*{dq} finalizers -∗
                ObjectMetaV.deepown_l metadata_l m dq)%I)
                with "[Hmetadata_l Hdeepown_creationtimestamp
                  Hdeepown_deletiontimestamp_some
                  Hdeepown_deletiongraceperiodseconds_some Hdeepown_labels_some
                  Hdeepown_annotations_some Hdeepown_ownerreferences_some
                  Hdeepown_managedfields_some]" as "Hrestore_m".
              { iIntros "Hsl". iExists metadata_c. iFrame.
                rewrite /ObjectMetaV.deepown Hfinalizers /=. iFrame.
                iFrame "%"; try (iPureIntro; done). }
              iDestruct (own_slice_len with "Hsl") as %[Hsl_len _].
              iDestruct (own_slice_wf with "Hsl") as %Hsl_wf.
              set I := (∃ (i : w64) (f : go_string),
                "Hi" ∷ i_ptr ↦ i ∗
                "Hf" ∷ f_ptr ↦ f ∗
                "Hsl" ∷ sl ↦*{dq} finalizers ∗
                "%Hi_bounds" ∷ ⌜ 0 ≤ sint.Z i ≤ sint.Z sl.(slice.len) ⌝ ∗
                "%Hscan" ∷ ⌜ delete_existing_gc_policy
                  (drop (sint.nat i) finalizers) =
                  delete_existing_gc_policy finalizers ⌝)%I.
              iAssert I with "[i f Hsl]" as "Hloop".
              { iExists (W64 0), (zero_val go_string). iFrame.
                iPureIntro. split; [word|done]. }
              wp_for "Hloop". wp_if_destruct.
              ** destruct (decide (0 ≤ sint.Z i < sint.Z sl.(slice.len)))
                   as [_|Hbounds]; last word.
                 destruct (lookup_lt_is_Some_2 finalizers (sint.nat i))
                   as [current Hcurrent_lookup].
                 { rewrite Hsl_len. word. }
                 wp_apply (wp_load_slice_index with "[$Hsl]"); [word|done|].
                 iIntros "Hsl". wp_auto.
                 assert (drop (sint.nat i) finalizers =
                   current :: drop (S (sint.nat i)) finalizers) as Hdrop.
                 { apply drop_S. exact Hcurrent_lookup. }
                 wp_if_destruct.
                 --- iApply wp_for_post_return.
                     rewrite return_val_unseal /return_val_def.
                     rewrite exception_do_unseal /exception_do_def. wp_auto.
                     rewrite exception_seq_unseal /exception.exception_seq_def. wp_auto.
                     iPoseProof ("Hrestore_m" with "Hsl") as "Hdeepown_m_l".
                     iApply ("HΦ" $! true). iFrame. iPureIntro.
                     rewrite Hshould_fallback /=.
                     rewrite Hdrop /= in Hscan.
                     rewrite -Hscan.
                     done.
                 --- wp_if_destruct.
                     +++ iApply wp_for_post_return.
                         rewrite return_val_unseal /return_val_def.
                         rewrite exception_do_unseal /exception_do_def. wp_auto.
                         rewrite exception_seq_unseal /exception.exception_seq_def. wp_auto.
                         iPoseProof ("Hrestore_m" with "Hsl") as "Hdeepown_m_l".
                         iApply ("HΦ" $! false). iFrame. iPureIntro.
                         rewrite Hshould_fallback /=.
                         rewrite Hdrop /= in Hscan.
                         rewrite -Hscan.
                         done.
                     +++ iApply wp_for_post_do. wp_auto.
                         iAssert I with "[Hi Hf Hsl]" as "Hloop".
                         { iExists (word.add i (W64 1)), current. iFrame.
                           iPureIntro. split; [word|].
                           assert (current ≠ delete_orphan_finalizer) as Hnot_orphan.
                           { rewrite /delete_orphan_finalizer. congruence. }
                           assert (current ≠ delete_foreground_finalizer) as Hnot_foreground.
                           { rewrite /delete_foreground_finalizer. congruence. }
                           rewrite Hdrop /= in Hscan.
                           repeat case_decide; try contradiction.
                           assert (sint.nat (word.add i (W64 1)) =
                             S (sint.nat i)) as -> by word.
                           exact Hscan. }
                         iFrame.
              ** assert (sint.nat i = length finalizers) as Hi_end.
                 { rewrite Hsl_len. word. }
                 rewrite Hi_end drop_all in Hscan.
                 iPoseProof ("Hrestore_m" with "Hsl") as "Hdeepown_m_l".
                 iApply ("HΦ" $! false). iFrame. iPureIntro.
                 rewrite Hshould_fallback /= -Hscan. done.
           ++ assert (sl = slice.nil) as ->.
              { apply (proj2 Hdeepown_finalizers_none). done. }
              iAssert (ObjectMetaV.deepown_l metadata_l m dq)
                with "[Hmetadata_l Hdeepown_creationtimestamp
                  Hdeepown_deletiontimestamp_some
                  Hdeepown_deletiongraceperiodseconds_some Hdeepown_labels_some
                  Hdeepown_annotations_some Hdeepown_ownerreferences_some
                  Hdeepown_managedfields_some]" as "Hdeepown_m_l".
              { iExists metadata_c. iFrame.
                rewrite /ObjectMetaV.deepown Hfinalizers /=. iFrame.
                iFrame "%"; try (iPureIntro; done). }
              set I_nil := ("Hi" ∷ i_ptr ↦ (W64 0) ∗
                "Hf" ∷ f_ptr ↦ (zero_val go_string))%I.
              iAssert I_nil with "[i f]" as "Hloop"; first iFrame.
              wp_for "Hloop". wp_if_destruct; first word.
              iApply ("HΦ" $! false). iFrame. iPureIntro.
              rewrite Hshould_fallback /=. done. }
    + assert (v1.DeleteOptions.PropagationPolicy' options_c = null) as Hpolicy_null.
      { apply (proj2 Hdeepown_propagationpolicy_none). done. }
      assert (bool_decide
        (v1.DeleteOptions.PropagationPolicy' options_c = null) = true)
        as Hpolicy_null_decide.
      { apply bool_decide_true. done. }
      rewrite Hoptions_nonnull_decide /=. wp_auto.
      rewrite Hpolicy_null_decide /=. wp_auto.
      iAssert (DeleteOptionsV.deepown options_c options dq)
        with "[Hdeepown_graceperiodseconds_some Hdeepown_preconditions_some]"
        as "Hoptions".
      { rewrite /DeleteOptionsV.deepown Horphan Hpolicy /=. iFrame.
        iFrame "%"; try (iPureIntro; done). }
      assert (delete_should_delete_dependents m options =
        match delete_existing_gc_policy
          (default [] m.(ObjectMetaV.Finalizers')) with
        | Some false => true
        | _ => false
        end) as Hshould_fallback.
      { rewrite /delete_should_delete_dependents /delete_gc_policy
          Horphan Hpolicy /=. done. }
      iDestruct "Hdeepown_m_l" as (metadata_c) "[Hmetadata_l Hmetadata]".
      wp_bind.
      wp_apply (v1.wp_GetFinalizers metadata_l metadata_c dq
        with "[$Hmetadata_l]") as "Hmetadata_l".
      set (sl := metadata_c.(v1.ObjectMeta.Finalizers')).
      iNamed "Hmetadata".
      destruct m.(ObjectMetaV.Finalizers') as [finalizers|] eqn:Hfinalizers.
      * iDestruct "Hdeepown_finalizers_some" as (cfinalizers) "[Hsl ->]".
        iAssert ((sl ↦*{dq} finalizers -∗
          ObjectMetaV.deepown_l metadata_l m dq)%I)
          with "[Hmetadata_l Hdeepown_creationtimestamp
            Hdeepown_deletiontimestamp_some
            Hdeepown_deletiongraceperiodseconds_some Hdeepown_labels_some
            Hdeepown_annotations_some Hdeepown_ownerreferences_some
            Hdeepown_managedfields_some]" as "Hrestore_m".
        { iIntros "Hsl". iExists metadata_c. iFrame.
          rewrite /ObjectMetaV.deepown Hfinalizers /=. iFrame.
          iFrame "%"; try (iPureIntro; done). }
        iDestruct (own_slice_len with "Hsl") as %[Hsl_len _].
        iDestruct (own_slice_wf with "Hsl") as %Hsl_wf.
        set I := (∃ (i : w64) (f : go_string),
          "Hi" ∷ i_ptr ↦ i ∗
          "Hf" ∷ f_ptr ↦ f ∗
          "Hsl" ∷ sl ↦*{dq} finalizers ∗
          "%Hi_bounds" ∷ ⌜ 0 ≤ sint.Z i ≤ sint.Z sl.(slice.len) ⌝ ∗
          "%Hscan" ∷ ⌜ delete_existing_gc_policy
            (drop (sint.nat i) finalizers) =
            delete_existing_gc_policy finalizers ⌝)%I.
        iAssert I with "[i f Hsl]" as "Hloop".
        { iExists (W64 0), (zero_val go_string). iFrame.
          iPureIntro. split; [word|done]. }
        wp_for "Hloop". wp_if_destruct.
        -- destruct (decide (0 ≤ sint.Z i < sint.Z sl.(slice.len)))
             as [_|Hbounds]; last word.
           destruct (lookup_lt_is_Some_2 finalizers (sint.nat i))
             as [current Hcurrent_lookup].
           { rewrite Hsl_len. word. }
           wp_apply (wp_load_slice_index with "[$Hsl]"); [word|done|].
           iIntros "Hsl". wp_auto.
           assert (drop (sint.nat i) finalizers =
             current :: drop (S (sint.nat i)) finalizers) as Hdrop.
           { apply drop_S. exact Hcurrent_lookup. }
           wp_if_destruct.
           ++ iApply wp_for_post_return.
              rewrite return_val_unseal /return_val_def.
              rewrite exception_do_unseal /exception_do_def. wp_auto.
              rewrite exception_seq_unseal /exception.exception_seq_def. wp_auto.
              iPoseProof ("Hrestore_m" with "Hsl") as "Hdeepown_m_l".
              iApply ("HΦ" $! true). iFrame. iPureIntro.
              rewrite Hshould_fallback /=.
              rewrite Hdrop /= in Hscan.
              rewrite -Hscan.
              done.
           ++ wp_if_destruct.
              ** iApply wp_for_post_return.
                 rewrite return_val_unseal /return_val_def.
                 rewrite exception_do_unseal /exception_do_def. wp_auto.
                 rewrite exception_seq_unseal /exception.exception_seq_def. wp_auto.
                 iPoseProof ("Hrestore_m" with "Hsl") as "Hdeepown_m_l".
                 iApply ("HΦ" $! false). iFrame. iPureIntro.
                 rewrite Hshould_fallback /=.
                 rewrite Hdrop /= in Hscan.
                 rewrite -Hscan.
                 done.
              ** iApply wp_for_post_do. wp_auto.
                 iAssert I with "[Hi Hf Hsl]" as "Hloop".
                 { iExists (word.add i (W64 1)), current. iFrame.
                   iPureIntro. split; [word|].
                   assert (current ≠ delete_orphan_finalizer) as Hnot_orphan.
                   { rewrite /delete_orphan_finalizer. congruence. }
                   assert (current ≠ delete_foreground_finalizer) as Hnot_foreground.
                   { rewrite /delete_foreground_finalizer. congruence. }
                   rewrite Hdrop /= in Hscan.
                   repeat case_decide; try contradiction.
                   assert (sint.nat (word.add i (W64 1)) =
                     S (sint.nat i)) as -> by word.
                   exact Hscan. }
                 iFrame.
        -- assert (sint.nat i = length finalizers) as Hi_end.
           { rewrite Hsl_len. word. }
           rewrite Hi_end drop_all in Hscan.
           iPoseProof ("Hrestore_m" with "Hsl") as "Hdeepown_m_l".
           iApply ("HΦ" $! false). iFrame. iPureIntro.
           rewrite Hshould_fallback /= -Hscan. done.
      * assert (sl = slice.nil) as ->.
        { apply (proj2 Hdeepown_finalizers_none). done. }
        iAssert (ObjectMetaV.deepown_l metadata_l m dq)
          with "[Hmetadata_l Hdeepown_creationtimestamp
            Hdeepown_deletiontimestamp_some
            Hdeepown_deletiongraceperiodseconds_some Hdeepown_labels_some
            Hdeepown_annotations_some Hdeepown_ownerreferences_some
            Hdeepown_managedfields_some]" as "Hdeepown_m_l".
        { iExists metadata_c. iFrame.
          rewrite /ObjectMetaV.deepown Hfinalizers /=. iFrame.
          iFrame "%"; try (iPureIntro; done). }
        set I_nil := ("Hi" ∷ i_ptr ↦ (W64 0) ∗
          "Hf" ∷ f_ptr ↦ (zero_val go_string))%I.
        iAssert I_nil with "[i f]" as "Hloop"; first iFrame.
        wp_for "Hloop". wp_if_destruct; first word.
        iApply ("HΦ" $! false). iFrame. iPureIntro.
        rewrite Hshould_fallback /=. done.
Qed.

Lemma wp_slice_literal_non_nil `[!ZeroVal V] `[!TypedPointsto V]
    `[!IntoValTyped V t]
    `{!st ↓u (go.SliceType t)} (l : list V) kvs Φ :
  let len := go.array_literal_size kvs in
  WP (CompositeLiteral (go.ArrayType len t) (LiteralValueV kvs))
    {{ v,
      ⌜ v = #(array.mk len l) ⌝ ∗
      (∀ sl_ptr,
        let sl := slice.mk sl_ptr (W64 len) (W64 len) in
        (sl ↦* l ∗ own_slice_cap V sl 1 ∗ ⌜ sl ≠ slice.nil ⌝) -∗
        Φ #sl) }}
  -∗
  WP (CompositeLiteral st (LiteralValueV kvs)) {{ Φ }}.
Proof.
  iIntros "* HΦ".
  pose proof go.composite_literal_slice.
  wp_pures. destruct decide; last by iApply wp_AngelicExit.
  wp_pures. wp_alloc_auto.
  iDestruct (typed_pointsto_not_null with "tmp") as %Hnotnull.
  wp_pure. wp_pure.
  wp_apply (wp_wand with "HΦ"). iIntros "% [-> HΦ]". wp_auto.
  rewrite decide_True.
  1: { enough (0 ≤ go.array_literal_size kvs) by word.
    unfold go.array_literal_size. destruct foldl. lia. }
  wp_auto. iDestruct (array_len with "tmp") as %Hlen.
  rewrite !go.array_index_ref_0 /=.
  wp_end.
  - iDestruct (slice_array with "tmp") as "$".
    { simpl. word. }
    iSplitL.
    + iApply own_slice_cap_empty; simpl; [done|word].
    + iPureIntro. intros Hnil. apply Hnotnull.
      by inversion Hnil.
  - ereplace (word.sub ?[a] ?[b]) with (?a) by word. done.
Qed.

Lemma wp_deletionFinalizersForGarbageCollection metadata_i metadata_l m options_l options dq :
  {{{ is_pkg_init apimodel ∗
      "%Hmetadata" ∷ ⌜ metadata_i = interface.mk (go.PointerType v1.ObjectMeta) #metadata_l ⌝ ∗
      "Hdeepown_m_l" ∷ ObjectMetaV.deepown_l metadata_l m dq ∗
      "Hdeepown_options_l" ∷ DeleteOptionsV.deepown_l options_l options dq ∗
      "%Hvalid_finalizers" ∷ ⌜ valid_finalizers m.(ObjectMetaV.Finalizers') ⌝
  }}}
    @! apimodel.deletionFinalizersForGarbageCollection #(interface.ok metadata_i) #options_l
  {{{ should_update_finalizers new_finalizers_sl new_finalizers, RET (#should_update_finalizers, #new_finalizers_sl);
      ⌜ should_update_finalizers = delete_should_update_finalizers m options ⌝ ∗
      ⌜ new_finalizers = delete_new_finalizers m options ⌝ ∗
      ⌜ valid_finalizers new_finalizers ⌝ ∗
      ⌜ new_finalizers_sl = slice.nil ↔ new_finalizers = None ⌝ ∗
      (if should_update_finalizers then
        match new_finalizers with
        | Some fs => ∃ cfs, new_finalizers_sl ↦* cfs ∗ ⌜ cfs = fs ⌝
        | None => True%I
        end
      else True%I) ∗
      ObjectMetaV.deepown_l metadata_l m dq ∗
      DeleteOptionsV.deepown_l options_l options dq
  }}}.
Proof.
  wp_start as "H". iNamed "H". subst metadata_i.
  wp_auto.
  wp_apply (wp_shouldOrphanDependents with
    "[$Hdeepown_m_l $Hdeepown_options_l]").
  { iFrame "#". iPureIntro. done. }
  iIntros (should_orphan) "(-> & Hdeepown_m_l & Hdeepown_options_l)".
  wp_auto.
  wp_apply (wp_shouldDeleteDependents with
    "[$Hdeepown_m_l $Hdeepown_options_l]").
  { iFrame "#". iPureIntro. done. }
  iIntros (should_delete) "(-> & Hdeepown_m_l & Hdeepown_options_l)".
  wp_auto.
  wp_apply wp_slice_literal_non_nil. iSplitR; first done.
  iIntros (new_sl_ptr) "(Hnew_sl & Hnew_cap & %Hnew_sl_non_nil)".
  set (new_sl := slice.mk new_sl_ptr (W64 0) (W64 0)). wp_auto.
  wp_apply (v1.wp_GetFinalizers_deepown with "[$Hdeepown_m_l]").
  iIntros (old_sl) "(%Hold_sl_nil & Hold_finalizers)".
  iAssert ("Hold_sl" ∷ old_sl ↦*{dq} default [] m.(ObjectMetaV.Finalizers') ∗
      "Hrestore_m" ∷ (old_sl ↦*{dq} default [] m.(ObjectMetaV.Finalizers') -∗
        ObjectMetaV.deepown_l metadata_l m dq))%I
    with "[Hold_finalizers]" as "(Hold_sl & Hrestore_m)".
  { destruct m.(ObjectMetaV.Finalizers') as [finalizers|]
      eqn:Hfinalizers_eq.
    - iDestruct "Hold_finalizers" as (cfinalizers)
        "(Hold_sl & -> & Hrestore_m)".
      iFrame.
    - assert (old_sl = slice.nil) as -> by
        (apply (proj2 Hold_sl_nil); done).
      simpl. iSplitL ""; first iApply (own_slice_nil (V := go_string) dq).
      iIntros "_". iFrame. }
  set (keep := fun finalizer : go_string =>
    finalizer ≠ delete_orphan_finalizer ∧
    finalizer ≠ delete_foreground_finalizer).
  set (old_finalizers := default [] m.(ObjectMetaV.Finalizers')).
  iDestruct (own_slice_len with "Hold_sl") as %[Hold_sl_len Hold_sl_nonneg].
  wp_auto.
  set I := (∃ (i : w64) (f : go_string) (result_sl : slice.t),
    "Hi" ∷ i_ptr ↦ i ∗
    "Hf" ∷ f_ptr ↦ f ∗
    "HnewFinalizers" ∷ newFinalizers_ptr ↦ result_sl ∗
    "Hresult" ∷ result_sl ↦* filter keep (take (sint.nat i) old_finalizers) ∗
    "Hresult_cap" ∷ own_slice_cap go_string result_sl (DfracOwn 1) ∗
    "%Hresult_non_nil" ∷ ⌜ result_sl ≠ slice.nil ⌝ ∗
    "Hold_sl" ∷ old_sl ↦*{dq} old_finalizers ∗
    "%Hi_bounds" ∷ ⌜ 0 ≤ sint.Z i ≤ sint.Z old_sl.(slice.len) ⌝)%I.
  iAssert I with "[i f newFinalizers Hnew_sl Hnew_cap Hold_sl]" as "Hloop".
  { iExists (W64 0), (zero_val go_string), new_sl. iFrame.
    iPureIntro. split; [exact Hnew_sl_non_nil|word]. }
  wp_for "Hloop". wp_if_destruct.
  - destruct (decide (0 ≤ sint.Z i < sint.Z old_sl.(slice.len)))
      as [_|Hbounds]; last word.
    destruct (lookup_lt_is_Some_2 old_finalizers (sint.nat i))
      as [current Hcurrent_lookup].
    { rewrite Hold_sl_len. word. }
    wp_apply (wp_load_slice_index with "[$Hold_sl]"); [word|done|].
    iIntros "Hold_sl". wp_auto.
    wp_if_destruct.
    + iApply wp_for_post_continue. wp_auto.
      iAssert I with
        "[Hi Hf HnewFinalizers Hresult Hresult_cap Hold_sl]" as "Hloop".
      { assert (sint.nat (word.add i (W64 1)) = S (sint.nat i)) as Hnext by word.
        assert (filter keep [delete_orphan_finalizer] = []) as Hfilter.
        { apply (@filter_singleton_False go_string keep _
            delete_orphan_finalizer []).
          intros [Hneq _]. apply Hneq. done. }
        assert (filter keep
            (take (sint.nat (word.add i (W64 1))) old_finalizers) =
          filter keep (take (sint.nat i) old_finalizers)) as Hresult_eq.
        { rewrite Hnext
            (take_S_r _ _ delete_orphan_finalizer Hcurrent_lookup)
            list.filter_app Hfilter app_nil_r. done. }
        iExists (word.add i (W64 1)), delete_orphan_finalizer, result_sl.
        rewrite Hresult_eq. iFrame. iPureIntro.
        split; [exact Hresult_non_nil|word]. }
      iFrame.
    + wp_if_destruct.
      * iApply wp_for_post_continue. wp_auto.
        iAssert I with
          "[Hi Hf HnewFinalizers Hresult Hresult_cap Hold_sl]" as "Hloop".
        { assert (sint.nat (word.add i (W64 1)) = S (sint.nat i)) as Hnext
            by word.
          assert (filter keep [delete_foreground_finalizer] = []) as Hfilter.
          { apply (@filter_singleton_False go_string keep _
              delete_foreground_finalizer []).
            intros [_ Hneq]. apply Hneq. done. }
          assert (filter keep
              (take (sint.nat (word.add i (W64 1))) old_finalizers) =
            filter keep (take (sint.nat i) old_finalizers)) as Hresult_eq.
          { rewrite Hnext
              (take_S_r _ _ delete_foreground_finalizer Hcurrent_lookup)
              list.filter_app Hfilter app_nil_r. done. }
          iExists (word.add i (W64 1)), delete_foreground_finalizer, result_sl.
          rewrite Hresult_eq. iFrame. iPureIntro.
          split; [exact Hresult_non_nil|word]. }
        iFrame.
      * wp_apply wp_slice_literal. iSplitR; first done.
        iIntros (one_sl_ptr) "[Hone_sl _]".
        set (one_sl := slice.mk one_sl_ptr (W64 1) (W64 1)). wp_auto.
        wp_apply (wp_slice_append with "[$Hresult $Hresult_cap $Hone_sl]").
        iIntros (result_sl') "(Hresult & Hresult_cap & _)".
        iDestruct (own_slice_len with "Hresult") as %[Hresult_sl_len _].
        assert (result_sl' ≠ slice.nil) as Hresult_sl_non_nil.
        { intros ->. simpl in Hresult_sl_len.
          assert (sint.nat (W64 0) = 0%nat) as Hzero by word.
          rewrite Hzero app_length /= in Hresult_sl_len. lia. }
        wp_auto. iApply wp_for_post_do. wp_auto.
        iAssert I with
          "[Hi Hf HnewFinalizers Hresult Hresult_cap Hold_sl]" as "Hloop".
        { assert (sint.nat (word.add i (W64 1)) = S (sint.nat i)) as Hnext
            by word.
          assert (filter keep [current] = [current]) as Hfilter.
          { apply (@filter_singleton_True go_string keep _ current []).
            unfold keep, delete_orphan_finalizer, delete_foreground_finalizer.
            split; congruence. }
          assert (filter keep
              (take (sint.nat (word.add i (W64 1))) old_finalizers) =
            filter keep (take (sint.nat i) old_finalizers) ++ [current])
              as Hresult_eq.
          { rewrite Hnext (take_S_r _ _ current Hcurrent_lookup)
              list.filter_app Hfilter. done. }
          iExists (word.add i (W64 1)), current, result_sl'.
          rewrite Hresult_eq. iFrame. iPureIntro.
          split; [exact Hresult_sl_non_nil|word]. }
        iFrame.
  - assert (sint.nat i = length old_finalizers) as Hi_end.
    { rewrite Hold_sl_len. word. }
    assert (take (sint.nat i) old_finalizers = old_finalizers) as Htake_all.
    { apply take_ge. rewrite Hi_end. lia. }
    iEval (rewrite Htake_all) in "Hresult".
    iPoseProof ("Hrestore_m" with "Hold_sl") as "Hdeepown_m_l".
    rewrite exception_do_unseal /exception_do_def.
    rewrite exception_seq_unseal /exception.exception_seq_def.
    wp_pures.
    set Jorphan := (fun v => ⌜ v = execute_val ⌝ ∗ ∃ result_sl,
      "HnewFinalizers" ∷ newFinalizers_ptr ↦ result_sl ∗
      "Hresult" ∷ result_sl ↦*
        (filter keep old_finalizers ++
          if delete_should_orphan_dependents m options
          then [delete_orphan_finalizer] else []) ∗
      "Hresult_cap" ∷ own_slice_cap go_string result_sl (DfracOwn 1) ∗
      "%Hresult_non_nil" ∷ ⌜ result_sl ≠ slice.nil ⌝)%I.
    wp_bind (if: #(delete_should_orphan_dependents m options)
      then _ else _)%E.
    iApply (wp_wand _ _ _ Jorphan
      with "[HnewFinalizers Hresult Hresult_cap]")%I;
      [destruct (delete_should_orphan_dependents m options)
        eqn:Hshould_orphan; wp_auto|].
    { wp_apply wp_slice_literal. iSplitR; first done.
      iIntros (one_sl_ptr) "[Hone_sl _]".
      set (one_sl := slice.mk one_sl_ptr (W64 1) (W64 1)). wp_auto.
      wp_apply (wp_slice_append with "[$Hresult $Hresult_cap $Hone_sl]").
      iIntros (result_sl') "(Hresult & Hresult_cap & _)". wp_auto.
      iDestruct (own_slice_len with "Hresult") as %[Hresult_sl_len _].
      assert (result_sl' ≠ slice.nil) as Hresult_sl_non_nil.
      { intros ->. simpl in Hresult_sl_len.
        assert (sint.nat (W64 0) = 0%nat) as Hzero by word.
        rewrite Hzero app_length /= in Hresult_sl_len. lia. }
      iSplit; first done. iExists result_sl'.
      simpl. unfold delete_orphan_finalizer. iFrame "%". iFrame. }
    { iSplit; first done. iExists result_sl.
      simpl. rewrite !app_nil_r. iFrame "%". iFrame. }
    iIntros (?) "(-> & Happend_orphan)". iNamed "Happend_orphan". wp_auto.
    set Jforeground := (fun v => ⌜ v = execute_val ⌝ ∗ ∃ final_sl,
      "HnewFinalizers" ∷ newFinalizers_ptr ↦ final_sl ∗
      "Hnew_finalizers" ∷ final_sl ↦*
        (filter keep old_finalizers ++
          (if delete_should_orphan_dependents m options
           then [delete_orphan_finalizer] else []) ++
          (if delete_should_delete_dependents m options
           then [delete_foreground_finalizer] else [])) ∗
      "Hnew_finalizers_cap" ∷
        own_slice_cap go_string final_sl (DfracOwn 1) ∗
      "%Hnew_finalizers_non_nil" ∷ ⌜ final_sl ≠ slice.nil ⌝)%I.
    rewrite execute_val_unseal /execute_val_def. wp_auto.
    wp_bind (if: #(delete_should_delete_dependents m options)
      then _ else _)%E.
    iApply (wp_wand _ _ _ Jforeground
      with "[HnewFinalizers Hresult Hresult_cap]")%I;
      [destruct (delete_should_delete_dependents m options)
        eqn:Hshould_foreground; wp_auto|].
    { wp_apply wp_slice_literal. iSplitR; first done.
      iIntros (one_sl_ptr) "[Hone_sl _]".
      set (one_sl := slice.mk one_sl_ptr (W64 1) (W64 1)). wp_auto.
      wp_apply (wp_slice_append with "[$Hresult $Hresult_cap $Hone_sl]").
      iIntros (final_sl) "(Hnew_finalizers & Hnew_finalizers_cap & _)".
      iDestruct (own_slice_len with "Hnew_finalizers") as %[Hfinal_sl_len _].
      assert (final_sl ≠ slice.nil) as Hnew_finalizers_non_nil.
      { intros ->. simpl in Hfinal_sl_len.
        assert (sint.nat (W64 0) = 0%nat) as Hzero by word.
        rewrite Hzero !app_length /= in Hfinal_sl_len. lia. }
      assert (sint.nat (W64 0) = 0%nat) as Hzero by word.
      iEval (rewrite Hzero /=) in "Hnew_finalizers".
      iEval (rewrite -app_assoc) in "Hnew_finalizers".
      wp_auto. iSplit; first done. iExists final_sl.
      simpl. unfold delete_foreground_finalizer. iFrame "%". iFrame. }
    { iSplit; first done. iExists result_sl0.
      simpl. rewrite !app_nil_r. iFrame "%". iFrame. }
    iIntros (?) "(-> & Happend_foreground)". iNamed "Happend_foreground".
    assert (filter keep old_finalizers ++
        (if delete_should_orphan_dependents m options
         then [delete_orphan_finalizer] else []) ++
        (if delete_should_delete_dependents m options
         then [delete_foreground_finalizer] else []) =
      delete_finalizers_for_gc m options) as Hnew_finalizers_eq.
    { rewrite /delete_finalizers_for_gc /keep /old_finalizers. done. }
    iEval (rewrite Hnew_finalizers_eq) in "Hnew_finalizers".
    wp_auto.
    rewrite execute_val_unseal /execute_val_def. wp_auto.
    wp_bind.
    wp_apply (v1.wp_GetFinalizers_deepown with "[$Hdeepown_m_l]").
    iIntros (old_sl') "(%Hold_sl_nil' & Hold_finalizers)".
    iAssert ("Hold_sl" ∷ old_sl' ↦*{dq} default [] m.(ObjectMetaV.Finalizers') ∗
        "Hrestore_m" ∷ (old_sl' ↦*{dq} default [] m.(ObjectMetaV.Finalizers') -∗
          ObjectMetaV.deepown_l metadata_l m dq))%I
      with "[Hold_finalizers]" as "(Hold_sl & Hrestore_m)".
    { destruct m.(ObjectMetaV.Finalizers') as [finalizers|]
        eqn:Hfinalizers_eq.
      - iDestruct "Hold_finalizers" as (cfinalizers)
          "(Hold_sl & -> & Hrestore_m)".
        iFrame.
      - assert (old_sl' = slice.nil) as -> by
          (apply (proj2 Hold_sl_nil'); done).
        simpl. iSplitL ""; first iApply (own_slice_nil (V := go_string) dq).
        iIntros "_". iFrame. }
    wp_auto.
    iDestruct (own_slice_len with "Hold_sl") as
      %[Hold_sl_len' Hold_sl_nonneg'].
    iDestruct (own_slice_len with "Hnew_finalizers") as
      %[Hnew_sl_len Hnew_sl_nonneg].
    rewrite execute_val_unseal /execute_val_def. wp_auto.
    wp_if_destruct.
    2: { assert (delete_finalizers_changed old_finalizers
        (delete_finalizers_for_gc m options)) as Hchanged.
      { left. intros Hlength_eq.
        rewrite Hlength_eq in Hold_sl_len'. word. }
      assert (delete_should_update_finalizers m options = true) as Hupdate.
      { rewrite /delete_should_update_finalizers /old_finalizers.
        apply bool_decide_eq_true_2. exact Hchanged. }
      iPoseProof ("Hrestore_m" with "Hold_sl") as "Hdeepown_m_l".
      rewrite return_val_unseal /return_val_def. wp_auto.
      iApply ("HΦ" $! true final_sl (Some (delete_finalizers_for_gc m options))).
      rewrite /delete_new_finalizers Hupdate /=.
      iFrame. iSplit; first done. iSplit; first done.
      iSplit; first (iPureIntro; by apply delete_finalizers_for_gc_valid).
      iSplit.
      { iPureIntro. split.
        - intros Hnil. exfalso. exact (Hnew_finalizers_non_nil Hnil).
        - discriminate. }
      done. }
    + rewrite execute_val_unseal /execute_val_def. wp_auto.
      wp_apply wp_map_make1 as (old_set_l) "Hold_set".
      rewrite execute_val_unseal /execute_val_def. wp_auto.
      wp_alloc old_f_ptr as "Hold_f". wp_auto.
      wp_alloc old_i_ptr as "Hold_i". wp_auto.
      iClear "Hi Hf".
      set Iold := (∃ (oi : w64) (oval : go_string),
        "Hi" ∷ old_i_ptr ↦ oi ∗
        "Hf" ∷ old_f_ptr ↦ oval ∗
        "HoldSet" ∷ oldSet_ptr ↦ old_set_l ∗
        "Hold_set" ∷ old_set_l ↦$
          list_to_map (((fun finalizer => (finalizer, true)) <$>
            take (sint.nat oi) old_finalizers)) ∗
        "Hold_sl" ∷ old_sl' ↦*{dq} old_finalizers ∗
        "%Hi_bounds" ∷ ⌜ 0 ≤ sint.Z oi ≤ sint.Z old_sl'.(slice.len) ⌝)%I.
      iAssert Iold with "[Hold_i Hold_f oldSet Hold_set Hold_sl]" as "Hloop".
      { iExists (W64 0), (zero_val go_string). iFrame.
        iPureIntro. word. }
      wp_for "Hloop". wp_if_destruct.
      * destruct (decide (0 ≤ sint.Z oi < sint.Z old_sl'.(slice.len)))
          as [_|Hbounds].
        2: { exfalso. apply Hbounds. split; [lia|word]. }
        destruct (lookup_lt_is_Some_2 old_finalizers (sint.nat oi))
          as [current Hcurrent_lookup].
        { rewrite Hold_sl_len'. word. }
        wp_apply (wp_load_slice_index with "[$Hold_sl]"); [word|done|].
        iIntros "Hold_sl". wp_auto.
        rewrite execute_val_unseal /execute_val_def. wp_auto.
        rewrite execute_val_unseal /execute_val_def. wp_auto.
        wp_apply (wp_map_insert go.string old_set_l _ current true
          with "Hold_set").
        iIntros "Hold_set". wp_auto. iApply wp_for_post_do. wp_auto.
        iAssert Iold with "[Hi Hf HoldSet Hold_set Hold_sl]" as "Hloop".
        { iExists (word.add oi (W64 1)), current.
          assert (sint.nat (word.add oi (W64 1)) = S (sint.nat oi))
            as Hnext by word.
          assert (list_to_map (((fun finalizer => (finalizer, true)) <$>
                take (sint.nat (word.add oi (W64 1))) old_finalizers)) =
              (<[current := true]>
                (list_to_map (((fun finalizer => (finalizer, true)) <$>
                  take (sint.nat oi) old_finalizers)) : gmap go_string bool)))
            as Hmap_eq.
          { rewrite Hnext (take_S_r _ _ current Hcurrent_lookup) fmap_app /=.
            rewrite list_to_map_app /=.
            set (prefix_map := (list_to_map
              (((fun finalizer => (finalizer, true)) <$>
                take (sint.nat oi) old_finalizers)) : gmap go_string bool)).
            fold prefix_map.
            rewrite insert_empty.
            destruct (prefix_map !! current) as [b|] eqn:Hlookup.
            - assert (b = true) as ->.
              { apply elem_of_list_to_map_2 in Hlookup.
                apply list_elem_of_fmap in Hlookup as [x [Heq _]].
                simpl in Heq. congruence. }
              rewrite (union_singleton_r _ _ true true Hlookup).
              by rewrite insert_id.
            - symmetry. by apply insert_union_singleton_r. }
          rewrite Hmap_eq. iFrame. iPureIntro. word. }
        iFrame.
      * assert (sint.nat oi = length old_finalizers) as Hoi_end.
        { rewrite Hold_sl_len'. word. }
        assert (take (sint.nat oi) old_finalizers = old_finalizers)
          as Htake_old_all.
        { apply take_ge. rewrite Hoi_end. lia. }
        iEval (rewrite Htake_old_all) in "Hold_set".
        rewrite execute_val_unseal /execute_val_def. wp_auto.
        wp_alloc new_f_ptr as "Hnew_f". wp_auto.
        wp_alloc new_i_ptr as "Hnew_i". wp_auto.
        iClear "Hi Hf".
        set Inew := (∃ (ni : w64) (nval : go_string),
          "Hi" ∷ new_i_ptr ↦ ni ∗
          "Hf" ∷ new_f_ptr ↦ nval ∗
          "HnewFinalizers" ∷ newFinalizers_ptr ↦ final_sl ∗
          "Hnew_finalizers" ∷ final_sl ↦* delete_finalizers_for_gc m options ∗
          "Hnew_finalizers_cap" ∷
            own_slice_cap go_string final_sl (DfracOwn 1) ∗
          "HoldSet" ∷ oldSet_ptr ↦ old_set_l ∗
          "Hold_set" ∷ old_set_l ↦$
            list_to_map (((fun finalizer => (finalizer, true)) <$> old_finalizers)) ∗
          "Hold_sl" ∷ old_sl' ↦*{dq} old_finalizers ∗
          "%Hi_bounds" ∷ ⌜ 0 ≤ sint.Z ni ≤ sint.Z final_sl.(slice.len) ⌝ ∗
          "%Hseen" ∷ ⌜ ∀ finalizer,
            finalizer ∈ take (sint.nat ni) (delete_finalizers_for_gc m options) →
            finalizer ∈ old_finalizers ⌝)%I.
        iAssert Inew with
          "[Hnew_i Hnew_f HnewFinalizers Hnew_finalizers Hnew_finalizers_cap
            HoldSet Hold_set Hold_sl]" as "Hloop".
        { iExists (W64 0), (zero_val go_string). iFrame.
          iPureIntro. split; [word|]. rewrite take_0. intros ? Hin.
          apply elem_of_nil in Hin. contradiction. }
        wp_for "Hloop". wp_if_destruct.
        -- destruct (decide (0 ≤ sint.Z ni < sint.Z final_sl.(slice.len)))
             as [_|Hbounds]; last word.
           destruct (lookup_lt_is_Some_2 (delete_finalizers_for_gc m options)
             (sint.nat ni)) as [current Hcurrent_lookup].
           { rewrite Hnew_sl_len. word. }
           wp_apply (wp_load_slice_index with "[$Hnew_finalizers]"); [word|done|].
           iIntros "Hnew_finalizers". wp_auto.
           rewrite execute_val_unseal /execute_val_def. wp_auto.
           rewrite execute_val_unseal /execute_val_def. wp_auto.
           wp_apply (wp_map_lookup1 go.string go.bool old_set_l _ current
             with "Hold_set") as "Hold_set".
           rewrite delete_finalizer_set_lookup.
           destruct (decide (current ∈ old_finalizers)) as [Hcurrent_old|Hcurrent_old].
           ++ rewrite (bool_decide_eq_true_2 _ Hcurrent_old). wp_auto.
              iApply wp_for_post_do. wp_auto.
              iAssert Inew with
                "[Hi Hf HnewFinalizers Hnew_finalizers Hnew_finalizers_cap
                  HoldSet Hold_set Hold_sl]" as "Hloop".
              { iExists (word.add ni (W64 1)), current. iFrame.
                iPureIntro. split; [word|].
                intros finalizer Hin.
                assert (sint.nat (word.add ni (W64 1)) =
                  S (sint.nat ni)) as Hnext by word.
                rewrite Hnext (take_S_r _ _ current Hcurrent_lookup) in Hin.
                apply elem_of_app in Hin as [Hin|Hin]; first by apply Hseen.
                apply list_elem_of_singleton in Hin. subst. exact Hcurrent_old. }
              iFrame.
           ++ rewrite (bool_decide_eq_false_2 _ Hcurrent_old). wp_auto.
              iApply wp_for_post_return.
              rewrite return_val_unseal /return_val_def.
              wp_auto.
              assert (delete_finalizers_changed old_finalizers
                (delete_finalizers_for_gc m options)) as Hchanged.
              { right. apply Exists_exists. exists current. split.
                - apply list_elem_of_In. eapply list_elem_of_lookup_2.
                  exact Hcurrent_lookup.
                - exact Hcurrent_old. }
              assert (delete_should_update_finalizers m options = true) as Hupdate.
              { rewrite /delete_should_update_finalizers /old_finalizers.
                apply bool_decide_eq_true_2. exact Hchanged. }
              iPoseProof ("Hrestore_m" with "Hold_sl") as "Hdeepown_m_l".
              iApply ("HΦ" $! true final_sl
                (Some (delete_finalizers_for_gc m options))).
              rewrite /delete_new_finalizers Hupdate /=.
              iFrame. iSplit; first done. iSplit; first done.
              iSplit; first (iPureIntro; by apply delete_finalizers_for_gc_valid).
              iSplit.
              { iPureIntro. split.
                - intros Hnil. exfalso. exact (Hnew_finalizers_non_nil Hnil).
                - discriminate. }
              done.
        -- assert (sint.nat ni = length (delete_finalizers_for_gc m options))
             as Hi_new_end.
           { rewrite Hnew_sl_len. word. }
           assert (∀ finalizer, finalizer ∈ delete_finalizers_for_gc m options →
             finalizer ∈ old_finalizers) as Hnew_subset.
           { intros finalizer Hin. apply Hseen.
             rewrite Hi_new_end. rewrite take_ge; [lia|exact Hin]. }
           assert (¬ delete_finalizers_changed old_finalizers
             (delete_finalizers_for_gc m options)) as Hnot_changed.
           { intros [Hlength_neq|Hexists].
             - apply Hlength_neq.
               rewrite Hold_sl_len' Hnew_sl_len e. done.
             - apply Exists_exists in Hexists as (finalizer & Hin & Hnotin).
               apply (proj2 (list_elem_of_In _ _)) in Hin.
               exact (Hnotin (Hnew_subset finalizer Hin)). }
           assert (delete_should_update_finalizers m options = false) as Hupdate.
           { rewrite /delete_should_update_finalizers /old_finalizers.
             apply bool_decide_eq_false_2. exact Hnot_changed. }
           rewrite execute_val_unseal /execute_val_def. wp_auto.
           rewrite return_val_unseal /return_val_def. wp_auto.
           iPoseProof ("Hrestore_m" with "Hold_sl") as "Hdeepown_m_l".
           iApply ("HΦ" $! false old_sl' m.(ObjectMetaV.Finalizers')).
           rewrite /delete_new_finalizers Hupdate /=.
           iFrame. iPureIntro. split; first done.
           split; first done. split; [exact Hvalid_finalizers|exact Hold_sl_nil'].
Qed.

Definition delete_zero_finalizers o options : Prop :=
  match delete_new_finalizers (KObjectV.objectmeta o) options with
  | None => True
  | Some fs => fs = []
  end.

Definition delete_zero_grace_period o options : Prop :=
  (if delete_graceful o options then
    match delete_new_grace_period_seconds o options with
    | Some grace_period => grace_period
    | None => W64 0
    end
  else W64 0) = W64 0.

(*  This captures exactly when the delete path removes [key] from [s.m].
    Reading [kubernetes_model/apimodel/new.go] top-to-bottom:
    1. We must not take the earlier "already pending graceful deletion" fast path:
      [if pendingGraceful { return nil }].
    2. After GC finalizer processing, the object must have no finalizers left.
    3. The computed grace period must be zero.
    When all three hold, the Go code reaches:
      [if len(metadata.GetFinalizers()) == 0 && gracePeriod == 0 { delete(s.m, key) }] *)
Definition delete_removes_from_state_map o options : Prop :=
  delete_pending_graceful o = false ∧
  delete_zero_finalizers o options ∧
  delete_zero_grace_period o options.

#[global] Instance delete_zero_finalizers_dec o options :
    Decision (delete_zero_finalizers o options).
Proof.
  unfold delete_zero_finalizers.
  destruct (delete_new_finalizers (KObjectV.objectmeta o) options) as
    [finalizers|].
  - destruct finalizers as [|finalizer finalizers].
    + left. done.
    + right. discriminate.
  - left. done.
Defined.

#[global] Instance delete_zero_grace_period_dec o options :
    Decision (delete_zero_grace_period o options).
Proof.
  unfold delete_zero_grace_period.
  destruct (delete_graceful o options).
  - destruct (delete_new_grace_period_seconds o options) as [grace_period|].
    + apply _.
    + left. done.
  - left. done.
Defined.

#[global] Instance delete_removes_from_state_map_dec o options :
    Decision (delete_removes_from_state_map o options).
Proof.
  unfold delete_removes_from_state_map.
  destruct (decide (delete_pending_graceful o = false)) as [Hpending|Hpending].
  2: { right. intros [Hpending' _]. contradiction. }
  destruct (decide (delete_zero_finalizers o options)) as [Hfinalizers|Hfinalizers].
  2: { right. intros [_ [Hfinalizers' _]]. contradiction. }
  destruct (decide (delete_zero_grace_period o options)) as [Hgrace|Hgrace].
  - left. done.
  - right. intros [_ [_ Hgrace']]. contradiction.
Defined.

Context `{!kubernetesModelG Σ}.

Lemma tombed_uid_delete_eq_used_uid_sub
  (abs_state : gmap KKey.t KObjectV.t) (used_uid tombed_uid : gset types.UID.t) key kobj :
  tombed_uid = used_uid ∖ map_to_set (C:=gset types.UID.t)
    (λ (_ : KKey.t) (obj : KObjectV.t), ObjectMetaV.UID' (KObjectV.objectmeta obj)) abs_state →
  map_Forall
    (λ (k' : KKey.t) (obj' : KObjectV.t), ObjectMetaV.UID' (KObjectV.objectmeta kobj) =
    ObjectMetaV.UID' (KObjectV.objectmeta obj') → key = k') abs_state →
  ObjectMetaV.UID' (KObjectV.objectmeta kobj) ∈ used_uid →
  abs_state !! key = Some kobj →
  tombed_uid ∪ {[ObjectMetaV.UID' (KObjectV.objectmeta kobj)]} =
  used_uid ∖ map_to_set (C:=gset types.UID.t)
    (λ (_ : KKey.t) (obj : KObjectV.t), ObjectMetaV.UID' (KObjectV.objectmeta obj)) (delete key abs_state).
Proof.
  intros Htombed Hunique_id Huid_in Hlookup_abs.
  set (uid := ObjectMetaV.UID' (KObjectV.objectmeta kobj)).
  set (uids := λ m : gmap KKey.t KObjectV.t,
    map_to_set (C:=gset types.UID.t)
      (λ (_ : KKey.t) (obj : KObjectV.t), ObjectMetaV.UID' (KObjectV.objectmeta obj))
      m).
  assert (uid ∉ uids (delete key abs_state)) as Huid_not_in_deleted.
  { intros Hcontra.
    rewrite /uids elem_of_map_to_set in Hcontra.
    destruct Hcontra as (key' & obj' & Hlookup_abs' & Huid_eq).
    apply lookup_delete_Some in Hlookup_abs' as [Hkey_neq Hlookup_abs'].
    pose proof (map_Forall_lookup_1 _ _ _ _ Hunique_id Hlookup_abs') as Hkey_eq.
    apply Hkey_neq.
    eapply Hkey_eq.
    symmetry; exact Huid_eq.
  }
  assert (uids abs_state = {[uid]} ∪ uids (delete key abs_state)) as Hmap_to_set_delete.
  { rewrite /uids.
    rewrite <- (insert_delete_id abs_state key kobj Hlookup_abs) at 1.
    assert (delete key abs_state !! key = None) as Hlookup_delete.
    { apply lookup_delete_eq. }
    rewrite (map_to_set_insert_L
      (λ (_ : KKey.t) (obj : KObjectV.t), ObjectMetaV.UID' (KObjectV.objectmeta obj))
      (delete key abs_state) key kobj Hlookup_delete).
    reflexivity.
  }
  rewrite /uids in Huid_not_in_deleted, Hmap_to_set_delete.
  rewrite Htombed Hmap_to_set_delete.
  change (
    (used_uid ∖ ({[uid]} ∪ uids (delete key abs_state))) ∪ {[uid]} =
    used_uid ∖ uids (delete key abs_state)
  ).
  apply set_eq. intros uid'.
  change (
    uid' ∈ (used_uid ∖ ({[uid]} ∪ uids (delete key abs_state))) ∪ {[uid]} ↔
    uid' ∈ used_uid ∖ uids (delete key abs_state)
  ).
  rewrite !elem_of_union !elem_of_difference !elem_of_singleton.
  destruct (decide (uid' = uid)) as [->|Huid_neq].
  - split.
    + intros _. split; [exact Huid_in|exact Huid_not_in_deleted].
    + intros _. right. reflexivity.
  - split.
    + intros Hcase.
      destruct Hcase as [Hcase|Hcase].
      * destruct Hcase as [Huid_used0 Huid_not_in0].
        split; [done|].
        intros Huid_in_deleted0.
        apply Huid_not_in0.
        rewrite elem_of_union.
        right. exact Huid_in_deleted0.
      * exfalso. apply Huid_neq. exact Hcase.
    + intros Hcase.
      destruct Hcase as [Huid_used0 Huid_not_in_deleted0].
      left. split; [done|].
      intros Hcontra.
      rewrite elem_of_union in Hcontra.
      destruct Hcontra as [Huid_eq0|Huid_in_deleted0].
      * rewrite elem_of_singleton in Huid_eq0.
        apply Huid_neq. exact Huid_eq0.
      * exact (Huid_not_in_deleted0 Huid_in_deleted0).
Qed.

Lemma tombed_uid_update_eq_used_uid_sub
  (abs_state : gmap KKey.t KObjectV.t) (used_uid tombed_uid : gset types.UID.t)
  key old_kobj new_kobj :
  tombed_uid = used_uid ∖ map_to_set (C:=gset types.UID.t)
    (λ (_ : KKey.t) (obj : KObjectV.t), ObjectMetaV.UID' (KObjectV.objectmeta obj)) abs_state →
  abs_state !! key = Some old_kobj →
  ObjectMetaV.UID' (KObjectV.objectmeta new_kobj) =
    ObjectMetaV.UID' (KObjectV.objectmeta old_kobj) →
  tombed_uid = used_uid ∖ map_to_set (C:=gset types.UID.t)
    (λ (_ : KKey.t) (obj : KObjectV.t), ObjectMetaV.UID' (KObjectV.objectmeta obj))
    (<[key := new_kobj]> abs_state).
Proof.
  intros Htombed Hlookup_abs Huid_eq.
  set (uid := ObjectMetaV.UID' (KObjectV.objectmeta old_kobj)).
  set (uids := λ m : gmap KKey.t KObjectV.t,
    map_to_set (C:=gset types.UID.t)
      (λ (_ : KKey.t) (obj : KObjectV.t), ObjectMetaV.UID' (KObjectV.objectmeta obj))
      m).
  assert (uids abs_state = {[uid]} ∪ uids (delete key abs_state)) as Hmap_to_set_old.
  { rewrite /uids.
    rewrite <- (insert_delete_id abs_state key old_kobj Hlookup_abs) at 1.
    assert (delete key abs_state !! key = None) as Hlookup_delete.
    { apply lookup_delete_eq. }
    rewrite (map_to_set_insert_L
      (λ (_ : KKey.t) (obj : KObjectV.t), ObjectMetaV.UID' (KObjectV.objectmeta obj))
      (delete key abs_state) key old_kobj Hlookup_delete).
    reflexivity.
  }
  assert (uids (<[key := new_kobj]> abs_state) = {[uid]} ∪ uids (delete key abs_state))
    as Hmap_to_set_new.
  { rewrite /uids.
    rewrite <- (insert_delete_eq abs_state key new_kobj).
    assert (delete key abs_state !! key = None) as Hlookup_delete.
    { apply lookup_delete_eq. }
    rewrite (map_to_set_insert_L
      (λ (_ : KKey.t) (obj : KObjectV.t), ObjectMetaV.UID' (KObjectV.objectmeta obj))
      (delete key abs_state) key new_kobj Hlookup_delete).
    rewrite Huid_eq.
    reflexivity.
  }
  rewrite Htombed.
  change (used_uid ∖ uids abs_state = used_uid ∖ uids (<[key := new_kobj]> abs_state)).
  rewrite Hmap_to_set_old Hmap_to_set_new.
  reflexivity.
Qed.

Definition delete_options_preconditions_resource_version_none (options : DeleteOptionsV.t) : Prop :=
  match options.(DeleteOptionsV.Preconditions') with
  | None => True
  | Some preconditions => preconditions.(PreconditionsV.ResourceVersion') = None
  end.

#[global] Instance delete_options_preconditions_resource_version_none_dec options :
  Decision (delete_options_preconditions_resource_version_none options).
Proof.
  unfold delete_options_preconditions_resource_version_none.
  destruct options.(DeleteOptionsV.Preconditions') as [preconditions|].
  - destruct preconditions.(PreconditionsV.ResourceVersion') as [rv|].
    + right. intros Hcontra. inversion Hcontra.
    + left. done.
  - left. done.
Qed.

Lemma own_meta_frag_equiv_except_resource_version {γ k uid dq meta1 meta2} :
  ObjectMetaV.equiv_except_resource_version meta1 meta2 →
  own_meta_frag γ k uid dq meta2 -∗
  own_meta_frag γ k uid dq meta1.
Proof.
  iIntros (Hmeta_eq) "Hown_meta".
  assert (kview.mk_meta_frag k uid dq meta1 = kview.mk_meta_frag k uid dq meta2) as Hfrag_eq.
  { rewrite /kview.mk_meta_frag /ObjectMetaV.equiv_except_resource_version in Hmeta_eq |- *.
    rewrite Hmeta_eq. done. }
  rewrite /own_meta_frag /kview.own_meta_frag Hfrag_eq.
  iExact "Hown_meta".
Qed.

Lemma delete_preconditions_match_equiv_except_resource_version m1 m2 options :
  ObjectMetaV.equiv_except_resource_version m1 m2 →
  delete_options_preconditions_resource_version_none options →
  delete_preconditions_match options m2 →
  delete_preconditions_match options m1.
Proof.
  intros Hmeta_eq Hrv_none Hmatch.
  rewrite /delete_preconditions_match /delete_options_preconditions_resource_version_none in Hrv_none, Hmatch |- *.
  destruct options.(DeleteOptionsV.Preconditions') as [preconditions|]; [|done].
  destruct preconditions.(PreconditionsV.ResourceVersion') as [rv|]; [done|].
  destruct preconditions.(PreconditionsV.UID') as [uid|]; [|done].
  simpl in Hmatch |- *.
  rewrite (ObjectMetaV.equiv_except_resource_version_uid _ _ Hmeta_eq).
  exact Hmatch.
Qed.

Definition delete_preconditions_match_uid (options : DeleteOptionsV.t) obj_uid : Prop :=
  match options.(DeleteOptionsV.Preconditions') with
  | None => True
  | Some preconditions =>
      (match preconditions.(PreconditionsV.UID') with
       | Some uid => uid = obj_uid
       | None => True
       end)
  end.

Lemma delete_preconditions_match_uid_of_match options uid kmeta :
  uid = kmeta.(ObjectMetaV.UID') →
  delete_preconditions_match options kmeta →
  delete_preconditions_match_uid options uid.
Proof.
  intros Huid_eq Hmatch.
  rewrite /delete_preconditions_match /delete_preconditions_match_uid in Hmatch |- *.
  destruct options.(DeleteOptionsV.Preconditions') as [preconditions|]; [|done].
  destruct preconditions.(PreconditionsV.UID') as [precondition_uid|]; [|done].
  destruct preconditions.(PreconditionsV.ResourceVersion') as [rv|]; simpl in Hmatch;
    rewrite Huid_eq; intuition.
Qed.

Lemma delete_preconditions_match_of_uid_rv_none options uid kmeta :
  uid = kmeta.(ObjectMetaV.UID') →
  delete_options_preconditions_resource_version_none options →
  delete_preconditions_match_uid options uid →
  delete_preconditions_match options kmeta.
Proof.
  intros Huid_eq Hrv_none Huid_match.
  rewrite /delete_options_preconditions_resource_version_none in Hrv_none.
  rewrite /delete_preconditions_match /delete_preconditions_match_uid in Huid_match |- *.
  destruct options.(DeleteOptionsV.Preconditions') as [preconditions|]; [|done].
  destruct preconditions.(PreconditionsV.ResourceVersion') as [rv|]; [done|].
  destruct preconditions.(PreconditionsV.UID') as [precondition_uid|]; simpl in Huid_match |- *.
  - split; [rewrite <-Huid_eq; done|done].
  - split; done.
Qed.

End proof.
