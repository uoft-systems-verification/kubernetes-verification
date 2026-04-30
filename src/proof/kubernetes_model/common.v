From New.proof Require Import prelude empty_ffi.
From New.proof.kubernetes_model Require Export apimodel_init.
From New.proof.k8s_io.apimachinery.pkg.apis.meta Require Import v1.
From New.proof Require Export pure_objects.

Section proof.
Context `{hG: !heapGS Σ} {go_ctx: GoContext}.

Lemma wp_deepCopy i obj:
  {{{ is_pkg_init apimodel ∗
      KObjectV.deepown_i i obj 1
  }}}
    @! apimodel.deepCopy #i
  {{{ i', RET #i';
      KObjectV.deepown_i i' obj 1 ∗
      KObjectV.deepown_i i obj 1
  }}}.
Proof.
Admitted.

Definition storage_object_normalize (obj : KObjectV.t) : KObjectV.t :=
  KObjectV.update_objectmeta obj
    ((KObjectV.objectmeta obj)
       <| ObjectMetaV.ResourceVersion' := ""%go |>
       <| ObjectMetaV.SelfLink' := ""%go |>).

Lemma storage_object_normalize_update_objectmeta_deletionTimestamp obj m :
  storage_object_normalize (KObjectV.update_objectmeta obj m) =
  storage_object_normalize obj →
  m.(ObjectMetaV.DeletionTimestamp') =
  (KObjectV.objectmeta obj).(ObjectMetaV.DeletionTimestamp').
Proof.
  destruct obj as [p|rs].
  - destruct p as [pt pm ps pst]. destruct pm. destruct m. simpl.
    intros H. inversion H. done.
  - destruct rs as [rt rm rspec rstatus]. destruct rm. destruct m. simpl.
    intros H. inversion H. done.
Qed.

Lemma wp_storageObjectDeepEqual i1 i2 obj1 obj2 dq1 dq2 :
  {{{ is_pkg_init apimodel ∗
      KObjectV.deepown_i i1 obj1 dq1 ∗
      KObjectV.deepown_i i2 obj2 dq2
  }}}
    @! apimodel.storageObjectDeepEqual #i1 #i2
  {{{ v, RET #v;
      KObjectV.deepown_i i1 obj1 dq1 ∗
      KObjectV.deepown_i i2 obj2 dq2 ∗
      ⌜ v = true ↔ storage_object_normalize obj1 = storage_object_normalize obj2 ⌝
  }}}.
Proof.
Admitted.

Lemma wp_deletionTimestampForDelete (graceful: bool) (gracePeriod: w64) :
  {{{ is_pkg_init apimodel }}}
    @! apimodel.deletionTimestampForDelete #graceful #gracePeriod
  {{{ l c v, RET #l;
      l ↦ c ∗
      TimeV.deepown c v
  }}}.
Proof.
Admitted.

Lemma wp_State__generateNewUIDAndUpdate l used_uid_l (used_uid : gmap types.UID.t unit) :
  {{{ is_pkg_init apimodel ∗
      l ↦s[apimodel.State :: "usedUID"] used_uid_l ∗
      used_uid_l ↦$ used_uid
  }}}
    l @ (ptrT.id apimodel.State.id) @ "generateNewUIDAndUpdate" #()
  {{{ uid, RET #uid;
      ⌜ used_uid !! uid = None ⌝ ∗
      ⌜ valid_uid uid ⌝ ∗
      l ↦s[apimodel.State :: "usedUID"] used_uid_l ∗
      used_uid_l ↦$ <[uid:=()]> used_uid
  }}}.
Proof.
Admitted.

Lemma wp_State__generateNewRVAndUpdate l used_rv_l (used_rv : gmap go_string unit) :
  {{{ is_pkg_init apimodel ∗
      l ↦s[apimodel.State :: "usedRV"] used_rv_l ∗
      used_rv_l ↦$ used_rv
  }}}
    l @ (ptrT.id apimodel.State.id) @ "generateNewRVAndUpdate" #()
  {{{ rv, RET #rv;
      ⌜ used_rv !! rv = None ⌝ ∗
      ⌜ valid_resource_version rv ⌝ ∗
      l ↦s[apimodel.State :: "usedRV"] used_rv_l ∗
      used_rv_l ↦$ <[rv:=()]> used_rv
  }}}.
Proof.
Admitted.

Lemma wp_State__generateNewName l m_ptr kind namespace generate_name (phys_state : gmap KKey.t interface.t):
  {{{ is_pkg_init apimodel ∗
      ⌜ valid_generate_name generate_name ⌝ ∗
      ⌜ length generate_name ≤ 58 ⌝ ∗
      l ↦s[apimodel.State :: "m"] m_ptr ∗
      m_ptr ↦$ phys_state
  }}}
    l @ (ptrT.id apimodel.State.id) @ "generateNewName" #kind #namespace #generate_name
  {{{ (new_name: go_string), RET #new_name;
      ⌜ new_name ≠ ""%go ⌝ ∗
      ⌜ valid_name new_name ⌝ ∗
      ⌜ phys_state !! {| KKey.Kind' := kind; KKey.Namespace' := namespace; KKey.Name' := new_name;|} = None ⌝ ∗
      l ↦s[apimodel.State :: "m"] m_ptr ∗
      m_ptr ↦$ phys_state
  }}}.
Proof.
Admitted.

Lemma wp_validateObjectMeta i (kind : go_string) l m dq :
  {{{ is_pkg_init apimodel ∗
      ⌜ i = interface.mk (ptrT.id v1.ObjectMeta.id) #l ⌝ ∗
      ObjectMetaV.deepown_l l m dq ∗
      ⌜ ObjectMetaV.valid m ⌝
  }}}
    @! apimodel.validateObjectMeta #i #kind
  {{{ RET #interface.nil;
      ObjectMetaV.deepown_l l m dq
  }}}.
Proof.
Admitted.

Lemma wp_applyValidationAndDefaulting i l o (name : go_string) :
  {{{ is_pkg_init apimodel ∗
      ⌜ KObjectV.valid_interface i l o ⌝ ∗
      KObjectV.deepown_l l o 1 ∗
      ⌜ let m := KObjectV.objectmeta o in
        (m.(ObjectMetaV.GenerateName') ≠ ""%go →
          valid_generate_name m.(ObjectMetaV.GenerateName')) ∧
        m.(ObjectMetaV.Name') ≠ ""%go ∧
        valid_name m.(ObjectMetaV.Name') ∧
        m.(ObjectMetaV.Namespace') ≠ ""%go ∧
        valid_namespace m.(ObjectMetaV.Namespace') ∧
        valid_labels m.(ObjectMetaV.Labels') ∧
        valid_annotations m.(ObjectMetaV.Annotations') ∧
        valid_owner_references m.(ObjectMetaV.OwnerReferences') ∧
        valid_finalizers m.(ObjectMetaV.Finalizers') ∧
        valid_managed_fields m.(ObjectMetaV.ManagedFields') ⌝
  }}}
    @! apimodel.applyValidationAndDefaulting #i #name
  {{{ o', RET #interface.nil;
      KObjectV.deepown_l l o' 1 ∗
      ⌜ KObjectV.same_kind o o' ⌝ ∗
      ⌜ ObjectMetaV.valid (KObjectV.objectmeta o') ⌝ ∗
      ⌜ ObjectSpecV.valid (KObjectV.spec o') ⌝ ∗
      ⌜ ObjectStatusV.valid (KObjectV.status o') ⌝ ∗
      ⌜ KObjectV.typemeta o' = KObjectV.typemeta o ⌝ ∗
      ⌜ KObjectV.objectmeta o' = ((KObjectV.objectmeta o) <| ObjectMetaV.Generation' := W64 1 |>) ⌝ ∗
      ⌜ ObjectSpecV.created (KObjectV.spec o) (KObjectV.spec o') ⌝ ∗
      ⌜ ObjectStatusV.created (KObjectV.status o) (KObjectV.status o') ⌝
  }}}.
Proof.
Admitted.

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

Lemma wp_newPreconditionUIDConflictError (kind name uid1 uid2: go_string) :
  {{{ is_pkg_init apimodel }}}
    @! apimodel.newPreconditionUIDConflictError #kind #name #uid1 #uid2
  {{{ err, RET #err; ⌜ err ≠ interface.nil ⌝ }}}.
Proof. Admitted.

Lemma wp_newPreconditionRVConflictError (kind name rv1 rv2: go_string) :
  {{{ is_pkg_init apimodel }}}
    @! apimodel.newPreconditionRVConflictError #kind #name #rv1 #rv2
  {{{ err, RET #err; ⌜ err ≠ interface.nil ⌝ }}}.
Proof. Admitted.

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
Admitted.

Lemma wp_validateDeletePreconditions i l m options_l options dq (kind : go_string) :
  {{{ is_pkg_init apimodel ∗
      "%Hi" ∷ ⌜ i = interface.mk (ptrT.id v1.ObjectMeta.id) #l ⌝ ∗
      "Hdeepown_m_l" ∷ ObjectMetaV.deepown_l l m dq ∗
      "Hdeepown_options_l" ∷ DeleteOptionsV.deepown_l options_l options dq
  }}}
    @! apimodel.validateDeletePreconditions #i #options_l #kind
  {{{ err, RET #err;
      ⌜ delete_preconditions_match options m ∧ err = interface.nil
        ∨
        ¬ delete_preconditions_match options m ∧ err ≠ interface.nil ⌝ ∗
      ObjectMetaV.deepown_l l m dq ∗
      DeleteOptionsV.deepown_l options_l options dq
  }}}.
Proof. (* This proof is fully written by Codex *)
  wp_start as "H".
  iNamed "H". subst i.
  iDestruct "Hdeepown_options_l" as (coptions) "[Hoptions_l Hdeepown_options]".
  iNamed "Hdeepown_options".
  destruct options.(DeleteOptionsV.Preconditions') as [preconditions|] eqn:Hpreconditions.
  - iDestruct "Hdeepown_preconditions_some" as (cpreconditions) "[Hpreconditions_l Hdeepown_preconditions]".
    iNamed "Hdeepown_preconditions".
    assert (v1.DeleteOptions.Preconditions' coptions ≠ null) as Hpreconditions_not_null.
    { intros Hnull. apply (proj1 Hdeepown_preconditions_none) in Hnull. congruence. }
    assert (bool_decide (v1.DeleteOptions.Preconditions' coptions = null) = false) as Hpreconditions_nonnull_decide.
    { apply bool_decide_false. done. }
    wp_auto.
    rewrite Hpreconditions_nonnull_decide /=.
    wp_auto.
    destruct preconditions.(PreconditionsV.UID') as [uid|] eqn:Huid.
    + iDestruct "Hdeepown_uid_some" as (cuid) "[Huid_l ->]".
      assert (v1.Preconditions.UID' cpreconditions ≠ null) as Huid_not_null.
      { intros Hnull. apply (proj1 Hdeepown_uid_none) in Hnull. congruence. }
      assert (bool_decide (v1.Preconditions.UID' cpreconditions = null) = false) as Huid_nonnull_decide.
      { apply bool_decide_false. done. }
      rewrite Huid_nonnull_decide /=.
      wp_auto.
      wp_apply (v1.wp_GetUID_deepown with "[$Hdeepown_m_l]").
      iIntros "Hdeepown_m_l".
      destruct (decide (uid = m.(ObjectMetaV.UID'))) as [Huid_eq|Huid_neq].
      * rewrite Huid_eq. wp_auto.
        rewrite bool_decide_true //. wp_auto.
        destruct preconditions.(PreconditionsV.ResourceVersion') as [rv|] eqn:Hrv.
        -- iDestruct "Hdeepown_resourceversion_some" as (crv) "[Hrv_l ->]".
           assert (v1.Preconditions.ResourceVersion' cpreconditions ≠ null) as Hrv_not_null.
           { intros Hnull. apply (proj1 Hdeepown_resourceversion_none) in Hnull. congruence. }
           assert (bool_decide (v1.Preconditions.ResourceVersion' cpreconditions = null) = false) as Hrv_nonnull_decide.
           { apply bool_decide_false. done. }
           rewrite Hrv_nonnull_decide /=.
           wp_auto.
           wp_apply (v1.wp_GetResourceVersion_deepown with "[$Hdeepown_m_l]").
           iIntros "Hdeepown_m_l".
           destruct (decide (rv = m.(ObjectMetaV.ResourceVersion'))) as [Hrv_eq|Hrv_neq].
           ++ rewrite Hrv_eq. wp_auto.
              rewrite bool_decide_true //. wp_auto.
              iAssert ((match preconditions.(PreconditionsV.UID') with
                | Some vu => ∃ cu, v1.Preconditions.UID' cpreconditions ↦{dq} cu ∗ ⌜ cu = vu ⌝
                | None => True
                end)%I) with "[Huid_l]" as "Hdeepown_uid_some".
              { rewrite Huid /=. iExists (ObjectMetaV.UID' m). iFrame "Huid_l". iPureIntro. symmetry. done. }
              iAssert ((match preconditions.(PreconditionsV.ResourceVersion') with
                | Some vrv => ∃ crv, v1.Preconditions.ResourceVersion' cpreconditions ↦{dq} crv ∗ ⌜ crv = vrv ⌝
                | None => True
                end)%I) with "[Hrv_l]" as "Hdeepown_resourceversion_some".
              { rewrite Hrv /=. iExists (ObjectMetaV.ResourceVersion' m). iFrame "Hrv_l". iPureIntro. symmetry. done. }
              iAssert (PreconditionsV.deepown cpreconditions preconditions dq)
                with "[Hdeepown_uid_some Hdeepown_resourceversion_some]" as "Hdeepown_preconditions".
              { rewrite /PreconditionsV.deepown Huid Hrv /=. iFrame. iPureIntro. done. }
              iAssert ((match options.(DeleteOptionsV.Preconditions') with
                | Some vp =>
                    ∃ cp, v1.DeleteOptions.Preconditions' coptions ↦{dq} cp ∗ PreconditionsV.deepown cp vp dq
                | None => True
                end)%I) with "[Hpreconditions_l Hdeepown_preconditions]" as "Hdeepown_preconditions_some".
              { rewrite Hpreconditions /=. iExists cpreconditions. iFrame. }
              iAssert (DeleteOptionsV.deepown_l options_l options dq)
                with "[Hoptions_l Hdeepown_graceperiodseconds_some Hdeepown_preconditions_some Hdeepown_orphandependents_some Hdeepown_propagationpolicy_some]" as "Hdeepown_options_l".
              { iExists coptions.
                rewrite /DeleteOptionsV.deepown Hpreconditions /=.
                iFrame.
                iPureIntro.
                done. }
              iApply "HΦ".
              iFrame "Hdeepown_m_l Hdeepown_options_l".
              iPureIntro.
              left. split.
              { rewrite /delete_preconditions_match Hpreconditions Huid Hrv /=. split; assumption. }
              done.
           ++ wp_auto.
              rewrite bool_decide_false //.
              wp_auto.
              wp_apply (wp_GetName_deepown with "[$Hdeepown_m_l]").
              iIntros "Hdeepown_m_l".
              wp_auto.
              wp_apply (v1.wp_GetResourceVersion_deepown with "[$Hdeepown_m_l]").
              iIntros "Hdeepown_m_l".
              wp_auto.
              wp_apply (wp_newPreconditionRVConflictError with "[$]").
              iIntros (err) "%Herr_non_nil".
              wp_auto.
              iAssert ((match preconditions.(PreconditionsV.UID') with
                | Some vu => ∃ cu, v1.Preconditions.UID' cpreconditions ↦{dq} cu ∗ ⌜ cu = vu ⌝
                | None => True
                end)%I) with "[Huid_l]" as "Hdeepown_uid_some".
              { rewrite Huid /=. iExists (ObjectMetaV.UID' m). iFrame "Huid_l". iPureIntro. symmetry. done. }
              iAssert ((match preconditions.(PreconditionsV.ResourceVersion') with
                | Some vrv => ∃ crv, v1.Preconditions.ResourceVersion' cpreconditions ↦{dq} crv ∗ ⌜ crv = vrv ⌝
                | None => True
                end)%I) with "[Hrv_l]" as "Hdeepown_resourceversion_some".
              { rewrite Hrv /=. iExists rv. iFrame "Hrv_l". iPureIntro. done. }
              iAssert (PreconditionsV.deepown cpreconditions preconditions dq)
                with "[Hdeepown_uid_some Hdeepown_resourceversion_some]" as "Hdeepown_preconditions".
              { rewrite /PreconditionsV.deepown Huid Hrv /=. iFrame. iPureIntro. done. }
              iAssert ((match options.(DeleteOptionsV.Preconditions') with
                | Some vp =>
                    ∃ cp, v1.DeleteOptions.Preconditions' coptions ↦{dq} cp ∗ PreconditionsV.deepown cp vp dq
                | None => True
                end)%I) with "[Hpreconditions_l Hdeepown_preconditions]" as "Hdeepown_preconditions_some".
              { rewrite Hpreconditions /=. iExists cpreconditions. iFrame. }
              iAssert (DeleteOptionsV.deepown_l options_l options dq)
                with "[Hoptions_l Hdeepown_graceperiodseconds_some Hdeepown_preconditions_some Hdeepown_orphandependents_some Hdeepown_propagationpolicy_some]" as "Hdeepown_options_l".
              { iExists coptions.
                rewrite /DeleteOptionsV.deepown Hpreconditions /=.
                iFrame.
                iPureIntro.
                done. }
              iApply "HΦ".
              iFrame "Hdeepown_m_l Hdeepown_options_l".
              iPureIntro.
              right. split.
              { rewrite /delete_preconditions_match Hpreconditions Huid Hrv /=.
                intros [_ Hmatch]. apply Hrv_neq. exact Hmatch. }
              done.
        -- assert (v1.Preconditions.ResourceVersion' cpreconditions = null) as Hrv_null.
           { apply (proj2 Hdeepown_resourceversion_none). done. }
           rewrite bool_decide_true //=.
           wp_auto.
           iAssert ((match preconditions.(PreconditionsV.UID') with
             | Some vu => ∃ cu, v1.Preconditions.UID' cpreconditions ↦{dq} cu ∗ ⌜ cu = vu ⌝
             | None => True
             end)%I) with "[Huid_l]" as "Hdeepown_uid_some".
           { rewrite Huid /=. iExists (ObjectMetaV.UID' m). iFrame "Huid_l". iPureIntro. symmetry. done. }
           iAssert ((match preconditions.(PreconditionsV.ResourceVersion') with
             | Some vrv => ∃ crv, v1.Preconditions.ResourceVersion' cpreconditions ↦{dq} crv ∗ ⌜ crv = vrv ⌝
             | None => True
             end)%I) as "Hdeepown_resourceversion_some_rebuild".
           { rewrite Hrv /=. done. }
           iAssert (PreconditionsV.deepown cpreconditions preconditions dq)
             with "[Hdeepown_uid_some Hdeepown_resourceversion_some_rebuild]" as "Hdeepown_preconditions".
           { rewrite /PreconditionsV.deepown Huid Hrv /=. iFrame. iPureIntro. done. }
           iAssert ((match options.(DeleteOptionsV.Preconditions') with
             | Some vp =>
                 ∃ cp, v1.DeleteOptions.Preconditions' coptions ↦{dq} cp ∗ PreconditionsV.deepown cp vp dq
             | None => True
             end)%I) with "[Hpreconditions_l Hdeepown_preconditions]" as "Hdeepown_preconditions_some".
           { rewrite Hpreconditions /=. iExists cpreconditions. iFrame. }
           iAssert (DeleteOptionsV.deepown_l options_l options dq)
             with "[Hoptions_l Hdeepown_graceperiodseconds_some Hdeepown_preconditions_some Hdeepown_orphandependents_some Hdeepown_propagationpolicy_some]" as "Hdeepown_options_l".
           { iExists coptions.
             rewrite /DeleteOptionsV.deepown Hpreconditions /=.
             iFrame.
             iPureIntro.
             done. }
           iApply "HΦ".
           iFrame "Hdeepown_m_l Hdeepown_options_l".
           iPureIntro.
           left. split.
           { rewrite /delete_preconditions_match Hpreconditions Huid Hrv /=. split; [assumption|done]. }
           done.
      * wp_auto.
        rewrite bool_decide_false //.
        wp_auto.
        wp_apply (wp_GetName_deepown with "[$Hdeepown_m_l]").
        iIntros "Hdeepown_m_l".
        wp_auto.
        wp_apply (v1.wp_GetUID_deepown with "[$Hdeepown_m_l]").
        iIntros "Hdeepown_m_l".
        wp_auto.
        wp_apply (wp_newPreconditionUIDConflictError with "[$]").
        iIntros (err) "%Herr_non_nil".
        wp_auto.
        iAssert ((match preconditions.(PreconditionsV.UID') with
          | Some vu => ∃ cu, v1.Preconditions.UID' cpreconditions ↦{dq} cu ∗ ⌜ cu = vu ⌝
          | None => True
          end)%I) with "[Huid_l]" as "Hdeepown_uid_some".
        { rewrite Huid /=. iExists uid. iFrame "Huid_l". iPureIntro. done. }
        iAssert (PreconditionsV.deepown cpreconditions preconditions dq)
          with "[Hdeepown_uid_some Hdeepown_resourceversion_some]" as "Hdeepown_preconditions".
        { rewrite /PreconditionsV.deepown Huid /=. iFrame. iPureIntro. done. }
        iAssert ((match options.(DeleteOptionsV.Preconditions') with
          | Some vp =>
              ∃ cp, v1.DeleteOptions.Preconditions' coptions ↦{dq} cp ∗ PreconditionsV.deepown cp vp dq
          | None => True
          end)%I) with "[Hpreconditions_l Hdeepown_preconditions]" as "Hdeepown_preconditions_some".
        { rewrite Hpreconditions /=. iExists cpreconditions. iFrame. }
        iAssert (DeleteOptionsV.deepown_l options_l options dq)
          with "[Hoptions_l Hdeepown_graceperiodseconds_some Hdeepown_preconditions_some Hdeepown_orphandependents_some Hdeepown_propagationpolicy_some]" as "Hdeepown_options_l".
        { iExists coptions.
          rewrite /DeleteOptionsV.deepown Hpreconditions /=.
          iFrame.
          iPureIntro.
          done. }
        iApply "HΦ".
        iFrame "Hdeepown_m_l Hdeepown_options_l".
        iPureIntro.
        right. split.
        { rewrite /delete_preconditions_match Hpreconditions Huid /=.
          intros [Hmatch _]. apply Huid_neq. exact Hmatch. }
        done.
    + assert (v1.Preconditions.UID' cpreconditions = null) as Huid_null.
      { apply (proj2 Hdeepown_uid_none). done. }
      rewrite bool_decide_true //=.
      wp_auto.
      destruct preconditions.(PreconditionsV.ResourceVersion') as [rv|] eqn:Hrv.
      * iDestruct "Hdeepown_resourceversion_some" as (crv) "[Hrv_l ->]".
        assert (v1.Preconditions.ResourceVersion' cpreconditions ≠ null) as Hrv_not_null.
        { intros Hnull. apply (proj1 Hdeepown_resourceversion_none) in Hnull. congruence. }
        assert (bool_decide (v1.Preconditions.ResourceVersion' cpreconditions = null) = false) as Hrv_nonnull_decide.
        { apply bool_decide_false. done. }
        rewrite Hrv_nonnull_decide /=.
        wp_auto.
        wp_apply (v1.wp_GetResourceVersion_deepown with "[$Hdeepown_m_l]").
        iIntros "Hdeepown_m_l".
        destruct (decide (rv = m.(ObjectMetaV.ResourceVersion'))) as [Hrv_eq|Hrv_neq].
        -- rewrite Hrv_eq. wp_auto.
           rewrite bool_decide_true //. wp_auto.
           iAssert ((match preconditions.(PreconditionsV.UID') with
             | Some vu => ∃ cu, v1.Preconditions.UID' cpreconditions ↦{dq} cu ∗ ⌜ cu = vu ⌝
             | None => True
             end)%I) as "Hdeepown_uid_some_rebuild".
           { rewrite Huid /=. done. }
           iAssert ((match preconditions.(PreconditionsV.ResourceVersion') with
             | Some vrv => ∃ crv, v1.Preconditions.ResourceVersion' cpreconditions ↦{dq} crv ∗ ⌜ crv = vrv ⌝
             | None => True
             end)%I) with "[Hrv_l]" as "Hdeepown_resourceversion_some".
           { rewrite Hrv /=. iExists (ObjectMetaV.ResourceVersion' m). iFrame "Hrv_l". iPureIntro. symmetry. done. }
           iAssert (PreconditionsV.deepown cpreconditions preconditions dq)
             with "[Hdeepown_uid_some_rebuild Hdeepown_resourceversion_some]" as "Hdeepown_preconditions".
           { rewrite /PreconditionsV.deepown Huid Hrv /=. iFrame. iPureIntro. done. }
           iAssert ((match options.(DeleteOptionsV.Preconditions') with
             | Some vp =>
                 ∃ cp, v1.DeleteOptions.Preconditions' coptions ↦{dq} cp ∗ PreconditionsV.deepown cp vp dq
             | None => True
             end)%I) with "[Hpreconditions_l Hdeepown_preconditions]" as "Hdeepown_preconditions_some".
           { rewrite Hpreconditions /=. iExists cpreconditions. iFrame. }
           iAssert (DeleteOptionsV.deepown_l options_l options dq)
             with "[Hoptions_l Hdeepown_graceperiodseconds_some Hdeepown_preconditions_some Hdeepown_orphandependents_some Hdeepown_propagationpolicy_some]" as "Hdeepown_options_l".
           { iExists coptions.
             rewrite /DeleteOptionsV.deepown Hpreconditions /=.
             iFrame.
             iPureIntro.
             done. }
           iApply "HΦ".
           iFrame "Hdeepown_m_l Hdeepown_options_l".
           iPureIntro.
           left. split.
           { rewrite /delete_preconditions_match Hpreconditions Huid Hrv /=. split; [done|assumption]. }
           done.
        -- wp_auto.
           rewrite bool_decide_false //.
           wp_auto.
           wp_apply (wp_GetName_deepown with "[$Hdeepown_m_l]").
           iIntros "Hdeepown_m_l".
           wp_auto.
           wp_apply (v1.wp_GetResourceVersion_deepown with "[$Hdeepown_m_l]").
           iIntros "Hdeepown_m_l".
           wp_auto.
           wp_apply (wp_newPreconditionRVConflictError with "[$]").
           iIntros (err) "%Herr_non_nil".
           wp_auto.
           iAssert ((match preconditions.(PreconditionsV.UID') with
             | Some vu => ∃ cu, v1.Preconditions.UID' cpreconditions ↦{dq} cu ∗ ⌜ cu = vu ⌝
             | None => True
             end)%I) as "Hdeepown_uid_some_rebuild".
           { rewrite Huid /=. done. }
           iAssert ((match preconditions.(PreconditionsV.ResourceVersion') with
             | Some vrv => ∃ crv, v1.Preconditions.ResourceVersion' cpreconditions ↦{dq} crv ∗ ⌜ crv = vrv ⌝
             | None => True
             end)%I) with "[Hrv_l]" as "Hdeepown_resourceversion_some".
           { rewrite Hrv /=. iExists rv. iFrame "Hrv_l". iPureIntro. done. }
           iAssert (PreconditionsV.deepown cpreconditions preconditions dq)
             with "[Hdeepown_uid_some_rebuild Hdeepown_resourceversion_some]" as "Hdeepown_preconditions".
           { rewrite /PreconditionsV.deepown Huid Hrv /=. iFrame. iPureIntro. done. }
           iAssert ((match options.(DeleteOptionsV.Preconditions') with
             | Some vp =>
                 ∃ cp, v1.DeleteOptions.Preconditions' coptions ↦{dq} cp ∗ PreconditionsV.deepown cp vp dq
             | None => True
             end)%I) with "[Hpreconditions_l Hdeepown_preconditions]" as "Hdeepown_preconditions_some".
           { rewrite Hpreconditions /=. iExists cpreconditions. iFrame. }
           iAssert (DeleteOptionsV.deepown_l options_l options dq)
             with "[Hoptions_l Hdeepown_graceperiodseconds_some Hdeepown_preconditions_some Hdeepown_orphandependents_some Hdeepown_propagationpolicy_some]" as "Hdeepown_options_l".
           { iExists coptions.
             rewrite /DeleteOptionsV.deepown Hpreconditions /=.
             iFrame.
             iPureIntro.
             done. }
           iApply "HΦ".
           iFrame "Hdeepown_m_l Hdeepown_options_l".
           iPureIntro.
           right. split.
           { rewrite /delete_preconditions_match Hpreconditions Huid Hrv /=.
             intros [_ Hmatch]. apply Hrv_neq. exact Hmatch. }
           done.
      * assert (v1.Preconditions.ResourceVersion' cpreconditions = null) as Hrv_null.
        { apply (proj2 Hdeepown_resourceversion_none). done. }
        rewrite bool_decide_true //=.
        wp_auto.
        iAssert ((match preconditions.(PreconditionsV.UID') with
          | Some vu => ∃ cu, v1.Preconditions.UID' cpreconditions ↦{dq} cu ∗ ⌜ cu = vu ⌝
          | None => True
          end)%I) as "Hdeepown_uid_some_rebuild".
        { rewrite Huid /=. done. }
        iAssert ((match preconditions.(PreconditionsV.ResourceVersion') with
          | Some vrv => ∃ crv, v1.Preconditions.ResourceVersion' cpreconditions ↦{dq} crv ∗ ⌜ crv = vrv ⌝
          | None => True
          end)%I) as "Hdeepown_resourceversion_some_rebuild".
        { rewrite Hrv /=. done. }
        iAssert (PreconditionsV.deepown cpreconditions preconditions dq)
          with "[Hdeepown_uid_some_rebuild Hdeepown_resourceversion_some_rebuild]" as "Hdeepown_preconditions".
        { rewrite /PreconditionsV.deepown Huid Hrv /=. iFrame. iPureIntro. done. }
        iAssert ((match options.(DeleteOptionsV.Preconditions') with
          | Some vp =>
              ∃ cp, v1.DeleteOptions.Preconditions' coptions ↦{dq} cp ∗ PreconditionsV.deepown cp vp dq
          | None => True
          end)%I) with "[Hpreconditions_l Hdeepown_preconditions]" as "Hdeepown_preconditions_some".
        { rewrite Hpreconditions /=. iExists cpreconditions. iFrame. done. }
        iAssert (DeleteOptionsV.deepown_l options_l options dq)
          with "[Hoptions_l Hdeepown_graceperiodseconds_some Hdeepown_preconditions_some Hdeepown_orphandependents_some Hdeepown_propagationpolicy_some]" as "Hdeepown_options_l".
        { iExists coptions.
          rewrite /DeleteOptionsV.deepown Hpreconditions /=.
          iFrame.
          iPureIntro.
          done. }
        iApply "HΦ".
        iFrame "Hdeepown_m_l Hdeepown_options_l".
        iPureIntro.
        left. split.
        { rewrite /delete_preconditions_match Hpreconditions Huid Hrv /=. split; done. }
        done.
  - assert (v1.DeleteOptions.Preconditions' coptions = null) as Hpreconditions_null.
    { apply (proj2 Hdeepown_preconditions_none). done. }
    wp_auto.
    rewrite bool_decide_true //.
    wp_auto.
    iAssert (DeleteOptionsV.deepown_l options_l options dq)
      with "[Hoptions_l Hdeepown_graceperiodseconds_some Hdeepown_preconditions_some Hdeepown_orphandependents_some Hdeepown_propagationpolicy_some]" as "Hdeepown_options_l".
    { iExists coptions.
      rewrite /DeleteOptionsV.deepown Hpreconditions /=.
      iFrame.
      iPureIntro.
      done. }
    iApply "HΦ".
    iFrame "Hdeepown_m_l Hdeepown_options_l".
    iPureIntro.
    left. split.
    { rewrite /delete_preconditions_match Hpreconditions /=. done. }
    done.
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
    @! apimodel.checkGracefulDelete #i #options_l
  {{{ graceful pendingGraceful options',
      RET (#graceful, #pendingGraceful, #interface.nil);
      KObjectV.deepown_l l o 1 ∗
      DeleteOptionsV.deepown_l options_l options' 1 ∗
      ⌜ pendingGraceful = true →
        (KObjectV.objectmeta o).(ObjectMetaV.DeletionTimestamp') ≠ None ⌝ ∗
      ⌜ graceful = delete_graceful o options ⌝ ∗
      ⌜ pendingGraceful = delete_pending_graceful o ⌝ ∗
      ⌜ options' = (options <| DeleteOptionsV.GracePeriodSeconds' :=
        delete_new_grace_period_seconds o options |>) ⌝
  }}}.
Proof.
Admitted.

(* delete_should_update_finalizers and delete_new_finalizers abstract the result of deletionFinalizersForGarbageCollection *)
Axiom delete_should_update_finalizers : ObjectMetaV.t -> DeleteOptionsV.t -> bool.
Axiom delete_new_finalizers : ObjectMetaV.t -> DeleteOptionsV.t -> option (list go_string).

Lemma wp_deletionFinalizersForGarbageCollection metadata_i metadata_l m options_l options dq :
  {{{ is_pkg_init apimodel ∗
      "%Hmetadata" ∷ ⌜ metadata_i = interface.mk (ptrT.id v1.ObjectMeta.id) #metadata_l ⌝ ∗
      "Hdeepown_m_l" ∷ ObjectMetaV.deepown_l metadata_l m dq ∗
      "Hdeepown_options_l" ∷ DeleteOptionsV.deepown_l options_l options dq ∗
      "%Hvalid_finalizers" ∷ ⌜ valid_finalizers m.(ObjectMetaV.Finalizers') ⌝
  }}}
    @! apimodel.deletionFinalizersForGarbageCollection #metadata_i #options_l
  {{{ should_update_finalizers new_finalizers_sl new_finalizers, RET (#should_update_finalizers, #new_finalizers_sl);
      ⌜ should_update_finalizers = delete_should_update_finalizers m options ⌝ ∗
      ⌜ new_finalizers = delete_new_finalizers m options ⌝ ∗
      ⌜ valid_finalizers new_finalizers ⌝ ∗
      ⌜ new_finalizers_sl = slice.nil ↔ new_finalizers = None ⌝ ∗
      (match new_finalizers with
      | Some fs => ∃ cfs, new_finalizers_sl ↦* cfs ∗ ⌜ cfs = fs ⌝
      | None => True%I
      end) ∗
      ObjectMetaV.deepown_l metadata_l m dq ∗
      DeleteOptionsV.deepown_l options_l options dq
  }}}.
Proof.
Admitted.

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

Axiom delete_removes_from_state_map_dec :
  forall (o : KObjectV.t) (options : DeleteOptionsV.t),
    Decision (delete_removes_from_state_map o options).
Global Existing Instance delete_removes_from_state_map_dec.

End proof.
