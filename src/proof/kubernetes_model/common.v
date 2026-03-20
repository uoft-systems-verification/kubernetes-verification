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

Lemma wp_State__generateNewUIDAndUpdate l used_uid_l (used_uid : gmap types.UID.t unit) :
  {{{ is_pkg_init apimodel ∗
      l ↦s[apimodel.State :: "usedUID"] used_uid_l ∗
      used_uid_l ↦$ used_uid
  }}}
    l @ (ptrT.id apimodel.State.id) @ "generateNewUIDAndUpdate" #()
  {{{ uid, RET #uid;
      ⌜ used_uid !! uid = None ⌝ ∗
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
      l ↦s[apimodel.State :: "usedRV"] used_rv_l ∗
      used_rv_l ↦$ <[rv:=()]> used_rv
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

Definition delete_preconditions_match (m : ObjectMetaV.t) (options : DeleteOptionsV.t) : Prop :=
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

Lemma wp_validateDeletePreconditions i l m options_l options dq (kind : go_string) :
  {{{ is_pkg_init apimodel ∗
      "%Hi" ∷ ⌜ i = interface.mk (ptrT.id v1.ObjectMeta.id) #l ⌝ ∗
      "Hdeepown_m_l" ∷ ObjectMetaV.deepown_l l m dq ∗
      "Hdeepown_options_l" ∷ DeleteOptionsV.deepown_l options_l options dq ∗
      "%Hpre" ∷ ⌜ delete_preconditions_match m options ⌝
  }}}
    @! apimodel.validateDeletePreconditions #i #options_l #kind
  {{{ RET #interface.nil;
      ObjectMetaV.deepown_l l m dq ∗
      DeleteOptionsV.deepown_l options_l options dq
  }}}.
Proof. (* This proof is fully written by Codex *)
  wp_start as "H".
  iNamed "H". subst i.
  iDestruct "Hdeepown_options_l" as (coptions) "[Hoptions_l Hdeepown_options]".
  iNamed "Hdeepown_options".
  unfold delete_preconditions_match in Hpre.
  destruct options.(DeleteOptionsV.Preconditions') as [preconditions|] eqn:Hpreconditions in Hpre |- *.
  - iDestruct "Hdeepown_preconditions_some" as (cpreconditions) "[Hpreconditions_l Hdeepown_preconditions]".
    iNamed "Hdeepown_preconditions".
    assert (v1.DeleteOptions.Preconditions' coptions ≠ null) as Hpreconditions_not_null.
    { intros Hnull.
      apply (proj1 Hdeepown_preconditions_none) in Hnull.
      congruence.
    }
    assert (bool_decide (v1.DeleteOptions.Preconditions' coptions = null) = false) as Hpreconditions_nonnull_decide.
    { apply bool_decide_false. done. }
    wp_auto.
    rewrite Hpreconditions_nonnull_decide.
    wp_auto.
    destruct preconditions.(PreconditionsV.UID') as [uid|] eqn:Huid in Hpre |- *.
    + destruct Hpre as [Huid_eq Hpre].
      iDestruct "Hdeepown_uid_some" as (cuid) "[Huid_l ->]".
      assert (v1.Preconditions.UID' cpreconditions ≠ null) as Huid_not_null.
      { intros Hnull.
        apply (proj1 Hdeepown_uid_none) in Hnull.
        congruence.
      }
      assert (bool_decide (v1.Preconditions.UID' cpreconditions = null) = false) as Huid_nonnull_decide.
      { apply bool_decide_false. done. }
      rewrite Huid_nonnull_decide /=.
      wp_auto.
      wp_apply (v1.wp_GetUID_deepown with "[$Hdeepown_m_l]").
      iIntros "Hdeepown_m_l".
      rewrite Huid_eq. wp_auto.
      rewrite bool_decide_true //. wp_auto.
      destruct preconditions.(PreconditionsV.ResourceVersion') as [rv|] eqn:Hrv in Hpre |- *.
      * rename Hpre into Hrv_eq.
        iDestruct "Hdeepown_resourceversion_some" as (crv) "[Hrv_l ->]".
        assert (v1.Preconditions.ResourceVersion' cpreconditions ≠ null) as Hrv_not_null.
        { intros Hnull.
          apply (proj1 Hdeepown_resourceversion_none) in Hnull.
          congruence.
        }
        assert (bool_decide (v1.Preconditions.ResourceVersion' cpreconditions = null) = false) as Hrv_nonnull_decide.
        { apply bool_decide_false. done. }
        rewrite Hrv_nonnull_decide /=.
        wp_auto.
        wp_apply (v1.wp_GetResourceVersion_deepown with "[$Hdeepown_m_l]").
        iIntros "Hdeepown_m_l".
        rewrite Hrv_eq. wp_auto.
        rewrite bool_decide_true //. wp_auto.
        iAssert ((match preconditions.(PreconditionsV.UID') with
          | Some vu => ∃ cu, v1.Preconditions.UID' cpreconditions ↦{dq} cu ∗ ⌜ cu = vu ⌝
          | None => True
          end)%I) with "[Huid_l]" as "Huid_some_packed".
        { rewrite Huid /=. iExists (ObjectMetaV.UID' m). iFrame "Huid_l". iPureIntro. symmetry. done. }
        iAssert ((match preconditions.(PreconditionsV.ResourceVersion') with
          | Some vrv => ∃ crv, v1.Preconditions.ResourceVersion' cpreconditions ↦{dq} crv ∗ ⌜ crv = vrv ⌝
          | None => True
          end)%I) with "[Hrv_l]" as "Hrv_some_packed".
        { rewrite Hrv /=. iExists (ObjectMetaV.ResourceVersion' m). iFrame "Hrv_l". iPureIntro. symmetry. done. }
        iAssert (PreconditionsV.deepown cpreconditions preconditions dq)
          with "[Huid_some_packed Hrv_some_packed]" as "Hpreconditions_packed".
        { rewrite /PreconditionsV.deepown Huid Hrv /=. iFrame. iPureIntro. done. }
        iAssert ((match options.(DeleteOptionsV.Preconditions') with
          | Some vp =>
              ∃ cp, v1.DeleteOptions.Preconditions' coptions ↦{dq} cp ∗ PreconditionsV.deepown cp vp dq
          | None => True
          end)%I) with "[Hpreconditions_l Hpreconditions_packed]" as "Hpreconditions_some_packed".
        { rewrite Hpreconditions /=. iExists cpreconditions. iFrame "Hpreconditions_l Hpreconditions_packed". }
        iApply "HΦ".
        iFrame "Hdeepown_m_l".
        iExists coptions.
        iFrame.
        iPureIntro.
        done.
      * assert (v1.Preconditions.ResourceVersion' cpreconditions = null) as Hrv_null.
        { apply (proj2 Hdeepown_resourceversion_none). done. }
        rewrite bool_decide_true //=.
        wp_auto.
        iAssert ((match preconditions.(PreconditionsV.UID') with
          | Some vu => ∃ cu, v1.Preconditions.UID' cpreconditions ↦{dq} cu ∗ ⌜ cu = vu ⌝
          | None => True
          end)%I) with "[Huid_l]" as "Huid_some_packed".
        { rewrite Huid /=. iExists (ObjectMetaV.UID' m). iFrame "Huid_l". iPureIntro. symmetry. done. }
        iAssert ((match preconditions.(PreconditionsV.ResourceVersion') with
          | Some vrv => ∃ crv, v1.Preconditions.ResourceVersion' cpreconditions ↦{dq} crv ∗ ⌜ crv = vrv ⌝
          | None => True
          end)%I) as "Hrv_some_packed".
        { rewrite Hrv /=. done. }
        iAssert (PreconditionsV.deepown cpreconditions preconditions dq)
          with "[Huid_some_packed Hrv_some_packed]" as "Hpreconditions_packed".
        { rewrite /PreconditionsV.deepown Huid Hrv /=. iFrame. iPureIntro. done. }
        iAssert ((match options.(DeleteOptionsV.Preconditions') with
          | Some vp =>
              ∃ cp, v1.DeleteOptions.Preconditions' coptions ↦{dq} cp ∗ PreconditionsV.deepown cp vp dq
          | None => True
          end)%I) with "[Hpreconditions_l Hpreconditions_packed]" as "Hpreconditions_some_packed".
        { rewrite Hpreconditions /=. iExists cpreconditions. iFrame "Hpreconditions_l Hpreconditions_packed". }
        iApply "HΦ".
        iFrame "Hdeepown_m_l".
        iExists coptions.
        iFrame.
        iPureIntro.
        done.
    + destruct Hpre as [_ Hpre].
      assert (v1.Preconditions.UID' cpreconditions = null) as Huid_null.
      { apply (proj2 Hdeepown_uid_none). done. }
      rewrite bool_decide_true //=.
      wp_auto.
      destruct preconditions.(PreconditionsV.ResourceVersion') as [rv|] eqn:Hrv in Hpre |- *.
      * rename Hpre into Hrv_eq.
        iDestruct "Hdeepown_resourceversion_some" as (crv) "[Hrv_l ->]".
        assert (v1.Preconditions.ResourceVersion' cpreconditions ≠ null) as Hrv_not_null.
        { intros Hnull.
          apply (proj1 Hdeepown_resourceversion_none) in Hnull.
          congruence.
        }
        assert (bool_decide (v1.Preconditions.ResourceVersion' cpreconditions = null) = false) as Hrv_nonnull_decide.
        { apply bool_decide_false. done. }
        rewrite Hrv_nonnull_decide /=.
        wp_auto.
        wp_apply (v1.wp_GetResourceVersion_deepown with "[$Hdeepown_m_l]").
        iIntros "Hdeepown_m_l".
        rewrite Hrv_eq. wp_auto.
        rewrite bool_decide_true //. wp_auto.
        iAssert ((match preconditions.(PreconditionsV.UID') with
          | Some vu => ∃ cu, v1.Preconditions.UID' cpreconditions ↦{dq} cu ∗ ⌜ cu = vu ⌝
          | None => True
          end)%I) as "Huid_some_packed".
        { rewrite Huid /=. done. }
        iAssert ((match preconditions.(PreconditionsV.ResourceVersion') with
          | Some vrv => ∃ crv, v1.Preconditions.ResourceVersion' cpreconditions ↦{dq} crv ∗ ⌜ crv = vrv ⌝
          | None => True
          end)%I) with "[Hrv_l]" as "Hrv_some_packed".
        { rewrite Hrv /=. iExists (ObjectMetaV.ResourceVersion' m). iFrame "Hrv_l". iPureIntro. symmetry. done. }
        iAssert (PreconditionsV.deepown cpreconditions preconditions dq)
          with "[Huid_some_packed Hrv_some_packed]" as "Hpreconditions_packed".
        { rewrite /PreconditionsV.deepown Huid Hrv /=. iFrame. iPureIntro. done. }
        iAssert ((match options.(DeleteOptionsV.Preconditions') with
          | Some vp =>
              ∃ cp, v1.DeleteOptions.Preconditions' coptions ↦{dq} cp ∗ PreconditionsV.deepown cp vp dq
          | None => True
          end)%I) with "[Hpreconditions_l Hpreconditions_packed]" as "Hpreconditions_some_packed".
        { rewrite Hpreconditions /=. iExists cpreconditions. iFrame "Hpreconditions_l Hpreconditions_packed". }
        iApply "HΦ".
        iFrame "Hdeepown_m_l".
        iExists coptions.
        iFrame.
        iPureIntro.
        done.
      * assert (v1.Preconditions.ResourceVersion' cpreconditions = null) as Hrv_null.
        { apply (proj2 Hdeepown_resourceversion_none). done. }
        rewrite bool_decide_true //=.
        wp_auto.
        iAssert ((match preconditions.(PreconditionsV.UID') with
          | Some vu => ∃ cu, v1.Preconditions.UID' cpreconditions ↦{dq} cu ∗ ⌜ cu = vu ⌝
          | None => True
          end)%I) as "Huid_some_packed".
        { rewrite Huid /=. done. }
        iAssert ((match preconditions.(PreconditionsV.ResourceVersion') with
          | Some vrv => ∃ crv, v1.Preconditions.ResourceVersion' cpreconditions ↦{dq} crv ∗ ⌜ crv = vrv ⌝
          | None => True
          end)%I) as "Hrv_some_packed".
        { rewrite Hrv /=. done. }
        iAssert (PreconditionsV.deepown cpreconditions preconditions dq)
          with "[Huid_some_packed Hrv_some_packed]" as "Hpreconditions_packed".
        { rewrite /PreconditionsV.deepown Huid Hrv /=. iFrame. iPureIntro. done. }
        iAssert ((match options.(DeleteOptionsV.Preconditions') with
          | Some vp =>
              ∃ cp, v1.DeleteOptions.Preconditions' coptions ↦{dq} cp ∗ PreconditionsV.deepown cp vp dq
          | None => True
          end)%I) with "[Hpreconditions_l Hpreconditions_packed]" as "Hpreconditions_some_packed".
        { rewrite Hpreconditions /=. iExists cpreconditions. iFrame "Hpreconditions_l Hpreconditions_packed". }
        iApply "HΦ".
        iFrame "Hdeepown_m_l".
        iExists coptions.
        iFrame.
        iPureIntro.
        done.
  - assert (v1.DeleteOptions.Preconditions' coptions = null) as Hpreconditions_null.
    { apply (proj2 Hdeepown_preconditions_none). done. }
    wp_auto.
    rewrite bool_decide_true //.
    wp_auto.
    iApply "HΦ".
    iFrame "Hdeepown_m_l".
    iExists coptions.
    rewrite /DeleteOptionsV.deepown Hpreconditions /=.
    iFrame.
    iPureIntro.
    done.
Qed.

Axiom delete_propagation_orphan_eq :
  v1.DeletePropagationOrphan = #("Orphan"%go).

Axiom delete_propagation_foreground_eq :
  v1.DeletePropagationForeground = #("Foreground"%go).

Axiom delete_propagation_background_eq :
  v1.DeletePropagationBackground = #("Background"%go).

Axiom finalizer_orphan_dependents_eq :
  v1.FinalizerOrphanDependents = "orphan"%go.

Axiom finalizer_delete_dependents_eq :
  v1.FinalizerDeleteDependents = "foregroundDeletion"%go.

Lemma wp_checkGracefulDelete
    (kind : go_string) (i : interface.t) (o : KObjectV.t)
    (options_l : loc) (options : DeleteOptionsV.t) :
  {{{ is_pkg_init apimodel ∗
      "Hdeepown_i" ∷ KObjectV.deepown_i i o 1 ∗
      "Hdeepown_options_l" ∷ DeleteOptionsV.deepown_l options_l options 1
  }}}
    @! apimodel.checkGracefulDelete #kind #i #options_l
  {{{ (graceful pendingGraceful : bool) (err : error.t) (o' : KObjectV.t)
      (options' : DeleteOptionsV.t), RET (#graceful, #pendingGraceful, #err);
      KObjectV.deepown_i i o' 1 ∗
      DeleteOptionsV.deepown_l options_l options' 1 ∗
      ⌜ pendingGraceful = true →
          (KObjectV.objectmeta o').(ObjectMetaV.DeletionTimestamp') ≠ None ⌝
  }}}.
Proof.
Admitted.

Lemma wp_shouldOrphanDependents
    (metadata_i : interface.t) (metadata_l : loc) (m : ObjectMetaV.t)
    (options_l : loc) (options : DeleteOptionsV.t) (dq : dfrac) :
  {{{ is_pkg_init apimodel ∗
      "%Hmetadata" ∷ ⌜ metadata_i = interface.mk (ptrT.id v1.ObjectMeta.id) #metadata_l ⌝ ∗
      "Hdeepown_m_l" ∷ ObjectMetaV.deepown_l metadata_l m dq ∗
      "Hdeepown_options_l" ∷ DeleteOptionsV.deepown_l options_l options dq
  }}}
    @! apimodel.shouldOrphanDependents #metadata_i #options_l
  {{{ (should_orphan : bool), RET #should_orphan;
      ObjectMetaV.deepown_l metadata_l m dq ∗
      DeleteOptionsV.deepown_l options_l options dq
  }}}.
Proof. (* This proof is fully written by Codex *)
  wp_start as "H".
  iNamed "H". subst metadata_i.
  iDestruct "Hdeepown_m_l" as (cmeta) "[Hmeta_l Hdeepown_m]".
  iDestruct "Hdeepown_options_l" as (coptions) "[Hoptions_l Hdeepown_options]".
  iNamed "Hdeepown_m".
  iNamed "Hdeepown_options".
  iDestruct (typed_pointsto_not_null (t:=v1.DeleteOptions) with "Hoptions_l") as %Hoptions_not_null;
    first (vm_compute; reflexivity).
  assert (bool_decide (options_l = null) = false) as Hoptions_nonnull_decide.
  { apply bool_decide_false. done. }
  wp_auto.
  destruct options.(DeleteOptionsV.PropagationPolicy') as [propagation_policy|] eqn:Hpropagation_policy.
  - iDestruct "Hdeepown_propagationpolicy_some" as (cpropagation_policy) "[Hpropagation_policy_l ->]".
    assert (v1.DeleteOptions.PropagationPolicy' coptions ≠ null) as Hpropagation_policy_not_null.
    { intros Hnull.
      apply (proj1 Hdeepown_propagationpolicy_none) in Hnull.
      congruence.
    }
    assert (bool_decide (v1.DeleteOptions.PropagationPolicy' coptions = null) = false)
      as Hpropagation_policy_nonnull_decide.
    { apply bool_decide_false. done. }
    rewrite Hoptions_nonnull_decide /=.
    wp_auto.
    rewrite Hpropagation_policy_nonnull_decide /=.
    wp_auto.
    rewrite delete_propagation_orphan_eq
      delete_propagation_foreground_eq
      delete_propagation_background_eq.
    wp_auto.
    destruct (bool_decide (propagation_policy = "Orphan"%go)) eqn:Hpropagation_policy_orphan.
    + rewrite Hpropagation_policy_orphan. wp_auto.
      iAssert (DeleteOptionsV.deepown_l options_l options dq) with
        "[Hoptions_l Hdeepown_graceperiodseconds_some Hdeepown_preconditions_some
          Hdeepown_orphandependents_some Hpropagation_policy_l]" as "Hdeepown_options_l".
      { iExists coptions.
        rewrite /DeleteOptionsV.deepown Hpropagation_policy /=.
        iFrame.
        iPureIntro.
        done. }
      iAssert (ObjectMetaV.deepown_l metadata_l m dq) with
        "[Hmeta_l Hdeepown_creationtimestamp Hdeepown_deletiontimestamp_some
          Hdeepown_deletiongraceperiodseconds_some Hdeepown_labels_some Hdeepown_annotations_some
          Hdeepown_ownerreferences_some Hdeepown_finalizers_some Hdeepown_managedfields_some]" as "Hdeepown_m_l".
      { iExists cmeta.
        rewrite /ObjectMetaV.deepown /=.
        iFrame.
        iPureIntro.
        done. }
      iApply "HΦ".
      iFrame.
    + rewrite Hpropagation_policy_orphan. wp_auto.
      destruct (bool_decide (propagation_policy = "Foreground"%go)) eqn:Hpropagation_policy_foreground.
      * rewrite Hpropagation_policy_foreground. wp_auto.
        iAssert (DeleteOptionsV.deepown_l options_l options dq) with
          "[Hoptions_l Hdeepown_graceperiodseconds_some Hdeepown_preconditions_some
            Hdeepown_orphandependents_some Hpropagation_policy_l]" as "Hdeepown_options_l".
        { iExists coptions.
          rewrite /DeleteOptionsV.deepown Hpropagation_policy /=.
          iFrame.
          iPureIntro.
          done. }
        iAssert (ObjectMetaV.deepown_l metadata_l m dq) with
          "[Hmeta_l Hdeepown_creationtimestamp Hdeepown_deletiontimestamp_some
            Hdeepown_deletiongraceperiodseconds_some Hdeepown_labels_some Hdeepown_annotations_some
            Hdeepown_ownerreferences_some Hdeepown_finalizers_some Hdeepown_managedfields_some]" as "Hdeepown_m_l".
        { iExists cmeta.
          rewrite /ObjectMetaV.deepown /=.
          iFrame.
          iPureIntro.
          done. }
        iApply "HΦ".
        iFrame.
      * rewrite Hpropagation_policy_foreground. wp_auto.
        destruct (bool_decide (propagation_policy = "Background"%go)) eqn:Hpropagation_policy_background.
        -- rewrite Hpropagation_policy_background. wp_auto.
           iAssert (DeleteOptionsV.deepown_l options_l options dq) with
             "[Hoptions_l Hdeepown_graceperiodseconds_some Hdeepown_preconditions_some
               Hdeepown_orphandependents_some Hpropagation_policy_l]" as "Hdeepown_options_l".
           { iExists coptions.
             rewrite /DeleteOptionsV.deepown Hpropagation_policy /=.
             iFrame.
             iPureIntro.
             done. }
           iAssert (ObjectMetaV.deepown_l metadata_l m dq) with
             "[Hmeta_l Hdeepown_creationtimestamp Hdeepown_deletiontimestamp_some
               Hdeepown_deletiongraceperiodseconds_some Hdeepown_labels_some Hdeepown_annotations_some
               Hdeepown_ownerreferences_some Hdeepown_finalizers_some Hdeepown_managedfields_some]" as "Hdeepown_m_l".
           { iExists cmeta.
             rewrite /ObjectMetaV.deepown /=.
             iFrame.
             iPureIntro.
             done. }
           iApply "HΦ".
           iFrame.
        -- rewrite Hpropagation_policy_background. wp_auto.
           iAssert (DeleteOptionsV.deepown_l options_l options dq) with
             "[Hoptions_l Hdeepown_graceperiodseconds_some Hdeepown_preconditions_some
               Hdeepown_orphandependents_some Hpropagation_policy_l]" as "Hdeepown_options_l".
           { iExists coptions.
             rewrite /DeleteOptionsV.deepown Hpropagation_policy /=.
             iFrame.
             iPureIntro.
             done. }
           destruct m.(ObjectMetaV.Finalizers') as [finalizers|] eqn:Hfinalizers.
           --- iDestruct "Hdeepown_finalizers_some" as (cfinalizers) "[Hfinalizers_l ->]".
               wp_apply (v1.wp_GetFinalizers with "[$Hmeta_l]").
               iIntros "Hmeta_l".
               wp_auto.
               Transparent slice.for_range.
               iDestruct (own_slice_len with "Hfinalizers_l") as %(Hfinalizers_len & Hfinalizers_nonneg).
               set I := (∃ (i : w64) (f : go_string),
                 "Hi_ptr" ∷ i_ptr ↦ i ∗
                 "Hf_ptr" ∷ f_ptr ↦ f ∗
                 "%Hi" ∷ ⌜ 0 ≤ sint.Z i ≤ sint.Z (slice.len_f (v1.ObjectMeta.Finalizers' cmeta)) ⌝
               )%I.
               iAssert (I) with "[i f]" as "Hloop_inv".
               { iExists (W64 0), (default_val go_string).
                 iFrame.
                 iPureIntro.
                 change (sint.Z (slice.len_f slice.nil)) with 0%Z.
                 word. }
               wp_for "Hloop_inv".
               wp_if_destruct.
               {
                   wp_pure; first word.
                   assert ((sint.nat i < length finalizers)%nat) as Hi_lookup.
                   { rewrite Hfinalizers_len. word. }
                   pose proof (list_lookup_lt finalizers (sint.nat i) Hi_lookup) as [this_finalizer Hlookup].
                   wp_apply (wp_load_slice_elem with "[$Hfinalizers_l]").
                   { word. }
                   { iPureIntro. exact Hlookup. }
                   iIntros "Hfinalizers_l".
                   wp_auto.
                   rewrite finalizer_orphan_dependents_eq
                     finalizer_delete_dependents_eq.
                   destruct (bool_decide (this_finalizer = "orphan"%go)) eqn:Hthis_finalizer_orphan.
                   { wp_auto.
                        wp_for_post.
                        iAssert ((match m.(ObjectMetaV.Finalizers') with
                          | Some vfs => ∃ cfs, cmeta.(v1.ObjectMeta.Finalizers') ↦*{dq} cfs ∗ ⌜ cfs = vfs ⌝
                          | None => True
                          end)%I) with "[Hfinalizers_l]" as "Hdeepown_finalizers_some".
                        { rewrite Hfinalizers /=.
                          iExists finalizers.
                          iFrame "Hfinalizers_l".
                          iPureIntro.
                          done. }
                        iAssert (ObjectMetaV.deepown_l metadata_l m dq) with
                          "[Hmeta_l Hdeepown_creationtimestamp Hdeepown_deletiontimestamp_some
                            Hdeepown_deletiongraceperiodseconds_some Hdeepown_labels_some Hdeepown_annotations_some
                            Hdeepown_ownerreferences_some Hdeepown_finalizers_some Hdeepown_managedfields_some]" as "Hdeepown_m_l".
                        { iExists cmeta.
                          rewrite /ObjectMetaV.deepown Hfinalizers /=.
                          iFrame.
                          iPureIntro.
                          done. }
                        iApply "HΦ".
                        iFrame.
                   }
                   { wp_auto.
                        destruct (bool_decide (this_finalizer = "foregroundDeletion"%go)) eqn:Hthis_finalizer_delete.
                        { wp_auto.
                           wp_for_post.
                           iAssert ((match m.(ObjectMetaV.Finalizers') with
                             | Some vfs => ∃ cfs, cmeta.(v1.ObjectMeta.Finalizers') ↦*{dq} cfs ∗ ⌜ cfs = vfs ⌝
                             | None => True
                             end)%I) with "[Hfinalizers_l]" as "Hdeepown_finalizers_some".
                           { rewrite Hfinalizers /=.
                             iExists finalizers.
                             iFrame "Hfinalizers_l".
                             iPureIntro.
                             done. }
                           iAssert (ObjectMetaV.deepown_l metadata_l m dq) with
                             "[Hmeta_l Hdeepown_creationtimestamp Hdeepown_deletiontimestamp_some
                               Hdeepown_deletiongraceperiodseconds_some Hdeepown_labels_some Hdeepown_annotations_some
                               Hdeepown_ownerreferences_some Hdeepown_finalizers_some Hdeepown_managedfields_some]" as "Hdeepown_m_l".
                           { iExists cmeta.
                             rewrite /ObjectMetaV.deepown Hfinalizers /=.
                             iFrame.
                             iPureIntro.
                             done. }
                           iApply "HΦ".
                           iFrame.
                        }
                        { wp_auto.
                           iApply wp_for_post_do.
                           wp_auto.
                           iFrame "Hdeepown_creationtimestamp Hdeepown_deletiontimestamp_some
                             Hdeepown_deletiongraceperiodseconds_some Hdeepown_labels_some
                             Hdeepown_annotations_some Hdeepown_ownerreferences_some Hfinalizers_l
                             Hdeepown_managedfields_some HΦ options metadata finalizers
                             Hdeepown_options_l Hmeta_l".
                           iExists (word.add i (W64 1)), this_finalizer.
                           iFrame.
                           iPureIntro.
                           word.
                        }
                   }
               }
               {
                   iAssert ((match m.(ObjectMetaV.Finalizers') with
                       | Some vfs => ∃ cfs, cmeta.(v1.ObjectMeta.Finalizers') ↦*{dq} cfs ∗ ⌜ cfs = vfs ⌝
                       | None => True
                       end)%I) with "[Hfinalizers_l]" as "Hdeepown_finalizers_some".
                   { rewrite Hfinalizers /=.
                     iExists finalizers.
                     iFrame "Hfinalizers_l".
                     iPureIntro.
                     done. }
                   iAssert (ObjectMetaV.deepown_l metadata_l m dq) with
                     "[Hmeta_l Hdeepown_creationtimestamp Hdeepown_deletiontimestamp_some
                       Hdeepown_deletiongraceperiodseconds_some Hdeepown_labels_some Hdeepown_annotations_some
                       Hdeepown_ownerreferences_some Hdeepown_finalizers_some Hdeepown_managedfields_some]" as "Hdeepown_m_l".
                   { iExists cmeta.
                     rewrite /ObjectMetaV.deepown Hfinalizers /=.
                     iFrame.
                     iPureIntro.
                     done. }
                   iApply "HΦ".
                   iFrame.
               }
           --- wp_apply (v1.wp_GetFinalizers with "[$Hmeta_l]").
               iIntros "Hmeta_l".
               assert (v1.ObjectMeta.Finalizers' cmeta = slice.nil) as Hfinalizers_nil.
               { apply (proj2 Hdeepown_finalizers_none). done. }
               wp_auto.
               Transparent slice.for_range.
               rewrite Hfinalizers_nil.
               set I := (∃ (i : w64) (f : go_string),
                 "Hi_ptr" ∷ i_ptr ↦ i ∗
                 "Hf_ptr" ∷ f_ptr ↦ f ∗
                 "%Hi" ∷ ⌜ 0 ≤ sint.Z i ≤ sint.Z (slice.len_f slice.nil) ⌝
               )%I.
               iAssert (I) with "[i f]" as "Hloop_inv".
               { iExists (W64 0), (default_val go_string).
                 iFrame.
                 iPureIntro.
                 assert (sint.Z (W64 0) = 0)%Z as -> by word.
                 change (sint.Z (slice.len_f slice.nil)) with 0%Z.
                 lia. }
               wp_for "Hloop_inv".
               wp_if_destruct.
               { exfalso. word. }
               {
                 iAssert (ObjectMetaV.deepown_l metadata_l m dq) with
                   "[Hmeta_l Hdeepown_creationtimestamp Hdeepown_deletiontimestamp_some
                     Hdeepown_deletiongraceperiodseconds_some Hdeepown_labels_some Hdeepown_annotations_some
                     Hdeepown_ownerreferences_some Hdeepown_managedfields_some]" as "Hdeepown_m_l".
                 { iExists cmeta.
                   rewrite /ObjectMetaV.deepown Hfinalizers /=.
                   iFrame.
                   iPureIntro.
                   done. }
                 iApply "HΦ".
                 iFrame.
               }
  - assert (v1.DeleteOptions.PropagationPolicy' coptions = null) as Hpropagation_policy_null.
    { apply (proj2 Hdeepown_propagationpolicy_none). done. }
    rewrite Hoptions_nonnull_decide /=.
    wp_auto.
    rewrite bool_decide_true //=.
    wp_auto.
    iAssert (DeleteOptionsV.deepown_l options_l options dq) with
      "[Hoptions_l Hdeepown_graceperiodseconds_some Hdeepown_preconditions_some
        Hdeepown_orphandependents_some]" as "Hdeepown_options_l".
    { iExists coptions.
      rewrite /DeleteOptionsV.deepown Hpropagation_policy /=.
      iFrame.
      iPureIntro.
      done. }
    destruct m.(ObjectMetaV.Finalizers') as [finalizers|] eqn:Hfinalizers.
    + iDestruct "Hdeepown_finalizers_some" as (cfinalizers) "[Hfinalizers_l ->]".
      wp_apply (v1.wp_GetFinalizers with "[$Hmeta_l]").
      iIntros "Hmeta_l".
      wp_auto.
      Transparent slice.for_range.
      iDestruct (own_slice_len with "Hfinalizers_l") as %(Hfinalizers_len & Hfinalizers_nonneg).
      set I := (∃ (i : w64) (f : go_string),
        "Hi_ptr" ∷ i_ptr ↦ i ∗
        "Hf_ptr" ∷ f_ptr ↦ f ∗
        "%Hi" ∷ ⌜ 0 ≤ sint.Z i ≤ sint.Z (slice.len_f (v1.ObjectMeta.Finalizers' cmeta)) ⌝
      )%I.
      iAssert (I) with "[i f]" as "Hloop_inv".
      { iExists (W64 0), (default_val go_string).
        iFrame.
        iPureIntro.
        change (sint.Z (slice.len_f slice.nil)) with 0%Z.
        word. }
      wp_for "Hloop_inv".
      wp_if_destruct.
      {
        wp_pure; first word.
        assert ((sint.nat i < length finalizers)%nat) as Hi_lookup.
        { rewrite Hfinalizers_len. word. }
        pose proof (list_lookup_lt finalizers (sint.nat i) Hi_lookup) as [this_finalizer Hlookup].
        wp_apply (wp_load_slice_elem with "[$Hfinalizers_l]").
        { word. }
        { iPureIntro. exact Hlookup. }
        iIntros "Hfinalizers_l".
        wp_auto.
        rewrite finalizer_orphan_dependents_eq
          finalizer_delete_dependents_eq.
        destruct (bool_decide (this_finalizer = "orphan"%go)) eqn:Hthis_finalizer_orphan.
        { wp_auto.
          wp_for_post.
          iAssert ((match m.(ObjectMetaV.Finalizers') with
            | Some vfs => ∃ cfs, cmeta.(v1.ObjectMeta.Finalizers') ↦*{dq} cfs ∗ ⌜ cfs = vfs ⌝
            | None => True
            end)%I) with "[Hfinalizers_l]" as "Hdeepown_finalizers_some".
          { rewrite Hfinalizers /=.
            iExists finalizers.
            iFrame "Hfinalizers_l".
            iPureIntro.
            done. }
          iAssert (ObjectMetaV.deepown_l metadata_l m dq) with
            "[Hmeta_l Hdeepown_creationtimestamp Hdeepown_deletiontimestamp_some
              Hdeepown_deletiongraceperiodseconds_some Hdeepown_labels_some Hdeepown_annotations_some
              Hdeepown_ownerreferences_some Hdeepown_finalizers_some Hdeepown_managedfields_some]" as "Hdeepown_m_l".
          { iExists cmeta.
            rewrite /ObjectMetaV.deepown Hfinalizers /=.
            iFrame.
            iPureIntro.
            done. }
          iApply "HΦ".
          iFrame.
        }
        { wp_auto.
          destruct (bool_decide (this_finalizer = "foregroundDeletion"%go)) eqn:Hthis_finalizer_delete.
          { wp_auto.
             wp_for_post.
             iAssert ((match m.(ObjectMetaV.Finalizers') with
               | Some vfs => ∃ cfs, cmeta.(v1.ObjectMeta.Finalizers') ↦*{dq} cfs ∗ ⌜ cfs = vfs ⌝
               | None => True
               end)%I) with "[Hfinalizers_l]" as "Hdeepown_finalizers_some".
             { rewrite Hfinalizers /=.
               iExists finalizers.
               iFrame "Hfinalizers_l".
               iPureIntro.
               done. }
             iAssert (ObjectMetaV.deepown_l metadata_l m dq) with
               "[Hmeta_l Hdeepown_creationtimestamp Hdeepown_deletiontimestamp_some
                 Hdeepown_deletiongraceperiodseconds_some Hdeepown_labels_some Hdeepown_annotations_some
                 Hdeepown_ownerreferences_some Hdeepown_finalizers_some Hdeepown_managedfields_some]" as "Hdeepown_m_l".
             { iExists cmeta.
               rewrite /ObjectMetaV.deepown Hfinalizers /=.
               iFrame.
               iPureIntro.
               done. }
             iApply "HΦ".
             iFrame.
          }
          { wp_auto.
             iApply wp_for_post_do.
             wp_auto.
             iFrame "Hdeepown_creationtimestamp Hdeepown_deletiontimestamp_some
               Hdeepown_deletiongraceperiodseconds_some Hdeepown_labels_some
               Hdeepown_annotations_some Hdeepown_ownerreferences_some Hfinalizers_l
               Hdeepown_managedfields_some HΦ options metadata finalizers
               Hdeepown_options_l Hmeta_l".
             iExists (word.add i (W64 1)), this_finalizer.
             iFrame.
             iPureIntro.
             word.
          }
        }
      }
      {
        iAssert ((match m.(ObjectMetaV.Finalizers') with
            | Some vfs => ∃ cfs, cmeta.(v1.ObjectMeta.Finalizers') ↦*{dq} cfs ∗ ⌜ cfs = vfs ⌝
            | None => True
            end)%I) with "[Hfinalizers_l]" as "Hdeepown_finalizers_some".
        { rewrite Hfinalizers /=.
          iExists finalizers.
          iFrame "Hfinalizers_l".
          iPureIntro.
          done. }
        iAssert (ObjectMetaV.deepown_l metadata_l m dq) with
          "[Hmeta_l Hdeepown_creationtimestamp Hdeepown_deletiontimestamp_some
            Hdeepown_deletiongraceperiodseconds_some Hdeepown_labels_some Hdeepown_annotations_some
            Hdeepown_ownerreferences_some Hdeepown_finalizers_some Hdeepown_managedfields_some]" as "Hdeepown_m_l".
        { iExists cmeta.
          rewrite /ObjectMetaV.deepown Hfinalizers /=.
          iFrame.
          iPureIntro.
          done. }
        iApply "HΦ".
        iFrame.
      }
    + wp_apply (v1.wp_GetFinalizers with "[$Hmeta_l]").
      iIntros "Hmeta_l".
      assert (v1.ObjectMeta.Finalizers' cmeta = slice.nil) as Hfinalizers_nil.
      { apply (proj2 Hdeepown_finalizers_none). done. }
      wp_auto.
      Transparent slice.for_range.
      rewrite Hfinalizers_nil.
      set I := (∃ (i : w64) (f : go_string),
        "Hi_ptr" ∷ i_ptr ↦ i ∗
        "Hf_ptr" ∷ f_ptr ↦ f ∗
        "%Hi" ∷ ⌜ 0 ≤ sint.Z i ≤ sint.Z (slice.len_f slice.nil) ⌝
      )%I.
      iAssert (I) with "[i f]" as "Hloop_inv".
      { iExists (W64 0), (default_val go_string).
        iFrame.
        iPureIntro.
        assert (sint.Z (W64 0) = 0)%Z as -> by word.
        change (sint.Z (slice.len_f slice.nil)) with 0%Z.
        lia. }
      wp_for "Hloop_inv".
      wp_if_destruct.
      { exfalso. word. }
      {
        iAssert (ObjectMetaV.deepown_l metadata_l m dq) with
          "[Hmeta_l Hdeepown_creationtimestamp Hdeepown_deletiontimestamp_some
            Hdeepown_deletiongraceperiodseconds_some Hdeepown_labels_some Hdeepown_annotations_some
            Hdeepown_ownerreferences_some Hdeepown_managedfields_some]" as "Hdeepown_m_l".
        { iExists cmeta.
          rewrite /ObjectMetaV.deepown Hfinalizers /=.
          iFrame.
          iPureIntro.
          done. }
        iApply "HΦ".
        iFrame.
      }
Qed.

Lemma wp_shouldDeleteDependents
    (metadata_i : interface.t) (metadata_l : loc) (m : ObjectMetaV.t)
    (options_l : loc) (options : DeleteOptionsV.t) (dq : dfrac) :
  {{{ is_pkg_init apimodel ∗
      "%Hmetadata" ∷ ⌜ metadata_i = interface.mk (ptrT.id v1.ObjectMeta.id) #metadata_l ⌝ ∗
      "Hdeepown_m_l" ∷ ObjectMetaV.deepown_l metadata_l m dq ∗
      "Hdeepown_options_l" ∷ DeleteOptionsV.deepown_l options_l options dq
  }}}
    @! apimodel.shouldDeleteDependents #metadata_i #options_l
  {{{ (should_delete : bool), RET #should_delete;
      ObjectMetaV.deepown_l metadata_l m dq ∗
      DeleteOptionsV.deepown_l options_l options dq
  }}}.
Proof. (* This proof is fully written by Codex *)
  wp_start as "H".
  iNamed "H". subst metadata_i.
  iDestruct "Hdeepown_m_l" as (cmeta) "[Hmeta_l Hdeepown_m]".
  iDestruct "Hdeepown_options_l" as (coptions) "[Hoptions_l Hdeepown_options]".
  iNamed "Hdeepown_m".
  iNamed "Hdeepown_options".
  iDestruct (typed_pointsto_not_null (t:=v1.DeleteOptions) with "Hoptions_l") as %Hoptions_not_null;
    first (vm_compute; reflexivity).
  assert (bool_decide (options_l = null) = false) as Hoptions_nonnull_decide.
  { apply bool_decide_false. done. }
  wp_auto.
  destruct options.(DeleteOptionsV.PropagationPolicy') as [propagation_policy|] eqn:Hpropagation_policy.
  - iDestruct "Hdeepown_propagationpolicy_some" as (cpropagation_policy) "[Hpropagation_policy_l ->]".
    assert (v1.DeleteOptions.PropagationPolicy' coptions ≠ null) as Hpropagation_policy_not_null.
    { intros Hnull.
      apply (proj1 Hdeepown_propagationpolicy_none) in Hnull.
      congruence.
    }
    assert (bool_decide (v1.DeleteOptions.PropagationPolicy' coptions = null) = false)
      as Hpropagation_policy_nonnull_decide.
    { apply bool_decide_false. done. }
    rewrite Hoptions_nonnull_decide /=.
    wp_auto.
    rewrite Hpropagation_policy_nonnull_decide /=.
    wp_auto.
    rewrite delete_propagation_orphan_eq
      delete_propagation_foreground_eq
      delete_propagation_background_eq.
    wp_auto.
    destruct (bool_decide (propagation_policy = "Foreground"%go)) eqn:Hpropagation_policy_foreground.
    + rewrite Hpropagation_policy_foreground. wp_auto.
      iAssert (DeleteOptionsV.deepown_l options_l options dq) with
        "[Hoptions_l Hdeepown_graceperiodseconds_some Hdeepown_preconditions_some
          Hdeepown_orphandependents_some Hpropagation_policy_l]" as "Hdeepown_options_l".
      { iExists coptions.
        rewrite /DeleteOptionsV.deepown Hpropagation_policy /=.
        iFrame.
        iPureIntro.
        done. }
      iAssert (ObjectMetaV.deepown_l metadata_l m dq) with
        "[Hmeta_l Hdeepown_creationtimestamp Hdeepown_deletiontimestamp_some
          Hdeepown_deletiongraceperiodseconds_some Hdeepown_labels_some Hdeepown_annotations_some
          Hdeepown_ownerreferences_some Hdeepown_finalizers_some Hdeepown_managedfields_some]" as "Hdeepown_m_l".
      { iExists cmeta.
        rewrite /ObjectMetaV.deepown /=.
        iFrame.
        iPureIntro.
        done. }
      iApply "HΦ".
      iFrame.
    + rewrite Hpropagation_policy_foreground. wp_auto.
      destruct (bool_decide (propagation_policy = "Orphan"%go)) eqn:Hpropagation_policy_orphan.
      * rewrite Hpropagation_policy_orphan. wp_auto.
        iAssert (DeleteOptionsV.deepown_l options_l options dq) with
          "[Hoptions_l Hdeepown_graceperiodseconds_some Hdeepown_preconditions_some
            Hdeepown_orphandependents_some Hpropagation_policy_l]" as "Hdeepown_options_l".
        { iExists coptions.
          rewrite /DeleteOptionsV.deepown Hpropagation_policy /=.
          iFrame.
          iPureIntro.
          done. }
        iAssert (ObjectMetaV.deepown_l metadata_l m dq) with
          "[Hmeta_l Hdeepown_creationtimestamp Hdeepown_deletiontimestamp_some
            Hdeepown_deletiongraceperiodseconds_some Hdeepown_labels_some Hdeepown_annotations_some
            Hdeepown_ownerreferences_some Hdeepown_finalizers_some Hdeepown_managedfields_some]" as "Hdeepown_m_l".
        { iExists cmeta.
          rewrite /ObjectMetaV.deepown /=.
          iFrame.
          iPureIntro.
          done. }
        iApply "HΦ".
        iFrame.
      * rewrite Hpropagation_policy_orphan. wp_auto.
        destruct (bool_decide (propagation_policy = "Background"%go)) eqn:Hpropagation_policy_background.
        -- rewrite Hpropagation_policy_background. wp_auto.
           iAssert (DeleteOptionsV.deepown_l options_l options dq) with
             "[Hoptions_l Hdeepown_graceperiodseconds_some Hdeepown_preconditions_some
               Hdeepown_orphandependents_some Hpropagation_policy_l]" as "Hdeepown_options_l".
           { iExists coptions.
             rewrite /DeleteOptionsV.deepown Hpropagation_policy /=.
             iFrame.
             iPureIntro.
             done. }
           iAssert (ObjectMetaV.deepown_l metadata_l m dq) with
             "[Hmeta_l Hdeepown_creationtimestamp Hdeepown_deletiontimestamp_some
               Hdeepown_deletiongraceperiodseconds_some Hdeepown_labels_some Hdeepown_annotations_some
               Hdeepown_ownerreferences_some Hdeepown_finalizers_some Hdeepown_managedfields_some]" as "Hdeepown_m_l".
           { iExists cmeta.
             rewrite /ObjectMetaV.deepown /=.
             iFrame.
             iPureIntro.
             done. }
           iApply "HΦ".
           iFrame.
        -- rewrite Hpropagation_policy_background. wp_auto.
           iAssert (DeleteOptionsV.deepown_l options_l options dq) with
             "[Hoptions_l Hdeepown_graceperiodseconds_some Hdeepown_preconditions_some
               Hdeepown_orphandependents_some Hpropagation_policy_l]" as "Hdeepown_options_l".
           { iExists coptions.
             rewrite /DeleteOptionsV.deepown Hpropagation_policy /=.
             iFrame.
             iPureIntro.
             done. }
           destruct m.(ObjectMetaV.Finalizers') as [finalizers|] eqn:Hfinalizers.
           --- iDestruct "Hdeepown_finalizers_some" as (cfinalizers) "[Hfinalizers_l ->]".
               wp_apply (v1.wp_GetFinalizers with "[$Hmeta_l]").
               iIntros "Hmeta_l".
               wp_auto.
               Transparent slice.for_range.
               iDestruct (own_slice_len with "Hfinalizers_l") as %(Hfinalizers_len & Hfinalizers_nonneg).
               set I := (∃ (i : w64) (f : go_string),
                 "Hi_ptr" ∷ i_ptr ↦ i ∗
                 "Hf_ptr" ∷ f_ptr ↦ f ∗
                 "%Hi" ∷ ⌜ 0 ≤ sint.Z i ≤ sint.Z (slice.len_f (v1.ObjectMeta.Finalizers' cmeta)) ⌝
               )%I.
               iAssert (I) with "[i f]" as "Hloop_inv".
               { iExists (W64 0), (default_val go_string).
                 iFrame.
                 iPureIntro.
                 word. }
               wp_for "Hloop_inv".
               wp_if_destruct.
               {
                 wp_pure; first word.
                 assert ((sint.nat i < length finalizers)%nat) as Hi_lookup.
                 { rewrite Hfinalizers_len. word. }
                 pose proof (list_lookup_lt finalizers (sint.nat i) Hi_lookup) as [this_finalizer Hlookup].
                 wp_apply (wp_load_slice_elem with "[$Hfinalizers_l]").
                 { word. }
                 { iPureIntro. exact Hlookup. }
                 iIntros "Hfinalizers_l".
                 wp_auto.
                 rewrite finalizer_orphan_dependents_eq
                   finalizer_delete_dependents_eq.
                 destruct (bool_decide (this_finalizer = "foregroundDeletion"%go)) eqn:Hthis_finalizer_delete.
                 { wp_auto.
                   wp_for_post.
                   iAssert ((match m.(ObjectMetaV.Finalizers') with
                     | Some vfs => ∃ cfs, cmeta.(v1.ObjectMeta.Finalizers') ↦*{dq} cfs ∗ ⌜ cfs = vfs ⌝
                     | None => True
                     end)%I) with "[Hfinalizers_l]" as "Hdeepown_finalizers_some".
                   { rewrite Hfinalizers /=.
                     iExists finalizers.
                     iFrame "Hfinalizers_l".
                     iPureIntro.
                     done. }
                   iAssert (ObjectMetaV.deepown_l metadata_l m dq) with
                     "[Hmeta_l Hdeepown_creationtimestamp Hdeepown_deletiontimestamp_some
                       Hdeepown_deletiongraceperiodseconds_some Hdeepown_labels_some Hdeepown_annotations_some
                       Hdeepown_ownerreferences_some Hdeepown_finalizers_some Hdeepown_managedfields_some]" as "Hdeepown_m_l".
                   { iExists cmeta.
                     rewrite /ObjectMetaV.deepown Hfinalizers /=.
                     iFrame.
                     iPureIntro.
                     done. }
                   iApply "HΦ".
                   iFrame.
                 }
                 { wp_auto.
                   destruct (bool_decide (this_finalizer = "orphan"%go)) eqn:Hthis_finalizer_orphan.
                   { wp_auto.
                     wp_for_post.
                     iAssert ((match m.(ObjectMetaV.Finalizers') with
                       | Some vfs => ∃ cfs, cmeta.(v1.ObjectMeta.Finalizers') ↦*{dq} cfs ∗ ⌜ cfs = vfs ⌝
                       | None => True
                       end)%I) with "[Hfinalizers_l]" as "Hdeepown_finalizers_some".
                     { rewrite Hfinalizers /=.
                       iExists finalizers.
                       iFrame "Hfinalizers_l".
                       iPureIntro.
                       done. }
                     iAssert (ObjectMetaV.deepown_l metadata_l m dq) with
                       "[Hmeta_l Hdeepown_creationtimestamp Hdeepown_deletiontimestamp_some
                         Hdeepown_deletiongraceperiodseconds_some Hdeepown_labels_some Hdeepown_annotations_some
                         Hdeepown_ownerreferences_some Hdeepown_finalizers_some Hdeepown_managedfields_some]" as "Hdeepown_m_l".
                     { iExists cmeta.
                       rewrite /ObjectMetaV.deepown Hfinalizers /=.
                       iFrame.
                       iPureIntro.
                       done. }
                     iApply "HΦ".
                     iFrame.
                   }
                   { wp_auto.
                     iApply wp_for_post_do.
                     wp_auto.
                     iFrame "Hdeepown_creationtimestamp Hdeepown_deletiontimestamp_some
                       Hdeepown_deletiongraceperiodseconds_some Hdeepown_labels_some
                       Hdeepown_annotations_some Hdeepown_ownerreferences_some Hfinalizers_l
                       Hdeepown_managedfields_some HΦ options metadata finalizers
                       Hdeepown_options_l Hmeta_l".
                     iExists (word.add i (W64 1)), this_finalizer.
                     iFrame.
                     iPureIntro.
                     word.
                   }
                 }
               }
               {
                 iAssert ((match m.(ObjectMetaV.Finalizers') with
                     | Some vfs => ∃ cfs, cmeta.(v1.ObjectMeta.Finalizers') ↦*{dq} cfs ∗ ⌜ cfs = vfs ⌝
                     | None => True
                     end)%I) with "[Hfinalizers_l]" as "Hdeepown_finalizers_some".
                 { rewrite Hfinalizers /=.
                   iExists finalizers.
                   iFrame "Hfinalizers_l".
                   iPureIntro.
                   done. }
                 iAssert (ObjectMetaV.deepown_l metadata_l m dq) with
                   "[Hmeta_l Hdeepown_creationtimestamp Hdeepown_deletiontimestamp_some
                     Hdeepown_deletiongraceperiodseconds_some Hdeepown_labels_some Hdeepown_annotations_some
                     Hdeepown_ownerreferences_some Hdeepown_finalizers_some Hdeepown_managedfields_some]" as "Hdeepown_m_l".
                 { iExists cmeta.
                   rewrite /ObjectMetaV.deepown Hfinalizers /=.
                   iFrame.
                   iPureIntro.
                   done. }
                 iApply "HΦ".
                 iFrame.
               }
           --- wp_apply (v1.wp_GetFinalizers with "[$Hmeta_l]").
               iIntros "Hmeta_l".
               assert (v1.ObjectMeta.Finalizers' cmeta = slice.nil) as Hfinalizers_nil.
               { apply (proj2 Hdeepown_finalizers_none). done. }
               wp_auto.
               Transparent slice.for_range.
               rewrite Hfinalizers_nil.
               set I := (∃ (i : w64) (f : go_string),
                 "Hi_ptr" ∷ i_ptr ↦ i ∗
                 "Hf_ptr" ∷ f_ptr ↦ f ∗
                 "%Hi" ∷ ⌜ 0 ≤ sint.Z i ≤ sint.Z (slice.len_f slice.nil) ⌝
               )%I.
               iAssert (I) with "[i f]" as "Hloop_inv".
               { iExists (W64 0), (default_val go_string).
                 iFrame.
                 iPureIntro.
                 assert (sint.Z (W64 0) = 0)%Z as -> by word.
                 change (sint.Z (slice.len_f slice.nil)) with 0%Z.
                 lia. }
               wp_for "Hloop_inv".
               wp_if_destruct.
               { exfalso. word. }
               {
                 iAssert (ObjectMetaV.deepown_l metadata_l m dq) with
                   "[Hmeta_l Hdeepown_creationtimestamp Hdeepown_deletiontimestamp_some
                     Hdeepown_deletiongraceperiodseconds_some Hdeepown_labels_some Hdeepown_annotations_some
                     Hdeepown_ownerreferences_some Hdeepown_managedfields_some]" as "Hdeepown_m_l".
                 { iExists cmeta.
                   rewrite /ObjectMetaV.deepown Hfinalizers /=.
                   iFrame.
                   iPureIntro.
                   done. }
                 iApply "HΦ".
                 iFrame.
               }
  - assert (v1.DeleteOptions.PropagationPolicy' coptions = null) as Hpropagation_policy_null.
    { apply (proj2 Hdeepown_propagationpolicy_none). done. }
    rewrite Hoptions_nonnull_decide /=.
    wp_auto.
    rewrite bool_decide_true //=.
    wp_auto.
    iAssert (DeleteOptionsV.deepown_l options_l options dq) with
      "[Hoptions_l Hdeepown_graceperiodseconds_some Hdeepown_preconditions_some
        Hdeepown_orphandependents_some]" as "Hdeepown_options_l".
    { iExists coptions.
      rewrite /DeleteOptionsV.deepown Hpropagation_policy /=.
      iFrame.
      iPureIntro.
      done. }
    destruct m.(ObjectMetaV.Finalizers') as [finalizers|] eqn:Hfinalizers.
    + iDestruct "Hdeepown_finalizers_some" as (cfinalizers) "[Hfinalizers_l ->]".
      wp_apply (v1.wp_GetFinalizers with "[$Hmeta_l]").
      iIntros "Hmeta_l".
      wp_auto.
      Transparent slice.for_range.
      iDestruct (own_slice_len with "Hfinalizers_l") as %(Hfinalizers_len & Hfinalizers_nonneg).
      set I := (∃ (i : w64) (f : go_string),
        "Hi_ptr" ∷ i_ptr ↦ i ∗
        "Hf_ptr" ∷ f_ptr ↦ f ∗
        "%Hi" ∷ ⌜ 0 ≤ sint.Z i ≤ sint.Z (slice.len_f (v1.ObjectMeta.Finalizers' cmeta)) ⌝
      )%I.
      iAssert (I) with "[i f]" as "Hloop_inv".
      { iExists (W64 0), (default_val go_string).
        iFrame.
        iPureIntro.
        word. }
      wp_for "Hloop_inv".
      wp_if_destruct.
      {
        wp_pure; first word.
        assert ((sint.nat i < length finalizers)%nat) as Hi_lookup.
        { rewrite Hfinalizers_len. word. }
        pose proof (list_lookup_lt finalizers (sint.nat i) Hi_lookup) as [this_finalizer Hlookup].
        wp_apply (wp_load_slice_elem with "[$Hfinalizers_l]").
        { word. }
        { iPureIntro. exact Hlookup. }
        iIntros "Hfinalizers_l".
        wp_auto.
        rewrite finalizer_orphan_dependents_eq
          finalizer_delete_dependents_eq.
        destruct (bool_decide (this_finalizer = "foregroundDeletion"%go)) eqn:Hthis_finalizer_delete.
        { wp_auto.
          wp_for_post.
          iAssert ((match m.(ObjectMetaV.Finalizers') with
            | Some vfs => ∃ cfs, cmeta.(v1.ObjectMeta.Finalizers') ↦*{dq} cfs ∗ ⌜ cfs = vfs ⌝
            | None => True
            end)%I) with "[Hfinalizers_l]" as "Hdeepown_finalizers_some".
          { rewrite Hfinalizers /=.
            iExists finalizers.
            iFrame "Hfinalizers_l".
            iPureIntro.
            done. }
          iAssert (ObjectMetaV.deepown_l metadata_l m dq) with
            "[Hmeta_l Hdeepown_creationtimestamp Hdeepown_deletiontimestamp_some
              Hdeepown_deletiongraceperiodseconds_some Hdeepown_labels_some Hdeepown_annotations_some
              Hdeepown_ownerreferences_some Hdeepown_finalizers_some Hdeepown_managedfields_some]" as "Hdeepown_m_l".
          { iExists cmeta.
            rewrite /ObjectMetaV.deepown Hfinalizers /=.
            iFrame.
            iPureIntro.
            done. }
          iApply "HΦ".
          iFrame.
        }
        { wp_auto.
          destruct (bool_decide (this_finalizer = "orphan"%go)) eqn:Hthis_finalizer_orphan.
          { wp_auto.
            wp_for_post.
            iAssert ((match m.(ObjectMetaV.Finalizers') with
              | Some vfs => ∃ cfs, cmeta.(v1.ObjectMeta.Finalizers') ↦*{dq} cfs ∗ ⌜ cfs = vfs ⌝
              | None => True
              end)%I) with "[Hfinalizers_l]" as "Hdeepown_finalizers_some".
            { rewrite Hfinalizers /=.
              iExists finalizers.
              iFrame "Hfinalizers_l".
              iPureIntro.
              done. }
            iAssert (ObjectMetaV.deepown_l metadata_l m dq) with
              "[Hmeta_l Hdeepown_creationtimestamp Hdeepown_deletiontimestamp_some
                Hdeepown_deletiongraceperiodseconds_some Hdeepown_labels_some Hdeepown_annotations_some
                Hdeepown_ownerreferences_some Hdeepown_finalizers_some Hdeepown_managedfields_some]" as "Hdeepown_m_l".
            { iExists cmeta.
              rewrite /ObjectMetaV.deepown Hfinalizers /=.
              iFrame.
              iPureIntro.
              done. }
            iApply "HΦ".
            iFrame.
          }
          { wp_auto.
            iApply wp_for_post_do.
            wp_auto.
            iFrame "Hdeepown_creationtimestamp Hdeepown_deletiontimestamp_some
              Hdeepown_deletiongraceperiodseconds_some Hdeepown_labels_some
              Hdeepown_annotations_some Hdeepown_ownerreferences_some Hfinalizers_l
              Hdeepown_managedfields_some HΦ options metadata finalizers
              Hdeepown_options_l Hmeta_l".
            iExists (word.add i (W64 1)), this_finalizer.
            iFrame.
            iPureIntro.
            word.
          }
        }
      }
      {
        iAssert ((match m.(ObjectMetaV.Finalizers') with
            | Some vfs => ∃ cfs, cmeta.(v1.ObjectMeta.Finalizers') ↦*{dq} cfs ∗ ⌜ cfs = vfs ⌝
            | None => True
            end)%I) with "[Hfinalizers_l]" as "Hdeepown_finalizers_some".
        { rewrite Hfinalizers /=.
          iExists finalizers.
          iFrame "Hfinalizers_l".
          iPureIntro.
          done. }
        iAssert (ObjectMetaV.deepown_l metadata_l m dq) with
          "[Hmeta_l Hdeepown_creationtimestamp Hdeepown_deletiontimestamp_some
            Hdeepown_deletiongraceperiodseconds_some Hdeepown_labels_some Hdeepown_annotations_some
            Hdeepown_ownerreferences_some Hdeepown_finalizers_some Hdeepown_managedfields_some]" as "Hdeepown_m_l".
        { iExists cmeta.
          rewrite /ObjectMetaV.deepown Hfinalizers /=.
          iFrame.
          iPureIntro.
          done. }
        iApply "HΦ".
        iFrame.
      }
    + wp_apply (v1.wp_GetFinalizers with "[$Hmeta_l]").
      iIntros "Hmeta_l".
      assert (v1.ObjectMeta.Finalizers' cmeta = slice.nil) as Hfinalizers_nil.
      { apply (proj2 Hdeepown_finalizers_none). done. }
      wp_auto.
      Transparent slice.for_range.
      rewrite Hfinalizers_nil.
      set I := (∃ (i : w64) (f : go_string),
        "Hi_ptr" ∷ i_ptr ↦ i ∗
        "Hf_ptr" ∷ f_ptr ↦ f ∗
        "%Hi" ∷ ⌜ 0 ≤ sint.Z i ≤ sint.Z (slice.len_f slice.nil) ⌝
      )%I.
      iAssert (I) with "[i f]" as "Hloop_inv".
      { iExists (W64 0), (default_val go_string).
        iFrame.
        iPureIntro.
        assert (sint.Z (W64 0) = 0)%Z as -> by word.
        change (sint.Z (slice.len_f slice.nil)) with 0%Z.
        lia. }
      wp_for "Hloop_inv".
      wp_if_destruct.
      { exfalso. word. }
      {
        iAssert (ObjectMetaV.deepown_l metadata_l m dq) with
          "[Hmeta_l Hdeepown_creationtimestamp Hdeepown_deletiontimestamp_some
            Hdeepown_deletiongraceperiodseconds_some Hdeepown_labels_some Hdeepown_annotations_some
            Hdeepown_ownerreferences_some Hdeepown_managedfields_some]" as "Hdeepown_m_l".
        { iExists cmeta.
          rewrite /ObjectMetaV.deepown Hfinalizers /=.
          iFrame.
          iPureIntro.
          done. }
        iApply "HΦ".
        iFrame.
      }
Qed.

Lemma wp_State__deletionFinalizersForGarbageCollection
    (l : loc) (metadata_i : interface.t) (metadata_l : loc) (m : ObjectMetaV.t)
    (options_l : loc) (options : DeleteOptionsV.t) (dq : dfrac) (owner_uid : types.UID.t) :
  {{{ is_pkg_init apimodel ∗
      "%Hmetadata" ∷ ⌜ metadata_i = interface.mk (ptrT.id v1.ObjectMeta.id) #metadata_l ⌝ ∗
      "Hdeepown_m_l" ∷ ObjectMetaV.deepown_l metadata_l m dq ∗
      "Hdeepown_options_l" ∷ DeleteOptionsV.deepown_l options_l options dq
  }}}
    l @ (ptrT.id apimodel.State.id) @ "deletionFinalizersForGarbageCollection"
      #metadata_i #options_l #owner_uid
  {{{ (should_update_finalizers : bool) (new_finalizers_sl : slice.t),
      RET (#should_update_finalizers, #new_finalizers_sl);
      ObjectMetaV.deepown_l metadata_l m dq ∗
      DeleteOptionsV.deepown_l options_l options dq
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

End proof.
