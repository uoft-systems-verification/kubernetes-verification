From New.proof Require Import prelude empty_ffi.
From New.proof.string Require Export prefix_suffix.
From New.proof.kubernetes_model Require Export get index create delete.
From New.proof Require Export util.
From New.proof Require Export external_wp.
From New.proof.controllers Require Export common.
From New.proof.controllers.statefulset Require Export name.
From New.proof.controllers.statefulset Require Export statefulset_init.
From New.proof.k8s_io.kubernetes.pkg Require Export controller.
From New.proof.k8s_io.apimachinery.pkg.runtime Require Export schema.
From New.proof.k8s_io.apimachinery.pkg.api Require Export errors.

Section proof.
Context `{hG: !heapGS Σ}.
Context {sem : go.Semantics}
  {package_sem : code.controllers.statefulset.statefulset.Assumptions}.
Collection W := sem + package_sem.
#[local] Instance base_common_sem : common.Assumptions | 100 :=
  code.controllers.statefulset.statefulset.import_common_Assumption.
#[local] Instance controller_sem : controller.Assumptions :=
  code.controllers.statefulset.statefulset.import_controller_Assumption.
#[local] Instance runtime_sem : code.k8s_io.apimachinery.pkg.runtime.runtime.Assumptions :=
  controller.import_runtime_Assumption.
#[local] Instance base_apimodel_sem : apimodel.Assumptions | 100 :=
  common.import_apimodel_Assumption.
#[local] Instance object_meta_v1_sem :
    code.k8s_io.apimachinery.pkg.apis.meta.v1.v1.Assumptions :=
  apimodel.import_apis_meta_v1_Assumption.
#[local] Instance object_apps_v1_sem :
    code.k8s_io.api.apps.v1.v1.Assumptions :=
  apimodel.import_api_apps_v1_Assumption.
#[local] Instance object_core_v1_sem :
    code.k8s_io.api.core.v1.v1.Assumptions :=
  code.k8s_io.api.apps.v1.v1.import_core_v1_Assumption.
#[local] Instance apimodel_sem : apimodel.Assumptions | 0.
Proof using package_sem.
  constructor; try exact object_core_v1_sem; try apply _.
Defined.
#[local] Instance common_sem : common.Assumptions | 0.
Proof using package_sem.
  constructor; try exact apimodel_sem; try apply _.
Defined.
Context `{!kubernetesModelG Σ}.
Local Set Default Proof Using "All".

Lemma wp_replicasOf set_l (set : StatefulSetV.t) dq :
  {{{ StatefulSetV.deepown_l set_l set dq ∗
      ⌜ StatefulSetSpecV.valid set.(StatefulSetV.Spec') ⌝ }}}
    @! statefulset.replicasOf #set_l
  {{{ (replicas : w64), RET #replicas;
      ⌜ sint.Z replicas = Z.of_nat (statefulset_replicas set) ⌝ ∗
      StatefulSetV.deepown_l set_l set dq
  }}}.
Proof.
  wp_start as "(Hset & %Hvalid)".
  iPoseProof (StatefulSetV.deepown_l_split with "Hset") as
    "(%Hset_l_not_null & Htypemeta & Hobjectmeta & Hspec_l & Hstatus_l)".
  iDestruct "Hspec_l" as (spec_c) "[Hspec_field Hspec]".
  iNamed "Hspec".
  pose proof (StatefulSetSpecV.valid_replicas _ Hvalid) as
    (replicas32 & Hreplicas_eq & Hreplicas_nonnegative).
  rewrite Hreplicas_eq.
  iDestruct "Hdeepown_replicas_some" as (replicas32_c)
    "[Hreplicas %Hreplicas32_c_eq]".
  subst replicas32_c.
  assert (spec_c.(v1.StatefulSetSpec.Replicas') ≠ null) as Hreplicas_ptr_not_null.
  { intros Hreplicas_ptr_null.
    apply Hdeepown_replicas_none in Hreplicas_ptr_null.
    congruence. }
  wp_auto.
  wp_if_destruct.
  { exfalso. done. }
  wp_pures.
  iApply ("HΦ" $! (W64 (sint.Z replicas32))).
  iSplitR.
  { iPureIntro.
    replace (sint.Z (W64 (sint.Z replicas32))) with (sint.Z replicas32) by word.
    unfold statefulset_replicas.
    rewrite Hreplicas_eq.
    replace (Z.of_nat (sint.nat replicas32)) with (sint.Z replicas32) by word.
    done. }
  iApply (StatefulSetV.deepown_l_restore _ _ _ Hset_l_not_null).
  iFrame "Htypemeta Hobjectmeta Hstatus_l".
  unfold StatefulSetSpecV.deepown_l, StatefulSetV.spec_ptr.
  iExists spec_c.
  iFrame "Hspec_field".
  unfold StatefulSetSpecV.deepown.
  iSplit; first done.
  iSplitL "Hreplicas".
  {
  rewrite Hreplicas_eq.
  iExists replicas32.
  iFrame.
  done.
  }
  iFrame.
  done.
Qed.

Lemma wp_endOrdinalOf set_l (set : StatefulSetV.t) dq :
  {{{ StatefulSetV.deepown_l set_l set dq ∗
      ⌜ StatefulSetSpecV.valid set.(StatefulSetV.Spec') ⌝ }}}
    @! statefulset.endOrdinalOf #set_l
  {{{ (end_ordinal : w64), RET #end_ordinal;
      ⌜ sint.Z end_ordinal = Z.of_nat (statefulset_replicas set) - 1 ⌝ ∗
      StatefulSetV.deepown_l set_l set dq
  }}}.
Proof.
  wp_start as "(Hset & %Hvalid)".
  wp_auto.
  wp_apply (wp_replicasOf with "[$Hset //]").
  iIntros (replicas) "[%Hreplicas Hset]".
  wp_pures.
  iApply "HΦ".
  iFrame.
  iPureIntro.
  assert (sint.Z (word.sub replicas (W64 1)) = sint.Z replicas - 1) as -> by word.
  rewrite Hreplicas.
  done.
Qed.

Lemma wp_podName (set_name : go_string) (ordinal : w64) :
  {{{ ⌜ 0 <= sint.Z ordinal ⌝ }}}
    @! statefulset.podName #set_name #ordinal
  {{{ RET #(set_name ++ "-"%go ++ decimal_string (sint.nat ordinal)); True }}}.
Proof.
  wp_start as "%Hordinal_nonnegative".
  wp_auto.
  wp_apply (wp_strconv_Itoa with "[]").
  { iSplit; first by iEval (rewrite is_pkg_init_unfold /=).
    iPureIntro. exact Hordinal_nonnegative. }
  wp_pures.
  iEval (rewrite List.app_assoc) in "HΦ".
  iApply "HΦ".
  done.
Qed.

Lemma wp_claimName
    (set_name claim_template_name : go_string) (ordinal : w64) :
  {{{ ⌜ 0 <= sint.Z ordinal ⌝ }}}
    @! statefulset.claimName #set_name #claim_template_name #ordinal
  {{{ RET #(claim_template_name ++ "-"%go ++ set_name ++ "-"%go ++
        decimal_string (sint.nat ordinal)); True }}}.
Proof.
  wp_start as "%Hordinal_nonnegative".
  wp_auto.
  wp_apply (wp_strconv_Itoa with "[]").
  { iSplit; first by iEval (rewrite is_pkg_init_unfold /=).
    iPureIntro. exact Hordinal_nonnegative. }
  wp_pures.
  iEval (rewrite !List.app_assoc) in "HΦ".
  iApply "HΦ".
  done.
Qed.

Lemma wp_parentNameAndOrdinal (pod_name : go_string) :
  {{{ ⌜ Z.of_nat (length pod_name) <= go_int_max ⌝ }}}
    @! statefulset.parentNameAndOrdinal #pod_name
  {{{ (parent : go_string) (ordinal : w64), RET (#parent, #ordinal);
      ⌜ ∀ set_name,
        (parent = set_name ∧
          0 <= sint.Z ordinal ∧
          pod_name = desired_pod_name set_name (sint.nat ordinal)) ↔
        pod_has_int32_member_name set_name pod_name ⌝
  }}}.
Proof.
  wp_start as "%Hpod_name_len".
  wp_auto.
  wp_apply (wp_strings_LastIndex_singleton pod_name byte_dash with "[]").
  { iSplit; first by iEval (rewrite is_pkg_init_unfold /=).
    iPureIntro. exact Hpod_name_len. }
  iIntros (idx) "%Hidx".
  wp_auto.
  destruct Hidx as [(parent & suffix & Hname_decomp & Hsuffix_no_dash & Hidx_Z)|
                    (Hno_dash & Hidx_Z)].
  - assert (Hprefix_next_bound : Z.of_nat (S (length parent)) <= go_int_max).
    { rewrite Hname_decomp app_length /= in Hpod_name_len. lia. }
    unfold go_int_max in Hprefix_next_bound.
    assert (Hidx_next_Z : sint.Z (word.add idx (W64 1)) =
        Z.of_nat (S (length parent))) by word.
    assert (Hidx_nat : sint.nat idx = length parent) by word.
    assert (Hidx_next_nonneg : 0 <= sint.Z (word.add idx (W64 1))).
    { rewrite Hidx_next_Z. lia. }
    assert (Hidx_next : sint.nat (word.add idx (W64 1)) = S (length parent)) by word.
    wp_if_destruct.
    { exfalso. rewrite Hidx_Z in l. change (sint.Z (W64 0)) with 0 in l. lia. }
    wp_pures.
    wp_pures.
    wp_bind (Slice go.string
      ((#(parent ++ [byte_dash] ++ suffix), #(word.add idx (W64 1)))%V,
       #(functions go.len [go.string]) (#(parent ++ [byte_dash] ++ suffix))))%E.
    iApply (wp_wand _ _ _
      (λ v, ⌜ v = #(drop (sint.nat (word.add idx (W64 1)))
        (parent ++ [byte_dash] ++ suffix)) ⌝)%I with "[]").
    { iApply (wp_string_slice_to_end
        (parent ++ [byte_dash] ++ suffix) (word.add idx (W64 1))).
      - iPureIntro.
        split; [exact Hidx_next_nonneg|].
        rewrite Hidx_next app_length /=.
        lia.
      - iIntros "_".
        iPureIntro.
        done. }
    iIntros (suffix_val) "->".
    assert (drop (sint.nat (word.add idx (W64 1)))
      (parent ++ [byte_dash] ++ suffix) = suffix) as Hdrop_suffix.
    { rewrite Hidx_next.
      clear Hpod_name_len Hsuffix_no_dash Hidx_Z Hprefix_next_bound
        Hidx_next_Z Hidx_nat Hidx_next_nonneg Hidx_next.
      induction parent as [|b parent IH]; simpl; [done|exact IH]. }
    rewrite Hdrop_suffix.
    wp_pures.
    wp_apply (wp_strconv_ParseInt_decimal_int32 with "[]").
    { by iEval (rewrite is_pkg_init_unfold /=). }
    iIntros (ordinal err) "%Hparse".
    wp_auto.
    destruct (parse_decimal_string suffix) as [expected_ordinal|] eqn:Hparse_suffix.
    + destruct (decide (expected_ordinal <= go_int32_max_nat)%nat) as
        [Hexpected_ordinal_bound|Hexpected_ordinal_overflow].
      * destruct Hparse as (Herr_nil & Hordinal_nat & Hordinal_Z & Hordinal_bounds).
        rewrite Herr_nil.
        wp_auto.
        wp_bind (Slice go.string
          (#(parent ++ [byte_dash] ++ suffix), #(W64 0), #idx)%V)%E.
        iApply (wp_wand _ _ _
          (λ v, ⌜ v = #(subslice (sint.nat (W64 0)) (sint.nat idx)
            (parent ++ [byte_dash] ++ suffix)) ⌝)%I with "[]").
        { iApply (wp_string_slice
            (parent ++ [byte_dash] ++ suffix) (W64 0) idx).
          - iPureIntro.
            split.
            + split; [word|].
              rewrite Hidx_Z.
              lia.
            + rewrite Hidx_nat app_length /=.
              lia.
          - iIntros "_".
            iPureIntro.
            done. }
        iIntros (parent_val) "->".
        wp_auto.
        rewrite /subslice /= Hidx_nat.
        rewrite drop_0.
        rewrite take_app_length.
        assert (Hpost : ∀ set_name,
          (parent = set_name ∧ 0 <= sint.Z ordinal ∧
            (parent ++ [byte_dash] ++ suffix) =
              desired_pod_name set_name (sint.nat ordinal)) ↔
          pod_has_int32_member_name set_name (parent ++ [byte_dash] ++ suffix)).
        { intros set_name. split.
          - intros (Hparent_eq & _ & Hname).
            subst set_name.
            unfold pod_has_int32_member_name.
            exists expected_ordinal.
            split; [done|].
            by rewrite -Hordinal_nat.
          - intros Hex.
            unfold pod_has_int32_member_name in Hex.
            destruct Hex as (ordinal' & Hordinal'_bound & Hcanonical).
            pose proof (desired_pod_name_last_dash_decomp
              (parent ++ [byte_dash] ++ suffix) parent suffix set_name ordinal'
              eq_refl Hsuffix_no_dash Hcanonical) as [-> Hsuffix].
            rewrite Hsuffix parse_decimal_string_decimal_string in Hparse_suffix.
            simplify_eq/=.
            repeat split; try done; try lia. }
        iApply ("HΦ" $! parent ordinal).
        iPureIntro.
        exact Hpost.
      * destruct err as [err_i|].
        2: { exfalso. apply Hparse. reflexivity. }
        wp_pures.
        iApply ("HΦ" $! ""%go (W64 (-1))).
        iPureIntro.
        intros set_name. split.
        -- intros (_ & Hnonnegative & _). word.
        -- intros (ordinal' & Hordinal'_bound & Hname).
           pose proof (desired_pod_name_last_dash_decomp
             (parent ++ [byte_dash] ++ suffix) parent suffix set_name ordinal'
             eq_refl Hsuffix_no_dash Hname) as [_ Hsuffix].
           rewrite Hsuffix parse_decimal_string_decimal_string in Hparse_suffix.
           simplify_eq/=.
    + destruct err as [err_i|].
      2: { exfalso. apply Hparse. reflexivity. }
      wp_pures.
      iApply ("HΦ" $! ""%go (W64 (-1))).
      iPureIntro.
      intros set_name. split.
      * intros (_ & Hnonnegative & _). word.
      * intros (ordinal' & Hordinal'_bound & Hname).
        pose proof (desired_pod_name_last_dash_decomp
          (parent ++ [byte_dash] ++ suffix) parent suffix set_name ordinal'
          eq_refl Hsuffix_no_dash Hname) as [_ Hsuffix].
        rewrite Hsuffix parse_decimal_string_decimal_string in Hparse_suffix.
        done.
  - 
    wp_if_destruct.
    2: { exfalso. word. }
    wp_pures.
    iApply ("HΦ" $! ""%go (W64 (-1))).
    iPureIntro.
    intros set_name. split.
    + intros (_ & Hnonnegative & _). word.
    + intros (ordinal' & Hordinal'_bound & Hname).
      exfalso.
      apply Hno_dash.
      rewrite Hname.
      apply desired_pod_name_has_dash.
Qed.

Lemma wp_ordinalOf pod_name ordinal set_name :
  {{{ ⌜ Z.of_nat (length pod_name) <= go_int_max ⌝ ∗
      ⌜ (ordinal <= go_int32_max_nat)%nat ∧
        pod_name = desired_pod_name set_name ordinal ⌝
  }}}
    @! statefulset.ordinalOf #pod_name
  {{{ (ordinal_ret : w64), RET #ordinal_ret;
      ⌜ sint.Z ordinal_ret = Z.of_nat ordinal ⌝
  }}}.
Proof.
  wp_start as "(%Hname_len & %Hpre)".
  destruct Hpre as (Hordinal_bound & Hname).
  wp_auto.
  wp_apply (wp_parentNameAndOrdinal with "[]").
  { iPureIntro. exact Hname_len. }
  iIntros (parent ordinal_ret) "%Hparent".
  wp_auto.
  iApply "HΦ".
  iPureIntro.
  unfold pod_has_int32_member_name.
  pose proof (proj2 (Hparent set_name)
    (ex_intro _ ordinal (conj Hordinal_bound Hname))) as
    (_ & Hordinal_ret_nonnegative & Hname_ret).
  assert (sint.nat ordinal_ret = ordinal) as Hordinal_ret.
  { apply (desired_pod_name_inj set_name).
    rewrite -Hname_ret. exact Hname. }
  replace (sint.Z ordinal_ret) with (Z.of_nat (sint.nat ordinal_ret)) by word.
  by rewrite Hordinal_ret.
Qed.

Lemma wp_isMemberOf (set_name name : go_string) :
  {{{ ⌜ Z.of_nat (length name) <= go_int_max ⌝ }}}
    @! statefulset.isMemberOf #set_name #name
  {{{ (ret : bool), RET #ret;
      ⌜ ret = true ↔ pod_has_int32_member_name set_name name ⌝
  }}}.
Proof.
  wp_start as "%Hname_len".
  wp_auto.
  wp_apply (wp_parentNameAndOrdinal with "[]").
  { iPureIntro. exact Hname_len. }
  iIntros (parent ordinal) "%Hparent".
  wp_auto.
  destruct (decide (parent = set_name)) as [Hparent_eq|Hparent_ne].
  - subst parent.
    replace (bool_decide (set_name = set_name)) with true by
      (symmetry; apply bool_decide_true; done).
    wp_pures.
    wp_load.
    destruct (decide (0 <= sint.Z ordinal)) as
      [Hordinal_nonnegative|Hordinal_negative].
    + wp_auto.
      replace (bool_decide (sint.Z (W64 0) ≤ sint.Z ordinal)) with true by
        (symmetry; apply bool_decide_true; word).
      wp_pures.
      wp_load.
      wp_load.
      wp_pures.
      wp_load.
      wp_pures.
      wp_bind (@! statefulset.podName #set_name #ordinal)%E.
      wp_apply (wp_podName set_name ordinal with "[]").
      { iPureIntro. exact Hordinal_nonnegative. }
      iApply ("HΦ" $! (bool_decide
        (name = desired_pod_name set_name (sint.nat ordinal)))).
      iPureIntro.
      unfold pod_has_int32_member_name.
      split.
      * intros Hret.
        apply bool_decide_eq_true in Hret.
        apply (proj1 (Hparent set_name)).
        repeat split; done.
      * intros Hex.
        destruct (proj2 (Hparent set_name) Hex) as (_ & _ & Hname_eq).
        apply bool_decide_eq_true_2.
        done.
    + wp_auto.
      replace (bool_decide (sint.Z (W64 0) ≤ sint.Z ordinal)) with false by
        (symmetry; apply bool_decide_false; word).
      wp_pures.
      iApply "HΦ".
      iPureIntro.
      unfold pod_has_int32_member_name.
      split; [done|].
      intros Hex.
      destruct (proj2 (Hparent set_name) Hex) as (_ & Hordinal_nonnegative & _).
      lia.
  - replace (bool_decide (parent = set_name)) with false by
      (symmetry; apply bool_decide_false; done).
    wp_auto.
    iApply "HΦ".
    iPureIntro.
    unfold pod_has_int32_member_name.
    split; [done|].
    intros Hex.
    destruct (proj2 (Hparent set_name) Hex) as (Hparent_eq & _ & _).
    contradiction.
Qed.

Lemma wp_podInOrdinalRange set_l (set : StatefulSetV.t) pod_name ordinal set_name dq :
  {{{ "Hset" ∷ StatefulSetV.deepown_l set_l set dq ∗
      "%Hspec_valid" ∷ ⌜ StatefulSetSpecV.valid set.(StatefulSetV.Spec') ⌝ ∗
      "%Hname_len" ∷ ⌜ Z.of_nat (length pod_name) <= go_int_max ⌝ ∗
      "%Hpod_name" ∷ ⌜ (ordinal <= go_int32_max_nat)%nat ∧
        pod_name = desired_pod_name set_name ordinal ⌝
  }}}
    @! statefulset.podInOrdinalRange #set_l #pod_name
  {{{ (ret : bool), RET #ret;
      ⌜ ret = true ↔ (ordinal < statefulset_replicas set)%nat ⌝ ∗
      StatefulSetV.deepown_l set_l set dq
  }}}.
Proof.
  wp_start as "H". iNamed "H".
  wp_auto.
  wp_apply (wp_ordinalOf pod_name ordinal set_name with "[]").
  { iPureIntro. split; done. }
  iIntros (ordinal_ret) "%Hordinal_ret".
  wp_auto.
  replace (bool_decide (sint.Z (W64 0) ≤ sint.Z ordinal_ret)) with true.
  2:{ symmetry. apply bool_decide_true.
      rewrite Hordinal_ret. change (sint.Z (W64 0)) with 0. lia. }
  wp_pures.
  wp_load.
  wp_pures.
  wp_load.
  wp_pures.
  wp_apply (wp_endOrdinalOf with "[$Hset //]").
  iIntros (end_ordinal) "[%Hend_ordinal Hset]".
  wp_pures.
  iApply "HΦ".
  iFrame.
  iPureIntro.
  split.
  - intros Hret.
    apply bool_decide_eq_true in Hret.
    rewrite Hordinal_ret Hend_ordinal in Hret.
    lia.
  - intros Hlt.
    apply bool_decide_eq_true_2.
    rewrite Hordinal_ret Hend_ordinal.
    lia.
Qed.

Lemma wp_isTerminating pod_l (pod : PodV.t) dq :
  {{{ PodV.deepown_l pod_l pod dq }}}
    @! statefulset.isTerminating #pod_l
  {{{ (ret : bool), RET #ret;
      ⌜ ret = true ↔ ¬ is_pod_alive pod ⌝ ∗
      PodV.deepown_l pod_l pod dq
  }}}.
Proof.
  wp_start as "Hpod".
  iPoseProof (PodV.deepown_l_split with "Hpod") as
    "(%Hpod_l_not_null & Hpod_typemeta & Hpod_objectmeta_l & Hpod_spec_l & Hpod_status_l)".
  iDestruct "Hpod_objectmeta_l" as (pod_meta_c) "[Hpod_objectmeta_field Hpod_objectmeta]".
  iNamedPrefix "Hpod_objectmeta" "Hpod_meta_".
  wp_auto.
  iCombineNamed "Hpod_meta_*" as "Hpod_objectmeta".
  iAssert (ObjectMetaV.deepown pod_meta_c pod.(PodV.ObjectMeta') dq)
    with "[Hpod_objectmeta]" as "Hpod_objectmeta".
  { iNamed "Hpod_objectmeta". iFrame. done. }
  iAssert (ObjectMetaV.deepown_l (PodV.objectmeta_ptr pod_l)
      pod.(PodV.ObjectMeta') dq)
    with "[Hpod_objectmeta_field Hpod_objectmeta]" as "Hpod_objectmeta_l".
  { iExists pod_meta_c. iFrame. }
  iPoseProof (PodV.deepown_l_restore _ _ _ Hpod_l_not_null
    with "[$Hpod_typemeta $Hpod_objectmeta_l $Hpod_spec_l $Hpod_status_l]") as "Hpod".
  iApply "HΦ".
  iFrame.
  iPureIntro.
  unfold is_pod_alive.
  split.
  - intros Hnot_null Hdeletion_timestamp_none.
    apply negb_true_iff in Hnot_null.
    apply bool_decide_eq_false in Hnot_null.
    apply Hnot_null.
    by apply Hpod_meta_Hdeepown_deletiontimestamp_none.
  - intros Hnot_alive.
    apply negb_true_iff.
    apply bool_decide_eq_false.
    intros Hnull.
    apply Hnot_alive.
    by apply Hpod_meta_Hdeepown_deletiontimestamp_none.
Qed.

Definition claim_templates_map_insert m claim_template : gmap go_string v1.PersistentVolumeClaim.t :=
  <[claim_template.(v1.PersistentVolumeClaim.ObjectMeta').(v1.ObjectMeta.Name') := claim_template]> m.

Definition claim_templates_map_of_list claim_templates : gmap go_string v1.PersistentVolumeClaim.t :=
  fold_left claim_templates_map_insert claim_templates ∅.

Lemma claim_templates_map_of_list_snoc claim_templates claim_template :
  claim_templates_map_of_list (claim_templates ++ [claim_template]) =
  claim_templates_map_insert (claim_templates_map_of_list claim_templates) claim_template.
Proof.
  unfold claim_templates_map_of_list.
  by rewrite fold_left_app.
Qed.

Lemma claim_templates_map_of_list_values claim_templates :
  map_Forall (λ name claim_template,
    claim_template ∈ claim_templates ∧
    claim_template.(v1.PersistentVolumeClaim.ObjectMeta').(v1.ObjectMeta.Name') = name)
    (claim_templates_map_of_list claim_templates).
Proof.
  induction claim_templates using rev_ind.
  - rewrite /claim_templates_map_of_list /=.
    apply map_Forall_empty.
  - rewrite claim_templates_map_of_list_snoc.
    rewrite map_Forall_lookup.
    intros name claim_template Hlookup.
    unfold claim_templates_map_insert in Hlookup.
    apply lookup_insert_Some in Hlookup as [[<- <-]|[Hname_ne Hlookup]].
    + split; [apply elem_of_app; right; by left|done].
    + rewrite map_Forall_lookup in IHclaim_templates.
      specialize (IHclaim_templates _ _ Hlookup) as [Hin Hname].
      split; [apply elem_of_app; by left|done].
Qed.

Lemma claim_templates_map_of_list_names claim_templates :
  Forall (λ claim_template,
    is_Some (claim_templates_map_of_list claim_templates !!
      claim_template.(v1.PersistentVolumeClaim.ObjectMeta').(v1.ObjectMeta.Name')))
    claim_templates.
Proof.
  induction claim_templates using rev_ind.
  - done.
  - apply Forall_forall. intros claim_template Hin.
    rewrite claim_templates_map_of_list_snoc /claim_templates_map_insert.
    apply in_app_or in Hin.
    destruct Hin as [Hin|Hin].
    + rewrite Forall_forall in IHclaim_templates.
      destruct (IHclaim_templates claim_template Hin) as [mapped Hlookup].
      destruct (decide (
        x.(v1.PersistentVolumeClaim.ObjectMeta').(v1.ObjectMeta.Name') =
        claim_template.(v1.PersistentVolumeClaim.ObjectMeta').(v1.ObjectMeta.Name'))) as
        [Heq|Hne].
      * exists x. by rewrite Heq lookup_insert_eq.
      * exists mapped. by rewrite lookup_insert_ne.
    + destruct Hin as [<-|[]].
      exists x. by rewrite lookup_insert_eq.
Qed.

(* The returned map contains physical PVC template values copied from the
   StatefulSet's physical VolumeClaimTemplates slice.  Keeping the StatefulSet
   deep ownership split in the postcondition exposes that physical slice and
   lets callers relate map entries back to the concrete templates without
   immediately hiding the fields behind StatefulSetV.deepown_l again. *)
Lemma wp_volumeClaimTemplatesByName set_l (set : StatefulSetV.t) dq :
  {{{ StatefulSetV.deepown_l set_l set dq }}}
    @! statefulset.volumeClaimTemplatesByName #set_l
  {{{ (set_phy : v1.StatefulSet.t) claim_templates_map claim_templates_list
      (claim_templates_phy : gmap go_string v1.PersistentVolumeClaim.t),
      RET #claim_templates_map;
      set_l ↦{dq} set_phy ∗
      "%Hdeepown_typemeta" ∷ ⌜ set_phy.(v1.StatefulSet.TypeMeta') = set.(StatefulSetV.TypeMeta') ⌝ ∗
      "Hdeepown_objectmeta" ∷
        ObjectMetaV.deepown set_phy.(v1.StatefulSet.ObjectMeta') set.(StatefulSetV.ObjectMeta') dq ∗
      "%Hdeepown_replicas_none" ∷
        ⌜ set_phy.(v1.StatefulSet.Spec').(v1.StatefulSetSpec.Replicas') = null ↔
          set.(StatefulSetV.Spec').(StatefulSetSpecV.Replicas') = None ⌝ ∗
      "Hdeepown_replicas_some" ∷
        (match set.(StatefulSetV.Spec').(StatefulSetSpecV.Replicas') with
        | Some i =>
            ∃ replicas,
              set_phy.(v1.StatefulSet.Spec').(v1.StatefulSetSpec.Replicas') ↦{dq} replicas ∗
              ⌜ replicas = i ⌝
        | None => True%I
        end) ∗
      "Hdeepown_template" ∷ PodTemplateSpecV.deepown set_phy.(v1.StatefulSet.Spec').(v1.StatefulSetSpec.Template')
          set.(StatefulSetV.Spec').(StatefulSetSpecV.Template') dq ∗
      "Hdeepown_volumeclaimtemplates" ∷ deepown_list
        set_phy.(v1.StatefulSet.Spec').(v1.StatefulSetSpec.VolumeClaimTemplates') claim_templates_list
          set.(StatefulSetV.Spec').(StatefulSetSpecV.VolumeClaimTemplates')
          (λ claim_template_phy pure_claim_template,
            PersistentVolumeClaimV.deepown claim_template_phy pure_claim_template dq) ∗
      "%Hclaim_templates_map_values" ∷
        ⌜ map_Forall (λ name claim_template_phy,
            claim_template_phy ∈ claim_templates_list ∧
            claim_template_phy.(v1.PersistentVolumeClaim.ObjectMeta').(v1.ObjectMeta.Name') = name
          ) claim_templates_phy ⌝ ∗
      "%Hclaim_templates_list_names" ∷
        ⌜ Forall (λ claim_template_phy,
            is_Some (claim_templates_phy !!
              claim_template_phy.(v1.PersistentVolumeClaim.ObjectMeta').(v1.ObjectMeta.Name'))
          ) claim_templates_list ⌝ ∗
      "%Hdeepown_servicename" ∷
        ⌜ set_phy.(v1.StatefulSet.Spec').(v1.StatefulSetSpec.ServiceName') =
          set.(StatefulSetV.Spec').(StatefulSetSpecV.ServiceName') ⌝ ∗
      "Hdeepown_status" ∷ StatefulSetStatusV.deepown set_phy.(v1.StatefulSet.Status') set.(StatefulSetV.Status') dq ∗
      "Hclaim_templates_map" ∷ claim_templates_map ↦$ claim_templates_phy
  }}}.
Proof.
  wp_start as "Hset".
  iDestruct "Hset" as (set_phy) "[Hset_ptr Hset_deepown]".
  iNamed "Hset_deepown".
  iNamed "Hdeepown_spec".
  iDestruct "Hdeepown_volumeclaimtemplates" as (claim_templates_list)
    "Hdeepown_volumeclaimtemplates".
  rewrite /deepown_list.
  iDestruct "Hdeepown_volumeclaimtemplates" as
    "[Hclaim_templates_slice Hclaim_templates_deepown]".
  wp_auto.
  wp_apply wp_map_make2 as "%claim_templates_map Hclaim_templates_map".
  iDestruct (own_slice_len with "Hclaim_templates_slice") as
    %(Hclaim_templates_len1 & Hclaim_templates_len2).
  iDestruct (own_slice_wf with "Hclaim_templates_slice") as
    %Hclaim_templates_cap.
  iDestruct (big_sepL2_length with "Hclaim_templates_deepown") as
    %Hclaim_templates_deepown_len.
  set I := (∃ (i : w64) (claim_template_value : v1.PersistentVolumeClaim.t)
      (claim_templates_map_l : map.t),
    "Hi_ptr" ∷ i_ptr ↦ i ∗
    "Hclaim_templates_slice" ∷
      set_phy.(v1.StatefulSet.Spec').(v1.StatefulSetSpec.VolumeClaimTemplates') ↦*
        claim_templates_list ∗
    "HclaimTemplate_ptr" ∷ claimTemplate_ptr ↦ claim_template_value ∗
    "HclaimTemplates_ptr" ∷ claimTemplates_ptr ↦ claim_templates_map_l ∗
    "Hclaim_templates_map" ∷ claim_templates_map_l ↦$
      claim_templates_map_of_list (take (sint.nat i) claim_templates_list) ∗
    "%Hi" ∷ ⌜ 0 ≤ sint.Z i ≤ sint.Z
      (slice.len set_phy.(v1.StatefulSet.Spec').(v1.StatefulSetSpec.VolumeClaimTemplates')) ⌝
  )%I.
  iAssert I with "[i Hclaim_templates_slice claimTemplate claimTemplates
      Hclaim_templates_map]" as
    "Hloop_inv".
  { iExists (W64 0), (zero_val v1.PersistentVolumeClaim.t), claim_templates_map.
    rewrite take_0 /claim_templates_map_of_list /=.
    iFrame.
    iPureIntro. word. }
  wp_for "Hloop_inv". wp_if_destruct.
  - destruct (decide (0 ≤ sint.Z i <
      sint.Z (slice.len set_phy.(v1.StatefulSet.Spec').(v1.StatefulSetSpec.VolumeClaimTemplates'))))
      as [_|Hbounds]; last word.
    assert (∃ this_claim_template,
      claim_templates_list !! sint.nat i = Some this_claim_template) as
      [this_claim_template Hthis_claim_template_lookup].
    { apply lookup_lt_is_Some_2. rewrite Hclaim_templates_len1. word. }
    wp_apply (wp_load_slice_index with "[$Hclaim_templates_slice]"); [word| |].
    { iPureIntro. exact Hthis_claim_template_lookup. }
    iIntros "Hclaim_templates_slice".
    wp_auto.
    wp_apply (wp_map_insert go.string with "[$Hclaim_templates_map]").
    iIntros "Hclaim_templates_map".
    wp_auto.
    iApply wp_for_post_do.
    wp_auto.
    iFrame "HΦ".
    iFrame "Hset_ptr Hdeepown_objectmeta Hdeepown_replicas_some
      Hdeepown_template Hclaim_templates_deepown Hdeepown_status".
    iExists (word.add i (W64 1)), this_claim_template, claim_templates_map_l.
    assert (claim_templates_map_of_list
      (take (sint.nat (word.add i (W64 1))) claim_templates_list) =
      claim_templates_map_insert
        (claim_templates_map_of_list (take (sint.nat i) claim_templates_list))
        this_claim_template) as Hmap_next.
    { assert (sint.nat (word.add i (W64 1)) = S (sint.nat i)) as -> by word.
      rewrite (take_S_r _ _ _ Hthis_claim_template_lookup).
      apply claim_templates_map_of_list_snoc. }
    rewrite Hmap_next.
    iFrame.
    iFrame "%".
    iPureIntro. word.
  - assert (take (sint.nat i) claim_templates_list = claim_templates_list) as Htake_all.
    { assert (sint.nat i = length claim_templates_list) as Hi_len.
      { rewrite Hclaim_templates_len1. word. }
      rewrite Hi_len.
      apply take_ge. lia. }
    rewrite Htake_all.
    iApply ("HΦ" $! set_phy claim_templates_map_l claim_templates_list
      (claim_templates_map_of_list claim_templates_list)).
    iFrame.
    rewrite /deepown_list.
    iFrame.
    iFrame "%".
    iSplit.
    + iPureIntro. apply claim_templates_map_of_list_values.
    + iPureIntro. apply claim_templates_map_of_list_names.
Unshelve.
  all: apply _.
Qed.

Lemma wp_filterPodsForStatefulSet set_l pods_sl
    (set : StatefulSetV.t) (ptrs : list loc) (pods : list PodV.t) dq_set dq_pods :
  {{{ "Hset" ∷ StatefulSetV.deepown_l set_l set dq_set ∗
      "Hpods_sl" ∷ pods_sl ↦* ptrs ∗
      "Hpods" ∷ ([∗ list] ptr;pod ∈ ptrs;pods, PodV.deepown_l ptr pod dq_pods) ∗
      "%Hpod_name_len" ∷ ⌜ ∀ pod, pod ∈ pods → Z.of_nat (length pod.(PodV.ObjectMeta').(ObjectMetaV.Name')) <= go_int_max ⌝
  }}}
    @! statefulset.filterPodsForStatefulSet #set_l #pods_sl
  {{{ result_sl ptrs', RET #result_sl;
      StatefulSetV.deepown_l set_l set dq_set ∗
      pods_sl ↦* ptrs ∗
      result_sl ↦* ptrs' ∗
      ([∗ list] ptr;pod ∈ ptrs';
        filter (λ pod, pod_has_int32_member_name
          set.(StatefulSetV.ObjectMeta').(ObjectMetaV.Name')
          pod.(PodV.ObjectMeta').(ObjectMetaV.Name')) pods,
        PodV.deepown_l ptr pod dq_pods)
  }}}.
Proof.
  wp_start as "H". iNamed "H".
  wp_auto.
  wp_apply wp_slice_literal. iSplitR; first done.
  iIntros (result_sl0) "[Hresult0 Hown_result_cap]".
  set result0 := {|
    slice.ptr := result_sl0;
    slice.len := W64 (go.array_literal_size []);
    slice.cap := W64 (go.array_literal_size []);
  |}.
  wp_auto.
  iDestruct (own_slice_len with "Hpods_sl") as %(Hpods_sl_len1 & Hpods_sl_len2).
  iDestruct (own_slice_wf with "Hpods_sl") as %Hpods_sl_cap.
  iDestruct (big_sepL2_length with "Hpods") as %Hlen.
  set set_name := set.(StatefulSetV.ObjectMeta').(ObjectMetaV.Name').
  set P := (λ pod, pod_has_int32_member_name set_name
    pod.(PodV.ObjectMeta').(ObjectMetaV.Name')).
  set I := (∃ (i: w64) (pod_ptr_value: loc) (result: slice.t) (ptrs': list loc),
    "Hi_ptr" ∷ i_ptr ↦ i ∗
    "Hset_ptr" ∷ set_ptr ↦ set_l ∗
    "Hset" ∷ StatefulSetV.deepown_l set_l set dq_set ∗
    "Hpod_ptr" ∷ pod_ptr ↦ pod_ptr_value ∗
    "Hresult_ptr" ∷ result_ptr ↦ result ∗
    "Hresult" ∷ result ↦* ptrs' ∗
    "Hlist_pre" ∷ ([∗ list] ptr;pod ∈ ptrs';filter P (take (sint.nat i) pods),
      PodV.deepown_l ptr pod dq_pods) ∗
    "Hlist_post" ∷ ([∗ list] ptr;pod ∈ (drop (sint.nat i) ptrs);(drop (sint.nat i) pods),
      PodV.deepown_l ptr pod dq_pods) ∗
    "Hown_result_cap" ∷ own_slice_cap loc result (DfracOwn 1) ∗
    "%Hi" ∷ ⌜ 0 ≤ sint.Z i ≤ sint.Z (slice.len pods_sl) ⌝
  )%I.
  iAssert (I) with "[i set Hset pod result Hpods Hresult0 Hown_result_cap]" as "Hloop_inv".
  { iExists (W64 0), (zero_val loc), result0, [].
    rewrite !take_0 !filter_nil !big_sepL2_nil.
    iFrame.
    iPureIntro. word. }
  wp_for "Hloop_inv".
  wp_if_destruct.
  - list_elem ptrs (sint.Z i) as this_ptr.
    destruct (decide (0 ≤ sint.Z i < sint.Z (slice.len pods_sl))) as [_|Hbounds]; last word.
    wp_apply (wp_load_slice_index with "[$Hpods_sl]"); [word| |].
    { iPureIntro. exact Hthis_ptr_lookup. }
    iIntros "Hpods_sl". wp_auto.
    assert (∃ this_pod, pods !! sint.nat i = Some this_pod) as [this_pod Hthis_pod_lookup].
    { apply lookup_lt_is_Some_2. rewrite -Hlen Hpods_sl_len1. word. }
    iPoseProof (big_sepL2_head_tail _ _ _ this_ptr this_pod with "Hlist_post") as "[Hthis Hother]".
    { split. all: rewrite lookup_drop Nat.add_0_r; done. }
    iPoseProof (PodV.deepown_l_split with "Hthis") as
      "(%Hthis_not_null & Hthis_typemeta & Hthis_objectmeta_l & Hthis_spec_l & Hthis_status_l)".
    iDestruct "Hthis_objectmeta_l" as (this_meta_c) "[Hthis_objectmeta_field Hthis_objectmeta]".
    iNamedPrefix "Hthis_objectmeta" "Hthis_meta_".
    iPoseProof (StatefulSetV.deepown_l_split with "Hset") as
      "(%Hset_l_not_null & Hset_typemeta & Hset_objectmeta_l & Hset_spec_l & Hset_status_l)".
    iDestruct "Hset_objectmeta_l" as (set_meta_c) "[Hset_objectmeta_field Hset_objectmeta]".
    iNamedPrefix "Hset_objectmeta" "Hset_meta_".
    wp_auto.
    rewrite Hset_meta_Hdeepown_name Hthis_meta_Hdeepown_name.
    wp_apply (wp_isMemberOf with "[]").
    { iPureIntro.
      apply Hpod_name_len.
      apply list_elem_of_lookup_2 in Hthis_pod_lookup.
      exact Hthis_pod_lookup. }
    iIntros (member) "%Hmember".
    iCombineNamed "Hset_meta_*" as "Hset_objectmeta".
    iAssert (ObjectMetaV.deepown set_meta_c set.(StatefulSetV.ObjectMeta') dq_set)
      with "[Hset_objectmeta]" as "Hset_objectmeta".
    { iNamed "Hset_objectmeta". iFrame. done. }
    iAssert (ObjectMetaV.deepown_l (StatefulSetV.objectmeta_ptr set_l)
        set.(StatefulSetV.ObjectMeta') dq_set)
      with "[Hset_objectmeta_field Hset_objectmeta]" as "Hset_objectmeta_l".
    { iExists set_meta_c. iFrame. }
    iPoseProof (StatefulSetV.deepown_l_restore _ _ _ Hset_l_not_null
      with "[$Hset_typemeta $Hset_objectmeta_l $Hset_spec_l $Hset_status_l]") as "Hset".
    iCombineNamed "Hthis_meta_*" as "Hthis_objectmeta".
    iAssert (ObjectMetaV.deepown this_meta_c this_pod.(PodV.ObjectMeta') dq_pods)
      with "[Hthis_objectmeta]" as "Hthis_objectmeta".
    { iNamed "Hthis_objectmeta". iFrame. done. }
    iAssert (ObjectMetaV.deepown_l (PodV.objectmeta_ptr this_ptr)
        this_pod.(PodV.ObjectMeta') dq_pods)
      with "[Hthis_objectmeta_field Hthis_objectmeta]" as "Hthis_objectmeta_l".
    { iExists this_meta_c. iFrame. }
    iPoseProof (PodV.deepown_l_restore _ _ _ Hthis_not_null
      with "[$Hthis_typemeta $Hthis_objectmeta_l $Hthis_spec_l $Hthis_status_l]") as "Hthis".
    wp_if_destruct.
    + wp_apply wp_slice_literal. iSplitR; first done.
      iIntros (sl0) "[Hsl0 _]". wp_auto.
      wp_apply (wp_slice_append with "[$Hresult $Hown_result_cap $Hsl0]").
      iIntros (result') "(Hresult & Hown_result_cap & Hsl0)". wp_auto.
      iApply wp_for_post_do. wp_auto.
      iFrame "Hpods_sl HΦ".
      iExists (word.add i (W64 1)), this_ptr, result', (ptrs' ++ [this_ptr]).
      assert (P this_pod) as Hthis_member.
      { unfold P.
        apply (proj1 Hmember). done. }
      assert (filter P (take (sint.nat i) pods) ++ [this_pod] =
              filter P (take (sint.nat (word.add i (W64 1))) pods)) as <-.
      { assert (sint.nat (word.add i (W64 1)) = S (sint.nat i)) as -> by word.
        rewrite (take_S_r _ _ this_pod); [done|].
        rewrite list.filter_app filter_singleton_True; [done|done|done]. }
      assert (sint.nat (word.add i (W64 1)) = S (sint.nat i)) as -> by word.
      rewrite !drop_drop Nat.add_1_r.
      iFrame.
      iSplitR; [done|]. iPureIntro. word.
    + 
      iApply wp_for_post_do. wp_auto.
      iFrame "Hpods_sl HΦ".
      iExists (word.add i (W64 1)), this_ptr, result, ptrs'.
      assert (¬ P this_pod) as Hthis_not_member.
      { unfold P.
        intros Hthis_member.
        pose proof (proj2 Hmember Hthis_member) as Hfalse.
        done. }
      assert (filter P (take (sint.nat i) pods) =
              filter P (take (sint.nat (word.add i (W64 1))) pods)) as <-.
      { assert (sint.nat (word.add i (W64 1)) = S (sint.nat i)) as -> by word.
        rewrite (take_S_r _ _ this_pod); [done|].
        rewrite list.filter_app filter_singleton_False; [done|done|rewrite app_nil_r; done]. }
      assert (sint.nat (word.add i (W64 1)) = S (sint.nat i)) as -> by word.
      rewrite !drop_drop Nat.add_1_r.
      iFrame. iPureIntro. word.
  - assert (take (sint.nat i) pods = pods) as ->.
    { assert (sint.nat i = length ptrs) as Hi_len.
      { rewrite Hpods_sl_len1. word. }
      rewrite Hlen in Hi_len. rewrite Hi_len.
      apply take_ge. lia. }
    iApply "HΦ". iFrame.
Qed.

(* TODO: complete this definition *)
Parameter pod_match : StatefulSetV.t → PodV.t → Prop.
Axiom pod_match_decision : ∀ sts pod, Decision (pod_match sts pod).
#[local] Existing Instance pod_match_decision.

Definition missing_pod_keys sts (pods : list PodV.t) : list KKey.t :=
  filter (λ key, key ∉ (PodV.key <$> pods)) (desired_pod_keys sts).

Definition needed_pods sts pods : list PodV.t :=
  filter (λ pod, pod_key_is_desired sts (PodV.key pod)) pods.

Definition outdated_pods sts pods : list PodV.t :=
  filter (λ pod, ¬ pod_match sts pod) (needed_pods sts pods).

Definition bad_name_pods sts pods : list PodV.t :=
  filter (λ pod, ¬ pod_has_member_key sts pod) pods.

Definition condemned_pods sts pods : list PodV.t :=
  filter (λ pod, pod_has_member_key sts pod ∧ ¬ pod_key_is_desired sts (PodV.key pod)) pods.

(* The progress metric gives an outdated desired Pod cost 2 and a missing
   desired Pod cost 1, so deleting one outdated Pod strictly reduces the
   distance even though the desired replacement Pod is created by a later run.
   Once the delete only sets DeletionTimestamp, the Pod is no longer alive and
   should not keep contributing to the outdated-Pod distance. *)
Definition pod_distance sts pods : nat :=
  length (missing_pod_keys sts pods) +
  2 * length (filter is_pod_alive (outdated_pods sts pods)) +
  length (filter is_pod_alive (condemned_pods sts pods)) +
  length (bad_name_pods sts pods).

Definition missing_pvc_keys sts (pvcs : list PersistentVolumeClaimV.t) : list KKey.t :=
  filter (λ key, key ∉ (PersistentVolumeClaimV.key <$> pvcs)) (desired_pvc_keys sts).

Definition pvc_distance sts pvcs : nat :=
  length (missing_pvc_keys sts pvcs).

Definition match_distance sts pods pvcs : nat :=
  pod_distance sts pods + pvc_distance sts pvcs.

Definition pods_match sts pods : Prop :=
  PodV.key <$> pods ≡ₚ desired_pod_keys sts ∧
  Forall is_pod_alive pods ∧
  Forall (pod_match sts) pods.

Definition pvcs_match sts (pvcs : list PersistentVolumeClaimV.t) : Prop :=
  ∀ key, key ∈ desired_pvc_keys sts →
    key ∈ (PersistentVolumeClaimV.key <$> pvcs).

Definition current_state_matches sts pods pvcs : Prop :=
  pods_match sts pods ∧ pvcs_match sts pvcs.

Lemma match_distance_zero_matches γ sts pods pvcs :
  (∀ pod, pod ∈ pods → is_pod_alive pod) →
  ([∗ list] pod ∈ pods, own_meta_frag γ (PodV.key pod) pod.(PodV.ObjectMeta').(ObjectMetaV.UID') 1 pod.(PodV.ObjectMeta')) -∗
  ⌜ match_distance sts pods pvcs = 0%nat ↔ current_state_matches sts pods pvcs ⌝.
Proof.
  iIntros (Hpods_alive) "Hpod_meta_frags".
  iPoseProof (kview.own_meta_list_no_dup PodV.key PodV.ObjectMeta'
    with "Hpod_meta_frags") as "%Hpods_nodup".
  iPureIntro.
  assert (Hdesired_pods_nodup : NoDup (desired_pod_keys sts)).
  { unfold desired_pod_keys, desired_ordinals.
    apply NoDup_fmap_2.
    - intros ordinal1 ordinal2 Hkey.
      apply (f_equal KKey.Name') in Hkey.
      simpl in Hkey.
      unfold desired_pod_name in Hkey.
      simpl in Hkey.
      apply app_inv_head in Hkey.
      inversion Hkey as [Hdecimal].
      by apply decimal_string_inj in Hdecimal.
    - apply NoDup_seq. }
	split.
	- intros Hdist.
	  unfold match_distance, pod_distance, pvc_distance in Hdist.
	  assert (Hmissing_pods : length (missing_pod_keys sts pods) = 0%nat) by lia.
    assert (Halive_outdated_pods :
        length (filter is_pod_alive (outdated_pods sts pods)) = 0%nat) by lia.
    assert (Hbad_name_pods : length (bad_name_pods sts pods) = 0%nat) by lia.
    assert (Halive_condemned_pods :
        length (filter is_pod_alive (condemned_pods sts pods)) = 0%nat) by lia.
    assert (Hmissing_pvcs : length (missing_pvc_keys sts pvcs) = 0%nat) by lia.
    assert (Hpod_good_name : ∀ pod,
        pod ∈ pods → pod_has_member_key sts pod).
    { intros pod Hpod.
      destruct (decide (pod_has_member_key sts pod)) as [Hgood|Hbad]; [done|].
      exfalso.
      eapply (filter_length_zero_not_elem
        (λ pod, ¬ pod_has_member_key sts pod) pods pod);
        [exact Hbad_name_pods|exact Hpod|exact Hbad]. }
    assert (Hdesired_pod_actual : ∀ key,
        key ∈ desired_pod_keys sts → key ∈ PodV.key <$> pods).
	  { intros key Hdesired.
	    destruct (decide (key ∈ PodV.key <$> pods)) as [Hactual|Hnot_actual]; [done|].
	    exfalso.
	    eapply (filter_length_zero_not_elem
	      (λ key, key ∉ (PodV.key <$> pods)) (desired_pod_keys sts) key);
	      [exact Hmissing_pods|exact Hdesired|exact Hnot_actual]. }
	  assert (Hactual_pod_desired : ∀ pod,
	      pod ∈ pods → pod_key_is_desired sts (PodV.key pod)).
	  { intros pod Hpod.
	    destruct (decide (pod_key_is_desired sts (PodV.key pod))) as [Hdesired|Hnot_desired]; [done|].
	    exfalso.
	    assert (Hpod_condemned : pod ∈ condemned_pods sts pods).
	    { unfold condemned_pods.
	      apply list_elem_of_filter. split; [split; [by apply Hpod_good_name|exact Hnot_desired]|exact Hpod]. }
	    eapply (filter_length_zero_not_elem
	      is_pod_alive (condemned_pods sts pods) pod);
	      [exact Halive_condemned_pods|exact Hpod_condemned|by apply Hpods_alive]. }
	  assert (Hpods_perm : PodV.key <$> pods ≡ₚ desired_pod_keys sts).
	  { apply NoDup_Permutation; [exact Hpods_nodup|exact Hdesired_pods_nodup|].
	    intros key. split.
	    - intros Hactual.
	      apply list_elem_of_fmap_1 in Hactual as (pod & Hkey_eq & Hpod).
	      rewrite Hkey_eq. by apply Hactual_pod_desired.
	    - intros Hdesired. by apply Hdesired_pod_actual. }
	  split.
	  + split; [exact Hpods_perm|].
	    split.
	    * apply Forall_forall. intros pod Hpod.
	      rewrite <- list_elem_of_In in Hpod.
	      by apply Hpods_alive.
	    * apply Forall_forall. intros pod Hpod.
	      rewrite <- list_elem_of_In in Hpod.
	      destruct (decide (pod_match sts pod)) as [Hmatch|Hnot_match]; [exact Hmatch|].
	      exfalso.
	      assert (Hpod_needed : pod ∈ needed_pods sts pods).
	      { unfold needed_pods.
	        apply list_elem_of_filter. split; [by apply Hactual_pod_desired|exact Hpod]. }
	      assert (Hpod_outdated : pod ∈ outdated_pods sts pods).
	      { unfold outdated_pods.
	        apply list_elem_of_filter. split; [exact Hnot_match|exact Hpod_needed]. }
	      eapply (filter_length_zero_not_elem
	        is_pod_alive
	        (outdated_pods sts pods) pod);
	        [exact Halive_outdated_pods|exact Hpod_outdated|].
	      by apply Hpods_alive.
	  + intros key Hdesired.
	    destruct (decide (key ∈ PersistentVolumeClaimV.key <$> pvcs)) as [Hactual|Hnot_actual]; [done|].
	    exfalso.
	    eapply (filter_length_zero_not_elem
	      (λ key, key ∉ (PersistentVolumeClaimV.key <$> pvcs)) (desired_pvc_keys sts) key);
	      [exact Hmissing_pvcs|exact Hdesired|exact Hnot_actual].
	- intros [[Hpods_perm [Hpods_alive_forall Hpods_match_forall]] Hpvcs_match].
	  unfold match_distance, pod_distance, pvc_distance.
	  assert (Hmissing_pods_nil : missing_pod_keys sts pods = []).
	  { unfold missing_pod_keys.
	    apply filter_none. intros key Hdesired Hnot_actual.
	    apply Hnot_actual.
	    rewrite Hpods_perm. exact Hdesired. }
	  assert (Houtdated_pods_nil : outdated_pods sts pods = []).
	  { unfold outdated_pods.
	    apply filter_none. intros pod Hpod Hnot_match.
	    rewrite Forall_forall in Hpods_match_forall.
	    unfold needed_pods in Hpod.
	    apply list_elem_of_filter in Hpod as [_ Hpod].
	    rewrite list_elem_of_In in Hpod.
	    exact (Hnot_match (Hpods_match_forall pod Hpod)). }
	  assert (Hbad_name_pods_nil : bad_name_pods sts pods = []).
	  { unfold bad_name_pods.
	    apply filter_none. intros pod Hpod Hnot_member.
	    apply Hnot_member.
	    assert (Hkey_desired : PodV.key pod ∈ desired_pod_keys sts).
	    { rewrite -Hpods_perm. by apply list_elem_of_fmap_2. }
	    unfold desired_pod_keys in Hkey_desired.
	    apply list_elem_of_fmap_1 in Hkey_desired as (ordinal & Hkey_eq & _).
	    exists ordinal. exact Hkey_eq. }
	  assert (Halive_condemned_pods_nil : filter is_pod_alive (condemned_pods sts pods) = []).
	  { apply filter_none. intros pod Hpod Halive.
	    unfold condemned_pods in Hpod.
	    apply list_elem_of_filter in Hpod as ((_ & Hnot_desired) & Hpod).
	    apply Hnot_desired.
	    unfold pod_key_is_desired.
	    rewrite -Hpods_perm. by apply list_elem_of_fmap_2. }
	  assert (Hmissing_pvcs_nil : missing_pvc_keys sts pvcs = []).
	  { unfold missing_pvc_keys.
	    apply filter_none. intros key Hdesired Hnot_actual.
      apply Hnot_actual. by apply Hpvcs_match. }
    rewrite Hmissing_pods_nil Houtdated_pods_nil Hbad_name_pods_nil
      Halive_condemned_pods_nil Hmissing_pvcs_nil.
    done.
Qed.

Definition pod_meta_except_resource_version_changed
    (pods pods' : list PodV.t) : Prop :=
  ∃ pod pod',
    pod ∈ pods ∧
    pod' ∈ pods' ∧
    PodV.key pod = PodV.key pod' ∧
    ObjectMetaV.without_resource_version pod.(PodV.ObjectMeta') ≠
      ObjectMetaV.without_resource_version pod'.(PodV.ObjectMeta').

Definition pod_spec_changed (pods pods' : list PodV.t) : Prop :=
  ∃ pod pod',
    pod ∈ pods ∧
    pod' ∈ pods' ∧
    PodV.key pod = PodV.key pod' ∧
    pod.(PodV.Spec') ≠ pod'.(PodV.Spec').

Definition pods_progress_observed (pods pods' : list PodV.t) : Prop :=
  list_to_set (C:=gset KKey.t) (PodV.key <$> pods) ≠
    list_to_set (C:=gset KKey.t) (PodV.key <$> pods') ∨
  pod_meta_except_resource_version_changed pods pods' ∨
  pod_spec_changed pods pods'.

Lemma wp_syncStatefulSet_progress γ l (gv: schema.GroupVersion.t) namespace name sts dq pods pvcs :
  {{{ is_pkg_init code.controllers.statefulset.pkg_id.statefulset ∗
      "#Hisk" ∷ is_kubernetes γ l ∗
      "#Hglobal_l" ∷ (global_addr apimodel.ModelState) ↦□ l ∗
      "#Hglobal_gv" ∷ (global_addr apps_v1.SchemeGroupVersion) ↦□ gv ∗
      "Hown_sts_meta_frag" ∷ own_meta_frag γ (StatefulSetV.key sts) sts.(StatefulSetV.ObjectMeta').(ObjectMetaV.UID') dq sts.(StatefulSetV.ObjectMeta') ∗
      "Hown_sts_spec_frag" ∷ own_spec_frag γ (StatefulSetV.key sts) sts.(StatefulSetV.ObjectMeta').(ObjectMetaV.UID') dq (ObjectSpecV.StatefulSetSpec sts.(StatefulSetV.Spec')) ∗
      "Hown_pod_frags" ∷ ([∗ list] pod ∈ pods,
        own_meta_frag γ (PodV.key pod) pod.(PodV.ObjectMeta').(ObjectMetaV.UID') 1 pod.(PodV.ObjectMeta') ∗
        own_spec_frag γ (PodV.key pod) pod.(PodV.ObjectMeta').(ObjectMetaV.UID') 1 (ObjectSpecV.PodSpec pod.(PodV.Spec'))) ∗
      "Hown_pvc_frags" ∷ ([∗ list] pvc ∈ pvcs,
        own_meta_frag γ (PersistentVolumeClaimV.key pvc) pvc.(PersistentVolumeClaimV.ObjectMeta').(ObjectMetaV.UID') 1 pvc.(PersistentVolumeClaimV.ObjectMeta') ∗
        own_spec_frag γ (PersistentVolumeClaimV.key pvc) pvc.(PersistentVolumeClaimV.ObjectMeta').(ObjectMetaV.UID') 1 (ObjectSpecV.PersistentVolumeClaimSpec pvc.(PersistentVolumeClaimV.Spec'))) ∗
      "Hown_children_frag" ∷ own_children_frag γ (StatefulSetV.key sts) sts.(StatefulSetV.ObjectMeta').(ObjectMetaV.UID') 1 (list_to_set (PodV.key <$> pods)) ∗
      "Hown_reserved_missing_pod_keys" ∷ ([∗ list] key ∈ missing_pod_keys sts pods, own_reserved_frag γ key) ∗
      "Hown_reserved_missing_pvc_keys" ∷ ([∗ list] key ∈ missing_pvc_keys sts pvcs, own_reserved_frag γ key) ∗
      "%Hnamespace_eq" ∷ ⌜ namespace = sts.(StatefulSetV.ObjectMeta').(ObjectMetaV.Namespace') ⌝ ∗
      "%Hname_eq" ∷ ⌜ name = sts.(StatefulSetV.ObjectMeta').(ObjectMetaV.Name') ⌝ ∗
      "%Hdeletion_timestamp_eq" ∷ ⌜ sts.(StatefulSetV.ObjectMeta').(ObjectMetaV.DeletionTimestamp') = None ⌝
  }}}
    @! statefulset.syncStatefulSet #namespace #name
  {{{ (pods' : list PodV.t) (pvcs' : list PersistentVolumeClaimV.t) (err : interface.t), RET #err;
      (* We expect one of the three cases when reconcile finishes:
        (1) the current state (pods' and pvcs') matches the desired state encoded in sts,
        (2) the distance is reduced and a new reoncile is rescheduled because of changes to pods
        (3) the distance doesn't get increased because the controller needs to wait for some terminating pods
      *)
      ⌜ current_state_matches sts pods' pvcs' ∨
        pods_progress_observed pods pods' ∧ match_distance sts pods' pvcs' < match_distance sts pods pvcs ∨
        (∃ pod, pod ∈ pods ∧ ¬ is_pod_alive pod) ∧ match_distance sts pods' pvcs' ≤ match_distance sts pods pvcs ⌝ ∗
      own_meta_frag γ (StatefulSetV.key sts) sts.(StatefulSetV.ObjectMeta').(ObjectMetaV.UID') dq sts.(StatefulSetV.ObjectMeta') ∗
      own_spec_frag γ (StatefulSetV.key sts) sts.(StatefulSetV.ObjectMeta').(ObjectMetaV.UID') dq (ObjectSpecV.StatefulSetSpec sts.(StatefulSetV.Spec')) ∗
      ([∗ list] pod ∈ pods',
        own_meta_frag γ (PodV.key pod) pod.(PodV.ObjectMeta').(ObjectMetaV.UID') 1 pod.(PodV.ObjectMeta') ∗
        own_spec_frag γ (PodV.key pod) pod.(PodV.ObjectMeta').(ObjectMetaV.UID') 1 (ObjectSpecV.PodSpec pod.(PodV.Spec'))) ∗
      ([∗ list] pvc ∈ pvcs',
        own_meta_frag γ (PersistentVolumeClaimV.key pvc) pvc.(PersistentVolumeClaimV.ObjectMeta').(ObjectMetaV.UID') 1 pvc.(PersistentVolumeClaimV.ObjectMeta') ∗
        own_spec_frag γ (PersistentVolumeClaimV.key pvc) pvc.(PersistentVolumeClaimV.ObjectMeta').(ObjectMetaV.UID') 1 (ObjectSpecV.PersistentVolumeClaimSpec pvc.(PersistentVolumeClaimV.Spec'))) ∗
      own_children_frag γ (StatefulSetV.key sts) sts.(StatefulSetV.ObjectMeta').(ObjectMetaV.UID') 1 (list_to_set (PodV.key <$> pods'))
  }}}.
Proof.
Admitted.

End proof.
