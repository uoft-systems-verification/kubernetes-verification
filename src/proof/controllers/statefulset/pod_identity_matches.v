From New.proof Require Import wp_keep.
From New.proof.controllers.statefulset Require Export pod_predicates.
From New.proof.controllers.statefulset Require Export ordinal.

Local Transparent ObjectMetaV.deepown ObjectMetaView.ObjectMetaV.deepown.


(* Collect transient allocations from imports before checking large program proofs. *)
Optimize Heap.

Section proof.
Context `{hG: !heapGS Σ} `{!ffi_semantics _ _}.
Context {sem : go.Semantics}
  {package_sem : code.controllers.statefulset.statefulset.Assumptions}.
Context {model_sem : apimodel.Assumptions}.
Collection W := sem + package_sem + model_sem.
#[local] Instance base_common_sem : common.Assumptions | 100 :=
  code.controllers.statefulset.statefulset.import_common_Assumption.
#[local] Instance controller_sem : controller.Assumptions :=
  code.controllers.statefulset.statefulset.import_controller_Assumption.
#[local] Instance runtime_sem : code.k8s_io.apimachinery.pkg.runtime.runtime.Assumptions :=
  controller.import_runtime_Assumption.
#[local] Instance runtime_object_underlying_eq :
    runtime.Object ≤u runtime.Objectⁱᵐᵖˡ.
Proof using package_sem model_sem. apply _. Qed.
#[local] Instance meta_object_underlying_eq :
    meta_v1.Object ≤u meta_v1.Objectⁱᵐᵖˡ.
Proof using package_sem model_sem. apply _. Qed.
#[local] Instance base_apimodel_sem : apimodel.Assumptions | 100 :=
  model_sem.
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
Proof using package_sem model_sem.
  constructor; try exact object_core_v1_sem; try apply _.
Defined.
#[local] Instance common_sem : common.Assumptions | 0.
Proof using package_sem model_sem.
  constructor; try exact apimodel_sem; try apply _.
Defined.
Context `{!kubernetesModelG Σ}.
Local Set Default Proof Using "All".

Lemma wp_identityMatches set_l pod_l (set : StatefulSetV.t) (pod : PodV.t)
    dq_set dq_pod :
  {{{ "Hset" ∷ StatefulSetV.deepown_l set_l set dq_set ∗
      "Hpod" ∷ PodV.deepown_l pod_l pod dq_pod ∗
      "%Hpod_name_len" ∷ ⌜ Z.of_nat (length pod.(PodV.ObjectMeta').(ObjectMetaV.Name')) <= go_int_max ⌝
  }}}
    @! statefulset.identityMatches #set_l #pod_l
  {{{ (ret : bool), RET #ret;
      "Hset" ∷ StatefulSetV.deepown_l set_l set dq_set ∗
      "Hpod" ∷ PodV.deepown_l pod_l pod dq_pod ∗
      "%Hret" ∷ ⌜ ret = true ↔ pod_identity_matches set pod ⌝
  }}}.
Proof.
  wp_start as "H". iNamed "H".
  (* Only metadata is read; keep both specifications folded across every branch. *)
  iPoseProof (StatefulSetV.deepown_l_split with "Hset") as
    "(%Hset_l_not_null & Hset_typemeta & Hset_objectmeta_l & Hset_spec_l & Hset_status_l)".
  iDestruct "Hset_objectmeta_l" as (set_meta_c)
    "[Hset_objectmeta_field Hset_objectmeta]".
  iNamedPrefix "Hset_objectmeta" "Hset_meta_".
  iPoseProof (PodV.deepown_l_split with "Hpod") as
    "(%Hpod_l_not_null & Hpod_typemeta & Hpod_objectmeta_l & Hpod_spec_l & Hpod_status_l)".
  iDestruct "Hpod_objectmeta_l" as (pod_meta_c)
    "[Hpod_objectmeta_field Hpod_objectmeta]".
  iNamedPrefix "Hpod_objectmeta" "Hpod_meta_".
  Ltac restore_identity_objects set_meta_c set dq_set set_l
      Hset_l_not_null pod_meta_c pod dq_pod pod_l
      Hpod_l_not_null :=
    iCombineNamed "Hset_meta_*" as "Hset_objectmeta";
    iAssert (ObjectMetaV.deepown set_meta_c
        set.(StatefulSetV.ObjectMeta') dq_set)
      with "[Hset_objectmeta]" as "Hset_objectmeta";
    [ iNamed "Hset_objectmeta"; iFrame; done | ];
    iAssert (ObjectMetaV.deepown_l (StatefulSetV.objectmeta_ptr set_l)
        set.(StatefulSetV.ObjectMeta') dq_set)
      with "[Hset_objectmeta_field Hset_objectmeta]" as "Hset_objectmeta_l";
    [ iExists set_meta_c; iFrame | ];
    iPoseProof (StatefulSetV.deepown_l_restore _ _ _ Hset_l_not_null
      with "[$Hset_typemeta $Hset_objectmeta_l $Hset_spec_l $Hset_status_l]")
      as "Hset";
    iCombineNamed "Hpod_meta_*" as "Hpod_objectmeta";
    iAssert (ObjectMetaV.deepown pod_meta_c pod.(PodV.ObjectMeta') dq_pod)
      with "[Hpod_objectmeta]" as "Hpod_objectmeta";
    [ iNamed "Hpod_objectmeta"; iFrame; done | ];
    iAssert (ObjectMetaV.deepown_l (PodV.objectmeta_ptr pod_l)
        pod.(PodV.ObjectMeta') dq_pod)
      with "[Hpod_objectmeta_field Hpod_objectmeta]" as "Hpod_objectmeta_l";
    [ iExists pod_meta_c; iFrame | ];
    iPoseProof (PodV.deepown_l_restore _ _ _ Hpod_l_not_null
      with "[$Hpod_typemeta $Hpod_objectmeta_l $Hpod_spec_l $Hpod_status_l]")
      as "Hpod".
  Ltac finish_identity_false set_meta_c set dq_set set_l
      Hset_l_not_null pod_meta_c pod dq_pod pod_l
      Hpod_l_not_null :=
    restore_identity_objects set_meta_c set dq_set set_l
      Hset_l_not_null pod_meta_c pod dq_pod pod_l Hpod_l_not_null;
    iApply ("HΦ" $! false);
    iFrame;
    iPureIntro;
    split; [done | intros; contradiction].
  Ltac finish_identity_false_with_labels set_meta_c set dq_set set_l
      Hset_l_not_null pod_meta_c pod dq_pod pod_l
      Hpod_l_not_null labels Hlabels Hlabels_none :=
    iAssert (match pod.(PodV.ObjectMeta').(ObjectMetaV.Labels') with
        | Some vl => ∃ cl,
            v1.ObjectMeta.Labels' pod_meta_c ↦${dq_pod} cl ∗ ⌜ cl = vl ⌝
        | None => True
        end)%I with "[Hpod_labels]" as "Hpod_meta_Hdeepown_labels_some";
    [ rewrite Hlabels; iExists labels; iFrame; done | ];
    iCombineNamed "Hset_meta_*" as "Hset_objectmeta";
    iAssert (ObjectMetaV.deepown set_meta_c
        set.(StatefulSetV.ObjectMeta') dq_set)
      with "[Hset_objectmeta]" as "Hset_objectmeta";
    [ iNamed "Hset_objectmeta"; iFrame; done | ];
    iAssert (ObjectMetaV.deepown_l (StatefulSetV.objectmeta_ptr set_l)
        set.(StatefulSetV.ObjectMeta') dq_set)
      with "[Hset_objectmeta_field Hset_objectmeta]" as "Hset_objectmeta_l";
    [ iExists set_meta_c; iFrame | ];
    iPoseProof (StatefulSetV.deepown_l_restore _ _ _ Hset_l_not_null
      with "[$Hset_typemeta $Hset_objectmeta_l $Hset_spec_l $Hset_status_l]")
      as "Hset";
    iCombineNamed "Hpod_meta_*" as "Hpod_objectmeta";
    iAssert (ObjectMetaV.deepown pod_meta_c pod.(PodV.ObjectMeta') dq_pod)
      with "[Hpod_objectmeta]" as "Hpod_objectmeta";
    [ iNamed "Hpod_objectmeta"; iFrame;
      repeat (iSplit; first (iPureIntro; done));
      iSplit;
      [ iPureIntro; rewrite Hlabels; exact Hlabels_none | ];
      repeat (iSplit; first (iPureIntro; done)); iFrame "%"
    | ];
    iAssert (ObjectMetaV.deepown_l (PodV.objectmeta_ptr pod_l)
        pod.(PodV.ObjectMeta') dq_pod)
      with "[Hpod_objectmeta_field Hpod_objectmeta]" as "Hpod_objectmeta_l";
    [ iExists pod_meta_c; iFrame | ];
    iPoseProof (PodV.deepown_l_restore _ _ _ Hpod_l_not_null
      with "[$Hpod_typemeta $Hpod_objectmeta_l $Hpod_spec_l $Hpod_status_l]")
      as "Hpod";
    iApply ("HΦ" $! false);
    iFrame;
    iPureIntro;
    split; [done | intros; contradiction].
  Ltac finish_identity_false_without_labels set_meta_c set dq_set set_l
      Hset_l_not_null pod_meta_c pod dq_pod pod_l
      Hpod_l_not_null Hlabels Hlabels_none :=
    iCombineNamed "Hset_meta_*" as "Hset_objectmeta";
    iAssert (ObjectMetaV.deepown set_meta_c
        set.(StatefulSetV.ObjectMeta') dq_set)
      with "[Hset_objectmeta]" as "Hset_objectmeta";
    [ iNamed "Hset_objectmeta"; iFrame; done | ];
    iAssert (ObjectMetaV.deepown_l (StatefulSetV.objectmeta_ptr set_l)
        set.(StatefulSetV.ObjectMeta') dq_set)
      with "[Hset_objectmeta_field Hset_objectmeta]" as "Hset_objectmeta_l";
    [ iExists set_meta_c; iFrame | ];
    iPoseProof (StatefulSetV.deepown_l_restore _ _ _ Hset_l_not_null
      with "[$Hset_typemeta $Hset_objectmeta_l $Hset_spec_l $Hset_status_l]")
      as "Hset";
    iCombineNamed "Hpod_meta_*" as "Hpod_objectmeta";
    iAssert (ObjectMetaV.deepown pod_meta_c pod.(PodV.ObjectMeta') dq_pod)
      with "[Hpod_objectmeta]" as "Hpod_objectmeta";
    [ iNamed "Hpod_objectmeta"; iFrame;
      do 9 (iSplit; first (iPureIntro; assumption));
      iSplit;
      [ iPureIntro; rewrite Hlabels; exact Hlabels_none | ];
      iSplit; [ rewrite Hlabels; done | ];
      repeat (iSplit; first (iPureIntro; assumption)); iFrame "%"
    | ];
    iAssert (ObjectMetaV.deepown_l (PodV.objectmeta_ptr pod_l)
        pod.(PodV.ObjectMeta') dq_pod)
      with "[Hpod_objectmeta_field Hpod_objectmeta]" as "Hpod_objectmeta_l";
    [ iExists pod_meta_c; iFrame | ];
    iPoseProof (PodV.deepown_l_restore _ _ _ Hpod_l_not_null
      with "[$Hpod_typemeta $Hpod_objectmeta_l $Hpod_spec_l $Hpod_status_l]")
      as "Hpod";
    iApply ("HΦ" $! false);
    iFrame;
    iPureIntro;
    split; [done | intros; contradiction].
  wp_auto_keep.
  wp_apply (wp_parentNameAndOrdinal with "[]").
  { iPureIntro. rewrite Hpod_meta_Hdeepown_name. exact Hpod_name_len. }
  iIntros (parent ordinal) "%Hparent".
  wp_auto_keep.
  destruct (decide (pod_identity_matches set pod)) as [Hmatches|Hnot_matches].
  2: {
    wp_if_destruct.
    2: { finish_identity_false set_meta_c set dq_set set_l
      Hset_l_not_null pod_meta_c pod dq_pod pod_l Hpod_l_not_null. }
    wp_if_destruct.
    2: { finish_identity_false set_meta_c set dq_set set_l
      Hset_l_not_null pod_meta_c pod dq_pod pod_l Hpod_l_not_null. }
    wp_apply (wp_podName (v1.ObjectMeta.Name' set_meta_c) ordinal with "[]").
    { iPureIntro. word. }
    wp_if_destruct.
    2: { finish_identity_false set_meta_c set dq_set set_l
      Hset_l_not_null pod_meta_c pod dq_pod pod_l Hpod_l_not_null. }
    wp_if_destruct.
    2: { finish_identity_false set_meta_c set dq_set set_l
      Hset_l_not_null pod_meta_c pod dq_pod pod_l Hpod_l_not_null. }
    destruct pod.(PodV.ObjectMeta').(ObjectMetaV.Labels') as [labels|]
      eqn:Hlabels.
    - iDestruct "Hpod_meta_Hdeepown_labels_some" as (labels_c)
        "[Hpod_labels %Hlabels_c]".
      subst labels_c.
      wp_apply (wp_map_lookup1 with "Hpod_labels") as "Hpod_labels".
      wp_if_destruct.
      2: {
        finish_identity_false_with_labels set_meta_c set dq_set set_l
          Hset_l_not_null pod_meta_c pod dq_pod pod_l
          Hpod_l_not_null labels Hlabels Hpod_meta_Hdeepown_labels_none.
      }
      wp_apply (wp_map_lookup1 with "Hpod_labels") as "Hpod_labels".
      wp_apply (wp_strconv_Itoa with "[]").
      { iSplit; first by iEval (rewrite is_pkg_init_unfold /=).
        iPureIntro. word. }
      wp_if_destruct.
      2: {
        finish_identity_false_with_labels set_meta_c set dq_set set_l
          Hset_l_not_null pod_meta_c pod dq_pod pod_l
          Hpod_l_not_null labels Hlabels Hpod_meta_Hdeepown_labels_none.
      }
      exfalso.
      apply Hnot_matches.
      assert (Hcanonical :
          pod.(PodV.ObjectMeta').(ObjectMetaV.Name') = desired_pod_name
            set.(StatefulSetV.ObjectMeta').(ObjectMetaV.Name')
            (sint.nat ordinal)).
      { rewrite -Hpod_meta_Hdeepown_name -Hset_meta_Hdeepown_name. exact e. }
      assert (Hparse : parse_member_name
          set.(StatefulSetV.ObjectMeta').(ObjectMetaV.Name')
          pod.(PodV.ObjectMeta').(ObjectMetaV.Name') =
          Some (sint.nat ordinal)).
      { by apply parse_member_name_complete. }
      pose proof (proj1 (Hparent (v1.ObjectMeta.Name' set_meta_c))
        (conj eq_refl (conj l e))) as Hmember.
      destruct Hmember as (member_ordinal & Hmember_bound & Hmember_name).
      assert (Hmember_ordinal : member_ordinal = sint.nat ordinal).
      { apply (desired_pod_name_inj (v1.ObjectMeta.Name' set_meta_c)).
        rewrite -Hmember_name. exact e. }
      subst member_ordinal.
      assert (Hpod_name_nonempty :
          v1.ObjectMeta.Name' pod_meta_c ≠ ""%go).
      { intros Hempty.
        pose proof (desired_pod_name_has_dash
          (v1.ObjectMeta.Name' set_meta_c) (sint.nat ordinal)) as Hdash.
        unfold desired_pod_name in Hdash.
        rewrite -e Hempty in Hdash.
        rewrite elem_of_nil in Hdash. exact Hdash. }
      assert (Hpod_name_lookup :
          labels !! statefulset_pod_name_label =
            Some pod.(PodV.ObjectMeta').(ObjectMetaV.Name')).
      { unfold statefulset_pod_name_label.
        destruct (labels !! "statefulset.kubernetes.io/pod-name"%go) as [label|]
          eqn:Hlookup.
        - simpl in e1. f_equal.
          rewrite -Hpod_meta_Hdeepown_name. exact e1.
        - simpl in e1. exfalso. apply Hpod_name_nonempty. by rewrite -e1. }
      assert (Hpod_index_lookup :
          labels !! pod_index_label = Some (decimal_string (sint.nat ordinal))).
      { unfold pod_index_label.
        destruct (labels !! "apps.kubernetes.io/pod-index"%go) as [label|]
          eqn:Hlookup.
        - simpl in e2. by f_equal.
        - simpl in e2.
          pose proof (parse_decimal_string_decimal_string
            (sint.nat ordinal)) as Hdecimal.
          rewrite -e2 in Hdecimal. done. }
      unfold pod_identity_matches.
      rewrite Hparse Hlabels.
      repeat split; try done.
      by rewrite -Hpod_meta_Hdeepown_namespace
        -Hset_meta_Hdeepown_namespace.
    - assert (Hlabels_nil : v1.ObjectMeta.Labels' pod_meta_c = null).
      { apply Hpod_meta_Hdeepown_labels_none. reflexivity. }
      rewrite Hlabels_nil.
      wp_auto_keep.
      wp_if_destruct.
      + rewrite Hlabels_nil.
        wp_auto_keep.
        wp_apply (wp_strconv_Itoa with "[]").
        { iSplit; first by iEval (rewrite is_pkg_init_unfold /=).
          iPureIntro. word. }
        wp_if_destruct.
        * exfalso.
          match goal with
          | H : ""%go = decimal_string (sint.nat ordinal) |- _ =>
              pose proof (parse_decimal_string_decimal_string
                (sint.nat ordinal)) as Hdecimal;
              rewrite -H in Hdecimal; done
          end.
        * finish_identity_false_without_labels set_meta_c set dq_set set_l
            Hset_l_not_null pod_meta_c pod dq_pod pod_l
            Hpod_l_not_null Hlabels Hpod_meta_Hdeepown_labels_none.
      + finish_identity_false_without_labels set_meta_c set dq_set set_l
          Hset_l_not_null pod_meta_c pod dq_pod pod_l
          Hpod_l_not_null Hlabels Hpod_meta_Hdeepown_labels_none.
  }
  unfold pod_identity_matches in Hmatches.
  destruct (parse_member_name
    set.(StatefulSetV.ObjectMeta').(ObjectMetaV.Name')
    pod.(PodV.ObjectMeta').(ObjectMetaV.Name')) as [expected_ordinal|]
    eqn:Hparse; [|done].
  destruct pod.(PodV.ObjectMeta').(ObjectMetaV.Labels') as [labels|]
    eqn:Hlabels; [|done].
  simpl in Hmatches.
  pose proof Hmatches as Hidentity_matches.
  destruct Hmatches as
    (Hordinal_bound & Hnamespace & Hpod_name_label & Hpod_index_label).
  assert (Hmember : pod_has_int32_member_name
      set.(StatefulSetV.ObjectMeta').(ObjectMetaV.Name')
      pod.(PodV.ObjectMeta').(ObjectMetaV.Name')).
  { exists expected_ordinal. split; [done|].
    by apply parse_member_name_sound. }
  assert (Hmember_c : pod_has_int32_member_name
      set.(StatefulSetV.ObjectMeta').(ObjectMetaV.Name')
      (v1.ObjectMeta.Name' pod_meta_c)).
  { rewrite Hpod_meta_Hdeepown_name. exact Hmember. }
  pose proof (proj2
    (Hparent set.(StatefulSetV.ObjectMeta').(ObjectMetaV.Name')) Hmember_c) as
    (Hparent_eq & Hordinal_nonnegative & Hcanonical).
  assert (Hexpected_ordinal : expected_ordinal = sint.nat ordinal).
  { apply (desired_pod_name_inj
      set.(StatefulSetV.ObjectMeta').(ObjectMetaV.Name')).
    rewrite -(parse_member_name_sound _ _ _ Hparse).
    rewrite Hpod_meta_Hdeepown_name in Hcanonical.
    exact Hcanonical. }
  wp_if_destruct.
  2: { exfalso. word. }
  wp_if_destruct.
  2: { exfalso. apply n. by rewrite Hset_meta_Hdeepown_name. }
  wp_apply (wp_podName
    (v1.ObjectMeta.Name' set_meta_c) ordinal with "[]").
  { iPureIntro. exact Hordinal_nonnegative. }
  wp_if_destruct.
  2: {
    exfalso. apply n.
    unfold desired_pod_name in Hcanonical.
    rewrite -Hset_meta_Hdeepown_name in Hcanonical.
    exact Hcanonical.
  }
  wp_if_destruct.
  2: {
    exfalso. apply n.
    by rewrite Hpod_meta_Hdeepown_namespace Hset_meta_Hdeepown_namespace.
  }
  iDestruct "Hpod_meta_Hdeepown_labels_some" as (labels_c)
    "[Hpod_labels %Hlabels_c]".
  subst labels_c.
  wp_apply (wp_map_lookup1 with "Hpod_labels") as "Hpod_labels".
  rewrite Hpod_name_label /=.
  wp_if_destruct.
  2: { exfalso. apply n. by rewrite Hpod_meta_Hdeepown_name. }
  wp_apply (wp_map_lookup1 with "Hpod_labels") as "Hpod_labels".
  rewrite Hpod_index_label /=.
  wp_apply (wp_strconv_Itoa with "[]").
  { iSplit; first by iEval (rewrite is_pkg_init_unfold /=).
    iPureIntro. exact Hordinal_nonnegative. }
  wp_if_destruct.
  2: { exfalso. done. }
  iCombineNamed "Hset_meta_*" as "Hset_objectmeta".
  iAssert (ObjectMetaV.deepown set_meta_c
      set.(StatefulSetV.ObjectMeta') dq_set)
    with "[Hset_objectmeta]" as "Hset_objectmeta".
  { iNamed "Hset_objectmeta". iFrame. done. }
  iAssert (ObjectMetaV.deepown_l (StatefulSetV.objectmeta_ptr set_l)
      set.(StatefulSetV.ObjectMeta') dq_set)
    with "[Hset_objectmeta_field Hset_objectmeta]" as "Hset_objectmeta_l".
  { iExists set_meta_c. iFrame. }
  iPoseProof (StatefulSetV.deepown_l_restore _ _ _ Hset_l_not_null
    with "[$Hset_typemeta $Hset_objectmeta_l $Hset_spec_l $Hset_status_l]")
    as "Hset".
  iAssert (match pod.(PodV.ObjectMeta').(ObjectMetaV.Labels') with
      | Some vl => ∃ cl,
          v1.ObjectMeta.Labels' pod_meta_c ↦${dq_pod} cl ∗ ⌜ cl = vl ⌝
      | None => True
      end)%I with "[Hpod_labels]" as "Hpod_meta_Hdeepown_labels_some".
  { rewrite Hlabels. iExists labels. iFrame. done. }
  iCombineNamed "Hpod_meta_*" as "Hpod_objectmeta".
  iAssert (ObjectMetaV.deepown pod_meta_c pod.(PodV.ObjectMeta') dq_pod)
    with "[Hpod_objectmeta]" as "Hpod_objectmeta".
  { iNamed "Hpod_objectmeta". iFrame.
    repeat (iSplit; first (iPureIntro; done)).
    iSplit.
    { iPureIntro. rewrite Hlabels. exact Hpod_meta_Hdeepown_labels_none. }
    repeat (iSplit; first (iPureIntro; done)).
    all: iFrame "%". }
  iAssert (ObjectMetaV.deepown_l (PodV.objectmeta_ptr pod_l)
      pod.(PodV.ObjectMeta') dq_pod)
    with "[Hpod_objectmeta_field Hpod_objectmeta]" as "Hpod_objectmeta_l".
  { iExists pod_meta_c. iFrame. }
  iPoseProof (PodV.deepown_l_restore _ _ _ Hpod_l_not_null
    with "[$Hpod_typemeta $Hpod_objectmeta_l $Hpod_spec_l $Hpod_status_l]")
    as "Hpod".
  iApply ("HΦ" $! true).
  iFrame.
  iPureIntro. split; [|done].
  intros _.
  unfold pod_identity_matches.
  rewrite Hparse Hlabels.
  exact Hidentity_matches.
Qed.

End proof.
