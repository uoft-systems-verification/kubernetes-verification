From New.proof Require Import prelude empty_ffi.
From New.proof.string Require Export prefix_suffix.
From New.proof.kubernetes_model Require Export get index create delete.
From New.proof Require Export util.
From New.proof Require Export wp_helpers.
From New.proof.controllers Require Export common.
From New.proof.controllers.statefulset Require Export ordinal.
From New.proof.controllers.statefulset Require Export pod_predicates.
From New.proof.controllers.statefulset Require Export statefulset_init.
From New.proof.k8s_io.api.apps Require Export v1.
From New.proof.k8s_io.kubernetes.pkg Require Export controller.
From New.proof.k8s_io.apimachinery.pkg.runtime Require Export schema.
From New.proof.k8s_io.apimachinery.pkg.api Require Export errors.

Section proof.
Context `{hG: !heapGS Σ} `{!ffi_semantics _ _}.
Context {sem : go.Semantics}
  {package_sem : code.controllers.statefulset.statefulset.Assumptions}.
Collection W := sem + package_sem.
#[local] Instance base_common_sem : common.Assumptions | 100 :=
  code.controllers.statefulset.statefulset.import_common_Assumption.
#[local] Instance controller_sem : controller.Assumptions :=
  code.controllers.statefulset.statefulset.import_controller_Assumption.
#[local] Instance runtime_sem : code.k8s_io.apimachinery.pkg.runtime.runtime.Assumptions :=
  controller.import_runtime_Assumption.
#[local] Instance runtime_object_underlying_eq :
    runtime.Object ≤u runtime.Objectⁱᵐᵖˡ.
Proof using package_sem. apply _. Qed.
#[local] Instance meta_object_underlying_eq :
    meta_v1.Object ≤u meta_v1.Objectⁱᵐᵖˡ.
Proof using package_sem. apply _. Qed.
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


(* The pure effect of [updateIdentity] after [ordinalOf] has successfully
   recovered [ordinal] from the Pod name. *)
Definition update_identity (set : StatefulSetV.t) (pod : PodV.t)
    (ordinal : nat) : PodV.t :=
  let pod_name := desired_pod_name
    set.(StatefulSetV.ObjectMeta').(ObjectMetaV.Name') ordinal in
  let labels : gmap go_string go_string :=
    default ∅ pod.(PodV.ObjectMeta').(ObjectMetaV.Labels') in
  let labels :=
    <[pod_index_label := decimal_string ordinal]>
      (<[statefulset_pod_name_label := pod_name]> labels) in
  let object_meta :=
    pod.(PodV.ObjectMeta')
      <| ObjectMetaV.Name' := pod_name |>
      <| ObjectMetaV.Namespace' :=
          set.(StatefulSetV.ObjectMeta').(ObjectMetaV.Namespace') |>
      <| ObjectMetaV.Labels' := Some labels |> in
  let spec :=
    pod.(PodV.Spec')
      <| PodSpecV.Hostname' := pod_name |>
      <| PodSpecV.Subdomain' :=
          set.(StatefulSetV.Spec').(StatefulSetSpecV.ServiceName') |> in
  pod <| PodV.ObjectMeta' := object_meta |>
      <| PodV.Spec' := spec |>.

Lemma update_identity_identity_matches set pod ordinal :
  (ordinal <= go_int32_max_nat)%nat →
  pod_identity_matches set (update_identity set pod ordinal).
Proof.
  intros Hordinal.
  unfold pod_identity_matches, update_identity.
  cbn -[parse_member_name].
  rewrite (parse_member_name_complete
    set.(StatefulSetV.ObjectMeta').(ObjectMetaV.Name')
    (desired_pod_name
      set.(StatefulSetV.ObjectMeta').(ObjectMetaV.Name') ordinal)
    ordinal eq_refl).
  cbn.
  split_and!; try done.
  - rewrite lookup_insert_ne.
    + {
      unfold pod_index_label, statefulset_pod_name_label.
      intros Hlabels. inversion Hlabels.
    }
    + rewrite lookup_insert_eq. done.
  - rewrite lookup_insert_eq. done.
Qed.

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
  iPoseProof (StatefulSetV.deepown_l_split with "Hset") as
    "(%Hset_l_not_null & Hset_typemeta & Hset_objectmeta_l & Hset_spec_l & Hset_status_l)".
  iDestruct "Hset_objectmeta_l" as (set_meta_c)
    "[Hset_objectmeta_field Hset_objectmeta]".
  iNamedPrefix "Hset_objectmeta" "Hset_meta_".
  iDestruct "Hset_spec_l" as (set_spec_c) "[Hset_spec_field Hset_spec]".
  iNamedPrefix "Hset_spec" "Hset_spec_".
  iPoseProof (PodV.deepown_l_split with "Hpod") as
    "(%Hpod_l_not_null & Hpod_typemeta & Hpod_objectmeta_l & Hpod_spec_l & Hpod_status_l)".
  iDestruct "Hpod_objectmeta_l" as (pod_meta_c)
    "[Hpod_objectmeta_field Hpod_objectmeta]".
  iNamedPrefix "Hpod_objectmeta" "Hpod_meta_".
  iDestruct "Hpod_spec_l" as (pod_spec_c) "[Hpod_spec_field Hpod_spec]".
  iNamedPrefix "Hpod_spec" "Hpod_spec_".
  Ltac restore_identity_objects set_meta_c set dq_set set_l
      set_spec_c Hset_l_not_null pod_meta_c pod dq_pod pod_l pod_spec_c
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
    iCombineNamed "Hset_spec_H*" as "Hset_spec";
    iAssert (StatefulSetSpecV.deepown set_spec_c
        set.(StatefulSetV.Spec') dq_set)
      with "[Hset_spec]" as "Hset_spec";
    [ iNamed "Hset_spec"; iFrame; done | ];
    iAssert (StatefulSetSpecV.deepown_l (StatefulSetV.spec_ptr set_l)
        set.(StatefulSetV.Spec') dq_set)
      with "[Hset_spec_field Hset_spec]" as "Hset_spec_l";
    [ iExists set_spec_c; iFrame | ];
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
    iCombineNamed "Hpod_spec_H*" as "Hpod_spec";
    iAssert (PodSpecV.deepown pod_spec_c pod.(PodV.Spec') dq_pod)
      with "[Hpod_spec]" as "Hpod_spec";
    [ iNamed "Hpod_spec"; iFrame; done | ];
    iAssert (PodSpecV.deepown_l (PodV.spec_ptr pod_l)
        pod.(PodV.Spec') dq_pod)
      with "[Hpod_spec_field Hpod_spec]" as "Hpod_spec_l";
    [ iExists pod_spec_c; iFrame | ];
    iPoseProof (PodV.deepown_l_restore _ _ _ Hpod_l_not_null
      with "[$Hpod_typemeta $Hpod_objectmeta_l $Hpod_spec_l $Hpod_status_l]")
      as "Hpod".
  Ltac finish_identity_false set_meta_c set dq_set set_l
      set_spec_c Hset_l_not_null pod_meta_c pod dq_pod pod_l pod_spec_c
      Hpod_l_not_null :=
    restore_identity_objects set_meta_c set dq_set set_l set_spec_c
      Hset_l_not_null pod_meta_c pod dq_pod pod_l pod_spec_c Hpod_l_not_null;
    iApply ("HΦ" $! false);
    iFrame;
    iPureIntro;
    split; [done | intros; contradiction].
  Ltac finish_identity_false_with_labels set_meta_c set dq_set set_l
      set_spec_c Hset_l_not_null pod_meta_c pod dq_pod pod_l pod_spec_c
      Hpod_l_not_null labels Hlabels Hlabels_none Hmanagedfields_none :=
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
    iCombineNamed "Hset_spec_H*" as "Hset_spec";
    iAssert (StatefulSetSpecV.deepown set_spec_c set.(StatefulSetV.Spec') dq_set)
      with "[Hset_spec]" as "Hset_spec";
    [ iNamed "Hset_spec"; iFrame; done | ];
    iAssert (StatefulSetSpecV.deepown_l (StatefulSetV.spec_ptr set_l)
        set.(StatefulSetV.Spec') dq_set)
      with "[Hset_spec_field Hset_spec]" as "Hset_spec_l";
    [ iExists set_spec_c; iFrame | ];
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
      repeat (iSplit; first (iPureIntro; done));
      iPureIntro; exact Hmanagedfields_none
    | ];
    iAssert (ObjectMetaV.deepown_l (PodV.objectmeta_ptr pod_l)
        pod.(PodV.ObjectMeta') dq_pod)
      with "[Hpod_objectmeta_field Hpod_objectmeta]" as "Hpod_objectmeta_l";
    [ iExists pod_meta_c; iFrame | ];
    iCombineNamed "Hpod_spec_H*" as "Hpod_spec";
    iAssert (PodSpecV.deepown pod_spec_c pod.(PodV.Spec') dq_pod)
      with "[Hpod_spec]" as "Hpod_spec";
    [ iNamed "Hpod_spec"; iFrame; done | ];
    iAssert (PodSpecV.deepown_l (PodV.spec_ptr pod_l) pod.(PodV.Spec') dq_pod)
      with "[Hpod_spec_field Hpod_spec]" as "Hpod_spec_l";
    [ iExists pod_spec_c; iFrame | ];
    iPoseProof (PodV.deepown_l_restore _ _ _ Hpod_l_not_null
      with "[$Hpod_typemeta $Hpod_objectmeta_l $Hpod_spec_l $Hpod_status_l]")
      as "Hpod";
    iApply ("HΦ" $! false);
    iFrame;
    iPureIntro;
    split; [done | intros; contradiction].
  Ltac finish_identity_false_without_labels set_meta_c set dq_set set_l
      set_spec_c Hset_l_not_null pod_meta_c pod dq_pod pod_l pod_spec_c
      Hpod_l_not_null Hlabels Hlabels_none Hmanagedfields_none :=
    iCombineNamed "Hset_meta_*" as "Hset_objectmeta";
    iAssert (ObjectMetaV.deepown set_meta_c
        set.(StatefulSetV.ObjectMeta') dq_set)
      with "[Hset_objectmeta]" as "Hset_objectmeta";
    [ iNamed "Hset_objectmeta"; iFrame; done | ];
    iAssert (ObjectMetaV.deepown_l (StatefulSetV.objectmeta_ptr set_l)
        set.(StatefulSetV.ObjectMeta') dq_set)
      with "[Hset_objectmeta_field Hset_objectmeta]" as "Hset_objectmeta_l";
    [ iExists set_meta_c; iFrame | ];
    iCombineNamed "Hset_spec_H*" as "Hset_spec";
    iAssert (StatefulSetSpecV.deepown set_spec_c set.(StatefulSetV.Spec') dq_set)
      with "[Hset_spec]" as "Hset_spec";
    [ iNamed "Hset_spec"; iFrame; done | ];
    iAssert (StatefulSetSpecV.deepown_l (StatefulSetV.spec_ptr set_l)
        set.(StatefulSetV.Spec') dq_set)
      with "[Hset_spec_field Hset_spec]" as "Hset_spec_l";
    [ iExists set_spec_c; iFrame | ];
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
      do 3 (iSplit; first (iPureIntro; assumption));
      iPureIntro; exact Hmanagedfields_none
    | ];
    iAssert (ObjectMetaV.deepown_l (PodV.objectmeta_ptr pod_l)
        pod.(PodV.ObjectMeta') dq_pod)
      with "[Hpod_objectmeta_field Hpod_objectmeta]" as "Hpod_objectmeta_l";
    [ iExists pod_meta_c; iFrame | ];
    iCombineNamed "Hpod_spec_H*" as "Hpod_spec";
    iAssert (PodSpecV.deepown pod_spec_c pod.(PodV.Spec') dq_pod)
      with "[Hpod_spec]" as "Hpod_spec";
    [ iNamed "Hpod_spec"; iFrame; done | ];
    iAssert (PodSpecV.deepown_l (PodV.spec_ptr pod_l) pod.(PodV.Spec') dq_pod)
      with "[Hpod_spec_field Hpod_spec]" as "Hpod_spec_l";
    [ iExists pod_spec_c; iFrame | ];
    iPoseProof (PodV.deepown_l_restore _ _ _ Hpod_l_not_null
      with "[$Hpod_typemeta $Hpod_objectmeta_l $Hpod_spec_l $Hpod_status_l]")
      as "Hpod";
    iApply ("HΦ" $! false);
    iFrame;
    iPureIntro;
    split; [done | intros; contradiction].
  wp_auto.
  wp_apply (wp_parentNameAndOrdinal with "[]").
  { iPureIntro. rewrite Hpod_meta_Hdeepown_name. exact Hpod_name_len. }
  iIntros (parent ordinal) "%Hparent".
  wp_auto.
  destruct (decide (pod_identity_matches set pod)) as [Hmatches|Hnot_matches].
  2: {
    wp_if_destruct.
    2: { finish_identity_false set_meta_c set dq_set set_l set_spec_c
      Hset_l_not_null pod_meta_c pod dq_pod pod_l pod_spec_c Hpod_l_not_null. }
    wp_if_destruct.
    2: { finish_identity_false set_meta_c set dq_set set_l set_spec_c
      Hset_l_not_null pod_meta_c pod dq_pod pod_l pod_spec_c Hpod_l_not_null. }
    wp_apply (wp_podName (v1.ObjectMeta.Name' set_meta_c) ordinal with "[]").
    { iPureIntro. word. }
    wp_if_destruct.
    2: { finish_identity_false set_meta_c set dq_set set_l set_spec_c
      Hset_l_not_null pod_meta_c pod dq_pod pod_l pod_spec_c Hpod_l_not_null. }
    wp_if_destruct.
    2: { finish_identity_false set_meta_c set dq_set set_l set_spec_c
      Hset_l_not_null pod_meta_c pod dq_pod pod_l pod_spec_c Hpod_l_not_null. }
    wp_if_destruct.
    2: { finish_identity_false set_meta_c set dq_set set_l set_spec_c
      Hset_l_not_null pod_meta_c pod dq_pod pod_l pod_spec_c Hpod_l_not_null. }
    wp_if_destruct.
    2: { finish_identity_false set_meta_c set dq_set set_l set_spec_c
      Hset_l_not_null pod_meta_c pod dq_pod pod_l pod_spec_c Hpod_l_not_null. }
    destruct pod.(PodV.ObjectMeta').(ObjectMetaV.Labels') as [labels|]
      eqn:Hlabels.
    - iDestruct "Hpod_meta_Hdeepown_labels_some" as (labels_c)
        "[Hpod_labels %Hlabels_c]".
      subst labels_c.
      wp_apply (wp_map_lookup1 with "Hpod_labels") as "Hpod_labels".
      wp_if_destruct.
      2: {
        finish_identity_false_with_labels set_meta_c set dq_set set_l
          set_spec_c Hset_l_not_null pod_meta_c pod dq_pod pod_l pod_spec_c
          Hpod_l_not_null labels Hlabels Hpod_meta_Hdeepown_labels_none
          Hpod_meta_Hdeepown_managedfields_none.
      }
      wp_apply (wp_map_lookup1 with "Hpod_labels") as "Hpod_labels".
      wp_apply (wp_strconv_Itoa with "[]").
      { iSplit; first by iEval (rewrite is_pkg_init_unfold /=).
        iPureIntro. word. }
      wp_if_destruct.
      2: {
        finish_identity_false_with_labels set_meta_c set dq_set set_l
          set_spec_c Hset_l_not_null pod_meta_c pod dq_pod pod_l pod_spec_c
          Hpod_l_not_null labels Hlabels Hpod_meta_Hdeepown_labels_none
          Hpod_meta_Hdeepown_managedfields_none.
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
        - simpl in e3. f_equal.
          rewrite -Hpod_meta_Hdeepown_name. exact e3.
        - simpl in e3. exfalso. apply Hpod_name_nonempty. by rewrite -e3. }
      assert (Hpod_index_lookup :
          labels !! pod_index_label = Some (decimal_string (sint.nat ordinal))).
      { unfold pod_index_label.
        destruct (labels !! "apps.kubernetes.io/pod-index"%go) as [label|]
          eqn:Hlookup.
        - simpl in e4. by f_equal.
        - simpl in e4.
          pose proof (parse_decimal_string_decimal_string
            (sint.nat ordinal)) as Hdecimal.
          rewrite -e4 in Hdecimal. done. }
      unfold pod_identity_matches.
      rewrite Hparse Hlabels.
      repeat split; try done.
      + by rewrite -Hpod_meta_Hdeepown_namespace
          -Hset_meta_Hdeepown_namespace.
      + by rewrite -Hpod_spec_Hdeepown_hostname
          -Hpod_meta_Hdeepown_name.
      + by rewrite -Hpod_spec_Hdeepown_subdomain
          -Hset_spec_Hdeepown_servicename.
    - assert (Hlabels_nil : v1.ObjectMeta.Labels' pod_meta_c = null).
      { apply Hpod_meta_Hdeepown_labels_none. reflexivity. }
      rewrite Hlabels_nil.
      wp_auto.
      wp_if_destruct.
      + rewrite Hlabels_nil.
        wp_auto.
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
            set_spec_c Hset_l_not_null pod_meta_c pod dq_pod pod_l pod_spec_c
            Hpod_l_not_null Hlabels Hpod_meta_Hdeepown_labels_none
            Hpod_meta_Hdeepown_managedfields_none.
      + finish_identity_false_without_labels set_meta_c set dq_set set_l
          set_spec_c Hset_l_not_null pod_meta_c pod dq_pod pod_l pod_spec_c
          Hpod_l_not_null Hlabels Hpod_meta_Hdeepown_labels_none
          Hpod_meta_Hdeepown_managedfields_none.
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
    (Hordinal_bound & Hnamespace & Hhostname & Hsubdomain &
      Hpod_name_label & Hpod_index_label).
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
  wp_if_destruct.
  2: {
    exfalso. apply n.
    by rewrite Hpod_spec_Hdeepown_hostname Hpod_meta_Hdeepown_name.
  }
  wp_if_destruct.
  2: {
    exfalso. apply n.
    by rewrite Hpod_spec_Hdeepown_subdomain Hset_spec_Hdeepown_servicename.
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
  iCombineNamed "Hset_spec_H*" as "Hset_spec".
  iAssert (StatefulSetSpecV.deepown set_spec_c
      set.(StatefulSetV.Spec') dq_set)
    with "[Hset_spec]" as "Hset_spec".
  { iNamed "Hset_spec". iFrame. done. }
  iAssert (StatefulSetSpecV.deepown_l (StatefulSetV.spec_ptr set_l)
      set.(StatefulSetV.Spec') dq_set)
    with "[Hset_spec_field Hset_spec]" as "Hset_spec_l".
  { iExists set_spec_c. iFrame. }
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
    iPureIntro. exact Hpod_meta_Hdeepown_managedfields_none. }
  iAssert (ObjectMetaV.deepown_l (PodV.objectmeta_ptr pod_l)
      pod.(PodV.ObjectMeta') dq_pod)
    with "[Hpod_objectmeta_field Hpod_objectmeta]" as "Hpod_objectmeta_l".
  { iExists pod_meta_c. iFrame. }
  iCombineNamed "Hpod_spec_H*" as "Hpod_spec".
  iAssert (PodSpecV.deepown pod_spec_c pod.(PodV.Spec') dq_pod)
    with "[Hpod_spec]" as "Hpod_spec".
  { iNamed "Hpod_spec". iFrame. done. }
  iAssert (PodSpecV.deepown_l (PodV.spec_ptr pod_l) pod.(PodV.Spec') dq_pod)
    with "[Hpod_spec_field Hpod_spec]" as "Hpod_spec_l".
  { iExists pod_spec_c. iFrame. }
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

(* The ordinal and name preconditions exclude the failure result (-1) from
   ordinalOf. The helper mutates the Pod in place, so it requires full Pod
   ownership and produces exactly the pure [update_identity] transformation. *)
Lemma wp_updateIdentity set_l pod_l (set : StatefulSetV.t) (pod : PodV.t)
    (ordinal : nat) dq_set :
  {{{ "Hset" ∷ StatefulSetV.deepown_l set_l set dq_set ∗
      "Hpod" ∷ PodV.deepown_l pod_l pod 1 ∗
      "%Hpod_name" ∷
        ⌜ pod.(PodV.ObjectMeta').(ObjectMetaV.Name') = desired_pod_name
            set.(StatefulSetV.ObjectMeta').(ObjectMetaV.Name') ordinal ⌝ ∗
      "%Hordinal_int32" ∷ ⌜ (ordinal <= go_int32_max_nat)%nat ⌝ ∗
      "%Hpod_name_len" ∷ ⌜ Z.of_nat (length pod.(PodV.ObjectMeta').(ObjectMetaV.Name')) <= go_int_max ⌝
  }}}
    @! statefulset.updateIdentity #set_l #pod_l
  {{{ RET #();
      "Hset" ∷ StatefulSetV.deepown_l set_l set dq_set ∗
      "Hpod" ∷ PodV.deepown_l pod_l (update_identity set pod ordinal) 1 ∗
      "%Hidentity_matches" ∷
        ⌜ pod_identity_matches set (update_identity set pod ordinal) ⌝
  }}}.
Proof.
  wp_start as "H". iNamed "H".
  iPoseProof (StatefulSetV.deepown_l_split with "Hset") as
    "(%Hset_l_not_null & Hset_typemeta & Hset_objectmeta_l & Hset_spec_l & Hset_status_l)".
  iDestruct "Hset_objectmeta_l" as (set_meta_c)
    "[Hset_objectmeta_field Hset_objectmeta]".
  iNamedPrefix "Hset_objectmeta" "Hset_meta_".
  iDestruct "Hset_spec_l" as (set_spec_c) "[Hset_spec_field Hset_spec]".
  iNamedPrefix "Hset_spec" "Hset_spec_".
  iPoseProof (PodV.deepown_l_split with "Hpod") as
    "(%Hpod_l_not_null & Hpod_typemeta & Hpod_objectmeta_l & Hpod_spec_l & Hpod_status_l)".
  iDestruct "Hpod_objectmeta_l" as (pod_meta_c)
    "[Hpod_objectmeta_field Hpod_objectmeta]".
  iNamedPrefix "Hpod_objectmeta" "Hpod_meta_".
  iDestruct "Hpod_spec_l" as (pod_spec_c) "[Hpod_spec_field Hpod_spec]".
  iNamedPrefix "Hpod_spec" "Hpod_spec_".
  wp_auto.
  wp_apply (wp_ordinalOf
    (v1.ObjectMeta.Name' pod_meta_c) ordinal
    (v1.ObjectMeta.Name' set_meta_c) with "[]").
  { iPureIntro. split.
    - rewrite Hpod_meta_Hdeepown_name. exact Hpod_name_len.
    - split; first exact Hordinal_int32.
      rewrite Hpod_meta_Hdeepown_name Hset_meta_Hdeepown_name.
      exact Hpod_name. }
  iIntros (ordinal_ret) "%Hordinal_ret".
  wp_auto.
  wp_apply (wp_podName
    (v1.ObjectMeta.Name' set_meta_c) ordinal_ret with "[]").
  { iPureIntro. rewrite Hordinal_ret. lia. }
  wp_pures.
  assert (Hordinal_ret_nat : sint.nat ordinal_ret = ordinal) by word.
  subst ordinal.
  destruct pod.(PodV.ObjectMeta').(ObjectMetaV.Labels') as [labels|]
    eqn:Hlabels.
  2: {
    assert (Hlabels_nil : v1.ObjectMeta.Labels' pod_meta_c = map.nil).
    { apply Hpod_meta_Hdeepown_labels_none. reflexivity. }
    rewrite Hlabels_nil.
    wp_pures.
    wp_apply wp_map_make1 as "%labels_l Hpod_labels".
    wp_pures.
    wp_apply (wp_map_insert go.string with "Hpod_labels") as "Hpod_labels".
    wp_pures.
    wp_apply (wp_strconv_Itoa with "[]").
    { iSplit; first by iEval (rewrite is_pkg_init_unfold /=).
      iPureIntro. rewrite Hordinal_ret. lia. }
    wp_apply (wp_map_insert go.string with "Hpod_labels") as "Hpod_labels".
    wp_pures.
    iPoseProof (own_map_not_nil with "Hpod_labels") as "%Hlabels_not_nil".
    iCombineNamed "Hset_meta_*" as "Hset_objectmeta".
    iAssert (ObjectMetaV.deepown set_meta_c
        set.(StatefulSetV.ObjectMeta') dq_set)
      with "[Hset_objectmeta]" as "Hset_objectmeta".
    { iNamed "Hset_objectmeta". iFrame. done. }
    iAssert (ObjectMetaV.deepown_l (StatefulSetV.objectmeta_ptr set_l)
        set.(StatefulSetV.ObjectMeta') dq_set)
      with "[Hset_objectmeta_field Hset_objectmeta]" as "Hset_objectmeta_l".
    { iExists set_meta_c. iFrame. }
    iCombineNamed "Hset_spec_H*" as "Hset_spec".
    iAssert (StatefulSetSpecV.deepown set_spec_c
        set.(StatefulSetV.Spec') dq_set)
      with "[Hset_spec]" as "Hset_spec".
    { iNamed "Hset_spec". iFrame. done. }
    iAssert (StatefulSetSpecV.deepown_l (StatefulSetV.spec_ptr set_l)
        set.(StatefulSetV.Spec') dq_set)
      with "[Hset_spec_field Hset_spec]" as "Hset_spec_l".
    { iExists set_spec_c. iFrame. }
    iPoseProof (StatefulSetV.deepown_l_restore _ _ _ Hset_l_not_null
      with "[$Hset_typemeta $Hset_objectmeta_l $Hset_spec_l $Hset_status_l]")
      as "Hset".
    iApply "HΦ".
    iFrame "Hset".
    iSplitL.
    2: { iPureIntro. apply update_identity_identity_matches.
         exact Hordinal_int32. }
    unfold update_identity.
    cbn.
    iEval (rewrite Hlabels /=).
    assert (Hpod_name_c :
        v1.ObjectMeta.Name' set_meta_c ++ "-"%go ++
            decimal_string (sint.nat ordinal_ret) =
        desired_pod_name
          set.(StatefulSetV.ObjectMeta').(ObjectMetaV.Name')
          (sint.nat ordinal_ret)).
    { unfold desired_pod_name.
      by rewrite Hset_meta_Hdeepown_name. }
    iEval (rewrite Hpod_name_c Hset_meta_Hdeepown_namespace) in
      "Hpod_objectmeta_field".
    iEval (rewrite Hpod_name_c Hset_spec_Hdeepown_servicename) in
      "Hpod_spec_field".
    iEval (rewrite Hpod_name_c) in "Hpod_labels".
    iCombineNamed "Hpod_meta_*" as "Hpod_objectmeta_old".
    iAssert (ObjectMetaV.deepown
        (pod_meta_c <| v1.ObjectMeta.Name' :=
            desired_pod_name
              set.(StatefulSetV.ObjectMeta').(ObjectMetaV.Name')
              (sint.nat ordinal_ret) |> <|
          v1.ObjectMeta.Namespace' :=
            set.(StatefulSetV.ObjectMeta').(ObjectMetaV.Namespace') |> <|
          v1.ObjectMeta.Labels' := labels_l |>)
        (pod.(PodV.ObjectMeta') <| ObjectMetaV.Name' :=
            desired_pod_name
              set.(StatefulSetV.ObjectMeta').(ObjectMetaV.Name')
              (sint.nat ordinal_ret) |> <|
          ObjectMetaV.Namespace' :=
            set.(StatefulSetV.ObjectMeta').(ObjectMetaV.Namespace') |> <|
          ObjectMetaV.Labels' := Some
            (<[pod_index_label := decimal_string (sint.nat ordinal_ret)]>
              (<[statefulset_pod_name_label := desired_pod_name
                set.(StatefulSetV.ObjectMeta').(ObjectMetaV.Name')
                (sint.nat ordinal_ret)]> (∅ : gmap go_string go_string))) |>) 1)
      with "[Hpod_labels Hpod_objectmeta_old]" as "Hpod_objectmeta".
    { iNamed "Hpod_objectmeta_old".
      rewrite /ObjectMetaV.deepown /=.
      iFrame.
      repeat (iSplit; first (iPureIntro; simpl; try done)).
      - apply Hpod_meta_Hdeepown_managedfields_none.
      - iPureIntro. apply Hpod_meta_Hdeepown_managedfields_none.
    }
    iAssert (ObjectMetaV.deepown_l (PodV.objectmeta_ptr pod_l)
        (pod.(PodV.ObjectMeta') <| ObjectMetaV.Name' :=
            desired_pod_name
              set.(StatefulSetV.ObjectMeta').(ObjectMetaV.Name')
              (sint.nat ordinal_ret) |> <|
          ObjectMetaV.Namespace' :=
            set.(StatefulSetV.ObjectMeta').(ObjectMetaV.Namespace') |> <|
          ObjectMetaV.Labels' := Some
            (<[pod_index_label := decimal_string (sint.nat ordinal_ret)]>
              (<[statefulset_pod_name_label := desired_pod_name
                set.(StatefulSetV.ObjectMeta').(ObjectMetaV.Name')
                (sint.nat ordinal_ret)]> (∅ : gmap go_string go_string))) |>) 1)
      with "[Hpod_objectmeta_field Hpod_objectmeta]" as "Hpod_objectmeta_l".
    { iExists (pod_meta_c <| v1.ObjectMeta.Name' :=
          desired_pod_name
            set.(StatefulSetV.ObjectMeta').(ObjectMetaV.Name')
            (sint.nat ordinal_ret) |> <|
        v1.ObjectMeta.Namespace' :=
          set.(StatefulSetV.ObjectMeta').(ObjectMetaV.Namespace') |> <|
        v1.ObjectMeta.Labels' := labels_l |>).
      iFrame. }
    iAssert (PodSpecV.deepown
        (pod_spec_c <| v1.PodSpec.Hostname' :=
            desired_pod_name
              set.(StatefulSetV.ObjectMeta').(ObjectMetaV.Name')
              (sint.nat ordinal_ret) |> <|
          v1.PodSpec.Subdomain' :=
            set.(StatefulSetV.Spec').(StatefulSetSpecV.ServiceName') |>)
        (pod.(PodV.Spec') <| PodSpecV.Hostname' :=
            desired_pod_name
              set.(StatefulSetV.ObjectMeta').(ObjectMetaV.Name')
              (sint.nat ordinal_ret) |> <|
          PodSpecV.Subdomain' :=
            set.(StatefulSetV.Spec').(StatefulSetSpecV.ServiceName') |>) 1)
      with "[Hpod_spec_Hdeepown_volumes]" as "Hpod_spec".
    { rewrite /PodSpecV.deepown /=. iFrame. done. }
    iAssert (PodSpecV.deepown_l (PodV.spec_ptr pod_l)
        (pod.(PodV.Spec') <| PodSpecV.Hostname' :=
            desired_pod_name
              set.(StatefulSetV.ObjectMeta').(ObjectMetaV.Name')
              (sint.nat ordinal_ret) |> <|
          PodSpecV.Subdomain' :=
            set.(StatefulSetV.Spec').(StatefulSetSpecV.ServiceName') |>) 1)
      with "[Hpod_spec_field Hpod_spec]" as "Hpod_spec_l".
    { iExists (pod_spec_c <| v1.PodSpec.Hostname' :=
          desired_pod_name
            set.(StatefulSetV.ObjectMeta').(ObjectMetaV.Name')
            (sint.nat ordinal_ret) |> <|
        v1.PodSpec.Subdomain' :=
          set.(StatefulSetV.Spec').(StatefulSetSpecV.ServiceName') |>).
      iFrame. }
    iApply (PodV.deepown_l_restore _ _ _ Hpod_l_not_null).
    iFrame.
  }
  iDestruct "Hpod_meta_Hdeepown_labels_some" as (labels_l)
    "[Hpod_labels %Hlabels_l]".
  subst labels_l.
  iPoseProof (own_map_not_nil with "Hpod_labels") as "%Hlabels_not_nil".
  wp_if_destruct.
  { exfalso. done. }
  wp_pures.
  wp_apply (wp_map_insert go.string with "Hpod_labels") as "Hpod_labels".
  wp_pures.
  wp_apply (wp_strconv_Itoa with "[]").
  { iSplit; first by iEval (rewrite is_pkg_init_unfold /=).
    iPureIntro. rewrite Hordinal_ret. lia. }
  wp_apply (wp_map_insert go.string with "Hpod_labels") as "Hpod_labels".
  wp_pures.
  iCombineNamed "Hset_meta_*" as "Hset_objectmeta".
  iAssert (ObjectMetaV.deepown set_meta_c
      set.(StatefulSetV.ObjectMeta') dq_set)
    with "[Hset_objectmeta]" as "Hset_objectmeta".
  { iNamed "Hset_objectmeta". iFrame. done. }
  iAssert (ObjectMetaV.deepown_l (StatefulSetV.objectmeta_ptr set_l)
      set.(StatefulSetV.ObjectMeta') dq_set)
    with "[Hset_objectmeta_field Hset_objectmeta]" as "Hset_objectmeta_l".
  { iExists set_meta_c. iFrame. }
  iCombineNamed "Hset_spec_H*" as "Hset_spec".
  iAssert (StatefulSetSpecV.deepown set_spec_c
      set.(StatefulSetV.Spec') dq_set)
    with "[Hset_spec]" as "Hset_spec".
  { iNamed "Hset_spec". iFrame. done. }
  iAssert (StatefulSetSpecV.deepown_l (StatefulSetV.spec_ptr set_l)
      set.(StatefulSetV.Spec') dq_set)
    with "[Hset_spec_field Hset_spec]" as "Hset_spec_l".
  { iExists set_spec_c. iFrame. }
  iPoseProof (StatefulSetV.deepown_l_restore _ _ _ Hset_l_not_null
    with "[$Hset_typemeta $Hset_objectmeta_l $Hset_spec_l $Hset_status_l]")
    as "Hset".
  iApply "HΦ".
  iFrame "Hset".
  iSplitL.
  2: { iPureIntro. apply update_identity_identity_matches.
       exact Hordinal_int32. }
  unfold update_identity.
  cbn.
  iEval (rewrite Hlabels /=).
  assert (Hpod_name_c :
      v1.ObjectMeta.Name' set_meta_c ++ "-"%go ++
          decimal_string (sint.nat ordinal_ret) =
      desired_pod_name
        set.(StatefulSetV.ObjectMeta').(ObjectMetaV.Name')
        (sint.nat ordinal_ret)).
  { unfold desired_pod_name.
    by rewrite Hset_meta_Hdeepown_name. }
  iEval (rewrite Hpod_name_c Hset_meta_Hdeepown_namespace) in
    "Hpod_objectmeta_field".
  iEval (rewrite Hpod_name_c Hset_spec_Hdeepown_servicename) in
    "Hpod_spec_field".
  iEval (rewrite Hpod_name_c) in "Hpod_labels".
  iCombineNamed "Hpod_meta_*" as "Hpod_objectmeta_old".
  iAssert (ObjectMetaV.deepown
      (pod_meta_c <| v1.ObjectMeta.Name' :=
          desired_pod_name
            set.(StatefulSetV.ObjectMeta').(ObjectMetaV.Name')
            (sint.nat ordinal_ret) |> <|
        v1.ObjectMeta.Namespace' :=
          set.(StatefulSetV.ObjectMeta').(ObjectMetaV.Namespace') |>)
      (pod.(PodV.ObjectMeta') <| ObjectMetaV.Name' :=
          desired_pod_name
            set.(StatefulSetV.ObjectMeta').(ObjectMetaV.Name')
            (sint.nat ordinal_ret) |> <|
        ObjectMetaV.Namespace' :=
          set.(StatefulSetV.ObjectMeta').(ObjectMetaV.Namespace') |> <|
        ObjectMetaV.Labels' := Some
          (<[pod_index_label := decimal_string (sint.nat ordinal_ret)]>
            (<[statefulset_pod_name_label := desired_pod_name
              set.(StatefulSetV.ObjectMeta').(ObjectMetaV.Name')
              (sint.nat ordinal_ret)]> labels)) |>) 1)
    with "[Hpod_labels Hpod_objectmeta_old]" as "Hpod_objectmeta".
  { iNamed "Hpod_objectmeta_old".
    rewrite /ObjectMetaV.deepown /=.
    iFrame.
    repeat (iSplit; first (iPureIntro; simpl; try done)).
    - apply Hpod_meta_Hdeepown_managedfields_none.
    - iPureIntro. apply Hpod_meta_Hdeepown_managedfields_none.
  }
  iAssert (ObjectMetaV.deepown_l (PodV.objectmeta_ptr pod_l)
      (pod.(PodV.ObjectMeta') <| ObjectMetaV.Name' :=
          desired_pod_name
            set.(StatefulSetV.ObjectMeta').(ObjectMetaV.Name')
            (sint.nat ordinal_ret) |> <|
        ObjectMetaV.Namespace' :=
          set.(StatefulSetV.ObjectMeta').(ObjectMetaV.Namespace') |> <|
        ObjectMetaV.Labels' := Some
          (<[pod_index_label := decimal_string (sint.nat ordinal_ret)]>
            (<[statefulset_pod_name_label := desired_pod_name
              set.(StatefulSetV.ObjectMeta').(ObjectMetaV.Name')
              (sint.nat ordinal_ret)]> labels)) |>) 1)
    with "[Hpod_objectmeta_field Hpod_objectmeta]" as "Hpod_objectmeta_l".
  { iExists (pod_meta_c <| v1.ObjectMeta.Name' :=
        desired_pod_name
          set.(StatefulSetV.ObjectMeta').(ObjectMetaV.Name')
          (sint.nat ordinal_ret) |> <|
      v1.ObjectMeta.Namespace' :=
        set.(StatefulSetV.ObjectMeta').(ObjectMetaV.Namespace') |>).
    iFrame. }
  iAssert (PodSpecV.deepown
      (pod_spec_c <| v1.PodSpec.Hostname' :=
          desired_pod_name
            set.(StatefulSetV.ObjectMeta').(ObjectMetaV.Name')
            (sint.nat ordinal_ret) |> <|
        v1.PodSpec.Subdomain' :=
          set.(StatefulSetV.Spec').(StatefulSetSpecV.ServiceName') |>)
      (pod.(PodV.Spec') <| PodSpecV.Hostname' :=
          desired_pod_name
            set.(StatefulSetV.ObjectMeta').(ObjectMetaV.Name')
            (sint.nat ordinal_ret) |> <|
        PodSpecV.Subdomain' :=
          set.(StatefulSetV.Spec').(StatefulSetSpecV.ServiceName') |>) 1)
    with "[Hpod_spec_Hdeepown_volumes]" as "Hpod_spec".
  { rewrite /PodSpecV.deepown /=. iFrame. done. }
  iAssert (PodSpecV.deepown_l (PodV.spec_ptr pod_l)
      (pod.(PodV.Spec') <| PodSpecV.Hostname' :=
          desired_pod_name
            set.(StatefulSetV.ObjectMeta').(ObjectMetaV.Name')
            (sint.nat ordinal_ret) |> <|
        PodSpecV.Subdomain' :=
          set.(StatefulSetV.Spec').(StatefulSetSpecV.ServiceName') |>) 1)
    with "[Hpod_spec_field Hpod_spec]" as "Hpod_spec_l".
  { iExists (pod_spec_c <| v1.PodSpec.Hostname' :=
        desired_pod_name
          set.(StatefulSetV.ObjectMeta').(ObjectMetaV.Name')
          (sint.nat ordinal_ret) |> <|
      v1.PodSpec.Subdomain' :=
        set.(StatefulSetV.Spec').(StatefulSetSpecV.ServiceName') |>).
    iFrame. }
  iApply (PodV.deepown_l_restore _ _ _ Hpod_l_not_null).
  iFrame.
  Unshelve. all: apply _.
Qed.

End proof.
