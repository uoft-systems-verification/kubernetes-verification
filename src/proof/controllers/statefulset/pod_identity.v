From New.proof Require Import wp_keep.
From New.proof.controllers.statefulset Require Export pod_predicates.
From New.proof.controllers.statefulset Require Export ordinal.
From New.proof.controllers.statefulset Require Export pod_identity_matches.

Local Transparent ObjectMetaV.deepown ObjectMetaView.ObjectMetaV.deepown.


(* Keep untouched specifications opaque during metadata-only reasoning. *)
Local Opaque StatefulSetSpecV.deepown StatefulSetView.StatefulSetSpecV.deepown.
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
  pod <| PodV.ObjectMeta' := object_meta |>.

(* Creation-time identity initialization additionally sets the two immutable
   PodSpec fields omitted by [update_identity]. *)
Definition init_identity (set : StatefulSetV.t) (pod : PodV.t)
    (ordinal : nat) : PodV.t :=
  let pod := update_identity set pod ordinal in
  let spec :=
    pod.(PodV.Spec')
      <| PodSpecV.Hostname' :=
          pod.(PodV.ObjectMeta').(ObjectMetaV.Name') |>
      <| PodSpecV.Subdomain' :=
          set.(StatefulSetV.Spec').(StatefulSetSpecV.ServiceName') |> in
  pod <| PodV.Spec' := spec |>.

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
  iPoseProof (PodV.deepown_l_split with "Hpod") as
    "(%Hpod_l_not_null & Hpod_typemeta & Hpod_objectmeta_l & Hpod_spec_l & Hpod_status_l)".
  iDestruct "Hpod_objectmeta_l" as (pod_meta_c)
    "[Hpod_objectmeta_field Hpod_objectmeta]".
  iNamedPrefix "Hpod_objectmeta" "Hpod_meta_".
  wp_auto_keep.
  wp_apply (wp_ordinalOf
    (v1.ObjectMeta.Name' pod_meta_c) ordinal
    (v1.ObjectMeta.Name' set_meta_c) with "[]").
  { iPureIntro. split.
    - rewrite Hpod_meta_Hdeepown_name. exact Hpod_name_len.
    - split; first exact Hordinal_int32.
      rewrite Hpod_meta_Hdeepown_name Hset_meta_Hdeepown_name.
      exact Hpod_name. }
  iIntros (ordinal_ret) "%Hordinal_ret".
  wp_auto_keep.
  wp_apply (wp_podName
    (v1.ObjectMeta.Name' set_meta_c) ordinal_ret with "[]").
  { iPureIntro. rewrite Hordinal_ret. lia. }
  wp_pures_keep.
  assert (Hordinal_ret_nat : sint.nat ordinal_ret = ordinal) by word.
  subst ordinal.
  destruct pod.(PodV.ObjectMeta').(ObjectMetaV.Labels') as [labels|]
    eqn:Hlabels.
  2: {
    assert (Hlabels_nil : v1.ObjectMeta.Labels' pod_meta_c = map.nil).
    { apply Hpod_meta_Hdeepown_labels_none. reflexivity. }
    rewrite Hlabels_nil.
    wp_pures_keep.
    wp_apply wp_map_make1 as "%labels_l Hpod_labels".
    wp_pures_keep.
    wp_apply (wp_map_insert go.string with "Hpod_labels") as "Hpod_labels".
    wp_pures_keep.
    wp_apply (wp_strconv_Itoa with "[]").
    { iSplit; first by iEval (rewrite is_pkg_init_unfold /=).
      iPureIntro. rewrite Hordinal_ret. lia. }
    wp_apply (wp_map_insert go.string with "Hpod_labels") as "Hpod_labels".
    wp_pures_keep.
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
      all: try iPureIntro; tauto.
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
    iApply (PodV.deepown_l_restore _ _ _ Hpod_l_not_null).
    iFrame.
  }
  iDestruct "Hpod_meta_Hdeepown_labels_some" as (labels_l)
    "[Hpod_labels %Hlabels_l]".
  subst labels_l.
  iPoseProof (own_map_not_nil with "Hpod_labels") as "%Hlabels_not_nil".
  wp_if_destruct.
  { exfalso. done. }
  wp_pures_keep.
  wp_apply (wp_map_insert go.string with "Hpod_labels") as "Hpod_labels".
  wp_pures_keep.
  wp_apply (wp_strconv_Itoa with "[]").
  { iSplit; first by iEval (rewrite is_pkg_init_unfold /=).
    iPureIntro. rewrite Hordinal_ret. lia. }
  wp_apply (wp_map_insert go.string with "Hpod_labels") as "Hpod_labels".
  wp_pures_keep.
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
    all: try iPureIntro; tauto.
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
  iApply (PodV.deepown_l_restore _ _ _ Hpod_l_not_null).
  iFrame.
  Unshelve. all: apply _.
Qed.

Local Transparent StatefulSetSpecV.deepown StatefulSetView.StatefulSetSpecV.deepown.

(* [initIdentity] is the creation-only extension of [updateIdentity]. It sets
   Hostname and Subdomain before the Pod is submitted to the create API. *)
Lemma wp_initIdentity set_l pod_l (set : StatefulSetV.t) (pod : PodV.t)
    (ordinal : nat) dq_set :
  {{{ "Hset" ∷ StatefulSetV.deepown_l set_l set dq_set ∗
      "Hpod" ∷ PodV.deepown_l pod_l pod 1 ∗
      "%Hpod_name" ∷
        ⌜ pod.(PodV.ObjectMeta').(ObjectMetaV.Name') = desired_pod_name
            set.(StatefulSetV.ObjectMeta').(ObjectMetaV.Name') ordinal ⌝ ∗
      "%Hordinal_int32" ∷ ⌜ (ordinal <= go_int32_max_nat)%nat ⌝ ∗
      "%Hpod_name_len" ∷
        ⌜ Z.of_nat
            (length pod.(PodV.ObjectMeta').(ObjectMetaV.Name')) <=
          go_int_max ⌝
  }}}
    @! statefulset.initIdentity #set_l #pod_l
  {{{ RET #();
      "Hset" ∷ StatefulSetV.deepown_l set_l set dq_set ∗
      "Hpod" ∷ PodV.deepown_l pod_l (init_identity set pod ordinal) 1 ∗
      "%Hidentity_matches" ∷
        ⌜ pod_identity_matches set (init_identity set pod ordinal) ⌝
  }}}.
Proof.
  wp_start as "H". iNamed "H".
  wp_auto_keep.
  wp_apply (wp_updateIdentity set_l pod_l set pod ordinal dq_set
    with "[$Hset $Hpod]").
  { iFrame "%". }
  iIntros "(Hset & Hpod & %Hidentity_matches)".
  iPoseProof (StatefulSetV.deepown_l_split with "Hset") as
    "(%Hset_l_not_null & Hset_typemeta & Hset_objectmeta_l &
      Hset_spec_l & Hset_status_l)".
  iDestruct "Hset_spec_l" as (set_spec_c)
    "[Hset_spec_field Hset_spec]".
  iNamedPrefix "Hset_spec" "Hset_spec_".
  iPoseProof (PodV.deepown_l_split with "Hpod") as
    "(%Hpod_l_not_null & Hpod_typemeta & Hpod_objectmeta_l &
      Hpod_spec_l & Hpod_status_l)".
  iDestruct "Hpod_objectmeta_l" as (pod_meta_c)
    "[Hpod_objectmeta_field Hpod_objectmeta]".
  iNamedPrefix "Hpod_objectmeta" "Hpod_meta_".
  iDestruct "Hpod_spec_l" as (pod_spec_c)
    "[Hpod_spec_field Hpod_spec]".
  iEval (rewrite PodSpecV.deepown_split) in "Hpod_spec".
  iNamedPrefix "Hpod_spec" "Hpod_spec_".
  wp_auto_keep.
  iEval (rewrite Hpod_meta_Hdeepown_name
    Hset_spec_Hdeepown_servicename) in "Hpod_spec_field".
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
    with "[$Hset_typemeta $Hset_objectmeta_l $Hset_spec_l
      $Hset_status_l]") as "Hset".
  iCombineNamed "Hpod_meta_*" as "Hpod_objectmeta".
  iAssert (ObjectMetaV.deepown pod_meta_c
      (update_identity set pod ordinal).(PodV.ObjectMeta') 1)
    with "[Hpod_objectmeta]" as "Hpod_objectmeta".
  { iNamed "Hpod_objectmeta". iFrame. done. }
  iAssert (ObjectMetaV.deepown_l (PodV.objectmeta_ptr pod_l)
      (update_identity set pod ordinal).(PodV.ObjectMeta') 1)
    with "[Hpod_objectmeta_field Hpod_objectmeta]"
    as "Hpod_objectmeta_l".
  { iExists pod_meta_c. iFrame. }
  iCombineNamed "Hpod_spec_H*" as "Hpod_spec".
  iAssert (PodSpecV.deepown
      (pod_spec_c <| v1.PodSpec.Hostname' :=
          (update_identity set pod ordinal).(PodV.ObjectMeta').(
            ObjectMetaV.Name') |> <|
        v1.PodSpec.Subdomain' :=
          set.(StatefulSetV.Spec').(StatefulSetSpecV.ServiceName') |>)
      ((update_identity set pod ordinal).(PodV.Spec')
        <| PodSpecV.Hostname' :=
            (update_identity set pod ordinal).(PodV.ObjectMeta').(
              ObjectMetaV.Name') |>
        <| PodSpecV.Subdomain' :=
            set.(StatefulSetV.Spec').(StatefulSetSpecV.ServiceName') |>) 1)
    with "[Hpod_spec]" as "Hpod_spec".
  { iNamed "Hpod_spec". iEval (rewrite PodSpecV.deepown_split /=). iFrame. done. }
  iAssert (PodSpecV.deepown_l (PodV.spec_ptr pod_l)
      ((update_identity set pod ordinal).(PodV.Spec')
        <| PodSpecV.Hostname' :=
            (update_identity set pod ordinal).(PodV.ObjectMeta').(
              ObjectMetaV.Name') |>
        <| PodSpecV.Subdomain' :=
            set.(StatefulSetV.Spec').(StatefulSetSpecV.ServiceName') |>) 1)
    with "[Hpod_spec_field Hpod_spec]" as "Hpod_spec_l".
  { iExists
      (pod_spec_c <| v1.PodSpec.Hostname' :=
          (update_identity set pod ordinal).(PodV.ObjectMeta').(
            ObjectMetaV.Name') |> <|
        v1.PodSpec.Subdomain' :=
          set.(StatefulSetV.Spec').(StatefulSetSpecV.ServiceName') |>).
    iFrame. }
  iApply "HΦ".
  iFrame "Hset".
  iSplitL.
  - unfold init_identity. cbn. iApply (PodV.deepown_l_restore _ _ _
      Hpod_l_not_null). iFrame.
  - iPureIntro.
    unfold init_identity, pod_identity_matches in *.
    exact Hidentity_matches.
Qed.


End proof.
