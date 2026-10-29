From New.proof Require Import wp_keep.
From New.proof.map Require Import for_range.
From New.proof.controllers.statefulset Require Import pod_predicates.
From New.proof.controllers.statefulset Require Export ordinal.
From New.proof.controllers.statefulset Require Export pvc_predicates.
From New.proof.k8s_io.api.core Require Export v1.

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

Definition statefulset_without_claim_templates_l set_l
    (set : StatefulSetV.t) dq (set_phy : v1.StatefulSet.t) : iProp Σ :=
  "Hset_ptr" ∷ set_l ↦{dq} set_phy ∗
  "%Hdeepown_typemeta" ∷
    ⌜ set_phy.(v1.StatefulSet.TypeMeta') =
        set.(StatefulSetV.TypeMeta') ⌝ ∗
  "Hdeepown_objectmeta" ∷
    ObjectMetaV.deepown set_phy.(v1.StatefulSet.ObjectMeta')
      set.(StatefulSetV.ObjectMeta') dq ∗
  "%Hset_spec_Hdeepown_replicas_none" ∷
    ⌜ set_phy.(v1.StatefulSet.Spec').(v1.StatefulSetSpec.Replicas') =
        null ↔
      set.(StatefulSetV.Spec').(StatefulSetSpecV.Replicas') = None ⌝ ∗
  "Hset_spec_Hdeepown_replicas_some" ∷
    (match set.(StatefulSetV.Spec').(StatefulSetSpecV.Replicas') with
     | Some replicas =>
         ∃ replicas_phy,
           set_phy.(v1.StatefulSet.Spec').(v1.StatefulSetSpec.Replicas')
             ↦{dq} replicas_phy ∗
           ⌜ replicas_phy = replicas ⌝
     | None => True%I
     end) ∗
  "%Hset_spec_Hdeepown_selector_none" ∷
    ⌜ set_phy.(v1.StatefulSet.Spec').(v1.StatefulSetSpec.Selector') =
        null ↔
      set.(StatefulSetV.Spec').(StatefulSetSpecV.Selector') = None ⌝ ∗
  "Hset_spec_Hdeepown_selector_some" ∷
    (match set.(StatefulSetV.Spec').(StatefulSetSpecV.Selector') with
     | Some selector =>
         ∃ selector_c,
           set_phy.(v1.StatefulSet.Spec').(v1.StatefulSetSpec.Selector')
             ↦{dq} selector_c ∗
           LabelSelectorV.deepown selector_c selector dq
     | None => True%I
     end) ∗
  "Hset_spec_Hdeepown_template" ∷
    PodTemplateSpecV.deepown
      set_phy.(v1.StatefulSet.Spec').(v1.StatefulSetSpec.Template')
      set.(StatefulSetV.Spec').(StatefulSetSpecV.Template') dq ∗
  "%Hset_spec_Hdeepown_servicename" ∷
    ⌜ set_phy.(v1.StatefulSet.Spec').(v1.StatefulSetSpec.ServiceName') =
        set.(StatefulSetV.Spec').(StatefulSetSpecV.ServiceName') ⌝ ∗
  "Hdeepown_status" ∷
    StatefulSetStatusV.deepown set_phy.(v1.StatefulSet.Status')
      set.(StatefulSetV.Status') dq.

Lemma statefulset_without_claim_templates_l_intro set_l
    (set : StatefulSetV.t) dq (set_phy : v1.StatefulSet.t)
    (Htypemeta :
      set_phy.(v1.StatefulSet.TypeMeta') =
        set.(StatefulSetV.TypeMeta'))
    (Hreplicas_none :
      set_phy.(v1.StatefulSet.Spec').(v1.StatefulSetSpec.Replicas') =
          null ↔
        set.(StatefulSetV.Spec').(StatefulSetSpecV.Replicas') = None)
    (Hselector_none :
      set_phy.(v1.StatefulSet.Spec').(v1.StatefulSetSpec.Selector') =
          null ↔
        set.(StatefulSetV.Spec').(StatefulSetSpecV.Selector') = None)
    (Hservicename :
      set_phy.(v1.StatefulSet.Spec').(v1.StatefulSetSpec.ServiceName') =
        set.(StatefulSetV.Spec').(StatefulSetSpecV.ServiceName')) :
  set_l ↦{dq} set_phy -∗
  ObjectMetaV.deepown set_phy.(v1.StatefulSet.ObjectMeta')
    set.(StatefulSetV.ObjectMeta') dq -∗
  (match set.(StatefulSetV.Spec').(StatefulSetSpecV.Replicas') with
   | Some replicas =>
       ∃ replicas_phy,
         set_phy.(v1.StatefulSet.Spec').(v1.StatefulSetSpec.Replicas')
           ↦{dq} replicas_phy ∗
         ⌜ replicas_phy = replicas ⌝
   | None => True%I
   end) -∗
  (match set.(StatefulSetV.Spec').(StatefulSetSpecV.Selector') with
   | Some selector =>
       ∃ selector_c,
         set_phy.(v1.StatefulSet.Spec').(v1.StatefulSetSpec.Selector')
           ↦{dq} selector_c ∗
         LabelSelectorV.deepown selector_c selector dq
   | None => True%I
   end) -∗
  PodTemplateSpecV.deepown
    set_phy.(v1.StatefulSet.Spec').(v1.StatefulSetSpec.Template')
    set.(StatefulSetV.Spec').(StatefulSetSpecV.Template') dq -∗
  StatefulSetStatusV.deepown set_phy.(v1.StatefulSet.Status')
    set.(StatefulSetV.Status') dq -∗
  statefulset_without_claim_templates_l set_l set dq set_phy.
Proof.
  iIntros "Hset_ptr Hobjectmeta Hreplicas Hselector Htemplate Hstatus".
  rewrite /statefulset_without_claim_templates_l.
  iFrame.
  iFrame "%".
Qed.

(* Borrow the contents and elements; the restoration continuation retains
   capacity ownership and the remaining generated fields. *)
Definition statefulset_claim_templates (set_phy : v1.StatefulSet.t)
    (set : StatefulSetV.t) dq : iProp Σ :=
  ∃ templates_c,
    set_phy.(v1.StatefulSet.Spec').(v1.StatefulSetSpec.VolumeClaimTemplates') ↦*{dq} templates_c ∗
    [∗ list] c;v ∈ templates_c;StatefulSetSpecV.volume_claim_templates_list set.(StatefulSetV.Spec'),
      PersistentVolumeClaimV.deepown c v dq.

Definition statefulset_restore_claim_templates_l set_l (set : StatefulSetV.t) dq set_phy : iProp Σ :=
  statefulset_without_claim_templates_l set_l set dq set_phy -∗
  statefulset_claim_templates set_phy set dq -∗
  StatefulSetV.deepown_l set_l set dq.

Lemma wp_newPersistentVolumeClaim_without_claim_templates
    set_l pod_l claim_template_l
    (set : StatefulSetV.t) (pod : PodV.t)
    (claim_template : PersistentVolumeClaimV.t) (ordinal : nat)
    dq_set dq_pod dq_claim_template_ptr dq_claim_template
    set_phy claim_template_phy :
  {{{ "#Hpkg" ∷ is_pkg_init code.controllers.statefulset.pkg_id.statefulset ∗
      "Hset" ∷ statefulset_without_claim_templates_l set_l set dq_set set_phy ∗
      "Hpod" ∷ PodV.deepown_l pod_l pod dq_pod ∗
      "Hclaim_template_ptr" ∷ claim_template_l ↦{dq_claim_template_ptr} claim_template_phy ∗
      "Hclaim_template" ∷ PersistentVolumeClaimV.deepown claim_template_phy claim_template dq_claim_template ∗
      "%Hordinal_bound" ∷ ⌜ (ordinal ≤ go_int32_max_nat)%nat ⌝ ∗
      "%Hpod_name" ∷
        ⌜ pod.(PodV.ObjectMeta').(ObjectMetaV.Name') =
            desired_pod_name
              set.(StatefulSetV.ObjectMeta').(ObjectMetaV.Name') ordinal ⌝ ∗
      "%Hpod_name_len" ∷
        ⌜ Z.of_nat
            (length pod.(PodV.ObjectMeta').(ObjectMetaV.Name')) ≤ go_int_max ⌝
  }}}
    @! statefulset.newPersistentVolumeClaim
      #set_l #pod_l #claim_template_l
  {{{ claim_l, RET #claim_l;
      "Hset" ∷ statefulset_without_claim_templates_l set_l set dq_set set_phy ∗
      "Hpod" ∷ PodV.deepown_l pod_l pod dq_pod ∗
      "Hclaim_template_ptr" ∷ claim_template_l ↦{dq_claim_template_ptr} claim_template_phy ∗
      "Hclaim_template" ∷ PersistentVolumeClaimV.deepown claim_template_phy claim_template dq_claim_template ∗
      "Hclaim" ∷ PersistentVolumeClaimV.deepown_l claim_l
        (new_persistent_volume_claim set claim_template ordinal) 1
  }}}.
Proof.
  wp_start as "H". iNamed "H".
  wp_auto_keep.
  iAssert (is_pkg_init code.k8s_io.api.core.v1.pkg_id.v1)
    as "#Hcore_v1".
  { iPkgInit. }
  wp_apply (wp_PersistentVolumeClaim__DeepCopy
    with "[$Hcore_v1 $Hclaim_template_ptr $Hclaim_template]").
  iIntros (claim_l)
    "(Hclaim & Hclaim_template_ptr & Hclaim_template)".
  wp_auto_keep.
  iNamed "Hset".
  set (set_meta_c := set_phy.(v1.StatefulSet.ObjectMeta')).
  set (set_spec_c := set_phy.(v1.StatefulSet.Spec')).
  iNamedPrefix "Hdeepown_objectmeta" "Hset_meta_".
  iDestruct "Hpod" as (pod_phy) "[Hpod_ptr Hpod_deepown]".
  iNamedPrefix "Hpod_deepown" "Hpod_".
  set (pod_meta_c := pod_phy.(v1.Pod.ObjectMeta')).
  iNamedPrefix "Hpod_Hdeepown_objectmeta" "Hpod_meta_".
  iPoseProof (PersistentVolumeClaimV.deepown_l_split with "Hclaim") as
    "(%Hclaim_l_not_null & Hclaim_typemeta & Hclaim_objectmeta_l &
      Hclaim_spec_l & Hclaim_status_l)".
  iDestruct "Hclaim_objectmeta_l" as (claim_meta_c)
    "[Hclaim_objectmeta_field Hclaim_objectmeta]".
  iNamedPrefix "Hclaim_objectmeta" "Hclaim_meta_".
  wp_auto_keep.
  wp_apply (wp_ordinalOf
    (v1.ObjectMeta.Name' pod_meta_c) ordinal
    (v1.ObjectMeta.Name' set_meta_c) with "[]").
  { iPureIntro. split.
    - rewrite Hpod_meta_Hdeepown_name. exact Hpod_name_len.
    - split; first exact Hordinal_bound.
      rewrite Hpod_meta_Hdeepown_name Hset_meta_Hdeepown_name.
      exact Hpod_name. }
  iIntros (ordinal_ret) "%Hordinal_ret".
  wp_auto_keep.
  wp_apply (wp_claimName
    (v1.ObjectMeta.Name' set_meta_c)
    (v1.ObjectMeta.Name' claim_meta_c) ordinal_ret with "[]").
  { iPureIntro. rewrite Hordinal_ret. lia. }
  assert (Hordinal_ret_nat : sint.nat ordinal_ret = ordinal) by word.
  iCombineNamed "Hpod_meta_*" as "Hpod_objectmeta".
  iAssert (ObjectMetaV.deepown pod_meta_c
      pod.(PodV.ObjectMeta') dq_pod)
    with "[Hpod_objectmeta]" as "Hpod_objectmeta_rebuilt".
  { iNamed "Hpod_objectmeta".
    rewrite /ObjectMetaV.deepown.
    iFrame.
    done. }
  iAssert (PodV.deepown_l pod_l pod dq_pod)
    with "[Hpod_ptr Hpod_objectmeta_rebuilt
      Hpod_Hdeepown_spec Hpod_Hdeepown_status]" as "Hpod".
  { iExists pod_phy.
    rewrite /PodV.deepown.
    iFrame.
    iFrame "%". }
  (* Join the nil/non-nil allocation cases before copying selector labels.
     Otherwise every selector case duplicates the entire ownership rebuild. *)
  wp_bind (if: _ then _ else _)%E.
  iApply (wp_wand _ _ _ (λ v,
    ⌜ v = execute_val ⌝ ∗
    claim_ptr ↦ claim_l ∗
    ∃ (claim_labels_l : map.t) (claim_meta_current : v1.ObjectMeta.t),
      PersistentVolumeClaimV.objectmeta_ptr claim_l ↦ claim_meta_current ∗
      ⌜ claim_meta_current =
          claim_meta_c
            <| v1.ObjectMeta.Name' :=
              v1.ObjectMeta.Name' claim_meta_c ++ "-"%go ++
              v1.ObjectMeta.Name' set_meta_c ++ "-"%go ++
              decimal_string (sint.nat ordinal_ret) |>
            <| v1.ObjectMeta.Namespace' := v1.ObjectMeta.Namespace' set_meta_c |>
            <| v1.ObjectMeta.OwnerReferences' := slice.nil |>
            <| v1.ObjectMeta.Labels' := claim_labels_l |> ⌝ ∗
      claim_labels_l ↦$ default ∅ claim_template.(PersistentVolumeClaimV.ObjectMeta').(ObjectMetaV.Labels'))%I
    with "[claim Hclaim_objectmeta_field Hclaim_meta_Hdeepown_labels_some]").
  {
    destruct claim_template.(PersistentVolumeClaimV.ObjectMeta').(ObjectMetaV.Labels')
      as [claim_labels|] eqn:Hclaim_labels_opt.
    all:
      match goal with
      | claim_labels : gmap go_string go_string |- _ =>
          iDestruct "Hclaim_meta_Hdeepown_labels_some" as (claim_labels_c)
            "[Hclaim_labels %Hclaim_labels_c]";
          subst claim_labels_c;
          iPoseProof (own_map_not_nil with "Hclaim_labels") as
            "%Hclaim_labels_not_nil";
          wp_if_destruct;
          [exfalso; done|];
          wp_pures_keep;
          set (claim_labels_l := v1.ObjectMeta.Labels' claim_meta_c);
          set (claim_labels_base := claim_labels)
      | _ =>
          assert (Hclaim_labels_nil :
            v1.ObjectMeta.Labels' claim_meta_c = map.nil);
          [apply Hclaim_meta_Hdeepown_labels_none; done|];
          rewrite Hclaim_labels_nil;
          wp_pures_keep;
          wp_apply wp_map_make1 as "%claim_labels_l Hclaim_labels";
          wp_pures_keep;
          set (claim_labels_base := (∅ : gmap go_string go_string))
      end.
    all:
      try wp_auto_keep;
      iSplit; first done;
      iFrame "claim";
      iExists claim_labels_l, _;
      iFrame "Hclaim_objectmeta_field";
      iSplit;
      [iPureIntro; try subst claim_labels_l; destruct claim_meta_c; reflexivity|];
      rewrite ?Hclaim_labels_opt /=;
      iExact "Hclaim_labels".
  }
  iIntros (v) "[-> (claim & %claim_labels_l & %claim_meta_current & Hclaim_objectmeta_field &
    %Hclaim_meta_current & Hclaim_labels)]".
  wp_pures_keep.
  set (claim_labels_base := default ∅ claim_template.(PersistentVolumeClaimV.ObjectMeta').(ObjectMetaV.Labels')).
  (* Join selector cases too, so metadata is reconstructed only once. *)
  wp_auto_keep.
  wp_bind (if: _ then _ else _)%E.
  iApply (wp_wand _ _ _ (λ v,
    ⌜ v = execute_val ⌝ ∗
    set_l ↦{dq_set} set_phy ∗
    claim_ptr ↦ claim_l ∗
    PersistentVolumeClaimV.objectmeta_ptr claim_l ↦ claim_meta_current ∗
    claim_labels_l ↦$ new_persistent_volume_claim_labels set claim_template ∗
    match set.(StatefulSetV.Spec').(StatefulSetSpecV.Selector') with
    | Some selector => ∃ selector_c,
        set_phy.(v1.StatefulSet.Spec').(v1.StatefulSetSpec.Selector') ↦{dq_set} selector_c ∗
        LabelSelectorV.deepown selector_c selector dq_set
    | None => True
    end)%I
    with "[set Hset_ptr claim Hset_spec_Hdeepown_selector_some Hclaim_objectmeta_field Hclaim_labels]").
  {
    all:
      destruct set.(StatefulSetV.Spec').(StatefulSetSpecV.Selector')
        as [selector|] eqn:Hselector_opt.
    all:
      lazymatch type of Hselector_opt with
      | _ = Some ?selector =>
          iDestruct "Hset_spec_Hdeepown_selector_some" as (selector_c)
            "[Hset_selector_ptr Hselector]";
          assert (Hselector_not_nil :
            v1.StatefulSetSpec.Selector' set_spec_c ≠ null)
            by (intros Hnil;
                pose proof
                  (proj1 Hset_spec_Hdeepown_selector_none Hnil) as Hfalse;
                discriminate);
          assert (Hselector_bool :
            bool_decide
              (v1.StatefulSetSpec.Selector' set_spec_c = null) = false)
            by (apply bool_decide_eq_false_2; exact Hselector_not_nil);
          rewrite Hselector_bool;
          wp_pures_keep;
          iNamedPrefix "Hselector" "Hselector_";
          wp_auto_keep;
          destruct selector.(LabelSelectorV.MatchLabels')
            as [selector_labels|] eqn:Hselector_labels_opt
      | _ = None =>
          assert (Hselector_nil :
            v1.StatefulSetSpec.Selector' set_spec_c = null)
            by (apply (proj2 Hset_spec_Hdeepown_selector_none);
                reflexivity);
          rewrite Hselector_nil;
          wp_pures_keep;
          iAssert True%I with "[]" as "Hset_selector_some";
          [done|];
          set (selector_labels_base := (∅ : gmap go_string go_string))
      end.
    all: try (
      iDestruct "Hselector_Hdeepown_matchlabels_some" as
        (selector_labels_c)
        "[Hselector_labels %Hselector_labels_c]";
      subst selector_labels_c;
      wp_apply (wp_map_for_range_return_func
        (key_type:=go.string)
        (λ (keys : list go_string) i,
          ∃ (last_value last_key : go_string),
            "value" ∷ value_ptr ↦ last_value ∗
            "key" ∷ key_ptr ↦ last_key ∗
            "claim" ∷ claim_ptr ↦ claim_l ∗
            "Hclaim_objectmeta_field" ∷
              PersistentVolumeClaimV.objectmeta_ptr claim_l ↦
                claim_meta_current ∗
            "Hclaim_labels" ∷ claim_labels_l ↦$
              (map_prefix keys i selector_labels ∪
                claim_labels_base))%I
        with "Hselector_labels");
      [done|];
      iIntros (keys) "%Hkeys";
      iSplitL "value key claim Hclaim_objectmeta_field Hclaim_labels";
      [iExists ""%go, ""%go;
       rewrite map_prefix_empty left_id_L;
       iFrame|];
      iSplitL "";
      [iModIntro;
       iIntros (i key value) "%Hiter Hloop";
       destruct Hkeys as
         [Hkeys_dom [Hkeys_len Hkeys_nodup]];
       destruct Hiter as
         [Hi_bounds [Hkey_lookup Hvalue_lookup]];
       destruct Hi_bounds as [Hi_nonneg Hi_upper];
       iDestruct "Hloop" as
         (last_value last_key)
         "(value & key & claim & Hclaim_objectmeta_field & Hclaim_labels)";
       assert (Hclaim_meta_labels :
         v1.ObjectMeta.Labels' claim_meta_current = claim_labels_l)
         by (rewrite Hclaim_meta_current; reflexivity);
       wp_pures_keep;
       simpl subst';
       wp_auto_keep;
       rewrite Hclaim_meta_labels;
       wp_apply (wp_map_insert (K:=go_string) (V:=go_string)
         go.string with "Hclaim_labels") as "Hclaim_labels";
       iRight; iSplit; [done|];
       iExists value, key;
       iFrame;
       iFrame "%";
       rewrite insert_union_l -map_prefix_insert;
       done
      |iIntros "Hselector_labels Hloop";
       iDestruct "Hloop" as
         (last_value last_key)
         "(value & key & claim & Hclaim_objectmeta_field & Hclaim_labels)";
       destruct Hkeys as
         [Hkeys_dom [Hkeys_len Hkeys_nodup]];
       rewrite
         (map_prefix_all keys selector_labels
           Hkeys_dom Hkeys_len);
       wp_pures_keep;
       set (selector_labels_base := selector_labels)]).
    all: try (
      assert (Hselector_labels_nil :
        v1.LabelSelector.MatchLabels' selector_c = map.nil)
        by (apply
              (proj2 Hselector_Hdeepown_matchlabels_none);
            reflexivity);
      rewrite Hselector_labels_nil;
      wp_apply (wp_map_for_range_nil go.string go.string);
      wp_pures_keep;
      set (selector_labels_base :=
        (∅ : gmap go_string go_string))).
    all:
      lazymatch goal with
      | Hselector_labels_opt :
          LabelSelectorV.MatchLabels' ?selector =
            Some ?selector_labels |- _ =>
          iAssert (LabelSelectorV.deepown selector_c selector dq_set)
            with "[Hselector_labels
                   Hselector_Hdeepown_matchexpressions]"
            as "Hselector";
          [rewrite /LabelSelectorV.deepown Hselector_labels_opt /=;
           iSplit;
           [iPureIntro;
            exact Hselector_Hdeepown_matchlabels_none|];
           iSplitL "Hselector_labels";
           [iExists selector_labels;
            iFrame;
            done|];
           iFrame "Hselector_Hdeepown_matchexpressions"|]
      | Hselector_labels_opt :
          LabelSelectorV.MatchLabels' ?selector = None |- _ =>
          iAssert (LabelSelectorV.deepown selector_c selector dq_set)
            with "[Hselector_Hdeepown_matchexpressions]"
            as "Hselector";
          [rewrite /LabelSelectorV.deepown Hselector_labels_opt /=;
           iSplit;
           [iPureIntro;
            exact Hselector_Hdeepown_matchlabels_none|];
           iSplit; [done|];
           iFrame "Hselector_Hdeepown_matchexpressions"|]
      | _ => idtac
      end.
    all: try (
      iAssert
        ((match set.(StatefulSetV.Spec').(StatefulSetSpecV.Selector') with
          | Some pure_selector =>
              ∃ selector_phy,
                v1.StatefulSetSpec.Selector' set_spec_c ↦{dq_set}
                  selector_phy ∗
                LabelSelectorV.deepown
                  selector_phy pure_selector dq_set
          | None => True%I
          end)%I)
        with "[Hset_selector_ptr Hselector]"
        as "Hset_selector_some";
      [rewrite Hselector_opt;
       iExists selector_c;
       iFrame|]).
    all:
      assert (Hclaim_labels_result :
        selector_labels_base ∪ claim_labels_base =
          new_persistent_volume_claim_labels set claim_template)
        by (subst selector_labels_base;
            subst claim_labels_base;
            unfold new_persistent_volume_claim_labels;
            rewrite Hselector_opt /=;
            try rewrite Hselector_labels_opt;
            rewrite ?left_id_L;
            done).
    all:
      iAssert (claim_labels_l ↦$
          new_persistent_volume_claim_labels set claim_template)
        with "[Hclaim_labels]" as "Hclaim_labels";
      [rewrite -Hclaim_labels_result;
       subst selector_labels_base;
       rewrite ?left_id_L;
       iExact "Hclaim_labels"|].
    all:
      iSplit; first done;
      iFrame "Hset_ptr claim Hclaim_labels Hclaim_objectmeta_field";
      rewrite ?Hselector_opt;
      iExact "Hset_selector_some".
  }
  iIntros (v) "[-> (Hset_ptr & claim & Hclaim_objectmeta_field & Hclaim_labels & Hset_spec_Hdeepown_selector_some)]".
  wp_pures_keep.
  iCombineNamed "Hset_meta_*" as "Hset_objectmeta";
  iAssert (ObjectMetaV.deepown set_meta_c
      set.(StatefulSetV.ObjectMeta') dq_set)
    with "[Hset_objectmeta]" as "Hset_objectmeta";
  [iNamed "Hset_objectmeta";
   rewrite /ObjectMetaV.deepown;
   iFrame;
   done|].
  iPoseProof (own_map_not_nil with "Hclaim_labels") as
    "%Hclaim_labels_l_not_nil".
  set (claim_meta_result :=
    claim_template.(PersistentVolumeClaimV.ObjectMeta')
      <| ObjectMetaV.Name' :=
          desired_pvc_name
            set.(StatefulSetV.ObjectMeta').(ObjectMetaV.Name')
            claim_template.(PersistentVolumeClaimV.ObjectMeta').(ObjectMetaV.Name')
            (sint.nat ordinal_ret) |>
      <| ObjectMetaV.Namespace' :=
          set.(StatefulSetV.ObjectMeta').(ObjectMetaV.Namespace') |>
      <| ObjectMetaV.OwnerReferences' := None |>
      <| ObjectMetaV.Labels' :=
          Some (new_persistent_volume_claim_labels set claim_template) |>).
  assert (Hclaim_meta_labels_none :
    claim_labels_l = map.nil ↔
      Some (new_persistent_volume_claim_labels
        set claim_template) = None)
    by (split;
        [intros Hnil; exfalso;
         apply Hclaim_labels_l_not_nil;
         exact Hnil
        |discriminate]).
  iAssert (ObjectMetaV.deepown claim_meta_current claim_meta_result 1)
    with "[Hclaim_labels
           Hclaim_meta_Hdeepown_creationtimestamp
           Hclaim_meta_Hdeepown_deletiontimestamp_some
           Hclaim_meta_Hdeepown_deletiongraceperiodseconds_some
           Hclaim_meta_Hdeepown_annotations_some
           Hclaim_meta_Hdeepown_finalizers_some
           Hclaim_meta_Hdeepown_managedfields
           Hclaim_meta_Hdeepown_finalizers_cap]"
    as "Hclaim_objectmeta";
  [subst claim_meta_result;
   rewrite Hclaim_meta_current /ObjectMetaV.deepown /=;
   iSplit;
   [iPureIntro;
    unfold desired_pvc_name;
    rewrite Hclaim_meta_Hdeepown_name
      Hset_meta_Hdeepown_name;
    done|];
   iSplit;
   [iPureIntro;
    exact Hclaim_meta_Hdeepown_generatename|];
   iSplit;
   [iPureIntro;
    exact Hset_meta_Hdeepown_namespace|];
   iSplit;
   [iPureIntro;
    exact Hclaim_meta_Hdeepown_selflink|];
   iSplit;
   [iPureIntro;
    exact Hclaim_meta_Hdeepown_uid|];
   iSplit;
   [iPureIntro;
    exact Hclaim_meta_Hdeepown_resourceversion|];
   iSplit;
   [iPureIntro;
    exact Hclaim_meta_Hdeepown_generation|];
   iFrame "Hclaim_meta_Hdeepown_creationtimestamp";
   iSplit;
   [iPureIntro;
    exact Hclaim_meta_Hdeepown_deletiontimestamp_none|];
   iFrame "Hclaim_meta_Hdeepown_deletiontimestamp_some";
   iSplit;
   [iPureIntro;
    exact Hclaim_meta_Hdeepown_deletiongraceperiodseconds_none|];
   iFrame
     "Hclaim_meta_Hdeepown_deletiongraceperiodseconds_some";
   iSplit;
   [iPureIntro;
    exact Hclaim_meta_labels_none|];
   iSplitL "Hclaim_labels";
   [iExists (new_persistent_volume_claim_labels
      set claim_template);
    iFrame;
    done|];
   iSplit;
   [iPureIntro;
    exact Hclaim_meta_Hdeepown_annotations_none|];
   iFrame "Hclaim_meta_Hdeepown_annotations_some";
   iSplitR;
   [iApply deepown_slice_nil|];
   iSplit;
   [iPureIntro;
    exact Hclaim_meta_Hdeepown_finalizers_none|];
   iFrame "Hclaim_meta_Hdeepown_finalizers_some Hclaim_meta_Hdeepown_finalizers_cap";
   iFrame "Hclaim_meta_Hdeepown_managedfields"|].
  iAssert (ObjectMetaV.deepown_l
      (PersistentVolumeClaimV.objectmeta_ptr claim_l)
      (claim_template.(PersistentVolumeClaimV.ObjectMeta')
        <| ObjectMetaV.Name' :=
            desired_pvc_name
              set.(StatefulSetV.ObjectMeta').(ObjectMetaV.Name')
              claim_template.(PersistentVolumeClaimV.ObjectMeta').(ObjectMetaV.Name')
              (sint.nat ordinal_ret) |>
        <| ObjectMetaV.Namespace' :=
            set.(StatefulSetV.ObjectMeta').(ObjectMetaV.Namespace') |>
        <| ObjectMetaV.OwnerReferences' := None |>
        <| ObjectMetaV.Labels' :=
            Some (new_persistent_volume_claim_labels
              set claim_template) |>) 1)
    with "[Hclaim_objectmeta_field Hclaim_objectmeta]"
    as "Hclaim_objectmeta_l";
  [iExists claim_meta_current; iFrame|].
  iPoseProof (PersistentVolumeClaimV.deepown_l_merge
    claim_l claim_template _ 1 Hclaim_l_not_null with
    "[$Hclaim_typemeta $Hclaim_objectmeta_l
     $Hclaim_spec_l $Hclaim_status_l]") as "Hclaim".
  iAssert (PersistentVolumeClaimV.deepown_l claim_l
      (new_persistent_volume_claim
        set claim_template (sint.nat ordinal_ret)) 1)
    with "[Hclaim]" as "Hclaim";
  [rewrite /new_persistent_volume_claim
     /PersistentVolumeClaimV.update_objectmeta;
   iExact "Hclaim"|].
  subst set_meta_c;
  subst set_spec_c;
  iPoseProof
    (statefulset_without_claim_templates_l_intro
      set_l set dq_set set_phy Hdeepown_typemeta
      Hset_spec_Hdeepown_replicas_none
      Hset_spec_Hdeepown_selector_none
      Hset_spec_Hdeepown_servicename
      with "Hset_ptr Hset_objectmeta
        Hset_spec_Hdeepown_replicas_some Hset_spec_Hdeepown_selector_some
        Hset_spec_Hdeepown_template Hdeepown_status")
    as "Hset".
  wp_pures_keep.
  lazymatch goal with
  | Hordinal_ret_nat :
      sint.nat ?ordinal_ret = ?ordinal |- _ =>
      iEval (rewrite Hordinal_ret_nat) in "Hclaim"
  | _ => idtac
  end.
all: try wp_load.
all: try wp_pures_keep.
  iApply ("HΦ" $! claim_l);
  iFrame.
Qed.

Local Transparent StatefulSetSpecV.deepown StatefulSetView.StatefulSetSpecV.deepown.

Lemma wp_newPersistentVolumeClaim set_l pod_l claim_template_l
    (set : StatefulSetV.t) (pod : PodV.t)
    (claim_template : PersistentVolumeClaimV.t) (ordinal : nat)
    dq_set dq_pod dq_claim_template :
  {{{ "#Hpkg" ∷ is_pkg_init code.controllers.statefulset.pkg_id.statefulset ∗
      "Hset" ∷ StatefulSetV.deepown_l set_l set dq_set ∗
      "Hpod" ∷ PodV.deepown_l pod_l pod dq_pod ∗
      "Hclaim_template" ∷ PersistentVolumeClaimV.deepown_l claim_template_l claim_template dq_claim_template ∗
      "%Hordinal_bound" ∷ ⌜ (ordinal ≤ go_int32_max_nat)%nat ⌝ ∗
      "%Hpod_name" ∷
        ⌜ pod.(PodV.ObjectMeta').(ObjectMetaV.Name') =
            desired_pod_name
              set.(StatefulSetV.ObjectMeta').(ObjectMetaV.Name') ordinal ⌝ ∗
      "%Hpod_name_len" ∷
        ⌜ Z.of_nat
            (length pod.(PodV.ObjectMeta').(ObjectMetaV.Name')) ≤ go_int_max ⌝
  }}}
    @! statefulset.newPersistentVolumeClaim
      #set_l #pod_l #claim_template_l
  {{{ claim_l, RET #claim_l;
      "Hset" ∷ StatefulSetV.deepown_l set_l set dq_set ∗
      "Hpod" ∷ PodV.deepown_l pod_l pod dq_pod ∗
      "Hclaim_template" ∷ PersistentVolumeClaimV.deepown_l claim_template_l claim_template dq_claim_template ∗
      "Hclaim" ∷ PersistentVolumeClaimV.deepown_l claim_l
        (new_persistent_volume_claim set claim_template ordinal) 1
  }}}.
Proof.
  iIntros (Φ) "H HΦ". iNamed "H".
  iDestruct "Hset" as (set_phy) "[Hset_ptr Hset]".
  iNamed "Hset".
  iNamed "Hdeepown_spec".
  iDestruct "Hclaim_template" as (claim_template_phy)
    "[Hclaim_template_ptr Hclaim_template]".
  iAssert (statefulset_without_claim_templates_l
      set_l set dq_set set_phy)
    with "[Hset_ptr Hdeepown_objectmeta
      Hdeepown_replicas_some Hdeepown_selector_some
      Hdeepown_template Hdeepown_status]" as "Hset".
  { rewrite /statefulset_without_claim_templates_l.
    iFrame. iFrame "%". }
  wp_apply (wp_newPersistentVolumeClaim_without_claim_templates
    set_l pod_l claim_template_l set pod claim_template ordinal
    dq_set dq_pod dq_claim_template dq_claim_template
    set_phy claim_template_phy
    with "[$Hpkg $Hset $Hpod $Hclaim_template_ptr $Hclaim_template]").
  { iFrame "%". }
  iIntros (claim_l) "H". iNamed "H".
  iAssert (PersistentVolumeClaimV.deepown_l
      claim_template_l claim_template dq_claim_template)
    with "[Hclaim_template_ptr Hclaim_template]"
    as "Hclaim_template_l".
  { iExists claim_template_phy. iFrame. }
  iNamed "Hset".
  iAssert (StatefulSetV.deepown_l set_l set dq_set)
    with "[Hset_ptr Hdeepown_objectmeta
      Hset_spec_Hdeepown_replicas_some
      Hset_spec_Hdeepown_selector_some
      Hset_spec_Hdeepown_template Hdeepown_volumeclaimtemplates
      Hdeepown_updatestrategy Hdeepown_revisionhistorylimit_some
      Hdeepown_persistentvolumeclaimretentionpolicy_some Hdeepown_ordinals_some
      Hdeepown_status]" as "Hset".
  { iExists set_phy.
    rewrite /StatefulSetV.deepown /StatefulSetSpecV.deepown.
    iFrame.
    iFrame "%". }
  iApply "HΦ".
  iFrame "Hset Hpod Hclaim_template_l Hclaim".
Qed.

End proof.
