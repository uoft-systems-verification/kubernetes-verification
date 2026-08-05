From New.proof.controllers.statefulset Require Import top_level.
From New.proof.controllers.statefulset Require Export pod_predicates.
From New.proof.controllers.statefulset Require Export ordinal.
From New.proof.k8s_io.api.core Require Export v1.
From New.proof.kubernetes_model.tx Require Export update_release.

Section proof.
Context `{hG: !heapGS Σ} `{!ffi_semantics _ _}.
Context {sem : go.Semantics}
  {package_sem : code.controllers.statefulset.statefulset.Assumptions}.
Collection W := sem + package_sem.
#[local] Instance base_common_sem : common.Assumptions | 100 :=
  code.controllers.statefulset.statefulset.import_common_Assumption.
#[local] Instance controller_sem : controller.Assumptions :=
  code.controllers.statefulset.statefulset.import_controller_Assumption.
#[local] Instance runtime_sem :
    code.k8s_io.apimachinery.pkg.runtime.runtime.Assumptions :=
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

Definition owner_references_without_uid
    (uid : types.UID.t) (owner_references : list OwnerReferenceV.t) :
    list OwnerReferenceV.t :=
  filter
    (λ owner_reference,
      owner_reference.(OwnerReferenceV.UID') ≠ uid)
    owner_references.

Definition release_pod_input
    (set : StatefulSetV.t) (pod : PodV.t) : PodV.t :=
  pod <| PodV.ObjectMeta' :=
    pod.(PodV.ObjectMeta')
      <| ObjectMetaV.OwnerReferences' :=
        Some (owner_references_without_uid
          set.(StatefulSetV.ObjectMeta').(ObjectMetaV.UID')
          (default []
            pod.(PodV.ObjectMeta').(ObjectMetaV.OwnerReferences'))) |> |>.

Lemma release_owner_references_facts meta parent_key parent_uid
    owner_references :
  meta.(ObjectMetaV.OwnerReferences') = Some owner_references →
  valid_owner_references (Some owner_references) →
  meta_parent_ref meta = Some (parent_key, parent_uid) →
  let released_owner_references :=
    owner_references_without_uid parent_uid owner_references in
  (∃ owner_reference,
      owner_reference ∈ owner_references ∧
      owner_reference.(OwnerReferenceV.UID') = parent_uid) ∧
  list_find
    (λ owner_reference,
      owner_reference.(OwnerReferenceV.Controller') = Some true)
    released_owner_references = None ∧
  valid_owner_references (Some released_owner_references).
Proof.
  intros Howner_references Hvalid Hparent.
  unfold meta_parent_ref in Hparent.
  rewrite Howner_references in Hparent.
  destruct (list_find
    (λ owner_reference : OwnerReferenceV.t,
      owner_reference.(OwnerReferenceV.Controller') = Some true)
    owner_references) as [[parent_i parent_reference]|]
      eqn:Hfind; last done.
  apply list_find_Some in Hfind as
    (Hparent_lookup & Hparent_controller & _).
  inversion Hparent; subst parent_uid; clear Hparent.
  destruct Hvalid as (Hunique & Hall_valid).
  set released_owner_references :=
    owner_references_without_uid
      parent_reference.(OwnerReferenceV.UID') owner_references.
  assert (Hno_controller :
      list_find
        (λ owner_reference : OwnerReferenceV.t,
          owner_reference.(OwnerReferenceV.Controller') = Some true)
        released_owner_references = None).
  {
    apply list_find_None.
    apply Forall_forall.
    intros owner_reference Hin Hcontroller.
    unfold released_owner_references,
      owner_references_without_uid in Hin.
    rewrite -list_elem_of_In in Hin.
    apply list_elem_of_filter in Hin as (Huid_ne & Hin).
    apply list_elem_of_lookup in Hin as (owner_i & Howner_lookup).
    pose proof (Hunique parent_i owner_i
      parent_reference owner_reference
      Hparent_lookup Howner_lookup
      Hparent_controller Hcontroller) as ->.
    rewrite Hparent_lookup in Howner_lookup.
    inversion Howner_lookup; subst owner_reference.
    done.
  }
  split.
  - exists parent_reference.
    split.
    + by apply list_elem_of_lookup_2 in Hparent_lookup.
    + done.
  - split; first exact Hno_controller.
    unfold valid_owner_references.
    split.
    + intros i1 i2 owner_reference1 owner_reference2
        Hlookup1 Hlookup2 Hcontroller1 Hcontroller2.
      apply list_find_None in Hno_controller.
      rewrite Forall_forall in Hno_controller.
      exfalso.
      apply (Hno_controller owner_reference1).
      * rewrite -list_elem_of_In.
        by apply list_elem_of_lookup_2 in Hlookup1.
      * exact Hcontroller1.
    + intros owner_reference Hin.
      unfold released_owner_references,
        owner_references_without_uid in Hin.
      apply list_elem_of_filter in Hin as (_ & Hin).
      by apply Hall_valid.
Qed.

Lemma release_pod_input_properties set pod owner_references :
  pod.(PodV.ObjectMeta').(ObjectMetaV.OwnerReferences') =
    Some owner_references →
  PodV.valid pod →
  meta_parent_ref pod.(PodV.ObjectMeta') =
    Some
      (StatefulSetV.key set,
       set.(StatefulSetV.ObjectMeta').(ObjectMetaV.UID')) →
  PodV.valid (release_pod_input set pod) ∧
  meta_parent_ref
    (release_pod_input set pod).(PodV.ObjectMeta') = None ∧
  ObjectMetaV.equiv_except_resource_version
    (pod.(PodV.ObjectMeta')
      <| ObjectMetaV.OwnerReferences' :=
        (release_pod_input set pod).(PodV.ObjectMeta').(
          ObjectMetaV.OwnerReferences') |>)
    (release_pod_input set pod).(PodV.ObjectMeta').
Proof.
  intros Howner_references Hvalid Hparent.
  destruct Hvalid as
    (Htypemeta & Hresource_version & Hmeta & Hspec & Hstatus).
  pose proof (ObjectMetaV.valid_owner_references_of_valid
    _ Hmeta) as Hvalid_owner_references.
  rewrite Howner_references in Hvalid_owner_references.
  pose proof (release_owner_references_facts
    pod.(PodV.ObjectMeta')
    (StatefulSetV.key set)
    set.(StatefulSetV.ObjectMeta').(ObjectMetaV.UID')
    owner_references
    Howner_references Hvalid_owner_references Hparent)
    as (_ & Hno_controller & Hvalid_released_owner_references).
  split.
  - split_and!; try done.
    unfold release_pod_input. simpl.
    unfold ObjectMetaV.valid in Hmeta |- *.
    simpl.
    destruct Hmeta as
      (Hgenerate_name & Hname_nonempty & Hname & Hnamespace_nonempty &
       Hnamespace & Huid & Hlabels & Hannotations & _ & Hfinalizers &
       Hmanaged_fields & Hself_link).
    split; [exact Hgenerate_name|].
    split; [exact Hname_nonempty|].
    split; [exact Hname|].
    split; [exact Hnamespace_nonempty|].
    split; [exact Hnamespace|].
    split; [exact Huid|].
    split; [exact Hlabels|].
    split; [exact Hannotations|].
    split.
    + rewrite Howner_references.
      exact Hvalid_released_owner_references.
    + split; [exact Hfinalizers|].
      split; [exact Hmanaged_fields|].
      exact Hself_link.
  - split.
    + unfold release_pod_input, meta_parent_ref. simpl.
      unfold owner_references_without_uid.
      rewrite Howner_references Hno_controller.
      done.
    + unfold release_pod_input,
        ObjectMetaV.equiv_except_resource_version,
        ObjectMetaV.without_resource_version.
      simpl.
      rewrite Howner_references.
      done.
Qed.

(* [wp_slice_literal] intentionally abstracts nil and empty non-nil slices
   together.  This strengthened local version retains the non-nil pointer
   produced by a Go slice literal, which is needed to represent the assigned
   ownerReferences field as [Some []] when every reference is removed. *)
Lemma wp_slice_literal_non_nil
    `[!ZeroVal V] `[!TypedPointsto V]
    `[!IntoValTyped V t] `{!st ↓u (go.SliceType t)}
    (l : list V) kvs Φ :
  let len := go.array_literal_size kvs in
  WP (CompositeLiteral (go.ArrayType len t) (LiteralValueV kvs))
    {{ v,
      ⌜ v = #(array.mk len l) ⌝ ∗
      (∀ sl_ptr,
        let sl := slice.mk sl_ptr (W64 len) (W64 len) in
        (⌜ sl_ptr ≠ null ⌝ ∗
         sl ↦* l ∗
         own_slice_cap V sl 1) -∗
        Φ #sl) }}
  -∗
  WP (CompositeLiteral st (LiteralValueV kvs)) {{ Φ }}.
Proof.
  iIntros "* HΦ".
  pose proof go.composite_literal_slice.
  wp_pures.
  destruct decide; last by iApply wp_AngelicExit.
  wp_pures. wp_alloc_auto.
  iDestruct (typed_pointsto_not_null with "tmp") as %Hsl_ptr_not_null.
  wp_pure. wp_pure.
  wp_apply (wp_wand with "HΦ").
  iIntros "% [-> HΦ]".
  wp_auto.
  rewrite -> decide_True by
    (enough (0 ≤ go.array_literal_size kvs) by word;
     unfold go.array_literal_size; destruct foldl; lia).
  wp_auto.
  iDestruct (array_len with "tmp") as %Hlen.
  rewrite !go.array_index_ref_0 /=.
  wp_end.
  - iSplit; first done.
    iDestruct (slice_array with "tmp") as "$".
    { simpl. word. }
    iApply own_slice_cap_empty; simpl; [done|word].
  - ereplace (word.sub ?[a] ?[b]) with (?a) by word.
    done.
Qed.

(* This is the intended controller call path: [pod] is a child of [set].
   Consequently [releasePod] finds the StatefulSet UID, performs the
   transactional update, and cannot observe NotFound.  The local [set] and
   [pod] are unchanged because the implementation updates a deep copy.  For a
   terminating Pod, Kubernetes may complete deletion during the update, so the
   result is either a live orphan or a tombstone.  In either case the Pod is no
   longer among the StatefulSet's children. *)
Lemma wp_releasePod γ model_l set_l pod_l
    (set : StatefulSetV.t) (pod : PodV.t)
    (children : gset KKey.t) dq_set dq_pod :
  {{{ "#Hpkg" ∷
        is_pkg_init code.controllers.statefulset.pkg_id.statefulset ∗
      "#Hisk" ∷ is_kubernetes γ model_l ∗
      "#Hglobal_l" ∷
        (global_addr apimodel.ModelState) ↦□ model_l ∗
      "Hset" ∷ StatefulSetV.deepown_l set_l set dq_set ∗
      "Hpod" ∷ PodV.deepown_l pod_l pod dq_pod ∗
      "%Hvalid_pod" ∷ ⌜ PodV.valid pod ⌝ ∗
      "%Hparent" ∷
        ⌜ meta_parent_ref pod.(PodV.ObjectMeta') =
          Some
            (StatefulSetV.key set,
             set.(StatefulSetV.ObjectMeta').(ObjectMetaV.UID')) ⌝ ∗
      "%Hkey_in" ∷ ⌜ PodV.key pod ∈ children ⌝ ∗
      "Hown_meta" ∷ own_meta_frag γ
        (PodV.key pod)
        pod.(PodV.ObjectMeta').(ObjectMetaV.UID') 1
        pod.(PodV.ObjectMeta') ∗
      "Hown_spec" ∷ own_spec_frag γ
        (PodV.key pod)
        pod.(PodV.ObjectMeta').(ObjectMetaV.UID') 1
        (ObjectSpecV.PodSpec pod.(PodV.Spec')) ∗
      "Hown_children" ∷ own_children_frag γ
        (StatefulSetV.key set)
        set.(StatefulSetV.ObjectMeta').(ObjectMetaV.UID') 1 children
  }}}
    @! statefulset.releasePod #set_l #pod_l
  {{{ RET #interface.nil;
      "Hset" ∷ StatefulSetV.deepown_l set_l set dq_set ∗
      "Hpod" ∷ PodV.deepown_l pod_l pod dq_pod ∗
      ( (∃ pod_meta',
          "Hown_meta" ∷ own_meta_frag γ
            (PodV.key pod)
            pod.(PodV.ObjectMeta').(ObjectMetaV.UID') 1
            pod_meta' ∗
          "Hown_spec" ∷ own_spec_frag γ
            (PodV.key pod)
            pod.(PodV.ObjectMeta').(ObjectMetaV.UID') 1
            (ObjectSpecV.PodSpec pod.(PodV.Spec')))
        ∨
        "Hown_tombstone" ∷ own_tombstone_frag γ
          pod.(PodV.ObjectMeta').(ObjectMetaV.UID')) ∗
      "Hown_children" ∷ own_children_frag γ
        (StatefulSetV.key set)
        set.(StatefulSetV.ObjectMeta').(ObjectMetaV.UID') 1
        (children ∖ {[PodV.key pod]})
  }}}.
Proof.
  wp_start as "H". iNamed "H". wp_auto.
  iAssert (is_pkg_init code.k8s_io.api.core.v1.pkg_id.v1)
    as "#Hcorev1".
  { iPkgInit. }
  iEval (rewrite /named) in "Hpod".
  iDestruct "Hpod" as (pod_phy) "[Hpod_ptr Hpod]".
  wp_apply (wp_Pod__DeepCopy
    (package_sem := object_core_v1_sem)
    (meta_v1_sem := object_meta_v1_sem)
    pod_l pod_phy pod dq_pod dq_pod
    with "[$Hcorev1 $Hpod_ptr $Hpod]").
  iIntros (updatedPod_l) "(HupdatedPod & Hpod_ptr & Hpod)".
  iAssert (PodV.deepown_l pod_l pod dq_pod)
    with "[Hpod_ptr Hpod]" as "Hpod".
  { iExists pod_phy. iFrame. }
  iPoseProof (PodV.deepown_l_split with "HupdatedPod") as
    "(%HupdatedPod_l_not_null & HupdatedPod_typemeta &
      HupdatedPod_objectmeta_l & HupdatedPod_spec_l &
      HupdatedPod_status_l)".
  iDestruct "HupdatedPod_objectmeta_l" as
    (updatedPod_meta_c)
    "[HupdatedPod_objectmeta_field HupdatedPod_objectmeta]".
  iNamedPrefix "HupdatedPod_objectmeta" "HupdatedPod_meta_".
  destruct pod.(PodV.ObjectMeta').(ObjectMetaV.OwnerReferences')
    as [owner_references|] eqn:Howner_references.
  2: {
    unfold meta_parent_ref in Hparent.
    rewrite Howner_references in Hparent.
    done.
  }
  pose proof Hvalid_pod as Hvalid_pod_parts.
  destruct Hvalid_pod_parts as
    (_ & _ & Hvalid_pod_meta & _).
  pose proof (ObjectMetaV.valid_owner_references_of_valid
    _ Hvalid_pod_meta) as Hvalid_owner_references.
  rewrite Howner_references in Hvalid_owner_references.
  pose proof (release_owner_references_facts
    pod.(PodV.ObjectMeta')
    (StatefulSetV.key set)
    set.(StatefulSetV.ObjectMeta').(ObjectMetaV.UID')
    owner_references Howner_references
    Hvalid_owner_references Hparent)
    as (Hmatching_owner_reference & _).
  iDestruct
    "HupdatedPod_meta_Hdeepown_ownerreferences_some"
    as (owner_reference_values)
      "[Howner_references Howner_reference_deepowns]".
  iPoseProof (StatefulSetV.deepown_l_split with "Hset") as
    "(%Hset_l_not_null & Hset_typemeta & Hset_objectmeta_l &
      Hset_spec_l & Hset_status_l)".
  iDestruct "Hset_objectmeta_l" as
    (set_meta_c) "[Hset_objectmeta_field Hset_objectmeta]".
  iNamedPrefix "Hset_objectmeta" "Hset_meta_".
  iCombineNamed "Hset_meta_*" as "Hset_objectmeta".
  iAssert (ObjectMetaV.deepown set_meta_c
      set.(StatefulSetV.ObjectMeta') dq_set)
    with "[Hset_objectmeta]" as "Hset_objectmeta".
  { iNamed "Hset_objectmeta". iFrame. done. }
  iAssert (ObjectMetaV.deepown_l
      (StatefulSetV.objectmeta_ptr set_l)
      set.(StatefulSetV.ObjectMeta') dq_set)
    with "[Hset_objectmeta_field Hset_objectmeta]"
    as "Hset_objectmeta_l".
  { iExists set_meta_c. iFrame. }
  iPoseProof (StatefulSetV.deepown_l_restore _ _ _
    Hset_l_not_null
    with "[$Hset_typemeta $Hset_objectmeta_l
      $Hset_spec_l $Hset_status_l]") as "Hset".
  wp_auto.
  wp_apply wp_slice_literal_non_nil.
  iSplitR; first done.
  iIntros (result_sl0)
    "(%Hresult_sl0_not_null & Hresult0 & Hown_result_cap)".
  set result0 := {|
    slice.ptr := result_sl0;
    slice.len := W64 (go.array_literal_size []);
    slice.cap := W64 (go.array_literal_size []);
  |}.
  wp_auto.
  iDestruct (own_slice_len with "Howner_references") as
    %(Howner_references_len1 & Howner_references_len2).
  iDestruct (own_slice_wf with "Howner_references") as
    %Howner_references_cap.
  iDestruct (big_sepL2_length with
    "Howner_reference_deepowns") as %Howner_reference_values_len.
  set set_uid :=
    set.(StatefulSetV.ObjectMeta').(ObjectMetaV.UID').
  set P := (λ owner_reference : OwnerReferenceV.t,
    owner_reference.(OwnerReferenceV.UID') ≠ set_uid).
  set I := (∃ (i : w64)
      (owner_reference_value : v1.OwnerReference.t)
      (result : slice.t)
      (result_values : list v1.OwnerReference.t)
      (released_value : bool),
    "Hi_ptr" ∷ i_ptr ↦ i ∗
    "Hset_ptr" ∷ set_ptr ↦ set_l ∗
    "Hset" ∷ StatefulSetV.deepown_l set_l set dq_set ∗
    "Howner_reference_ptr" ∷
      ownerReference_ptr ↦ owner_reference_value ∗
    "Hresult_ptr" ∷ ownerReferences_ptr ↦ result ∗
    "Hreleased_ptr" ∷ released_ptr ↦ released_value ∗
    "Hresult" ∷ result ↦* result_values ∗
    "Hlist_pre" ∷
      ([∗ list] owner_reference_value;owner_reference
        ∈ result_values;filter P (take (sint.nat i) owner_references),
        OwnerReferenceV.deepown
          owner_reference_value owner_reference 1) ∗
    "Hlist_post" ∷
      ([∗ list] owner_reference_value;owner_reference
        ∈ drop (sint.nat i) owner_reference_values;
          drop (sint.nat i) owner_references,
        OwnerReferenceV.deepown
          owner_reference_value owner_reference 1) ∗
    "Hown_result_cap" ∷
      own_slice_cap v1.OwnerReference.t result (DfracOwn 1) ∗
    "%Hresult_not_nil" ∷ ⌜ result ≠ slice.nil ⌝ ∗
    "%Hreleased" ∷
      ⌜ released_value = true ↔
        ∃ owner_reference,
          owner_reference ∈ take (sint.nat i) owner_references ∧
          owner_reference.(OwnerReferenceV.UID') = set_uid ⌝ ∗
    "%Hi" ∷
      ⌜ 0 ≤ sint.Z i ≤
        sint.Z (slice.len
          updatedPod_meta_c.(v1.ObjectMeta.OwnerReferences')) ⌝
  )%I.
  iAssert I with
    "[i set Hset ownerReference ownerReferences released
      Hresult0 Howner_reference_deepowns Hown_result_cap]"
    as "Hloop_inv".
  {
    iExists (W64 0), (zero_val v1.OwnerReference.t),
      result0, ([] : list v1.OwnerReference.t), false.
    rewrite !take_0 filter_nil !big_sepL2_nil !drop_0.
    iFrame.
    iSplit.
    {
      iPureIntro.
      intros Hresult0_nil.
      apply Hresult_sl0_not_null.
      exact (f_equal slice.ptr Hresult0_nil).
    }
    iSplit.
    { iPureIntro. split; [done|].
      intros (owner_reference & Hin & _).
      inversion Hin. }
    iPureIntro. word.
  }
  wp_for "Hloop_inv".
  wp_if_destruct.
  - list_elem owner_reference_values (sint.Z i)
      as this_owner_reference_value.
    destruct (decide
      (0 ≤ sint.Z i <
        sint.Z (slice.len
          updatedPod_meta_c.(v1.ObjectMeta.OwnerReferences'))))
      as [_|Hbounds]; last word.
    wp_apply (wp_load_slice_index with
      "[$Howner_references]"); [word| |].
    {
      iPureIntro.
      exact Hthis_owner_reference_value_lookup.
    }
    iIntros "Howner_references".
    wp_auto.
    assert (∃ this_owner_reference,
        owner_references !! sint.nat i =
          Some this_owner_reference)
      as [this_owner_reference Hthis_owner_reference_lookup].
    {
      apply lookup_lt_is_Some_2.
      rewrite -Howner_reference_values_len
        Howner_references_len1.
      word.
    }
    assert (Htake_next :
        take (S (sint.nat i)) owner_references =
          take (sint.nat i) owner_references ++
            [this_owner_reference]).
    {
      by apply take_S_r.
    }
    iPoseProof (big_sepL2_head_tail _ _ _
      this_owner_reference_value this_owner_reference
      with "Hlist_post") as "[Hthis Hother]".
    {
      split.
      all: rewrite lookup_drop Nat.add_0_r; done.
    }
    iNamedPrefix "Hthis" "Hthis_".
    iPoseProof (StatefulSetV.deepown_l_split with "Hset") as
      "(%Hset_l_not_null0 & Hset_typemeta &
        Hset_objectmeta_l & Hset_spec_l & Hset_status_l)".
    iDestruct "Hset_objectmeta_l" as
      (set_meta_c0)
      "[Hset_objectmeta_field Hset_objectmeta]".
    iNamedPrefix "Hset_objectmeta" "Hset_meta_".
    wp_auto.
    rewrite Hthis_Hdeepown_uid.
    match goal with
    | Huid : v1.ObjectMeta.UID' set_meta_c0 = _ |- _ =>
        rewrite Huid
    end.
    destruct (decide
      (this_owner_reference.(OwnerReferenceV.UID') = set_uid))
      as [Huid_eq|Huid_ne].
    + rewrite -> bool_decide_true by exact Huid_eq.
      wp_auto.
      iCombineNamed "Hset_meta_*" as "Hset_objectmeta".
      iAssert (ObjectMetaV.deepown set_meta_c0
          set.(StatefulSetV.ObjectMeta') dq_set)
        with "[Hset_objectmeta]" as "Hset_objectmeta".
      { iNamed "Hset_objectmeta". iFrame. done. }
      iAssert (ObjectMetaV.deepown_l
          (StatefulSetV.objectmeta_ptr set_l)
          set.(StatefulSetV.ObjectMeta') dq_set)
        with "[Hset_objectmeta_field Hset_objectmeta]"
        as "Hset_objectmeta_l".
      { iExists set_meta_c0. iFrame. }
      iPoseProof (StatefulSetV.deepown_l_restore _ _ _
        Hset_l_not_null0
        with "[$Hset_typemeta $Hset_objectmeta_l
          $Hset_spec_l $Hset_status_l]") as "Hset".
      iApply wp_for_post_continue.
      wp_auto.
      iFrame
        "HupdatedPod_meta_Hdeepown_creationtimestamp
         HupdatedPod_meta_Hdeepown_deletiontimestamp_some
         HupdatedPod_meta_Hdeepown_deletiongraceperiodseconds_some
         HupdatedPod_meta_Hdeepown_labels_some
         HupdatedPod_meta_Hdeepown_annotations_some
         HupdatedPod_meta_Hdeepown_finalizers_some
         HupdatedPod_meta_Hdeepown_managedfields_some".
      iFrame "updatedPod Howner_references Hpod Hown_meta Hown_spec
        Hown_children HupdatedPod_typemeta
        HupdatedPod_objectmeta_field HupdatedPod_spec_l
        HupdatedPod_status_l HΦ".
      iExists (word.add i (W64 1)),
        this_owner_reference_value, result, result_values, true.
      assert (¬ P this_owner_reference) as Hnot_P.
      {
        unfold P.
        intros Huid_ne'.
        exact (Huid_ne' Huid_eq).
      }
      assert (filter P (take (sint.nat i) owner_references) =
          filter P
            (take (sint.nat (word.add i (W64 1)))
              owner_references)) as <-.
      {
        assert (sint.nat (word.add i (W64 1)) =
            S (sint.nat i)) as -> by word.
        rewrite Htake_next.
        rewrite list.filter_app.
        assert (filter P [this_owner_reference] = []) as ->.
        { by apply filter_singleton_False. }
        rewrite app_nil_r. done.
      }
      assert (sint.nat (word.add i (W64 1)) =
          S (sint.nat i)) as Hnext by word.
      rewrite Hnext !drop_drop Nat.add_1_r.
      iFrame.
      iSplit.
      { iPureIntro. exact Hresult_not_nil. }
      iSplit.
      {
        iPureIntro. split; first intros _.
        - exists this_owner_reference.
          split; last exact Huid_eq.
          rewrite Htake_next.
          apply elem_of_app. right.
          by apply list_elem_of_singleton.
        - done.
      }
      iPureIntro. word.
    + rewrite -> bool_decide_false by exact Huid_ne.
      wp_auto.
      iAssert (OwnerReferenceV.deepown
          this_owner_reference_value this_owner_reference 1)
        with
          "[Hthis_Hdeepown_controller_some
            Hthis_Hdeepown_blockownerdeleton_some]"
        as "Hthis".
      {
        unfold OwnerReferenceV.deepown.
        iFrame. iFrame "%".
      }
      wp_apply wp_slice_literal.
      iSplitR; first done.
      iIntros (one_owner_reference_slice)
        "[Hone_owner_reference_slice _]".
      wp_auto.
      wp_apply (wp_slice_append with
        "[$Hresult $Hown_result_cap
          $Hone_owner_reference_slice]").
      iIntros (result')
        "(Hresult & Hown_result_cap &
          Hone_owner_reference_slice)".
      iDestruct (own_slice_len with "Hresult") as
        %(Hresult_len & _).
      assert (Hresult_not_nil' : result' ≠ slice.nil).
      {
        intros ->.
        rewrite length_app /= in Hresult_len.
        change (length result_values + 1 = 0)%nat in Hresult_len.
        lia.
      }
      wp_auto.
      iCombineNamed "Hset_meta_*" as "Hset_objectmeta".
      iAssert (ObjectMetaV.deepown set_meta_c0
          set.(StatefulSetV.ObjectMeta') dq_set)
        with "[Hset_objectmeta]" as "Hset_objectmeta".
      { iNamed "Hset_objectmeta". iFrame. done. }
      iAssert (ObjectMetaV.deepown_l
          (StatefulSetV.objectmeta_ptr set_l)
          set.(StatefulSetV.ObjectMeta') dq_set)
        with "[Hset_objectmeta_field Hset_objectmeta]"
        as "Hset_objectmeta_l".
      { iExists set_meta_c0. iFrame. }
      iPoseProof (StatefulSetV.deepown_l_restore _ _ _
        Hset_l_not_null0
        with "[$Hset_typemeta $Hset_objectmeta_l
          $Hset_spec_l $Hset_status_l]") as "Hset".
      iApply wp_for_post_do.
      wp_auto.
      iFrame
        "HupdatedPod_meta_Hdeepown_creationtimestamp
         HupdatedPod_meta_Hdeepown_deletiontimestamp_some
         HupdatedPod_meta_Hdeepown_deletiongraceperiodseconds_some
         HupdatedPod_meta_Hdeepown_labels_some
         HupdatedPod_meta_Hdeepown_annotations_some
         HupdatedPod_meta_Hdeepown_finalizers_some
         HupdatedPod_meta_Hdeepown_managedfields_some".
      iFrame "updatedPod Howner_references Hpod Hown_meta Hown_spec
        Hown_children HupdatedPod_typemeta
        HupdatedPod_objectmeta_field HupdatedPod_spec_l
        HupdatedPod_status_l HΦ".
      iExists (word.add i (W64 1)),
        this_owner_reference_value, result',
        (result_values ++ [this_owner_reference_value]),
        released_value.
      assert (P this_owner_reference) as Hthis_P.
      { unfold P, set_uid. exact Huid_ne. }
      assert (filter P (take (sint.nat i) owner_references) ++
          [this_owner_reference] =
          filter P
            (take (sint.nat (word.add i (W64 1)))
              owner_references)) as <-.
      {
        assert (sint.nat (word.add i (W64 1)) =
            S (sint.nat i)) as -> by word.
        rewrite Htake_next.
        rewrite list.filter_app.
        assert (filter P [this_owner_reference] =
            [this_owner_reference]) as ->.
        { by apply filter_singleton_True. }
        done.
      }
      iAssert
        (([∗ list] owner_reference_value0;owner_reference
          ∈ result_values ++ [this_owner_reference_value];
            filter P (take (sint.nat i) owner_references) ++
              [this_owner_reference],
          OwnerReferenceV.deepown
            owner_reference_value0 owner_reference 1))%I
        with "[Hlist_pre Hthis]" as "Hlist_pre".
      {
        iApply (big_sepL2_app with "[$Hlist_pre]").
        simpl. iFrame.
      }
      assert (sint.nat (word.add i (W64 1)) =
          S (sint.nat i)) as Hnext by word.
      rewrite Hnext !drop_drop Nat.add_1_r.
      iFrame.
      iSplit.
      { iPureIntro. exact Hresult_not_nil'. }
      iSplit.
      {
        iPureIntro.
        rewrite Hreleased.
        split.
        - intros
            (owner_reference & Hin & Howner_reference_uid).
          exists owner_reference.
          split; last exact Howner_reference_uid.
          rewrite Htake_next.
          by apply elem_of_app; left.
        - intros
            (owner_reference & Hin & Howner_reference_uid).
          rewrite Htake_next in Hin.
          apply elem_of_app in Hin as [Hin|Hin];
            first by eauto.
          rewrite list_elem_of_singleton in Hin.
          subst owner_reference.
          done.
      }
      iPureIntro. word.
  - assert (take (sint.nat i) owner_references =
        owner_references) as Htake_all.
    {
      assert (sint.nat i =
          length owner_reference_values) as Hi_len.
      {
        rewrite Howner_references_len1.
        word.
      }
      rewrite Howner_reference_values_len in Hi_len.
      rewrite Hi_len.
      apply take_ge. lia.
    }
    rewrite Htake_all in Hreleased.
    assert (released_value = true) as Hreleased_true.
    {
      apply Hreleased.
      exact Hmatching_owner_reference.
    }
    iEval (rewrite Htake_all) in "Hlist_pre".
    subst released_value.
    wp_auto.
    set released_owner_references :=
      owner_references_without_uid set_uid owner_references.
    assert (Hreleased_owner_references :
        filter P owner_references = released_owner_references).
    {
      unfold P, released_owner_references,
        owner_references_without_uid.
      done.
    }
    iEval (rewrite Hreleased_owner_references) in "Hlist_pre".
    iAssert
      (∃ owner_reference_values',
        result ↦* owner_reference_values' ∗
        ([∗ list] owner_reference_value;owner_reference
          ∈ owner_reference_values';released_owner_references,
          OwnerReferenceV.deepown
            owner_reference_value owner_reference 1))%I
      with "[Hresult Hlist_pre]" as "Hreleased_owner_references".
    {
      iExists result_values. iFrame.
    }
    assert (Hreleased_owner_references_none :
        result = slice.nil ↔
          Some released_owner_references = None).
    {
      split.
      - intros Hresult_nil.
        exfalso.
        exact (Hresult_not_nil Hresult_nil).
      - done.
    }
    set released_meta_c :=
      updatedPod_meta_c
        <| v1.ObjectMeta.OwnerReferences' := result |>.
    iAssert (ObjectMetaV.deepown released_meta_c
        (release_pod_input set pod).(PodV.ObjectMeta') 1)
      with
        "[Hreleased_owner_references
          HupdatedPod_meta_Hdeepown_creationtimestamp
          HupdatedPod_meta_Hdeepown_deletiontimestamp_some
          HupdatedPod_meta_Hdeepown_deletiongraceperiodseconds_some
          HupdatedPod_meta_Hdeepown_labels_some
          HupdatedPod_meta_Hdeepown_annotations_some
          HupdatedPod_meta_Hdeepown_finalizers_some
          HupdatedPod_meta_Hdeepown_managedfields_some]"
      as "Hreleased_meta".
    {
      unfold ObjectMetaV.deepown, release_pod_input.
      simpl.
      rewrite Howner_references.
      change
        (owner_references_without_uid
          (ObjectMetaV.UID' (StatefulSetV.ObjectMeta' set))
          owner_references)
        with released_owner_references.
      iFrame. iFrame "%".
    }
    iAssert (ObjectMetaV.deepown_l
        (PodV.objectmeta_ptr updatedPod_l)
        (release_pod_input set pod).(PodV.ObjectMeta') 1)
      with
        "[HupdatedPod_objectmeta_field Hreleased_meta]"
      as "Hreleased_meta_l".
    {
      iExists released_meta_c.
      iFrame.
    }
    iAssert (PodV.deepown_l updatedPod_l
        (release_pod_input set pod) 1)
      with
        "[HupdatedPod_typemeta Hreleased_meta_l
          HupdatedPod_spec_l HupdatedPod_status_l]"
      as "Hreleased_pod".
    {
      iApply (PodV.deepown_l_restore
        updatedPod_l (release_pod_input set pod) 1
        HupdatedPod_l_not_null).
      iFrame.
    }
    pose proof (release_pod_input_properties
      set pod owner_references
      Howner_references Hvalid_pod Hparent)
      as (Hreleased_pod_valid &
          Hreleased_pod_parent &
          Hreleased_pod_meta_update).
    assert (Hreleased_pod_namespace :
        (release_pod_input set pod).(PodV.ObjectMeta').(
          ObjectMetaV.Namespace') =
        pod.(PodV.ObjectMeta').(ObjectMetaV.Namespace')).
    { unfold release_pod_input. done. }
    assert (Hreleased_pod_key :
        PodV.key pod = PodV.key (release_pod_input set pod)).
    {
      unfold release_pod_input, PodV.key, PodV.meta_key.
      done.
    }
    assert (Hreleased_pod_uid :
        pod.(PodV.ObjectMeta').(ObjectMetaV.UID') =
        (release_pod_input set pod).(PodV.ObjectMeta').(
          ObjectMetaV.UID')).
    { unfold release_pod_input. done. }
    assert (Hreleased_pod_spec :
        (release_pod_input set pod).(PodV.Spec') =
          pod.(PodV.Spec')).
    { unfold release_pod_input. done. }
    assert (Hreleased_pod_valid_create :
        PodV.valid_named_create
          (release_pod_input set pod).(PodV.ObjectMeta').(
            ObjectMetaV.Namespace')
          (release_pod_input set pod)).
    { eapply PodV.valid_named_create_of_valid; done. }
    assert (Hreleased_pod_uid_nonempty :
        (release_pod_input set pod).(PodV.ObjectMeta').(
          ObjectMetaV.UID') ≠ ""%go).
    { destruct Hreleased_pod_valid as (_ & _ & Hmeta & _).
      eapply valid_uid_non_empty.
      eapply ObjectMetaV.valid_uid_of_valid. exact Hmeta. }
    rewrite HupdatedPod_meta_Hdeepown_namespace.
    iAssert (is_pkg_init apimodel) as "#Hapimodel".
    { iPkgInit. }
    wp_apply (wp_State__PodUpdateTx_release γ model_l
      (release_pod_input set pod).(PodV.ObjectMeta').(
        ObjectMetaV.Namespace')
      updatedPod_l (release_pod_input set pod)
      (PodV.key pod)
      pod.(PodV.ObjectMeta').(ObjectMetaV.UID')
      pod.(PodV.ObjectMeta')
      pod.(PodV.Spec')
      children
      (StatefulSetV.key set)
      set.(StatefulSetV.ObjectMeta').(ObjectMetaV.UID')
      1
      with
        "[$Hapimodel $Hisk $Hreleased_pod
          $Hown_meta $Hown_spec $Hown_children]").
    {
      iFrame "%".
    }
    iIntros (returned_pod_l returned_pod) "Hupdate".
    iDestruct "Hupdate" as
      "(_ & _ & _ & _ & _ & _ & Hreturned_pod &
        Hown_children & Hrelease_result)".
    wp_auto.
    wp_apply (wp_IsNotFound interface.nil with "[]").
    replace (bool_decide (not_found_error interface.nil))
      with false by
      (symmetry; apply bool_decide_false;
       exact not_found_error_nil).
    wp_auto.
    iDestruct "Hrelease_result" as
      "[(Hown_meta & Hown_spec) | Hown_tombstone]".
    + iApply "HΦ".
      iSplitL "Hset"; first iExact "Hset".
      iSplitL "Hpod"; first iExact "Hpod".
      iSplitL "Hown_meta Hown_spec".
      { iLeft. iExists returned_pod.(PodV.ObjectMeta'). iFrame. }
      iExact "Hown_children".
    + iApply "HΦ".
      iSplitL "Hset"; first iExact "Hset".
      iSplitL "Hpod"; first iExact "Hpod".
      iSplitL "Hown_tombstone"; first by iRight.
      iExact "Hown_children".
Qed.

Definition pods_with_bad_names
    (set : StatefulSetV.t) (pods : list PodV.t) : list PodV.t :=
  filter
    (λ pod,
      ¬ pod_has_int32_member_name
        set.(StatefulSetV.ObjectMeta').(ObjectMetaV.Name')
        pod.(PodV.ObjectMeta').(ObjectMetaV.Name'))
    pods.

Lemma bad_pod_key_not_in_prefix
    (Bad : PodV.t → Prop) `{∀ pod, Decision (Bad pod)}
    pods pod i :
  NoDup (PodV.key <$> filter Bad pods) →
  pods !! i = Some pod →
  Bad pod →
  PodV.key pod ∉ PodV.key <$> filter Bad (take i pods).
Proof.
  intros Hnodup Hlookup Hbad Hin.
  rewrite -(take_drop_middle pods i pod Hlookup) in Hnodup.
  rewrite list.filter_app
    (filter_cons_True Bad pod (drop (S i) pods) Hbad)
    fmap_app /= in Hnodup.
  apply list.NoDup_app in Hnodup as (_ & Hdisjoint & _).
  apply (Hdisjoint (PodV.key pod) Hin).
  by left.
Qed.

(* [releasePodsWithBadNames] leaves the input Go objects unchanged because
   [releasePod] updates a deep copy.  Each released Pod is either stored as a
   live orphan (with existential server-updated metadata) or has completed
   deletion and is represented by a tombstone. *)
Lemma wp_releasePodsWithBadNames γ model_l set_l pods_sl
    (set : StatefulSetV.t) (ptrs : list loc)
    (pods bad_name_pods : list PodV.t)
    (children : gset KKey.t) dq_set dq_pods :
  {{{ "#Hpkg" ∷
        is_pkg_init code.controllers.statefulset.pkg_id.statefulset ∗
      "#Hisk" ∷ is_kubernetes γ model_l ∗
      "#Hglobal_l" ∷
        (global_addr apimodel.ModelState) ↦□ model_l ∗
      "Hset" ∷ StatefulSetV.deepown_l set_l set dq_set ∗
      "Hpods_sl" ∷ pods_sl ↦* ptrs ∗
      "Hpods" ∷
        ([∗ list] ptr;pod ∈ ptrs;pods,
          PodV.deepown_l ptr pod dq_pods) ∗
      "%Hbad_name_pods" ∷
        ⌜ bad_name_pods = pods_with_bad_names set pods ⌝ ∗
      "Hown_meta" ∷
        ([∗ list] pod ∈ bad_name_pods,
          own_meta_frag γ
            (PodV.key pod)
            pod.(PodV.ObjectMeta').(ObjectMetaV.UID') 1
            pod.(PodV.ObjectMeta')) ∗
      "Hown_spec" ∷
        ([∗ list] pod ∈ bad_name_pods,
          own_spec_frag γ
            (PodV.key pod)
            pod.(PodV.ObjectMeta').(ObjectMetaV.UID') 1
            (ObjectSpecV.PodSpec pod.(PodV.Spec'))) ∗
      "Hown_children" ∷ own_children_frag γ
        (StatefulSetV.key set)
        set.(StatefulSetV.ObjectMeta').(ObjectMetaV.UID') 1
        children ∗
      "%Hname_lengths" ∷
        ⌜ Forall
          (λ pod,
            Z.of_nat
              (length
                pod.(PodV.ObjectMeta').(ObjectMetaV.Name')) ≤
            go_int_max)
          pods ⌝ ∗
      "%Hreleaseable" ∷
        ⌜ Forall
          (λ pod,
            PodV.valid pod ∧
            meta_parent_ref pod.(PodV.ObjectMeta') =
              Some
                (StatefulSetV.key set,
                 set.(StatefulSetV.ObjectMeta').(
                   ObjectMetaV.UID')) ∧
            PodV.key pod ∈ children)
          bad_name_pods ⌝
  }}}
    @! statefulset.releasePodsWithBadNames #set_l #pods_sl
  {{{ RET #interface.nil;
      "Hset" ∷ StatefulSetV.deepown_l set_l set dq_set ∗
      "Hpods_sl" ∷ pods_sl ↦* ptrs ∗
      "Hpods" ∷
        ([∗ list] ptr;pod ∈ ptrs;pods,
          PodV.deepown_l ptr pod dq_pods) ∗
      "Hreleased" ∷
        ([∗ list] pod ∈ bad_name_pods,
          ( (∃ pod_meta',
              own_meta_frag γ
                (PodV.key pod)
                pod.(PodV.ObjectMeta').(ObjectMetaV.UID') 1
                pod_meta' ∗
              own_spec_frag γ
                (PodV.key pod)
                pod.(PodV.ObjectMeta').(ObjectMetaV.UID') 1
                (ObjectSpecV.PodSpec pod.(PodV.Spec')))
            ∨
            own_tombstone_frag γ
              pod.(PodV.ObjectMeta').(ObjectMetaV.UID'))) ∗
      "Hown_children" ∷ own_children_frag γ
        (StatefulSetV.key set)
        set.(StatefulSetV.ObjectMeta').(ObjectMetaV.UID') 1
        (children ∖
          list_to_set (PodV.key <$> bad_name_pods))
  }}}.
Proof.
  wp_start as "H". iNamed "H".
  subst bad_name_pods.
  set Bad := (λ pod : PodV.t,
    ¬ pod_has_int32_member_name
      set.(StatefulSetV.ObjectMeta').(ObjectMetaV.Name')
      pod.(PodV.ObjectMeta').(ObjectMetaV.Name')).
  iEval (fold Bad) in "Hown_meta".
  iEval (fold Bad) in "Hown_spec".
  unfold pods_with_bad_names in Hreleaseable.
  fold Bad in Hreleaseable.
  iPoseProof (kview.own_meta_list_no_dup
    PodV.key PodV.ObjectMeta' (filter Bad pods)
    with "Hown_meta") as "%Hbad_name_pods_nodup".
  wp_auto.
  iDestruct (own_slice_len with "Hpods_sl") as
    %(Hpods_sl_len1 & Hpods_sl_len2).
  iDestruct (own_slice_wf with "Hpods_sl") as
    %Hpods_sl_cap.
  iDestruct (big_sepL2_length with "Hpods") as %Hpods_len.
  set I := (∃ (i : w64) (pod_ptr_value : loc),
    "Hi_ptr" ∷ i_ptr ↦ i ∗
    "Hset_ptr" ∷ set_ptr ↦ set_l ∗
    "Hset" ∷ StatefulSetV.deepown_l set_l set dq_set ∗
    "Hpod_ptr" ∷ pod_ptr ↦ pod_ptr_value ∗
    "Hpods_sl" ∷ pods_sl ↦* ptrs ∗
    "Hpods" ∷
      ([∗ list] ptr;pod ∈ ptrs;pods,
        PodV.deepown_l ptr pod dq_pods) ∗
    "Hreleased_done" ∷
      ([∗ list] pod ∈ filter Bad (take (sint.nat i) pods),
        ( (∃ pod_meta',
            own_meta_frag γ
              (PodV.key pod)
              pod.(PodV.ObjectMeta').(ObjectMetaV.UID') 1
              pod_meta' ∗
            own_spec_frag γ
              (PodV.key pod)
              pod.(PodV.ObjectMeta').(ObjectMetaV.UID') 1
              (ObjectSpecV.PodSpec pod.(PodV.Spec')))
          ∨
          own_tombstone_frag γ
            pod.(PodV.ObjectMeta').(ObjectMetaV.UID'))) ∗
    "Hown_meta_todo" ∷
      ([∗ list] pod ∈ filter Bad (drop (sint.nat i) pods),
        own_meta_frag γ
          (PodV.key pod)
          pod.(PodV.ObjectMeta').(ObjectMetaV.UID') 1
          pod.(PodV.ObjectMeta')) ∗
    "Hown_spec_todo" ∷
      ([∗ list] pod ∈ filter Bad (drop (sint.nat i) pods),
        own_spec_frag γ
          (PodV.key pod)
          pod.(PodV.ObjectMeta').(ObjectMetaV.UID') 1
          (ObjectSpecV.PodSpec pod.(PodV.Spec'))) ∗
    "Hown_children" ∷ own_children_frag γ
      (StatefulSetV.key set)
      set.(StatefulSetV.ObjectMeta').(ObjectMetaV.UID') 1
      (children ∖ list_to_set
        (PodV.key <$> filter Bad (take (sint.nat i) pods))) ∗
    "%Hi" ∷
      ⌜ 0 ≤ sint.Z i ≤ sint.Z (slice.len pods_sl) ⌝
  )%I.
  iAssert I with
    "[i set Hset pod Hpods_sl Hpods Hown_meta Hown_spec
      Hown_children]" as "Hloop_inv".
  {
    iExists (W64 0), (zero_val loc).
    rewrite !take_0 !drop_0 !filter_nil
      !big_sepL_nil
      fmap_nil list_to_set_nil difference_empty_L.
    iFrame.
    iPureIntro. word.
  }
  wp_for "Hloop_inv".
  wp_if_destruct.
  - list_elem ptrs (sint.Z i) as this_ptr.
    destruct (decide
      (0 ≤ sint.Z i < sint.Z (slice.len pods_sl)))
      as [_|Hbounds]; last word.
    wp_apply (wp_load_slice_index with
      "[$Hpods_sl]"); [word| |].
    {
      iPureIntro.
      exact Hthis_ptr_lookup.
    }
    iIntros "Hpods_sl".
    wp_auto.
    assert (∃ this_pod,
        pods !! sint.nat i = Some this_pod)
      as [this_pod Hthis_pod_lookup].
    {
      apply lookup_lt_is_Some_2.
      rewrite -Hpods_len Hpods_sl_len1.
      word.
    }
    iDestruct (big_sepL2_lookup_acc with "Hpods")
      as "[Hthis Hpods_restore]".
    { exact Hthis_ptr_lookup. }
    { exact Hthis_pod_lookup. }
    iPoseProof (PodV.deepown_l_split with "Hthis") as
      "(%Hthis_not_null & Hthis_typemeta &
        Hthis_objectmeta_l & Hthis_spec_l & Hthis_status_l)".
    iDestruct "Hthis_objectmeta_l" as
      (this_meta_c)
      "[Hthis_objectmeta_field Hthis_objectmeta]".
    iNamedPrefix "Hthis_objectmeta" "Hthis_meta_".
    iPoseProof (StatefulSetV.deepown_l_split with "Hset") as
      "(%Hset_l_not_null & Hset_typemeta &
        Hset_objectmeta_l & Hset_spec_l & Hset_status_l)".
    iDestruct "Hset_objectmeta_l" as
      (set_meta_c)
      "[Hset_objectmeta_field Hset_objectmeta]".
    iNamedPrefix "Hset_objectmeta" "Hset_meta_".
    wp_auto.
    rewrite Hset_meta_Hdeepown_name Hthis_meta_Hdeepown_name.
    wp_apply (wp_isMemberOf with "[]").
    {
      iPureIntro.
      rewrite Forall_forall in Hname_lengths.
      apply Hname_lengths.
      rewrite -list_elem_of_In.
      apply list_elem_of_lookup_2 in Hthis_pod_lookup.
      exact Hthis_pod_lookup.
    }
    iIntros (member) "%Hmember".
    iCombineNamed "Hset_meta_*" as "Hset_objectmeta".
    iAssert (ObjectMetaV.deepown set_meta_c
        set.(StatefulSetV.ObjectMeta') dq_set)
      with "[Hset_objectmeta]" as "Hset_objectmeta".
    { iNamed "Hset_objectmeta". iFrame. done. }
    iAssert (ObjectMetaV.deepown_l
        (StatefulSetV.objectmeta_ptr set_l)
        set.(StatefulSetV.ObjectMeta') dq_set)
      with "[Hset_objectmeta_field Hset_objectmeta]"
      as "Hset_objectmeta_l".
    { iExists set_meta_c. iFrame. }
    iPoseProof (StatefulSetV.deepown_l_restore _ _ _
      Hset_l_not_null
      with "[$Hset_typemeta $Hset_objectmeta_l
        $Hset_spec_l $Hset_status_l]") as "Hset".
    iCombineNamed "Hthis_meta_*" as "Hthis_objectmeta".
    iAssert (ObjectMetaV.deepown this_meta_c
        this_pod.(PodV.ObjectMeta') dq_pods)
      with "[Hthis_objectmeta]" as "Hthis_objectmeta".
    { iNamed "Hthis_objectmeta". iFrame. done. }
    iAssert (ObjectMetaV.deepown_l
        (PodV.objectmeta_ptr this_ptr)
        this_pod.(PodV.ObjectMeta') dq_pods)
      with "[Hthis_objectmeta_field Hthis_objectmeta]"
      as "Hthis_objectmeta_l".
    { iExists this_meta_c. iFrame. }
    iAssert (PodV.deepown_l this_ptr this_pod dq_pods)
      with
        "[Hthis_typemeta Hthis_objectmeta_l
          Hthis_spec_l Hthis_status_l]"
      as "Hthis".
    {
      iApply (PodV.deepown_l_restore
        this_ptr this_pod dq_pods Hthis_not_null).
      iFrame.
    }
    wp_if_destruct.
    + assert (¬ Bad this_pod) as Hthis_good.
      {
        unfold Bad.
        intros Hthis_bad.
        apply Hthis_bad.
        apply (proj1 Hmember).
        done.
      }
      assert (Htake_next :
          take (S (sint.nat i)) pods =
            take (sint.nat i) pods ++ [this_pod]).
      { by apply take_S_r. }
      assert (Hdrop_current :
          drop (sint.nat i) pods =
            this_pod :: drop (S (sint.nat i)) pods).
      { by apply drop_S. }
      assert (Hnext :
          sint.nat (word.add i (W64 1)) =
            S (sint.nat i)) by word.
      assert (Hfilter_take :
          filter Bad
              (take (sint.nat (word.add i (W64 1))) pods) =
            filter Bad (take (sint.nat i) pods)).
      {
        rewrite Hnext Htake_next list.filter_app.
        assert (filter Bad [this_pod] = []) as ->.
        { by apply filter_singleton_False. }
        by rewrite app_nil_r.
      }
      assert (Hfilter_drop :
          filter Bad (drop (sint.nat i) pods) =
            filter Bad
              (drop (sint.nat (word.add i (W64 1))) pods)).
      {
        rewrite Hnext Hdrop_current.
        by rewrite (filter_cons_False Bad this_pod
          (drop (S (sint.nat i)) pods) Hthis_good).
      }
      iPoseProof ("Hpods_restore" with "Hthis") as "Hpods".
      iApply wp_for_post_continue.
      wp_auto.
      iFrame "HΦ".
      iExists (word.add i (W64 1)), this_ptr.
      rewrite Hfilter_take -Hfilter_drop.
      iFrame.
      iPureIntro. word.
    + assert (Bad this_pod) as Hthis_bad.
      {
        unfold Bad.
        intros Hthis_good.
        pose proof (proj2 Hmember Hthis_good) as Hfalse.
        done.
      }
      assert (Htake_next :
          take (S (sint.nat i)) pods =
            take (sint.nat i) pods ++ [this_pod]).
      { by apply take_S_r. }
      assert (Hdrop_current :
          drop (sint.nat i) pods =
            this_pod :: drop (S (sint.nat i)) pods).
      { by apply drop_S. }
      iEval (rewrite Hdrop_current
        (filter_cons_True Bad this_pod
          (drop (S (sint.nat i)) pods) Hthis_bad))
        in "Hown_meta_todo".
      iDestruct "Hown_meta_todo" as
        "[Hown_meta_this Hown_meta_todo]".
      iEval (rewrite Hdrop_current
        (filter_cons_True Bad this_pod
          (drop (S (sint.nat i)) pods) Hthis_bad))
        in "Hown_spec_todo".
      iDestruct "Hown_spec_todo" as
        "[Hown_spec_this Hown_spec_todo]".
      assert (Hthis_in_bad_name_pods :
          this_pod ∈ filter Bad pods).
      {
        apply list_elem_of_filter.
        split; first exact Hthis_bad.
        by apply list_elem_of_lookup_2 in Hthis_pod_lookup.
      }
      rewrite Forall_forall in Hreleaseable.
      assert (Hthis_in_bad_name_pods_In :
          In this_pod (filter Bad pods)).
      {
        rewrite -list_elem_of_In.
        exact Hthis_in_bad_name_pods.
      }
      pose proof (Hreleaseable this_pod
        Hthis_in_bad_name_pods_In) as
        (Hthis_valid & Hthis_parent & Hthis_key_in).
      assert (Hthis_key_not_removed :
          PodV.key this_pod ∉
            PodV.key <$> filter Bad (take (sint.nat i) pods)).
      {
        eapply bad_pod_key_not_in_prefix;
          [exact Hbad_name_pods_nodup
          |exact Hthis_pod_lookup
          |exact Hthis_bad].
      }
      assert (Hthis_key_in_current :
          PodV.key this_pod ∈
            children ∖ list_to_set
              (PodV.key <$>
                filter Bad (take (sint.nat i) pods))).
      {
        apply elem_of_difference.
        split; first exact Hthis_key_in.
        rewrite elem_of_list_to_set.
        exact Hthis_key_not_removed.
      }
      wp_apply (wp_releasePod γ model_l
        set_l this_ptr set this_pod
        (children ∖ list_to_set
          (PodV.key <$> filter Bad
            (take (sint.nat i) pods)))
        dq_set dq_pods
        with
          "[$Hpkg $Hisk $Hglobal_l $Hset $Hthis
            $Hown_meta_this $Hown_spec_this
            $Hown_children]").
      {
        iFrame "%".
      }
      iIntros
        "(Hrelease_Hset & Hrelease_Hpod &
          Hrelease_result & Hrelease_Hown_children)".
      wp_auto.
      assert (Hnext :
          sint.nat (word.add i (W64 1)) =
            S (sint.nat i)) by word.
      assert (Hfilter_take :
          filter Bad
              (take (sint.nat (word.add i (W64 1))) pods) =
            filter Bad (take (sint.nat i) pods) ++ [this_pod]).
      {
        rewrite Hnext Htake_next list.filter_app.
        assert (filter Bad [this_pod] = [this_pod]) as ->.
        { by apply filter_singleton_True. }
        done.
      }
      assert (Hfilter_drop :
          filter Bad
              (drop (sint.nat (word.add i (W64 1))) pods) =
            filter Bad (drop (S (sint.nat i)) pods)).
      { by rewrite Hnext. }
      assert (Hchildren_next :
          (children ∖ list_to_set
              (PodV.key <$> filter Bad
                (take (sint.nat i) pods))) ∖
              {[PodV.key this_pod]} =
            children ∖ list_to_set
              (PodV.key <$> filter Bad
                (take (sint.nat
                  (word.add i (W64 1))) pods))).
      {
        rewrite Hfilter_take fmap_app /=.
        apply set_eq. intros key.
        rewrite !elem_of_difference !elem_of_list_to_set
          !elem_of_app !elem_of_singleton.
        Timeout 10 set_solver.
      }
      iEval (rewrite Hchildren_next Hfilter_take)
        in "Hrelease_Hown_children".
      iPoseProof ("Hpods_restore" with
        "Hrelease_Hpod") as "Hpods".
      iApply wp_for_post_do.
      wp_auto.
      iFrame "HΦ".
      iExists (word.add i (W64 1)), this_ptr.
      rewrite Hfilter_take Hfilter_drop.
      iFrame.
      simpl.
      iFrame.
      iPureIntro. word.
  - assert (Hindex_end :
        sint.nat i = length pods).
    {
      rewrite -Hpods_len Hpods_sl_len1.
      word.
    }
    assert (Htake_all :
        take (sint.nat i) pods = pods).
    {
      rewrite Hindex_end.
      apply take_ge. lia.
    }
    assert (Hdrop_all :
        drop (sint.nat i) pods = []).
    {
      rewrite Hindex_end.
      apply drop_ge. lia.
    }
    iEval (rewrite Htake_all)
      in "Hreleased_done Hown_children".
    iEval (rewrite Hdrop_all filter_nil !big_sepL_nil)
      in "Hown_meta_todo Hown_spec_todo".
    iApply "HΦ".
    unfold pods_with_bad_names, Bad.
    iFrame.
Qed.

End proof.
