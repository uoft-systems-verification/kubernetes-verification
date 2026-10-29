From New.proof.controllers Require Import client_tactics.
From New.proof Require Import wp_keep.
From New.proof.controllers.statefulset Require Export pod_predicates.
From New.proof.controllers.statefulset Require Export ordinal.
From New.proof.k8s_io.api.core Require Export v1.
From New.proof.kubernetes_model.tx Require Export update_release.

Local Transparent ObjectMetaV.deepown ObjectMetaView.ObjectMetaV.deepown.

(* Collect transient allocations from imports before checking large program proofs. *)
Optimize Heap.

Section proof.
Context `{hG: !heapGS Σ} `{!ffi_semantics _ _}.
Context {sem : go.Semantics}
  {package_sem : code.controllers.statefulset.statefulset.Assumptions}.
Context {model_sem : apimodel.Assumptions}.
Context {client_ctx : code.context.context.Context.t} {kube_client : loc}.
Collection W := sem + package_sem + model_sem.
#[local] Instance base_common_sem : common.Assumptions | 100 :=
  code.controllers.statefulset.statefulset.import_common_Assumption.
#[local] Instance controller_sem : controller.Assumptions :=
  code.controllers.statefulset.statefulset.import_controller_Assumption.
#[local] Instance runtime_sem :
    code.k8s_io.apimachinery.pkg.runtime.runtime.Assumptions :=
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
Context `{!KObjectV.ObjectInterfaceAssumptions}.
Local Set Default Proof Using "All - client_ctx - kube_client".

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
  assert (valid_owner_references
      pod.(PodV.ObjectMeta').(ObjectMetaV.OwnerReferences'))
    as Hvalid_owner_references.
  { unfold ObjectMetaV.valid in Hmeta. tauto. }
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
  wp_pures_keep.
  destruct decide; last by iApply wp_AngelicExit.
  wp_pures_keep. wp_alloc_auto.
  iDestruct (typed_pointsto_not_null with "tmp") as %Hsl_ptr_not_null.
  wp_pure. wp_pure.
  wp_apply (wp_wand with "HΦ").
  iIntros "% [-> HΦ]".
  wp_auto_keep.
  rewrite -> decide_True by
    (enough (0 ≤ go.array_literal_size kvs) by word;
     unfold go.array_literal_size; destruct foldl; lia).
  wp_auto_keep.
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

(* The local [set] and [pod] stay unchanged because [releasePod] updates a deep
   copy. A living child follows the strong kview path and is removed from the
   living-child set. A terminating child instead uses its persistent deletion
   observation; its update may fail, and it never requires meta/spec ownership. *)
Lemma wp_releasePod_combined γ model_l set_l pod_l
    (set : StatefulSetV.t) (pod : PodV.t)
    (children : gset KKey.t) dq_set dq_pod (terminating : bool)
    (terminating_bound : nat) pod_orphans :
  {{{ "#Hpkg" ∷
        is_pkg_init code.controllers.statefulset.pkg_id.statefulset ∗
      "#Hisk" ∷ is_kubernetes γ model_l ∗
      "#Hglobal_l" ∷
        (global_addr apimodel.ModelState) ↦□ model_l ∗
      "#Hmodel_init" ∷ is_pkg_init apimodel ∗
      "Hset" ∷ StatefulSetV.deepown_l set_l set dq_set ∗
      "Hpod" ∷ PodV.deepown_l pod_l pod dq_pod ∗
      "%Hvalid_pod" ∷ ⌜ PodV.valid pod ⌝ ∗
      "%Hparent" ∷
        ⌜ meta_parent_ref pod.(PodV.ObjectMeta') =
          Some
            (StatefulSetV.key set,
             set.(StatefulSetV.ObjectMeta').(ObjectMetaV.UID')) ⌝ ∗
      "Hrelease_ownership" ∷
        (if terminating then
          ⌜ pod.(PodV.ObjectMeta').(ObjectMetaV.DeletionTimestamp') ≠ None ⌝ ∗
          own_deletion_observed_frag γ (PodV.key pod) pod.(PodV.ObjectMeta').(ObjectMetaV.UID') ∗
          own_terminating_children_frag γ (StatefulSetV.key set)
            set.(StatefulSetV.ObjectMeta').(ObjectMetaV.UID') terminating_bound
        else
          ⌜ PodV.key pod ∈ children ⌝ ∗
          own_meta_frag γ (PodV.key pod) pod.(PodV.ObjectMeta').(ObjectMetaV.UID') 1 pod.(PodV.ObjectMeta') ∗
          own_spec_frag γ (PodV.key pod) pod.(PodV.ObjectMeta').(ObjectMetaV.UID') 1
            (ObjectSpecV.PodSpec pod.(PodV.Spec')) ∗
          own_children_frag γ (StatefulSetV.key set)
            set.(StatefulSetV.ObjectMeta').(ObjectMetaV.UID') 1 children)%I ∗
      "Hown_pod_orphans" ∷ own_orphans_frag γ
        (PodV.kind, set.(StatefulSetV.ObjectMeta').(ObjectMetaV.Namespace'))
        (DfracOwn 1) pod_orphans
  }}}
    @! statefulset.releasePod #client_ctx #kube_client #set_l #pod_l
  {{{ (err : interface.t), RET #err;
      "%Herr" ∷ ⌜ terminating = false → err = interface.nil ⌝ ∗
      "Hset" ∷ StatefulSetV.deepown_l set_l set dq_set ∗
      "Hpod" ∷ PodV.deepown_l pod_l pod dq_pod ∗
      (if terminating then
        own_terminating_children_frag γ (StatefulSetV.key set)
          set.(StatefulSetV.ObjectMeta').(ObjectMetaV.UID') terminating_bound
      else
        own_children_frag γ (StatefulSetV.key set)
          set.(StatefulSetV.ObjectMeta').(ObjectMetaV.UID') 1
          (children ∖ {[PodV.key pod]}) ∗
        ∃ pod', ⌜ PodV.key pod' = PodV.key pod ⌝ ∗
          ⌜ PodV.updated pod.(PodV.Spec') (release_pod_input set pod) pod' ⌝ ∗
          own_meta_frag γ (PodV.key pod') pod'.(PodV.ObjectMeta').(ObjectMetaV.UID') 1
            pod'.(PodV.ObjectMeta') ∗
          own_spec_frag γ (PodV.key pod') pod'.(PodV.ObjectMeta').(ObjectMetaV.UID') 1
            (ObjectSpecV.PodSpec pod'.(PodV.Spec')))%I ∗
      "Hown_pod_orphans" ∷ own_orphans_frag γ
        (PodV.kind, set.(StatefulSetV.ObjectMeta').(ObjectMetaV.Namespace'))
        (DfracOwn 1) (if terminating then pod_orphans else pod_orphans ∪ {[PodV.key pod]})
  }}}.
Proof.
  wp_start as "H". iNamed "H". wp_auto_keep.
  iPersist "ctx". iPersist "kubeClient".
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
  assert (valid_owner_references
      pod.(PodV.ObjectMeta').(ObjectMetaV.OwnerReferences'))
    as Hvalid_owner_references.
  { unfold ObjectMetaV.valid in Hvalid_pod_meta. tauto. }
  rewrite Howner_references in Hvalid_owner_references.
  pose proof (release_owner_references_facts
    pod.(PodV.ObjectMeta')
    (StatefulSetV.key set)
    set.(StatefulSetV.ObjectMeta').(ObjectMetaV.UID')
    owner_references Howner_references
    Hvalid_owner_references Hparent)
    as (Hmatching_owner_reference & _).
  iDestruct
    "HupdatedPod_meta_Hdeepown_ownerreferences"
    as "(_ & %owner_reference_values & Howner_references & _ & Howner_reference_deepowns)".
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
  wp_auto_keep.
  wp_apply wp_slice_literal_non_nil.
  iSplitR; first done.
  iIntros (result_sl0)
    "(%Hresult_sl0_not_null & Hresult0 & Hown_result_cap)".
  set result0 := {|
    slice.ptr := result_sl0;
    slice.len := W64 (go.array_literal_size []);
    slice.cap := W64 (go.array_literal_size []);
  |}.
  wp_auto_keep.
  iDestruct (own_slice_len with "Howner_references") as
    %(Howner_references_len1 & Howner_references_len2).
  iDestruct (own_slice_wf with "Howner_references") as
    %Howner_references_cap.
  iDestruct (big_sepL2_length with
    "Howner_reference_deepowns") as %Howner_reference_values_len.
  rewrite ?Howner_references /= in Howner_reference_values_len.
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
    wp_auto_keep.
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
    wp_auto_keep.
    rewrite Hthis_Hdeepown_uid.
    match goal with
    | Huid : v1.ObjectMeta.UID' set_meta_c0 = _ |- _ =>
        rewrite Huid
    end.
    destruct (decide
      (this_owner_reference.(OwnerReferenceV.UID') = set_uid))
      as [Huid_eq|Huid_ne].
    + rewrite -> bool_decide_true by exact Huid_eq.
      wp_auto_keep.
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
      wp_auto_keep.
      iFrame
        "HupdatedPod_meta_Hdeepown_creationtimestamp
         HupdatedPod_meta_Hdeepown_deletiontimestamp_some
         HupdatedPod_meta_Hdeepown_deletiongraceperiodseconds_some
         HupdatedPod_meta_Hdeepown_labels_some
         HupdatedPod_meta_Hdeepown_annotations_some
         HupdatedPod_meta_Hdeepown_finalizers_some
         HupdatedPod_meta_Hdeepown_managedfields
         HupdatedPod_meta_Hdeepown_finalizers_cap".
      iFrame "updatedPod Howner_references Hpod Hrelease_ownership Hown_pod_orphans HupdatedPod_typemeta
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
      wp_auto_keep.
      iAssert (OwnerReferenceV.deepown
          this_owner_reference_value this_owner_reference 1)
        with
          "[Hthis_Hdeepown_controller_some
            Hthis_Hdeepown_blockownerdeletion_some]"
        as "Hthis".
      {
        unfold OwnerReferenceV.deepown.
        iFrame. iFrame "%".
      }
      wp_apply wp_slice_literal.
      iSplitR; first done.
      iIntros (one_owner_reference_slice)
        "[Hone_owner_reference_slice _]".
      wp_auto_keep.
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
      wp_auto_keep.
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
      wp_auto_keep.
      iFrame
        "HupdatedPod_meta_Hdeepown_creationtimestamp
         HupdatedPod_meta_Hdeepown_deletiontimestamp_some
         HupdatedPod_meta_Hdeepown_deletiongraceperiodseconds_some
         HupdatedPod_meta_Hdeepown_labels_some
         HupdatedPod_meta_Hdeepown_annotations_some
         HupdatedPod_meta_Hdeepown_finalizers_some
         HupdatedPod_meta_Hdeepown_managedfields
         HupdatedPod_meta_Hdeepown_finalizers_cap".
      iFrame "updatedPod Howner_references Hpod Hrelease_ownership Hown_pod_orphans HupdatedPod_typemeta
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
    wp_auto_keep.
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
    iAssert (deepown_slice OwnerReferenceV.deepown result (Some released_owner_references) 1)%I
      with "[Hresult Hlist_pre Hown_result_cap]" as "Hreleased_owner_references".
    { rewrite /deepown_slice. iSplit; first done. iExists result_values. iFrame. }
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
          HupdatedPod_meta_Hdeepown_managedfields
          HupdatedPod_meta_Hdeepown_finalizers_cap]"
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
        PodV.valid_update_input PodV.kind
          (release_pod_input set pod).(PodV.ObjectMeta').(
            ObjectMetaV.Namespace')
          (release_pod_input set pod)).
    { eapply PodV.valid_update_input_of_valid; done. }
    assert (Hreleased_pod_name_nonempty :
        (release_pod_input set pod).(PodV.ObjectMeta').(
          ObjectMetaV.Name') ≠ ""%go).
    { destruct Hreleased_pod_valid as (_ & _ & Hmeta & _).
      unfold ObjectMetaV.valid in Hmeta. tauto. }
    assert (Hreleased_pod_valid_typemeta :
        valid_typemeta PodV.kind (release_pod_input set pod).(PodV.TypeMeta')).
    { destruct Hreleased_pod_valid as (Htypemeta & _). exact Htypemeta. }
    assert (Hreleased_pod_uid_nonempty :
        (release_pod_input set pod).(PodV.ObjectMeta').(
          ObjectMetaV.UID') ≠ ""%go).
    { destruct Hreleased_pod_valid as (_ & _ & Hmeta & _).
      eapply valid_uid_non_empty.
      unfold ObjectMetaV.valid in Hmeta. tauto. }
    assert (Hreleased_pod_resource_version_valid :
        valid_resource_version
          (release_pod_input set pod).(PodV.ObjectMeta').(
            ObjectMetaV.ResourceVersion')).
    { destruct Hreleased_pod_valid as (_ & Hresource_version & _).
      exact Hresource_version. }
    assert (Hreleased_pod_meta_valid_update :
        ObjectMetaV.valid_update pod.(PodV.ObjectMeta')
          (release_pod_input set pod).(PodV.ObjectMeta')).
    { destruct Hreleased_pod_valid as (_ & _ & Hmeta & _).
      rewrite /ObjectMetaV.valid_update.
      destruct Hmeta as (_ & _ & _ & _ & _ & _ & Hreleased_meta_labels_valid &
        Hreleased_meta_annotations_valid & Hreleased_meta_owner_references_valid &
        Hreleased_meta_finalizers_valid & Hreleased_meta_managed_fields_valid & _).
      split.
      - right. exact Hreleased_pod_meta_update.
      - split_and!; done. }
    assert (Hreleased_pod_spec_valid_update :
        PodSpecV.valid_update pod.(PodV.Spec')
          (release_pod_input set pod).(PodV.Spec')).
    { rewrite Hreleased_pod_spec.
      apply PodSpecV.valid_update_refl.
      destruct Hreleased_pod_valid as (_ & _ & _ & Hspec & _).
      exact (proj1 Hspec). }
    assert (Hreleased_pod_valid_update :
        KObjectV.valid_update PodV.kind
          (release_pod_input set pod).(PodV.ObjectMeta').(ObjectMetaV.Namespace')
          pod.(PodV.ObjectMeta') (ObjectSpecV.PodSpec pod.(PodV.Spec'))
          (KObjectV.Pod (release_pod_input set pod))).
    { rewrite /KObjectV.valid_update /= /PodV.valid_update.
      split_and!; try done.
      destruct Hreleased_pod_valid as (_ & _ & _ & [Hspec Hannotations] & _).
      pose proof Hspec as (_ & _ & Hfixed & _).
      rewrite /release_pod_input /= in Hannotations, Hfixed |- *.
      rewrite Hfixed. exact Hannotations. }
    rewrite HupdatedPod_meta_Hdeepown_namespace.
    iAssert (is_pkg_init apimodel) as "#Hapimodel".
    { iPkgInit. }
    destruct terminating.
    + iSimpl in "Hrelease_ownership".
      assert (PodV.valid_body (release_pod_input set pod)) as Hreleased_pod_valid_body.
      { destruct Hreleased_pod_valid as (_ & _ & _ & Hbody & _). exact Hbody. }
      iDestruct "Hrelease_ownership" as
        "(%Hterminating & #Hown_deletion_observed_frag & Hown_terminating_children_frag)".
      iEval (rewrite Hreleased_pod_key Hreleased_pod_uid) in "Hown_deletion_observed_frag".
      wp_client_model.
      wp_apply (wp_State__PodUpdateTx_release_terminating γ model_l
        (release_pod_input set pod).(PodV.ObjectMeta').(ObjectMetaV.Namespace')
        updatedPod_l (release_pod_input set pod)
        with "[$Hapimodel $Hisk $Hreleased_pod $Hown_deletion_observed_frag]").
      { iFrame "%". }
      iIntros (returned_pod_l err) "_". wp_controller_auto.
      wp_apply (wp_IsNotFound err with "[]").
      destruct (decide (not_found_error err)) as [Hnot_found|Hnot_found].
      * replace (bool_decide (not_found_error err)) with true by
          (symmetry; apply bool_decide_true; exact Hnot_found).
        wp_auto_keep. iApply ("HΦ" $! interface.nil). iFrame. done.
      * replace (bool_decide (not_found_error err)) with false by
          (symmetry; apply bool_decide_false; exact Hnot_found).
        wp_auto_keep. iApply ("HΦ" $! err). iFrame. done.
    + iSimpl in "Hrelease_ownership".
      iDestruct "Hrelease_ownership" as
        "(%Hkey_in & Hown_meta & Hown_spec & Hown_children)".
      (* The released Pod becomes an orphan in the StatefulSet's namespace. *)
      assert (pod.(PodV.ObjectMeta').(ObjectMetaV.Namespace') =
        set.(StatefulSetV.ObjectMeta').(ObjectMetaV.Namespace')) as Hpod_namespace.
      { rewrite /meta_parent_ref Howner_references in Hparent.
        by destruct (list_find _ owner_references) as [[]|]; inversion Hparent. }
      iEval (rewrite -Hpod_namespace) in "Hown_pod_orphans".
      wp_client_model.
      wp_apply (wp_State__PodUpdateTx_release γ model_l
        (release_pod_input set pod).(PodV.ObjectMeta').(ObjectMetaV.Namespace')
        updatedPod_l (release_pod_input set pod)
        (PodV.key pod) pod.(PodV.ObjectMeta').(ObjectMetaV.UID')
        pod.(PodV.ObjectMeta') pod.(PodV.Spec') children pod_orphans
        (StatefulSetV.key set) set.(StatefulSetV.ObjectMeta').(ObjectMetaV.UID') 1
        with "[$Hapimodel $Hisk $Hreleased_pod $Hown_meta $Hown_spec $Hown_children
          $Hown_pod_orphans]").
      { iFrame "%". }
      iIntros (returned_pod_l returned_pod) "Hupdate".
      iDestruct "Hupdate" as
        "(_ & %Hreturned_updated & %Hreturned_spec_eq & _ & %Hreturned_key & %Hreturned_uid &
          Hreturned_pod & Hown_children & Hown_orphans_frag & Hreturned_meta & Hreturned_spec)".
      iEval (rewrite /own_orphans_frag_of /orphan_view.bucket_of /= Hpod_namespace) in "Hown_orphans_frag".
      iEval (rewrite -Hreturned_key -Hreturned_uid) in "Hreturned_meta Hreturned_spec".
      iEval (rewrite -Hreturned_spec_eq) in "Hreturned_spec".
      wp_controller_auto.
      wp_apply (wp_IsNotFound interface.nil with "[]").
      replace (bool_decide (not_found_error interface.nil)) with false by
        (symmetry; apply bool_decide_false; exact not_found_error_nil).
      wp_auto_keep.
      iApply ("HΦ" $! interface.nil). iFrame "∗ %". done.
Qed.

End proof.
