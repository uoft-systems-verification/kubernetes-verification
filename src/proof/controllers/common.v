From New.proof Require Import prelude empty_ffi.
From New.proof.kubernetes_model Require Export index.
From New.proof Require Export util.
From New.proof.controllers Require Export common_init.
From New.proof.k8s_io.kubernetes.pkg Require Export controller.
From New.proof.k8s_io.apimachinery.pkg.runtime Require Export schema.
From New.proof.k8s_io.apimachinery.pkg.api Require Export errors.

Section proof.
Context `{hG: !heapGS Σ} {go_ctx: GoContext}.
Context `{!kubernetesModelG Σ}.

Definition is_pod_alive (pod: PodV.t): Prop :=
  pod.(PodV.ObjectMeta').(ObjectMetaV.DeletionTimestamp') = None.

Definition delete_options_with_uid (uid : types.UID.t) : DeleteOptionsV.t :=
  {|
    DeleteOptionsV.TypeMeta' := default_val _;
    DeleteOptionsV.GracePeriodSeconds' := None;
    DeleteOptionsV.Preconditions' := Some {|
      PreconditionsV.UID' := Some uid;
      PreconditionsV.ResourceVersion' := None;
    |};
    DeleteOptionsV.OrphanDependents' := None;
    DeleteOptionsV.PropagationPolicy' := None;
  |}.

Lemma wp_NewDeleteOptionsWithUID uid :
  {{{ is_pkg_init code.controllers.common.common }}}
    @! common.NewDeleteOptionsWithUID #uid
  {{{ options, RET #options;
      DeleteOptionsV.deepown options (delete_options_with_uid uid) 1 ∗
      ⌜ DeleteOptionsV.valid (delete_options_with_uid uid)⌝
  }}}.
Proof. Admitted.
  (* wp_start as "H".
  wp_alloc uid_ptr as "Huid_ptr".
  wp_auto.
  wp_alloc preconditions_ptr as "Hpreconditions_ptr".
  wp_auto.
  iAssert (⌜ uid_ptr ≠ null ⌝%I) as "%Huid_ptr_not_null".
  { iDestruct (typed_pointsto_not_null with "Huid_ptr") as %H; [done|]. done. }
  iAssert (⌜ preconditions_ptr ≠ null ⌝%I) as "%Hpreconditions_ptr_not_null".
  { iDestruct (typed_pointsto_not_null with "Hpreconditions_ptr") as %H; [done|]. done. }
  iApply "HΦ".
  rewrite /delete_options_with_uid /DeleteOptionsV.deepown /PreconditionsV.deepown /=.
  iFrame.
  iPureIntro.
  split_and!; naive_solver.
Qed. *)

Lemma deepown_preserves_deletion_timestamp_activeness pod pure_pod dq:
  PodV.deepown pod pure_pod dq -∗
    ⌜ pod.(v1.Pod.ObjectMeta').(v1.ObjectMeta.DeletionTimestamp') = null ↔
      is_pod_alive pure_pod ⌝.
Proof.
  iIntros "H". iNamed "H". iNamed "Hdeepown_objectmeta".
  iPureIntro. unfold is_pod_alive.
  rewrite Hdeepown_deletiontimestamp_none. done.
Qed.

Lemma wp_FilterActivePods sl ptrs pods dq :
  {{{ is_pkg_init code.controllers.common.common ∗
      "Hsl" ∷ sl ↦* ptrs ∗
      "Hdeepown_l_pods" ∷ ([∗ list] ptr;pod ∈ ptrs;pods, PodV.deepown_l ptr pod dq)
  }}}
    @! common.FilterActivePods #sl
  {{{ sl' ptrs', RET #sl';
      sl' ↦* ptrs' ∗
      ([∗ list] ptr;pod ∈ ptrs';filter is_pod_alive pods, PodV.deepown_l ptr pod dq)
  }}}.
Proof.
  wp_start as "H". iNamed "H". wp_auto.
  iPoseProof own_slice_nil as "Hslice_nil".
  iPoseProof own_slice_cap_nil as "Hown_slice_nil_cap".
  iDestruct (own_slice_len with "Hsl") as %(Hsl_len1 & Hsl_len2).
  iDestruct (own_slice_wf with "Hsl") as %Hsl_cap.
  iDestruct (big_sepL2_length with "Hdeepown_l_pods") as %Hlen.
  set I := (∃ (i: w64) (p: loc) (result: slice.t) (ptrs': list loc),
    "Hi_ptr" ∷ i_ptr ↦ i ∗
    "Hp_ptr" ∷ p_ptr ↦ p ∗
    "Hresult_ptr" ∷ result_ptr ↦ result ∗
    "Hresult" ∷ result ↦* ptrs' ∗
    "Hlist_pre" ∷ ([∗ list] ptr;pod ∈ ptrs';filter is_pod_alive (take (sint.nat i) pods),
      PodV.deepown_l ptr pod dq) ∗
    "Hlist_post" ∷ ([∗ list] ptr;pod ∈ (drop (sint.nat i) ptrs);(drop (sint.nat i) pods),
      PodV.deepown_l ptr pod dq) ∗
    "Hown_result_cap" ∷ own_slice_cap loc result (DfracOwn 1) ∗
    "%Hi" ∷ ⌜ 0 ≤ sint.Z i ≤ sint.Z (slice.len_f sl) ⌝
  )%I.
  iAssert (I) with "[i result p Hdeepown_l_pods]" as "Hloop_inv".
  { iExists (W64 0), (default_val loc), slice.nil, [].
    iFrame. iFrame "#".
    rewrite !take_0 !filter_nil !big_sepL2_nil. done. }
  wp_for "Hloop_inv".
  wp_if_destruct.
  - wp_pure; first word.
    list_elem ptrs (sint.Z i) as this_ptr.
    wp_apply (wp_load_slice_elem with "[$Hsl]"); [word|eauto| ]. iIntros "Hsl". wp_auto.
    assert (∃ this_pod, pods !! sint.nat i = Some this_pod) as [this_pod Hthis_pod_lookup].
    { apply lookup_lt_is_Some_2. rewrite -Hlen Hsl_len1. word. }
    iPoseProof (big_sepL2_head_tail _ _ _ this_ptr this_pod with "Hlist_post") as "[Hthis Hother]".
    { split. all: rewrite lookup_drop Nat.add_0_r; done. }
    iDestruct "Hthis" as (this_pod_c) "[Hthis_ptr Hthis_pod]".
    iDestruct (deepown_preserves_deletion_timestamp_activeness with "Hthis_pod") as %Hactive.
    iDestruct (struct_fields_split with "Hthis_ptr") as "Hthis_fields".
    iNamed "Hthis_fields".
    wp_auto.
    wp_if_destruct.
    + assert (is_pod_alive this_pod) as Hpod_active.
      { apply Hactive. done. }
      wp_apply wp_slice_literal. iIntros (sl0) "Hsl0". wp_auto.
      wp_apply (wp_slice_append with "[$Hresult $Hown_result_cap $Hsl0]").
      iIntros (result') "(Hresult & Hown_result_cap & Hsl0)". wp_auto.
      iDestruct (struct_fields_combine (v:=this_pod_c)
        with "[$HTypeMeta $HObjectMeta $HSpec $HStatus]") as "Hthis_ptr".
      iAssert (PodV.deepown_l this_ptr this_pod dq) with "[Hthis_ptr Hthis_pod]" as "Hthis".
      { iExists this_pod_c. iFrame. }
      iApply wp_for_post_do. wp_auto.
      iFrame "Hsl HΦ pods".
      iExists (word.add i (W64 1)), this_ptr, result', (ptrs' ++ [this_ptr]).
      assert (filter is_pod_alive (take (sint.nat i) pods) ++ [this_pod] =
              filter is_pod_alive (take (sint.nat (word.add i (W64 1))) pods)) as <-.
      { assert (sint.nat (word.add i (W64 1)) = S (sint.nat i)) as -> by word.
        rewrite (take_S_r _ _ this_pod); [done|].
        rewrite list.filter_app filter_singleton_True; [done|done|done]. }
      assert (sint.nat (word.add i (W64 1)) = S (sint.nat i)) as -> by word.
      rewrite !drop_drop Nat.add_1_r.
      iFrame.
      iSplitR; [done|]. iPureIntro. word.
    + assert (¬ is_pod_alive this_pod) as Hpod_active.
      { intros Hpod_active.
        apply Hactive in Hpod_active. done. }
      iDestruct (struct_fields_combine (v:=this_pod_c)
        with "[$HTypeMeta $HObjectMeta $HSpec $HStatus]") as "Hthis_ptr".
      iAssert (PodV.deepown_l this_ptr this_pod dq) with "[Hthis_ptr Hthis_pod]" as "Hthis".
      { iExists this_pod_c. iFrame. }
      iApply wp_for_post_do. wp_auto.
      iFrame "Hsl HΦ pods".
      iExists (word.add i (W64 1)), this_ptr, result, ptrs'.
      assert (filter is_pod_alive (take (sint.nat i) pods) =
              filter is_pod_alive (take (sint.nat (word.add i (W64 1))) pods)) as <-.
      { assert (sint.nat (word.add i (W64 1)) = S (sint.nat i)) as -> by word.
        rewrite (take_S_r _ _ this_pod); [done|].
        rewrite list.filter_app filter_singleton_False; [done|done|rewrite app_nil_r; done]. }
      assert (sint.nat (word.add i (W64 1)) = S (sint.nat i)) as -> by word.
      rewrite !drop_drop Nat.add_1_r.
      iFrame. iPureIntro. word.
  - assert (take (sint.nat i) pods = pods) as ->.
    { assert (sint.nat i = length ptrs) as Hi_len.
      { rewrite Hsl_len1. word. }
      rewrite Hlen in Hi_len. rewrite Hi_len.
      apply take_ge. lia. }
    iApply "HΦ". iFrame.
Qed.

Definition owner_ref_key (owner_kind : go_string) (owner_meta : ObjectMetaV.t) : KKey.t := {|
  KKey.Kind' := owner_kind;
  KKey.Namespace' := owner_meta.(ObjectMetaV.Namespace');
  KKey.Name' := owner_meta.(ObjectMetaV.Name');
|}.

Lemma wp_FilterPodsByOwner γ l owner owner_kind meta dq1 dq2 pods children_keys :
  {{{ is_pkg_init code.controllers.common.common ∗
      "#Hisk" ∷ is_kubernetes γ l ∗
      "#Hglobal_l" ∷ (global_addr common.State) ↦□ l ∗
      "Hdeepown_l_meta" ∷ ObjectMetaV.deepown_l owner meta dq1 ∗
      "Hown_pod_meta_frags" ∷ ([∗ list] pod ∈ pods,
        own_meta_frag γ (PodV.key pod) pod.(PodV.ObjectMeta').(ObjectMetaV.UID') dq2 pod.(PodV.ObjectMeta')) ∗
      "Hown_children_frag" ∷ own_children_frag γ (owner_ref_key owner_kind meta) meta.(ObjectMetaV.UID') dq2 children_keys ∗
      "%Hnodup" ∷ ⌜ NoDup (PodV.key <$> pods) ⌝ ∗
      "%Hdom_eq" ∷ ⌜ list_to_set (PodV.key <$> pods) = filter (λ key, key.(KKey.Kind') = "Pod"%go) children_keys ⌝ ∗
      "%Hslash_free" ∷ ⌜ slash_free owner_kind ∧
        slash_free meta.(ObjectMetaV.Namespace') ∧
        slash_free meta.(ObjectMetaV.Name') ∧
        slash_free meta.(ObjectMetaV.UID') ⌝
  }}}
    @! common.FilterPodsByOwner #owner #owner_kind
  {{{ sl ptrs pods' dq', RET (#sl, #interface.nil);
      sl ↦* ptrs ∗
      ([∗ list] ptr;pod ∈ ptrs;pods', PodV.deepown_l ptr pod dq') ∗
      ⌜ ObjectMetaV.without_resource_version <$> (PodV.ObjectMeta' <$> pods') ≡ₚ
        ObjectMetaV.without_resource_version <$> (PodV.ObjectMeta' <$> pods) ⌝ ∗
      ⌜ Forall PodV.valid pods' ⌝ ∗
      ⌜ NoDup (PodV.key <$> pods') ⌝ ∗
      ObjectMetaV.deepown_l owner meta dq1 ∗
      ([∗ list] pod ∈ pods',
        own_meta_frag γ (PodV.key pod) pod.(PodV.ObjectMeta').(ObjectMetaV.UID') dq2 pod.(PodV.ObjectMeta')) ∗
      own_children_frag γ (owner_ref_key owner_kind meta) meta.(ObjectMetaV.UID') dq2 children_keys
  }}}.
Proof.
  wp_start as "H". iNamed "H". subst. wp_auto.
  iDestruct "Hdeepown_l_meta" as "(%meta_c & Howner & Hdeepown_meta)". wp_auto.
  wp_alloc owner_reference as "Howner_reference". wp_auto.
  wp_apply (controller.wp_PodControllerIndexKey with "[$Howner_reference]").
  iIntros (index_key) "->". wp_auto.
  wp_apply wp_globals_get.
  iNamedPrefix "Hdeepown_meta" "Htemp_".
  wp_apply (wp_State__ByIndex_podController with "[$Hown_pod_meta_frags $Hown_children_frag]").
  { iFrame "#". iFrame "%". iPureIntro. rewrite Htemp_Hdeepown_namespace. rewrite Htemp_Hdeepown_name.
    rewrite Htemp_Hdeepown_uid. done. }
  iCombineNamed "Htemp_*" as "H".
  iAssert (ObjectMetaV.deepown meta_c meta dq1) with "[H]" as "Hdeepown_meta".
  { iNamed "H". iFrame. done. }
  iIntros (sl interfaces pods' dq') "H". iNamedPrefix "H" "Hindex_". wp_auto.
  rewrite bool_decide_true //. wp_auto.
  iPoseProof own_slice_nil as "Hslice_nil".
  iPoseProof own_slice_cap_nil as "Hown_slice_nil_cap".
  iDestruct (own_slice_len with "Hindex_Hsl") as %(Hsl_len1 & Hsl_len2).
  iDestruct (own_slice_wf with "Hindex_Hsl") as %Hsl_cap.
  iDestruct (big_sepL2_length with "Hindex_Hpods") as %Hlen.
  set I := (∃ (i: w64) (result: slice.t) (ptrs: list loc) (v: interface.t),
    "Hi_ptr" ∷ i_ptr ↦ i ∗
    "Hresult_ptr" ∷ result_ptr ↦ result ∗
    "Hresult" ∷ result ↦* ptrs ∗
    "Hdeepown_l_pods" ∷ ([∗ list] ptr;pod ∈ ptrs;take (sint.nat i) pods', PodV.deepown_l ptr pod dq') ∗
    "Hdeepown_i_pods" ∷ ([∗ list] i;pod ∈ drop (sint.nat i) interfaces;drop (sint.nat i) pods', KObjectV.deepown_i i (KObjectV.Pod pod) dq') ∗
    "Hobj" ∷ obj_ptr ↦ v ∗
    "Hown_result_cap" ∷ own_slice_cap loc result (DfracOwn 1) ∗
    "%Hi" ∷ ⌜ 0 ≤ sint.Z i ≤ sint.Z (slice.len_f sl) ⌝
  )%I.
  iAssert (I) with "[i result obj Hindex_Hpods]" as "Hloop_inv".
  { iExists (W64 0), slice.nil, [], (default_val interface.t).
    iFrame. iFrame "#". iSplit.
    - rewrite take_0 big_sepL2_nil. done.
    - iPureIntro. word.
  }
  wp_for "Hloop_inv".
  wp_if_destruct.
  - wp_pure; first word.
    list_elem interfaces (sint.Z i) as this_interface.
    wp_apply (wp_load_slice_elem with "[$Hindex_Hsl]"); [word|eauto| ]. iIntros "Hindex_Hsl". wp_auto.
    assert (∃ this_pod, pods' !! sint.nat i = Some this_pod) as [this_pod Hthis_this_ptrookup].
    { apply lookup_lt_is_Some_2. word. }
    iPoseProof (big_sepL2_head_tail _ _ _ this_interface this_pod with "Hdeepown_i_pods") as "[Hthis_i_pod Hother_i_pod]".
    { split. all: rewrite lookup_drop Nat.add_0_r; done. }
    iDestruct "Hthis_i_pod" as (this_ptr) "[%Hthis_i Hdeepown_l]".
    unfold KObjectV.valid_interface in Hthis_i. rewrite Hthis_i.
    unshelve wp_apply wp_interface_checked_type_assert; try tc_solve.
    { iPureIntro. intros ptr_id. exists this_ptr. done. }
    iIntros (y ok) "%if_ok".
    assert (ok = true) as ->.
    { destruct ok; [done|]. intuition. }
    inversion if_ok. apply (inj to_val) in H0. subst y.
    wp_auto.
    wp_apply wp_slice_literal. iIntros (sl0) "Hsl0". wp_auto.
    wp_apply (wp_slice_append with "[$Hresult $Hown_result_cap $Hsl0]").
    iIntros (result') "(Hresult & Hown_result_cap & Hsl0)". wp_auto.
    iApply wp_for_post_do. wp_auto.
    iAssert (I) with "[Hi_ptr Hresult Hresult_ptr Hobj Hown_result_cap Hother_i_pod Hdeepown_l Hdeepown_l_pods]" as
      "Hloop_inv".
    { iExists (word.add i (W64 1)), result', (ptrs ++ [this_ptr]). iFrame. iSplitR "Hother_i_pod". 2: iSplitL.
      - assert (sint.nat (word.add i (W64 1)) = S (sint.nat i)) as -> by word.
        rewrite (take_S_r _ _ this_pod Hthis_this_ptrookup).
        iApply (big_sepL2_app with "[$Hdeepown_l_pods]"). iFrame. done.
      - assert (sint.nat (word.add i (W64 1)) = S (sint.nat i)) as -> by word.
        rewrite !drop_drop. replace (S (sint.nat i)) with (sint.nat i + 1)%nat by lia. iFrame.
      - iPureIntro. word.
    }
    iFrame.
  - iApply "HΦ". iFrame.
    assert (take (sint.nat i) pods' = pods') as ->.
    { assert (sint.nat i = length interfaces) as -> by word.
      rewrite Hlen. apply take_ge. lia.
    }
    iFrame "%". iFrame.
Qed.

End proof.
