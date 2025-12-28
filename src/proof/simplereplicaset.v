From New.proof Require Import prelude empty_ffi.
From New.proof Require Export index.
From New.proof.kubernetes_model Require Export simplereplicaset_init.
From New.proof.k8s_io.kubernetes.pkg Require Export controller.

Section proof.
Context `{!mapG Σ KKey.t PureKObject.t}.
Context `{!mapG Σ KKey.t (gset KKey.t)}.
Context `{!auth_setG Σ KKey.t}.
Context `{hG: !heapGS Σ} {go_ctx: GoContext}.

Axiom active_pod: v1.Pod.t → bool.

Definition active_child_count (child_pods: gmap KKey.t v1.Pod.t) : nat :=
  length (filter (λ kv, active_pod (snd kv)) (map_to_list child_pods)).

Lemma wp_FilterPodsByOwner γ l owner owner_kind metadata pure_metadata dq
  parent_key owned_parent owned_pod_map owned_child_keys:
  {{{ is_pkg_init simplereplicaset ∗
      "#Hisk" ∷ is_kubernetes γ l ∗
      "#Hglobal" ∷ (global_addr simplereplicaset.state)↦□l ∗
      "Hdeepown_l_meta" ∷ PureObjectMeta.deepown_l owner metadata pure_metadata dq ∗
      "%Howner_kind_eq" ∷ ⌜ owner_kind = parent_key.(KKey.Kind') ⌝ ∗
      "%Hnamespace_eq" ∷ ⌜ pure_metadata.(PureObjectMeta.Namespace') = parent_key.(KKey.Namespace') ⌝ ∗
      "%Hname_eq" ∷ ⌜ pure_metadata.(PureObjectMeta.Name') = parent_key.(KKey.Name') ⌝ ∗
      "%Howner_kind_nonempty" ∷ ⌜ owner_kind ≠ ""%go ⌝ ∗
      "Hown_parent" ∷ parent_key [[ γ.(γ_state) ]]↦ owned_parent ∗
      "Hown_pods" ∷ ([∗ map] key ↦ pod ∈ owned_pod_map, key [[ γ.(γ_state) ]]↦ PureKObject.Pod pod) ∗
      "Hown_child_keys" ∷ parent_key [[ γ.(γ_children) ]]↦ owned_child_keys ∗
      "%Howned_child_keys_equal_dom_owned_pods" ∷ ⌜ owned_child_keys = dom owned_pod_map ⌝ ∗
      "%Hindexed_value" ∷ ⌜ pure_metadata = (PureKObject.metadata owned_parent) ⌝ ∗
      "%Hmeta_wellformed" ∷ ⌜ PureObjectMeta.well_formed pure_metadata ⌝
  }}}
  @! simplereplicaset.FilterPodsByOwner #owner #owner_kind
  {{{ (ptr_slice: slice.t) (ptrs: list loc) (pods: list v1.Pod.t) (pure_pods: list PurePod.t), RET (#ptr_slice, #interface.nil);
      ptr_slice ↦* ptrs ∗
      ([∗ list] ptr;pod ∈ ptrs;pods, ptr ↦ pod) ∗
      ([∗ list] pod;pure_pod ∈ pods;pure_pods, PurePod.deepown pod pure_pod 1) ∗
      ⌜ ∀ pure_pod, pure_pod ∈ pure_pods → PurePod.well_formed pure_pod ⌝ ∗
      ⌜ length pure_pods = size owned_pod_map ⌝ ∗
      ⌜ ∀ pure_pod, pure_pod ∈ pure_pods → ∃ k, owned_pod_map !! k = Some pure_pod ⌝ ∗
      PureObjectMeta.deepown_l owner metadata pure_metadata dq ∗
      parent_key [[ γ.(γ_state) ]]↦ owned_parent ∗
      ([∗ map] key ↦ pod ∈ owned_pod_map, key [[ γ.(γ_state) ]]↦ PureKObject.Pod pod) ∗
      parent_key [[ γ.(γ_children) ]]↦ owned_child_keys
  }}}.
Proof.
  wp_start as "H". iNamed "H". iDestruct "Hdeepown_l_meta" as "[Howner Hdeepown_meta]". subst. wp_auto.
  wp_alloc owner_reference as "Howner_reference". wp_auto.
  wp_apply (controller.wp_PodControllerIndexKey with "[$Howner_reference]").
  iIntros (index_key) "%Hindex_key_eq". wp_auto.
  wp_apply wp_globals_get.
  iNamedPrefix "Hdeepown_meta" "Htemp_".
  wp_apply (wp_State__ByIndex_pod with "[$Hown_parent $Hown_pods $Hown_child_keys]").
  { iFrame "#". iPureIntro. unfold controller.PodControllerIndex. rewrite <-Hnamespace_eq. rewrite <-Hname_eq.
    rewrite Hindex_key_eq. rewrite Htemp_Hdeepown_namespace. rewrite Htemp_Hdeepown_name. rewrite Htemp_Hdeepown_uid. done. }
  iCombineNamed "Htemp_*" as "H".
  iAssert (PureObjectMeta.deepown metadata (PureKObject.metadata owned_parent) dq) with "[H]" as "Hdeepown_meta".
  { iNamed "H". iFrame. done. }
  iIntros (objs_l ptrs pods pure_pods) "H".
  set objs := map (λ ptr : loc, interface.mk (ptrT.id v1.Pod.id) (# ptr)) ptrs.
  iNamed "H". wp_auto. rewrite bool_decide_true //. wp_auto.
  iPoseProof own_slice_nil as "Hslice_nil".
  iPoseProof own_slice_cap_nil as "Hown_slice_nil_cap".
  iDestruct (own_slice_len with "Hobjs_l") as %(Hobjs_l_len1 & Hobjs_l_len2).
  iDestruct (own_slice_wf with "Hobjs_l") as %Hobjs_l_cap.
  iDestruct (big_sepL2_length with "Hptrs_pods") as %Hlen.
  iAssert ((∃ (i: w64) (result: slice.t) (v: interface.t),
      "Hi_ptr" :: i_ptr ↦ i ∗
      "Hresult_ptr" :: result_ptr ↦ result ∗
      "Hresult" ∷ result ↦* take (sint.nat i) ptrs ∗
      "Hobj" ∷ obj_ptr ↦ v ∗
      "Hown_result_cap" :: own_slice_cap loc result (DfracOwn 1) ∗
      "%Hi" :: ⌜0 ≤ sint.Z i ≤ sint.Z (slice.len_f objs_l)⌝
  )%I) with "[i result obj]" as "Hloop_inv". {
    iExists (W64 0), slice.nil, (default_val interface.t).
    iFrame. iFrame "#". iPureIntro. word. }
  wp_for "Hloop_inv".
  wp_if_destruct.
  - wp_pure; first word.
    list_elem objs (sint.Z i) as this_obj.
    wp_apply (wp_load_slice_elem with "[$Hobjs_l]"); [word|eauto| ].
    iIntros "Hobjs_l". wp_auto.
    assert (∃ this_ptr, ptrs !! sint.nat i = Some this_ptr) as [this_ptr Hthis_ptr].
    { apply lookup_lt_is_Some_2.
      assert (length objs = length ptrs) as Hlen_eq.
      { subst objs. apply map_length. }
      rewrite -Hlen_eq Hobjs_l_len1.
      word. }
    assert (this_obj = interface.mk (ptrT.id v1.Pod.id) (# this_ptr)) as ->.
    { subst objs.
      rewrite list_lookup_fmap in Hthis_obj_lookup.
      rewrite Hthis_ptr in Hthis_obj_lookup.
      simpl in Hthis_obj_lookup.
      congruence. }
    unshelve wp_apply wp_interface_checked_type_assert; try tc_solve.
    { iPureIntro. intros ptr_id. exists this_ptr. done. }
    iIntros (y ok) "%if_ok".
    assert (ok = true) as ->.
    { destruct ok; [done|]. intuition. }
    inversion if_ok. apply (inj to_val) in H0. subst y.
    wp_auto.
    wp_apply wp_slice_literal. iIntros (sl) "Hsl". wp_auto.
    wp_apply (wp_slice_append with "[$Hresult $Hown_result_cap $Hsl]").
    iIntros (result') "(Hresult & Hown_result_cap & Hsl)". wp_auto.
    iApply wp_for_post_do. wp_auto.
    iFrame "Howner HΦ err pods ownerKind owner key Hdeepown_meta Hobjs_l Hptrs_pods Hpods_purepods Hown_pods Hown_child_keys Hown_parent".
    iExists (word.add i (W64 1)), result', (interface.mk (ptrT.id v1.Pod.id) (# this_ptr)).
    iFrame.
    iSplitL;[|iPureIntro;word].
    assert (sint.nat (word.add i (W64 1)) = S (sint.nat i)) as -> by word.
    assert (take (S (sint.nat i)) ptrs = take (sint.nat i) ptrs ++ [this_ptr]) as ->.
    { apply take_S_r. done. }
    iFrame.
  - iApply "HΦ". iFrame.
    assert (take (sint.nat i) ptrs = ptrs) as ->.
    { assert (sint.nat i = length objs) as -> by word.
      assert (length objs = length ptrs) as ->.
      { subst objs. apply map_length. }
      apply take_ge. lia. }
    iFrame. iPureIntro. done.
Qed.

(* Lemma wp_syncReplicaSet namespace name
  γ_state γ_children γ_fresh_keys rs_key rs child_keys child_pods (n: w32):
  {{{ is_pkg_init simplereplicaset ∗
      is_kubernetes γ_state γ_children γ_fresh_keys ∗
      ⌜ rs_key = mk_replicaset_key namespace name ⌝ ∗
      rs_key [[ γ_state ]]↦ PureKObject.ReplicaSet rs ∗
      ([∗ map] key ↦ v ∈ child_pods, key [[ γ_state ]]↦ PureKObject.Pod v) ∗
      rs_key [[ γ_children ]]↦ child_keys ∗
      ⌜ child_keys = dom child_pods ⌝ ∗
      rs.(v1.ReplicaSet.Spec').(v1.ReplicaSetSpec.Replicas') ↦ n
  }}}
  @! simplereplicaset.syncReplicaSet #namespace #name
  {{{ (err : error.t) child_keys' child_pods', RET #err;
      rs_key [[ γ_state ]]↦ PureKObject.ReplicaSet rs ∗
      ([∗ map] key ↦ v ∈ child_pods', key [[ γ_state ]]↦ PureKObject.Pod v) ∗
      rs_key [[ γ_children ]]↦ child_keys' ∗
      ⌜ child_keys' = dom child_pods' ⌝ ∗
      if decide (err = interface.nil) then
        ⌜ size child_keys' = sint.nat n ⌝
      else
        ⌜ Z.abs (Z.of_nat (active_child_count child_pods) - sint.Z n) <
          Z.abs (Z.of_nat (active_child_count child_pods') - sint.Z n) ⌝
  }}}.
Proof. Admitted. *)


End proof.
