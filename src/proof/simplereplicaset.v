From New.proof Require Import prelude empty_ffi.
From New.proof Require Export apimodel.
From New.proof.kubernetes_model Require Export simplereplicaset_init.

Section proof.
Context `{!mapG Σ KKey.t PureKObject.t}.
Context `{!mapG Σ KKey.t (gset KKey.t)}.
Context `{!auth_setG Σ KKey.t}.
Context `{hG: !heapGS Σ} {go_ctx: GoContext}.

Definition active_pod (pod: v1.Pod.t) : bool :=
  true.

Definition active_child_count (child_pods: gmap KKey.t v1.Pod.t) : nat :=
  length (filter (λ kv, active_pod (snd kv)) (map_to_list child_pods)).

(* Lemma wp_FilterPodsByOwner owner (metadata: v1.ObjectMeta.t)
  γ_state γ_children γ_fresh_keys parent_key owned_parent owned_pod_map owned_child_keys:
  {{{ is_pkg_init simplereplicaset ∗
      "#inv" ∷ is_kubernetes γ_state γ_children γ_fresh_keys ∗
      "owner" ∷ owner ↦ metadata ∗
      "own_parent" ∷ parent_key [[ γ_state ]]↦ owned_parent ∗
      "own_pods" ∷ ([∗ map] key ↦ pod ∈ owned_pod_map, key [[ γ_state ]]↦ PureKObject.Pod pod) ∗
      "own_child_keys" ∷ parent_key [[ γ_children ]]↦ owned_child_keys ∗
      "%owned_child_keys_equal_dom_owned_pods" ∷ ⌜ owned_child_keys = dom owned_pod_map ⌝ ∗
      "%indexed_value" ∷ ⌜ metadata.(v1.ObjectMeta.UID') = (PureKObject.metadata owned_parent).(v1.ObjectMeta.UID') ⌝
  }}}
  @! simplereplicaset.FilterPodsByOwner #owner
  {{{ (l: slice.t) (err: error.t) (ptrs: list loc) (pods: list v1.Pod.t), RET (#l, #err);
      l ↦* ptrs ∗
      ⌜ err = interface.nil ⌝ ∗
      ⌜ NoDup (map extract_pod_key pods) ⌝ ∗
      ([∗ list] ptr ; pod ∈ ptrs ; pods, ptr ↦ pod) ∗
      ([∗ list] pod ∈ pods,
        PurePod.well_formed pod ∗
        has_controller_parent_of pod.(v1.Pod.ObjectMeta').(v1.ObjectMeta.OwnerReferences') (PureKObject.metadata owned_parent).(v1.ObjectMeta.UID')
      ) ∗
      ([∗ list] pod ∈ pods, ∃ owned_pod,
        ⌜ owned_pod_map !! extract_pod_key pod = Some owned_pod ⌝ ∗ deepcopy_Pod owned_pod pod
      ) ∗
      ⌜ dom owned_pod_map = list_to_set (extract_pod_key <$> pods) ⌝ ∗
      parent_key [[ γ_state ]]↦ owned_parent ∗
      ([∗ map] key ↦ pod ∈ owned_pod_map, key [[ γ_state ]]↦ PureKObject.Pod pod) ∗
      parent_key [[ γ_children ]]↦ owned_child_keys
  }}}.
Proof.
  wp_start as "H". iNamed "H". wp_alloc owner_ptr as "owner_ptr". wp_auto.
  wp_apply (apimodel.wp_ByIndex_pod_ptsto_mut with "[$own_parent $own_pods $own_child_keys]").
  { iFrame "#". iPureIntro. done. }
  iIntros (l err objs pods) "H". iNamed "H". subst err. wp_auto.
  assert ((bool_decide (interface.nil = interface.nil)) = true) as nil_is_nil.
  { rewrite bool_decide_true //. }
  rewrite nil_is_nil. clear nil_is_nil. wp_auto.
  iPoseProof own_slice_nil as "slice_nil_points_to_empty_slice".
  iPoseProof own_slice_cap_nil as "own_slice_nil_cap".
  iDestruct (own_slice_len with "l") as %l_len.
  iDestruct (own_slice_wf with "l") as %l_cap.
  iDestruct (big_sepL2_length with "obj_pts_to_pod") as %len.
  iAssert ((∃ (i: w64) (result: slice.t) (ptrs: list loc) (v: interface.t),
      "i" :: i_ptr ↦ i ∗
      "result" :: result_ptr ↦ result ∗
      "ptrs" :: result ↦* ptrs ∗
      "obj_pts_to_pod" ∷ ([∗ list] obj ; pod ∈ drop (sint.nat i) objs ; drop (sint.nat i) pods, ∃ ptr : loc, ⌜obj = interface.mk (ptrT.id v1.Pod.id) (# ptr)⌝ ∗ ptr ↦ pod) ∗
      "ptr_pts_to_pod" ∷ ([∗ list] ptr ; pod ∈ ptrs ; take (sint.nat i) pods, ptr ↦ pod) ∗
      "obj" ∷ obj_ptr ↦ v ∗
      "own_result_cap" :: own_slice_cap loc result (DfracOwn 1) ∗
      "%Hi" :: ⌜0 ≤ sint.Z i ≤ sint.Z (slice.len_f l)⌝
  )%I) with "[i result obj obj_pts_to_pod]" as "loop_inv".
  {
    iExists (W64 0), slice.nil, [], (default_val interface.t).
    iFrame. iFrame "#". iSplit.
    - rewrite take_0. auto.
    - iPureIntro. word.
  }
  wp_for "loop_inv".
  wp_if_destruct.
  - wp_pure; first word.
    list_elem objs (sint.Z i) as obj.
    wp_apply (wp_load_slice_elem with "[$l]"); [ word | eauto | ].
    iIntros "l". wp_auto.
    list_elem pods (sint.Z i) as pod.
    iPoseProof (big_sepL2_destruct_cons _ (drop (sint.nat i) objs) (drop (sint.nat i) pods) obj pod with "[$obj_pts_to_pod]")
    as "[this_obj_pts_to_pod other_obj_pts_to_pod]".
    { rewrite !lookup_drop Nat.add_0_r. auto. }
    iDestruct "this_obj_pts_to_pod" as (this_ptr) "(%obj_made_of_ptr & this_ptr)".
    subst obj.
    unshelve wp_apply wp_interface_checked_type_assert; try tc_solve.
    { iPureIntro. intros ptr_id. exists this_ptr. done. }
    iIntros (y ok) "%if_ok".
    assert (ok = true) as ok_is_true.
    { destruct ok; [done|]. intuition. }
    subst ok. inversion if_ok. apply (inj to_val) in H0. subst this_ptr.
    wp_auto.
    wp_apply wp_slice_literal. iIntros (sl) "sl". wp_auto.
    wp_apply (wp_slice_append with "[$ptrs $own_result_cap $sl]").
    iIntros (result') "(ptrs & own_result_cap & sl)". wp_auto.
    iApply wp_for_post_do. wp_auto. iFrame "owner HΦ err pods pods_well_formed pods_found_in_map owner_ptr l own_pods own_child_keys own_parent".
    iExists (word.add i (W64 1)), result', (ptrs ++ [y]), (interface.mk (ptrT.id v1.Pod.id) (# y)).
    iFrame.
    iSplitL "other_obj_pts_to_pod".
    + rewrite !drop_drop Nat.add_comm /=.
      assert (sint.nat (word.add i (W64 1)) = S (sint.nat i)) as ->.
      { word. }
      done.
    + iSplitL; [ | iPureIntro; word ].
      assert (sint.nat (word.add i (W64 1)) = S (sint.nat i)) as ->.
      { word. }
      assert (take (S (sint.nat i)) pods = take (sint.nat i) pods ++ [pod]) as ->.
      { apply take_S_r. done. }
      iApply (big_sepL2_app with "[$ptr_pts_to_pod]").
      simpl. iFrame.
  - iApply "HΦ".
    rewrite indexed_value.
    iFrame.
    assert (sint.nat i = length pods) as -> by word.
    assert (take (length pods) pods = pods) as ->.
    { apply take_ge. lia. }
    iFrame.
    iPureIntro. done.
Qed.

Lemma wp_syncReplicaSet namespace name
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
