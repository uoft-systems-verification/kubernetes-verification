From New.proof Require Import prelude empty_ffi.
From New.proof.simple Require Export get index create delete.
From New.proof Require Export util.
From New.proof.simple Require Export simplereplicaset_init.
From New.proof.k8s_io.kubernetes.pkg Require Export controller.
From New.proof.k8s_io.apimachinery.pkg.runtime Require Export schema.
From New.proof.k8s_io.apimachinery.pkg.api Require Export errors.

Section proof.
Context `{!mapG Σ KKey.t KObjectV.t}.
Context `{!mapG Σ KKey.t (gset KKey.t)}.
Context `{!auth_setG Σ KKey.t}.
Context `{hG: !heapGS Σ} {go_ctx: GoContext}.

Lemma wp_manageReplicas γ l (gv: schema.GroupVersion.t) pod_l_sl rs_l
  (ptrs: list loc) active_pure_pods rs pure_rs rs_key pure_pod_map active_pure_pod_map grand_child_keys dq1 dq2 (n: w32):
  {{{ is_pkg_init simplereplicaset ∗
      "#Hisk" ∷ is_kubernetes γ l ∗
      "#Hglobal_l" ∷ (global_addr simplereplicaset.state) ↦□ l ∗
      "#Hglobal_gv" ∷ (global_addr v1.SchemeGroupVersion) ↦□ gv ∗
      "Hpod_l_sl" ∷ pod_l_sl ↦* ptrs ∗
      "Hlist" ∷ ([∗ list] ptr;pure_pod ∈ ptrs;active_pure_pods, PodV.deepown_l ptr pure_pod dq1) ∗
      "Hrs_l" ∷ rs_l ↦{dq2} rs ∗
      "Hdeepown_rs" ∷ ReplicaSetV.deepown rs pure_rs dq2 ∗
      "%Hpure_rs_valid" ∷ ⌜ ReplicaSetV.valid pure_rs ⌝ ∗
      "%Hpure_rs_name_short" ∷ ⌜ length pure_rs.(ReplicaSetV.ObjectMeta').(ObjectMetaV.Name') < 58 ⌝ ∗
      "%Hrs_key_namespace_eq" ∷ ⌜ pure_rs.(ReplicaSetV.ObjectMeta').(ObjectMetaV.Namespace') = rs_key.(KKey.Namespace') ⌝ ∗
      "%Hrs_key_name_eq" ∷ ⌜ pure_rs.(ReplicaSetV.ObjectMeta').(ObjectMetaV.Name') = rs_key.(KKey.Name') ⌝ ∗
      "%Hrs_key_kind_eq" ∷ ⌜ rs_key.(KKey.Kind') = "ReplicaSet"%go ⌝ ∗
      "Hghostown_rs" ∷ rs_key [[ γ.(γ_state) ]]↦ (KObjectV.ReplicaSet pure_rs) ∗
      "Hghostown_pods" ∷ ([∗ map] key ↦ pod ∈ pure_pod_map, key [[ γ.(γ_state) ]]↦ KObjectV.Pod pod) ∗
      "Hghostown_children" ∷ rs_key [[ γ.(γ_children) ]]↦ dom pure_pod_map ∗
      "Hghostown_grandchildren" ∷ ([∗ map] key ↦ s ∈ grand_child_keys, key [[ γ.(γ_children) ]]↦ s) ∗
      "%Hdom_eq" ∷ ⌜ dom pure_pod_map = dom grand_child_keys ⌝ ∗
      "%Hpods_keys_eq" ∷ ⌜ ∀ key pod, pure_pod_map !! key = Some pod → key = PodV.key pod ⌝ ∗
      "%Hpods_ns_eq" ∷ ⌜ ∀ key, key ∈ dom pure_pod_map → key.(KKey.Namespace') = rs_key.(KKey.Namespace') ⌝ ∗
      "%Hactive_map_eq" ∷ ⌜ active_pure_pod_map = filter (λ kv, controller.is_pure_pod_active (snd kv)) pure_pod_map ⌝ ∗
      "%Hlen_size_eq" ∷ ⌜ length active_pure_pods = size active_pure_pod_map ⌝ ∗
      "%Hin" ∷ ⌜ ∀ pure_pod, pure_pod ∈ active_pure_pods → active_pure_pod_map !! (PodV.key pure_pod) = Some pure_pod ⌝ ∗
      "%Hno_dup" ∷ ⌜ ∀ i j p1 p2, i ≠ j → active_pure_pods !! i = Some p1 → active_pure_pods !! j = Some p2 → (PodV.key p1) ≠ (PodV.key p2) ⌝ ∗
      "%Hreplicas_eq" ∷ ⌜ pure_rs.(ReplicaSetV.Spec').(ReplicaSetSpecV.Replicas') = Some n ⌝
  }}}
  @! simplereplicaset.manageReplicas #pod_l_sl #rs_l
  {{{ pure_pod_map' grand_child_keys', RET #interface.nil;
      rs_key [[ γ.(γ_state) ]]↦ (KObjectV.ReplicaSet pure_rs) ∗
      ([∗ map] key ↦ pod ∈ pure_pod_map', key [[ γ.(γ_state) ]]↦ KObjectV.Pod pod) ∗
      rs_key [[ γ.(γ_children) ]]↦ dom pure_pod_map' ∗
      ([∗ map] key ↦ s ∈ grand_child_keys', key [[ γ.(γ_children) ]]↦ s) ∗
      ⌜ dom pure_pod_map' = dom grand_child_keys' ⌝ ∗
      ⌜ size (filter (λ kv, controller.is_pure_pod_active (snd kv)) pure_pod_map') = sint.nat n ⌝
  }}}.
Proof. Admitted.

Lemma wp_FilterActivePods l ptrs pure_pods dq:
  {{{ is_pkg_init simplereplicaset ∗
      "Hl" ∷ l ↦* ptrs ∗
      "Hlist" ∷ ([∗ list] ptr;pure_pod ∈ ptrs;pure_pods, PodV.deepown_l ptr pure_pod dq)
  }}}
  @! simplereplicaset.FilterActivePods #l
  {{{ l' ptrs' pure_pods', RET #l';
      l' ↦* ptrs' ∗
      ([∗ list] ptr;pure_pod ∈ ptrs';pure_pods', PodV.deepown_l ptr pure_pod dq) ∗
      ⌜ pure_pods' = filter (λ v, controller.is_pure_pod_active v) pure_pods ⌝
  }}}.
Proof.
  wp_start as "H". iNamed "H". wp_auto.
  iPoseProof own_slice_nil as "Hslice_nil".
  iPoseProof own_slice_cap_nil as "Hown_slice_nil_cap".
  iDestruct (own_slice_len with "Hl") as %(Hl_len1 & Hl_len2).
  iDestruct (own_slice_wf with "Hl") as %Hl_cap.
  iDestruct (big_sepL2_length with "Hlist") as %Hlen.
  set I := (∃ (i: w64) (p: loc) (result: slice.t) (ptrs': list loc) pure_pods',
      "Hi_ptr" ∷ i_ptr ↦ i ∗
      "Hp_ptr" ∷ p_ptr ↦ p ∗
      "Hresult_ptr" ∷ result_ptr ↦ result ∗
      "Hresult" ∷ result ↦* ptrs' ∗
      "Hlist_pre" ∷ ([∗ list] ptr;pure_pod ∈ ptrs';pure_pods', PodV.deepown_l ptr pure_pod dq) ∗
      "Hlist_post" ∷ ([∗ list] ptr;pure_pod ∈ (drop (sint.nat i) ptrs);(drop (sint.nat i) pure_pods), PodV.deepown_l ptr pure_pod dq) ∗
      "Hown_result_cap" ∷ own_slice_cap loc result (DfracOwn 1) ∗
      "%Hi" ∷ ⌜ 0 ≤ sint.Z i ≤ sint.Z (slice.len_f l) ⌝ ∗
      "%Hpure_pods'_eq" ∷ ⌜ pure_pods' = filter (λ v, controller.is_pure_pod_active v) (take (sint.nat i) pure_pods) ⌝
  )%I.
  iAssert (I) with "[i result p Hlist]" as "Hloop_inv". {
    iExists (W64 0), (default_val loc), slice.nil, [], [].
    iFrame. iFrame "#".
    rewrite !take_0 !filter_nil !big_sepL2_nil. done. }
  wp_for "Hloop_inv".
  wp_if_destruct.
  - wp_pure; first word.
    list_elem ptrs (sint.Z i) as this_ptr.
    wp_apply (wp_load_slice_elem with "[$Hl]"); [word|eauto| ]. iIntros "Hl". wp_auto.
    assert (∃ this_pure_pod, pure_pods !! sint.nat i = Some this_pure_pod) as [this_pure_pod Hthis_pure_pod_lookup].
    { apply lookup_lt_is_Some_2. rewrite -Hlen Hl_len1. word. }
    iPoseProof (big_sepL2_head_tail _ _ _ this_ptr this_pure_pod with "Hlist_post") as "[Hthis Hother]".
    { split. all: rewrite lookup_drop Nat.add_0_r; done. }
    iDestruct "Hthis" as (this_pod) "[Hthis_ptr Hthis_pure_pod]".
    iDestruct (controller.deepown_preserves_activeness with "Hthis_pure_pod") as %Hactive.
    wp_apply (controller.wp_IsPodActive with "[$Hthis_ptr]").
    iIntros "Hthis_ptr".
    destruct (bool_decide (is_pod_active this_pod)) eqn:Hpod_active_decide. all: wp_auto.
    + assert (is_pod_active this_pod) as Hpod_active.
      { rewrite bool_decide_eq_true in Hpod_active_decide. done. }
      assert (is_pure_pod_active this_pure_pod) as Hpure_active.
      { apply Hactive. done. }
      wp_apply wp_slice_literal. iIntros (sl) "Hsl". wp_auto.
      wp_apply (wp_slice_append with "[$Hresult $Hown_result_cap $Hsl]"). iIntros (result') "(Hresult & Hown_result_cap & Hsl)". wp_auto.
      iApply wp_for_post_do. wp_auto.
      iFrame "Hl HΦ pods".
      iExists (word.add i (W64 1)), this_ptr, result', (ptrs' ++ [this_ptr]),
        ((filter (λ v, controller.is_pure_pod_active v) (take (sint.nat (word.add i (W64 1))) pure_pods))).
      assert (filter (λ v, is_pure_pod_active v) (take (sint.nat i) pure_pods) ++ [this_pure_pod] =
              filter (λ v, is_pure_pod_active v) (take (sint.nat (word.add i (W64 1))) pure_pods)) as <-.
      { assert (sint.nat (word.add i (W64 1)) = S (sint.nat i)) as -> by word.
        rewrite (take_S_r _ _ this_pure_pod); [done|].
        rewrite list.filter_app filter_singleton_True; [done|done|done]. }
      assert (sint.nat (word.add i (W64 1)) = S (sint.nat i)) as -> by word. rewrite !drop_drop Nat.add_1_r.
      iFrame.
      iSplitR; [done|]. iSplitR; [word|done].
    + assert (¬ is_pod_active this_pod) as Hpod_active.
      { rewrite bool_decide_eq_false in Hpod_active_decide. done. }
      assert (¬ is_pure_pod_active this_pure_pod) as Hpure_active.
      { intros H. apply Hactive in H. done. }
      iApply wp_for_post_do. wp_auto. iFrame "Hl HΦ pods".
      iExists (word.add i (W64 1)), this_ptr, result, ptrs',
        ((filter (λ v, controller.is_pure_pod_active v) (take (sint.nat (word.add i (W64 1))) pure_pods))).
      assert (filter (λ v, is_pure_pod_active v) (take (sint.nat i) pure_pods) =
              filter (λ v, is_pure_pod_active v) (take (sint.nat (word.add i (W64 1))) pure_pods)) as <-.
      { assert (sint.nat (word.add i (W64 1)) = S (sint.nat i)) as -> by word.
        rewrite (take_S_r _ _ this_pure_pod); [done|].
        rewrite list.filter_app filter_singleton_False; [done|done|rewrite app_nil_r; done]. }
      assert (sint.nat (word.add i (W64 1)) = S (sint.nat i)) as -> by word. rewrite !drop_drop Nat.add_1_r.
      iFrame. iPureIntro. split; [word|done].
  - iApply "HΦ". iFrame "Hresult Hlist_pre".
    iPureIntro. assert (sint.nat i = length pure_pods) as -> by word. rewrite take_ge; [lia|]. done.
Qed.

Lemma wp_FilterPodsByOwner γ l owner owner_kind metadata pure_metadata dq
  parent_key parent owned_pod_map children_keys:
  {{{ is_pkg_init simplereplicaset ∗
      "#Hisk" ∷ is_kubernetes γ l ∗
      "#Hglobal" ∷ (global_addr simplereplicaset.state)↦□l ∗
      "Howner" ∷ owner ↦{dq} metadata ∗
      "Hdeepown_meta" ∷ ObjectMetaV.deepown metadata pure_metadata dq ∗
      "%Howner_kind_eq" ∷ ⌜ owner_kind = parent_key.(KKey.Kind') ⌝ ∗
      "%Hnamespace_eq" ∷ ⌜ pure_metadata.(ObjectMetaV.Namespace') = parent_key.(KKey.Namespace') ⌝ ∗
      "%Hname_eq" ∷ ⌜ pure_metadata.(ObjectMetaV.Name') = parent_key.(KKey.Name') ⌝ ∗
      "%Howner_kind_nonempty" ∷ ⌜ owner_kind ≠ ""%go ⌝ ∗
      "Hghost_parent" ∷ parent_key [[ γ.(γ_state) ]]↦ parent ∗
      "Hown_pods" ∷ ([∗ map] key ↦ pod ∈ owned_pod_map, key [[ γ.(γ_state) ]]↦ KObjectV.Pod pod) ∗
      "Hghost_children_keys" ∷ parent_key [[ γ.(γ_children) ]]↦ children_keys ∗
      "%Hchildren_keys_equal_dom_owned_pods" ∷ ⌜ children_keys = dom owned_pod_map ⌝ ∗
      "%Hindexed_value" ∷ ⌜ pure_metadata = (KObjectV.objectmeta parent) ⌝ ∗
      "%Hmeta_wellformed" ∷ ⌜ ObjectMetaV.valid pure_metadata ⌝
  }}}
  @! simplereplicaset.FilterPodsByOwner #owner #owner_kind
  {{{ (ptr_slice: slice.t) (ptrs: list loc) (pure_pods: list PodV.t) dq', RET (#ptr_slice, #interface.nil);
      ptr_slice ↦* ptrs ∗
      ([∗ list] ptr;pure_pod ∈ ptrs;pure_pods, PodV.deepown_l ptr pure_pod dq') ∗
      ⌜ ∀ pure_pod, pure_pod ∈ pure_pods → PodV.valid pure_pod ⌝ ∗
      ⌜ ∀ p, p ∈ pure_pods → owned_pod_map !! (PodV.key p) = Some p ⌝ ∗
      ⌜ ∀ k p, owned_pod_map !! k = Some p → p ∈ pure_pods ⌝ ∗
      ⌜ ∀ key p, owned_pod_map !! key = Some p → key = PodV.key p ⌝ ∗
      ⌜ ∀ i j p1 p2, i ≠ j → pure_pods !! i = Some p1 → pure_pods !! j = Some p2 → (PodV.key p1) ≠ (PodV.key p2) ⌝ ∗
      ⌜ ∀ key, key ∈ dom owned_pod_map → key.(KKey.Namespace') = parent_key.(KKey.Namespace') ⌝ ∗
      owner ↦{dq} metadata ∗
      ObjectMetaV.deepown metadata pure_metadata dq ∗
      parent_key [[ γ.(γ_state) ]]↦ parent ∗
      ([∗ map] key ↦ pod ∈ owned_pod_map, key [[ γ.(γ_state) ]]↦ KObjectV.Pod pod) ∗
      parent_key [[ γ.(γ_children) ]]↦ children_keys
  }}}.
Proof. Admitted.

Lemma wp_syncReplicaSet γ l (gv: schema.GroupVersion.t) namespace name
  rs_key pure_rs pure_pod_map grand_child_key_map (n: w32):
  {{{ is_pkg_init simplereplicaset ∗
      "#Hisk" ∷ is_kubernetes γ l ∗
      "#Hglobal_l" ∷ (global_addr simplereplicaset.state)↦□l ∗
      "#Hglobal_gv" ∷ (global_addr v1.SchemeGroupVersion) ↦□ gv ∗
      "%rs_key_eq" ∷ ⌜ rs_key = mk_replicaset_key namespace name ⌝ ∗
      "Hghostown_rs" ∷ rs_key [[ γ.(γ_state) ]]↦ KObjectV.ReplicaSet pure_rs ∗
      "Hghostown_pods" ∷ ([∗ map] key ↦ v ∈ pure_pod_map, key [[ γ.(γ_state) ]]↦ KObjectV.Pod v) ∗
      "Hghostown_children" ∷ rs_key [[ γ.(γ_children) ]]↦ dom pure_pod_map ∗
      "Hghostown_grandchildren" ∷ ([∗ map] key ↦ s ∈ grand_child_key_map, key [[ γ.(γ_children) ]]↦ s) ∗
      "%Hpure_rs_name_short" ∷ ⌜ length pure_rs.(ReplicaSetV.ObjectMeta').(ObjectMetaV.Name') < 58 ⌝ ∗
      "%Hdom_eq" ∷ ⌜ dom pure_pod_map = dom grand_child_key_map ⌝ ∗
      "%Hts_non" ∷ ⌜ pure_rs.(ReplicaSetV.ObjectMeta').(ObjectMetaV.DeletionTimestamp') = None ⌝ ∗
      "%Hreplicas_eq" ∷ ⌜ pure_rs.(ReplicaSetV.Spec').(ReplicaSetSpecV.Replicas') = Some n ⌝
  }}}
  @! simplereplicaset.syncReplicaSet #namespace #name
  {{{ (pure_pod_map': gmap KKey.t PodV.t) grand_child_key_map', RET #interface.nil;
      rs_key [[ γ.(γ_state) ]]↦ KObjectV.ReplicaSet pure_rs ∗
      ([∗ map] key ↦ v ∈ pure_pod_map', key [[ γ.(γ_state) ]]↦ KObjectV.Pod v) ∗
      rs_key [[ γ.(γ_children) ]]↦ dom pure_pod_map' ∗
      ([∗ map] key ↦ s ∈ grand_child_key_map', key [[ γ.(γ_children) ]]↦ s) ∗
      ⌜ dom pure_pod_map' = dom grand_child_key_map' ⌝ ∗
      ⌜ size (filter (λ kv, controller.is_pure_pod_active (snd kv)) pure_pod_map') = sint.nat n ⌝
  }}}.
Proof. Admitted.

End proof.
