From New.proof Require Import prelude empty_ffi.
From New.proof.simple Require Export apimodel list.
From New.proof Require Export util.
From New.proof.simple Require Export apimodel_init.

Section proof.
Context `{!mapG Σ KKey.t KObjectV.t}.
Context `{!mapG Σ KKey.t (gset KKey.t)}.
Context `{!auth_setG Σ KKey.t}.
Context `{hG: !heapGS Σ} {go_ctx: GoContext}.

Lemma wp_index_of_podController index_name obj ptr pod pure_pod dq:
  {{{ is_pkg_init apimodel ∗
      "%Hindex_name" ∷ ⌜ index_name = "podController"%go ⌝ ∗
      "%Hobj" ∷ ⌜ obj = interface.mk (ptrT.id v1.Pod.id) #ptr ⌝ ∗
      "Hptr" ∷ ptr ↦{dq} pod ∗
      "Hdeepown_pod" ∷ PodV.deepown pod pure_pod dq ∗
      "%Hwf" ∷ ⌜ PodV.valid pure_pod ⌝
  }}}
    @! apimodel.index_of #index_name #obj
  {{{ sl idx_val_list idx_val, RET (#sl, #interface.nil);
      sl ↦* idx_val_list ∗
      ⌜ idx_val_list = [idx_val] ⌝ ∗
      ⌜ ∀ parent_kind parent_name parent_uid,
        obj_has_controller_parent_of (KObjectV.Pod pure_pod) parent_kind parent_name parent_uid ↔
        idx_val = pure_pod.(PodV.ObjectMeta').(ObjectMetaV.Namespace') ++ "/"%go ++
                  parent_kind ++ "/"%go ++ parent_name ++ "/"%go ++ parent_uid ⌝ ∗
      ⌜ idx_val = pure_pod.(PodV.ObjectMeta').(ObjectMetaV.Namespace') ∨ (* the orphan case *)
        ∃ suffix, idx_val = pure_pod.(PodV.ObjectMeta').(ObjectMetaV.Namespace') ++ "/"%go ++ suffix ⌝ ∗
      ptr ↦{dq} pod ∗
      PodV.deepown pod pure_pod dq
  }}}.
Proof. Admitted.

Lemma wp_State__ByIndex_pod γ l kind index_name indexed_value parent_key parent pure_pod_map children_keys:
  {{{ is_pkg_init apimodel ∗
      "#Hisk" ∷ is_kubernetes γ l ∗
      "%Hkind" ∷ ⌜ kind = "Pod"%go ⌝ ∗
      "%Hindex_name" ∷ ⌜ index_name = "podController"%go ⌝ ∗
      "%Hindexed_value" ∷ ⌜ indexed_value = parent_key.(KKey.Namespace') ++ "/"%go ++
                                            parent_key.(KKey.Kind') ++ "/"%go ++
                                            parent_key.(KKey.Name') ++ "/"%go ++
                                            (KObjectV.objectmeta parent).(ObjectMetaV.UID') ⌝ ∗
      "Hghost_parent" ∷ parent_key [[ γ.(γ_state) ]]↦ parent ∗
      "Hghost_pure_pod_map" ∷ ([∗ map] key ↦ pod ∈ pure_pod_map, key [[ γ.(γ_state) ]]↦ KObjectV.Pod pod) ∗
      "Hghost_children_keys" ∷ parent_key [[ γ.(γ_children) ]]↦ children_keys ∗
      "%Hdom_eq" ∷ ⌜ children_keys = dom pure_pod_map ⌝
  }}}
    l @ (ptrT.id apimodel.State.id) @ "ByIndex" #kind #index_name #indexed_value
  {{{ objs_l (ptr_list: list loc) (pure_pod_list: list PodV.t) dq, RET (#objs_l, #interface.nil);
      "Hobjs_l" ∷ objs_l ↦* map (λ ptr, interface.mk (ptrT.id v1.Pod.id) #ptr) ptr_list ∗
      "Hptrs_purepods" ∷ ([∗ list] ptr;pure_pod ∈ ptr_list;pure_pod_list, ∃ pod, ptr ↦{dq} pod ∗ PodV.deepown pod pure_pod dq) ∗
      "%Hwf_pure_pod_list" ∷ ⌜ ∀ p, p ∈ pure_pod_list → PodV.valid p ⌝ ∗
      "%Hlist_in_map" ∷  ⌜ ∀ p, p ∈ pure_pod_list → pure_pod_map !! (PodV.key p) = Some p ⌝ ∗
      "%Hmap_in_list" ∷ ⌜ ∀ k p, pure_pod_map !! k = Some p → p ∈ pure_pod_list ⌝ ∗
      "%Hown_pod_keys_eq" ∷ ⌜ ∀ key pod, pure_pod_map !! key = Some pod → key = PodV.key pod ⌝ ∗
      "%Hno_dup" ∷ ⌜ ∀ i j p1 p2, i ≠ j → pure_pod_list !! i = Some p1 → pure_pod_list !! j = Some p2 → (PodV.key p1) ≠ (PodV.key p2) ⌝ ∗
      "%Hpure_pod_map_namespace_eq" ∷ ⌜ ∀ key, key ∈ dom pure_pod_map → key.(KKey.Namespace') = parent_key.(KKey.Namespace') ⌝ ∗
      "Hghost_parent" ∷ parent_key [[ γ.(γ_state) ]]↦ parent ∗
      "Hghost_pure_pod_map" ∷ ([∗ map] key ↦ pod ∈ pure_pod_map, key [[ γ.(γ_state) ]]↦ KObjectV.Pod pod) ∗
      "Hghost_children_keys" ∷ parent_key [[ γ.(γ_children) ]]↦ children_keys
  }}}.
Proof.
  wp_start as "H". iNamed "H". iNamed "Hisk".
  wp_apply wp_with_defer. iIntros (defer) "Hdefer". simpl subst. wp_auto.
  wp_apply wp_Mutex__Lock; [done|]. iIntros "[Hown_Mutex H]". iNamedPrefix "H" "Hinv_".
  iAssert (⌜ abs_state !! parent_key = Some (parent) ⌝%I) as "%Hlookup_abs_parent".
  { iDestruct (map_valid with "Hinv_Hown_abs Hghost_parent") as %Hlookup. iPureIntro; exact Hlookup. }
  iAssert (⌜ children !! parent_key = Some (children_keys) ⌝%I) as "%Hlookup_children".
  { iDestruct (map_valid with "Hinv_Hown_children Hghost_children_keys") as %Hlookup. iPureIntro; exact Hlookup. }
  wp_auto.
  wp_apply (wp_State__objListLocked_pod with "[$Hghost_pure_pod_map $Hinv_Hstate_m_addr $Hinv_Hown_phys $Hinv_Hown_abs $Hinv_Hphys_abs_rep]").
  { iPureIntro. split; [done|]. destruct Hinv_Hghost_valid. done. }
  iIntros (sl ptr_list pure_pod_list) "(Hsl & Hlist & %Hwf & %Hlookup_abs & %Hno_dup & %Hns_match & %Hmap_in_list &
    Hinv_Hstate_m_addr & Hinv_Hown_phys & Hinv_Hown_abs & Hinv_Hphys_abs_rep & Hghost_pure_pod_map)". wp_auto.
  assert (∀ (k : KKey.t) (p : PodV.t), pure_pod_map !! k = Some p → p ∈ pure_pod_list) as Hmap_in_list'.
  { intros k p Hlookup. apply (Hmap_in_list k p Hlookup). unfold namespace_matches. left. done. }
  clear Hns_match. rename Hmap_in_list' into Hns_match.
  set obj_list := map (λ ptr : loc, interface.mk (ptrT.id v1.Pod.id) (# ptr)) ptr_list.
  assert (length obj_list = length ptr_list) as Hlen_obj_ptr.
  { unfold obj_list. rewrite map_length. done. }
  iPoseProof own_slice_nil as "Hslice_nil".
  iPoseProof own_slice_cap_nil as "Hown_slice_nil_cap".
  iDestruct (own_slice_len with "Hsl") as %(Hsl_len1 & Hsl_len2).
  iDestruct (own_slice_wf with "Hsl") as %Hsl_cap.
  iDestruct (big_sepL2_length with "Hlist") as %Hlen_ptr_pure_pod.
  set P := (λ p, obj_has_controller_parent_of (KObjectV.Pod p) parent_key.(KKey.Kind') parent_key.(KKey.Name') (KObjectV.objectmeta parent).(ObjectMetaV.UID')).
  set I := (∃ (i: w64) (val: interface.t) (sl': slice.t) (ptr_list': list loc) (pure_pod_list': list PodV.t),
    "Hi_ptr" ∷ i_ptr ↦ i ∗
    "Hval_ptr" ∷ val_ptr ↦ val ∗
    "Hitems_ptr" ∷ items_ptr ↦ sl' ∗
    "Hsl'" ∷ sl' ↦* map (λ ptr : loc, interface.mk (ptrT.id v1.Pod.id) (# ptr)) ptr_list' ∗
    "Hlist_pre" ∷ ([∗ list] ptr;pure_pod ∈ ptr_list';pure_pod_list', PodV.deepown_l ptr pure_pod 1) ∗
    "Hlist_post" ∷ ([∗ list] ptr;pure_pod ∈ (drop (sint.nat i) ptr_list);(drop (sint.nat i) pure_pod_list), PodV.deepown_l ptr pure_pod 1) ∗
    "Hcap_sl'" :: own_slice_cap interface.t sl' (DfracOwn 1) ∗
    "%Hfilter_ptr_list" ∷ ⌜ pure_pod_list' = filter P (take (sint.nat i) pure_pod_list) ⌝ ∗
    "%Hi" ∷ ⌜ 0 ≤ sint.Z i ≤ sint.Z (slice.len_f sl) ⌝
  )%I.
  iAssert (I) with "[i val items Hlist]" as "Hloop_inv". {
    iExists (W64 0), (default_val interface.t), (default_val slice.t), [], [].
    iFrame. iFrame "#". rewrite !big_sepL2_nil. done. }
  wp_for "Hloop_inv". wp_if_destruct.
  - wp_pure; first word.
    list_elem obj_list (sint.Z i) as this_obj.
    wp_apply (wp_load_slice_elem with "[$Hsl]"); [word|eauto| ]. iIntros "Hsl". wp_auto.
    assert (∃ this_ptr, ptr_list !! sint.nat i = Some this_ptr) as [this_ptr Hthis_ptr_lookup].
    { apply lookup_lt_is_Some_2. word. }
    assert (∃ this_pure_pod, pure_pod_list !! sint.nat i = Some this_pure_pod) as [this_pure_pod Hthis_pure_pod_lookup].
    { apply lookup_lt_is_Some_2. word. }
    iPoseProof (big_sepL2_head_tail _ _ _ this_ptr this_pure_pod with "Hlist_post") as "[Hthis_ptr_pure_pod Hother_ptr_pure_pod]".
    { split. all: rewrite lookup_drop Nat.add_0_r; done. }
    iDestruct "Hthis_ptr_pure_pod" as (this_pod) "[Hthis_ptr Hdeepown_this_pod]".
    wp_apply (wp_index_of_podController with "[$Hthis_ptr $Hdeepown_this_pod]").
    { iPureIntro. split_and!; [done| | ].
      - unfold obj_list in Hthis_obj_lookup. rewrite list_lookup_fmap in Hthis_obj_lookup.
        rewrite Hthis_ptr_lookup in Hthis_obj_lookup. simpl in Hthis_obj_lookup.
        injection Hthis_obj_lookup. done.
      - apply Hwf. apply (list_elem_of_lookup_2 _ (sint.nat i)). done. }
    iIntros (sl0 idx_val_list idx_val) "(Hsl0 & -> & %Hidx_val & %Hidx_val_prefix & Hthis_ptr & Hdeepown_this_pod)". wp_auto.
    specialize Hidx_val with parent_key.(KKey.Kind') parent_key.(KKey.Name') (KObjectV.objectmeta parent).(ObjectMetaV.UID').
    rewrite bool_decide_true //. wp_auto.
    wp_alloc j_ptr as "Hj_ptr". wp_auto.
    iDestruct (own_slice_len with "Hsl0") as %(Hsl0_len1 & _). simpl in Hsl0_len1.
    set I0 := (∃ (j: w64) (v: go_string) (sl': slice.t),
      "Hj_ptr" ∷ j_ptr ↦ j ∗
      "Hv_ptr" ∷ v_ptr ↦ v ∗
      "Hitems_ptr" ∷ items_ptr ↦ sl' ∗
      "Hsl'" ∷ sl' ↦* map (λ ptr : loc, interface.mk (ptrT.id v1.Pod.id) (# ptr)) ptr_list' ∗
      "Hcap_sl'" :: own_slice_cap interface.t sl' (DfracOwn 1) ∗
      "%Hneg_P" ∷ ⌜ sint.Z j = sint.Z (slice.len_f sl0) → ¬ P this_pure_pod ⌝ ∗
      "%Hj" ∷ ⌜ 0 ≤ sint.Z j ≤ sint.Z (slice.len_f sl0) ⌝
    )%I.
    iAssert (I0) with "[Hj_ptr v Hitems_ptr Hsl' Hcap_sl']" as "Hloop_inv0". {
      iExists (W64 0), (default_val go_string), sl'.
      iFrame. iPureIntro. simpl. word. }
    wp_for "Hloop_inv0". wp_if_destruct.
    + wp_pure; first word.
      wp_apply (wp_load_slice_elem with "[$Hsl0]"); [word| | ].
      { iPureIntro. assert (sint.nat j = 0%nat) as -> by word. done. }
      iIntros "Hsl0". wp_auto.
      assert (P this_pure_pod ↔ idx_val = ObjectMetaV.Namespace' (PodV.ObjectMeta' this_pure_pod) ++ "/"%go ++
                                          parent_key.(KKey.Kind') ++ "/"%go ++
                                          parent_key.(KKey.Name') ++ "/"%go ++
                                          (KObjectV.objectmeta parent).(ObjectMetaV.UID')) as Hidx_val'.
      { unfold P. apply Hidx_val. }
      simpl in Hidx_val'.
      destruct (bool_decide(P this_pure_pod)) eqn:HP.
      * apply bool_decide_eq_true in HP.
        assert (this_pure_pod.(PodV.ObjectMeta').(ObjectMetaV.Namespace') = parent_key.(KKey.Namespace')) as Hns_eq.
        { destruct Hinv_Hghost_valid. 
          assert (this_pure_pod.(PodV.ObjectMeta').(ObjectMetaV.Namespace') = (PodV.key this_pure_pod).(KKey.Namespace')) as -> by done.
          symmetry.
          apply (Hparents_children_same_namespace _ (dom pure_pod_map) _ Hlookup_children).
          pose proof (split_children_point_to_parent _ _ Hchildren_point_to_parent) as [Hchildren_point_to_parent1 Hchildren_point_to_parent2].
          assert (abs_state !! PodV.key this_pure_pod = Some (KObjectV.Pod this_pure_pod)) as Hlookup_abs'.
          { apply Hlookup_abs. apply (list_elem_of_lookup_2 _ (sint.nat i)). done. }
          apply (Hchildren_point_to_parent1 parent_key parent (PodV.key this_pure_pod) (KObjectV.Pod this_pure_pod)).
          all: try done. }
        rewrite bool_decide_true //.
        { rewrite <-Hns_eq. apply Hidx_val'. done. }
        wp_auto.
        wp_apply wp_slice_literal. iIntros (sl1) "Hsl1". wp_auto.
        wp_apply (wp_slice_append with "[$Hsl' $Hcap_sl' $Hsl1]").
        iIntros (sl'') "(Hsl'' & Hcap_sl'' & Hsl1)". wp_auto.
        wp_for_post.
        wp_for_post.
        iAssert (I) with "[Hi_ptr Hval_ptr Hitems_ptr Hsl'' Hlist_pre Hthis_ptr Hdeepown_this_pod Hother_ptr_pure_pod Hcap_sl'']" as "Hloop_inv".
        { iExists (word.add i (W64 1)), this_obj, sl'', (ptr_list' ++ [this_ptr]), ((filter P (take (sint.nat i) pure_pod_list)) ++ [this_pure_pod]).
          assert (map (λ ptr : loc, interface.mk (ptrT.id v1.Pod.id) (# ptr)) ptr_list' ++ [this_obj] =
                  map (λ ptr, interface.mk (ptrT.id v1.Pod.id) (# ptr)) (ptr_list' ++ [this_ptr])) as ->.
          { rewrite map_app. simpl.
            unfold obj_list in Hthis_obj_lookup.
            rewrite list_lookup_fmap in Hthis_obj_lookup.
            rewrite Hthis_ptr_lookup in Hthis_obj_lookup.
            simpl in Hthis_obj_lookup.
            injection Hthis_obj_lookup as <-.
            reflexivity. }
          iFrame.
          rewrite !big_sepL2_nil.
          assert (sint.nat (word.add i (W64 1)) = S (sint.nat i)) as -> by word.
          rewrite !drop_drop Nat.add_1_r.
          iFrame. iPureIntro. split; [|word].
          rewrite (take_S_r _ _ this_pure_pod Hthis_pure_pod_lookup).
          rewrite filter_app. f_equal. unfold filter. simpl.
          destruct (decide (P this_pure_pod)); [done|done]. }
        iFrame.
      * apply bool_decide_eq_false in HP.
        rewrite bool_decide_false //.
        { destruct (bool_decide(this_pure_pod.(PodV.ObjectMeta').(ObjectMetaV.Namespace') = parent_key.(KKey.Namespace'))) eqn:Hns.
          -- apply bool_decide_eq_true in Hns. rewrite <-Hns. intros Heq. apply HP. apply Hidx_val'. done.
          -- assert (slash_free (ObjectMetaV.Namespace' (PodV.ObjectMeta' this_pure_pod))) as Hslash_free1.
            { apply valid_namespace_slash_free.
              assert (PodV.valid this_pure_pod) as Hwf_pod.
              { apply Hwf. apply (list_elem_of_lookup_2 _ (sint.nat i)). done. }
              destruct Hwf_pod as [Hwf_meta _].
              eapply ObjectMetaV.valid_namespace_of_valid; exact Hwf_meta. }
            assert (slash_free (KKey.Namespace' parent_key)) as Hslash_free2.
            { apply valid_namespace_slash_free.
              destruct Hinv_Hghost_valid. 
              pose proof Habs_state_valid parent_key parent Hlookup_abs_parent as [Hparent_key Hwf_parent].
              pose proof valid_object_has_valid_key parent_key parent Hparent_key Hwf_parent as Hwf_key.
              intuition. }
            assert (ObjectMetaV.Namespace' (PodV.ObjectMeta' this_pure_pod) ≠ KKey.Namespace' parent_key) as Hneq.
            { intros H. apply bool_decide_eq_false in Hns. done. }
            destruct Hidx_val_prefix as [Hidx_val_prefix|Hidx_val_prefix].
            ++ rewrite Hidx_val_prefix. apply pod_controller_index_key_inequality1. all: done.
            ++ destruct Hidx_val_prefix as [suffix Hidx_val_prefix]. rewrite Hidx_val_prefix.
              apply pod_controller_index_key_inequality2. all: done. }
        wp_auto.
        wp_for_post.
        iAssert (I0) with "[Hj_ptr Hv_ptr Hitems_ptr Hsl' Hcap_sl']" as "Hloop_inv0".
        { iExists (word.add j (W64 1)), idx_val, sl'0. iFrame. iPureIntro. split;[|word]. intros. done. }
        iFrame.
    + wp_for_post.
      iAssert (I) with "[Hi_ptr Hval_ptr Hitems_ptr Hsl' Hlist_pre Hthis_ptr Hdeepown_this_pod Hother_ptr_pure_pod Hcap_sl']" as "Hloop_inv".
      { iExists (word.add i (W64 1)), this_obj, sl'0, ptr_list', (filter P (take (sint.nat i) pure_pod_list)).
        iFrame.
        assert (sint.nat (word.add i (W64 1)) = S (sint.nat i)) as -> by word.
        rewrite !drop_drop Nat.add_1_r.
        iFrame. iPureIntro. split; [|word].
        rewrite (take_S_r _ _ this_pure_pod Hthis_pure_pod_lookup).
        rewrite filter_app. unfold filter. simpl.
        assert (¬ P this_pure_pod) as Hnot_P.
        { apply Hneg_P. word. }
        destruct (decide (P this_pure_pod)); [done|].
        rewrite filter_nil app_nil_r. done. }
      iFrame.
  - iAssert (⌜ ∀ key pod, pure_pod_map !! key = Some pod → abs_state !! key = Some (KObjectV.Pod pod) ⌝%I)
    as "%Hsub_map".
    { iAssert (⌜ fmap KObjectV.Pod pure_pod_map ⊆ abs_state ⌝%I) as %Hsubset.
      { iApply (map_valid_subset with "Hinv_Hown_abs").
        rewrite big_sepM_fmap. iFrame "Hghost_pure_pod_map". }
      iPureIntro. intros key pod Hlookup.
      assert ((fmap KObjectV.Pod pure_pod_map) !! key = Some (KObjectV.Pod pod)) as Hlookup_fmap.
      { rewrite lookup_fmap. rewrite Hlookup. done. }
      eapply lookup_weaken; [exact Hlookup_fmap|exact Hsubset]. }
    iCombineNamed "Hinv_*" as "H".
    wp_apply (wp_Mutex__Unlock _ (kubernetes_inv γ l) with "[$Hown_Mutex H]").
    { iNamed "H". iFrame. iFrame "#". done. }
    iApply "HΦ". iFrame "Hsl' Hlist_pre". iFrame.
    iPureIntro.
    assert ((take (sint.nat i) pure_pod_list) = pure_pod_list) as ->.
    { apply take_ge. word. }
    assert (∀ key pod, pure_pod_map !! key = Some pod → P pod) as HmapP.
    { intros key pod Hlookup. destruct Hinv_Hghost_valid.
      pose proof Hsub_map key pod Hlookup as Hlookup'.
      assert (key ∈ (dom pure_pod_map)) as Hkeyin.
      { apply elem_of_dom. exists pod. done. }
      pose proof Hchildren_point_to_parent parent_key parent key (KObjectV.Pod pod) (dom pure_pod_map)
        Hlookup_abs_parent Hlookup' Hlookup_children as Hbi.
      pose proof (proj1 Hbi) Hkeyin as Hobj_has_controller_parent_of. done. }
    split_and!.
    * intros p Hpin. apply Hwf. apply list_elem_of_filter in Hpin. destruct Hpin as [_ Hpin]. done.
    * intros p Hlookup_list. apply list_elem_of_filter in Hlookup_list as [HPp Hlookup_list].
      pose proof Hlookup_abs p Hlookup_list as Hlookup_abs'.
      destruct Hinv_Hghost_valid.
      pose proof Hchildren_point_to_parent parent_key parent (PodV.key p) (KObjectV.Pod p)
        (dom pure_pod_map) Hlookup_abs_parent Hlookup_abs' Hlookup_children as Hbi.
      pose proof (proj2 Hbi) HPp as Hkey_in_dom. apply elem_of_dom in Hkey_in_dom as [p' Hlookup_map].
      pose proof Hsub_map (PodV.key p) p' Hlookup_map as Hlookup_abs''.
      rewrite Hlookup_abs' in Hlookup_abs''. injection Hlookup_abs''. intros ->. done.
    * intros k p Hlookup. pose proof HmapP k p Hlookup as HPp. apply list_elem_of_filter. split; [done|].
      pose proof Hns_match k p Hlookup. done.
    * intros k p Hlookup. destruct Hinv_Hghost_valid. pose proof Hsub_map k p Hlookup as Hlookup'.
      pose proof Habs_state_valid k (KObjectV.Pod p) Hlookup' as Hwf'. destruct Hwf' as [Hwf' _]. done.
    * apply filter_preserves_key_uniqueness. done.
    * intros k Hkindom. destruct Hinv_Hghost_valid. symmetry.
      apply (Hparents_children_same_namespace _ (dom pure_pod_map)); [done|done].
Qed.

End proof.
