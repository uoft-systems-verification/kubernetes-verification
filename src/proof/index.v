From New.proof Require Import prelude empty_ffi.
From New.proof Require Export apimodel list.
From New.proof.kubernetes_model Require Export apimodel_init.

Section proof.
Context `{!mapG Σ KKey.t PureKObject.t}.
Context `{!mapG Σ KKey.t (gset KKey.t)}.
Context `{!auth_setG Σ KKey.t}.
Context `{hG: !heapGS Σ} {go_ctx: GoContext}.

Lemma wp_index_of_podController index_name obj ptr pod pure_pod dq:
  {{{ is_pkg_init apimodel ∗
      "%Hindex_name" ∷ ⌜ index_name = "podController"%go ⌝ ∗
      "%Hobj" ∷ ⌜ obj = interface.mk (ptrT.id v1.Pod.id) #ptr ⌝ ∗
      "Hptr" ∷ ptr ↦{dq} pod ∗
      "Hdeepown_pod" ∷ PurePod.deepown pod pure_pod dq ∗
      "%Hwell_formed" ∷ ⌜ PurePod.well_formed pure_pod ⌝
  }}}
    @! apimodel.index_of #index_name #obj
  {{{ sl idx_val_list idx_val, RET (#sl, #interface.nil);
      sl ↦* idx_val_list ∗
      ⌜ idx_val_list = [idx_val] ⌝ ∗
      ⌜ ∀ parent_kind parent_name parent_uid,
        obj_has_controller_parent_of (PureKObject.Pod pure_pod) parent_kind parent_name parent_uid ↔
        idx_val = pure_pod.(PurePod.ObjectMeta').(PureObjectMeta.Namespace') ++ "/"%go ++
                  parent_kind ++ "/"%go ++ parent_name ++ "/"%go ++ parent_uid ⌝ ∗
      ⌜ idx_val = pure_pod.(PurePod.ObjectMeta').(PureObjectMeta.Namespace') ∨ (* the orphan case *)
        ∃ suffix, idx_val = pure_pod.(PurePod.ObjectMeta').(PureObjectMeta.Namespace') ++ "/"%go ++ suffix ⌝ ∗
      ptr ↦{dq} pod ∗
      PurePod.deepown pod pure_pod dq
  }}}.
Proof. Admitted.

Lemma wp_State__ByIndex_pod γ l kind index_name indexed_value
  parent_key owned_parent pure_pod_map owned_child_keys:
  {{{ is_pkg_init apimodel ∗
      "#Hisk" ∷ is_kubernetes γ l ∗
      "%Hkind" ∷ ⌜ kind = "Pod"%go ⌝ ∗
      "%Hindex_name" ∷ ⌜ index_name = "podController"%go ⌝ ∗
      "%Hindexed_value" ∷ ⌜ indexed_value = parent_key.(KKey.Namespace') ++ "/"%go ++
                                            parent_key.(KKey.Kind') ++ "/"%go ++
                                            parent_key.(KKey.Name') ++ "/"%go ++
                                            (PureKObject.metadata owned_parent).(PureObjectMeta.UID') ⌝ ∗
      "Hown_parent" ∷ parent_key [[ γ.(γ_state) ]]↦ owned_parent ∗
      "Hown_pod_list" ∷ ([∗ map] key ↦ pod ∈ pure_pod_map, key [[ γ.(γ_state) ]]↦ PureKObject.Pod pod) ∗
      "Hown_child_keys" ∷ parent_key [[ γ.(γ_children) ]]↦ owned_child_keys ∗
      "%Hdom_eq" ∷ ⌜ owned_child_keys = dom pure_pod_map ⌝
  }}}
    l @ (ptrT.id apimodel.State.id) @ "ByIndex" #kind #index_name #indexed_value
  {{{ objs_l (ptr_list: list loc) (pod_list: list v1.Pod.t) (pure_pod_list: list PurePod.t) dq, RET (#objs_l, #interface.nil);
      "Hobjs_l" ∷ objs_l ↦* map (λ ptr, interface.mk (ptrT.id v1.Pod.id) #ptr) ptr_list ∗
      "Hptrs_pods" ∷ ([∗ list] ptr;pod ∈ ptr_list;pod_list, ptr ↦{dq} pod) ∗
      "Hpods_purepods" ∷ ([∗ list] pod;pure_pod ∈ pod_list;pure_pod_list, PurePod.deepown pod pure_pod dq) ∗
      "%Hwell_formed_pure_pod_list" ∷ ⌜ ∀ p, p ∈ pure_pod_list → PurePod.well_formed p ⌝ ∗
      "%Hlen_size_eq" ∷ ⌜ length pure_pod_list = size pure_pod_map ⌝ ∗
      "%Hlist_in_map" ∷  ⌜ ∀ p, p ∈ pure_pod_list → pure_pod_map !! (PurePod.key p) = Some p ⌝ ∗
      "%Hmap_in_list" ∷ ⌜ ∀ k p, pure_pod_map !! k = Some p → p ∈ pure_pod_list ⌝ ∗
      "%Hown_pod_keys_eq" ∷ ⌜ ∀ key pod, pure_pod_map !! key = Some pod → key = PurePod.key pod ⌝ ∗
      "%Hown_pod_list_namespace_eq" ∷ ⌜ ∀ key, key ∈ dom pure_pod_map → key.(KKey.Namespace') = parent_key.(KKey.Namespace') ⌝ ∗
      "%Hno_dup" ∷ ⌜ ∀ i j p1 p2, i ≠ j → pure_pod_list !! i = Some p1 → pure_pod_list !! j = Some p2 → (PurePod.key p1) ≠ (PurePod.key p2) ⌝ ∗
      "Hown_parent" ∷ parent_key [[ γ.(γ_state) ]]↦ owned_parent ∗
      "Hown_pod_list" ∷ ([∗ map] key ↦ pod ∈ pure_pod_map, key [[ γ.(γ_state) ]]↦ PureKObject.Pod pod) ∗
      "Hown_child_keys" ∷ parent_key [[ γ.(γ_children) ]]↦ owned_child_keys
  }}}.
Proof.
  wp_start as "H". iNamed "H". iNamed "Hisk".
  wp_apply wp_with_defer. iIntros (defer) "Hdefer". simpl subst. wp_auto.
  wp_apply wp_Mutex__Lock; [done|]. iIntros "[Hown_Mutex H]". iNamedPrefix "H" "Hinv_".
  iAssert (⌜ abs_state !! parent_key = Some (owned_parent) ⌝%I) as "%Hlookup_abs_parent".
  { iDestruct (map_valid with "Hinv_Hown_abs Hown_parent") as %Hlookup. iPureIntro; exact Hlookup. }
  iAssert (⌜ children !! parent_key = Some (owned_child_keys) ⌝%I) as "%Hlookup_children".
  { iDestruct (map_valid with "Hinv_Hown_children Hown_child_keys") as %Hlookup. iPureIntro; exact Hlookup. }
  wp_auto.
  wp_apply (wp_State__objListLocked_pod with "[$Hown_pod_list $Hinv_Hstate_m_addr $Hinv_Hown_phys $Hinv_Hown_abs $Hinv_Hphys_abs_rep]").
  { iPureIntro. split; [done|]. destruct Hinv_Hghost_well_formed. done. }
  iIntros (sl ptr_list pod_list pure_pod_list) "(Hsl & Hptr_pod_list & Hpod_pure_pod_list & %Hwell_formed & %Hlookup_abs
    & %Hns_match & %Hmap_in_list & Hinv_Hstate_m_addr & Hinv_Hown_phys & Hinv_Hown_abs & Hinv_Hphys_abs_rep & Hown_pod_list)". wp_auto.
  assert (∀ (k : KKey.t) (p : PurePod.t), pure_pod_map !! k = Some p → p ∈ pure_pod_list) as Hns_match'.
  { intros k p Hlookup. apply (Hmap_in_list k p Hlookup). unfold namespace_matches. left. done. }
  clear Hns_match. rename Hns_match' into Hns_match.
  set obj_list := map (λ ptr : loc, interface.mk (ptrT.id v1.Pod.id) (# ptr)) ptr_list.
  assert (length obj_list = length ptr_list) as Hlen_obj_ptr.
  { unfold obj_list. rewrite map_length. done. }
  iPoseProof own_slice_nil as "Hslice_nil".
  iPoseProof own_slice_cap_nil as "Hown_slice_nil_cap".
  iDestruct (own_slice_len with "Hsl") as %(Hsl_len1 & Hsl_len2).
  iDestruct (own_slice_wf with "Hsl") as %Hsl_cap.
  iDestruct (big_sepL2_length with "Hptr_pod_list") as %Hlen_ptr_pod.
  iDestruct (big_sepL2_length with "Hpod_pure_pod_list") as %Hlen_pod_pure_pod.
  set P := (λ p, obj_has_controller_parent_of (PureKObject.Pod p) parent_key.(KKey.Kind') parent_key.(KKey.Name') (PureKObject.metadata owned_parent).(PureObjectMeta.UID')).
  set I := (∃ (i: w64) (val: interface.t) (sl': slice.t) (ptr_list': list loc) (pod_list': list v1.Pod.t) (pure_pod_list': list PurePod.t),
    "Hi_ptr" ∷ i_ptr ↦ i ∗
    "Hval_ptr" ∷ val_ptr ↦ val ∗
    "Hitems_ptr" ∷ items_ptr ↦ sl' ∗
    "Hsl'" ∷ sl' ↦* map (λ ptr : loc, interface.mk (ptrT.id v1.Pod.id) (# ptr)) ptr_list' ∗
    "Hptr_pod_list_pre" ∷ ([∗ list] ptr;pod ∈ ptr_list';pod_list', ptr ↦ pod) ∗
    "Hptr_pod_list_post" ∷ ([∗ list] ptr;pod ∈ (drop (sint.nat i) ptr_list);(drop (sint.nat i) pod_list), ptr ↦ pod) ∗
    "Hpod_pure_pod_list_pre" ∷ ([∗ list] pod;pure_pod ∈ pod_list';pure_pod_list', PurePod.deepown pod pure_pod 1) ∗
    "Hpod_pure_pod_list_post" ∷ ([∗ list] pod;pure_pod ∈ (drop (sint.nat i) pod_list);(drop (sint.nat i) pure_pod_list), PurePod.deepown pod pure_pod 1) ∗
    "Hcap_sl'" :: own_slice_cap interface.t sl' (DfracOwn 1) ∗
    "%Hfilter_ptr_list" ∷ ⌜ pure_pod_list' = filter P (take (sint.nat i) pure_pod_list) ⌝ ∗
    "%Hi" ∷ ⌜ 0 ≤ sint.Z i ≤ sint.Z (slice.len_f sl) ⌝
  )%I.
  iAssert (I) with "[i val items Hptr_pod_list Hpod_pure_pod_list]" as "Hloop_inv". {
    iExists (W64 0), (default_val interface.t), (default_val slice.t), [], [], [].
    iFrame. iFrame "#". rewrite !big_sepL2_nil. done. }
  wp_for "Hloop_inv". wp_if_destruct.
  - wp_pure; first word.
    list_elem obj_list (sint.Z i) as this_obj.
    wp_apply (wp_load_slice_elem with "[$Hsl]"); [word|eauto| ]. iIntros "Hsl". wp_auto.
    assert (∃ this_ptr, ptr_list !! sint.nat i = Some this_ptr) as [this_ptr Hthis_ptr_lookup].
    { apply lookup_lt_is_Some_2. word. }
    assert (∃ this_pod, pod_list !! sint.nat i = Some this_pod) as [this_pod Hthis_pod_lookup].
    { apply lookup_lt_is_Some_2. word. }
    assert (∃ this_pure_pod, pure_pod_list !! sint.nat i = Some this_pure_pod) as [this_pure_pod Hthis_pure_pod_lookup].
    { apply lookup_lt_is_Some_2. word. }
    iPoseProof (big_sepL2_destruct_cons _ _ _ this_ptr this_pod with "Hptr_pod_list_post") as "[Hthis_ptr Hother_ptr_pod]".
    { split. all: rewrite lookup_drop Nat.add_0_r; done. }
    iPoseProof (big_sepL2_destruct_cons _ _ _ this_pod this_pure_pod with "Hpod_pure_pod_list_post") as "[Hdeepown_this_pod Hother_pod_pure_pod]".
    { split. all: rewrite lookup_drop Nat.add_0_r; done. }
    wp_apply (wp_index_of_podController with "[$Hthis_ptr $Hdeepown_this_pod]").
    { iPureIntro. split_and!; [done| | ].
      - unfold obj_list in Hthis_obj_lookup. rewrite list_lookup_fmap in Hthis_obj_lookup.
        rewrite Hthis_ptr_lookup in Hthis_obj_lookup. simpl in Hthis_obj_lookup.
        injection Hthis_obj_lookup. done.
      - apply Hwell_formed. apply (list_elem_of_lookup_2 _ (sint.nat i)). done. }
    iIntros (sl0 idx_val_list idx_val) "(Hsl0 & -> & %Hidx_val & %Hidx_val_prefix & Hthis_ptr & Hdeepown_this_pod)". wp_auto.
    specialize Hidx_val with parent_key.(KKey.Kind') parent_key.(KKey.Name') (PureKObject.metadata owned_parent).(PureObjectMeta.UID').
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
      assert (P this_pure_pod ↔ idx_val = PureObjectMeta.Namespace' (PurePod.ObjectMeta' this_pure_pod) ++ "/"%go ++
                                          parent_key.(KKey.Kind') ++ "/"%go ++
                                          parent_key.(KKey.Name') ++ "/"%go ++
                                          (PureKObject.metadata owned_parent).(PureObjectMeta.UID')) as Hidx_val'.
      { unfold P. apply Hidx_val. }
      simpl in Hidx_val'.
      destruct (bool_decide(P this_pure_pod)) eqn:HP.
      * apply bool_decide_eq_true in HP.
        assert (this_pure_pod.(PurePod.ObjectMeta').(PureObjectMeta.Namespace') = parent_key.(KKey.Namespace')) as Hns_eq.
        { destruct Hinv_Hghost_well_formed. 
          assert (this_pure_pod.(PurePod.ObjectMeta').(PureObjectMeta.Namespace') = (PurePod.key this_pure_pod).(KKey.Namespace')) as -> by done.
          symmetry.
          apply (Hparents_children_same_namespace _ (dom pure_pod_map) _ Hlookup_children).
          pose proof (split_children_point_to_parent _ _ Hchildren_point_to_parent) as [Hchildren_point_to_parent1 Hchildren_point_to_parent2].
          assert (abs_state !! PurePod.key this_pure_pod = Some (PureKObject.Pod this_pure_pod)) as Hlookup_abs'.
          { apply Hlookup_abs. apply (list_elem_of_lookup_2 _ (sint.nat i)). done. }
          apply (Hchildren_point_to_parent1 parent_key owned_parent (PurePod.key this_pure_pod) (PureKObject.Pod this_pure_pod)).
          all: try done. }
        rewrite bool_decide_true //.
        { rewrite <-Hns_eq. apply Hidx_val'. done. }
        wp_auto.
        wp_apply wp_slice_literal. iIntros (sl1) "Hsl1". wp_auto.
        wp_apply (wp_slice_append with "[$Hsl' $Hcap_sl' $Hsl1]").
        iIntros (sl'') "(Hsl'' & Hcap_sl'' & Hsl1)". wp_auto.
        wp_for_post.
        wp_for_post.
        iAssert (I) with "[Hi_ptr Hval_ptr Hitems_ptr Hsl'' Hptr_pod_list_pre Hthis_ptr Hother_ptr_pod
          Hpod_pure_pod_list_pre Hdeepown_this_pod Hother_pod_pure_pod Hcap_sl'']" as "Hloop_inv".
        { iExists (word.add i (W64 1)), this_obj, sl'', (ptr_list' ++ [this_ptr]), (pod_list' ++ [this_pod]), ((filter P (take (sint.nat i) pure_pod_list)) ++ [this_pure_pod]).
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
          destruct (decide (P this_pure_pod)); [done|done].
        }
        iFrame.
      * apply bool_decide_eq_false in HP.
        rewrite bool_decide_false //.
        { destruct (bool_decide(this_pure_pod.(PurePod.ObjectMeta').(PureObjectMeta.Namespace') = parent_key.(KKey.Namespace'))) eqn:Hns.
          -- apply bool_decide_eq_true in Hns. rewrite <-Hns. intros Heq. apply HP. apply Hidx_val'. done.
          -- destruct Hidx_val_prefix as [Hidx_val_prefix|Hidx_val_prefix].
            ++ admit.
            ++ admit. }
        wp_auto.
        wp_for_post.
        iAssert (I0) with "[Hj_ptr Hv_ptr Hitems_ptr Hsl' Hcap_sl']" as "Hloop_inv0".
        { iExists (word.add j (W64 1)), idx_val, sl'0. iFrame. iPureIntro. split;[|word]. intros. done. }
        iFrame.
    + wp_for_post.
      iAssert (I) with "[Hi_ptr Hval_ptr Hitems_ptr Hsl' Hptr_pod_list_pre Hthis_ptr Hother_ptr_pod
        Hpod_pure_pod_list_pre Hdeepown_this_pod Hother_pod_pure_pod Hcap_sl']" as "Hloop_inv".
      { iExists (word.add i (W64 1)), this_obj, sl'0, ptr_list', pod_list', (filter P (take (sint.nat i) pure_pod_list)).
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
  - iCombineNamed "Hinv_*" as "H".
    wp_apply (wp_Mutex__Unlock _ (kubernetes_inv γ l) with "[$Hown_Mutex H]").
    { iNamed "H". iFrame. iFrame "#". done. }
    iApply "HΦ". iFrame "Hsl' Hptr_pod_list_pre Hpod_pure_pod_list_pre". iFrame.
    iPureIntro.
    assert ((take (sint.nat i) pure_pod_list) = pure_pod_list) as ->.
    { apply take_ge. word. }
    split_and!.
    * intros p Hpin. apply Hwell_formed. apply list_elem_of_filter in Hpin. destruct Hpin as [_ Hpin]. done.
    * admit.
    * admit.
    * admit.
    * admit.
    * admit.
    * admit. 
Admitted.

End proof.
