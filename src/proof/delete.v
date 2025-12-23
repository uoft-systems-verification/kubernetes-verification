From New.proof Require Import prelude empty_ffi.
From New.proof Require Export apimodel.
Export apimodel.apimodel.

Section proof.
Context `{hG: !heapGS Σ} {go_ctx: GoContext}.
Context `{!mapG Σ KKey.t interface.t}.
Context `{!mapG Σ KKey.t PureKObject.t}.
Context `{!mapG Σ KKey.t (gset KKey.t)}.
Context `{!auth_setG Σ KKey.t}.

Lemma wp_State__objDelete_pod γ l key
  pure_pod parent_key owned_child_keys owned_grandchild_keys:
  {{{ is_pkg_init apimodel ∗
      "#Hisk" ∷ is_kubernetes γ l ∗
      "%Hpod_is_child" ∷ ⌜ key ∈ owned_child_keys ⌝ ∗
      "%Hkind_is_pod" ∷ ⌜ KKey.Kind' key = "Pod"%go ⌝ ∗
      "Hown_pod" ∷ key [[ γ.(γ_state) ]]↦ (PureKObject.Pod pure_pod) ∗
      "Hown_child_keys" ∷ parent_key [[ γ.(γ_children) ]]↦ owned_child_keys ∗
      "Hown_grandchild_keys" ∷ key [[ γ.(γ_children) ]]↦ owned_grandchild_keys
  }}}
    l @ (ptrT.id apimodel.State.id) @ "objDelete" #key
  {{{ updated_pure_pod, RET #interface.nil;
      "pod_updated_or_deleted" ∷ ("pod_updated" ∷ (
        "%deletiontimestamp_notnull" ∷ ⌜ updated_pure_pod.(PurePod.ObjectMeta').(PureObjectMeta.DeletionTimestamp') ≠ None ⌝ ∗
        "Hown_pod" ∷ key [[ γ.(γ_state) ]]↦ (PureKObject.Pod updated_pure_pod) ∗
        "Hown_child_keys" ∷ parent_key [[ γ.(γ_children) ]]↦ owned_child_keys ∗
        "Hown_grandchild_keys" ∷ key [[ γ.(γ_children) ]]↦ owned_grandchild_keys
      ) ∨
      "Hown_child_keys" ∷ parent_key [[ γ.(γ_children) ]]↦ (owned_child_keys ∖ {[key]}))
  }}}.
Proof.
  wp_start as "H". iNamed "H". iNamed "Hisk". wp_apply wp_with_defer. iIntros (defer) "Hdefer". simpl subst. wp_auto.
  wp_apply wp_Mutex__Lock; [done|]. iIntros "[Hown_Mutex H]". iNamedPrefix "H" "Hinv_". wp_auto.
  iAssert (⌜ abs_state !! key = Some (PureKObject.Pod pure_pod) ⌝%I) as "%Hkey_in_abs".
  { iDestruct (map_valid with "Hinv_Hown_abs Hown_pod") as %Hlookup. iPureIntro; done. }
  iAssert (⌜ children !! parent_key = Some owned_child_keys ⌝%I) as "%Hparent_key_in_children".
  { iDestruct (map_valid with "Hinv_Hown_children Hown_child_keys") as %Hlookup. iPureIntro; done. }
  iAssert (⌜ children !! key = Some owned_grandchild_keys ⌝%I) as "%Hkey_in_children".
  { iDestruct (map_valid with "Hinv_Hown_children Hown_grandchild_keys") as %Hlookup. iPureIntro; done. }
  iAssert (⌜ ∃ obj, phys_state !! key = Some obj ⌝%I) as "%Hkey_in_phys".
  {
    iDestruct (big_sepM2_lookup_r with "Hinv_Hphys_abs_rep") as (obj Hkey_in_phys) "_"; [done|].
    iPureIntro. exists obj. done.
  }
  destruct Hkey_in_phys as [obj Hkey_in_phys].
  iDestruct (big_sepM2_split_singleton _ key _ _ phys_state abs_state Hkey_in_phys Hkey_in_abs
    with "Hinv_Hphys_abs_rep") as "[Hk_rep Hother_rep]".
  destruct decide_kind_is_pod with (KKey.Kind' key) as [kind_is_pod kind_is_not_replicaset]; [done|].
  iAssert (∃ ptr pod pure_pod', pod_rep obj (PureKObject.Pod pure_pod) ptr pod pure_pod')%I
  with "[Hk_rep]" as "(%ptr & %pod & %pure_pod' & Hpod_rep)".
  { unfold obj_rep. rewrite kind_is_pod. iDestruct "Hk_rep" as "(%ptr & %pod & %pure_pod' & H)". iExists ptr, pod, pure_pod'. iFrame. }
  iNamed "Hpod_rep".
  injection Habs_v_is_pod as <-.
  wp_apply (wp_map_get with "[$Hinv_Hown_phys]"). iIntros "Hinv_Hown_phys". wp_auto.
  rewrite /is_Some Hkey_in_phys. wp_auto.
  wp_apply wp_Accessor; [done|].
  assert ((bool_decide (interface.nil = interface.nil)) = true) as nil_is_nil.
  { rewrite bool_decide_true //. }
  rewrite nil_is_nil. wp_auto.
  iDestruct "Hdeepown_l_pod" as "[Hpod_ptr Hdeepown_pod]".
  iDestruct (struct_fields_split with "Hpod_ptr") as "H". iNamed "H".
  wp_apply (wp_GetFinalizers with "[$HObjectMeta]").
  iIntros "HObjectMeta". wp_auto.
  wp_if_destruct.
  - wp_apply (wp_GetDeletionTimestamp with "[$HObjectMeta]"). iIntros "HObjectMeta". wp_auto.
    wp_if_destruct.
    + wp_apply v1.wp_Now. iIntros (time pure_time) "Hdeepown_time". wp_auto.
      wp_apply (wp_SetDeletionTimestamp with "[$HObjectMeta]"). iIntros "HObjectMeta". wp_auto.
      wp_apply wp_strconv_FormatInt. iIntros (rv_str) "_". wp_auto.
      wp_apply (wp_SetResourceVersion with "[$HObjectMeta]"). iIntros "HObjectMeta". wp_auto.
      iDestruct (struct_fields_combine (v:=v1.Pod.mk _ _ _ _)
        with "[$HTypeMeta $HObjectMeta $HSpec $HStatus]") as "Hpod_ptr". simpl.
      iDestruct (rename_pod with "Hpod_ptr") as "(%updated_pod & Hpod_ptr & %Hupdated_pod_eq)".
      set updated_pure_meta := pure_pod.(PurePod.ObjectMeta')
        <| PureObjectMeta.ResourceVersion' := rv_str |>
        <| PureObjectMeta.DeletionTimestamp' := Some pure_time |>.
      set updated_pure_pod := pure_pod <| PurePod.ObjectMeta' := updated_pure_meta |>.
      iMod (auth_map.map_update _ _ (PureKObject.Pod updated_pure_pod) with "Hinv_Hown_abs Hown_pod")
        as "[Hinv_Hown_abs Hown_pod]".
      iAssert (state_rep phys_state (<[key:=PureKObject.Pod updated_pure_pod]> abs_state) %I)
      with "[Hpod_ptr Hdeepown_pod Hother_rep Hdeepown_time now]" as "Hinv_Hphys_abs_rep".
      { assert (delete key abs_state = delete key (<[key:=PureKObject.Pod updated_pure_pod]> abs_state)) as ->.
        { rewrite delete_insert_eq. reflexivity. }
        iApply (big_sepM2_split_singleton _ key _ (PureKObject.Pod updated_pure_pod) phys_state (<[key:=PureKObject.Pod updated_pure_pod]> abs_state)
          Hkey_in_phys with "[$Hother_rep Hpod_ptr Hdeepown_pod Hdeepown_time now]").
        { rewrite lookup_insert. destruct (decide (key = key)) as [|Hcontra]; [done|done]. }
        unfold obj_rep. rewrite kind_is_pod. iExists ptr, updated_pod, updated_pure_pod. unfold pod_rep.
        iSplit;[done|iSplit;[done|]].
        iNamed "Hdeepown_pod". iFrame. iSplitR; [iPureIntro; rewrite Hupdated_pod_eq //|].
        iNamed "Hdeepown_objectmeta". rewrite Hupdated_pod_eq //.
        iAssert (⌜ now_ptr ≠ null ⌝%I) as "%now_ptr_not_null".
        { by iDestruct (typed_pointsto_not_null with "now") as %?. }
        iFrame. iPureIntro. done. }
      assert (ghost_well_formed (dom used_uid) (<[key:=PureKObject.Pod updated_pure_pod]> abs_state) children fresh_keys)
      as Hinv_Hghost_well_formed'.
      {
        destruct Hinv_Hghost_well_formed.
        assert (parent_key ≠ key) as parent_neq_key.
        { specialize (Hno_self_parenting parent_key owned_child_keys key Hparent_key_in_children Hpod_is_child). done. }
        assert (dom (<[key:=PureKObject.Pod updated_pure_pod]> abs_state) = dom abs_state) as abs_dom_simpl.
        { rewrite dom_insert_L.
          assert ({[key]} ∪ dom abs_state = dom abs_state) as ->.
          { set_solver. }
          reflexivity. }
        assert ((PureKObject.metadata (PureKObject.Pod updated_pure_pod)).(PureObjectMeta.OwnerReferences') = (PureKObject.metadata (PureKObject.Pod pure_pod)).(PureObjectMeta.OwnerReferences'))
        as updated_pure_pod_owner_references_eq.
        { simpl. subst updated_pure_pod. simpl. reflexivity. }
        assert ((PureKObject.metadata (PureKObject.Pod updated_pure_pod)).(PureObjectMeta.UID') = (PureKObject.metadata (PureKObject.Pod pure_pod)).(PureObjectMeta.UID'))
        as updated_pure_pod_uid_eq.
        { simpl. subst updated_pure_pod. simpl. reflexivity. }
        assert (PureKObject.agree_with_key (PureKObject.Pod updated_pure_pod) key ∧ PureKObject.well_formed (PureKObject.Pod updated_pure_pod))
          as [Hagree Hwell_formed].
        { assert (PureKObject.agree_with_key (PureKObject.Pod pure_pod) key ∧ PureKObject.well_formed (PureKObject.Pod pure_pod))
          as [Hagree Hwell_formed].
          { apply Habs_state_well_formed. done. } done. }
        apply mk_ghost_well_formed.
        - intros k obj Hlookup.
          rewrite lookup_insert_Some in Hlookup.
          destruct Hlookup as [(<- & <-) | (Hk_neq & Hlookup)].
          + done.
          + eapply Habs_state_well_formed. done.
        - set_solver.
        - intros k s Hlookup. specialize (Hchildren_exist k s Hlookup). rewrite dom_insert_L. set_solver.
        - apply Hparents_children_same_namespace.
        - apply Hno_self_parenting.
        - apply Hchildren_disjoint.
        - rewrite dom_insert_L. set_solver.
        - apply Hfresh_keys_reserved.
        - intros k1 k2 obj1 obj2 Hlookup1 Hlookup2 Huid_eq.
          rewrite lookup_insert_Some in Hlookup1.
          rewrite lookup_insert_Some in Hlookup2.
          destruct Hlookup1 as [(<- & Hobj1_eq) | (Hk1_neq & Hlookup_obj1)];
          destruct Hlookup2 as [(<- & Hobj2_eq) | (Hk2_neq & Hlookup_obj2)].
          + done.
          + eapply Hno_duplicate_uid; [eauto|eauto|].
            rewrite -Huid_eq -Hobj1_eq. done.
          + eapply Hno_duplicate_uid; [eauto|eauto|].
            rewrite Huid_eq -Hobj2_eq. done.
          + eapply Hno_duplicate_uid; [eauto|eauto|done].
        - intros k obj Hlookup.
          rewrite lookup_insert_Some in Hlookup.
          destruct Hlookup as [(<- & <-) | (Hk_neq & Hlookup_obj)].
          + rewrite updated_pure_pod_uid_eq. eapply Hexisting_uid_is_used. done.
          + eapply Hexisting_uid_is_used. done.
        - intros key_p obj_p key_c obj_c s Hlookup_p Hlookup_c Hlookup_children.
          rewrite lookup_insert_Some in Hlookup_p.
          rewrite lookup_insert_Some in Hlookup_c.
          split; [intros Hkey_in_s|intros Hobj_has_controller_parent_of];
          destruct Hlookup_p as [(<- & <-) | (Hkey_p_neq & Hlookup_p)];
          destruct Hlookup_c as [(<- & <-) | (Hkey_c_neq & Hlookup_c)].
          + exfalso. by apply (Hno_self_parenting key s key Hlookup_children Hkey_in_s).
          + rewrite updated_pure_pod_uid_eq. eapply Hchildren_point_to_parent; [done|done|done|done].
          + unfold obj_has_controller_parent_of. rewrite updated_pure_pod_owner_references_eq.
            eapply Hchildren_point_to_parent; [done|done|done|done].
          + eapply Hchildren_point_to_parent; [done|done|done|done].
          + rewrite updated_pure_pod_uid_eq in Hobj_has_controller_parent_of.
            pose proof ((proj2 (Hchildren_point_to_parent _ _ _ _ _ Hkey_in_abs Hkey_in_abs Hlookup_children) Hobj_has_controller_parent_of)). done.
          + rewrite updated_pure_pod_uid_eq in Hobj_has_controller_parent_of.
            pose proof ((proj2 (Hchildren_point_to_parent _ _ _ _ _ Hkey_in_abs Hlookup_c Hlookup_children) Hobj_has_controller_parent_of)). done.
          + unfold obj_has_controller_parent_of in Hobj_has_controller_parent_of.
            rewrite updated_pure_pod_owner_references_eq in Hobj_has_controller_parent_of.
            pose proof ((proj2 (Hchildren_point_to_parent _ _ _ _ _ Hlookup_p Hkey_in_abs Hlookup_children) Hobj_has_controller_parent_of)). done.
          + pose proof ((proj2 (Hchildren_point_to_parent _ _ _ _ _ Hlookup_p Hlookup_c Hlookup_children) Hobj_has_controller_parent_of)). done.
        - intros k obj kind name uid Hlookup Href.
          rewrite lookup_insert_Some in Hlookup.
          destruct Hlookup as [(<- & <-) | (Hkey_neq & Hlookup)].
          + unfold obj_has_controller_parent_of in Href.
            rewrite updated_pure_pod_owner_references_eq in Href.
            eapply Hparent_uid_is_used; [done|done].
          + eapply Hparent_uid_is_used; [done|done].
      }
      iCombineNamed "Hinv_*" as "H".
      wp_apply (wp_Mutex__Unlock _ (kubernetes_inv γ l) with "[$Hown_Mutex H]").
      { iNamed "H". iFrame. iFrame "#". done. }
      iApply "HΦ". iLeft. iFrame. done.
    + iDestruct (struct_fields_combine (V:=v1.Pod.t) with "[$HTypeMeta $HObjectMeta $HSpec $HStatus]") as "Hpod_ptr".
      iAssert (⌜ pure_pod.(PurePod.ObjectMeta').(PureObjectMeta.DeletionTimestamp') ≠ None ⌝%I) as "%Hdeletiontimestamp_not_none". {
        iNamed "Hdeepown_pod". iNamed "Hdeepown_objectmeta". iPureIntro. intros H. apply (proj2 Hdeepown_deletiontimestamp_none) in H. done. }
      iAssert (state_rep phys_state abs_state %I) with "[Hpod_ptr Hother_rep Hdeepown_pod]" as "Hinv_Hphys_abs_rep". {
        iApply big_sepM2_split_singleton; [done | done|]. iFrame. unfold obj_rep. rewrite kind_is_pod.
        iExists ptr, pod, pure_pod. iFrame. iFrame "#". done. }
      iCombineNamed "Hinv_*" as "H".
      wp_apply (wp_Mutex__Unlock _ (kubernetes_inv γ l) with "[$Hown_Mutex H]").
      { iNamed "H". iFrame. iFrame "#". done. }
      iApply "HΦ". iLeft. iFrame. done.
  - wp_apply (wp_map_delete with "[$Hinv_Hown_phys]"). iIntros "Hinv_Hown_phys". wp_auto.
    iDestruct (struct_fields_combine (V:=v1.Pod.t)
      with "[$HTypeMeta $HObjectMeta $HSpec $HStatus]") as "Hpod_ptr".
    iMod (auth_map.map_delete with "Hown_pod Hinv_Hown_abs") as "Hinv_Hown_abs".
    iMod (auth_map.map_update _ _ (owned_child_keys ∖ {[key]}) with "Hinv_Hown_children Hown_child_keys")
      as "[Hinv_Hown_children Hown_child_keys]".
    iMod (auth_map.map_delete with "Hown_grandchild_keys Hinv_Hown_children") as "Hinv_Hown_children".
    iAssert (state_rep (delete key phys_state) (delete key abs_state) %I) with "[Hother_rep]" as "Hinv_Hphys_abs_rep"; [done|].
    assert (ghost_well_formed (dom used_uid) (delete key abs_state) (delete key (<[parent_key:=owned_child_keys ∖ {[key]}]> children)) fresh_keys) as Hinv_Hghost_well_formed'.
    {
      destruct Hinv_Hghost_well_formed.
      assert (parent_key ≠ key) as parent_neq_key.
      { specialize (Hno_self_parenting parent_key owned_child_keys key Hparent_key_in_children Hpod_is_child). done. }
      assert (dom (delete key (<[parent_key:=owned_child_keys ∖ {[key]}]> children)) = dom (delete key children) )
      as Hdom_children_eq. {
        assert (key ≠ parent_key) as key_neq_parent by (symmetry; exact parent_neq_key).
        rewrite !dom_delete_L dom_insert_L.
        assert (parent_key ∈ dom children) as parent_in_children_dom.
        { apply elem_of_dom. exists owned_child_keys. exact Hparent_key_in_children. }
        assert ({[parent_key]} ∪ dom children = dom children) as ->.
        { set_solver. }
        reflexivity. }
      apply mk_ghost_well_formed.
      - intros k obj Hlookup. rewrite lookup_delete_Some in Hlookup.
        eapply Habs_state_well_formed. intuition.
      - set_solver.
      - intros k s Hlookup.
        rewrite lookup_delete_Some lookup_insert_Some in Hlookup.
        destruct Hlookup as (Hk_neq_key & [(<- & <-) | (Hk_neq_parent & Hlookup)]).
        + rewrite dom_delete_L.
          assert (owned_child_keys ⊆ dom abs_state) as owned_children_in_abs.
          { apply Hchildren_exist with (k := parent_key). exact Hparent_key_in_children. }
          set_solver.
        + rewrite dom_delete_L.
          assert (s ⊆ dom abs_state) as s_in_abs by (apply Hchildren_exist with (k := k); exact Hlookup).
          assert (s ## owned_child_keys) as s_disj_owned.
          { destruct (decide (k = parent_key)); [congruence|]. eapply Hchildren_disjoint; done. }
          assert (key ∉ s) as key_not_in_s.
          { intros Hcontra. assert (key ∈ owned_child_keys) by exact Hpod_is_child. set_solver. }
          set_solver.
      - intros k s child_key Hlookup Hchild_in_s.
        rewrite lookup_delete_Some lookup_insert_Some in Hlookup.
        destruct Hlookup as (Hk_neq_key & [(<- & <-) | (Hk_neq_parent & Hlookup)]).
        + eapply Hparents_children_same_namespace; [exact Hparent_key_in_children | set_solver].
        + eapply Hparents_children_same_namespace; done.
      - intros k s child_key Hlookup Hchild_in_s.
        rewrite lookup_delete_Some lookup_insert_Some in Hlookup.
        destruct Hlookup as (Hk_neq_key & [(<- & <-) | (Hk_neq_parent & Hlookup)]).
        + eapply Hno_self_parenting; [exact Hparent_key_in_children | set_solver].
        + eapply Hno_self_parenting; done.
      - intros k1 s1 k2 s2 Hk1_neq_k2 Hlookup1 Hlookup2.
        rewrite lookup_delete_Some lookup_insert_Some in Hlookup1.
        rewrite lookup_delete_Some lookup_insert_Some in Hlookup2.
        destruct Hlookup1 as (Hk1_neq_key & [(<- & <-) | (Hk1_neq_parent & Hlookup1)]);
        [destruct Hlookup2 as (Hk2_neq_key & [(<- & <-) | (Hk2_neq_parent & Hlookup2)]) |
         destruct Hlookup2 as (Hk2_neq_key & [(<- & <-) | (Hk2_neq_parent & Hlookup2)])].
        + contradiction.
        + assert (owned_child_keys ## s2) as disj_orig.
          { apply Hchildren_disjoint with (k1 := parent_key) (k2 := k2); [|assumption|assumption].
            intros Heq. subst. contradiction. }
          set_solver.
        + assert (s1 ## owned_child_keys) as disj_orig.
          { apply Hchildren_disjoint with (k1 := k1) (k2 := parent_key); [|assumption|assumption].
            intros Heq. subst. contradiction. }
          set_solver.
        + apply Hchildren_disjoint with (k1 := k1) (k2 := k2); assumption.
      - rewrite dom_delete_L. set_solver.
      - apply Hfresh_keys_reserved.
      - intros k1 k2 obj1 obj2 Hlookup1 Hlookup2 Huid_eq.
        rewrite lookup_delete_Some in Hlookup1.
        rewrite lookup_delete_Some in Hlookup2.
        destruct Hlookup1 as (Hk1_neq_key & Hlookup_obj1).
        destruct Hlookup2 as (Hk2_neq_key & Hlookup_obj2).
        eapply Hno_duplicate_uid; [eauto|eauto|done].
      - intros k obj Hlookup.
        rewrite lookup_delete_Some in Hlookup.
        destruct Hlookup as (Hk_neq_key & Hlookup_obj).
        eapply Hexisting_uid_is_used. done.
      - intros key_p obj_p key_c obj_c s Hlookup_p Hlookup_c Hlookup_children.
        rewrite lookup_delete_Some in Hlookup_children.
        rewrite lookup_delete_Some in Hlookup_p.
        rewrite lookup_delete_Some in Hlookup_c.
        split;
        destruct Hlookup_children as [Hkey_p_neq Hlookup_children];
        destruct Hlookup_p as [Hkey_p_neq' Hlookup_p];
        destruct Hlookup_c as [Hkey_c_neq Hlookup_c];
        rewrite lookup_insert_Some in Hlookup_children;
        destruct Hlookup_children as [(<- & <-) | (Hkey_p_neq'' & Hlookup_children)].
        + intros Hkey_c_in_s. eapply Hchildren_point_to_parent; [done|done|done|set_solver].
        + intros Hkey_c_in_s. eapply Hchildren_point_to_parent; [done|done|done|done].
        + intros Hobj_has_controller_parent_of.
          pose proof ((proj2 (Hchildren_point_to_parent _ _ _ _ _ Hlookup_p Hlookup_c Hparent_key_in_children) Hobj_has_controller_parent_of)). set_solver.
        + intros Hobj_has_controller_parent_of.
          pose proof ((proj2 (Hchildren_point_to_parent _ _ _ _ _ Hlookup_p Hlookup_c Hlookup_children) Hobj_has_controller_parent_of)). done.
      - intros k obj kind name uid Hlookup.
        rewrite lookup_delete_Some in Hlookup.
        destruct Hlookup as (Hk_neq_key & Hlookup_obj).
        eapply Hparent_uid_is_used. done.
    }
    iCombineNamed "Hinv_*" as "H".
    wp_apply (wp_Mutex__Unlock _ (kubernetes_inv γ l) with "[$Hown_Mutex H]").
    { iNamed "H". iFrame. iFrame "#". done. }
    iApply "HΦ". iFrame.
    Unshelve. done.
Qed.

Lemma wp_State__PodDelete γ l namespace name
  pure_pod parent_key owned_child_keys owned_grandchild_keys:
  {{{ is_pkg_init apimodel ∗
      "#inv" ∷ is_kubernetes γ l ∗
      "Hown_pod" ∷ (mk_pod_key namespace name) [[ γ.(γ_state) ]]↦ (PureKObject.Pod pure_pod) ∗
      "Hown_child_keys" ∷ parent_key [[ γ.(γ_children) ]]↦ owned_child_keys ∗
      "Hown_grandchild_keys" ∷ (mk_pod_key namespace name) [[ γ.(γ_children) ]]↦ owned_grandchild_keys ∗
      "%Hpod_is_child" ∷ ⌜ (mk_pod_key namespace name) ∈ owned_child_keys ⌝
  }}}
    l @ (ptrT.id apimodel.State.id) @ "PodDelete" #namespace #name
  {{{ updated_pure_pod, RET #interface.nil;
      "pod_updated_or_deleted" ∷ ("pod_updated" ∷ (
        "%deletiontimestamp_notnull" ∷ ⌜ updated_pure_pod.(PurePod.ObjectMeta').(PureObjectMeta.DeletionTimestamp') ≠ None ⌝ ∗
        "Hown_pod" ∷ (mk_pod_key namespace name) [[ γ.(γ_state) ]]↦ (PureKObject.Pod updated_pure_pod) ∗
        "Hown_child_keys" ∷ parent_key [[ γ.(γ_children) ]]↦ owned_child_keys ∗
        "Hown_grandchild_keys" ∷ (mk_pod_key namespace name) [[ γ.(γ_children) ]]↦ owned_grandchild_keys
      ) ∨
      "Hown_child_keys" ∷ parent_key [[ γ.(γ_children) ]]↦ (owned_child_keys ∖ {[mk_pod_key namespace name]}))
  }}}.
Proof.
  wp_start as "H". iNamed "H". wp_auto.
  wp_apply (wp_State__objDelete_pod with "[$Hown_pod $Hown_child_keys $Hown_grandchild_keys]").
  { iFrame "#". done. }
  iIntros (updated_pure_pod) "H". iNamed "H". wp_auto. iApply "HΦ". iFrame.
Qed.

End proof.
