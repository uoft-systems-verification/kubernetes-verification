From New.proof Require Import prelude empty_ffi.
From New.proof.simple Require Export apimodel.
From New.proof Require Export external_wp.

Section proof.
Context `{hG: !heapGS Σ} {go_ctx: GoContext}.
Context `{!mapG Σ KKey.t interface.t}.
Context `{!mapG Σ KKey.t KObjectV.t}.
Context `{!mapG Σ KKey.t (gset KKey.t)}.
Context `{!auth_setG Σ KKey.t}.

Lemma wp_State__objDelete γ l key
  pure_kobj parent_key children_keys owned_grandchild_keys:
  {{{ is_pkg_init apimodel ∗
      "#Hisk" ∷ is_kubernetes γ l ∗
      "%Hkind_eq" ∷ ⌜ KKey.Kind' key = KObjectV.kind pure_kobj ⌝ ∗
      "%His_child" ∷ ⌜ key ∈ children_keys ⌝ ∗
      "Hghost_pure_kobj" ∷ key [[ γ.(γ_state) ]]↦ pure_kobj ∗
      "Hghost_children_keys" ∷ parent_key [[ γ.(γ_children) ]]↦ children_keys ∗
      "Hghost_grandchildren_keys" ∷ key [[ γ.(γ_children) ]]↦ owned_grandchild_keys
  }}}
    l @ (ptrT.id apimodel.State.id) @ "objDelete" #key
  {{{ (pure_kobj': KObjectV.t), RET #interface.nil;
      (("%Hsame_cons" ∷ ⌜ KObjectV.same_kind pure_kobj pure_kobj' ⌝ ∗
        "%Hts" ∷ ⌜ (KObjectV.objectmeta pure_kobj').(ObjectMetaV.DeletionTimestamp') ≠ None ⌝ ∗
        "Hghost_pure_kobj" ∷ key [[ γ.(γ_state) ]]↦ pure_kobj' ∗
        "Hghost_children_keys" ∷ parent_key [[ γ.(γ_children) ]]↦ children_keys ∗
        "Hghost_grandchildren_keys" ∷ key [[ γ.(γ_children) ]]↦ owned_grandchild_keys
      ) ∨
      parent_key [[ γ.(γ_children) ]]↦ (children_keys ∖ {[key]}))
  }}}.
Proof.
  wp_start as "H". iNamed "H". iNamed "Hisk". wp_apply wp_with_defer. iIntros (defer) "Hdefer". simpl subst. wp_auto.
  wp_apply wp_Mutex__Lock; [done|]. iIntros "[Hown_Mutex H]". iNamedPrefix "H" "Hinv_". wp_auto.
  iAssert (⌜ abs_state !! key = Some pure_kobj ⌝%I) as "%Hkey_in_abs".
  { iDestruct (map_valid with "Hinv_Hown_abs Hghost_pure_kobj") as %Hlookup. iPureIntro; done. }
  iAssert (⌜ children !! parent_key = Some children_keys ⌝%I) as "%Hparent_key_in_children".
  { iDestruct (map_valid with "Hinv_Hown_children Hghost_children_keys") as %Hlookup. iPureIntro; done. }
  iAssert (⌜ children !! key = Some owned_grandchild_keys ⌝%I) as "%Hkey_in_children".
  { iDestruct (map_valid with "Hinv_Hown_children Hghost_grandchildren_keys") as %Hlookup. iPureIntro; done. }
  iAssert (⌜ ∃ obj, phys_state !! key = Some obj ⌝%I) as "%Hkey_in_phys". {
    iDestruct (big_sepM2_lookup_r with "Hinv_Hphys_abs_rep") as (obj Hkey_in_phys) "_"; [done|].
    iPureIntro. exists obj. done. }
  destruct Hkey_in_phys as [obj Hkey_in_phys].
  iDestruct (big_sepM2_delete _ phys_state abs_state key _ _ Hkey_in_phys Hkey_in_abs
    with "Hinv_Hphys_abs_rep") as "[Hk_rep Hother_rep]".
  iDestruct "Hk_rep" as "(%ptr & %kobj & %Hvalid_interface & Hdeepown_l)".
  wp_apply (wp_map_get with "[$Hinv_Hown_phys]"). iIntros "Hinv_Hown_phys". wp_auto.
  rewrite /is_Some Hkey_in_phys bool_decide_true //; [exists obj; done|]. wp_auto.
  wp_apply wp_Accessor; [done|]. rewrite bool_decide_true //. wp_auto.
  iPoseProof (KObjectV.deepown_l_split _ _ _ with "Hdeepown_l")
    as "(Htypemeta_ptr & Hdeepown_l_objectmeta & Hdeepown_l_other)".
  iDestruct "Hdeepown_l_objectmeta" as (objmeta) "[Hobjectmeta_ptr Hdeepown_objectmeta]".
  wp_apply (wp_GetFinalizers with "[$Hobjectmeta_ptr]"). iIntros "Hobjectmeta_ptr". wp_auto.
  wp_if_destruct.
  - wp_apply (wp_GetDeletionTimestamp with "[$Hobjectmeta_ptr]"). iIntros "Hobjectmeta_ptr". wp_auto.
    wp_if_destruct.
    + wp_apply v1.wp_Now. iIntros (time pure_time) "Hdeepown_time". wp_auto.
      wp_apply (wp_SetDeletionTimestamp with "[$Hobjectmeta_ptr]"). iIntros "Hobjectmeta_ptr". wp_auto.
      wp_apply wp_strconv_FormatInt. iIntros (rv_str) "_". wp_auto.
      wp_apply (wp_SetResourceVersion with "[$Hobjectmeta_ptr]"). iIntros "Hobjectmeta_ptr". wp_auto.
      set new_pure_objectmeta := KObjectV.objectmeta pure_kobj
        <| ObjectMetaV.DeletionTimestamp' := Some pure_time |>
        <| ObjectMetaV.ResourceVersion' := rv_str |>.
      set new_objectmeta := objmeta
        <| v1.ObjectMeta.DeletionTimestamp' := now_ptr |>
        <| v1.ObjectMeta.ResourceVersion' := rv_str |>.
      iAssert (ObjectMetaV.deepown_l (KObjectV.objectmeta_ptr ptr pure_kobj) new_pure_objectmeta 1)
        with "[Hobjectmeta_ptr Hdeepown_objectmeta now Hdeepown_time]" as "Hdeepown_l_objectmeta".
      { iAssert (⌜ now_ptr ≠ null ⌝%I) as "%now_ptr_not_null".
        { by iDestruct (typed_pointsto_not_null with "now") as %?. }
        iNamed "Hdeepown_objectmeta". iExists new_objectmeta. iFrame. iPureIntro. split_and!; done. }
      iPoseProof (KObjectV.deepown_l_merge _ _ _ _ with "[Htypemeta_ptr Hdeepown_l_objectmeta Hdeepown_l_other]")
        as "Hdeepown_l".
      { iFrame. }
      set updated_kobj := (KObject.update_objectmeta kobj new_objectmeta).
      set updated_pure_kobj := (KObjectV.update_objectmeta pure_kobj new_pure_objectmeta).
      iMod (auth_map.map_update _ _ updated_pure_kobj with "Hinv_Hown_abs Hghost_pure_kobj")
        as "[Hinv_Hown_abs Hghost_pure_kobj]".
      iAssert (state_rep phys_state (<[key:=updated_pure_kobj]> abs_state) %I)
        with "[Hdeepown_l Hother_rep]" as "Hinv_Hphys_abs_rep".
      { assert (delete key abs_state = delete key (<[key:=updated_pure_kobj]> abs_state)) as ->.
        { rewrite delete_insert_eq. reflexivity. }
        iApply (big_sepM2_delete _ phys_state (<[key:=updated_pure_kobj]> abs_state) key _ (updated_pure_kobj)
          Hkey_in_phys with "[$Hother_rep Hdeepown_l]").
        { rewrite lookup_insert. destruct (decide (key = key)) as [|Hcontra]; [done|done]. }
        iExists ptr, updated_kobj. iFrame. iPureIntro. destruct pure_kobj; done. }
      assert (ghost_valid (dom used_uid) (<[key:=updated_pure_kobj]> abs_state) children fresh_keys)
        as Hinv_Hghost_valid'.
      {
        destruct Hinv_Hghost_valid.
        assert (parent_key ≠ key) as parent_neq_key.
        { specialize (Hno_self_parenting parent_key children_keys key Hparent_key_in_children His_child). done. }
        assert (dom (<[key:=updated_pure_kobj]> abs_state) = dom abs_state) as abs_dom_simpl.
        { rewrite dom_insert_L.
          assert ({[key]} ∪ dom abs_state = dom abs_state) as ->.
          { set_solver. }
          reflexivity. }
        assert ((KObjectV.objectmeta updated_pure_kobj).(ObjectMetaV.OwnerReferences') = (KObjectV.objectmeta pure_kobj).(ObjectMetaV.OwnerReferences'))
        as updated_pure_kobj_owner_references_eq.
        { destruct pure_kobj; done. }
        assert ((KObjectV.objectmeta updated_pure_kobj).(ObjectMetaV.UID') = (KObjectV.objectmeta pure_kobj).(ObjectMetaV.UID'))
        as updated_pure_kobj_uid_eq.
        { destruct pure_kobj; done. }
        assert (key = KObjectV.key updated_pure_kobj ∧ KObjectV.valid_old updated_pure_kobj)
          as [Hagree Hwf].
        { assert (key = KObjectV.key pure_kobj ∧ KObjectV.valid_old pure_kobj) as [Hagree Hwf].
          { apply Habs_state_valid. done. } destruct pure_kobj; done. }
        apply mk_ghost_valid.
        - intros k o Hlookup.
          rewrite lookup_insert_Some in Hlookup.
          destruct Hlookup as [(<- & <-) | (Hk_neq & Hlookup)].
          + done.
          + eapply Habs_state_valid. done.
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
        - intros k o Hlookup.
          rewrite lookup_insert_Some in Hlookup.
          destruct Hlookup as [(<- & <-) | (Hk_neq & Hlookup_obj)].
          + rewrite updated_pure_kobj_uid_eq. eapply Hexisting_uid_is_used. done.
          + eapply Hexisting_uid_is_used. done.
        - intros key_p obj_p key_c obj_c s Hlookup_p Hlookup_c Hlookup_children.
          rewrite lookup_insert_Some in Hlookup_p.
          rewrite lookup_insert_Some in Hlookup_c.
          split; [intros Hkey_in_s|intros Hobj_has_controller_parent_of];
          destruct Hlookup_p as [(<- & <-) | (Hkey_p_neq & Hlookup_p)];
          destruct Hlookup_c as [(<- & <-) | (Hkey_c_neq & Hlookup_c)].
          + exfalso. by apply (Hno_self_parenting key s key Hlookup_children Hkey_in_s).
          + rewrite updated_pure_kobj_uid_eq. eapply Hchildren_point_to_parent; [done|done|done|done].
          + unfold obj_has_controller_parent_of. rewrite updated_pure_kobj_owner_references_eq.
            eapply Hchildren_point_to_parent; [done|done|done|done].
          + eapply Hchildren_point_to_parent; [done|done|done|done].
          + assert (obj_has_controller_parent_of pure_kobj (KKey.Kind' key) (KKey.Name' key)
              (ObjectMetaV.UID' (KObjectV.objectmeta pure_kobj))) as H.
            { rewrite updated_pure_kobj_uid_eq in Hobj_has_controller_parent_of. destruct pure_kobj; done. }
            pose proof ((proj2 (Hchildren_point_to_parent _ _ _ _ _ Hkey_in_abs Hkey_in_abs Hlookup_children) H)). done.
          + rewrite updated_pure_kobj_uid_eq in Hobj_has_controller_parent_of.
            pose proof ((proj2 (Hchildren_point_to_parent _ _ _ _ _ Hkey_in_abs Hlookup_c Hlookup_children) Hobj_has_controller_parent_of)). done.
          + unfold obj_has_controller_parent_of in Hobj_has_controller_parent_of.
            rewrite updated_pure_kobj_owner_references_eq in Hobj_has_controller_parent_of.
            pose proof ((proj2 (Hchildren_point_to_parent _ _ _ _ _ Hlookup_p Hkey_in_abs Hlookup_children) Hobj_has_controller_parent_of)). done.
          + pose proof ((proj2 (Hchildren_point_to_parent _ _ _ _ _ Hlookup_p Hlookup_c Hlookup_children) Hobj_has_controller_parent_of)). done.
        - intros k o kind name uid Hlookup Href.
          rewrite lookup_insert_Some in Hlookup.
          destruct Hlookup as [(<- & <-) | (Hkey_neq & Hlookup)].
          + unfold obj_has_controller_parent_of in Href.
            rewrite updated_pure_kobj_owner_references_eq in Href.
            eapply Hparent_uid_is_used; [done|done].
          + eapply Hparent_uid_is_used; [done|done].
      }
      iCombineNamed "Hinv_*" as "H".
      wp_apply (wp_Mutex__Unlock _ (kubernetes_inv γ l) with "[$Hown_Mutex H]").
      { iNamed "H". iFrame. iFrame "#". done. }
      iApply "HΦ". iLeft. iFrame. iPureIntro. destruct pure_kobj; done.
    + iAssert (⌜ (KObjectV.objectmeta pure_kobj).(ObjectMetaV.DeletionTimestamp') ≠ None ⌝%I) as "%Hdt".
      { iNamed "Hdeepown_objectmeta". iPureIntro. intros H. apply (proj2 Hdeepown_deletiontimestamp_none) in H. done. }
      iAssert (ObjectMetaV.deepown_l (KObjectV.objectmeta_ptr ptr pure_kobj) (KObjectV.objectmeta pure_kobj) 1)
        with "[Hobjectmeta_ptr Hdeepown_objectmeta]" as "Hdeepown_l_objectmeta".
      { iExists objmeta. iFrame. }
      iPoseProof (KObjectV.deepown_l_restore _ _ _
        with "[Htypemeta_ptr Hdeepown_l_objectmeta Hdeepown_l_other]") as "Hdeepown_l".
      { iFrame. }
      iAssert (KObjectV.deepown_l ptr pure_kobj 1) with "[Hdeepown_l]" as "Hdeepown_l".
      { destruct pure_kobj; iFrame. }
      iAssert (state_rep phys_state abs_state %I) with "[Hdeepown_l Hother_rep]" as "Hinv_Hphys_abs_rep".
      { iApply big_sepM2_delete; [done | done|]. iFrame. iPureIntro. destruct pure_kobj; done. }
      iCombineNamed "Hinv_*" as "H".
      wp_apply (wp_Mutex__Unlock _ (kubernetes_inv γ l) with "[$Hown_Mutex H]").
      { iNamed "H". iFrame. iFrame "#". done. }
      iApply "HΦ". iLeft. iFrame. destruct pure_kobj; done.
  - wp_apply (wp_map_delete with "[$Hinv_Hown_phys]"). iIntros "Hinv_Hown_phys". wp_auto.
    iMod (auth_map.map_delete with "Hghost_pure_kobj Hinv_Hown_abs") as "Hinv_Hown_abs".
    iMod (auth_map.map_update _ _ (children_keys ∖ {[key]}) with "Hinv_Hown_children Hghost_children_keys")
      as "[Hinv_Hown_children Hghost_children_keys]".
    iMod (auth_map.map_delete with "Hghost_grandchildren_keys Hinv_Hown_children") as "Hinv_Hown_children".
    iAssert (state_rep (delete key phys_state) (delete key abs_state) %I) with "[Hother_rep]" as "Hinv_Hphys_abs_rep"; [done|].
    assert (ghost_valid (dom used_uid) (delete key abs_state) (delete key (<[parent_key:=children_keys ∖ {[key]}]> children)) fresh_keys) as Hinv_Hghost_valid'.
    {
      destruct Hinv_Hghost_valid.
      assert (parent_key ≠ key) as parent_neq_key.
      { specialize (Hno_self_parenting parent_key children_keys key Hparent_key_in_children His_child). done. }
      assert (dom (delete key (<[parent_key:=children_keys ∖ {[key]}]> children)) = dom (delete key children) )
      as Hdom_children_eq. {
        assert (key ≠ parent_key) as key_neq_parent by (symmetry; exact parent_neq_key).
        rewrite !dom_delete_L dom_insert_L.
        assert (parent_key ∈ dom children) as parent_in_children_dom.
        { apply elem_of_dom. exists children_keys. exact Hparent_key_in_children. }
        assert ({[parent_key]} ∪ dom children = dom children) as ->.
        { set_solver. }
        reflexivity. }
      apply mk_ghost_valid.
      - intros k o Hlookup. rewrite lookup_delete_Some in Hlookup.
        eapply Habs_state_valid. intuition.
      - set_solver.
      - intros k s Hlookup.
        rewrite lookup_delete_Some lookup_insert_Some in Hlookup.
        destruct Hlookup as (Hk_neq_key & [(<- & <-) | (Hk_neq_parent & Hlookup)]).
        + rewrite dom_delete_L.
          assert (children_keys ⊆ dom abs_state) as owned_children_in_abs.
          { apply Hchildren_exist with (k := parent_key). exact Hparent_key_in_children. }
          set_solver.
        + rewrite dom_delete_L.
          assert (s ⊆ dom abs_state) as s_in_abs by (apply Hchildren_exist with (k := k); exact Hlookup).
          assert (s ## children_keys) as s_disj_owned.
          { destruct (decide (k = parent_key)); [congruence|]. eapply Hchildren_disjoint; done. }
          assert (key ∉ s) as key_not_in_s.
          { intros Hcontra. assert (key ∈ children_keys) by exact His_child. set_solver. }
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
        + assert (children_keys ## s2) as disj_orig.
          { apply Hchildren_disjoint with (k1 := parent_key) (k2 := k2); [|assumption|assumption].
            intros Heq. subst. contradiction. }
          set_solver.
        + assert (s1 ## children_keys) as disj_orig.
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
      - intros k o Hlookup.
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
      - intros k o kind name uid Hlookup.
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
  key pure_pod parent_key children_keys owned_grandchild_keys:
  {{{ is_pkg_init apimodel ∗
      "#inv" ∷ is_kubernetes γ l ∗
      "%Hkey_eq" ∷ ⌜ key = mk_pod_key namespace name ⌝ ∗
      "Hghost_pure_pod" ∷ key [[ γ.(γ_state) ]]↦ (KObjectV.Pod pure_pod) ∗
      "Hghost_children_keys" ∷ parent_key [[ γ.(γ_children) ]]↦ children_keys ∗
      "Hghost_grandchildren_keys" ∷ key [[ γ.(γ_children) ]]↦ owned_grandchild_keys ∗
      "%His_child" ∷ ⌜ key ∈ children_keys ⌝
  }}}
    l @ (ptrT.id apimodel.State.id) @ "PodDelete" #namespace #name
  {{{ pure_pod', RET #interface.nil;
      (("%Hts" ∷ ⌜ pure_pod'.(PodV.ObjectMeta').(ObjectMetaV.DeletionTimestamp') ≠ None ⌝ ∗
        "Hghost_pure_pod" ∷ key [[ γ.(γ_state) ]]↦ (KObjectV.Pod pure_pod') ∗
        "Hghost_children_keys" ∷ parent_key [[ γ.(γ_children) ]]↦ children_keys ∗
        "Hghost_grandchildren_keys" ∷ key [[ γ.(γ_children) ]]↦ owned_grandchild_keys
      ) ∨
      parent_key [[ γ.(γ_children) ]]↦ (children_keys ∖ {[key]}))
  }}}.
Proof.
  wp_start as "H". iNamed "H". subst key. wp_auto.
  wp_apply (wp_State__objDelete with "[$Hghost_pure_pod $Hghost_children_keys $Hghost_grandchildren_keys]").
  { iFrame "#". done. }
  iIntros (pure_kobj') "H". wp_auto. iDestruct "H" as "[H|H]".
  - iNamed "H".
    assert (∃ pure_pod', pure_kobj' = KObjectV.Pod pure_pod') as [pure_pod' ->].
    { destruct pure_kobj'; try done. exists p. done. }
    iApply "HΦ". iLeft. iFrame. done.
  - iApply "HΦ". iRight. iFrame. 
  Unshelve. done.
Qed.

End proof.
