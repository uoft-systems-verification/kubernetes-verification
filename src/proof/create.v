From New.proof Require Import prelude empty_ffi.
From New.proof Require Export apimodel external_wp.

Section proof.
Context `{hG: !heapGS Σ} {go_ctx: GoContext}.
Context `{!mapG Σ KKey.t interface.t}.
Context `{!mapG Σ KKey.t PureKObject.t}.
Context `{!mapG Σ KKey.t (gset KKey.t)}.
Context `{!auth_setG Σ KKey.t}.

Lemma wp_State__objCreate_without_name γ l kind namespace obj
  ptr kobj pure_kobj parent_key parent children_keys:
  {{{ is_pkg_init apimodel ∗
      "#Hisk" ∷ is_kubernetes γ l ∗
      "%Hkind_eq" ∷ ⌜ kind = PureKObject.kind pure_kobj ⌝ ∗
      "%Hnamespace_is_parent_namespace" ∷ ⌜ namespace = parent_key.(KKey.Namespace') ⌝ ∗
      "%Hnamespace_valid" ∷ ⌜ namespace ≠ ""%go ∧ valid_namespace namespace ⌝ ∗
      "%Hinterface_agree" ∷ ⌜ PureKObject.interface_agree obj ptr pure_kobj ⌝ ∗
      "Hdeepown_l" ∷ PureKObject.deepown_l ptr kobj pure_kobj 1 ∗
      "%Hpure_kobj_is_child" ∷ ⌜ obj_has_controller_parent_of pure_kobj parent_key.(KKey.Kind')
        parent_key.(KKey.Name') (PureKObject.objectmeta parent).(PureObjectMeta.UID') ⌝ ∗
      "%Hwf" ∷ ⌜ PureKObject.well_formed_for_nameless_create pure_kobj ⌝ ∗
      "Hghost_parent" ∷ parent_key [[ γ.(γ_state) ]]↦ parent ∗
      "Hghost_children_keys" ∷ parent_key [[ γ.(γ_children) ]]↦ children_keys
  }}}
    l @ (ptrT.id apimodel.State.id) @ "objCreate" #kind #namespace #obj
  {{{ obj' ptr' kobj' pure_kobj', RET (#obj', #interface.nil);
      "%Hinterface_agree'" ∷ ⌜ PureKObject.interface_agree obj' ptr' pure_kobj' ⌝ ∗
      "%Hsame_cons" ∷ ⌜ PureKObject.same_constructor pure_kobj pure_kobj' ⌝ ∗
      "Hdeepown_l'" ∷ PureKObject.deepown_l ptr' kobj' pure_kobj' 1 ∗
      "%Hwf" ∷ ⌜ PureKObject.well_formed pure_kobj' ⌝ ∗
      "%Hnamespace_eq" ∷ ⌜ (PureKObject.objectmeta pure_kobj').(PureObjectMeta.Namespace') = namespace ⌝ ∗
      "%Hnew_key_notin" ∷ ⌜ (PureKObject.key pure_kobj') ∉ children_keys ⌝ ∗
      "Hghost_pure_kobj'" ∷ (PureKObject.key pure_kobj') [[ γ.(γ_state) ]]↦ pure_kobj' ∗
      "Hghost_parent" ∷ parent_key [[ γ.(γ_state) ]]↦ parent ∗
      "Hghost_children_keys" ∷  parent_key [[ γ.(γ_children) ]]↦ (children_keys ∪ {[PureKObject.key pure_kobj']}) ∗
      "Hghost_grandchildren_keys" ∷ (PureKObject.key pure_kobj') [[ γ.(γ_children) ]]↦ ∅
      (* TODO: specify that pure_kobj' shares some content with pure_kobj *)
  }}}.
Proof.
  wp_start as "H". iNamed "H". iNamed "Hisk".
  pose proof PureKObject.well_formed_for_nameless_create_split _ Hwf as [Hwf_meta Hwf_other].
  unfold PureObjectMeta.well_formed_for_nameless_create in Hwf_meta.
  destruct Hwf_meta as (Hgenerate_name & Hgenerate_name_len & Hname & Hnamespace & Howner_ref).
  destruct Hgenerate_name as (prefix & Hprefx & Hprefix_not_empty & Hvalid_prefix & Hnot_reserved_prefix).
  wp_apply wp_with_defer. iIntros (defer) "Hdefer". simpl subst. wp_auto.
  wp_apply wp_Mutex__Lock; [done|]. iIntros "[Hown_Mutex H]". iNamedPrefix "H" "Hinv_". wp_auto.
  wp_apply (wp_deepCopy with "[$Hdeepown_l]"); [done|].
  iIntros (copied_i copied_ptr copied_kobj) "(%Hinterface_agree_copied & Hdeepown_l_copied & Hdeepown_l)". wp_auto.
  wp_apply wp_Accessor; [done|]. rewrite bool_decide_true //. wp_auto.
  iPoseProof (PureKObject.deepown_l_split _ _ _ _ with "Hdeepown_l_copied")
    as "(Htypemeta_ptr & %Htypemeta_eq & Hdeepown_l_objectmeta & Hdeepown_l_other)".
  iDestruct "Hdeepown_l_objectmeta" as "[Hobjectmeta_ptr Hdeepown_objectmeta]".
  wp_apply (wp_SetNamespace with "[$Hobjectmeta_ptr]"). iIntros "Hobjectmeta_ptr". wp_auto.
  wp_apply (wp_GetName with "[$Hobjectmeta_ptr]"). iIntros "Hobjectmeta_ptr". wp_auto.
  wp_apply (wp_GetGenerateName with "[$Hobjectmeta_ptr]"). iIntros "Hobjectmeta_ptr". wp_auto.
  iNamedPrefix "Hdeepown_objectmeta" "Hcopied_kobj_".
  assert (v1.ObjectMeta.Name' (KObject.objectmeta copied_kobj) = ""%go) as -> by congruence. wp_auto.
  assert (v1.ObjectMeta.GenerateName' (KObject.objectmeta copied_kobj) ≠ ""%go) as Hgenerate_name_not_empty.
  { rewrite Hcopied_kobj_Hdeepown_generatename. rewrite Hprefx. intro Hcontra. apply app_eq_nil in Hcontra.
    destruct Hcontra as [_ Hcontra]. discriminate Hcontra. }
  wp_if_destruct; [done|]. rewrite bool_decide_false //. wp_auto.
  assert (v1.ObjectMeta.GenerateName' (KObject.objectmeta copied_kobj) = prefix ++ "-"%go) as ->.
  { rewrite Hcopied_kobj_Hdeepown_generatename. intuition. }
  wp_apply (wp_State__generateNewName _ _ _ _ _ (prefix ++ "-"%go) with "[$Hinv_Hstate_m_addr $Hinv_Hown_phys]").
  { eauto. }
  iIntros (new_name) "(%Hnew_name_valid & %Hnew_key_not_in_phys & %Hnew_name_not_reserved & Hinv_Hstate_m_addr & Hinv_Hown_phys)". wp_auto.
  wp_apply (wp_SetName with "[$Hobjectmeta_ptr]"). iIntros "Hobjectmeta_ptr". wp_auto.
  wp_apply (wp_map_get with "[$Hinv_Hown_phys]"). iIntros "Hinv_Hown_phys". wp_auto.
  rewrite /is_Some Hnew_key_not_in_phys. wp_auto.
  wp_apply (wp_State__generateNewUIDAndUpdate with "[$Hinv_Hstate_used_uid_addr $Hinv_Hown_used_uid]").
  iIntros (generated_uid) "(%Hgenerated_uid_is_not_used & Hinv_Hstate_used_uid_addr & Hinv_Hown_used_uid)". wp_auto.
  wp_apply (wp_SetUID with "[$Hobjectmeta_ptr]"). iIntros "Hobjectmeta_ptr". wp_auto.
  wp_apply wp_strconv_FormatInt. iIntros (rv_str) "_". wp_auto.
  wp_apply (wp_SetResourceVersion with "[$Hobjectmeta_ptr]"). iIntros "Hobjectmeta_ptr". wp_auto.
  wp_apply (wp_map_insert with "[$Hinv_Hown_phys]"). iIntros "Hinv_Hown_phys". wp_auto.
  set new_objectmeta := KObject.objectmeta copied_kobj
    <| v1.ObjectMeta.Namespace' := KKey.Namespace' parent_key |>
    <| v1.ObjectMeta.Name' := new_name |>
    <| v1.ObjectMeta.UID' := generated_uid |>
    <| v1.ObjectMeta.ResourceVersion' := rv_str |>.
  set new_pure_objectmeta := PureKObject.objectmeta pure_kobj
    <| PureObjectMeta.Namespace' := KKey.Namespace' parent_key |>
    <| PureObjectMeta.Name' := new_name |>
    <| PureObjectMeta.UID' := generated_uid |>
    <| PureObjectMeta.ResourceVersion' := rv_str |>.
  iCombineNamed "Hcopied_kobj_*" as "H".
  iAssert (PureObjectMeta.deepown_l (PureKObject.objectmeta_ptr copied_ptr pure_kobj) new_objectmeta new_pure_objectmeta 1)
    with "[Hobjectmeta_ptr H]" as "Hdeepown_l_objectmeta".
  { iNamed "H". iFrame. iPureIntro. done. }
  iPoseProof (PureKObject.deepown_l_merge _ _ _ _ _ _ with "[Htypemeta_ptr Hdeepown_l_objectmeta Hdeepown_l_other]")
    as "Hdeepown_l_copied".
  { iFrame. done. }
  wp_apply (wp_deepCopy with "[Hdeepown_l_copied]").
  { iFrame. iPureIntro. destruct pure_kobj; exact Hinterface_agree_copied. }
  iIntros (interface_obj' ptr' obj') "(%Hinterface_agree' & Hdeepown_l' & Hdeepown_l_copied)". wp_auto.
  set new_key := {|
    KKey.Kind' := PureKObject.kind pure_kobj;
    KKey.Name' := new_name;
    KKey.Namespace' := KKey.Namespace' parent_key
  |}.
  fold new_key in Hnew_key_not_in_phys.
  assert (new_key = PureKObject.key (PureKObject.update_objectmeta pure_kobj new_pure_objectmeta)) as Hnew_key_eq.
  { unfold new_key. destruct pure_kobj; done. }
  iAssert (⌜ abs_state !! new_key = None ⌝%I) as "%Hnew_key_not_in_abs".
  { iDestruct (big_sepM2_dom with "Hinv_Hphys_abs_rep") as %Hdom_eq. iPureIntro. apply not_elem_of_dom.
    apply not_elem_of_dom in Hnew_key_not_in_phys. set_solver. }
  assert (children !! new_key = None) as Hnew_key_not_in_children.
  { destruct Hinv_Hghost_well_formed. apply not_elem_of_dom. apply not_elem_of_dom in Hnew_key_not_in_abs. set_solver. }
  iAssert (⌜ abs_state !! parent_key = Some (parent) ⌝%I) as "%Hparent_key_in_abs".
  { iDestruct (map_valid with "Hinv_Hown_abs Hghost_parent") as %Hlookup. iPureIntro; exact Hlookup. }
  iAssert (⌜ children !! parent_key = Some (children_keys) ⌝%I) as "%Hparent_key_in_children".
  { iDestruct (map_valid with "Hinv_Hown_children Hghost_children_keys") as %Hlookup. iPureIntro; exact Hlookup. }
  assert (new_key ≠ parent_key) as Hnew_key_neq_parent_key.
  { intros Heq. congruence. }
  assert (<[parent_key:=children_keys ∪ {[new_key]}]> children !! new_key = None) as Hnew_key_not_in_children_after_update.
  { destruct Hinv_Hghost_well_formed. apply not_elem_of_dom. apply not_elem_of_dom in Hnew_key_not_in_abs. set_solver. }
  assert (new_key ∉ children_keys) as Hnew_key_not_in_children_keys.
  { destruct Hinv_Hghost_well_formed.
    assert (children_keys ⊆ dom abs_state) as Howned_in_abs.
    { apply Hchildren_exist with (k := parent_key). exact Hparent_key_in_children. }
    apply not_elem_of_dom in Hnew_key_not_in_abs.
    set_solver. }
  iMod (map_alloc new_key (PureKObject.update_objectmeta pure_kobj new_pure_objectmeta) with "[$Hinv_Hown_abs]")
    as "[Hinv_Hown_abs Hown_pod]"; [eauto|].
  iMod (auth_map.map_update _ _ (children_keys ∪ {[new_key]}) with "Hinv_Hown_children Hghost_children_keys")
    as "[Hinv_Hown_children Hghost_children_keys]".
  iMod (map_alloc new_key ∅ with "[$Hinv_Hown_children]") as "[Hinv_Hown_children Hghost_grandchildren_keys]"; [eauto|].
  set phys_state' := <[new_key:=copied_i]> phys_state.
  set used_uid' := <[generated_uid:=()]> used_uid.
  set abs_state' := <[new_key:=PureKObject.update_objectmeta pure_kobj new_pure_objectmeta]> abs_state.
  set children' := (<[new_key:=∅]> (<[parent_key:=children_keys ∪ {[new_key]}]> children)).
  iAssert (state_rep phys_state' abs_state' %I) with "[Hdeepown_l_copied Hinv_Hphys_abs_rep]" as "Hinv_Hphys_abs_rep".
  { unfold state_rep. unfold phys_state'. unfold abs_state'.
    rewrite (big_sepM2_insert _ phys_state abs_state new_key _ _ Hnew_key_not_in_phys Hnew_key_not_in_abs).
    iSplitL "Hdeepown_l_copied".
    - iExists copied_ptr, (KObject.update_objectmeta copied_kobj new_objectmeta). iFrame. iPureIntro.
      destruct pure_kobj; exact Hinterface_agree_copied.
    - done. }
  assert (PureKObject.well_formed (PureKObject.update_objectmeta pure_kobj new_pure_objectmeta)) as Hwf'.
  { assert (PureObjectMeta.well_formed new_pure_objectmeta) as Hwf_meta'.
    { unfold PureObjectMeta.well_formed. 
      split_and!.
      1: intros; left; exists prefix; done. all: intuition. }
    pose proof PureKObject.well_formed_implies _ Hwf_other as Hwf_other'.
    apply PureKObject.well_formed_merge. split; [done|done]. }
  assert (ghost_well_formed (dom used_uid') abs_state' children' fresh_keys ) as Hinv_Hghost_well_formed'.
  {
    assert (dom children' = dom children ∪ {[new_key]}) as Hdom_children_eq. {
      unfold children'.
      rewrite !dom_insert_L.
      assert (parent_key ∈ dom children) as Hparent_in_dom.
      { apply elem_of_dom. exists children_keys. exact Hparent_key_in_children. }
      assert ({[parent_key]} ∪ dom children = dom children) as ->.
      { set_solver. }
      set_solver. }
    assert (PureObjectMeta.UID' (PureKObject.objectmeta (PureKObject.update_objectmeta pure_kobj new_pure_objectmeta)) = generated_uid)
      as Hpure_pod'_uiq_eq.
    { destruct pure_kobj; done. }
    assert (generated_uid ∉ dom used_uid) as Hgenerated_not_in_used.
    { apply not_elem_of_dom. exact Hgenerated_uid_is_not_used. }
    assert (obj_has_controller_parent_of (PureKObject.update_objectmeta pure_kobj new_pure_objectmeta) (KKey.Kind' parent_key)
      (KKey.Name' parent_key) (PureObjectMeta.UID' (PureKObject.objectmeta parent)))
      as Hpure_pod'_has_controller_parent_of_parent.
    { destruct pure_kobj; done. }
    destruct Hinv_Hghost_well_formed.
    apply mk_ghost_well_formed.
    - intros k o Hlookup. unfold abs_state' in Hlookup.
      rewrite lookup_insert_Some in Hlookup.
      destruct Hlookup as [(<- & <-) | (Hk_neq & Hlookup)].
      + split; [done|done].
      + eapply Habs_state_well_formed. done.
    - unfold abs_state'. unfold children'. rewrite Hdom_children_eq. rewrite dom_insert_L. set_solver.
    - intros k s Hlookup.
      unfold children' in Hlookup. unfold abs_state'.
      rewrite lookup_insert_Some in Hlookup.
      destruct Hlookup as [(<- & <-) | (Hk_neq & Hlookup)]; [set_solver|].
      rewrite lookup_insert_Some in Hlookup.
      destruct Hlookup as [(<- & <-) | (Hk_neq_parent & Hlookup)]; [set_solver|].
      rewrite dom_insert_L.
      assert (s ⊆ dom abs_state) as s_in_abs.
      { apply Hchildren_exist with (k := k). done. }
      set_solver.
    - intros k s child_key Hlookup Hchild_in_s.
      unfold children' in Hlookup.
      rewrite lookup_insert_Some in Hlookup.
      destruct Hlookup as [(<- & <-) | (Hk_neq & Hlookup)]; [set_solver|].
      rewrite lookup_insert_Some in Hlookup.
      destruct Hlookup as [(<- & <-) | (Hk_neq_parent & Hlookup)].
      + assert (child_key ∈ children_keys ∨ child_key = new_key) as Hchild_cases by set_solver.
        destruct Hchild_cases as [Hchild_in_owned | ->].
        * apply Hparents_children_same_namespace with (k := parent_key) (s := children_keys); done.
        * done.
      + apply Hparents_children_same_namespace with (k := k) (s := s); done.
    - intros k s child_key Hlookup Hchild_in_s.
      unfold children' in Hlookup.
      rewrite lookup_insert_Some in Hlookup.
      destruct Hlookup as [(<- & <-) | (Hk_neq & Hlookup)]; [set_solver|].
      rewrite lookup_insert_Some in Hlookup.
      destruct Hlookup as [(<- & <-) | (Hk_neq_parent & Hlookup)].
      + assert (child_key ∈ children_keys ∨ child_key = new_key) as Hchild_cases by set_solver.
        destruct Hchild_cases as [Hchild_in_owned | ->]; [|done].
        apply Hno_self_parenting with (k := parent_key) (s := children_keys); done.
      + apply Hno_self_parenting with (k := k) (s := s); done.
    - intros k1 s1 k2 s2 Hk1_neq_k2 Hlookup1 Hlookup2.
      unfold children' in Hlookup1, Hlookup2.
      rewrite lookup_insert_Some in Hlookup1.
      rewrite lookup_insert_Some in Hlookup2.
      destruct Hlookup1 as [(<- & <-) | (Hk1_neq & Hlookup1)]; [done|].
      destruct Hlookup2 as [(<- & <-) | (Hk2_neq & Hlookup2)]; [done|].
      rewrite lookup_insert_Some in Hlookup1.
      rewrite lookup_insert_Some in Hlookup2.
      destruct Hlookup1 as [(<- & <-) | (Hk1_neq_parent & Hlookup1)];
      destruct Hlookup2 as [(<- & <-) | (Hk2_neq_parent & Hlookup2)].
      + done.
      + assert (s2 ⊆ dom abs_state) as s2_in_abs.
        { apply Hchildren_exist with (k := k2). exact Hlookup2. }
        assert (children_keys ## s2) as disj.
        { apply Hchildren_disjoint with (k1 := parent_key) (k2 := k2); [|exact Hparent_key_in_children|exact Hlookup2].
          intros Heq. done. }
        assert (new_key ∉ dom abs_state) as key_not_in_abs.
        { apply not_elem_of_dom. exact Hnew_key_not_in_abs. }
        clear -disj s2_in_abs key_not_in_abs. set_solver.
      + assert (s1 ⊆ dom abs_state) as s1_in_abs.
        { apply Hchildren_exist with (k := k1). exact Hlookup1. }
        assert (s1 ## children_keys) as disj.
        { apply Hchildren_disjoint with (k1 := k1) (k2 := parent_key); [|exact Hlookup1|exact Hparent_key_in_children].
          intros Heq. done. }
        assert (new_key ∉ dom abs_state) as key_not_in_abs.
        { apply not_elem_of_dom. exact Hnew_key_not_in_abs. }
        clear -disj s1_in_abs key_not_in_abs. set_solver.
      + apply Hchildren_disjoint with (k1 := k1) (k2 := k2); done.
    - unfold abs_state'. rewrite dom_insert_L.
      assert (new_key ∉ fresh_keys) as Hkey_not_in_fresh.
      { intros Hin. apply Hfresh_keys_reserved in Hin. unfold new_key in Hin. simpl in Hin.
        pose proof (derived_name_and_generated_name_neq new_name new_name Hin Hnew_name_not_reserved).
        done. }
      clear -Hfresh_keys_absent Hkey_not_in_fresh.
      set_solver.
    - apply Hfresh_keys_reserved.
    - intros k1 k2 obj1 obj2 Hlookup1 Hlookup2 Huid_eq.
      unfold abs_state' in Hlookup1, Hlookup2.
      rewrite lookup_insert_Some in Hlookup1.
      rewrite lookup_insert_Some in Hlookup2.
      destruct Hlookup1 as [(<- & <-) | (Hk1_neq & Hlookup1)];
      destruct Hlookup2 as [(<- & <-) | (Hk2_neq & Hlookup2)].
      + done.
      + assert ((PureKObject.objectmeta obj2).(PureObjectMeta.UID') ∈ dom used_uid) as Hobj2_uid_in_used.
        { apply Hexisting_uid_is_used with (k := k2). done. }
        rewrite <-Huid_eq, Hpure_pod'_uiq_eq in Hobj2_uid_in_used. done.
      + assert ((PureKObject.objectmeta obj1).(PureObjectMeta.UID') ∈ dom used_uid) as Hobj1_uid_in_used.
        { apply Hexisting_uid_is_used with (k := k1). done. }
        rewrite Huid_eq Hpure_pod'_uiq_eq in Hobj1_uid_in_used. done.
      + apply Hno_duplicate_uid with (obj1 := obj1) (obj2 := obj2); done.
    - intros k o Hlookup_abs_state. unfold abs_state', used_uid'.
      rewrite dom_insert_L. rewrite lookup_insert_Some in Hlookup_abs_state.
      destruct Hlookup_abs_state as [(<- & <-) | (Hk_neq & Hlookup_abs_state)]; [set_solver|set_solver].
    - intros key_p obj_p key_c obj_c s Hlookup_p Hlookup_c Hlookup_children.
      unfold abs_state' in Hlookup_p, Hlookup_c.
      unfold children' in Hlookup_children.
      rewrite lookup_insert_Some in Hlookup_p.
      rewrite lookup_insert_Some in Hlookup_c.
      rewrite lookup_insert_Some in Hlookup_children.
      split.
      + intros Hkey_c_in_s.
        destruct Hlookup_children as [(<- & <-) | (Hkey_p_neq & Hlookup_children)]; [done|].
        destruct Hlookup_p as [(<- & <-) | (Hkey_p_neq' & Hlookup_p)]; [done|].
        destruct Hlookup_c as [(<- & <-) | (Hkey_c_neq & Hlookup_c)].
        * rewrite lookup_insert_Some in Hlookup_children.
          destruct Hlookup_children as [(<- & <-) | (Hkey_p_neq'' & Hlookup_children)].
          -- rewrite Hparent_key_in_abs in Hlookup_p. injection Hlookup_p as <-. done.
          -- eapply Hchildren_exist in Hlookup_children. apply not_elem_of_dom in Hnew_key_not_in_abs. set_solver.
        * rewrite lookup_insert_Some in Hlookup_children.
          destruct Hlookup_children as [(<- & <-) | (Hkey_p_neq'' & Hlookup_children)].
          -- eapply Hchildren_point_to_parent; [done|done|done|]. set_solver.
          -- eapply Hchildren_point_to_parent; [done|done|done|done].
      + intros Hobj_has_controller_parent_of.
        destruct Hlookup_c as [(<- & <-) | (Hkey_c_neq & Hlookup_c)].
        * pose proof (well_formed_obj_has_at_most_one_controller_parent
            (PureKObject.update_objectmeta pure_kobj new_pure_objectmeta) Hwf' _ _ _ _ _ _
            Hobj_has_controller_parent_of Hpure_pod'_has_controller_parent_of_parent)
            as (Hkind_eq & Hname_eq & Huid_eq).
          destruct Hlookup_p as [(<- & <-) | (Hkey_p_neq & Hlookup_p)].
          -- exfalso.
            pose proof (Hexisting_uid_is_used parent_key parent Hparent_key_in_abs).
            rewrite Hpure_pod'_uiq_eq in Huid_eq.
            rewrite <-Huid_eq in H. done.
          -- pose proof (Hno_duplicate_uid _ _ _ _ Hlookup_p Hparent_key_in_abs Huid_eq) as ->.
            destruct Hlookup_children as [(Hkey_p_eq_new & <-) | (Hkey_p_neq' & Hlookup_children)]; [done|].
            rewrite lookup_insert_Some in Hlookup_children.
            destruct Hlookup_children as [(Hkey_p_eq_new & <-) | (Hkey_p_neq'' & Hlookup_children)]; [set_solver|done].
        * destruct Hlookup_p as [(<- & <-) | (Hkey_p_neq & Hlookup_p)].
          -- rewrite Hpure_pod'_uiq_eq in Hobj_has_controller_parent_of.
            pose proof (Hparent_uid_is_used _ _ _ _ _ Hlookup_c Hobj_has_controller_parent_of).
            done.
          -- destruct Hlookup_children as [(Hkey_p_eq_new & <-) | (Hkey_p_neq' & Hlookup_children)]; [done|].
            rewrite lookup_insert_Some in Hlookup_children.
            destruct Hlookup_children as [(<- & <-) | (Hkey_p_neq'' & Hlookup_children)].
            ++ rewrite Hparent_key_in_abs in Hlookup_p. injection Hlookup_p as <-.
              pose proof ((proj2 (Hchildren_point_to_parent _ _ _ _ _ Hparent_key_in_abs Hlookup_c Hparent_key_in_children))).
              set_solver.
            ++ pose proof ((proj2 (Hchildren_point_to_parent _ _ _ _ _ Hlookup_p Hlookup_c Hlookup_children))
                Hobj_has_controller_parent_of).
              done.
    - intros k o kind name uid Hlookup_abs Hhas_parent.
      unfold abs_state' in Hlookup_abs.
      rewrite lookup_insert_Some in Hlookup_abs.
      destruct Hlookup_abs as [(<- & <-) | (Hk_neq & Hlookup_abs)].
      + pose proof (well_formed_obj_has_at_most_one_controller_parent
          (PureKObject.update_objectmeta pure_kobj new_pure_objectmeta) Hwf' _ _ _ _ _ _ Hhas_parent
          Hpure_pod'_has_controller_parent_of_parent) as (Hkind_eq & Hname_eq & ->).
        pose proof (Hexisting_uid_is_used parent_key parent Hparent_key_in_abs).
        unfold used_uid'. set_solver.
      + pose proof (Hparent_uid_is_used k o kind name uid Hlookup_abs Hhas_parent).
        unfold used_uid'. set_solver.
  }
  iCombineNamed "Hinv_*" as "H".
  wp_apply (wp_Mutex__Unlock _ (kubernetes_inv γ l) with "[$Hown_Mutex H]").
  { iNamed "H". iFrame. iFrame "#". done. }
  iApply "HΦ". iFrame "Hdeepown_l'". iFrame. rewrite <-Hnew_key_eq. iFrame. iPureIntro. split_and!.
  all: try done; destruct pure_kobj; done.
Qed.

Lemma wp_State__PodCreate_without_name γ l namespace ptr
  pod pure_pod parent_key parent children_keys:
  {{{ is_pkg_init apimodel ∗
      "#Hisk" ∷ is_kubernetes γ l ∗
      "%Hnamespace_is_parent_namespace" ∷ ⌜ namespace = parent_key.(KKey.Namespace') ⌝ ∗
      "%Hnamespace_valid" ∷ ⌜ namespace ≠ ""%go ∧ valid_namespace namespace ⌝ ∗
      "Hdeepown_l" ∷ PurePod.deepown_l ptr pod pure_pod 1 ∗
      "%Hpure_pod_is_child" ∷ ⌜ obj_has_controller_parent_of (PureKObject.Pod pure_pod) parent_key.(KKey.Kind')
        parent_key.(KKey.Name') (PureKObject.objectmeta parent).(PureObjectMeta.UID') ⌝ ∗
      "#Hwf" ∷ ⌜ PurePod.well_formed_for_nameless_create pure_pod ⌝ ∗
      "Hghost_parent" ∷ parent_key [[ γ.(γ_state) ]]↦ parent ∗
      "Hghost_children_keys" ∷ parent_key [[ γ.(γ_children) ]]↦ children_keys
  }}}
    l @ (ptrT.id apimodel.State.id) @ "PodCreate" #namespace #ptr
  {{{ ptr' pod' pure_pod', RET (#ptr', #interface.nil);
      "Hdeepown_l'" ∷ PurePod.deepown_l ptr' pod' pure_pod' 1 ∗
      "%Hwf" ∷ ⌜ PurePod.well_formed pure_pod' ⌝ ∗
      "%Hnamespace_matches" ∷ ⌜ pure_pod'.(PurePod.ObjectMeta').(PureObjectMeta.Namespace') = namespace ⌝ ∗
      "%Hnew_key_notin" ∷ ⌜ (PurePod.key pure_pod') ∉ children_keys ⌝ ∗
      "Hghost_pure_pod" ∷ (PurePod.key pure_pod') [[ γ.(γ_state) ]]↦ (PureKObject.Pod pure_pod') ∗
      "Hghost_parent" ∷ parent_key [[ γ.(γ_state) ]]↦ parent ∗
      "Hghost_children_keys" ∷  parent_key [[ γ.(γ_children) ]]↦ (children_keys ∪ {[PurePod.key pure_pod']}) ∗
      "Hghost_grandchildren_keys" ∷ (PurePod.key pure_pod') [[ γ.(γ_children) ]]↦ ∅
      (* TODO: specify that pod' shares some contents with pod *)
  }}}.
Proof.
  wp_start as "H". iNamed "H". iNamed "Hisk". wp_auto.
  wp_apply (wp_State__objCreate_without_name _ _ _ _ _ _ (KObject.Pod pod) (PureKObject.Pod pure_pod)
  with "[$Hdeepown_l $Hghost_children_keys $Hghost_parent]").
  { iFrame "#". done. }
  iIntros (obj' ptr' kobj' pure_kobj') "H". iNamed "H". wp_auto.
  assert (∃ pure_pod', pure_kobj' = PureKObject.Pod pure_pod') as [pure_pod' ->].
  { destruct pure_kobj'; try done. exists p. done. }
  iPoseProof (PureKObject.pod_deepown_l with "Hdeepown_l'") as "(%pod' & -> & Hdeepown_l')".
  rewrite bool_decide_true //. wp_auto.
  unfold PureKObject.interface_agree in Hinterface_agree'. rewrite Hinterface_agree'.
  unshelve wp_apply wp_interface_checked_type_assert; try tc_solve.
  { iPureIntro. intros ptr_id. exists ptr'. done. }
  iIntros (y ok) "%if_ok".
  assert (ok = true) as ->.
  { destruct ok; [done|]. intuition. }
  wp_auto.
  assert (ptr' = y) as ->.
  { inversion if_ok. apply (inj to_val). done. }
  iApply "HΦ". iFrame. done.
Qed.

End proof.
