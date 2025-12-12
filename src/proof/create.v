From Perennial.algebra Require Export auth_map.
From New.proof.github_com.goose_lang.goose.model.channel Require Export auth_set.
Require Export New.proof.sync.

From proof.kubernetes_model Require Export apimodel_init.
From proof.k8s_io.apimachinery.pkg.api Require Export meta.
From proof.k8s_io.apimachinery.pkg.apis.meta Require Export v1.
From proof Require Import prelude empty_ffi.
From proof Require Export well_formed apimodel.
From proof.big_op Require Import big_sepL big_sepM.
Export apimodel.apimodel.

Section proof.
Context `{hG: !heapGS Σ} {go_ctx: GoContext}.
Context `{!mapG Σ KKey.t interface.t}.
Context `{!mapG Σ KKey.t KObject.t}.
Context `{!mapG Σ KKey.t (gset KKey.t)}.
Context `{!auth_setG Σ KKey.t}.

Lemma wp_objCreate_pod_without_name_ptsto_mut kind namespace obj
  to_create_pod_ptr to_create_pod to_create_pure_pod γ_state γ_children γ_fresh_keys parent_key owned_parent owned_child_keys:
  {{{ is_pkg_init apimodel ∗
      "#Hinv" ∷ is_kubernetes_state γ_state γ_children γ_fresh_keys ∗
      "%Hkind_is_pod" ∷ ⌜ kind = "Pod"%go ⌝ ∗
      "%Hnamespace_is_parent_namespace" ∷ ⌜ namespace = parent_key.(KKey.Namespace') ⌝ ∗
      "%Hnamespace_valid" ∷ ⌜ namespace ≠ ""%go ∧ valid_namespace namespace ⌝ ∗
      "%Hinterface_is_rs_ptr" ∷ ⌜ obj = interface.mk (ptrT.id v1.Pod.id) #to_create_pod_ptr ⌝ ∗
      "Hto_create_pod_ptr" ∷ to_create_pod_ptr ↦ to_create_pod ∗
      "Hdeep_own_to_create_pod" ∷ Pod.own to_create_pod to_create_pure_pod ∗
      "%Hto_create_pure_pod_namespace_valid" ∷ ⌜ to_create_pure_pod.(PurePod.ObjectMeta').(PureObjectMeta.Namespace') = namespace ∨
        to_create_pure_pod.(PurePod.ObjectMeta').(PureObjectMeta.Namespace') = ""%go ⌝ ∗
      "%Hto_create_pure_pod_name_valid" ∷ ⌜ to_create_pure_pod.(PurePod.ObjectMeta').(PureObjectMeta.Name') = ""%go ⌝ ∗
      "%Hto_create_pure_pod_generate_name_valid" ∷ ⌜ to_create_pure_pod.(PurePod.ObjectMeta').(PureObjectMeta.GenerateName') ≠ ""%go ∧
        valid_name to_create_pure_pod.(PurePod.ObjectMeta').(PureObjectMeta.GenerateName') ⌝ ∗
      "%Hto_create_pure_pod_is_child" ∷ ⌜ obj_has_controller_parent_of (KObject.Pod to_create_pure_pod) parent_key.(KKey.Kind') parent_key.(KKey.Name') (extract_kobject_metadata owned_parent).(PureObjectMeta.UID') ⌝ ∗
      "%Hwell_formed_to_create_Pod" ∷ ⌜ well_formed_to_create_Pod to_create_pure_pod ⌝ ∗
      "Hown_parent" ∷ parent_key [[ γ_state ]]↦ owned_parent ∗
      "Hown_child_keys" ∷ parent_key [[ γ_children ]]↦ owned_child_keys
  }}}
    @! apimodel.objCreate #kind #namespace #obj
  {{{ created_pod_ptr created_pod created_pure_pod new_key, RET (#(interface.mk (ptrT.id v1.Pod.id) #created_pod_ptr), #interface.nil);
      created_pod_ptr ↦ created_pod ∗
      Pod.own created_pod created_pure_pod ∗
      ⌜ well_formed_Pod created_pure_pod ⌝ ∗
      ⌜ new_key = mk_pod_key namespace created_pure_pod.(PurePod.ObjectMeta').(PureObjectMeta.Name') ⌝ ∗
      ⌜ new_key ∉ owned_child_keys ⌝ ∗
      new_key [[ γ_state ]]↦ (KObject.Pod created_pure_pod) ∗
      parent_key [[ γ_state ]]↦ owned_parent ∗
      parent_key [[ γ_children ]]↦ (owned_child_keys ∪ {[new_key]}) ∗
      new_key [[ γ_children ]]↦ ∅
      (* TODO: specify that created_pod shares the same content with to_create_pod *)
  }}}.
Proof.
  wp_start as "H". iNamed "H".
  wp_apply wp_with_defer. iIntros (defer) "Hdefer". simpl subst. wp_auto.
  wp_apply wp_globals_get. wp_apply wp_Mutex__Lock; [done|]. iIntros "[Hown_Mutex H]". iNamedPrefix "H" "Hinv_". wp_auto.
  wp_apply wp_globals_get. wp_apply (wp_deepCopy_pod with "[$Hto_create_pod_ptr $Hdeep_own_to_create_pod]"); [done|].
  iIntros (copied_ptr copied_pod) "(Hcopied_ptr & Hdeep_own_copied_pod & Hto_create_pod_ptr & Hdeep_own_to_create_pod)". wp_auto.
  wp_apply wp_Accessor; [done|]. iIntros (o err) "(-> & ->)". wp_auto.
  rewrite bool_decide_true //. wp_auto.
  iDestruct (struct_fields_split with "Hcopied_ptr") as "H". iNamed "H".
  wp_apply (wp_SetNamespace with "[$HObjectMeta]"). iIntros (meta') "(-> & HObjectMeta)". wp_auto.
  wp_apply (wp_GetName with "[$HObjectMeta]"). iIntros (name) "(-> & HObjectMeta)". wp_auto.
  wp_apply (wp_GetGenerateName with "[$HObjectMeta]"). iIntros (generate_name) "(-> & HObjectMeta)". wp_auto.
  iAssert (⌜ v1.ObjectMeta.Name' (v1.Pod.ObjectMeta' copied_pod) = ""%go ⌝%I) as "->".
  { iNamed "Hdeep_own_copied_pod". iNamed "Hown_objectmeta". iPureIntro. congruence. }
  iAssert (⌜ v1.ObjectMeta.GenerateName' (v1.Pod.ObjectMeta' copied_pod) ≠ ""%go ⌝%I) as "%Hgenerate_name_not_empty".
  { iNamed "Hdeep_own_copied_pod". iNamed "Hown_objectmeta". iPureIntro.
    destruct Hto_create_pure_pod_generate_name_valid as [H _]. congruence. }
  wp_auto. wp_if_destruct; [done|]. rewrite bool_decide_false //. wp_auto.
  wp_apply wp_globals_get. wp_apply (wp_generateNewName with "[$Hinv_Hown_phys]").
  iIntros (new_name) "(%Hnew_name_valid & %Hnew_key_not_in_phys & %Hnew_key_not_reserved & Hinv_Hown_phys)". wp_auto.
  wp_apply (wp_SetName with "[$HObjectMeta]"). iIntros (meta') "(-> & HObjectMeta)". wp_auto.
  wp_apply wp_globals_get. wp_apply (wp_map_get with "[$Hinv_Hown_phys]"). iIntros "Hinv_Hown_phys". wp_auto.
  rewrite /is_Some Hnew_key_not_in_phys. wp_auto.
  wp_apply wp_globals_get. wp_apply (wp_generateNewUID with "[$Hinv_Hown_used_uid]").
  iIntros (generated_uid) "(%Hgenerated_uid_is_not_used & Hinv_Hown_used_uid)". wp_auto.
  wp_apply (wp_SetUID with "[$HObjectMeta]"). iIntros (meta') "(-> & HObjectMeta)". wp_auto.
  wp_apply wp_globals_get. wp_apply wp_globals_get. wp_apply wp_globals_get.
  wp_apply wp_strconv_FormatInt. iIntros (rv_str) "_". wp_auto.
  wp_apply (wp_SetResourceVersion with "[$HObjectMeta]"). iIntros (meta') "(-> & HObjectMeta)". wp_auto.
  wp_apply wp_globals_get. wp_apply (wp_map_insert with "[$Hinv_Hown_phys]"). iIntros "Hinv_Hown_phys". wp_auto.
  iDestruct (struct_fields_combine (v:=v1.Pod.mk _ _ _ _)
    with "[$HTypeMeta $HObjectMeta $HSpec $HStatus]") as "Hcopied_ptr". simpl.
  iDestruct (rename_pod with "Hcopied_ptr") as (created_pod) "(Hcopied_ptr & %Hcreated_pod_eq)".
  set created_pure_meta := to_create_pure_pod.(PurePod.ObjectMeta')
    <| PureObjectMeta.Namespace' := KKey.Namespace' parent_key |>
    <| PureObjectMeta.Name' := new_name |>
    <| PureObjectMeta.UID' := generated_uid |>
    <| PureObjectMeta.ResourceVersion' := rv_str |>.
  set created_pure_pod := to_create_pure_pod <| PurePod.ObjectMeta' := created_pure_meta |>.
  iAssert (Pod.own created_pod created_pure_pod) with "[Hdeep_own_copied_pod]" as "Hdeep_own_created_pod".
  { iNamed "Hdeep_own_copied_pod". iFrame. iSplitR; [iPureIntro; rewrite Hcreated_pod_eq //|].
    iNamed "Hown_objectmeta". rewrite Hcreated_pod_eq //. iFrame. iPureIntro. done. }
  wp_apply (wp_deepCopy_pod with "[$Hcopied_ptr $Hdeep_own_created_pod]"); [done|].
  iIntros (returned_ptr returned_pod) "(Hreturned_ptr & Hdeepown_returned_pod & Hcopied_ptr & Hdeepown_created_pod)". wp_auto.
  set new_key := {| KKey.Kind' := "Pod"; KKey.Name' := new_name; KKey.Namespace' := KKey.Namespace' parent_key |}.
  fold new_key in Hnew_key_not_in_phys. fold new_key in Hnew_key_not_reserved.
  iAssert (⌜ abs_state !! new_key = None ⌝%I) with "[Hinv_Hphys_abs_rep]" as "%Hnew_key_not_in_abs".
  { iDestruct (big_sepM2_dom with "Hinv_Hphys_abs_rep") as %Hdom_eq. iPureIntro. apply not_elem_of_dom. apply not_elem_of_dom in Hnew_key_not_in_phys. set_solver. }
  assert (children !! new_key = None) as Hnew_key_not_in_children.
  { destruct Hinv_Hghost_well_formed. apply not_elem_of_dom. apply not_elem_of_dom in Hnew_key_not_in_abs. set_solver. }
  iAssert (⌜ abs_state !! parent_key = Some (owned_parent) ⌝%I) with "[Hown_parent Hinv_Hown_abs]" as "%Hparent_key_in_abs".
  { iDestruct (map_valid with "Hinv_Hown_abs Hown_parent") as %Hlookup. iPureIntro; exact Hlookup. }
  iAssert (⌜ children !! parent_key = Some (owned_child_keys) ⌝%I) with "[Hown_child_keys Hinv_Hown_children]" as "%Hparent_key_in_children".
  { iDestruct (map_valid with "Hinv_Hown_children Hown_child_keys") as %Hlookup. iPureIntro; exact Hlookup. }
  assert (new_key ≠ parent_key) as Hnew_key_neq_parent_key.
  { intros Heq. congruence. }
  assert (<[parent_key:=owned_child_keys ∪ {[new_key]}]> children !! new_key = None) as Hnew_key_not_in_children_after_update.
  { destruct Hinv_Hghost_well_formed. apply not_elem_of_dom. apply not_elem_of_dom in Hnew_key_not_in_abs. set_solver. }
  assert (new_key ∉ owned_child_keys) as Hnew_key_not_in_owned_child_keys.
  { destruct Hinv_Hghost_well_formed.
    assert (owned_child_keys ⊆ dom abs_state) as Howned_in_abs.
    { apply Hchildren_exist with (k := parent_key). exact Hparent_key_in_children. }
    apply not_elem_of_dom in Hnew_key_not_in_abs.
    set_solver. }
  iMod (map_alloc new_key (KObject.Pod created_pure_pod) with "[$Hinv_Hown_abs]") as "[Hinv_Hown_abs Hown_pod]"; [eauto|].
  iMod (auth_map.map_update _ _ (owned_child_keys ∪ {[new_key]}) with "Hinv_Hown_children Hown_child_keys")
    as "[Hinv_Hown_children Hown_child_keys]".
  iMod (map_alloc new_key ∅ with "[$Hinv_Hown_children]") as "[Hinv_Hown_children Hown_grandchild_keys]"; [eauto|].
  set phys_state' := <[new_key:=interface.mk (ptrT.id v1.Pod.id) (# copied_ptr)]> phys_state.
  set used_uid' := <[generated_uid:=()]> used_uid.
  set abs_state' := <[new_key:=KObject.Pod created_pure_pod]> abs_state.
  set children' := (<[new_key:=∅]> (<[parent_key:=owned_child_keys ∪ {[new_key]}]> children)).
  iAssert ((⌜ created_pure_pod.(PurePod.ObjectMeta').(PureObjectMeta.Namespace') = new_key.(KKey.Namespace') ⌝ ∗
      ⌜ created_pure_pod.(PurePod.ObjectMeta').(PureObjectMeta.Name') = new_key.(KKey.Name') ⌝ ∗
      ⌜ well_formed_Pod created_pure_pod ⌝) %I)
  as "(%Hnamespace_match & %Hname_match & %Hwell_formed_Pod)".
  { iPureIntro. split; [done|split;[done|]].
    unfold well_formed_Pod. unfold well_formed_to_create_Pod in Hwell_formed_to_create_Pod.
    split; [|split; [intuition|intuition]].
    unfold well_formed_ObjectMeta. unfold well_formed_to_create_ObjectMeta in Hwell_formed_to_create_Pod. intuition. }
  iAssert (state_rep phys_state' abs_state' %I) with "[Hcopied_ptr Hdeepown_created_pod Hinv_Hphys_abs_rep]" as "Hinv_Hphys_abs_rep".
  { unfold state_rep. unfold phys_state'. unfold abs_state'.
    rewrite (big_sepM2_insert _ phys_state abs_state new_key _ _ Hnew_key_not_in_phys Hnew_key_not_in_abs).
    iSplitL "Hcopied_ptr Hdeepown_created_pod".
    - unfold obj_rep.
      assert (bool_decide (KKey.Kind' new_key = "Pod"%go) = true) as kind_is_pod.
      { apply bool_decide_true. unfold new_key. simpl. reflexivity. }
      rewrite kind_is_pod.
      iExists copied_ptr, created_pod, created_pure_pod.
      unfold pod_rep. iFrame "#". iFrame. iPureIntro. done.
    - done. }
  assert (ghost_well_formed (dom used_uid') abs_state' children' fresh_keys ) as Hinv_Hghost_well_formed'.
  {
    assert (dom children' = dom children ∪ {[new_key]}) as Hdom_children_eq.
    {
      unfold children'.
      rewrite !dom_insert_L.
      assert (parent_key ∈ dom children) as Hparent_in_dom.
      { apply elem_of_dom. exists owned_child_keys. exact Hparent_key_in_children. }
      assert ({[parent_key]} ∪ dom children = dom children) as ->.
      { set_solver. }
      set_solver.
    }
    assert (PureObjectMeta.UID' (extract_kobject_metadata (KObject.Pod created_pure_pod)) = generated_uid) as Hcreated_pure_pod_uiq_eq.
    { intuition. }
    assert (generated_uid ∉ dom used_uid) as Hgenerated_not_in_used.
    { apply not_elem_of_dom. exact Hgenerated_uid_is_not_used. }
    assert (obj_has_controller_parent_of (KObject.Pod created_pure_pod) (KKey.Kind' parent_key)
      (KKey.Name' parent_key) (PureObjectMeta.UID' (extract_kobject_metadata owned_parent)))
      as Hcreated_pure_pod_has_controller_parent_of_owned_parent by done.
    destruct Hinv_Hghost_well_formed.
    apply mk.
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
      + assert (child_key ∈ owned_child_keys ∨ child_key = new_key) as Hchild_cases by set_solver.
        destruct Hchild_cases as [Hchild_in_owned | ->].
        * apply Hparents_children_same_namespace with (k := parent_key) (s := owned_child_keys); done.
        * done.
      + apply Hparents_children_same_namespace with (k := k) (s := s); done.
    - intros k s child_key Hlookup Hchild_in_s.
      unfold children' in Hlookup.
      rewrite lookup_insert_Some in Hlookup.
      destruct Hlookup as [(<- & <-) | (Hk_neq & Hlookup)]; [set_solver|].
      rewrite lookup_insert_Some in Hlookup.
      destruct Hlookup as [(<- & <-) | (Hk_neq_parent & Hlookup)].
      + assert (child_key ∈ owned_child_keys ∨ child_key = new_key) as Hchild_cases by set_solver.
        destruct Hchild_cases as [Hchild_in_owned | ->]; [|done].
        apply Hno_self_parenting with (k := parent_key) (s := owned_child_keys); done.
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
        assert (owned_child_keys ## s2) as disj.
        { apply Hchildren_disjoint with (k1 := parent_key) (k2 := k2); [|exact Hparent_key_in_children|exact Hlookup2].
          intros Heq. done. }
        assert (new_key ∉ dom abs_state) as key_not_in_abs.
        { apply not_elem_of_dom. exact Hnew_key_not_in_abs. }
        clear -disj s2_in_abs key_not_in_abs. set_solver.
      + assert (s1 ⊆ dom abs_state) as s1_in_abs.
        { apply Hchildren_exist with (k := k1). exact Hlookup1. }
        assert (s1 ## owned_child_keys) as disj.
        { apply Hchildren_disjoint with (k1 := k1) (k2 := parent_key); [|exact Hlookup1|exact Hparent_key_in_children].
          intros Heq. done. }
        assert (new_key ∉ dom abs_state) as key_not_in_abs.
        { apply not_elem_of_dom. exact Hnew_key_not_in_abs. }
        clear -disj s1_in_abs key_not_in_abs. set_solver.
      + apply Hchildren_disjoint with (k1 := k1) (k2 := k2); done.
    - unfold abs_state'. rewrite dom_insert_L.
      assert (new_key ∉ fresh_keys) as Hkey_not_in_fresh.
      { intros Hin. apply Hfresh_keys_reserved in Hin. done. }
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
      + assert ((extract_kobject_metadata obj2).(PureObjectMeta.UID') ∈ dom used_uid) as Hobj2_uid_in_used.
        { apply Hexisting_uid_is_used with (k := k2). done. }
        rewrite <-Huid_eq, Hcreated_pure_pod_uiq_eq in Hobj2_uid_in_used. done.
      + assert ((extract_kobject_metadata obj1).(PureObjectMeta.UID') ∈ dom used_uid) as Hobj1_uid_in_used.
        { apply Hexisting_uid_is_used with (k := k1). done. }
        rewrite Huid_eq Hcreated_pure_pod_uiq_eq in Hobj1_uid_in_used. done.
      + apply Hno_duplicate_uid with (obj1 := obj1) (obj2 := obj2); done.
    - intros k obj Hlookup_abs_state. unfold abs_state', used_uid'.
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
        * assert (well_formed_kobject (KObject.Pod created_pure_pod)) as Hwell_formed_kobject by done.
          pose proof (well_formed_obj_has_at_most_one_controller_parent (KObject.Pod created_pure_pod) Hwell_formed_kobject
            _ _ _ _ _ _ Hobj_has_controller_parent_of Hcreated_pure_pod_has_controller_parent_of_owned_parent) as (Hkind_eq & Hname_eq & Huid_eq).
          destruct Hlookup_p as [(<- & <-) | (Hkey_p_neq & Hlookup_p)].
          -- exfalso.
            pose proof (Hexisting_uid_is_used parent_key owned_parent Hparent_key_in_abs).
            rewrite Hcreated_pure_pod_uiq_eq in Huid_eq.
            rewrite <-Huid_eq in H. done.
          -- pose proof (Hno_duplicate_uid _ _ _ _ Hlookup_p Hparent_key_in_abs Huid_eq) as ->.
            destruct Hlookup_children as [(Hkey_p_eq_new & <-) | (Hkey_p_neq' & Hlookup_children)]; [done|].
            rewrite lookup_insert_Some in Hlookup_children.
            destruct Hlookup_children as [(Hkey_p_eq_new & <-) | (Hkey_p_neq'' & Hlookup_children)]; [set_solver|done].
        * destruct Hlookup_p as [(<- & <-) | (Hkey_p_neq & Hlookup_p)].
          -- rewrite Hcreated_pure_pod_uiq_eq in Hobj_has_controller_parent_of.
            pose proof (Hparent_uid_is_used _ _ _ _ _ Hlookup_c Hobj_has_controller_parent_of).
            done.
          -- destruct Hlookup_children as [(Hkey_p_eq_new & <-) | (Hkey_p_neq' & Hlookup_children)]; [done|].
            rewrite lookup_insert_Some in Hlookup_children.
            destruct Hlookup_children as [(<- & <-) | (Hkey_p_neq'' & Hlookup_children)].
            ++ rewrite Hparent_key_in_abs in Hlookup_p. injection Hlookup_p as <-.
              pose proof ((proj2 (Hchildren_point_to_parent _ _ _ _ _ Hparent_key_in_abs Hlookup_c Hparent_key_in_children))).
              set_solver.
            ++ pose proof ((proj2 (Hchildren_point_to_parent _ _ _ _ _ Hlookup_p Hlookup_c Hlookup_children)) Hobj_has_controller_parent_of).
              done.
    - intros k obj kind name uid Hlookup_abs Hhas_parent.
      unfold abs_state' in Hlookup_abs.
      rewrite lookup_insert_Some in Hlookup_abs.
      destruct Hlookup_abs as [(<- & <-) | (Hk_neq & Hlookup_abs)].
      + assert (well_formed_kobject (KObject.Pod created_pure_pod)) as Hwell_formed_kobject by done.
        pose proof (well_formed_obj_has_at_most_one_controller_parent (KObject.Pod created_pure_pod) Hwell_formed_kobject
          _ _ _ _ _ _ Hhas_parent Hcreated_pure_pod_has_controller_parent_of_owned_parent) as (Hkind_eq & Hname_eq & ->).
        pose proof (Hexisting_uid_is_used parent_key owned_parent Hparent_key_in_abs).
        unfold used_uid'. set_solver.
      + pose proof (Hparent_uid_is_used k obj kind name uid Hlookup_abs Hhas_parent).
        unfold used_uid'. set_solver.
  }
  iCombineNamed "Hinv_*" as "H".
  wp_apply (wp_Mutex__Unlock _ (is_kubernetes_state_inner γ_state γ_children γ_fresh_keys)
    with "[$Hown_Mutex H]").
  { iNamed "H". iFrame. iFrame "#". done. }
  iApply "HΦ". iFrame "Hreturned_ptr". iFrame. done.
Qed.

(* Lemma wp_PodCreate_without_name_ptsto_mut namespace to_create_pod_ptr to_create_pod
  γ_state γ_children γ_fresh_keys parent_key owned_parent owned_child_keys:
  {{{ is_pkg_init apimodel ∗
      "#inv" ∷ is_kubernetes_state γ_state γ_children γ_fresh_keys ∗
      "own_parent" ∷ parent_key [[ γ_state ]]↦ owned_parent ∗
      "own_child_keys" ∷ parent_key [[ γ_children ]]↦ owned_child_keys ∗
      "%namespace_valid" ∷ ⌜ namespace = parent_key.(KKey.Namespace') ⌝ ∗
      "to_create_pod_ptr" ∷ to_create_pod_ptr ↦ to_create_pod ∗
      "parent_uid" ∷ has_controller_parent_of to_create_pod.(v1.Pod.ObjectMeta').(v1.ObjectMeta.OwnerReferences') (extract_kobject_metadata owned_parent).(v1.ObjectMeta.UID') ∗
      "#well_formed_to_create_Pod" ∷ well_formed_to_create_Pod to_create_pod ∗
      "%to_create_pod_namespace_valid" ∷ ⌜ to_create_pod.(v1.Pod.ObjectMeta').(v1.ObjectMeta.Namespace') = namespace ∨ to_create_pod.(v1.Pod.ObjectMeta').(v1.ObjectMeta.Namespace') = ""%go ⌝ ∗
      "%to_create_pod_name_valid" ∷ ⌜ to_create_pod.(v1.Pod.ObjectMeta').(v1.ObjectMeta.Name') = ""%go ⌝
  }}}
    @! apimodel.PodCreate #namespace #to_create_pod_ptr
  {{{ created_pod_ptr (err: error.t) created_pod new_key, RET (#created_pod_ptr, #err);
      ⌜ err = interface.nil ⌝ ∗
      created_pod_ptr ↦ created_pod ∗
      well_formed_Pod created_pod ∗
      ⌜ new_key = extract_pod_key created_pod ⌝ ∗
      ⌜ new_key ∉ owned_child_keys ⌝ ∗
      new_key [[ γ_state ]]↦ (KObject.Pod created_pod) ∗
      parent_key [[ γ_state ]]↦ owned_parent ∗
      parent_key [[ γ_children ]]↦ (owned_child_keys ∪ {[new_key]})
      (* TODO: specify that created_pod shares some contents with to_create_pod *)
  }}}.
Proof.
Admitted. *)

End proof.
