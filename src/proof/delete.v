From Perennial.algebra Require Export auth_map.
From New.proof.github_com.goose_lang.goose.model.channel Require Export auth_set.
Require Export New.proof.sync.

From proof.kubernetes_model Require Export apimodel_init.
From proof.k8s_io.apimachinery.pkg.api Require Export meta.
From proof.k8s_io.apimachinery.pkg.apis.meta Require Export v1.
From proof Require Import prelude empty_ffi.
From proof Require Export well_formed.
From proof.big_op Require Import big_sepL big_sepM.
Export apimodel.apimodel.

Section proof.
Context `{hG: !heapGS Σ} {go_ctx: GoContext}.
Context `{!mapG Σ KKey.t interface.t}.
Context `{!mapG Σ KKey.t PureKObject.t}.
Context `{!mapG Σ KKey.t (gset KKey.t)}.
Context `{!auth_setG Σ KKey.t}.

(* TODO: Revisit this spec and see if owned_grandchild_keys is necessary *)
Lemma wp_objDelete_pod_ptsto_mut key
  γ_state γ_children γ_fresh_keys owned_pod parent_key owned_child_keys owned_grandchild_keys:
  {{{ is_pkg_init apimodel ∗
      "#inv" ∷ is_kubernetes_state γ_state γ_children γ_fresh_keys ∗
      "own_pod" ∷ key [[ γ_state ]]↦ (PureKObject.Pod owned_pod) ∗
      "own_child_keys" ∷ parent_key [[ γ_children ]]↦ owned_child_keys ∗
      "own_grandchild_keys" ∷ key [[ γ_children ]]↦ owned_grandchild_keys ∗
      "%pod_is_child" ∷ ⌜ key ∈ owned_child_keys ⌝ ∗
      "%kind" ∷ ⌜ KKey.Kind' key = "Pod"%go ⌝
  }}}
    @! apimodel.objDelete #key
  {{{ (err: error.t) pod, RET #err;
      "err_is_nil" ∷ ⌜ err = interface.nil ⌝ ∗
      "pod_updated_or_deleted" ∷ ("pod_updated" ∷ (
        "own_pod" ∷ key [[ γ_state ]]↦ (PureKObject.Pod pod) ∗
        "own_child_keys" ∷ parent_key [[ γ_children ]]↦ owned_child_keys ∗
        "own_grandchild_keys" ∷ key [[ γ_children ]]↦ owned_grandchild_keys ∗
        "%deletiontimestamp_notnull" ∷ ⌜ pod.(v1.Pod.ObjectMeta').(v1.ObjectMeta.DeletionTimestamp') ≠ null ⌝
      ) ∨
      "own_child_keys" ∷ parent_key [[ γ_children ]]↦ (owned_child_keys ∖ {[key]}))
  }}}.
Proof.
  wp_start as "H". iNamed "H".
  wp_apply wp_with_defer.
  iIntros (defer) "defer". simpl subst. wp_auto. iRename "key" into "key_ptr".
  wp_apply wp_globals_get.
  wp_apply wp_Mutex__Lock; [done|].
  iIntros "[own_Mutex H]". iNamed "H". wp_auto.
  wp_apply wp_globals_get. wp_apply wp_globals_get.
  iAssert (⌜ abs_state !! key = Some (PureKObject.Pod owned_pod) ⌝%I) with "[own_pod own_abs]" as "%key_in_abs".
  { iDestruct (map_valid with "own_abs own_pod") as %Hlookup. iPureIntro; exact Hlookup. }
  iAssert (⌜ children !! parent_key = Some owned_child_keys ⌝%I) with "[own_children own_child_keys]" as "%parent_key_in_children".
  { iDestruct (map_valid with "own_children own_child_keys") as %Hlookup. iPureIntro; exact Hlookup. }
  iAssert (⌜ children !! key = Some owned_grandchild_keys ⌝%I) with "[own_children own_grandchild_keys]" as "%key_in_children".
  { iDestruct (map_valid with "own_children own_grandchild_keys") as %Hlookup. iPureIntro; exact Hlookup. }
  iAssert (⌜ ∃ obj, phys_state !! key = Some obj ⌝%I) with "[phys_abs_rep]" as "%key_in_phys".
  {
    iDestruct (big_sepM2_lookup_r with "phys_abs_rep") as (obj key_in_phys) "_".
    { exact key_in_abs. }
    iPureIntro. exists obj. exact key_in_phys.
  }
  destruct key_in_phys as [obj key_in_phys].
  iDestruct (big_sepM2_split_singleton _ key _ _ phys_state abs_state key_in_phys key_in_abs with "phys_abs_rep") as "[k_rep other_rep]".
  destruct decide_kind_is_pod with (KKey.Kind' key) as [kind_is_pod kind_is_not_replicaset].
  { done. }
  iAssert (∃ (ptr: loc) (pod: v1.Pod.t), pod_rep key obj (PureKObject.Pod owned_pod) ptr pod)%I 
  with "[k_rep]" as "(%ptr & %pod & pod_rep)".
  { unfold obj_rep. rewrite kind_is_pod. done. }
  iNamed "pod_rep".
  inversion abs_v_is_pod as [Heq]. symmetry in Heq. subst. clear abs_v_is_pod.
  wp_apply (wp_map_get with "[$own_phys]"). iIntros "own_phys". wp_auto.
  rewrite /is_Some key_in_phys. wp_auto.
  wp_apply wp_Accessor.
  { done. }
  iIntros (ret err) "(-> & ->)". wp_auto.
  assert ((bool_decide (interface.nil = interface.nil)) = true) as nil_is_nil.
  { rewrite bool_decide_true //. }
  rewrite nil_is_nil. wp_auto.
  iDestruct (struct_fields_split with "pod_ptr") as "H". iNamed "H".
  wp_apply (wp_GetFinalizers with "[$HObjectMeta]").
  iIntros (finalizers) "(-> & HObjectMeta)". wp_auto.
  wp_if_destruct.
  - wp_apply (wp_GetDeletionTimestamp with "[$HObjectMeta]").
    iIntros (deletion_timestamp) "(-> & HObjectMeta)". wp_auto.
    wp_if_destruct.
    + wp_apply v1.wp_Now.
      iIntros (time) "_". wp_auto.
      wp_apply (wp_SetDeletionTimestamp with "[$HObjectMeta]").
      iIntros (meta') "(-> & HObjectMeta)". wp_auto. wp_bind.
      wp_apply wp_globals_get.
      (* TODO: fix the resource version counter overflow in the Go code *)
      wp_apply wp_globals_get. wp_bind. wp_apply wp_globals_get.
      wp_apply wp_strconv_FormatInt. iIntros (rv_str) "_". wp_auto.
      wp_apply (wp_SetResourceVersion with "[$HObjectMeta]").
      iIntros (meta') "(-> & HObjectMeta)". wp_auto.
      iDestruct (struct_fields_combine (v:=v1.Pod.mk _ _ _ _)
        with "[$HTypeMeta $HObjectMeta $HSpec $HStatus]") as "pod_ptr". simpl.
      iDestruct (rename_pod with "pod_ptr") as "(%updated_pod & pod_ptr & %updated_pod_eq)".
      iMod (auth_map.map_update _ _ (PureKObject.Pod updated_pod) with "own_abs own_pod")
        as "[own_abs own_pod]".
      iAssert (state_rep phys_state (<[key:=PureKObject.Pod updated_pod]> abs_state) %I)
      with "[pod_ptr other_rep]" as "phys_abs_rep".
      {
        assert (delete key abs_state = delete key (<[key:=PureKObject.Pod updated_pod]> abs_state)) as ->.
        { rewrite delete_insert_eq. reflexivity. }
        iAssert (("%namespace_match" ∷ ⌜ updated_pod.(v1.Pod.ObjectMeta').(v1.ObjectMeta.Namespace') = (KKey.Namespace' key) ⌝ ∗
                  "%name_match" ∷ ⌜ updated_pod.(v1.Pod.ObjectMeta').(v1.ObjectMeta.Name') = (KKey.Name' key) ⌝ ∗
                  "#well_formed_Pod" ∷ well_formed_Pod updated_pod)%I)
        as "(% & % & #well_formed_Pod')".
        {
          unfold well_formed_Pod. unfold well_formed_ObjectMeta.
          subst updated_pod. simpl. iFrame "#". done.
        }
        iAssert (obj_rep key (interface.mk (ptrT.id v1.Pod.id) (# ptr)) (PureKObject.Pod updated_pod)%I)
        with "[pod_ptr]" as "k_rep".
        { unfold obj_rep. rewrite kind_is_pod. iExists ptr, updated_pod. unfold pod_rep. iFrame. iFrame "#". done. }
        assert ((<[key:=PureKObject.Pod updated_pod]> abs_state) !! key = Some (PureKObject.Pod updated_pod)) as key_in_new_abs.
        { rewrite lookup_insert. destruct (decide (key = key)) as [|Hcontra]; [reflexivity | contradiction]. }
        iApply (big_sepM2_split_singleton _ key _ (PureKObject.Pod updated_pod) phys_state (<[key:=PureKObject.Pod updated_pod]> abs_state)
          key_in_phys key_in_new_abs with "[k_rep other_rep]").
        iFrame.
      }
      iAssert (kubernetes_state_consistent (dom used_uid) (<[key:=PureKObject.Pod updated_pod]> abs_state) children fresh_keys %I)
      as "consistent'".
      {
        iNamed "consistent".
        assert (parent_key ≠ key) as parent_neq_key.
        { specialize (no_self_parenting parent_key owned_child_keys key parent_key_in_children pod_is_child). done. }
        assert (dom (<[key:=PureKObject.Pod updated_pod]> abs_state) = dom abs_state) as abs_dom_simpl.
        {
          rewrite dom_insert_L.
          assert ({[key]} ∪ dom abs_state = dom abs_state) as union_eq.
          { set_solver. }
          rewrite union_eq.
          reflexivity.
        }
        assert ((extract_kobject_metadata (PureKObject.Pod updated_pod)).(v1.ObjectMeta.OwnerReferences') = (extract_kobject_metadata (PureKObject.Pod owned_pod)).(v1.ObjectMeta.OwnerReferences'))
        as updated_pod_owner_references_eq.
        { simpl. subst updated_pod. simpl. reflexivity. }
        assert ((extract_kobject_metadata (PureKObject.Pod updated_pod)).(v1.ObjectMeta.UID') = (extract_kobject_metadata (PureKObject.Pod owned_pod)).(v1.ObjectMeta.UID'))
        as updated_pod_uid_eq.
        { simpl. subst updated_pod. simpl. reflexivity. }
        iSplitR; [|iSplitR; [|iSplitR; [|iSplitR; [|iSplitR; [|iSplitR; [|iSplitR; [|iSplitR; [|iSplitR; [|iSplitR; [|iSplitR ]]]]]]]]]].
        { iPureIntro. set_solver. }
        { iPureIntro. intros k s Hlookup. specialize (children_exist k s Hlookup). rewrite dom_insert_L. set_solver. }
        { iPureIntro. apply parents_children_same_namespace. }
        { iPureIntro. apply no_self_parenting. }
        { iPureIntro. apply children_disjoint. }
        { iPureIntro. rewrite dom_insert_L. set_solver. }
        { iPureIntro. apply fresh_keys_reserved. }
        {
          iPureIntro.
          intros k1 k2 obj1 obj2 Hlookup1 Hlookup2 Huid_eq.
          rewrite lookup_insert_Some in Hlookup1.
          rewrite lookup_insert_Some in Hlookup2.
          destruct Hlookup1 as [(Hk1_eq & Hobj1_eq) | (Hk1_neq & Hlookup_obj1)];
          destruct Hlookup2 as [(Hk2_eq & Hobj2_eq) | (Hk2_neq & Hlookup_obj2)].
          - subst k1 k2. done.
          - subst k1. eapply no_duplicate_uid; [eauto|eauto|].
            rewrite -Huid_eq -Hobj1_eq. done.
          - subst k2. eapply no_duplicate_uid; [eauto|eauto|].
            rewrite Huid_eq -Hobj2_eq. done.
          - eapply no_duplicate_uid; [eauto|eauto|done].
        }
        {
          iPureIntro.
          intros k obj Hlookup.
          rewrite lookup_insert_Some in Hlookup.
          destruct Hlookup as [(Hk_eq & Hobj_eq) | (Hk_neq & Hlookup_obj)].
          - subst k obj. rewrite updated_pod_uid_eq. eapply existing_uid_is_used. done.
          - eapply existing_uid_is_used. done.
        }
        {
          iModIntro.
          iIntros (k s parent child_key child) "(%Hlookup_children & %Hlookup_child & %Hlookup_parent & %Hchild_in_s)".
          rewrite lookup_insert_Some in Hlookup_child.
          rewrite lookup_insert_Some in Hlookup_parent.
          destruct Hlookup_child as [(Heq_child & Hchild_eq) | (Hneq_child & Hlookup_child)];
          destruct Hlookup_parent as [(Heq_parent & Hparent_eq) | (Hneq_parent & Hlookup_parent)].
          - subst child_key k child parent.
            exfalso. by apply (no_self_parenting key s key Hlookup_children Hchild_in_s).
          - subst child_key child.
            rewrite updated_pod_owner_references_eq. iApply "children_point_to_parent". done.
          - subst k parent.
            rewrite updated_pod_uid_eq. iApply "children_point_to_parent". done.
          - iApply ("children_point_to_parent" $! k s parent child_key child). iPureIntro. done.
        }
        {
          iModIntro.
          iIntros (k s parent child_key child) "[(%Hlookup_children & %Hlookup_child & %Hlookup_parent) Hmeta]".
          rewrite lookup_insert_Some in Hlookup_child.
          rewrite lookup_insert_Some in Hlookup_parent.
          destruct Hlookup_child as [(Heq_child & Hchild_eq) | (Hneq_child & Hlookup_child)];
          destruct Hlookup_parent as [(Heq_parent & Hparent_eq) | (Hneq_parent & Hlookup_parent)].
          - subst child_key k child parent.
            rewrite updated_pod_owner_references_eq updated_pod_uid_eq.
            iDestruct ("only_children_point_to_parent" $! key s (PureKObject.Pod owned_pod) key (PureKObject.Pod owned_pod)
              with "[Hmeta]") as "%Hkey_in_s".
            { iFrame "Hmeta". iPureIntro. split; [|split]; done. }
            exfalso. by apply (no_self_parenting key s key Hlookup_children Hkey_in_s).
          - subst child_key child.
            rewrite updated_pod_owner_references_eq.
            iApply ("only_children_point_to_parent" $! k s parent key (PureKObject.Pod owned_pod) with "[Hmeta]").
            iFrame "Hmeta". iPureIntro. split; [|split]; done.
          - subst k parent.
            rewrite updated_pod_uid_eq.
            iApply ("only_children_point_to_parent" $! key s (PureKObject.Pod owned_pod) child_key child with "[Hmeta]").
            iFrame "Hmeta". iPureIntro. split; [|split]; done.
          - iApply ("only_children_point_to_parent" $! k s parent child_key child with "[Hmeta]").
            iFrame "Hmeta". iPureIntro. split; [|split]; done.
        }
        {
          iModIntro.
          iIntros (k obj uid) "%Hlookup".
          rewrite lookup_insert_Some in Hlookup.
          destruct Hlookup as [(Hk_eq & Hobj_eq) | (Hk_neq & Hlookup_obj)].
          - subst k obj. rewrite updated_pod_owner_references_eq.
            iApply "parent_uid_is_used". done.
          - iApply ("parent_uid_is_used" $! k obj uid). done.
        }
      }
      wp_apply (wp_Mutex__Unlock _ (is_kubernetes_state_inner γ_state γ_children γ_fresh_keys)
      with "[$own_Mutex state_m_addr state_used_uid_addr state_rvc_addr own_phys own_used_uid own_abs phys_abs_rep own_children own_fresh_keys]").
      { iFrame. iFrame "#". }
      iApply "HΦ". iFrame. iSplitR; [done|]. iLeft. iFrame.
      iAssert (⌜ now_ptr ≠ null ⌝%I) with "[now]" as "%now_ptr_not_null".
      { by iDestruct (typed_pointsto_not_null with "now") as %?. }
      iPureIntro. subst updated_pod. done.
    + iDestruct (struct_fields_combine (V:=v1.Pod.t) with "[$HTypeMeta $HObjectMeta $HSpec $HStatus]") as "pod_ptr".
      iAssert (state_rep phys_state abs_state %I) with "[pod_ptr other_rep]" as "phys_abs_rep".
      {
        iApply big_sepM2_split_singleton; [done | done|]. iFrame. unfold obj_rep. rewrite kind_is_pod.
        iExists ptr, owned_pod. iFrame. iFrame "#". done.
      }
      wp_apply (wp_Mutex__Unlock _ (is_kubernetes_state_inner γ_state γ_children γ_fresh_keys)
        with "[$own_Mutex state_m_addr state_used_uid_addr state_rvc_addr own_phys own_used_uid own_abs phys_abs_rep own_children own_fresh_keys]").
      { iFrame. iFrame "#". }
      iApply "HΦ". iSplitR; [done|]. iLeft. iFrame. done.
  - wp_apply wp_globals_get.
    wp_apply (wp_map_delete with "[$own_phys]").
    iIntros "own_phys". wp_auto.
    iDestruct (struct_fields_combine (V:=v1.Pod.t)
      with "[$HTypeMeta $HObjectMeta $HSpec $HStatus]") as "pod_ptr".
    iMod (auth_map.map_delete with "own_pod own_abs") as "own_abs".
    iMod (auth_map.map_update _ _ (owned_child_keys ∖ {[key]}) with "own_children own_child_keys")
      as "[own_children own_child_keys]".
    iMod (auth_map.map_delete with "own_grandchild_keys own_children") as "own_children".
    iAssert (state_rep (delete key phys_state) (delete key abs_state) %I) with "[other_rep]" as "phys_abs_rep".
    { done. }
    iAssert (kubernetes_state_consistent (dom used_uid) (delete key abs_state) (delete key (<[parent_key:=owned_child_keys ∖ {[key]}]> children)) fresh_keys %I)
    as "consistent'".
    {
      iNamed "consistent".
      assert (parent_key ≠ key) as parent_neq_key.
      { specialize (no_self_parenting parent_key owned_child_keys key parent_key_in_children pod_is_child). done. }
      assert (dom (delete key (<[parent_key:=owned_child_keys ∖ {[key]}]> children)) = dom (delete key children) )
      as Hdom_children_eq.
      {
        assert (key ≠ parent_key) as key_neq_parent by (symmetry; exact parent_neq_key).
        rewrite !dom_delete_L dom_insert_L.
        assert (parent_key ∈ dom children) as parent_in_children_dom.
        { apply elem_of_dom. exists owned_child_keys. exact parent_key_in_children. }
        assert ({[parent_key]} ∪ dom children = dom children) as union_eq.
        { set_solver. }
        rewrite union_eq.
        reflexivity.
      }
      iSplitR; [|iSplitR; [|iSplitR; [|iSplitR; [|iSplitR; [|iSplitR; [|iSplitR; [|iSplitR; [|iSplitR; [|iSplitR; [|iSplitR ]]]]]]]]]].
      { iPureIntro. set_solver. }
      {
        iPureIntro. intros k s Hlookup.
        rewrite lookup_delete_Some lookup_insert_Some in Hlookup.
        destruct Hlookup as (Hk_neq_key & [(Hk_eq & Hs_eq) | (Hk_neq_parent & Hlookup)]).
        - subst k s. rewrite dom_delete_L.
          assert (owned_child_keys ⊆ dom abs_state) as owned_children_in_abs.
          { apply children_exist with (k := parent_key). exact parent_key_in_children. }
          set_solver.
        - rewrite dom_delete_L.
          assert (s ⊆ dom abs_state) as s_in_abs by (apply children_exist with (k := k); exact Hlookup).
          assert (s ## owned_child_keys) as s_disj_owned.
          { destruct (decide (k = parent_key)); [congruence|]. eapply children_disjoint; done. }
          assert (key ∉ s) as key_not_in_s.
          { intros Hcontra. assert (key ∈ owned_child_keys) by exact pod_is_child. set_solver. }
          set_solver.
      }
      {
        iPureIntro. intros k s child_key Hlookup Hchild_in_s.
        rewrite lookup_delete_Some lookup_insert_Some in Hlookup.
        destruct Hlookup as (Hk_neq_key & [(Hk_eq & Hs_eq) | (Hk_neq_parent & Hlookup)]).
        - subst k s. eapply parents_children_same_namespace; [exact parent_key_in_children | set_solver].
        - eapply parents_children_same_namespace; done.
      }
      {
        iPureIntro. intros k s child_key Hlookup Hchild_in_s.
        rewrite lookup_delete_Some lookup_insert_Some in Hlookup.
        destruct Hlookup as (Hk_neq_key & [(Hk_eq & Hs_eq) | (Hk_neq_parent & Hlookup)]).
        - subst k s. eapply no_self_parenting; [exact parent_key_in_children | set_solver].
        - eapply no_self_parenting; done.
      }
      {
        iPureIntro. intros k1 s1 k2 s2 Hk1_neq_k2 Hlookup1 Hlookup2.
        rewrite lookup_delete_Some lookup_insert_Some in Hlookup1.
        rewrite lookup_delete_Some lookup_insert_Some in Hlookup2.
        destruct Hlookup1 as (Hk1_neq_key & [(Hk1_eq & Hs1_eq) | (Hk1_neq_parent & Hlookup1)]);
        [destruct Hlookup2 as (Hk2_neq_key & [(Hk2_eq & Hs2_eq) | (Hk2_neq_parent & Hlookup2)]) |
         destruct Hlookup2 as (Hk2_neq_key & [(Hk2_eq & Hs2_eq) | (Hk2_neq_parent & Hlookup2)])].
        - subst k1 k2. contradiction.
        - subst k1 s1.
          assert (owned_child_keys ## s2) as disj_orig.
          { apply children_disjoint with (k1 := parent_key) (k2 := k2); [|assumption|assumption].
            intros Heq. subst. contradiction. }
          set_solver.
        - subst k2 s2.
          assert (s1 ## owned_child_keys) as disj_orig.
          { apply children_disjoint with (k1 := k1) (k2 := parent_key); [|assumption|assumption].
            intros Heq. subst. contradiction. }
          set_solver.
        - apply children_disjoint with (k1 := k1) (k2 := k2); assumption.
      }
      { iPureIntro. rewrite dom_delete_L. set_solver. }
      { iPureIntro. apply fresh_keys_reserved. }
      {
        iPureIntro.
        intros k1 k2 obj1 obj2 Hlookup1 Hlookup2 Huid_eq.
        rewrite lookup_delete_Some in Hlookup1.
        rewrite lookup_delete_Some in Hlookup2.
        destruct Hlookup1 as (Hk1_neq_key & Hlookup_obj1).
        destruct Hlookup2 as (Hk2_neq_key & Hlookup_obj2).
        eapply no_duplicate_uid; [eauto|eauto|done].
      }
      {
        iPureIntro.
        intros k obj Hlookup.
        rewrite lookup_delete_Some in Hlookup.
        destruct Hlookup as (Hk_neq_key & Hlookup_obj).
        eapply existing_uid_is_used. done.
      }
      {
        iModIntro.
        iIntros (k s parent child_key child) "(%Hchildren_lookup & %Hchild_lookup & %Hparent_lookup & %Hchild_in_s)".
        rewrite lookup_delete_Some in Hchildren_lookup.
        rewrite lookup_delete_Some in Hchild_lookup.
        rewrite lookup_delete_Some in Hparent_lookup.
        destruct Hchildren_lookup as (Hk_neq_key, Hchildren_lookup).
        destruct Hchild_lookup as (Hchild_key_neq_key, Hchild_lookup).
        destruct Hparent_lookup as (Hk_neq_key', Hparent_lookup).
        rewrite lookup_insert_Some in Hchildren_lookup.
        destruct Hchildren_lookup as [(Hk_eq, Hs_eq) | (Hk_neq_parent, Hchildren_lookup)].
        - subst k s.
          iApply ("children_point_to_parent" $! parent_key owned_child_keys parent child_key child).
          iPureIntro. split; [|split; [|split]]; try done; set_solver.
        - iApply ("children_point_to_parent" $! k s parent child_key child).
          iPureIntro. split; [|split; [|split]]; done.
      }
      {
        iModIntro.
        iIntros (k s parent child_key child) "[(%Hchildren_lookup & %Hchild_lookup & %Hparent_lookup) Hmeta]".
        rewrite lookup_delete_Some in Hchildren_lookup.
        rewrite lookup_delete_Some in Hchild_lookup.
        rewrite lookup_delete_Some in Hparent_lookup.
        destruct Hchildren_lookup as (Hk_neq_key, Hchildren_lookup).
        destruct Hchild_lookup as (Hchild_key_neq_key, Hchild_lookup).
        destruct Hparent_lookup as (Hk_neq_key', Hparent_lookup).
        rewrite lookup_insert_Some in Hchildren_lookup.
        destruct Hchildren_lookup as [(Hk_eq, Hs_eq) | (Hk_neq_parent, Hchildren_lookup)].
        - subst k s.
          iDestruct ("only_children_point_to_parent" $! parent_key owned_child_keys parent child_key child
            with "[Hmeta]") as "%Hchild_in_owned".
          { iFrame "Hmeta". iPureIntro. split; [|split]; done. }
          iPureIntro. set_solver.
        - iDestruct ("only_children_point_to_parent" $! k s parent child_key child
            with "[Hmeta]") as "%Hchild_in_s".
          { iFrame "Hmeta". iPureIntro. split; [|split]; done. }
          iPureIntro. exact Hchild_in_s.
      }
      {
        iModIntro.
        iIntros (k obj uid) "%Hlookup".
        rewrite lookup_delete_Some in Hlookup.
        destruct Hlookup as (Hk_neq_key & Hlookup_obj).
        iApply ("parent_uid_is_used" $! k obj uid). done.
      }
    }
    wp_apply (wp_Mutex__Unlock _ (is_kubernetes_state_inner γ_state γ_children γ_fresh_keys)
      with "[$own_Mutex state_m_addr state_used_uid_addr state_rvc_addr own_phys own_used_uid own_abs phys_abs_rep own_children own_fresh_keys]").
    { iFrame. iFrame "#". }
    iApply "HΦ". iFrame. done.
    Unshelve.
    done.
Qed.

Lemma wp_PodDelete_ptsto_mut namespace name
  γ_state γ_children γ_fresh_keys owned_pod parent_key owned_child_keys owned_grandchild_keys:
  {{{ is_pkg_init apimodel ∗
      "#inv" ∷ is_kubernetes_state γ_state γ_children γ_fresh_keys ∗
      "own_pod" ∷ (mk_pod_key namespace name) [[ γ_state ]]↦ (PureKObject.Pod owned_pod) ∗
      "own_child_keys" ∷ parent_key [[ γ_children ]]↦ owned_child_keys ∗
      "own_grandchild_keys" ∷ (mk_pod_key namespace name) [[ γ_children ]]↦ owned_grandchild_keys ∗
      "%pod_is_child" ∷ ⌜ (mk_pod_key namespace name) ∈ owned_child_keys ⌝
  }}}
    @! apimodel.PodDelete #namespace #name
  {{{ (err: error.t) pod, RET #err;
      "err_is_nil" ∷ ⌜ err = interface.nil ⌝ ∗
      "pod_updated_or_deleted" ∷ ("pod_updated" ∷ (
        "own_pod" ∷ (mk_pod_key namespace name) [[ γ_state ]]↦ (PureKObject.Pod pod) ∗
        "own_child_keys" ∷ parent_key [[ γ_children ]]↦ owned_child_keys ∗
        "own_grandchild_keys" ∷ (mk_pod_key namespace name) [[ γ_children ]]↦ owned_grandchild_keys ∗
        "%deletiontimestamp_notnull" ∷ ⌜ pod.(v1.Pod.ObjectMeta').(v1.ObjectMeta.DeletionTimestamp') ≠ null ⌝
      ) ∨
      "own_child_keys" ∷ parent_key [[ γ_children ]]↦ (owned_child_keys ∖ {[mk_pod_key namespace name]}))
  }}}.
Proof.
  wp_start as "H". iNamed "H". wp_auto.
  wp_apply (wp_objDelete_pod_ptsto_mut with "[$own_pod $own_child_keys $own_grandchild_keys]").
  { iFrame "#". done. }
  iIntros (err pod) "H". iNamed "H". wp_auto. iApply "HΦ". iFrame.
Qed.

End proof.
