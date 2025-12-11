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

Lemma wp_objGet_replicaset_ptsto_mut key γ_state γ_children γ_fresh_keys pure_rs:
  {{{ is_pkg_init apimodel ∗
      "#Hinv" ∷ is_kubernetes_state γ_state γ_children γ_fresh_keys ∗
      "%Hkind_eq" ∷ ⌜ KKey.Kind' key = "ReplicaSet"%go ⌝ ∗
      "Hown_rs" ∷ key [[ γ_state ]]↦ (KObject.ReplicaSet pure_rs)
  }}}
    @! apimodel.objGet #key
  {{{ obj exists' ptr rs, RET (#obj, #exists');
      ⌜ obj = interface.mk (ptrT.id v1.ReplicaSet.id) #ptr ⌝ ∗
      ⌜ exists' = true ⌝ ∗
      ptr ↦ rs ∗
      ReplicaSet.own rs pure_rs ∗
      ⌜ well_formed_ReplicaSet pure_rs ⌝ ∗
      ⌜ pure_rs.(PureReplicaSet.ObjectMeta').(PureObjectMeta.Namespace') = (KKey.Namespace' key) ⌝ ∗
      ⌜ pure_rs.(PureReplicaSet.ObjectMeta').(PureObjectMeta.Name') = (KKey.Name' key) ⌝ ∗
      key [[ γ_state ]]↦ (KObject.ReplicaSet pure_rs)
  }}}.
Proof.
  wp_start as "H". iNamed "H".
  wp_apply wp_with_defer. iIntros (defer) "Hdefer". simpl subst. wp_auto.
  wp_apply wp_globals_get. wp_apply wp_Mutex__Lock; [done|]. iIntros "[Hown_Mutex H]". iNamed "H". wp_auto.
  wp_apply wp_globals_get. wp_apply wp_globals_get.
  iAssert (⌜ abs_state !! key = Some (KObject.ReplicaSet pure_rs) ⌝%I) with "[Hown_rs Hown_abs]" as "%Hkey_in_abs".
  { iDestruct (map_valid with "Hown_abs Hown_rs") as %Hlookup.
    iPureIntro; exact Hlookup. }
  iAssert (⌜ ∃ obj, phys_state !! key = Some obj ⌝%I) with "[Hphys_abs_rep]" as "%Hkey_in_phys".
  { iDestruct (big_sepM2_lookup_r with "Hphys_abs_rep") as (obj Hkey_in_phys) "_".
    { exact Hkey_in_abs. }
    iPureIntro. exists obj. exact Hkey_in_phys. }
  destruct Hkey_in_phys as [obj Hkey_in_phys].
  iDestruct (big_sepM2_lookup_acc _ _ _ _ _ _ Hkey_in_phys Hkey_in_abs with "Hphys_abs_rep") as "[Hk_rep Hother_rep]".
  destruct decide_kind_is_replicaset with (KKey.Kind' key) as [Hkind_is_replicaset Hkind_is_not_pod]; [done|].
  unfold obj_rep. rewrite Hkind_is_replicaset Hkind_is_not_pod.
  iDestruct "Hk_rep" as "(%ptr & %rs & H)". iNamed "H". injection Habs_v_is_rs as <-.
  wp_apply (wp_map_get with "[$Hown_phys]"). iIntros "Hown_phys". wp_auto.
  rewrite /is_Some Hkey_in_phys. wp_auto.
  wp_apply (wp_deepCopy_replicaset with "[$Hrs_ptr $Hdeepown_rs]"); [done|].
  iIntros (copied_obj copied_ptr copied_rs) "(%H_copied_obj_is_ptr & Hcopied_ptr & Hdeepown_copied_rs & Hrs_ptr & Hdeepown_rs)". wp_auto.
  iAssert (state_rep phys_state abs_state %I) with "[Hrs_ptr Hother_rep Hdeepown_rs]" as "Hphys_abs_rep".
  { iApply "Hother_rep". iExists ptr, rs, pure_rs. iFrame. done. }
  wp_apply (wp_Mutex__Unlock _ (is_kubernetes_state_inner γ_state γ_children γ_fresh_keys)
  with "[$Hown_Mutex Hstate_m_addr Hstate_used_uid_addr Hstate_rvc_addr Hown_phys Hown_used_uid Hown_abs Hphys_abs_rep Hown_children Hown_fresh_keys]").
  { iFrame. iFrame "#". }
  iApply ("HΦ" $! copied_obj true copied_ptr copied_rs).
  iFrame. done.
Qed.

Lemma wp_ReplicaSetMutGet_ptsto_mut namespace name γ_state γ_children γ_fresh_keys pure_rs:
  {{{ is_pkg_init apimodel ∗
      "#Hinv" ∷ is_kubernetes_state γ_state γ_children γ_fresh_keys ∗
      "Hown_rs" ∷ (mk_replicaset_key namespace name) [[ γ_state ]]↦ (KObject.ReplicaSet pure_rs)
  }}}
    @! apimodel.ReplicaSetMutGet #namespace #name
  {{{ l (err: error.t) rs, RET (#l, #err);
      l ↦ rs ∗
      ⌜ err = interface.nil ⌝ ∗
      ReplicaSet.own rs pure_rs ∗
      ⌜ well_formed_ReplicaSet pure_rs ⌝ ∗
      ⌜ pure_rs.(PureReplicaSet.ObjectMeta').(PureObjectMeta.Namespace') = namespace ⌝ ∗
      ⌜ pure_rs.(PureReplicaSet.ObjectMeta').(PureObjectMeta.Name') = name ⌝ ∗
      (mk_replicaset_key namespace name) [[ γ_state ]]↦ (KObject.ReplicaSet pure_rs)
  }}}.
Proof.
  wp_start as "H". iNamed "H". wp_auto.
  wp_apply (wp_objGet_replicaset_ptsto_mut with "[$Hown_rs]"); [iFrame "#"; done|].
  iIntros (obj exists' ptr rs) "(-> & -> & Hptr & Hdeepown_rs & %Hwell_formed_pure_rs & -> & -> & Hown_pure_rs)". wp_auto.
  unshelve wp_apply wp_interface_checked_type_assert; try tc_solve.
  { iPureIntro. intros ptr_id. exists ptr. done. }
  iIntros (y ok) "%if_ok".
  assert (ok = true) as ->.
  { destruct ok; [done|]. intuition. }
  wp_auto.
  assert (ptr = y) as ->.
  { inversion if_ok. apply (inj to_val). done. }
  iApply "HΦ". iFrame. done.
Qed.

Lemma wp_ReplicaSetGet_ptsto_mut namespace name γ_state γ_children γ_fresh_keys pure_rs:
  {{{ is_pkg_init apimodel ∗
      "#Hinv" ∷ is_kubernetes_state γ_state γ_children γ_fresh_keys ∗
      "Hown_rs" ∷ (mk_replicaset_key namespace name) [[ γ_state ]]↦ (KObject.ReplicaSet pure_rs)
  }}}
    @! apimodel.ReplicaSetGet #namespace #name
  {{{ l (err: error.t) rs dq, RET (#l, #err);
      l ↦{dq} rs ∗
      ⌜ err = interface.nil ⌝ ∗
      ReplicaSet.own rs pure_rs ∗
      ⌜ well_formed_ReplicaSet pure_rs ⌝ ∗
      ⌜ pure_rs.(PureReplicaSet.ObjectMeta').(PureObjectMeta.Namespace') = namespace ⌝ ∗
      ⌜ pure_rs.(PureReplicaSet.ObjectMeta').(PureObjectMeta.Name') = name ⌝ ∗
      (mk_replicaset_key namespace name) [[ γ_state ]]↦ (KObject.ReplicaSet pure_rs)
  }}}.
Proof.
  wp_start as "H". iNamed "H". wp_auto.
  wp_apply (wp_ReplicaSetMutGet_ptsto_mut with "[$Hown_rs]"); [done|].
  iIntros (l err rs) "(Hl & -> & Hdeepown_rs & %Hwell_formed_pure_rs & -> & -> & Hown_rs)". wp_auto.
  iApply "HΦ". iFrame. done.
Qed.

(* TODO: revisit this spec *)
Lemma wp_ByIndex_pod_ptsto_mut kind index_name indexed_value
  γ_state γ_children γ_fresh_keys parent_key owned_parent owned_pod_map owned_child_keys:
  {{{ is_pkg_init apimodel ∗
      "#inv" ∷ is_kubernetes_state γ_state γ_children γ_fresh_keys ∗
      "own_parent" ∷ parent_key [[ γ_state ]]↦ owned_parent ∗
      "own_pods" ∷ ([∗ map] key ↦ pod ∈ owned_pod_map, key [[ γ_state ]]↦ KObject.Pod pod) ∗
      "own_child_keys" ∷ parent_key [[ γ_children ]]↦ owned_child_keys ∗
      "%owned_child_keys_equal_dom_owned_pods" ∷ ⌜ owned_child_keys = dom owned_pod_map ⌝ ∗
      "%indexed_value" ∷ ⌜ indexed_value = (extract_kobject_metadata owned_parent).(PureObjectMeta.UID') ⌝ ∗
      "%kind" ∷ ⌜ kind = "Pod"%go ⌝ ∗
      "%index_name" ∷ ⌜ index_name = "podControllerUID"%go ⌝
  }}}
    @! apimodel.ByIndex #kind #index_name #indexed_value
  {{{ (l: slice.t) (err: error.t) (objs: list interface.t) (pods: list v1.Pod.t), RET (#l, #err);
      "l" ∷ l ↦* objs ∗
      "%err_is_nil" ∷ ⌜ err = interface.nil ⌝ ∗
      "obj_pts_to_pod" ∷ ([∗ list] obj ; pod ∈ objs ; pods, ∃ (ptr : loc) (owned_pod : PurePod.t),
        ⌜ obj = interface.mk (ptrT.id v1.Pod.id) #ptr ⌝ ∗
        ptr ↦ pod ∗
        Pod.own pod owned_pod ∗
        ⌜ ∃ k, owned_pod_map !! k = Some owned_pod ⌝ ∗
        ⌜ obj_has_controller_parent_of (KObject.Pod owned_pod) parent_key.(KKey.Kind') parent_key.(KKey.Name') indexed_value ⌝ ∗
        ⌜ well_formed_Pod owned_pod ⌝
      ) ∗
      "%key_set_equal_dom_owned_pods" ∷  ⌜ list_to_set (extract_pod_key <$> pods) = dom owned_pod_map ⌝ ∗
      "own_parent" ∷ parent_key [[ γ_state ]]↦ owned_parent ∗
      "own_pods" ∷ ([∗ map] key ↦ pod ∈ owned_pod_map, key [[ γ_state ]]↦ KObject.Pod pod) ∗
      "own_child_keys" ∷ parent_key [[ γ_children ]]↦ owned_child_keys
  }}}.
Proof.
Admitted.

End proof.
