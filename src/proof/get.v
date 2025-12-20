From Perennial.algebra Require Export auth_map.
From New.proof.github_com.goose_lang.goose.model.channel Require Export auth_set.
Require Export New.proof.sync.

From proof.kubernetes_model Require Export apimodel_init.
From proof.k8s_io.apimachinery.pkg.api Require Export meta.
From proof.k8s_io.apimachinery.pkg.apis.meta Require Export v1.
From proof Require Import prelude empty_ffi.
From proof Require Export apimodel.
From proof.big_op Require Import big_sepL big_sepM.
Export apimodel.apimodel.

Section proof.
Context `{hG: !heapGS Σ} {go_ctx: GoContext}.
Context `{!mapG Σ KKey.t interface.t}.
Context `{!mapG Σ KKey.t PureKObject.t}.
Context `{!mapG Σ KKey.t (gset KKey.t)}.
Context `{!auth_setG Σ KKey.t}.

Lemma wp_objGet_replicaset_ptsto_mut key γ_state γ_children γ_fresh_keys pure_rs:
  {{{ is_pkg_init apimodel ∗
      "#Hinv" ∷ is_kubernetes_state γ_state γ_children γ_fresh_keys ∗
      "%Hkind_eq" ∷ ⌜ KKey.Kind' key = "ReplicaSet"%go ⌝ ∗
      "Hown_rs" ∷ key [[ γ_state ]]↦ (PureKObject.ReplicaSet pure_rs)
  }}}
    @! apimodel.objGet #key
  {{{ ptr rs, RET (#(interface.mk (ptrT.id v1.ReplicaSet.id) #ptr), #true);
      PureReplicaSet.deepown_l ptr rs pure_rs 1 ∗
      ⌜ PureReplicaSet.well_formed pure_rs ⌝ ∗
      ⌜ pure_rs.(PureReplicaSet.ObjectMeta').(PureObjectMeta.Namespace') = key.(KKey.Namespace') ⌝ ∗
      ⌜ pure_rs.(PureReplicaSet.ObjectMeta').(PureObjectMeta.Name') = key.(KKey.Name') ⌝ ∗
      key [[ γ_state ]]↦ (PureKObject.ReplicaSet pure_rs)
  }}}.
Proof.
  wp_start as "H". iNamed "H".
  wp_apply wp_with_defer. iIntros (defer) "Hdefer". simpl subst. wp_auto.
  wp_apply wp_globals_get. wp_apply wp_Mutex__Lock; [done|]. iIntros "[Hown_Mutex H]". iNamedPrefix "H" "Hinv_". wp_auto.
  wp_apply wp_globals_get. wp_apply wp_globals_get.
  iAssert (⌜ abs_state !! key = Some (PureKObject.ReplicaSet pure_rs) ⌝%I) with "[Hown_rs Hinv_Hown_abs]" as "%Hkey_in_abs".
  { iDestruct (map_valid with "Hinv_Hown_abs Hown_rs") as %Hlookup.
    iPureIntro; exact Hlookup. }
  iAssert (⌜ ∃ obj, phys_state !! key = Some obj ⌝%I) with "[Hinv_Hphys_abs_rep]" as "%Hinv_Hkey_in_phys".
  { iDestruct (big_sepM2_lookup_r with "Hinv_Hphys_abs_rep") as (obj Hkey_in_phys) "_".
    { exact Hkey_in_abs. }
    iPureIntro. exists obj. exact Hkey_in_phys. }
  destruct Hinv_Hkey_in_phys as [obj Hinv_Hkey_in_phys].
  iDestruct (big_sepM2_lookup_acc _ _ _ _ _ _ Hinv_Hkey_in_phys Hkey_in_abs with "Hinv_Hphys_abs_rep") as "[Hk_rep Hother_rep]".
  destruct decide_kind_is_replicaset with (KKey.Kind' key) as [Hkind_is_replicaset Hkind_is_not_pod]; [done|].
  unfold obj_rep. rewrite Hkind_is_replicaset Hkind_is_not_pod.
  iDestruct "Hk_rep" as "(%ptr & %rs & %pure_rs' & H)". iNamed "H". injection Habs_v_is_rs as <-.
  wp_apply (wp_map_get with "[$Hinv_Hown_phys]"). iIntros "Hinv_Hown_phys". wp_auto.
  rewrite /is_Some Hinv_Hkey_in_phys. wp_auto.
  wp_apply (wp_deepCopy_replicaset with "[$Hdeepown_l_rs]"); [done|].
  iIntros (copied_ptr copied_rs) "(Hdeepown_l_copied_rs & Hdeepown_l_rs)". wp_auto.
  iAssert (state_rep phys_state abs_state) with "[Hdeepown_l_rs Hother_rep]" as "Hinv_Hphys_abs_rep".
  { iApply "Hother_rep". iExists ptr, rs, pure_rs. iFrame. done. }
  assert (PureKObject.agree_with_key (PureKObject.ReplicaSet pure_rs) key ∧ PureKObject.well_formed (PureKObject.ReplicaSet pure_rs))
    as [Hagree Hwell_formed].
  { destruct Hinv_Hghost_well_formed. apply Habs_state_well_formed. exact Hkey_in_abs. }
  destruct Hagree as [Hkind [Hnamespace Hname]].
  iCombineNamed "Hinv_*" as "H".
  wp_apply (wp_Mutex__Unlock _ (is_kubernetes_state_inner γ_state γ_children γ_fresh_keys)
  with "[$Hown_Mutex H]").
  { iNamed "H". iFrame. iFrame "#". done. }
  iApply "HΦ". iFrame. done.
Qed.

Lemma wp_ReplicaSetMutGet_ptsto_mut namespace name γ_state γ_children γ_fresh_keys pure_rs:
  {{{ is_pkg_init apimodel ∗
      "#Hinv" ∷ is_kubernetes_state γ_state γ_children γ_fresh_keys ∗
      "Hown_rs" ∷ (mk_replicaset_key namespace name) [[ γ_state ]]↦ (PureKObject.ReplicaSet pure_rs)
  }}}
    @! apimodel.ReplicaSetMutGet #namespace #name
  {{{ ptr rs, RET (#ptr, #interface.nil);
      PureReplicaSet.deepown_l ptr rs pure_rs 1 ∗
      ⌜ PureReplicaSet.well_formed pure_rs ⌝ ∗
      ⌜ pure_rs.(PureReplicaSet.ObjectMeta').(PureObjectMeta.Namespace') = namespace ⌝ ∗
      ⌜ pure_rs.(PureReplicaSet.ObjectMeta').(PureObjectMeta.Name') = name ⌝ ∗
      (mk_replicaset_key namespace name) [[ γ_state ]]↦ (PureKObject.ReplicaSet pure_rs)
  }}}.
Proof.
  wp_start as "H". iNamed "H". wp_auto.
  wp_apply (wp_objGet_replicaset_ptsto_mut with "[$Hown_rs]"); [iFrame "#"; done|].
  iIntros (ptr rs) "(Hdeepown_l_rs & %Hwell_formed_pure_rs & -> & -> & Hown_pure_rs)". wp_auto.
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
      "Hown_rs" ∷ (mk_replicaset_key namespace name) [[ γ_state ]]↦ (PureKObject.ReplicaSet pure_rs)
  }}}
    @! apimodel.ReplicaSetGet #namespace #name
  {{{ ptr rs dq, RET (#ptr, #interface.nil);
      PureReplicaSet.deepown_l ptr rs pure_rs dq ∗
      ⌜ PureReplicaSet.well_formed pure_rs ⌝ ∗
      ⌜ pure_rs.(PureReplicaSet.ObjectMeta').(PureObjectMeta.Namespace') = namespace ⌝ ∗
      ⌜ pure_rs.(PureReplicaSet.ObjectMeta').(PureObjectMeta.Name') = name ⌝ ∗
      (mk_replicaset_key namespace name) [[ γ_state ]]↦ (PureKObject.ReplicaSet pure_rs)
  }}}.
Proof.
  wp_start as "H". iNamed "H". wp_auto.
  wp_apply (wp_ReplicaSetMutGet_ptsto_mut with "[$Hown_rs]"); [done|].
  iIntros (l rs) "(Hdeepown_l_rs & %Hwell_formed_pure_rs & -> & -> & Hown_rs)". wp_auto.
  iApply "HΦ". iFrame. done.
Qed.

End proof.
