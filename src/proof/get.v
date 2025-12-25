From New.proof Require Import prelude empty_ffi.
From New.proof Require Export apimodel.

Section proof.
Context `{hG: !heapGS Σ} {go_ctx: GoContext}.
Context `{!mapG Σ KKey.t interface.t}.
Context `{!mapG Σ KKey.t PureKObject.t}.
Context `{!mapG Σ KKey.t (gset KKey.t)}.
Context `{!auth_setG Σ KKey.t}.

Lemma wp_State__objGet_replicaset γ l key pure_rs:
  {{{ is_pkg_init apimodel ∗
      "#Hisk" ∷ is_kubernetes γ l ∗
      "%Hkind_eq" ∷ ⌜ KKey.Kind' key = "ReplicaSet"%go ⌝ ∗
      "Hown_rs" ∷ key [[ γ.(γ_state) ]]↦ (PureKObject.ReplicaSet pure_rs)
  }}}
    l @ (ptrT.id apimodel.State.id) @ "objGet" #key
  {{{ ptr rs, RET (#(interface.mk (ptrT.id v1.ReplicaSet.id) #ptr), #true);
      PureReplicaSet.deepown_l ptr rs pure_rs 1 ∗
      ⌜ PureReplicaSet.well_formed pure_rs ⌝ ∗
      ⌜ pure_rs.(PureReplicaSet.ObjectMeta').(PureObjectMeta.Namespace') = key.(KKey.Namespace') ⌝ ∗
      ⌜ pure_rs.(PureReplicaSet.ObjectMeta').(PureObjectMeta.Name') = key.(KKey.Name') ⌝ ∗
      key [[ γ.(γ_state) ]]↦ (PureKObject.ReplicaSet pure_rs)
  }}}.
Proof.
  wp_start as "H". iNamed "H". iNamed "Hisk".
  wp_apply wp_with_defer. iIntros (defer) "Hdefer". simpl subst. wp_auto.
  wp_apply wp_Mutex__Lock; [done|]. iIntros "[Hown_Mutex H]". iNamedPrefix "H" "Hinv_". wp_auto.
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
  wp_apply (wp_Mutex__Unlock _ (kubernetes_inv γ l)
  with "[$Hown_Mutex H]").
  { iNamed "H". iFrame. iFrame "#". done. }
  iApply "HΦ". iFrame. done.
Qed.

Lemma wp_State__ReplicaSetMutGet γ l namespace name pure_rs:
  {{{ is_pkg_init apimodel ∗
      "#Hisk" ∷ is_kubernetes γ l ∗
      "Hown_rs" ∷ (mk_replicaset_key namespace name) [[ γ.(γ_state) ]]↦ (PureKObject.ReplicaSet pure_rs)
  }}}
    l @ (ptrT.id apimodel.State.id) @ "ReplicaSetMutGet" #namespace #name
  {{{ ptr rs, RET (#ptr, #interface.nil);
      PureReplicaSet.deepown_l ptr rs pure_rs 1 ∗
      ⌜ PureReplicaSet.well_formed pure_rs ⌝ ∗
      ⌜ pure_rs.(PureReplicaSet.ObjectMeta').(PureObjectMeta.Namespace') = namespace ⌝ ∗
      ⌜ pure_rs.(PureReplicaSet.ObjectMeta').(PureObjectMeta.Name') = name ⌝ ∗
      (mk_replicaset_key namespace name) [[ γ.(γ_state) ]]↦ (PureKObject.ReplicaSet pure_rs)
  }}}.
Proof.
  wp_start as "H". iNamed "H". wp_auto.
  wp_apply (wp_State__objGet_replicaset with "[$Hown_rs]"); [iFrame "#"; done|].
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

Lemma wp_State__ReplicaSetGet γ l namespace name pure_rs:
  {{{ is_pkg_init apimodel ∗
      "#Hisk" ∷ is_kubernetes γ l ∗
      "Hown_rs" ∷ (mk_replicaset_key namespace name) [[ γ.(γ_state) ]]↦ (PureKObject.ReplicaSet pure_rs)
  }}}
    l @ (ptrT.id apimodel.State.id) @ "ReplicaSetGet" #namespace #name
  {{{ ptr rs dq, RET (#ptr, #interface.nil);
      PureReplicaSet.deepown_l ptr rs pure_rs dq ∗
      ⌜ PureReplicaSet.well_formed pure_rs ⌝ ∗
      ⌜ pure_rs.(PureReplicaSet.ObjectMeta').(PureObjectMeta.Namespace') = namespace ⌝ ∗
      ⌜ pure_rs.(PureReplicaSet.ObjectMeta').(PureObjectMeta.Name') = name ⌝ ∗
      (mk_replicaset_key namespace name) [[ γ.(γ_state) ]]↦ (PureKObject.ReplicaSet pure_rs)
  }}}.
Proof.
  wp_start as "H". iNamed "H". wp_auto.
  wp_apply (wp_State__ReplicaSetMutGet with "[$Hown_rs]"); [done|].
  iIntros (ptr rs) "(Hdeepown_l_rs & %Hwell_formed_pure_rs & -> & -> & Hown_rs)". wp_auto.
  iApply "HΦ". iFrame. done.
Qed.

End proof.
