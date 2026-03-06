From New.proof Require Import prelude empty_ffi.
From New.proof.simple Require Export apimodel.

Section proof.
Context `{hG: !heapGS Σ} {go_ctx: GoContext}.
Context `{!mapG Σ KKey.t interface.t}.
Context `{!mapG Σ KKey.t KObjectV.t}.
Context `{!mapG Σ KKey.t (gset KKey.t)}.
Context `{!auth_setG Σ KKey.t}.

Lemma wp_State__objGet γ l key pure_kobj:
  {{{ is_pkg_init apimodel ∗
      "#Hisk" ∷ is_kubernetes γ l ∗
      "Hghost" ∷ key [[ γ.(γ_state) ]]↦ pure_kobj
  }}}
    l @ (ptrT.id apimodel.State.id) @ "objGet" #key
  {{{ obj ptr, RET (#obj, #true);
      ⌜ KObjectV.valid_interface obj ptr pure_kobj ⌝ ∗
      KObjectV.deepown_l ptr pure_kobj 1 ∗
      ⌜ KObjectV.valid_old pure_kobj ⌝ ∗
      ⌜ key.(KKey.Namespace') = (KObjectV.objectmeta pure_kobj).(ObjectMetaV.Namespace') ⌝ ∗
      ⌜ key.(KKey.Name') = (KObjectV.objectmeta pure_kobj).(ObjectMetaV.Name') ⌝ ∗
      key [[ γ.(γ_state) ]]↦ pure_kobj
  }}}.
Proof.
  wp_start as "H". iNamed "H". iNamed "Hisk".
  wp_apply wp_with_defer. iIntros (defer) "Hdefer". simpl subst. wp_auto.
  wp_apply wp_Mutex__Lock; [done|]. iIntros "[Hown_Mutex H]". iNamedPrefix "H" "Hinv_". wp_auto.
  iAssert (⌜ abs_state !! key = Some pure_kobj ⌝%I) with "[Hghost Hinv_Hown_abs]" as "%Hkey_in_abs".
  { iDestruct (map_valid with "Hinv_Hown_abs Hghost") as %Hlookup.
    iPureIntro; exact Hlookup. }
  iAssert (⌜ ∃ obj, phys_state !! key = Some obj ⌝%I) with "[Hinv_Hphys_abs_rep]" as "%Hinv_Hkey_in_phys".
  { iDestruct (big_sepM2_lookup_r with "Hinv_Hphys_abs_rep") as (obj Hkey_in_phys) "_".
    { exact Hkey_in_abs. }
    iPureIntro. exists obj. exact Hkey_in_phys. }
  destruct Hinv_Hkey_in_phys as [obj Hinv_Hkey_in_phys].
  iDestruct (big_sepM2_lookup_acc _ _ _ _ _ _ Hinv_Hkey_in_phys Hkey_in_abs with "Hinv_Hphys_abs_rep")
    as "(Hk_rep & Hother_rep)".
  iDestruct "Hk_rep" as "(%ptr & %kobj & %Hvalid_interface & Hdeepown_l)".
  wp_apply (wp_map_get with "[$Hinv_Hown_phys]"). iIntros "Hinv_Hown_phys". wp_auto.
  rewrite /is_Some Hinv_Hkey_in_phys. wp_auto.
  iAssert (KObjectV.deepown_i obj pure_kobj 1) with "[Hdeepown_l]" as "Hdeepown_i".
  { iExists ptr. iSplit; first done. iFrame. }
  wp_apply (wp_deepCopy with "[$Hdeepown_i]").
  iIntros (obj') "(Hdeepown_i' & Hdeepown_i)". wp_auto.
  iDestruct "Hdeepown_i'" as (ptr') "(%Hvalid_interface' & Hdeepown_l')".
  iDestruct "Hdeepown_i" as (ptr0) "(%Hvalid_interface0 & Hdeepown_l0)".
  iAssert (state_rep phys_state abs_state) with "[Hdeepown_l0 Hother_rep]" as "Hinv_Hphys_abs_rep".
  { iApply "Hother_rep". iExists ptr0, kobj. iFrame. done. }
  assert (key = KObjectV.key pure_kobj ∧ KObjectV.valid_old pure_kobj) as [-> Hwf].
  { destruct Hinv_Hghost_valid. apply Habs_state_valid. exact Hkey_in_abs. }
  iCombineNamed "Hinv_*" as "H".
  wp_apply (wp_Mutex__Unlock _ (kubernetes_inv γ l) with "[$Hown_Mutex H]").
  { iNamed "H". iFrame. iFrame "#". done. }
  iApply "HΦ". iFrame. iPureIntro. split; [done|]. split_and!;[done|done|done].
Qed.

Lemma wp_State__ReplicaSetMutGet γ l key namespace name pure_rs:
  {{{ is_pkg_init apimodel ∗
      "#Hisk" ∷ is_kubernetes γ l ∗
      "%Hkey_eq" ∷ ⌜ key = (mk_replicaset_key namespace name) ⌝ ∗
      "Hghost" ∷ key [[ γ.(γ_state) ]]↦ (KObjectV.ReplicaSet pure_rs)
  }}}
    l @ (ptrT.id apimodel.State.id) @ "ReplicaSetMutGet" #namespace #name
  {{{ ptr rs, RET (#ptr, #interface.nil);
      ptr ↦ rs ∗ ReplicaSetV.deepown rs pure_rs 1 ∗
      ⌜ ReplicaSetV.valid pure_rs ⌝ ∗
      ⌜ namespace = pure_rs.(ReplicaSetV.ObjectMeta').(ObjectMetaV.Namespace') ⌝ ∗
      ⌜ name = pure_rs.(ReplicaSetV.ObjectMeta').(ObjectMetaV.Name') ⌝ ∗
      (mk_replicaset_key namespace name) [[ γ.(γ_state) ]]↦ (KObjectV.ReplicaSet pure_rs)
  }}}.
Proof.
  wp_start as "H". iNamed "H". wp_auto. subst key. unfold mk_replicaset_key.
  wp_apply (wp_State__objGet with "[$Hghost]"); [iFrame "#";done|].
  iIntros (obj ptr) "(%Hvalid_interface & Hdeepown_l & %Hwf & %Hns_eq & %Hname_eq & Hghost)". wp_auto.
  unfold KObjectV.valid_interface in Hvalid_interface. rewrite Hvalid_interface.
  unshelve wp_apply wp_interface_checked_type_assert; try tc_solve.
  { iPureIntro. intros ptr_id. exists ptr. done. }
  iIntros (y ok) "%if_ok".
  assert (ok = true) as ->.
  { destruct ok; [done|]. intuition. }
  wp_auto.
  assert (ptr = y) as ->.
  { inversion if_ok. apply (inj to_val). done. }
  iPoseProof (KObjectV.replicaset_deepown_l with "Hdeepown_l") as "Hdeepown_l".
  iDestruct "Hdeepown_l" as (rs) "[Hptr Hdeepown_rs]".
  iApply "HΦ". iFrame. done.
Qed.

Lemma wp_State__ReplicaSetGet γ l key namespace name pure_rs:
  {{{ is_pkg_init apimodel ∗
      "#Hisk" ∷ is_kubernetes γ l ∗
      "%Hkey_eq" ∷ ⌜ key = (mk_replicaset_key namespace name) ⌝ ∗
      "Hghost" ∷ key [[ γ.(γ_state) ]]↦ (KObjectV.ReplicaSet pure_rs)
  }}}
    l @ (ptrT.id apimodel.State.id) @ "ReplicaSetGet" #namespace #name
  {{{ ptr rs dq, RET (#ptr, #interface.nil);
      ptr ↦{dq} rs ∗ ReplicaSetV.deepown rs pure_rs dq ∗
      ⌜ ReplicaSetV.valid pure_rs ⌝ ∗
      ⌜ namespace = pure_rs.(ReplicaSetV.ObjectMeta').(ObjectMetaV.Namespace') ⌝ ∗
      ⌜ name = pure_rs.(ReplicaSetV.ObjectMeta').(ObjectMetaV.Name') ⌝ ∗
      (mk_replicaset_key namespace name) [[ γ.(γ_state) ]]↦ (KObjectV.ReplicaSet pure_rs)
  }}}.
Proof.
  wp_start as "H". iNamed "H". wp_auto.
  wp_apply (wp_State__ReplicaSetMutGet with "[$Hghost]"); [iFrame "#";done|].
  iIntros (ptr rs) "(Hptr & Hdeepown_rs & %Hwf & <- & <- & Hghost)". wp_auto.
  iApply "HΦ". iFrame. done.
Qed.

End proof.
