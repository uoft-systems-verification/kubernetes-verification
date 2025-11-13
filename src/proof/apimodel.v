From Perennial.algebra Require Export auth_map.
From New.proof.github_com.goose_lang.goose.model.channel Require Export auth_set.
Require Export New.proof.sync.

From proof.kubernetes_model Require Export apimodel_init.
From proof Require Import prelude empty_ffi.
Export apimodel.apimodel.

Module KKey.
  Global Instance eq_dec : EqDecision KKey.t.
  Proof. solve_decision. Qed.

  Global Instance countable : Countable KKey.t.
  Proof.
    refine (inj_countable'
              (λ k, (KKey.Kind' k,
                     KKey.Name' k,
                     KKey.Namespace' k))
              (λ '(kind, name, namespace),
                KKey.mk kind name namespace)
              _).
    intros []; reflexivity.
  Qed.
End KKey.

Module KObject.
  Inductive t :=
  | Pod (p : v1.Pod.t)
  | ReplicaSet (rs : v1.ReplicaSet.t).
End KObject.

Global Existing Instance KKey.eq_dec.
Global Existing Instance KKey.countable.

Section proof.
Context `{hG: !heapGS Σ} {go_ctx: GoContext}.
Context `{!mapG Σ KKey.t interface.t}.
Context `{!mapG Σ KKey.t KObject.t}.
Context `{!mapG Σ KKey.t (gset KKey.t)}.
Context `{!auth_setG Σ KKey.t}.

Definition mk_pod_key (namespace name: go_string) : KKey.t :=
  {| KKey.Kind' := "Pod"%go; KKey.Namespace' := namespace; KKey.Name' := name;|}.

Definition extract_pod_key pod : KKey.t :=
  mk_pod_key pod.(v1.Pod.ObjectMeta').(v1.ObjectMeta.Namespace') pod.(v1.Pod.ObjectMeta').(v1.ObjectMeta.Name').

Definition mk_replicaset_key (namespace name: go_string) : KKey.t :=
  {| KKey.Kind' := "ReplicaSet"%go; KKey.Namespace' := namespace; KKey.Name' := name;|}.


Definition pod_well_formed (pod: v1.Pod.t) : iProp Σ :=
  True%I.

Definition pod_nn_well_formed (pod: v1.Pod.t) (namespace name: go_string) : iProp Σ :=
  ⌜ pod.(v1.Pod.ObjectMeta').(v1.ObjectMeta.Namespace') = namespace ⌝ ∗
  ⌜ pod.(v1.Pod.ObjectMeta').(v1.ObjectMeta.Name') = name ⌝ ∗
  pod_well_formed pod.


Definition replicaset_nn_well_formed (rs: v1.ReplicaSet.t) (namespace name: go_string) : iProp Σ :=
 True%I.

Definition pod_rep k v1 v2 ptr pod : iProp Σ :=
  "%interface_is_pod_ptr" ∷ ⌜ v1 = interface.mk (ptrT.id v1.Pod.id) #ptr ⌝ ∗
  "pod_ptr" ∷ ptr ↦ pod ∗
  "%abs_v_is_pod" ∷ ⌜ v2 = KObject.Pod pod ⌝ ∗
  "%pod_nn_well_formed" ∷ pod_nn_well_formed pod (KKey.Namespace' k) (KKey.Name' k).

Definition replicaset_rep k v1 v2 ptr rs : iProp Σ :=
  "%interface_is_rs_ptr" ∷ ⌜ v1 = interface.mk (ptrT.id v1.ReplicaSet.id) #ptr ⌝ ∗
  "rs_ptr" ∷ ptr ↦ rs ∗
  "%abs_v_is_rs" ∷ ⌜ v2 = KObject.ReplicaSet rs ⌝ ∗
  "%replicaset_nn_well_formed" ∷ replicaset_nn_well_formed rs (KKey.Namespace' k) (KKey.Name' k).

Definition state_rep (phys_state: gmap KKey.t interface.t) (abs_state: gmap KKey.t KObject.t) : iProp Σ :=
  [∗ map] k ↦ v1; v2 ∈ phys_state; abs_state,
    if bool_decide (KKey.Kind' k = "Pod"%go) then
      ∃ (ptr: loc) (pod: v1.Pod.t), pod_rep k v1 v2 ptr pod
    else if bool_decide (KKey.Kind' k = "ReplicaSet"%go) then
      ∃ (ptr: loc) (rs: v1.ReplicaSet.t), replicaset_rep k v1 v2 ptr rs
    else False%I.


Definition kubernetes_state_consistent (abs_state: gmap KKey.t KObject.t) (children: gmap KKey.t (gset KKey.t)) (fresh_keys: gset KKey.t): Prop := 
  True.


Definition is_kubernetes_state_inner γ_state γ_children γ_fresh_keys: iProp Σ :=
  ∃ (l: loc) (phys_state: gmap KKey.t interface.t) (abs_state: gmap KKey.t KObject.t) (children: gmap KKey.t (gset KKey.t)) (fresh_keys: gset KKey.t),
    "state_m_addr" ∷ (global_addr apimodel.state) ↦s[ apimodel.State :: "m" ] l ∗
    "own_phys" ∷ l ↦$ phys_state ∗
    "own_abs" ∷ map_ctx γ_state 1 abs_state ∗
    "phys_abs_rep" ∷ state_rep phys_state abs_state ∗
    "own_children" ∷ map_ctx γ_children 1 children ∗
    "own_fresh_keys" ∷ auth_set_auth γ_fresh_keys fresh_keys ∗
    "%consistent" ∷ ⌜ kubernetes_state_consistent abs_state children fresh_keys ⌝ .


Definition is_kubernetes_state γ_state γ_children γ_fresh_keys : iProp Σ :=
  is_Mutex (global_addr apimodel.stateMu) (is_kubernetes_state_inner γ_state γ_children γ_fresh_keys).

(* TODO: finish the deepcopy definition *)
Definition is_deepcopy_pod (pod1 pod2: v1.Pod.t) : iProp Σ :=
  True%I.

Definition is_deepcopy_replicaset (rs1 rs2: v1.ReplicaSet.t) : iProp Σ :=
  True%I.

Definition pod_has_controller_parent_uid (pod: v1.Pod.t) (os: list v1.OwnerReference.t) (o: v1.OwnerReference.t) (c: bool) : iProp Σ :=
  pod.(v1.Pod.ObjectMeta').(v1.ObjectMeta.OwnerReferences') ↦* os ∗
  ⌜ o ∈ os ⌝ ∗
  o.(v1.OwnerReference.Controller') ↦ c ∗
  ⌜ c = true ⌝.

Definition index_is_pod_controller_uid_index (pod: v1.Pod.t) (index: go_string): iProp Σ :=
  (∃ os o c, pod_has_controller_parent_uid pod os o c ∗ ⌜ o.(v1.OwnerReference.UID') = index ⌝) ∨
  (¬(∃ os o c, pod_has_controller_parent_uid pod os o c) ∗ ⌜ index = "_ORPHAN_POD"%go ⌝).

Lemma well_formed_preserved_by_deepcopy_replicaset rs1 rs2 namespace name:
  is_deepcopy_replicaset rs1 rs2 -∗
    replicaset_nn_well_formed rs1 namespace name -∗
      replicaset_nn_well_formed rs2 namespace name.
Proof.
Admitted.

Lemma decide_kind_is_replicaset kind:
  kind = "ReplicaSet"%go →
    bool_decide (kind = "ReplicaSet"%go) = true ∧
    bool_decide (kind = "Pod"%go) = false.
Proof.
  intros Hkind.
  split.
  - apply bool_decide_true; exact Hkind.
  - apply bool_decide_false. intros Hcontra. rewrite Hcontra in Hkind. done.
Qed.


Lemma wp_deepCopy_replicaset (obj: interface.t) (ptr: loc) (rs: v1.ReplicaSet.t):
  {{{ is_pkg_init apimodel ∗
      "%interface_is_rs_ptr" ∷ ⌜ obj = interface.mk (ptrT.id v1.ReplicaSet.id) #ptr ⌝ ∗
      "rs_ptr" ∷ ptr ↦ rs
  }}}
    @! apimodel.deepCopy #obj
  {{{ (obj': interface.t) (ptr': loc) (rs': v1.ReplicaSet.t), RET #obj';
    ⌜ obj' = interface.mk (ptrT.id v1.ReplicaSet.id) #ptr' ⌝ ∗
    ptr' ↦ rs' ∗
    is_deepcopy_replicaset rs rs' ∗
    ptr ↦ rs
  }}}.
Proof.
Admitted.

Lemma wp_objGet (key: KKey.t) γ_state γ_children γ_fresh_keys:
  {{{ is_pkg_init apimodel ∗
      "#inv" ∷ is_kubernetes_state γ_state γ_children γ_fresh_keys
  }}}
    @! apimodel.objGet #key
  {{{ (obj: interface.t) (exists': bool), RET (#obj, #exists');
    True
  }}}.
Proof.
  wp_start as "H". iNamed "H".
  wp_apply wp_with_defer. simpl subst.
  iIntros (defer) "defer". wp_auto. iRename "key" into "key_ptr".
  wp_apply wp_globals_get.
  wp_apply wp_Mutex__Lock.
  { done. }
  iIntros "[own_Mutex H]". iNamed "H". wp_auto.
  wp_apply wp_globals_get. wp_apply wp_globals_get.
  wp_apply (wp_map_get with "[$own_phys]").
  iIntros "own_phys". wp_auto.
  (* wp_apply (wp_Mutex__Unlock _ (is_kubernetes_state_inner γ_state γ_children γ_fresh_keys)
    with "[$own_Mutex state_m_addr own_phys own_abs phys_abs_rep own_children own_fresh_keys]").
  { iFrame. done. }
  iApply ("HΦ" $! (default interface.nil (phys_state !! key))
                 (bool_decide (is_Some (phys_state !! key)))).
  done. *)
Admitted.


Lemma wp_PodGet (namespace name: go_string) γ_state γ_children γ_fresh_keys:
  {{{ is_pkg_init apimodel ∗
      is_kubernetes_state γ_state γ_children γ_fresh_keys
  }}}
    @! apimodel.PodGet #namespace #name
  {{{ (l: loc) (err: error.t) dq2 (pod: v1.Pod.t), RET (#l, #err);
    if decide (err = interface.nil) then
      l ↦{dq2} pod
    else
      True
  }}}.
Proof.
Admitted.


Lemma wp_podControllerUIDIndex_with_controller_parent obj ptr pod:
  {{{ is_pkg_init apimodel ∗
      "%obj_is_ptr" ∷ ⌜ obj = interface.mk (ptrT.id v1.ReplicaSet.id) #ptr ⌝ ∗
      "ptr" ∷ ptr ↦ pod
  }}}
    @! apimodel.podControllerUIDIndex #obj
  {{{ indexes (err: error.t) vs index, RET (#indexes, #err);
    ⌜ err = interface.nil ⌝ ∗
    indexes ↦* vs ∗
    ⌜ vs = [index] ⌝ ∗
    index_is_pod_controller_uid_index pod index
  }}}.
Proof.
Admitted.

Lemma wp_objList_pod_ptsto_mut kind namespace γ_state γ_children γ_fresh_keys owned_pod_map:
  {{{ is_pkg_init apimodel ∗
      "#inv" ∷ is_kubernetes_state γ_state γ_children γ_fresh_keys ∗
      "own_pods" ∷ ([∗ map] key ↦ pod ∈ owned_pod_map, key [[ γ_state ]]↦ KObject.Pod pod) ∗
      "%kind" ∷ ⌜ kind = "Pod"%go ⌝
  }}}
  @! apimodel.objList #kind #namespace
  {{{ (l: slice.t) (objs: list interface.t) (pods: list v1.Pod.t), RET #l;
    l ↦* objs ∗
    ⌜ NoDup (map extract_pod_key pods) ⌝ ∗
    ([∗ list] obj ; pod ∈ objs ; pods, ∃ (ptr : loc),
      ⌜ obj = interface.mk (ptrT.id v1.ReplicaSet.id) #ptr ⌝ ∗
      ptr ↦ pod ∗
      pod_well_formed pod ∗
      ⌜ namespace = ""%go ∨ pod.(v1.Pod.ObjectMeta').(v1.ObjectMeta.Namespace') = namespace ⌝
    ) ∗
    ([∗ map] key ↦ owned_pod ∈ owned_pod_map,
      if bool_decide (namespace = ""%go ∨ key.(KKey.Namespace') = namespace)
      then ∃ pod, ⌜ pod ∈ pods ⌝ ∗ is_deepcopy_pod owned_pod pod
      else ∀ pod, ⌜ pod ∈ pods → key ≠ extract_pod_key pod ⌝
    ) ∗
    ([∗ map] key ↦ pod ∈ owned_pod_map, key [[ γ_state ]]↦ KObject.Pod pod)
  }}}.
Proof.
Admitted.


Lemma wp_objGet_replicaset_ptsto_mut key γ_state γ_children γ_fresh_keys owned_rs:
  {{{ is_pkg_init apimodel ∗
      "#inv" ∷ is_kubernetes_state γ_state γ_children γ_fresh_keys ∗
      "own_rs" ∷ key [[ γ_state ]]↦ (KObject.ReplicaSet owned_rs) ∗
      "%kind" ∷ ⌜ KKey.Kind' key = "ReplicaSet"%go ⌝
  }}}
    @! apimodel.objGet #key
  {{{ obj exists' rs, RET (#obj, #exists');
    ⌜ exists' = true ⌝ ∗
    (∃ (ptr : loc),
        ⌜ obj = interface.mk (ptrT.id v1.ReplicaSet.id) #ptr ⌝ ∗
        ptr ↦ rs
    ) ∗
    is_deepcopy_replicaset owned_rs rs ∗
    replicaset_nn_well_formed rs (KKey.Namespace' key) (KKey.Name' key) ∗
    key [[ γ_state ]]↦ (KObject.ReplicaSet owned_rs)
  }}}.
Proof.
  wp_start as "H". iNamed "H".
  wp_apply wp_with_defer.
  iIntros (defer) "defer". simpl subst. wp_auto. iRename "key" into "key_ptr".
  wp_apply wp_globals_get.
  wp_apply wp_Mutex__Lock.
  { done. }
  iIntros "[own_Mutex H]". iNamed "H". wp_auto.
  wp_apply wp_globals_get. wp_apply wp_globals_get.
  iAssert (⌜ abs_state !! key = Some (KObject.ReplicaSet owned_rs) ⌝%I) with "[own_rs own_abs]" as "%key_in_abs".
  { 
    iDestruct (map_valid with "own_abs own_rs") as %Hlookup.
    iPureIntro; exact Hlookup.
  }
  iAssert (⌜ ∃ obj, phys_state !! key = Some obj ⌝%I) with "[phys_abs_rep]" as "%key_in_phys".
  {
    iDestruct (big_sepM2_lookup_r with "phys_abs_rep") as (obj key_in_phys) "_".
    { exact key_in_abs. }
    iPureIntro. exists obj. exact key_in_phys.
  }
  destruct key_in_phys as [obj key_in_phys].
  iDestruct (big_sepM2_lookup_acc _ _ _ _ _ _ key_in_phys key_in_abs with "phys_abs_rep") as "[k_rep other_rep]".
  destruct decide_kind_is_replicaset with (KKey.Kind' key) as [kind_is_replicaset kind_is_not_pod].
  { done. }
  rewrite kind_is_replicaset kind_is_not_pod.
  iDestruct "k_rep" as "(%ptr & %rs0 & rs_rep)". iNamed "rs_rep".
  inversion abs_v_is_rs as [Heq]. symmetry in Heq. subst. clear abs_v_is_rs.
  wp_apply (wp_map_get with "[$own_phys]"). iIntros "own_phys". wp_auto.
  rewrite /is_Some key_in_phys. wp_auto.
  wp_apply (wp_deepCopy_replicaset with "[$rs_ptr]").
  { iPureIntro. reflexivity. }
  iIntros (obj' ptr' rs') "(%obj'_is_ptr & ptr' & rs'_is_deepcopy_of_rs & rs_ptr)".
  iAssert (replicaset_nn_well_formed rs' (KKey.Namespace' key) (KKey.Name' key)%I) with "[rs'_is_deepcopy_of_rs]" as "%rs'_well_formed".
  {
    iApply (well_formed_preserved_by_deepcopy_replicaset with "[$rs'_is_deepcopy_of_rs]").
    iPureIntro. done.
  }
  wp_auto.
  iAssert (state_rep phys_state abs_state %I) with "[rs_ptr other_rep]" as "phys_abs_rep".
  { iApply "other_rep". iExists ptr, owned_rs. iFrame. done. }
  wp_apply (wp_Mutex__Unlock _ (is_kubernetes_state_inner γ_state γ_children γ_fresh_keys)
  with "[$own_Mutex state_m_addr own_phys own_abs phys_abs_rep own_children own_fresh_keys]").
  { iFrame. done. }
  iApply ("HΦ" $! obj' true).
  iSplitR.
  { iPureIntro. done. }
  iFrame.
  iPureIntro. done.
Qed.

Lemma wp_ReplicaSetMutGet_ptsto_mut namespace name γ_state γ_children γ_fresh_keys owned_rs:
  {{{ is_pkg_init apimodel ∗
      "#inv" ∷ is_kubernetes_state γ_state γ_children γ_fresh_keys ∗
      "own_rs" ∷ (mk_replicaset_key namespace name) [[ γ_state ]]↦ (KObject.ReplicaSet owned_rs)
  }}}
    @! apimodel.ReplicaSetMutGet #namespace #name
  {{{ l (err: error.t) rs, RET (#l, #err);
    ⌜ err = interface.nil ⌝ ∗
    (mk_replicaset_key namespace name) [[ γ_state ]]↦ (KObject.ReplicaSet owned_rs) ∗
    l ↦ rs ∗
    is_deepcopy_replicaset owned_rs rs ∗
    replicaset_nn_well_formed rs namespace name
  }}}.
Proof.
  wp_start as "H". iNamed "H". wp_auto.
  wp_apply (wp_objGet_replicaset_ptsto_mut with "[$own_rs]").
  { iFrame "#". done. }
  iIntros (obj exists' rs') "(%exists'_is_true & (%ptr & %obj_is_ptr & ptr) & deepcopy & %well_formed & own_rs)".
  subst exists' obj.
  wp_auto.
  unshelve wp_apply wp_interface_checked_type_assert; try tc_solve.
  { iPureIntro. intros ptr_id. exists ptr. done. }
  iIntros (y ok) "%if_ok".
  assert (ok = true) as ok_is_true.
  { destruct ok; [done|]. intuition. }
  subst ok. inversion if_ok.
  assert (ptr = y) as ptr_is_y.
  { apply (inj to_val). done. }
  subst ptr.
  wp_auto.
  iApply "HΦ".
  iFrame. iPureIntro. done.
Qed.


Lemma wp_ReplicaSetGet_ptsto_mut namespace name γ_state γ_children γ_fresh_keys owned_rs:
  {{{ is_pkg_init apimodel ∗
      "#inv" ∷ is_kubernetes_state γ_state γ_children γ_fresh_keys ∗
      "own_rs" ∷ (mk_replicaset_key namespace name) [[ γ_state ]]↦ (KObject.ReplicaSet owned_rs)
  }}}
    @! apimodel.ReplicaSetGet #namespace #name
  {{{ l (err: error.t) rs dq, RET (#l, #err);
    ⌜ err = interface.nil ⌝ ∗
    (mk_replicaset_key namespace name) [[ γ_state ]]↦ (KObject.ReplicaSet owned_rs) ∗
    l ↦{dq} rs ∗
    is_deepcopy_replicaset owned_rs rs ∗
    replicaset_nn_well_formed owned_rs namespace name
  }}}.
Proof.
  wp_start as "H". iNamed "H". wp_auto.
  wp_apply (wp_ReplicaSetMutGet_ptsto_mut with "[$own_rs]").
  { done. }
  iIntros (l err rs') "(%err_is_nil & own_rs & l & deepcopy & %well_formed)".
  wp_auto.
  iApply "HΦ". iFrame. done.
Qed.

End proof.
