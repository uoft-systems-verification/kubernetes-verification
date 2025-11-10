From Perennial.algebra Require Export auth_map.
From New.proof.github_com.goose_lang.goose.model.channel Require Export auth_set.
Require Export New.proof.sync.

From verification.kubernetes_model Require Export simpleapiserver_init.
From verification Require Import prelude empty_ffi.
Export simpleapiserver.simpleapiserver.

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


Definition pod_well_formed (pod: v1.Pod.t) (namespace name: go_string) : Prop :=
 True.


Definition replicaset_well_formed (rs: v1.ReplicaSet.t) (namespace name: go_string) : Prop :=
 True.


Definition state_rep (phys_state: gmap KKey.t interface.t) (abs_state: gmap KKey.t KObject.t) : iProp Σ :=
  [∗ map] k ↦ v1; v2 ∈ phys_state; abs_state,
    if bool_decide (KKey.Kind' k = "Pod"%go) then
      ∃ (ptr : loc) (pod : v1.Pod.t),
        ⌜ v1 = interface.mk (ptrT.id v1.Pod.id) #ptr ⌝ ∗
        ptr ↦ pod ∗
        ⌜ v2 = KObject.Pod pod ⌝ ∗
        ⌜ pod_well_formed pod (KKey.Namespace' k) (KKey.Name' k) ⌝
    else if bool_decide (KKey.Kind' k = "ReplicaSet"%go) then
      ∃ (ptr : loc) (rs : v1.ReplicaSet.t),
        ⌜ v1 = interface.mk (ptrT.id v1.ReplicaSet.id) #ptr ⌝ ∗
        ptr ↦ rs ∗
        ⌜ v2 = KObject.ReplicaSet rs ⌝ ∗
        ⌜ replicaset_well_formed rs (KKey.Namespace' k) (KKey.Name' k) ⌝
    else False%I.


Definition kubernetes_state_consistent (abs_state: gmap KKey.t KObject.t) (children: gmap KKey.t (gset KKey.t)) (fresh_keys: gset KKey.t): Prop := 
  True.


Definition is_kubernetes_state_inner γ_state γ_children γ_fresh_keys: iProp Σ :=
  ∃ (l: loc) (phys_state: gmap KKey.t interface.t) (abs_state: gmap KKey.t KObject.t) (children: gmap KKey.t (gset KKey.t)) (fresh_keys: gset KKey.t),
    "state_m_addr" ∷ (global_addr simpleapiserver.state) ↦s[ simpleapiserver.State :: "m" ] l ∗
    "own_phys" ∷ l ↦$ phys_state ∗
    "own_abs" ∷ map_ctx γ_state 1 abs_state ∗
    "phys_abs_rep" ∷ state_rep phys_state abs_state ∗
    "own_children" ∷ map_ctx γ_children 1 children ∗
    "own_fresh_keys" ∷ auth_set_auth γ_fresh_keys fresh_keys ∗
    "consistent" ∷ ⌜ kubernetes_state_consistent abs_state children fresh_keys ⌝ .


Definition is_kubernetes_state γ_state γ_children γ_fresh_keys : iProp Σ :=
  is_Mutex (global_addr simpleapiserver.stateMu) (is_kubernetes_state_inner γ_state γ_children γ_fresh_keys).

Lemma wp_objGet (key: KKey.t) γ_state γ_children γ_fresh_keys:
  {{{ is_pkg_init simpleapiserver ∗
      "#inv" ∷ is_kubernetes_state γ_state γ_children γ_fresh_keys
  }}}
    @! simpleapiserver.objGet #key
  {{{ (obj: interface.t) (exists': bool), RET (#obj, #exists');
    True
  }}}.
Proof.
  wp_start as "H". iNamed "H".
  wp_apply wp_with_defer. simpl subst.
  iIntros (defer) "defer". wp_auto. iRename "key" into "kep_ptr".
  wp_apply wp_globals_get.
  wp_apply wp_Mutex__Lock.
  { done. }
  iIntros "[own_Mutex H]". iNamed "H". wp_auto.
  wp_apply wp_globals_get. wp_apply wp_globals_get.
  wp_apply (wp_map_get with "[$own_phys]").
  iIntros "own_phys". wp_auto.
  wp_apply (wp_Mutex__Unlock _ (is_kubernetes_state_inner γ_state γ_children γ_fresh_keys)
    with "[$own_Mutex state_m_addr own_phys own_abs phys_abs_rep own_children own_fresh_keys consistent]").
  { iFrame. done. }
  iApply ("HΦ" $! (default interface.nil (phys_state !! key))
                 (bool_decide (is_Some (phys_state !! key)))).
  done.
Qed.


Lemma wp_PodGet (namespace name: go_string) γ_state γ_children γ_fresh_keys:
  {{{ is_pkg_init simpleapiserver ∗
      is_kubernetes_state γ_state γ_children γ_fresh_keys
  }}}
    @! simpleapiserver.PodGet #namespace #name
  {{{ (l: loc) (err: error.t) dq2 (pod: v1.Pod.t), RET (#l, #err);
    if decide (err = interface.nil) then
      l ↦{dq2} pod
    else
      True
  }}}.
  wp_start as "H". iNamed "H".
Admitted.


Lemma wp_PodGet_with_ptsto_mut_state (namespace name: go_string) γ_state γ_children γ_fresh_keys dq pod:
  {{{ is_pkg_init simpleapiserver ∗
      is_kubernetes_state γ_state γ_children γ_fresh_keys ∗
      ptsto_mut γ_state (mk_pod_key namespace name) dq (KObject.Pod pod)
  }}}
    @! simpleapiserver.PodGet #namespace #name
  {{{ (l: loc) (err: error.t) dq2, RET (#l, #err);
    ⌜ err = interface.nil ⌝ ∗
    l ↦{dq2} pod ∗
    ptsto_mut γ_state (mk_pod_key namespace name) dq (KObject.Pod pod)
  }}}.
Admitted.


(* Lemma wp_PodList_with_ptsto_mut_children (namespace: go_string) (l: loc) γ_state γ_fresh_keys dq pods:
  {{{ is_pkg_init simpleapiserver ∗
      is_kubernetes_state l γ_state γ_fresh_keys ∗

  }}} *)

End proof.
