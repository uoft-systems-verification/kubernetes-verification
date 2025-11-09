From Perennial.algebra Require Export auth_map.
From New.proof.github_com.goose_lang.goose.model.channel Require Export auth_set.
Require Import New.proof.sync.
From New.generatedproof.kubernetes_model Require Export simpleapiserver.
From verification.kubernetes_model Require Export simpleapiserver_init.
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

Section model.
Context `{heapGS Σ, !ffi_semantics _ _}.
Context `{!mapG Σ KKey.t interface.t}.
Context `{!mapG Σ KKey.t KObject.t}.
Context `{!auth_setG Σ KKey.t}.

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


Definition is_kubernetes_state_inner (l: loc) γ_state γ_fresh_keys: iProp Σ :=
  ∃ (phys_state: gmap KKey.t interface.t) (abs_state: gmap KKey.t KObject.t) (s_fresh_keys: gset KKey.t),
    "Hphys" ∷ l ↦$ phys_state ∗
    "Habs" ∷ map_ctx γ_state 1 abs_state ∗
    "Hrep" ∷ state_rep phys_state abs_state ∗
    "Hfreshkeys" ∷ auth_set_auth γ_fresh_keys s_fresh_keys.


Definition is_kubernetes_state (l: loc) γ_state γ_fresh_keys : iProp Σ :=
  ∃ mu_l, "#Hkinv" ∷ is_Mutex mu_l (is_kubernetes_state_inner l γ_state γ_fresh_keys).

End model.
