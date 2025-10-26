From Perennial.algebra Require Import auth_map.
From New.proof.github_com.goose_lang.goose.model.channel Require Import auth_set.
Require Import New.proof.sync.
From verification Require Import replicaset_init.

Module KKey.
  Record t := mk {
    kind : go_string;
    namespace : go_string;
    name : go_string
  }.

  Global Instance eq_dec : EqDecision t.
  Proof. solve_decision. Qed.

  Global Instance countable : Countable t.
  Proof.
    refine (inj_countable'
              (fun k => (kind k, namespace k, name k))
              (fun '(k, ns, n) => mk k ns n)
              _).
    intros []; reflexivity.
  Qed.
End KKey.

Global Existing Instance KKey.eq_dec.
Global Existing Instance KKey.countable.

Section model.

Context `{!mapG Σ KKey.t v1.Pod.t}.
Context `{!mapG Σ KKey.t (gset KKey.t)}.
Context `{!auth_setG Σ KKey.t}.
Context `{heapGS Σ, !ffi_semantics _ _}.

Definition foo γ (m : gmap KKey.t v1.Pod.t) k v : iProp Σ :=
  map_ctx γ 1 m ∗ k [[ γ ]]↦ v.

Definition bar γ (m : gmap KKey.t (gset KKey.t)) k v : iProp Σ :=
  map_ctx γ 1 m ∗ k [[ γ ]]↦ v.

Definition baz γ (s : gset KKey.t) (v : KKey.t) : iProp Σ :=
  auth_set_auth γ s ∗ auth_set_frag γ v.

Axiom state_well_formed : gmap KKey.t v1.Pod.t → Prop.

Axiom state_and_children_consistent : gmap KKey.t v1.Pod.t → gmap KKey.t (gset KKey.t) → Prop.

Axiom state_and_fresh_keys_consistent : gmap KKey.t v1.Pod.t → gset KKey.t → Prop.

Definition is_kubernetes_state_inner γ : iProp Σ :=
  ∃ (m_state : gmap KKey.t v1.Pod.t) (m_children : gmap KKey.t (gset KKey.t)) (s_fresh_keys : gset KKey.t),
    map_ctx γ 1 m_state ∗
    map_ctx γ 1 m_children ∗
    auth_set_auth γ s_fresh_keys ∗
    ⌜ state_well_formed m_state ∧
      state_and_children_consistent m_state m_children ∧
      state_and_fresh_keys_consistent m_state s_fresh_keys ⌝.

Definition is_kubernetes_state γ : iProp Σ :=
  ∃ l, is_Mutex l (is_kubernetes_state_inner γ).

Global Instance is_kubernetes_state_persistent γ : Persistent (is_kubernetes_state γ).
Proof. apply _. Qed.

End model.
