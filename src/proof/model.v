From Perennial.algebra Require Export auth_map.
From New.proof.github_com.goose_lang.goose.model.channel Require Export auth_set.
Require Import New.proof.sync.
From proof.k8s_io.api.core Require Export v1_init.
From proof.k8s_io.api.apps Require Import v1_init.

Module KKind.
  Inductive t :=
  | Pod
  | ReplicaSet.

  Definition encode (k : t) : nat :=
    match k with
    | Pod => 0
    | ReplicaSet => 1
    end.

  Definition decode (n : nat) : t :=
    match n with
    | 0%nat => Pod
    | _ => ReplicaSet
    end.

  Lemma decode_encode k : decode (encode k) = k.
  Proof. destruct k; reflexivity. Qed.

  Global Instance eq_dec : EqDecision t.
  Proof. solve_decision. Qed.

  Global Instance countable : Countable t.
  Proof.
    refine (inj_countable' encode decode _).
    intros []; apply decode_encode.
  Qed.
End KKind.

Module KObject.
  Inductive t :=
  | Pod (p : v1.Pod.t)
  | ReplicaSet (rs : v1.ReplicaSet.t).
End KObject.

Module KKey.
  Record t := mk {
    kind : KKind.t;
    namespace : go_string;
    name : go_string
  }.

  Global Instance eq_dec : EqDecision t.
  Proof. solve_decision. Qed.

  Global Instance countable : Countable t.
  Proof.
    refine (inj_countable'
              (fun k => (kind k, namespace k, name k))
              (fun '(k, ns, n) => mk  k ns n)
              _).
    intros []; reflexivity.
  Qed.
End KKey.

Global Existing Instance KKey.eq_dec.
Global Existing Instance KKey.countable.

Section model.

Context `{!mapG Σ KKey.t KObject.t}.
Context `{!mapG Σ KKey.t (gset KKey.t)}.
Context `{!auth_setG Σ KKey.t}.
Context `{heapGS Σ, !ffi_semantics _ _}.

Definition foo γ (m : gmap KKey.t KObject.t) k v : iProp Σ :=
  map_ctx γ 1 m ∗ k [[ γ ]]↦ v.

Definition bar γ (m : gmap KKey.t (gset KKey.t)) k v : iProp Σ :=
  map_ctx γ 1 m ∗ k [[ γ ]]↦ v.

Definition baz γ (s : gset KKey.t) (v : KKey.t) : iProp Σ :=
  auth_set_auth γ s ∗ auth_set_frag γ v.

Axiom kubernetes_state_well_formed : gmap KKey.t KObject.t → Prop.

Axiom kubernetes_state_consistent : gmap KKey.t KObject.t → gmap KKey.t (gset KKey.t) → gset KKey.t → Prop.

Definition kubernetes_inv γ_state γ_children γ_fresh_keys : iProp Σ :=
  ∃ (m_state : gmap KKey.t KObject.t) (m_children : gmap KKey.t (gset KKey.t)) (s_fresh_keys : gset KKey.t),
    "Hstate" ∷ map_ctx γ_state 1 m_state ∗
    "Hchildren" ∷ map_ctx γ_children 1 m_children ∗
    "Hfreshkeys" ∷ auth_set_auth γ_fresh_keys s_fresh_keys ∗
    "%Hwellformed" ∷ ⌜ kubernetes_state_well_formed m_state ⌝ ∗
    "%Hconsistent" ∷ ⌜ kubernetes_state_consistent m_state m_children s_fresh_keys ⌝.

Definition is_kubernetes γ_state γ_children γ_fresh_keys : iProp Σ :=
  ∃ l, "#Hkinv" ∷ is_Mutex l (kubernetes_inv γ_state γ_children γ_fresh_keys).

Global Instance is_kubernetes_persistent γ_state γ_children γ_fresh_keys : Persistent (is_kubernetes γ_state γ_children γ_fresh_keys).
Proof. apply _. Qed.

End model.
