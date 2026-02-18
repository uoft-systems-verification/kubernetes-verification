From New.proof Require Import prelude.
From iris.algebra Require Import cmra gset.

(*
  cview describes reversed reference using Iris' view resource algebra.
  
  The auth is a map from key (K) to value (V), where each value has at most one
  reference (R) pointing to another key in the map. We say the reference is from
  a child to its parent.

  The frag is a map from reference to set of keys. For each reference, the set of
  keys give us exactly the set of values in the auth that shares this reference.
  The frag gives us the reversed reference: from the parent to all its children.

  Function f abstracts how to retrieve the reference from the value. Function g
  abstracts how to convert the key and value into a reference that other values
  might point to. In some simple cases where R equals K, g just returns the key and
  ignores the value.

  One usage of this resource algebra is to describe the parent reference (or owner
  reference) mechanism in Kubernetes, where each object has at most one controller
  owner. We often need to reason about the state of all children objects of a given
  parent object, which is described by the frag. In this case, K is KKey.t, V is the
  KObjectV.t, R is the product of KKey.t and UID.t, f returns the (only) controller
  owner if it exists, and g returns the product of key and uid.
*)

Section cview.
Context (K : Type) `{Countable K} (R : Type) `{Countable R} (V : Type).
Context (f : V → option R) (g : K → V → R).

Definition authO : ofe :=
  gmapO K (leibnizO V).

Definition fragUR : ucmra :=
  gmapUR R (prodR dfracR (agreeR (gset K))).

Implicit Types (a : authO) (b : fragUR).
Implicit Types (k : K) (r : R) (v : V) (n : nat).

Local Definition view_rel_raw n a b :=
  (* dfracs are valid *)
  (map_Forall (λ _ '(dq, _), ✓ dq) b) ∧
  (* for each (r, ks) in b, ks is exactly the set of children of r in a *)
  (map_Forall (λ r '(_, agree_ks),
    ∃ ks, agree_ks = to_agree ks ∧ ks = dom (filter (λ '(_, v), f v = Some r) a)) b) ∧
  (* different (k, v) have different r *)
  (map_Forall (λ k1 v1, map_Forall (λ k2 v2, k1 ≠ k2 → g k1 v1 ≠ g k2 v2) a) a) ∧
  (* each r in a has an entry in b *)
  (map_Forall (λ k v, ∃ da, b !! (g k v) = Some da) a) ∧
  (* no self-parenting *)
  (map_Forall (λ r '(_, agree_ks),
    ∃ ks, agree_ks = to_agree ks ∧ set_Forall (λ k, ∀ v, a !! k = Some v → g k v ≠ r) ks) b).

Local Axiom view_rel_raw_mono :
  ∀ n1 n2 a1 a2 b1 b2,
  view_rel_raw n1 a1 b1 →
  a1 ≡{n2}≡ a2 →
  b2 ≼{n2} b1 →
  (n2 ≤ n1)%nat →
  view_rel_raw n2 a2 b2.

Local Axiom view_rel_raw_valid :
  ∀ n a b, view_rel_raw n a b → ✓{n} b.

Local Axiom view_rel_raw_unit :
  ∀ n, ∃ a, view_rel_raw n a ε.

Local Canonical Structure view_rel :
    view_rel authO fragUR :=
  ViewRel view_rel_raw view_rel_raw_mono
          view_rel_raw_valid view_rel_raw_unit.

Definition cview_auth dq a : viewR view_rel := ●V{dq} a.
Definition cview_frag b : viewR view_rel := ◯V b.
Definition mk_frag (p: R) (dq: dfrac) (ks: gset K) : fragUR :=
  {[p := (dq, to_agree ks)]}.
Notation "●C a" := (cview_auth 1 a) (at level 20).
Notation "◯C b" := (cview_frag b) (at level 20).

Lemma auth_frag_valid a r dq ks:
✓ (●C a ⋅ ◯C (mk_frag r dq ks)) →
ks = dom (filter (λ kv, f kv.2 = Some r) a) ∧
∀ k v, k ∈ ks → a !! k = Some v → g k v ≠ r.
Proof. Admitted.

Lemma create_child a k v r ks:
a !! k = None →
f v = Some r →
g k v ≠ r →
(●C a ⋅ ◯C (mk_frag r 1 ks)) ~~>
  (●C (<[k := v]> a) ⋅ ◯C (mk_frag r 1 (ks ∪ {[k]})) ⋅ ◯C (mk_frag (g k v) 1 ∅)).
Proof. Admitted.

Lemma adopt_orphan a k v r ks v':
a !! k = Some v →
f v = None →
f v' = Some r →
g k v' ≠ r →
(●C a ⋅ ◯C (mk_frag r 1 ks)) ~~>
  (●C (<[k := v']> a) ⋅ ◯C (mk_frag r 1 (ks ∪ {[k]}))).
Proof. Admitted.

Lemma release_child a k v r ks v':
a !! k = Some v →
f v = Some r →
f v' = None →
k ∈ ks →
(●C a ⋅ ◯C (mk_frag r 1 ks)) ~~>
  (●C (<[k := v']> a) ⋅ ◯C (mk_frag r 1 (ks ∖ {[k]}))).
Proof. Admitted.

Lemma delete_child a k r ks:
k ∈ ks →
(●C a ⋅ ◯C (mk_frag r 1 ks)) ~~>
  (●C (delete k a) ⋅ ◯C (mk_frag r 1 (ks ∖ {[k]}))).
Proof. Admitted.

Lemma simple_update a k v v':
a !! k = Some v →
f v = f v' →
●C a ~~> ●C (<[k := v']> a).
Proof. Admitted.

Lemma create_orphan a k v:
a !! k = None →
f v = None →
●C a ~~> ●C (<[k := v]> a).
Proof. Admitted.

Lemma delete_orphan a k v:
a !! k = Some v →
f v = None →
●C a ~~> ●C (delete k a).
Proof. Admitted.

Class cviewG Σ :=
  { #[global] cview_inG :: inG Σ (viewR view_rel); }.

Definition cviewΣ :=
  #[GFunctor (viewR view_rel)].

#[global]
Instance subG_cviewG Σ :
  subG cviewΣ Σ → cviewG Σ.
Proof. solve_inG. Qed.

Context `{!cviewG Σ}.

Definition own_auth γ (state: gmap K V) : iProp Σ :=
  own γ (●C state).

Global Instance own_auth_discretizable γ state : Discretizable (own_auth γ state).
Proof. apply _. Qed.

Definition own_frag γ r dq ks : iProp Σ :=
  own γ (◯C (mk_frag r dq ks)).

Global Instance own_frag_timeless γ r dq ks : Timeless (own_frag γ r dq ks).
Proof. apply _. Qed.

Global Instance own_frag_discretizable γ r dq ks : Discretizable (own_frag γ r dq ks).
Proof. apply _. Qed.

Lemma create_child_vs {γ state r ks} k v:
state !! k = None →
f v = Some r →
g k v ≠ r →
own_auth γ state ∗ own_frag γ r 1 ks ==∗
  own_auth γ (<[k := v]> state) ∗
  own_frag γ r 1 (ks ∪ {[k]}) ∗
  own_frag γ (g k v) 1 ∅.
Proof. Admitted.

Lemma adopt_orphan_vs {γ state r ks} k v v':
state !! k = Some v →
f v = None →
f v' = Some r →
g k v' ≠ r →
own_auth γ state ∗ own_frag γ r 1 ks ==∗
  own_auth γ (<[k := v']> state) ∗ own_frag γ r 1 (ks ∪ {[k]}).
Proof. Admitted.

Lemma release_child_vs {γ state r ks} k v v':
state !! k = Some v →
f v = Some r →
f v' = None →
k ∈ ks →
own_auth γ state ∗ own_frag γ r 1 ks ==∗
  own_auth γ (<[k := v']> state) ∗ own_frag γ r 1 (ks ∖ {[k]}).
Proof. Admitted.

Lemma delete_child_vs {γ state r ks} k:
k ∈ ks →
own_auth γ state ∗ own_frag γ r 1 ks ==∗
  own_auth γ (delete k state) ∗ own_frag γ r 1 (ks ∖ {[k]}).
Proof. Admitted.

Lemma simple_update_vs {γ state} k v v':
state !! k = Some v →
f v = f v' →
own_auth γ state ==∗ own_auth γ (<[k := v']> state).
Proof. Admitted.

Lemma create_orphan_vs {γ state} k v:
state !! k = None →
f v = None →
own_auth γ state ==∗ own_auth γ (<[k := v]> state).
Proof. Admitted.

Lemma delete_orphan_vs {γ state} k v:
state !! k = Some v →
f v = None →
own_auth γ state ==∗ own_auth γ (delete k state).
Proof. Admitted.

End cview.

(* Definition meta_is_child_of meta key uid: Prop :=
  meta.(ObjectMetaV.Namespace') = key.(KKey.Namespace') ∧
  match meta.(ObjectMetaV.OwnerReferences') with
  | Some os => os_has_controller_parent_of os key.(KKey.Kind') key.(KKey.Name') uid
  | None => False
  end. *)

(* Definition meta_is_orphan meta: Prop := ∀ k uid, ¬ meta_is_child_of meta k uid. *)
