From New.proof Require Import prelude empty_ffi.
From New.proof Require Export pure_objects.
From New.proof.algebra Require Export mono_gmap.

Section snapshot.

Definition key : Type := ((KKey.t * types.UID.t) * go_string)%type.
Definition object : Type := KObjectV.t.

#[global]
Instance key_eq_dec : EqDecision key.
Proof. solve_decision. Qed.

#[global]
Instance key_countable : Countable key.
Proof.
  refine (inj_countable'
            (λ '((k, uid), rv), (KKey.Kind' k,
                                 KKey.Name' k,
                                 KKey.Namespace' k,
                                 uid,
                                 rv))
            (λ '(kind, name, namespace, uid, rv),
              ((KKey.mk kind name namespace, uid), rv))
            _).
  intros [[[] uid] rv]; reflexivity.
Qed.

Definition snapshotUR : ucmra := mono_gmapUR key object.

Class snapshotG Σ :=
  { #[global] snapshot_mono_gmapG :: mono_gmapG key object Σ; }.

Definition snapshotΣ :=
  mono_gmapΣ key object.

#[global]
Instance subG_snapshotG Σ :
  subG snapshotΣ Σ → snapshotG Σ.
Proof.
  intros Hsub.
  constructor.
  exact (subG_mono_gmapG key object Σ Hsub).
Qed.

Context `{!snapshotG Σ}.

Definition own_auth γ (snapshots : gmap key object) : iProp Σ :=
  mono_gmap.own_auth key object γ snapshots.

Definition own_frag γ (k : key) (obj : object) : iProp Σ :=
  mono_gmap.own_frag key object γ k obj.

Global Instance own_auth_timeless γ snapshots :
  Timeless (own_auth γ snapshots).
Proof. unfold own_auth. apply _. Qed.

Global Instance own_frag_timeless γ k obj :
  Timeless (own_frag γ k obj).
Proof. unfold own_frag. apply _. Qed.

Global Instance own_frag_persistent γ k obj :
  Persistent (own_frag γ k obj).
Proof. unfold own_frag. apply _. Qed.

Lemma alloc snapshots:
  ⊢ |==> ∃ γ, own_auth γ snapshots.
Proof.
  unfold own_auth.
  apply (mono_gmap.alloc key object snapshots).
Qed.

Lemma frag_elem_of_auth {γ snapshots k obj}:
  own_auth γ snapshots -∗ own_frag γ k obj -∗ ⌜ snapshots !! k = Some obj ⌝.
Proof.
  unfold own_auth, own_frag.
  apply (mono_gmap.frag_elem_of_auth key object).
Qed.

Lemma frag_agree {γ k obj1 obj2}:
  own_frag γ k obj1 -∗ own_frag γ k obj2 -∗ ⌜ obj1 = obj2 ⌝.
Proof.
  unfold own_frag.
  apply (mono_gmap.frag_agree key object).
Qed.

Lemma insert_vs {γ snapshots} k obj:
  snapshots !! k = None →
  own_auth γ snapshots ==∗ own_auth γ (<[k := obj]> snapshots) ∗ own_frag γ k obj.
Proof.
  unfold own_auth, own_frag.
  apply (mono_gmap.insert_vs key object k obj).
Qed.

Lemma lookup_vs {γ snapshots} k obj:
  snapshots !! k = Some obj →
  own_auth γ snapshots ==∗ own_auth γ snapshots ∗ own_frag γ k obj.
Proof.
  unfold own_auth, own_frag.
  apply (mono_gmap.lookup_vs key object k obj).
Qed.

End snapshot.
