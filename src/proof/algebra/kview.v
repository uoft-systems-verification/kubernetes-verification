From New.proof Require Import prelude.
From New.proof Require Export pure_objects.
From New.proof.k8s_io.apimachinery.pkg.apis.meta Require Export v1_init.
From iris.algebra Require Import cmra gset.


Section kview.

Definition authO : ofe := prodO (gmapO KKey.t (leibnizO KObjectV.t)) (gsetO (leibnizO types.UID.t)).

Definition metaUR : ucmra := gmapUR (KKey.t * types.UID.t) (prodR dfracR (agreeR (leibnizO ObjectMetaV.t))).
Definition specUR : ucmra := gmapUR (KKey.t * types.UID.t) (prodR dfracR (agreeR (leibnizO ObjectSpecV.t))).
Definition statusUR : ucmra := gmapUR (KKey.t * types.UID.t) (prodR dfracR (agreeR (leibnizO ObjectStatusV.t))).
Definition fragUR : ucmra := prodUR metaUR (prodUR specUR statusUR).

Implicit Types (a : authO) (b : fragUR).

Local Definition proj_state a : gmap KKey.t KObjectV.t := fst a.
Local Definition proj_used_uids a : gset types.UID.t := snd a.

Local Definition proj_meta b : metaUR := fst b.
Local Definition proj_spec b : specUR := fst (snd b).
Local Definition proj_status b : statusUR := snd (snd b).

Local Definition valid_kauth a : Prop :=
  ∀ k obj, proj_state a !! k = Some obj →
    k = KObjectV.key obj ∧
    KObjectV.well_formed obj ∧
    (KObjectV.objectmeta obj).(ObjectMetaV.UID') ∈ proj_used_uids a.

Local Definition compatible_kfrag b a : Prop :=
  map_Forall (λ '(k, uid) '(dq, agree_meta),
    ∃ meta, agree_meta = to_agree meta ∧
      ✓ dq ∧
      ∃ obj, proj_state a !! k = Some obj ∧
        (KObjectV.objectmeta obj).(ObjectMetaV.UID') = uid ∧
        KObjectV.objectmeta obj = meta
  ) (proj_meta b) ∧
  map_Forall (λ '(k, uid) '(dq, agree_spec),
    ∃ spec, agree_spec = to_agree spec ∧
      uid ∈ proj_used_uids a ∧
      ✓ dq ∧
      ∀ obj, proj_state a !! k = Some obj →
        (KObjectV.objectmeta obj).(ObjectMetaV.UID') = uid →
        KObjectV.spec obj = spec
  ) (proj_spec b) ∧
  map_Forall (λ '(k, uid) '(dq, agree_status),
    ∃ status, agree_status = to_agree status ∧
      uid ∈ proj_used_uids a ∧
      ✓ dq ∧
      ∀ obj, proj_state a !! k = Some obj →
        (KObjectV.objectmeta obj).(ObjectMetaV.UID') = uid →
        KObjectV.status obj = status
  ) (proj_status b).

Local Definition view_rel_raw (n: nat) a b :=
  valid_kauth a ∧ compatible_kfrag b a.

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

Local Canonical Structure view_rel : view_rel authO fragUR :=
  ViewRel view_rel_raw view_rel_raw_mono
          view_rel_raw_valid view_rel_raw_unit.

Definition kview_auth dq a : viewR view_rel := ●V{dq} a.
Definition kview_frag b : viewR view_rel := ◯V b.
Notation "●K a" := (kview_auth 1 a) (at level 20).
Notation "◯K b" := (kview_frag b) (at level 20).

Definition mk_meta_frag (k: KKey.t) (uid: types.UID.t) (dq: dfrac) (m: ObjectMetaV.t) : fragUR :=
  ({[(k, uid) := (dq, to_agree m)]}, (∅, ∅)).
Definition mk_spec_frag (k: KKey.t) (uid: types.UID.t) (dq: dfrac) (s: ObjectSpecV.t) : fragUR :=
  (∅, ({[(k, uid) := (dq, to_agree s)]}, ∅)).
Definition mk_status_frag (k: KKey.t) (uid: types.UID.t) (dq: dfrac) (s: ObjectStatusV.t) : fragUR :=
  (∅, (∅, {[(k, uid) := (dq, to_agree s)]})).

Lemma auth_frag_valid (n: nat) a b:
✓ (●K a ⋅ ◯K b) →
∀ n, view_rel_raw n a b.
Proof. Admitted.

Lemma meta_valid k uid dq meta:
✓ (◯K (mk_meta_frag k uid dq meta)) →
k.(KKey.Name') = meta.(ObjectMetaV.Name') ∧
k.(KKey.Namespace') = meta.(ObjectMetaV.Namespace') ∧
uid = meta.(ObjectMetaV.UID') ∧
ObjectMetaV.well_formed meta.
Proof. Admitted.

Lemma auth_meta_valid a k uid dq meta:
✓ (●K a ⋅ ◯K (mk_meta_frag k uid dq meta)) →
∃ obj, (proj_state a) !! k = Some obj ∧ (KObjectV.objectmeta obj) = meta.
Proof. Admitted.

Lemma meta_meta_valid k uid dq1 meta1 dq2 meta2:
✓ (◯K (mk_meta_frag k uid dq1 meta1) ⋅
   ◯K (mk_meta_frag k uid dq2 meta2)) →
✓ (dq1 ⋅ dq2) ∧ meta1 = meta2.
Proof. Admitted.

Lemma auth_spec_valid a k uid dq spec:
✓ (●K a ⋅ ◯K (mk_spec_frag k uid dq spec)) →
∀ obj, (proj_state a) !! k = Some obj →
  (KObjectV.objectmeta obj).(ObjectMetaV.UID') = uid →
    (KObjectV.spec obj) = spec.
Proof. Admitted.

Definition valid_k_uid_obj k uid obj: Prop :=
  k = KObjectV.key obj ∧
  uid = (KObjectV.objectmeta obj).(ObjectMetaV.UID') ∧
  KObjectV.well_formed obj.

Lemma create_kobj a k uid obj:
(proj_state a) !! k = None →
uid ∉ (proj_used_uids a) →
valid_k_uid_obj k uid obj →
●K a ~~>
  (●K ((<[k := obj]> (proj_state a)), ((proj_used_uids a) ∪ {[uid]})) ⋅
      ◯K (mk_meta_frag k uid 1 (KObjectV.objectmeta obj)) ⋅
      ◯K (mk_spec_frag k uid 1 (KObjectV.spec obj)) ⋅
      ◯K (mk_status_frag k uid 1 (KObjectV.status obj))).
Proof. Admitted.

Lemma delete_kobj a k uid meta:
(●K a ⋅ ◯K (mk_meta_frag k uid 1 meta)) ~~>
  ●K (delete k (proj_state a), proj_used_uids a).
Proof. Admitted.

Lemma update_kobj a k uid meta spec prev_obj obj:
valid_k_uid_obj k uid obj →
(proj_state a) !! k = Some prev_obj →
(KObjectV.status prev_obj) = (KObjectV.status obj) →
(●K a ⋅
  ◯K (mk_meta_frag k uid 1 meta) ⋅
  ◯K (mk_spec_frag k uid 1 spec)) ~~>
  (●K ((<[k := obj]> (proj_state a)), proj_used_uids a) ⋅
    ◯K (mk_meta_frag k uid 1 (KObjectV.objectmeta obj)) ⋅
    ◯K (mk_spec_frag k uid 1 (KObjectV.spec obj))).
Proof. Admitted.

Lemma update_status_kobj a k uid meta status prev_obj obj:
valid_k_uid_obj k uid obj →
(proj_state a) !! k = Some prev_obj →
(KObjectV.spec prev_obj) = (KObjectV.spec obj) →
(●K a ⋅
  ◯K (mk_meta_frag k uid 1 meta) ⋅
  ◯K (mk_status_frag k uid 1 status)) ~~>
  (●K ((<[k := obj]> (proj_state a)), proj_used_uids a) ⋅
    ◯K (mk_meta_frag k uid 1 (KObjectV.objectmeta obj)) ⋅
    ◯K (mk_status_frag k uid 1 (KObjectV.status obj))).
Proof. Admitted.

Class kviewG Σ :=
  { #[global] kview_inG :: inG Σ (viewR view_rel); }.

Definition kviewΣ :=
  #[GFunctor (viewR view_rel)].

#[global]
Instance subG_kviewG Σ :
  subG kviewΣ Σ → kviewG Σ.
Proof. solve_inG. Qed.

Context `{!kviewG Σ}.

Definition own_auth γ (state: gmap KKey.t KObjectV.t) (used_uids: gsetO types.UID.t) : iProp Σ :=
  own γ (●K (state, used_uids)).

Global Instance own_auth_discretizable γ state used_uids : Discretizable (own_auth γ state used_uids).
Proof. apply _. Qed.

Definition own_meta_frag γ k uid dq m : iProp Σ :=
  own γ (◯K (mk_meta_frag k uid dq m)).

Definition own_spec_frag γ k uid dq sp : iProp Σ :=
  own γ (◯K (mk_spec_frag k uid dq sp)).

Definition own_status_frag γ k uid dq st : iProp Σ :=
  own γ (◯K (mk_status_frag k uid dq st)).

Lemma create_kobj_fupd {γ state used_uids} k uid obj:
state !! k = None →
uid ∉ used_uids →
valid_k_uid_obj k uid obj →
own_auth γ state used_uids ==∗
  own_auth γ ((<[k := obj]> state)) (used_uids ∪ {[uid]}) ∗
  own_meta_frag γ k uid 1 (KObjectV.objectmeta obj) ∗
  own_spec_frag γ k uid 1 (KObjectV.spec obj) ∗
  own_status_frag γ k uid 1 (KObjectV.status obj).
Proof. Admitted.

Lemma delete_kobj_fupd {γ state used_uids k uid meta}:
own_auth γ state used_uids ∗ own_meta_frag γ k uid 1 meta ==∗
  own_auth γ (delete k state) used_uids.
Proof. Admitted.

Lemma update_kobj_fupd {γ state used_uids k uid meta spec} prev_obj obj:
valid_k_uid_obj k uid obj →
state !! k = Some prev_obj →
(KObjectV.status prev_obj) = (KObjectV.status obj) →
own_auth γ state used_uids ∗
own_meta_frag γ k uid 1 meta ∗
own_spec_frag γ k uid 1 spec ==∗
  own_auth γ (<[k := obj]> state) used_uids ∗
  own_meta_frag γ k uid 1 (KObjectV.objectmeta obj) ∗
  own_spec_frag γ k uid 1 (KObjectV.spec obj).
Proof. Admitted.

Lemma update_status_kobj_fupd {γ state used_uids k uid meta status} prev_obj obj:
valid_k_uid_obj k uid obj →
state !! k = Some prev_obj →
(KObjectV.spec prev_obj) = (KObjectV.spec obj) →
own_auth γ state used_uids ∗
own_meta_frag γ k uid 1 meta ∗
own_status_frag γ k uid 1 status ==∗
  own_auth γ (<[k := obj]> state) used_uids ∗
  own_meta_frag γ k uid 1 (KObjectV.objectmeta obj) ∗
  own_status_frag γ k uid 1 (KObjectV.status obj).
Proof. Admitted.

End kview.
