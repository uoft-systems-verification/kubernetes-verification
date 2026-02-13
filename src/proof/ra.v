From New.proof Require Import prelude.
From New.proof Require Export pure_objects.
From New.proof.k8s_io.apimachinery.pkg.apis.meta Require Export v1_init.
(* From iris.algebra Require Import gmap_view. *)

Module KAuth.
Section def.
Axiom t: Type. (* t might just be a product of some gmap and gset *)
Axiom state: t → gmap KKey.t KObjectV.t.
Axiom used_uids: t → gset types.UID.t.
Axiom reserved_keys: gset KKey.t.
End def.
End KAuth.

Module KFrag.
Section def.
Inductive key_status :=
| Idle
| InUse.
(* TODO: Just use ProdR instead of record *)
Axiom t: Type.
(* Record t := mk {
  frag_meta_proj : gmapUR (KKey.t * types.UID.t) (prodR dfracR (agreeR (leibnizO ObjectMetaV.t)));
  frag_spec_proj : gmapUR (KKey.t * types.UID.t) (prodR dfracR (agreeR (leibnizO ObjectSpecV.t)));
  frag_status_proj : gmapUR (KKey.t * types.UID.t) (prodR dfracR (agreeR (leibnizO ObjectStatusV.t)));
  ...
}. *)
Axiom meta: KKey.t → types.UID.t → dfrac → ObjectMetaV.t → t.
Axiom spec: KKey.t → types.UID.t → dfrac → ObjectSpecV.t → t.
Axiom status: KKey.t → types.UID.t → dfrac → ObjectStatusV.t → t.
Axiom children: KKey.t → types.UID.t → dfrac → (gset KKey.t) → t.
Axiom reserved: KKey.t → dfrac → key_status → t.
Axiom tombstone: KKey.t → types.UID.t → t.
Axiom unit: t.
End def.
End KFrag.

(* A valid KAuth should satisfy the following:
(1) objects in (state kauth) must be valid Kubernetes objects
(2) uids in (used_uid kauth) must cover existing uids (and historical uids)
(3) key status in (reserved kauth) must match the keys in (state kauth)
 *)
Axiom valid_kauth: KAuth.t → Prop.

(* A KFrag is compatible with the KAuth depending on the constructor of KFrag:
Meta: the object of k exists in (KAuth.state a) with the KFrag.meta' uid and meta, and dq is valid
Spec: if the object of k exists with the uid, then the object has the Spec's spec, and dq is valid
Status: similar as above
KFrag.children: the set of objects that exist and has (k * uid) as parent reference is exactly children, and dq is valid
 KFrag.reserved: the k is in (reserved a) and its status matches the key's existence in (KAuth.state a)
KFrag.tombstone: the object of k either doesn't exist, or it exists with a different uid
*)
Axiom compatible_kfrag: KFrag.t → KAuth.t → Prop.

Definition kubernetes_view_rel_raw {SI : sidx} (n : SI) (a: KAuth.t) (b: KFrag.t) :=
  valid_kauth a ∧ compatible_kfrag b a.

Axiom kauth_equiv : Equiv KAuth.t.
Axiom kauth_dist  : Dist KAuth.t.
#[global] Existing Instance kauth_equiv.
#[global] Existing Instance kauth_dist.
Axiom kauth_ofe_mixin : OfeMixin KAuth.t.
Canonical Structure KAuthO : ofe := Ofe KAuth.t kauth_ofe_mixin.

Axiom kfrag_equiv : Equiv KFrag.t.
Axiom kfrag_dist  : Dist KFrag.t.
Axiom kfrag_pcore : PCore KFrag.t.
Axiom kfrag_op    : Op KFrag.t.
Axiom kfrag_valid : Valid KFrag.t.
Axiom kfrag_validN : ValidN KFrag.t.
Axiom kfrag_unit   : Unit KFrag.t.
#[global] Existing Instance kfrag_equiv.
#[global] Existing Instance kfrag_dist.
#[global] Existing Instance kfrag_pcore.
#[global] Existing Instance kfrag_op.
#[global] Existing Instance kfrag_valid.
#[global] Existing Instance kfrag_validN.
#[global] Existing Instance kfrag_unit.
Axiom kfrag_ofe_mixin : OfeMixin KFrag.t.
Axiom kfrag_cmra_mixin : CmraMixin KFrag.t.
Canonical Structure KFragO : ofe := Ofe KFrag.t kfrag_ofe_mixin.
Canonical Structure KFragR : cmra := Cmra KFrag.t kfrag_cmra_mixin.
Axiom kfrag_ucmra_mixin : UcmraMixin KFrag.t.
Canonical Structure KFragUR : ucmra := Ucmra KFrag.t kfrag_ucmra_mixin.

Axiom kubernetes_view_rel_raw_mono :
  ∀ {SI : sidx} n1 n2 a1 a2 b1 b2,
    kubernetes_view_rel_raw n1 a1 b1 →
    a1 ≡{n2}≡ a2 →
    b2 ≼{n2} b1 →
    (n2 ≤ n1)%sidx →
    kubernetes_view_rel_raw n2 a2 b2.

Axiom kubernetes_view_rel_raw_valid :
  ∀ {SI : sidx} n a b, kubernetes_view_rel_raw n a b → ✓{n} b.

Axiom kubernetes_view_rel_raw_unit :
  ∀ {SI : sidx} n, ∃ a, kubernetes_view_rel_raw n a ε.

Canonical Structure kubernetes_view_rel : view_rel KAuthO KFragUR :=
  ViewRel kubernetes_view_rel_raw kubernetes_view_rel_raw_mono
    kubernetes_view_rel_raw_valid kubernetes_view_rel_raw_unit.

Notation kubernetes_view := (view (A:=KAuth.t) (B:=KFrag.t) kubernetes_view_rel_raw).

Definition kubernetes_auth: dfrac → KAuth.t → kubernetes_view := view_auth.
Definition kubernetes_frag : KFrag.t → kubernetes_view := view_frag.

Notation "●K a" := (kubernetes_auth 1 a) (at level 20).

Notation "◯K b" := (kubernetes_frag b) (at level 20).

(* Validity and Op *)

Lemma kauth_kfrag_valid {SI : sidx} (n : SI) a b:
✓ (●K a ⋅ ◯K b) → ∀ n, kubernetes_view_rel_raw n a b.
Proof. Admitted.

Lemma meta_valid k uid dq meta:
✓ (◯K KFrag.meta k uid dq meta) →
  k.(KKey.Name') = meta.(ObjectMetaV.Name') ∧
  k.(KKey.Namespace') = meta.(ObjectMetaV.Namespace') ∧
  uid = meta.(ObjectMetaV.UID') ∧
  ObjectMetaV.well_formed meta.
Proof. Admitted.

Lemma kauth_meta_valid a k uid dq meta:
✓ (●K a ⋅ ◯K KFrag.meta k uid dq meta) →
  ∃ obj, (KAuth.state a) !! k = Some obj ∧ (KObjectV.objectmeta obj) = meta.
Proof. Admitted.

Lemma meta_meta_valid k uid dq1 meta1 dq2 meta2:
✓ (◯K KFrag.meta k uid dq1 meta1 ⋅ ◯K KFrag.meta k uid dq2 meta2) →
  ✓ (dq1 ⋅ dq2) ∧ meta1 = meta2.
Proof. Admitted.

Lemma kauth_spec_valid a k uid dq spec:
✓ (●K a ⋅ ◯K KFrag.spec k uid dq spec) →
  ∀ obj, (KAuth.state a) !! k = Some obj →
    (KObjectV.objectmeta obj).(ObjectMetaV.UID') = uid →
      (KObjectV.spec obj) = spec.
Proof. Admitted.

Lemma children_valid k uid dq children:
✓ (◯K KFrag.children k uid dq children) → k ∉ children.
Proof. Admitted.

Definition meta_is_child_of meta key uid: Prop :=
  meta.(ObjectMetaV.Namespace') = key.(KKey.Namespace') ∧
  match meta.(ObjectMetaV.OwnerReferences') with
  | Some os => os_has_controller_parent_of os key.(KKey.Kind') key.(KKey.Name') uid
  | None => False
  end.

Lemma meta_children_valid k1 uid1 dq1 meta k2 uid2 dq2 children:
✓ (◯K KFrag.meta k1 uid1 dq1 meta ⋅ ◯K KFrag.children k2 uid2 dq2 children) →
    (meta_is_child_of meta k2 uid2 ↔ k1 ∈ children).
Proof. Admitted.

Lemma reserved_valid k dq s:
✓ (◯K KFrag.reserved k dq s) → k ∈ KAuth.reserved_keys.
Proof. Admitted.

Lemma meta_reserved_valid k1 uid1 dq1 meta k2 dq2:
✓ (◯K KFrag.meta k1 uid1 dq1 meta ⋅ ◯K KFrag.reserved k2 dq2 KFrag.Idle) → k1 ≠ k2.
Proof. Admitted.

Lemma meta_tombstone_valid k1 uid1 dq meta k2 uid2:
✓ (◯K KFrag.meta k1 uid1 dq meta ⋅ ◯K KFrag.tombstone k2 uid2) → uid1 ≠ uid2.
Proof. Admitted.

Lemma tombstone_op k uid:
◯K KFrag.tombstone k uid ⋅ ◯K KFrag.tombstone k uid = ◯K KFrag.tombstone k uid.
Proof. Admitted.

(* Update *)

Lemma delete_child a k1 uid1 meta k2 uid2 children a': 
meta_is_child_of meta k2 uid2 →
delete k1 (KAuth.state a) = KAuth.state a' →
KAuth.used_uids a = KAuth.used_uids a' →
(●K a ⋅ ◯K KFrag.meta k1 uid1 1 meta ⋅ ◯K KFrag.children k2 uid2 1 children) ~~>
  (●K a' ⋅ ◯K KFrag.tombstone k1 uid1 ⋅ ◯K KFrag.children k2 uid2 1 (children ∖ {[k1]})).
Proof. Admitted.

Lemma delete_reserved_child a k1 uid1 meta k2 uid2 children a': 
meta_is_child_of meta k2 uid2 →
delete k1 (KAuth.state a) = KAuth.state a' →
KAuth.used_uids a = KAuth.used_uids a' →
(●K a ⋅ ◯K KFrag.meta k1 uid1 1 meta ⋅
  ◯K KFrag.reserved k1 1 KFrag.InUse ⋅
  ◯K KFrag.children k2 uid2 1 children) ~~>
  (●K a' ⋅ ◯K KFrag.tombstone k1 uid1 ⋅
    ◯K KFrag.reserved k1 1 KFrag.Idle ⋅
    ◯K KFrag.children k2 uid2 1 (children ∖ {[k1]})).
Proof. Admitted.

Definition valid_k_uid_obj k uid obj: Prop :=
  k.(KKey.Name') = (KObjectV.objectmeta obj).(ObjectMetaV.Name') ∧
  k.(KKey.Namespace') = (KObjectV.objectmeta obj).(ObjectMetaV.Namespace') ∧
  uid = (KObjectV.objectmeta obj).(ObjectMetaV.UID') ∧
  KObjectV.well_formed obj.

Lemma create_child a k1 uid1 meta spec status k2 uid2 children a': 
meta_is_child_of meta k2 uid2 →
(KAuth.state a) !! k1 = None → (* Need to prove the key is absent when it's not reserved as Idle *)
k1 ∉ KAuth.reserved_keys →
uid1 ∉ (KAuth.used_uids a) →
(∃ obj, valid_k_uid_obj k1 uid1 obj ∧
  meta = (KObjectV.objectmeta obj) ∧
  spec = (KObjectV.spec obj) ∧
  status = (KObjectV.status obj) ∧
  (<[k1 := obj]> (KAuth.state a)) = KAuth.state a') →
(KAuth.used_uids a) ∪ {[uid1]} = KAuth.used_uids a' →
(●K a ⋅ ◯K KFrag.children k2 uid2 1 children) ~~>
    (●K a' ⋅ ◯K KFrag.meta k1 uid1 1 meta ⋅
            ◯K KFrag.spec k1 uid1 1 spec ⋅
            ◯K KFrag.status k1 uid1 1 status ⋅
            ◯K KFrag.children k1 uid1 1 ∅ ⋅
            ◯K KFrag.children k2 uid2 1 (children ∪ {[k1]})).
Proof. Admitted.

Lemma create_reserved_child a k1 uid1 meta spec status k2 uid2 children a': 
meta_is_child_of meta k2 uid2 →
uid1 ∉ (KAuth.used_uids a) →
(∃ obj, valid_k_uid_obj k1 uid1 obj ∧
  meta = (KObjectV.objectmeta obj) ∧
  spec = (KObjectV.spec obj) ∧
  status = (KObjectV.status obj) ∧
  (<[k1 := obj]> (KAuth.state a)) = KAuth.state a') →
(KAuth.used_uids a) ∪ {[uid1]} = KAuth.used_uids a' →
(●K a ⋅ ◯K KFrag.reserved k1 1 KFrag.Idle ⋅
        ◯K KFrag.children k2 uid2 1 children) ~~>
    (●K a' ⋅ ◯K KFrag.meta k1 uid1 1 meta ⋅
            ◯K KFrag.spec k1 uid1 1 spec ⋅
            ◯K KFrag.status k1 uid1 1 status ⋅
            ◯K KFrag.reserved k1 1 KFrag.InUse ⋅
            ◯K KFrag.children k1 uid1 1 ∅ ⋅
            ◯K KFrag.children k2 uid2 1 (children ∪ {[k1]})).
Proof. Admitted.

Axiom meta_simple_update: ObjectMetaV.t → ObjectMetaV.t → Prop.

Lemma simple_update a k uid meta spec a' meta' spec':
meta_simple_update meta meta' →
(∃ obj, valid_k_uid_obj k uid obj ∧
  meta' = (KObjectV.objectmeta obj) ∧
  spec' = (KObjectV.spec obj) ∧
  (∀ prev_obj, (KAuth.state a) !! k = Some prev_obj →
    (KObjectV.status prev_obj) = (KObjectV.status obj)) ∧
  (<[k := obj]> (KAuth.state a)) = KAuth.state a') →
KAuth.used_uids a = KAuth.used_uids a' →
    (●K a ⋅ ◯K KFrag.meta k uid 1 meta ⋅ ◯K KFrag.spec k uid 1 spec) ~~>
        (●K a' ⋅ ◯K KFrag.meta k uid 1 meta' ⋅ ◯K KFrag.spec k uid 1 spec').
Proof. Admitted.

Definition meta_is_orphan meta: Prop := ∀ k uid, ¬ meta_is_child_of meta k uid.

Lemma release_child a k1 uid1 meta k2 uid2 children a' meta':
meta_is_child_of meta k2 uid2 →
meta_is_orphan meta' →
(∃ obj, valid_k_uid_obj k1 uid1 obj ∧
  meta' = (KObjectV.objectmeta obj) ∧
  (∀ prev_obj, (KAuth.state a) !! k1 = Some prev_obj →
    (KObjectV.spec prev_obj) = (KObjectV.spec obj) ∧
    (KObjectV.status prev_obj) = (KObjectV.status obj)) ∧
  (<[k1 := obj]> (KAuth.state a)) = KAuth.state a') →
KAuth.used_uids a = KAuth.used_uids a' →
(●K a ⋅ ◯K KFrag.meta k1 uid1 1 meta ⋅ ◯K KFrag.children k2 uid2 1 children) ~~>
    (●K a' ⋅ ◯K KFrag.meta k1 uid1 1 meta' ⋅ ◯K KFrag.children k2 uid2 1 (children ∖ {[k1]})).
Proof. Admitted.

Lemma adopt_orphan a k1 uid1 meta k2 uid2 children a' meta':
meta_is_orphan meta →
meta_is_child_of meta' k2 uid2 →
(∃ obj, valid_k_uid_obj k1 uid1 obj ∧
  meta' = (KObjectV.objectmeta obj) ∧
  (∀ prev_obj, (KAuth.state a) !! k1 = Some prev_obj →
    (KObjectV.spec prev_obj) = (KObjectV.spec obj) ∧
    (KObjectV.status prev_obj) = (KObjectV.status obj)) ∧
  (<[k1 := obj]> (KAuth.state a)) = KAuth.state a') →
KAuth.used_uids a = KAuth.used_uids a' →
(●K a ⋅ ◯K KFrag.meta k1 uid1 1 meta ⋅ ◯K KFrag.children k2 uid2 1 children) ~~>
    (●K a' ⋅ ◯K KFrag.meta k1 uid1 1 meta' ⋅ ◯K KFrag.children k2 uid2 1 (children ∪ {[k1]})).
Proof. Admitted.
