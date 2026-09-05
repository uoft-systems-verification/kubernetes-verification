From New.proof Require Import prelude empty_ffi.
From New.proof.kubernetes_model Require Export apimodel_init.
From New.proof.k8s_io.apimachinery.pkg.api Require Export errors.
From New.proof.k8s_io.apimachinery.pkg.apis.meta Require Import v1.
From New.proof.kubernetes_types Require Export prelude.
From New.proof.kubernetes_model Require Export inv.

Section proof.
Context `{hG: !heapGS Σ} `{!ffi_semantics _ _}.
Context {sem : go.Semantics} {package_sem : apimodel.Assumptions}.
Local Set Default Proof Using "All".

#[global] Instance KKey_into_val_inj : go.IntoValInj KKey.t.
Proof.
  constructor. intros k1 k2 Heq.
  assert (k1.(KKey.Kind') = k2.(KKey.Kind')) as Hkind.
  {
    pose proof (go.tagged_steps under
      (StructFieldGet apimodel.KKeyⁱᵐᵖˡ "Kind"%go) (#k1)
      (#k1.(KKey.Kind')) _) as Hstep1.
    pose proof (go.tagged_steps under
      (StructFieldGet apimodel.KKeyⁱᵐᵖˡ "Kind"%go) (#k2)
      (#k2.(KKey.Kind')) _) as Hstep2.
    assert (is_go_step_pure (StructFieldGet apimodel.KKeyⁱᵐᵖˡ "Kind"%go)
      (#k1) (#k1.(KKey.Kind'))) as Hpure.
    { rewrite (go.is_go_step_pure_det (IsGoStepPureDet:=Hstep1)). done. }
    rewrite Heq in Hpure.
    rewrite (go.is_go_step_pure_det (IsGoStepPureDet:=Hstep2)) in Hpure.
    symmetry in Hpure.
    injection Hpure as Hpure.
    destruct go.into_val_inj_string as [Hinj].
    specialize (Hinj k1.(KKey.Kind') k2.(KKey.Kind')).
    exact (Hinj Hpure).
  }
  assert (k1.(KKey.Name') = k2.(KKey.Name')) as Hname.
  {
    pose proof (go.tagged_steps under
      (StructFieldGet apimodel.KKeyⁱᵐᵖˡ "Name"%go) (#k1)
      (#k1.(KKey.Name')) _) as Hstep1.
    pose proof (go.tagged_steps under
      (StructFieldGet apimodel.KKeyⁱᵐᵖˡ "Name"%go) (#k2)
      (#k2.(KKey.Name')) _) as Hstep2.
    assert (is_go_step_pure (StructFieldGet apimodel.KKeyⁱᵐᵖˡ "Name"%go)
      (#k1) (#k1.(KKey.Name'))) as Hpure.
    { rewrite (go.is_go_step_pure_det (IsGoStepPureDet:=Hstep1)). done. }
    rewrite Heq in Hpure.
    rewrite (go.is_go_step_pure_det (IsGoStepPureDet:=Hstep2)) in Hpure.
    symmetry in Hpure.
    injection Hpure as Hpure.
    destruct go.into_val_inj_string as [Hinj].
    specialize (Hinj k1.(KKey.Name') k2.(KKey.Name')).
    exact (Hinj Hpure).
  }
  assert (k1.(KKey.Namespace') = k2.(KKey.Namespace')) as Hnamespace.
  {
    pose proof (go.tagged_steps under
      (StructFieldGet apimodel.KKeyⁱᵐᵖˡ "Namespace"%go) (#k1)
      (#k1.(KKey.Namespace')) _) as Hstep1.
    pose proof (go.tagged_steps under
      (StructFieldGet apimodel.KKeyⁱᵐᵖˡ "Namespace"%go) (#k2)
      (#k2.(KKey.Namespace')) _) as Hstep2.
    assert (is_go_step_pure (StructFieldGet apimodel.KKeyⁱᵐᵖˡ "Namespace"%go)
      (#k1) (#k1.(KKey.Namespace'))) as Hpure.
    { rewrite (go.is_go_step_pure_det (IsGoStepPureDet:=Hstep1)). done. }
    rewrite Heq in Hpure.
    rewrite (go.is_go_step_pure_det (IsGoStepPureDet:=Hstep2)) in Hpure.
    symmetry in Hpure.
    injection Hpure as Hpure.
    destruct go.into_val_inj_string as [Hinj].
    specialize (Hinj k1.(KKey.Namespace') k2.(KKey.Namespace')).
    exact (Hinj Hpure).
  }
  destruct k1, k2; simpl in *; congruence.
Qed.

#[global] Instance KKey_safe_map_key key :
  SafeMapKey (K:=KKey.t) apimodel.KKey key.
Proof.
  constructor. iIntros (stk E Ψ) "HΨ". wp_auto.
  replace (bool_decide (apimodel.KKey.Kind' key = apimodel.KKey.Kind' key)) with true by
    (symmetry; apply bool_decide_eq_true_2; done).
  wp_auto.
  replace (bool_decide (apimodel.KKey.Name' key = apimodel.KKey.Name' key)) with true by
    (symmetry; apply bool_decide_eq_true_2; done).
  wp_auto. done.
Qed.

Lemma wp_deepCopy i obj:
  {{{ is_pkg_init apimodel ∗
      KObjectV.deepown_i i obj 1
  }}}
    @! apimodel.deepCopy #(interface.ok i)
  {{{ i', RET #(interface.ok i');
      KObjectV.deepown_i i' obj 1 ∗
      KObjectV.deepown_i i obj 1
  }}}.
Proof.
Admitted.

Definition storage_object_normalize (obj : KObjectV.t) : KObjectV.t :=
  KObjectV.update_objectmeta obj
    ((KObjectV.objectmeta obj)
       <| ObjectMetaV.ResourceVersion' := ""%go |>
       <| ObjectMetaV.SelfLink' := ""%go |>).

Lemma objectmeta_update_objectmeta obj m :
  KObjectV.objectmeta (KObjectV.update_objectmeta obj m) = m.
Proof. destruct obj; done. Qed.

Lemma storage_object_normalize_update_objectmeta_deletionTimestamp obj m :
  storage_object_normalize (KObjectV.update_objectmeta obj m) =
  storage_object_normalize obj →
  m.(ObjectMetaV.DeletionTimestamp') =
  (KObjectV.objectmeta obj).(ObjectMetaV.DeletionTimestamp').
Proof.
  destruct obj as [p|rs|pvc|sts|d].
  - destruct p as [pt pm ps pst]. destruct pm. destruct m. simpl.
    intros H. inversion H. done.
  - destruct rs as [rt rm rspec rstatus]. destruct rm. destruct m. simpl.
    intros H. inversion H. done.
  - destruct pvc as [pvct pvcm pvcs pvcst]. destruct pvcm. destruct m. simpl.
    intros H. inversion H. done.
  - destruct sts as [stst stsm stss stsst]. destruct stsm. destruct m. simpl.
    intros H. inversion H. done.
  - destruct d as [dt dm ds dst]. destruct dm. destruct m. simpl.
    intros H. inversion H. done.
Qed.

Lemma objectmeta_updated_of_valid_simple_update_without_rv_selflink_eq m_old m_input m_updated :
  ObjectMetaV.valid_simple_update m_old m_input →
  ObjectMetaV.updated m_input m_updated →
  (m_updated <| ObjectMetaV.ResourceVersion' := ""%go |> <| ObjectMetaV.SelfLink' := ""%go |>) =
  (m_old <| ObjectMetaV.ResourceVersion' := ""%go |> <| ObjectMetaV.SelfLink' := ""%go |>) →
  ObjectMetaV.updated m_input m_old.
Proof.
  rewrite /ObjectMetaV.valid_simple_update /ObjectMetaV.updated.
  destruct m_old, m_input, m_updated; simpl.
  intros Hvalid Hupdated Hnormalized. inversion Hnormalized; subst.
  simpl in *. intuition congruence.
Qed.

Lemma storage_object_normalize_objectmeta_updated obj_old obj_input obj_updated :
  storage_object_normalize obj_updated = storage_object_normalize obj_old →
  ObjectMetaV.valid_simple_update
    (KObjectV.objectmeta obj_old)
    (KObjectV.objectmeta obj_input) →
  ObjectMetaV.updated
    (KObjectV.objectmeta obj_input)
    (KObjectV.objectmeta obj_updated) →
  ObjectMetaV.updated
    (KObjectV.objectmeta obj_input)
    (KObjectV.objectmeta obj_old).
Proof.
  intros Hstorage Hvalid Hupdated.
  eapply objectmeta_updated_of_valid_simple_update_without_rv_selflink_eq; [done|done|].
  assert (KObjectV.objectmeta (storage_object_normalize obj_updated) =
          KObjectV.objectmeta (storage_object_normalize obj_old)) as Hnormalized.
  { rewrite Hstorage. done. }
  rewrite /storage_object_normalize !objectmeta_update_objectmeta in Hnormalized.
  exact Hnormalized.
Qed.

Lemma storage_object_normalize_spec_eq obj1 obj2 :
  storage_object_normalize obj1 = storage_object_normalize obj2 →
  KObjectV.spec obj1 = KObjectV.spec obj2.
Proof.
  intros Hstorage.
  assert (KObjectV.spec (storage_object_normalize obj1) =
          KObjectV.spec (storage_object_normalize obj2)) as Hspec_eq.
  { rewrite Hstorage. done. }
  rewrite /storage_object_normalize !KObjectV.spec_update_objectmeta in Hspec_eq.
  exact Hspec_eq.
Qed.

Lemma wp_storageObjectDeepEqual i1 i2 obj1 obj2 dq1 dq2 :
  {{{ is_pkg_init apimodel ∗
      KObjectV.deepown_i i1 obj1 dq1 ∗
      KObjectV.deepown_i i2 obj2 dq2
  }}}
    @! apimodel.storageObjectDeepEqual #(interface.ok i1) #(interface.ok i2)
  {{{ v, RET #v;
      KObjectV.deepown_i i1 obj1 dq1 ∗
      KObjectV.deepown_i i2 obj2 dq2 ∗
      ⌜ v = true ↔ storage_object_normalize obj1 = storage_object_normalize obj2 ⌝
  }}}.
Proof.
Admitted.

Lemma wp_deletionTimestampForDelete (graceful: bool) (gracePeriod: w64) :
  {{{ is_pkg_init apimodel }}}
    @! apimodel.deletionTimestampForDelete #graceful #gracePeriod
  {{{ l c v, RET #l;
      l ↦ c ∗
      TimeV.deepown c v 1
  }}}.
Proof.
Admitted.

Lemma wp_State__generateNewRVAndUpdate l used_rv_l (used_rv : gmap go_string unit) :
  {{{ is_pkg_init apimodel ∗
      l.[(apimodel.State.t), "usedRV"] ↦ used_rv_l ∗
      used_rv_l ↦$ used_rv
  }}}
    l @! (go.PointerType apimodel.State) @! "generateNewRVAndUpdate" #()
  {{{ rv, RET #rv;
      ⌜ used_rv !! rv = None ⌝ ∗
      ⌜ valid_resource_version rv ⌝ ∗
      l.[(apimodel.State.t), "usedRV"] ↦ used_rv_l ∗
      used_rv_l ↦$ <[rv:=()]> used_rv
  }}}.
Proof.
Admitted.

Lemma wp_validateObjectMeta i (kind : go_string) l o m dq :
  {{{ is_pkg_init apimodel ∗
      ⌜ KObjectV.valid_interface i l o ⌝ ∗
      ObjectMetaV.deepown_l (KObjectV.objectmeta_ptr l o) m dq ∗
      ⌜ ObjectMetaV.valid kind m ⌝
  }}}
    @! apimodel.validateObjectMeta #(interface.ok i) #kind
  {{{ RET #interface.nil;
      ObjectMetaV.deepown_l (KObjectV.objectmeta_ptr l o) m dq
  }}}.
Proof.
Admitted.

Lemma wp_parseResourceVersion rv :
  {{{ is_pkg_init apimodel ∗
      ⌜ valid_resource_version rv ⌝
  }}}
    @! apimodel.parseResourceVersion #rv
  {{{ (ret : w64), RET (#ret, #interface.nil);
    True
  }}}.
Proof. Admitted.

Lemma wp_newUpdateResourceVersionConflictError (kind name old_rv new_rv : go_string) :
  {{{ is_pkg_init apimodel }}}
    @! apimodel.newUpdateResourceVersionConflictError #kind #name #old_rv #new_rv
  {{{ err, RET #err;
      ⌜ conflict_error err ⌝
  }}}.
Proof. Admitted.

Lemma wp_newUpdateUIDConflictError (kind name existing_uid uid : go_string) :
  {{{ is_pkg_init apimodel }}}
    @! apimodel.newUpdateUIDConflictError #kind #name #existing_uid #uid
  {{{ err, RET #err;
      ⌜ conflict_error err ⌝
  }}}.
Proof. Admitted.

Lemma wp_newPreconditionUIDConflictError (kind name uid1 uid2: go_string) :
  {{{ is_pkg_init apimodel }}}
    @! apimodel.newPreconditionUIDConflictError #kind #name #uid1 #uid2
  {{{ err, RET #err;
      ⌜ conflict_error err ⌝
  }}}.
Proof. Admitted.

Lemma wp_newPreconditionRVConflictError (kind name rv1 rv2: go_string) :
  {{{ is_pkg_init apimodel }}}
    @! apimodel.newPreconditionRVConflictError #kind #name #rv1 #rv2
  {{{ err, RET #err;
      ⌜ conflict_error err ⌝
  }}}.
Proof. Admitted.

End proof.
