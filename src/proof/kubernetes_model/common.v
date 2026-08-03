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
  destruct obj as [p|rs|pvc|sts].
  - destruct p as [pt pm ps pst]. destruct pm. destruct m. simpl.
    intros H. inversion H. done.
  - destruct rs as [rt rm rspec rstatus]. destruct rm. destruct m. simpl.
    intros H. inversion H. done.
  - destruct pvc as [pvct pvcm pvcs pvcst]. destruct pvcm. destruct m. simpl.
    intros H. inversion H. done.
  - destruct sts as [stst stsm stss stsst]. destruct stsm. destruct m. simpl.
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

Lemma wp_State__generateNewUIDAndUpdate l used_uid_l (used_uid : gmap types.UID.t unit) :
  {{{ is_pkg_init apimodel ∗
      l.[(apimodel.State.t), "usedUID"] ↦ used_uid_l ∗
      used_uid_l ↦$ used_uid
  }}}
    l @! (go.PointerType apimodel.State) @! "generateNewUIDAndUpdate" #()
  {{{ uid, RET #uid;
      ⌜ used_uid !! uid = None ⌝ ∗
      ⌜ valid_uid uid ⌝ ∗
      l.[(apimodel.State.t), "usedUID"] ↦ used_uid_l ∗
      used_uid_l ↦$ <[uid:=()]> used_uid
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

Lemma wp_State__generateNewName l m_ptr kind namespace generate_name (phys_state : gmap KKey.t interface.t):
  {{{ is_pkg_init apimodel ∗
      ⌜ valid_generate_name kind generate_name ⌝ ∗
      ⌜ length generate_name ≤ 58 ⌝ ∗
      l.[(apimodel.State.t), "m"] ↦ m_ptr ∗
      m_ptr ↦$ phys_state
  }}}
    l @! (go.PointerType apimodel.State) @! "generateNewName" #kind #namespace #generate_name
  {{{ (new_name: go_string), RET #new_name;
      ⌜ new_name ≠ ""%go ⌝ ∗
      ⌜ valid_name kind new_name ⌝ ∗
      ⌜ phys_state !! {| KKey.Kind' := kind; KKey.Namespace' := namespace; KKey.Name' := new_name;|} = None ⌝ ∗
      ⌜ ∀ kind namespace,
          ¬ reserved_key_pred {| KKey.Kind' := kind;
                             KKey.Namespace' := namespace;
                             KKey.Name' := new_name |} ⌝ ∗
      l.[(apimodel.State.t), "m"] ↦ m_ptr ∗
      m_ptr ↦$ phys_state
  }}}.
Proof.
Admitted.

Lemma wp_validateObjectMeta i (kind : go_string) l m dq :
  {{{ is_pkg_init apimodel ∗
      ⌜ i = interface.mk (go.PointerType v1.ObjectMeta) #l ⌝ ∗
      ObjectMetaV.deepown_l l m dq ∗
      ⌜ ObjectMetaV.valid kind m ⌝
  }}}
    @! apimodel.validateObjectMeta #(interface.ok i) #kind
  {{{ RET #interface.nil;
      ObjectMetaV.deepown_l l m dq
  }}}.
Proof.
Admitted.

Lemma wp_applyValidationAndDefaulting i l o (name : go_string) :
  {{{ is_pkg_init apimodel ∗
      ⌜ KObjectV.valid_interface i l o ⌝ ∗
      KObjectV.deepown_l l o 1 ∗
      ⌜ valid_create_typemeta (KObjectV.kind o) (KObjectV.typemeta o) ∧
        let m := KObjectV.objectmeta o in
        (m.(ObjectMetaV.GenerateName') ≠ ""%go →
          valid_generate_name (KObjectV.kind o) m.(ObjectMetaV.GenerateName')) ∧
        m.(ObjectMetaV.Name') ≠ ""%go ∧
        valid_name (KObjectV.kind o) m.(ObjectMetaV.Name') ∧
        m.(ObjectMetaV.Namespace') ≠ ""%go ∧
        valid_namespace m.(ObjectMetaV.Namespace') ∧
        valid_labels m.(ObjectMetaV.Labels') ∧
        valid_annotations m.(ObjectMetaV.Annotations') ∧
        valid_owner_references m.(ObjectMetaV.OwnerReferences') ∧
        valid_finalizers m.(ObjectMetaV.Finalizers') ∧
        valid_managed_fields m.(ObjectMetaV.ManagedFields') ⌝
  }}}
    @! apimodel.applyValidationAndDefaulting #(interface.ok i) #name
  {{{ o', RET #interface.nil;
      KObjectV.deepown_l l o' 1 ∗
      ⌜ KObjectV.same_kind o o' ⌝ ∗
      ⌜ ObjectMetaV.valid (KObjectV.kind o') (KObjectV.objectmeta o') ⌝ ∗
      ⌜ ObjectSpecV.valid (KObjectV.spec o') ⌝ ∗
      ⌜ ObjectStatusV.valid (KObjectV.status o') ⌝ ∗
      (* This contract includes the omitted decoder step: a create request may
         omit TypeMeta.kind, while the typed object returned by Kubernetes has
         the concrete kind selected by the endpoint. *)
      ⌜ valid_typemeta (KObjectV.kind o') (KObjectV.typemeta o') ⌝ ∗
      ⌜ KObjectV.objectmeta o' = ((KObjectV.objectmeta o) <| ObjectMetaV.Generation' := W64 1 |>) ⌝ ∗
      ⌜ ObjectSpecV.created (KObjectV.spec o) (KObjectV.spec o') ⌝ ∗
      ⌜ ObjectStatusV.created (KObjectV.status o) (KObjectV.status o') ⌝
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

(* [newNotFoundError] isolates the opaque Kubernetes API error constructor.
   Its clients reason only about the semantic class observed by
   [errors.IsNotFound]. *)
Lemma wp_newNotFoundError (kind name : go_string) :
  {{{ is_pkg_init apimodel }}}
    @! apimodel.newNotFoundError #kind #name
  {{{ err, RET #err;
      ⌜ not_found_error err ⌝
  }}}.
Proof. Admitted.

Lemma wp_newUpdateResourceVersionConflictError (kind name old_rv new_rv : go_string) :
  {{{ is_pkg_init apimodel }}}
    @! apimodel.newUpdateResourceVersionConflictError #kind #name #old_rv #new_rv
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

Lemma wp_allowUnconditionalUpdate (kind : go_string) :
  {{{ is_pkg_init apimodel }}}
    @! apimodel.allowUnconditionalUpdate #kind
  {{{ (ret : bool), RET #ret;
      True
  }}}.
Proof. Admitted.

Lemma wp_applyValidationAndDefaultingOnUpdate new_i new_l new_obj old_i old_l old_obj dq (namespace : go_string) :
  {{{ is_pkg_init apimodel ∗
      ⌜ KObjectV.valid_interface new_i new_l new_obj ⌝ ∗
      ⌜ KObjectV.valid_interface old_i old_l old_obj ⌝ ∗
      KObjectV.deepown_l new_l new_obj 1 ∗
      KObjectV.deepown_l old_l old_obj dq ∗
      ⌜ KObjectV.valid new_obj ⌝ ∗
      ⌜ KObjectV.valid old_obj ⌝ ∗
      ⌜ KObjectV.key old_obj = KObjectV.key new_obj ⌝ ∗
      ⌜ namespace = (KObjectV.objectmeta new_obj).(ObjectMetaV.Namespace') ⌝ ∗
      ⌜ ObjectMetaV.valid_update
          (KObjectV.objectmeta old_obj)
          (KObjectV.objectmeta new_obj) ⌝ ∗
      ⌜ ObjectSpecV.valid_update
          (KObjectV.spec old_obj)
          (KObjectV.spec new_obj) ⌝
  }}}
    @! apimodel.applyValidationAndDefaultingOnUpdate #(interface.ok new_i) #(interface.ok old_i) #namespace
  {{{ updated_obj, RET #interface.nil;
      KObjectV.deepown_l new_l updated_obj 1 ∗
      KObjectV.deepown_l old_l old_obj dq ∗
      ⌜ KObjectV.valid_interface new_i new_l updated_obj ⌝ ∗
      ⌜ KObjectV.valid updated_obj ⌝ ∗
      ⌜ KObjectV.key old_obj = KObjectV.key updated_obj ⌝ ∗
      ⌜ KObjectV.typemeta updated_obj = KObjectV.typemeta new_obj ⌝ ∗
      ⌜ ObjectMetaV.updated
          (KObjectV.objectmeta new_obj)
          (KObjectV.objectmeta updated_obj) ⌝ ∗
      ⌜ ObjectSpecV.updated
          (KObjectV.spec new_obj)
          (KObjectV.spec updated_obj) ⌝ ∗
      ⌜ KObjectV.spec new_obj = KObjectV.spec old_obj →
        KObjectV.spec updated_obj = KObjectV.spec old_obj ⌝ ∗
      ⌜ KObjectV.status updated_obj = KObjectV.status old_obj ⌝
  }}}.
Proof. Admitted.

Lemma wp_applyValidationAndDefaultingOnStatusUpdate
    new_i new_l new_obj old_i old_l old_obj dq (namespace : go_string) :
  {{{ is_pkg_init apimodel ∗
      ⌜ KObjectV.valid_interface new_i new_l new_obj ⌝ ∗
      ⌜ KObjectV.valid_interface old_i old_l old_obj ⌝ ∗
      KObjectV.deepown_l new_l new_obj 1 ∗
      KObjectV.deepown_l old_l old_obj dq ∗
      ⌜ KObjectV.valid new_obj ⌝ ∗
      ⌜ KObjectV.valid old_obj ⌝ ∗
      ⌜ KObjectV.key old_obj = KObjectV.key new_obj ⌝ ∗
      ⌜ namespace = (KObjectV.objectmeta new_obj).(ObjectMetaV.Namespace') ⌝ ∗
      ⌜ ObjectMetaV.valid_simple_update
          (KObjectV.objectmeta old_obj)
          (KObjectV.objectmeta new_obj) ⌝ ∗
      ⌜ ObjectStatusV.valid_update
          (KObjectV.status old_obj)
          (KObjectV.status new_obj) ⌝
  }}}
    @! apimodel.applyValidationAndDefaultingOnStatusUpdate #(interface.ok new_i) #(interface.ok old_i) #namespace
  {{{ updated_obj, RET #interface.nil;
      KObjectV.deepown_l new_l updated_obj 1 ∗
      KObjectV.deepown_l old_l old_obj dq ∗
      ⌜ KObjectV.valid_interface new_i new_l updated_obj ⌝ ∗
      ⌜ KObjectV.valid updated_obj ⌝ ∗
      ⌜ KObjectV.key old_obj = KObjectV.key updated_obj ⌝ ∗
      ⌜ KObjectV.same_kind new_obj updated_obj ⌝ ∗
      ⌜ ObjectMetaV.updated
          (KObjectV.objectmeta new_obj)
          (KObjectV.objectmeta updated_obj) ⌝ ∗
      ⌜ KObjectV.spec updated_obj = KObjectV.spec old_obj ⌝ ∗
      ⌜ ObjectStatusV.updated
          (KObjectV.status new_obj)
          (KObjectV.status updated_obj) ⌝
  }}}.
Proof. Admitted.

(* This is not a complete spec for shouldDeleteDuringUpdate, but it is sufficient
   because we only need to prove that it returns false when DeletionTimestamp is nil. *)
Lemma wp_shouldDeleteDuringUpdate_false new_i new_l new_obj old_i old_l old_obj dq :
  {{{ is_pkg_init apimodel ∗
      ⌜ KObjectV.valid_interface new_i new_l new_obj ⌝ ∗
      ⌜ KObjectV.valid_interface old_i old_l old_obj ⌝ ∗
      KObjectV.deepown_l new_l new_obj dq ∗
      KObjectV.deepown_l old_l old_obj dq ∗
      ⌜ (KObjectV.objectmeta old_obj).(ObjectMetaV.DeletionTimestamp') = None ⌝
  }}}
    @! apimodel.shouldDeleteDuringUpdate #(interface.ok new_i) #(interface.ok old_i)
  {{{ RET #false;
    KObjectV.deepown_l new_l new_obj dq ∗
    KObjectV.deepown_l old_l old_obj dq
  }}}.
Proof. Admitted.

(* General ownership-preserving specification.  Release updates also apply to
   terminating objects, for which Kubernetes may return either boolean.  The
   caller handles both the update and immediate-deletion branches. *)
Lemma wp_shouldDeleteDuringUpdate_general
    new_i new_l new_obj old_i old_l old_obj dq :
  {{{ is_pkg_init apimodel ∗
      ⌜ KObjectV.valid_interface new_i new_l new_obj ⌝ ∗
      ⌜ KObjectV.valid_interface old_i old_l old_obj ⌝ ∗
      KObjectV.deepown_l new_l new_obj dq ∗
      KObjectV.deepown_l old_l old_obj dq
  }}}
    @! apimodel.shouldDeleteDuringUpdate
      #(interface.ok new_i) #(interface.ok old_i)
  {{{ (should_delete : bool), RET #should_delete;
      KObjectV.deepown_l new_l new_obj dq ∗
      KObjectV.deepown_l old_l old_obj dq
  }}}.
Proof. Admitted.

End proof.
