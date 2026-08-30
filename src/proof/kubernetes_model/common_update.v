From New.proof Require Import prelude empty_ffi.
From New.proof.kubernetes_model Require Export common.
From New.proof.k8s_io.apiserver.pkg.registry Require Export rest.

(** Important modeling assumption: we currently ignore fields that are not
    represented by the Kubernetes view types. In particular, we assume that
    validation of those Go fields always succeeds. We will gradually add those
    fields to the view types and verify their validation. Proofs using the
    specifications of [applyValidationAndDefaultingOnUpdate] and
    [applyValidationAndDefaultingOnStatusUpdate] do not need to own or reason
    about the unmodeled fields.

    TODO: [KObjectV.deepown_l] must existentially own all reachable Go fields,
    including unmodeled fields, so helper calls cannot mutate memory outside
    their separation-logic footprint. *)

Section proof.
Context `{hG: !heapGS Σ} `{!ffi_semantics _ _}.
Context {sem : go.Semantics} {package_sem : apimodel.Assumptions}.
Context `{!kubernetesModelG Σ}.
Local Set Default Proof Using "All".

Lemma own_update_frag_identity γ state used_uid key uid {dq} request_kind namespace old_meta old_spec input :
  KObjectV.valid_update request_kind namespace old_meta old_spec input →
  own_kview_auth γ state used_uid -∗
  own_meta_frag γ key uid 1 old_meta -∗
  own_spec_frag γ key uid dq old_spec -∗
  ⌜ key = KObjectV.key input ∧
    uid = (KObjectV.objectmeta input).(ObjectMetaV.UID') ∧
    old_meta.(ObjectMetaV.DeletionTimestamp') = None ⌝.
Proof.
  iIntros (Hvalid_update) "Hauth Hmeta Hspec".
  rewrite /own_kview_auth /own_meta_frag /own_spec_frag.
  iPoseProof (kview.own_meta_valid with "Hmeta") as
    "(%Hkey_name & %Hkey_namespace & %Huid_meta & %Hmeta_valid & %Hmeta_living)".
  iPoseProof (kview.own_meta_exists with "Hauth Hmeta") as
    "(%old & %Hlookup_old & %Huid_old & %Hmeta_eq & %Huid_in)".
  iPoseProof (kview.own_auth_valid2 key old Hlookup_old with "Hauth") as
    "(%Hkey_old & %Hold_valid & %Huid_old_in & %Hno_speculative_parent & %Huid_unique)".
  iPoseProof (kview.own_meta_living Hlookup_old with "Hauth Hmeta") as "%Hold_living".
  iPoseProof (kview.own_spec_exists with "Hauth Hspec") as "%Hspec_exists".
  assert (KObjectV.spec old = old_spec) as Hspec_old.
  { eapply Hspec_exists; done. }
  assert (ObjectMetaV.valid_update old_meta (KObjectV.objectmeta input) ∧
      ObjectSpecV.valid_update old_spec (KObjectV.spec input)) as
    (Hmeta_update & Hspec_update).
  { destruct old_spec, input; rewrite /KObjectV.valid_update /= in Hvalid_update |- *;
      rewrite ?/PodV.valid_update ?/ReplicaSetV.valid_update
        ?/PersistentVolumeClaimV.valid_update ?/StatefulSetV.valid_update in Hvalid_update;
      try contradiction; tauto. }
  assert ((KObjectV.objectmeta old).(ObjectMetaV.Name') = old_meta.(ObjectMetaV.Name') ∧
      (KObjectV.objectmeta old).(ObjectMetaV.Namespace') = old_meta.(ObjectMetaV.Namespace'))
    as (Hname_old & Hnamespace_old).
  { pose proof Hmeta_eq as Hmeta_eq_fields.
    rewrite /ObjectMetaV.equiv_except_resource_version
      /ObjectMetaV.without_resource_version in Hmeta_eq_fields.
    pose proof (f_equal ObjectMetaV.Name' Hmeta_eq_fields) as Hname.
    pose proof (f_equal ObjectMetaV.Namespace' Hmeta_eq_fields) as Hnamespace.
    simpl in Hname, Hnamespace. done. }
  assert ((KObjectV.objectmeta input).(ObjectMetaV.Name') = old_meta.(ObjectMetaV.Name') ∧
      (KObjectV.objectmeta input).(ObjectMetaV.Namespace') = old_meta.(ObjectMetaV.Namespace') ∧
      (KObjectV.objectmeta input).(ObjectMetaV.UID') = old_meta.(ObjectMetaV.UID'))
    as (Hname_input & Hnamespace_input & Huid_input).
  { destruct Hmeta_update as ([Hsimple | Hrelease] & _).
    - rewrite /ObjectMetaV.valid_simple_update in Hsimple. tauto.
    - rewrite /ObjectMetaV.equiv_except_resource_version
        /ObjectMetaV.without_resource_version in Hrelease.
      pose proof (f_equal ObjectMetaV.Name' Hrelease) as Hname.
      pose proof (f_equal ObjectMetaV.Namespace' Hrelease) as Hnamespace.
      pose proof (f_equal ObjectMetaV.UID' Hrelease) as Huid.
      simpl in Hname, Hnamespace, Huid.
      split_and!; symmetry; assumption. }
  iPureIntro. split_and!.
  - rewrite Hkey_old.
    assert ((KObjectV.objectmeta old).(ObjectMetaV.Name') =
      (KObjectV.objectmeta input).(ObjectMetaV.Name')) as Hname by congruence.
    assert ((KObjectV.objectmeta old).(ObjectMetaV.Namespace') =
      (KObjectV.objectmeta input).(ObjectMetaV.Namespace')) as Hnamespace by congruence.
    destruct old_spec, input, old; simpl in *; try contradiction; try discriminate;
      rewrite /KObjectV.key /= Hname Hnamespace //.
  - congruence.
  - exact Hmeta_living.
Qed.

Lemma own_status_update_frag_identity γ state used_uid key uid request_kind namespace
    old_meta old_status input :
  KObjectV.valid_status_update request_kind namespace old_meta old_status input →
  own_kview_auth γ state used_uid -∗
  own_meta_frag γ key uid 1 old_meta -∗
  own_status_frag γ key uid 1 old_status -∗
  ⌜ key = KObjectV.key input ∧
    uid = (KObjectV.objectmeta input).(ObjectMetaV.UID') ∧
    old_meta.(ObjectMetaV.DeletionTimestamp') = None ⌝.
Proof.
  iIntros (Hvalid_update) "Hauth Hmeta Hstatus".
  rewrite /own_kview_auth /own_meta_frag /own_status_frag.
  iPoseProof (kview.own_meta_valid with "Hmeta") as
    "(%Hkey_name & %Hkey_namespace & %Huid_meta & %Hmeta_valid & %Hmeta_living)".
  iPoseProof (kview.own_meta_exists with "Hauth Hmeta") as
    "(%old & %Hlookup_old & %Huid_old & %Hmeta_eq & %Huid_in)".
  iPoseProof (kview.own_auth_valid2 key old Hlookup_old with "Hauth") as
    "(%Hkey_old & %Hold_valid & %Huid_old_in & %Hno_speculative_parent & %Huid_unique)".
  iPoseProof (kview.own_meta_living Hlookup_old with "Hauth Hmeta") as "%Hold_living".
  iPoseProof (kview.own_status_exists with "Hauth Hstatus") as "%Hstatus_exists".
  assert (KObjectV.status old = old_status) as Hstatus_old.
  { eapply Hstatus_exists; done. }
  assert (ObjectMetaV.valid_update old_meta (KObjectV.objectmeta input)) as Hmeta_update.
  { destruct old_status, input; rewrite /KObjectV.valid_status_update /= in Hvalid_update;
      rewrite ?/PodV.valid_status_update ?/ReplicaSetV.valid_status_update
        ?/PersistentVolumeClaimV.valid_status_update ?/StatefulSetV.valid_status_update
        in Hvalid_update;
      try contradiction; tauto. }
  assert ((KObjectV.objectmeta old).(ObjectMetaV.Name') = old_meta.(ObjectMetaV.Name') ∧
      (KObjectV.objectmeta old).(ObjectMetaV.Namespace') = old_meta.(ObjectMetaV.Namespace'))
    as (Hname_old & Hnamespace_old).
  { pose proof Hmeta_eq as Hmeta_eq_fields.
    rewrite /ObjectMetaV.equiv_except_resource_version
      /ObjectMetaV.without_resource_version in Hmeta_eq_fields.
    pose proof (f_equal ObjectMetaV.Name' Hmeta_eq_fields) as Hname.
    pose proof (f_equal ObjectMetaV.Namespace' Hmeta_eq_fields) as Hnamespace.
    simpl in Hname, Hnamespace. done. }
  assert ((KObjectV.objectmeta input).(ObjectMetaV.Name') = old_meta.(ObjectMetaV.Name') ∧
      (KObjectV.objectmeta input).(ObjectMetaV.Namespace') = old_meta.(ObjectMetaV.Namespace') ∧
      (KObjectV.objectmeta input).(ObjectMetaV.UID') = old_meta.(ObjectMetaV.UID'))
    as (Hname_input & Hnamespace_input & Huid_input).
  { destruct Hmeta_update as ([Hsimple | Hrelease] & _).
    - rewrite /ObjectMetaV.valid_simple_update in Hsimple. tauto.
    - rewrite /ObjectMetaV.equiv_except_resource_version
        /ObjectMetaV.without_resource_version in Hrelease.
      pose proof (f_equal ObjectMetaV.Name' Hrelease) as Hname.
      pose proof (f_equal ObjectMetaV.Namespace' Hrelease) as Hnamespace.
      pose proof (f_equal ObjectMetaV.UID' Hrelease) as Huid.
      simpl in Hname, Hnamespace, Huid.
      split_and!; symmetry; assumption. }
  iPureIntro. split_and!.
  - rewrite Hkey_old.
    assert ((KObjectV.objectmeta old).(ObjectMetaV.Name') =
      (KObjectV.objectmeta input).(ObjectMetaV.Name')) as Hname by congruence.
    assert ((KObjectV.objectmeta old).(ObjectMetaV.Namespace') =
      (KObjectV.objectmeta input).(ObjectMetaV.Namespace')) as Hnamespace by congruence.
    destruct old_status, input, old; simpl in Hstatus_old |- *; try discriminate;
      inversion Hstatus_old; subst; rewrite /KObjectV.key /= Hname Hnamespace //.
  - congruence.
  - exact Hmeta_living.
Qed.

(** [update_objects_equiv_except_resource_version] relates two views of the
    same object when only the server-managed resource version may differ.
    Storage establishes this relation between the helper result and the stored
    object. *)
Definition update_objects_equiv_except_resource_version (obj1 obj2 : KObjectV.t) : Prop :=
  KObjectV.same_kind obj1 obj2 ∧
  KObjectV.typemeta obj1 = KObjectV.typemeta obj2 ∧
  ObjectMetaV.equiv_except_resource_version (KObjectV.objectmeta obj1) (KObjectV.objectmeta obj2) ∧
  KObjectV.spec obj1 = KObjectV.spec obj2 ∧
  KObjectV.status obj1 = KObjectV.status obj2.

Lemma kobject_updated_parent_ref input stored :
  KObjectV.updated input stored →
  obj_parent_ref stored = obj_parent_ref input.
Proof.
  intros Hupdated. rewrite /obj_parent_ref.
  assert ((KObjectV.objectmeta stored).(ObjectMetaV.Namespace') =
      (KObjectV.objectmeta input).(ObjectMetaV.Namespace')) as Hnamespace.
  { destruct input, stored;
      rewrite /KObjectV.updated /PodV.updated /ReplicaSetV.updated
        /PersistentVolumeClaimV.updated /StatefulSetV.updated /= in Hupdated |- *;
      try done; destruct Hupdated as (_ & Hmeta & _);
      rewrite /ObjectMetaV.updated in Hmeta; tauto. }
  assert ((KObjectV.objectmeta stored).(ObjectMetaV.OwnerReferences') =
    (KObjectV.objectmeta input).(ObjectMetaV.OwnerReferences')) as Howners.
  { destruct input, stored;
      rewrite /KObjectV.updated /PodV.updated /ReplicaSetV.updated
        /PersistentVolumeClaimV.updated /StatefulSetV.updated /= in Hupdated |- *;
      try done; destruct Hupdated as (_ & Hmeta & _);
      rewrite /ObjectMetaV.updated in Hmeta; tauto. }
  rewrite /meta_parent_ref Howners.
  destruct (KObjectV.objectmeta input).(ObjectMetaV.OwnerReferences') as [owners|]; last done.
  destruct (list_find
    (fun owner => owner.(OwnerReferenceV.Controller') = Some true) owners)
    as [[idx owner]|]; last done.
  rewrite Hnamespace. done.
Qed.

Lemma kobject_status_updated_parent_ref input stored :
  KObjectV.status_updated input stored →
  obj_parent_ref stored = obj_parent_ref input.
Proof.
  intros Hupdated. rewrite /obj_parent_ref.
  assert ((KObjectV.objectmeta stored).(ObjectMetaV.Namespace') =
      (KObjectV.objectmeta input).(ObjectMetaV.Namespace')) as Hnamespace.
  { destruct input, stored;
      rewrite /KObjectV.status_updated /PodV.status_updated /ReplicaSetV.status_updated
        /PersistentVolumeClaimV.status_updated /StatefulSetV.status_updated /= in Hupdated |- *;
      try done; destruct Hupdated as (_ & Hmeta & _);
      rewrite /ObjectMetaV.updated in Hmeta; tauto. }
  assert ((KObjectV.objectmeta stored).(ObjectMetaV.OwnerReferences') =
      (KObjectV.objectmeta input).(ObjectMetaV.OwnerReferences')) as Howners.
  { destruct input, stored;
      rewrite /KObjectV.status_updated /PodV.status_updated /ReplicaSetV.status_updated
        /PersistentVolumeClaimV.status_updated /StatefulSetV.status_updated /= in Hupdated |- *;
      try done; destruct Hupdated as (_ & Hmeta & _);
      rewrite /ObjectMetaV.updated in Hmeta; tauto. }
  rewrite /meta_parent_ref Howners.
  destruct (KObjectV.objectmeta input).(ObjectMetaV.OwnerReferences') as [owners|]; last done.
  destruct (list_find
    (fun owner => owner.(OwnerReferenceV.Controller') = Some true) owners)
    as [[idx owner]|]; last done.
  rewrite Hnamespace. done.
Qed.

Lemma storage_object_normalize_eq_implies_update_objects_equiv_except_resource_version
    obj1 obj2 :
  KObjectV.valid obj1 →
  KObjectV.valid obj2 →
  storage_object_normalize obj1 = storage_object_normalize obj2 →
  update_objects_equiv_except_resource_version obj1 obj2.
Proof.
  destruct obj1 as [[tm1 meta1 spec1 status1]|[tm1 meta1 spec1 status1]|
      [tm1 meta1 spec1 status1]|[tm1 meta1 spec1 status1]],
    obj2 as [[tm2 meta2 spec2 status2]|[tm2 meta2 spec2 status2]|
      [tm2 meta2 spec2 status2]|[tm2 meta2 spec2 status2]];
    try discriminate;
    destruct meta1, meta2;
    rewrite /KObjectV.valid /storage_object_normalize
      /KObjectV.update_objectmeta /update_objects_equiv_except_resource_version
      /ObjectMetaV.equiv_except_resource_version
      /ObjectMetaV.without_resource_version /=;
    intros Hvalid1 Hvalid2 Hnormalize;
    pose proof (f_equal KObjectV.typemeta Hnormalize) as Htypemeta;
    pose proof (f_equal KObjectV.objectmeta Hnormalize) as Hobjectmeta;
    pose proof (f_equal KObjectV.spec Hnormalize) as Hspec;
    pose proof (f_equal KObjectV.status Hnormalize) as Hstatus;
    simpl in Htypemeta, Hobjectmeta, Hspec, Hstatus;
    inversion Hobjectmeta; subst; simpl in *;
    destruct Hvalid1 as (_ & _ & Hmeta1 & _);
    destruct Hvalid2 as (_ & _ & Hmeta2 & _);
    rewrite /ObjectMetaV.valid in Hmeta1, Hmeta2;
    destruct Hmeta1 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hself1);
    destruct Hmeta2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hself2);
    simpl in Hself1, Hself2;
    split_and!; try done;
    try (rewrite Htypemeta; done);
    try (rewrite Hspec; done);
    try (rewrite Hstatus; done);
    try (replace SelfLink' with SelfLink'0 by congruence; done).
Qed.

(** [update_prepared_for_helper] describes the object that the update caller
    passes to an update or status-update validation/defaulting helper. [input]
    is the object submitted to the request. The caller fills an empty namespace
    with [namespace]. It fills an omitted resource version from [old], while a
    nonempty submitted resource version must already equal the old one. Schema
    defaulting and the remaining normalization happen inside the helper, not in
    this preparation relation. *)
Definition update_prepared_for_helper
    (namespace : go_string) (old input helper_input : KObjectV.t) : Prop :=
  ((KObjectV.objectmeta input).(ObjectMetaV.Namespace') = ""%go ∨
   (KObjectV.objectmeta input).(ObjectMetaV.Namespace') = namespace) ∧
  ((KObjectV.objectmeta input).(ObjectMetaV.ResourceVersion') = ""%go ∨
   (KObjectV.objectmeta input).(ObjectMetaV.ResourceVersion') =
     (KObjectV.objectmeta old).(ObjectMetaV.ResourceVersion')) ∧
  KObjectV.key old = KObjectV.key helper_input ∧
  helper_input =
    KObjectV.update_objectmeta input
      ((KObjectV.objectmeta input) <| ObjectMetaV.Namespace' := namespace |>
                                   <| ObjectMetaV.ResourceVersion' :=
                                        (KObjectV.objectmeta old).(ObjectMetaV.ResourceVersion') |>).

(** This is the single trusted semantic contract for a successful ordinary
    update-helper call. [old] and [helper_input] are the objects passed to the
    helper, and [helper_result] is the mutated input object after it returns.

    The first two conjuncts expose facts needed by callers that separately own
    status or rely on an unchanged spec. The remaining conjuncts connect the
    helper result to the public end-to-end update relation and invariants. *)
Definition applyValidationAndDefaultingOnUpdate_updated
    (namespace : go_string) (old helper_input helper_result : KObjectV.t) : Prop :=
  KObjectV.status helper_result = KObjectV.status old ∧
  (KObjectV.spec helper_input = KObjectV.spec old →
    KObjectV.spec helper_result = KObjectV.spec old) ∧
  (∀ input stored,
    update_prepared_for_helper namespace old input helper_input →
    update_objects_equiv_except_resource_version helper_result stored →
    KObjectV.updated input stored) ∧
  (KObjectV.valid old →
    valid_typemeta (KObjectV.kind helper_input) (KObjectV.typemeta helper_input) →
    KObjectV.valid helper_result) ∧
  (KObjectV.extra_valid old → KObjectV.extra_valid helper_result).

(** Top-level validation, preparation by the update caller, and a successful
    helper call establish the object invariant for the helper result. TypeMeta
    validity follows from these premises and is not a separate assumption. *)
Lemma applyValidationAndDefaultingOnUpdate_updated_implies_valid :
  ∀ request_kind namespace old input helper_input helper_result,
    KObjectV.valid old →
    KObjectV.valid_update request_kind namespace
      (KObjectV.objectmeta old) (KObjectV.spec old) input →
    update_prepared_for_helper namespace old input helper_input →
    applyValidationAndDefaultingOnUpdate_updated namespace old helper_input helper_result →
    KObjectV.valid helper_result.
Proof.
  intros request_kind namespace old input helper_input helper_result Hvalid Hvalid_update
    Hprepared Hupdated.
  destruct Hupdated as (_ & _ & _ & Hvalid_result & _).
  apply Hvalid_result; first exact Hvalid.
  destruct Hprepared as (_ & _ & _ & ->).
  rewrite KObjectV.kind_update_objectmeta KObjectV.typemeta_update_objectmeta.
  destruct (KObjectV.spec old), input; rewrite /KObjectV.valid_update /= in Hvalid_update;
    rewrite ?/PodV.valid_update ?/ReplicaSetV.valid_update
      ?/PersistentVolumeClaimV.valid_update ?/StatefulSetV.valid_update in Hvalid_update;
    try contradiction; tauto.
Qed.

(** General contract used when the helper may reject an update. On failure the
    new object may already have been mutated, so the postcondition returns an
    unconstrained view of that same allocation instead of the original view. *)
Lemma wp_applyValidationAndDefaultingOnUpdate_general
    new_i new_l new_obj old_i old_l old_obj dq (namespace : go_string) :
  {{{ is_pkg_init apimodel ∗
      ⌜ KObjectV.valid_interface new_i new_l new_obj ⌝ ∗
      ⌜ KObjectV.valid_interface old_i old_l old_obj ⌝ ∗
      ⌜ KObjectV.same_kind old_obj new_obj ⌝ ∗
      KObjectV.deepown_l new_l new_obj 1 ∗
      KObjectV.deepown_l old_l old_obj dq
  }}}
    @! apimodel.applyValidationAndDefaultingOnUpdate #(interface.ok new_i) #(interface.ok old_i) #namespace
  {{{ (err : interface.t), RET #err;
      (⌜ err = interface.nil ⌝ ∗
        ∃ updated_obj,
          KObjectV.deepown_l new_l updated_obj 1 ∗
          KObjectV.deepown_l old_l old_obj dq ∗
          ⌜ KObjectV.valid_interface new_i new_l updated_obj ⌝ ∗
          ⌜ applyValidationAndDefaultingOnUpdate_updated namespace old_obj new_obj updated_obj ⌝) ∨
      (⌜ err ≠ interface.nil ⌝ ∗
        ⌜ ¬ conflict_error err ⌝ ∗
        ∃ failed_obj,
          KObjectV.deepown_l new_l failed_obj 1 ∗
          KObjectV.deepown_l old_l old_obj dq ∗
          ⌜ KObjectV.valid_interface new_i new_l failed_obj ⌝)
  }}}.
Proof. Admitted.

(** Strong contract for an update satisfying the modeled sufficient validity
    condition. [input] is the submitted update object and [new_obj] is the
    prepared object passed to the helper. Under the modeling assumption above,
    validation of unmodeled fields adds no precondition. The old object is
    read-only; the helper mutates the new object and returns its resulting
    view. *)
Lemma wp_applyValidationAndDefaultingOnUpdate_ok
    new_i new_l new_obj old_i old_l old_obj dq (namespace : go_string) input :
  {{{ is_pkg_init apimodel ∗
      ⌜ KObjectV.valid_interface new_i new_l new_obj ⌝ ∗
      ⌜ KObjectV.valid_interface old_i old_l old_obj ⌝ ∗
      ⌜ KObjectV.valid old_obj ⌝ ∗
      ⌜ KObjectV.valid_update (KObjectV.kind input) namespace
          (KObjectV.objectmeta old_obj) (KObjectV.spec old_obj) input ⌝ ∗
      ⌜ update_prepared_for_helper namespace old_obj input new_obj ⌝ ∗
      KObjectV.deepown_l new_l new_obj 1 ∗
      KObjectV.deepown_l old_l old_obj dq
  }}}
    @! apimodel.applyValidationAndDefaultingOnUpdate #(interface.ok new_i) #(interface.ok old_i) #namespace
  {{{ updated_obj, RET #interface.nil;
      KObjectV.deepown_l new_l updated_obj 1 ∗
      KObjectV.deepown_l old_l old_obj dq ∗
      ⌜ KObjectV.valid_interface new_i new_l updated_obj ⌝ ∗
      ⌜ applyValidationAndDefaultingOnUpdate_updated namespace old_obj new_obj updated_obj ⌝
  }}}.
Proof. Admitted.

(** This is the single trusted semantic contract for a successful status-update
    helper call. [old] and [helper_input] are the objects passed to the helper,
    and [helper_result] is the mutated input object after it returns. *)
Definition applyValidationAndDefaultingOnStatusUpdate_updated
    (namespace : go_string) (old helper_input helper_result : KObjectV.t) : Prop :=
  (∀ request_kind input stored,
    KObjectV.valid old →
    KObjectV.valid_status_update request_kind namespace
      (KObjectV.objectmeta old) (KObjectV.status old) input →
    update_prepared_for_helper namespace old input helper_input →
    update_objects_equiv_except_resource_version helper_result stored →
    KObjectV.status_updated input stored ∧
    KObjectV.spec stored = KObjectV.spec old) ∧
  (KObjectV.valid old →
    valid_typemeta (KObjectV.kind helper_input) (KObjectV.typemeta helper_input) →
    KObjectV.valid helper_result).

(** Top-level status-update validation, caller preparation, and a successful
    helper call establish the object invariant for the helper result. TypeMeta
    validity follows from these premises and is not a separate assumption. *)
Lemma applyValidationAndDefaultingOnStatusUpdate_updated_implies_valid :
  ∀ request_kind namespace old input helper_input helper_result,
    KObjectV.valid old →
    KObjectV.valid_status_update request_kind namespace
      (KObjectV.objectmeta old) (KObjectV.status old) input →
    update_prepared_for_helper namespace old input helper_input →
    applyValidationAndDefaultingOnStatusUpdate_updated namespace old helper_input helper_result →
    KObjectV.valid helper_result.
Proof.
  intros request_kind namespace old input helper_input helper_result Hvalid
    Hvalid_status_update Hprepared Hupdated.
  destruct Hupdated as (_ & Hvalid_result).
  apply Hvalid_result; first exact Hvalid.
  assert (valid_typemeta (KObjectV.kind input) (KObjectV.typemeta input))
    as Hvalid_typemeta_input.
  { destruct (KObjectV.status old), input;
      rewrite /KObjectV.valid_status_update /= in Hvalid_status_update;
      rewrite ?/PodV.valid_status_update ?/ReplicaSetV.valid_status_update
        ?/PersistentVolumeClaimV.valid_status_update ?/StatefulSetV.valid_status_update
        /ObjectMetaV.valid_update in Hvalid_status_update;
      try contradiction; tauto. }
  destruct Hprepared as (_ & _ & _ & ->).
  rewrite KObjectV.kind_update_objectmeta KObjectV.typemeta_update_objectmeta.
  exact Hvalid_typemeta_input.
Qed.

(** General contract used when the status-update helper may reject an update.
    On failure the new object may already have been mutated, so the
    postcondition returns an unconstrained view of that same allocation instead
    of the original view. *)
Lemma wp_applyValidationAndDefaultingOnStatusUpdate_general
    new_i new_l new_obj old_i old_l old_obj dq (namespace : go_string) :
  {{{ is_pkg_init apimodel ∗
      ⌜ KObjectV.valid_interface new_i new_l new_obj ⌝ ∗
      ⌜ KObjectV.valid_interface old_i old_l old_obj ⌝ ∗
      ⌜ KObjectV.same_kind old_obj new_obj ⌝ ∗
      KObjectV.deepown_l new_l new_obj 1 ∗
      KObjectV.deepown_l old_l old_obj dq
  }}}
    @! apimodel.applyValidationAndDefaultingOnStatusUpdate
      #(interface.ok new_i) #(interface.ok old_i) #namespace
  {{{ (err : interface.t), RET #err;
      (⌜ err = interface.nil ⌝ ∗
        ∃ updated_obj,
          KObjectV.deepown_l new_l updated_obj 1 ∗
          KObjectV.deepown_l old_l old_obj dq ∗
          ⌜ KObjectV.valid_interface new_i new_l updated_obj ⌝ ∗
          ⌜ applyValidationAndDefaultingOnStatusUpdate_updated
              namespace old_obj new_obj updated_obj ⌝) ∨
      (⌜ err ≠ interface.nil ⌝ ∗
        ⌜ ¬ conflict_error err ⌝ ∗
        ∃ failed_obj,
          KObjectV.deepown_l new_l failed_obj 1 ∗
          KObjectV.deepown_l old_l old_obj dq ∗
          ⌜ KObjectV.valid_interface new_i new_l failed_obj ⌝)
  }}}.
Proof. Admitted.

(** Strong contract for a status update satisfying the modeled sufficient
    validity condition. [input] is the submitted status-update object and
    [new_obj] is the prepared object passed to the helper. Under the modeling
    assumption above, validation of unmodeled fields adds no precondition. The
    old object is read-only; the helper mutates the new object and returns its
    resulting view. *)
Lemma wp_applyValidationAndDefaultingOnStatusUpdate_ok
    new_i new_l new_obj old_i old_l old_obj dq
    (request_kind namespace : go_string) input :
  {{{ is_pkg_init apimodel ∗
      ⌜ KObjectV.valid_interface new_i new_l new_obj ⌝ ∗
      ⌜ KObjectV.valid_interface old_i old_l old_obj ⌝ ∗
      ⌜ KObjectV.valid old_obj ⌝ ∗
      ⌜ KObjectV.valid_status_update request_kind namespace
          (KObjectV.objectmeta old_obj) (KObjectV.status old_obj) input ⌝ ∗
      ⌜ update_prepared_for_helper namespace old_obj input new_obj ⌝ ∗
      KObjectV.deepown_l new_l new_obj 1 ∗
      KObjectV.deepown_l old_l old_obj dq
  }}}
    @! apimodel.applyValidationAndDefaultingOnStatusUpdate
      #(interface.ok new_i) #(interface.ok old_i) #namespace
  {{{ updated_obj, RET #interface.nil;
      KObjectV.deepown_l new_l updated_obj 1 ∗
      KObjectV.deepown_l old_l old_obj dq ∗
      ⌜ KObjectV.valid_interface new_i new_l updated_obj ⌝ ∗
      ⌜ applyValidationAndDefaultingOnStatusUpdate_updated
          namespace old_obj new_obj updated_obj ⌝
  }}}.
Proof. Admitted.

Lemma wp_allowUnconditionalUpdate (kind : go_string) :
  {{{ is_pkg_init apimodel }}}
    @! apimodel.allowUnconditionalUpdate #kind
  {{{ (ret : bool), RET #ret;
      True
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
      KObjectV.deepown_l old_l old_obj dq ∗
      ⌜ should_delete = true →
        (KObjectV.objectmeta old_obj).(ObjectMetaV.DeletionTimestamp') ≠ None ⌝
  }}}.
Proof. Admitted.

End proof.
