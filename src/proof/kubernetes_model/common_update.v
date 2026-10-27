From New.proof Require Import prelude empty_ffi wp_keep.
From New.proof.kubernetes_model Require Export common admitted.
From New.proof.k8s_io.apiserver.pkg.registry Require Export rest.

(** Pod update contracts use the complete recursive view and the full-input
    defaulting/validation contracts in [PodAPI]. The upstream implementations
    remain trusted library boundaries. Other resources still have partial
    views and assume that validation of omitted fields succeeds; their
    reachable-memory footprints also need the recursive treatment used by Pod. *)

Local Transparent ObjectMetaV.deepown ObjectMetaView.ObjectMetaV.deepown.

Section proof.
Context `{hG: !heapGS Σ} `{!ffi_semantics _ _}.
Context {sem : go.Semantics} {package_sem : apimodel.Assumptions}.
Local Set Default Proof Using "All".


Lemma valid_update_equiv_except_resource_version kind namespace m1 m2 kspec input :
  ObjectMetaV.equiv_except_resource_version m1 m2 →
  KObjectV.valid_update kind namespace m1 kspec input →
  KObjectV.valid_update kind namespace m2 kspec input.
Proof.
  intros Heq Hvalid.
  assert (ObjectMetaV.valid_update m1 (KObjectV.objectmeta input) →
      ObjectMetaV.valid_update m2 (KObjectV.objectmeta input)) as Htransfer.
  { revert Heq.
    rewrite /ObjectMetaV.equiv_except_resource_version /ObjectMetaV.without_resource_version.
    destruct m1, m2; simpl. intros Heq. inversion Heq; subst. done. }
  assert (m1.(ObjectMetaV.Annotations') = m2.(ObjectMetaV.Annotations')) as Hannotations.
  { apply (f_equal ObjectMetaV.Annotations') in Heq. exact Heq. }
  destruct kspec, input; rewrite /KObjectV.valid_update /= in Hvalid Htransfer |- *;
    rewrite ?/PodV.valid_update ?/ReplicaSetV.valid_update
      ?/PersistentVolumeClaimV.valid_update ?/StatefulSetV.valid_update
      ?/DeploymentV.valid_update ?/ControllerRevisionV.valid_update in Hvalid |- *;
    try contradiction; rewrite -?Hannotations; intuition.
Qed.

(** Specialize the imported parser contract to a stored-valid resource version. *)
Local Transparent valid_resource_version.
Lemma wp_ParseUint_resource_version_valid (rv : go_string) :
  {{{ is_pkg_init strconv ∗
      ⌜ valid_resource_version rv ⌝
  }}}
    @! strconv.ParseUint #rv #(W64 10) #(W64 64)
  {{{ (ret : w64), RET (#ret, #interface.nil); True }}}.
Proof.
  iIntros (Φ) "(#Hinit & %Hvalid) HΦ".
  wp_apply (wp_ParseUint_decimal with "Hinit").
  iIntros (ret err) "(%Hparsed & _)".
  unfold valid_resource_version in Hvalid.
  rewrite (Hparsed Hvalid). iApply "HΦ". done.
Qed.
Local Opaque valid_resource_version.

Lemma wp_allowUnconditionalUpdate (kind : go_string) :
  {{{ is_pkg_init apimodel }}}
    @! apimodel.allowUnconditionalUpdate #kind
  {{{ (ret : bool) (err : error.t), RET (#ret, #err);
      True
  }}}.
Proof.
  wp_start as "#Hinit".
  wp_auto_keep.
  do 8 (wp_if_destruct; first (iApply "HΦ"; done)).
  wp_apply wp_slice_literal. iSplitR; first done.
  iIntros (args_sl) "[Hargs _]". wp_auto_keep.
  wp_apply (wp_Errorf with "[$Hargs]").
  iIntros (err) "_". wp_auto_keep.
  iApply "HΦ". done.
Qed.

(* Release updates may either retain a terminating object or delete it. *)
Lemma wp_shouldDeleteDuringUpdate_general
    new_i new_l new_obj old_i old_l old_obj dq :
  {{{ is_pkg_init apimodel ∗
      ⌜ KObjectV.valid_interface new_i new_l new_obj ⌝ ∗
      ⌜ KObjectV.valid_interface old_i old_l old_obj ⌝ ∗
      KObjectV.deepown_l new_l new_obj dq ∗
      KObjectV.deepown_l old_l old_obj dq
  }}}
    @! apimodel.shouldDeleteDuringUpdate #(interface.ok new_i) #(interface.ok old_i)
  {{{ (should_delete : bool), RET #should_delete;
      KObjectV.deepown_l new_l new_obj dq ∗
      KObjectV.deepown_l old_l old_obj dq ∗
      ⌜ should_delete = true → (KObjectV.objectmeta old_obj).(ObjectMetaV.DeletionTimestamp') ≠ None ⌝
  }}}.
Proof.
  wp_start as "(%Hnew_i & %Hold_i & Hnew & Hold)".
  assert (Hnew_runtime : go.type_set_contains new_i.(interface.ty)
      code.k8s_io.apimachinery.pkg.runtime.runtime.Object = true).
  { destruct new_obj; simpl in Hnew_i; destruct Hnew_i as [-> [_ Hruntime]]; done. }
  assert (Hold_runtime : go.type_set_contains old_i.(interface.ty)
      code.k8s_io.apimachinery.pkg.runtime.runtime.Object = true).
  { destruct old_obj; simpl in Hold_i; destruct Hold_i as [-> [_ Hruntime]]; done. }
  iDestruct (KObjectV.deepown_l_split with "Hnew") as
    "(%Hnew_not_null & Hnew_type & Hnew_meta & Hnew_spec & Hnew_status)".
  iDestruct (KObjectV.deepown_l_split with "Hold") as
    "(%Hold_not_null & Hold_type & Hold_meta & Hold_spec & Hold_status)".
  iDestruct "Hnew_meta" as (new_c) "[Hnew_meta Hnew_deepown]".
  iDestruct "Hold_meta" as (old_c) "[Hold_meta Hold_deepown]".
  iAssert (∀ b : bool,
      KObjectV.objectmeta_ptr new_l new_obj ↦{dq} new_c -∗
      KObjectV.objectmeta_ptr old_l old_obj ↦{dq} old_c -∗
      ObjectMetaV.deepown old_c (KObjectV.objectmeta old_obj) dq -∗
      ⌜ b = true → (KObjectV.objectmeta old_obj).(ObjectMetaV.DeletionTimestamp') ≠ None ⌝ -∗
      Φ #b)%I with
    "[HΦ Hnew_type Hnew_spec Hnew_status Hnew_deepown Hold_type Hold_spec Hold_status]" as "Hdone".
  { iIntros (b) "Hnew_meta Hold_meta Hold_deepown %Htimestamp".
    iApply "HΦ". iSplitL "Hnew_type Hnew_meta Hnew_spec Hnew_status Hnew_deepown".
    { iApply (KObjectV.deepown_l_restore new_l new_obj dq Hnew_not_null).
      iFrame "Hnew_type Hnew_spec Hnew_status". iExists new_c. iFrame. }
    iSplitL.
    { iApply (KObjectV.deepown_l_restore old_l old_obj dq Hold_not_null).
      iFrame "Hold_type Hold_spec Hold_status". iExists old_c. iFrame. }
    done. }
  wp_auto_keep.
  wp_func_call. wp_call. wp_auto_keep.
  rewrite Hnew_runtime. wp_auto_keep.
  rewrite Hold_runtime. wp_auto_keep.
  wp_func_call. wp_call. wp_auto_keep.
  wp_apply (wp_Accessor new_i new_l new_obj). { done. }
  wp_apply (wp_Accessor old_i old_l old_obj). { done. }
  wp_apply (wp_GetFinalizers_kobject new_i new_l new_obj new_c dq with "[$Hnew_meta]").
  { done. }
  iIntros "Hnew_meta". wp_auto_keep. wp_if_destruct.
  { iApply ("Hdone" $! false with "Hnew_meta Hold_meta Hold_deepown"). done. }
  wp_apply (wp_GetDeletionTimestamp_kobject old_i old_l old_obj old_c dq with "[$Hold_meta]").
  { done. }
  iIntros "Hold_meta". wp_auto_keep. wp_if_destruct.
  { iApply ("Hdone" $! false with "Hnew_meta Hold_meta Hold_deepown"). done. }
  iNamed "Hold_deepown".
  assert (Hold_timestamp : (KObjectV.objectmeta old_obj).(ObjectMetaV.DeletionTimestamp') ≠ None).
  { intros Hnone. pose proof (proj2 Hdeepown_deletiontimestamp_none Hnone). congruence. }
  wp_apply (wp_GetDeletionGracePeriodSeconds_kobject old_i old_l old_obj old_c dq with "[$Hold_meta]").
  { done. }
  iIntros "Hold_meta". wp_auto_keep. wp_if_destruct.
  { iApply ("Hdone" $! true with "Hnew_meta Hold_meta [-]").
    { rewrite /ObjectMetaV.deepown. iFrame. done. }
    done. }
  destruct (KObjectV.objectmeta old_obj).(ObjectMetaV.DeletionGracePeriodSeconds') as [seconds|] eqn:Hgrace.
  2: { exfalso. pose proof (proj2 Hdeepown_deletiongraceperiodseconds_none eq_refl). congruence. }
  iDestruct "Hdeepown_deletiongraceperiodseconds_some" as (cd) "[Hgrace %Hcd]". subst cd.
  wp_apply (wp_GetDeletionGracePeriodSeconds_kobject old_i old_l old_obj old_c dq with "[$Hold_meta]").
  { done. }
  iIntros "Hold_meta". wp_auto_keep.
  iApply ("Hdone" $! (bool_decide (seconds = W64 0)) with "Hnew_meta Hold_meta [-]").
  { rewrite /ObjectMetaV.deepown Hgrace /=. iFrame. done. }
  done.
Qed.

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
Proof.
  iIntros (Φ) "(#Hinit & %Hnew_i & %Hold_i & Hnew & Hold & %Hnone) HΦ".
  wp_apply (wp_shouldDeleteDuringUpdate_general with "[$Hinit $Hnew $Hold]").
  { done. }
  iIntros (b) "(Hnew & Hold & %Htimestamp)".
  assert (b = false) as ->.
  { destruct b; last done. exfalso. exact (Htimestamp eq_refl Hnone). }
  iApply "HΦ". iFrame.
Qed.

Context `{!kubernetesModelG Σ}.

(** Success follows from the stronger metadata-preservation contract. *)
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
Proof.
  iIntros (Φ) "Hpre HΦ".
  wp_apply (wp_applyValidationAndDefaultingOnStatusUpdate_ok_same_meta
    new_i new_l new_obj old_i old_l old_obj dq request_kind namespace input with "Hpre").
  iIntros (updated_obj) "(Hnew & Hold & Hinterface & Hupdated & _)".
  iApply ("HΦ" $! updated_obj). iFrame.
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
Proof.
  iIntros (Φ) "Hpre HΦ".
  wp_apply (wp_applyValidationAndDefaultingOnStatusUpdate_general_same_meta
    new_i new_l new_obj old_i old_l old_obj dq namespace with "Hpre").
  iIntros (err) "[Hsuccess | Hfailure]".
  - iDestruct "Hsuccess" as "(%Herr & %updated_obj & Hnew & Hold & Hinterface & Hupdated & _)".
    iApply ("HΦ" $! err). iLeft. iSplit; first done.
    iExists updated_obj. iFrame.
  - iApply ("HΦ" $! err). iRight. iExact "Hfailure".
Qed.

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
        ?/PersistentVolumeClaimV.valid_update ?/StatefulSetV.valid_update
        ?/DeploymentV.valid_update ?/ControllerRevisionV.valid_update in Hvalid_update;
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
        ?/DeploymentV.valid_status_update
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

Lemma kobject_updated_parent_ref {old_spec} input stored :
  KObjectV.updated old_spec input stored →
  obj_parent_ref stored = obj_parent_ref input.
Proof.
  intros Hupdated. rewrite /obj_parent_ref.
  assert ((KObjectV.objectmeta stored).(ObjectMetaV.Namespace') =
      (KObjectV.objectmeta input).(ObjectMetaV.Namespace')) as Hnamespace.
  { destruct old_spec, input, stored;
      rewrite /KObjectV.updated /PodV.updated /ReplicaSetV.updated
        /PersistentVolumeClaimV.updated /StatefulSetV.updated
        /DeploymentV.updated /= in Hupdated |- *;
      try done; destruct Hupdated as (_ & Hmeta & _);
      rewrite /ObjectMetaV.updated in Hmeta; tauto. }
  assert ((KObjectV.objectmeta stored).(ObjectMetaV.OwnerReferences') =
    (KObjectV.objectmeta input).(ObjectMetaV.OwnerReferences')) as Howners.
  { destruct old_spec, input, stored;
      rewrite /KObjectV.updated /PodV.updated /ReplicaSetV.updated
        /PersistentVolumeClaimV.updated /StatefulSetV.updated
        /DeploymentV.updated /= in Hupdated |- *;
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
        /PersistentVolumeClaimV.status_updated /StatefulSetV.status_updated
        /DeploymentV.status_updated /= in Hupdated |- *;
      try done; destruct Hupdated as (_ & Hmeta & _);
      rewrite /ObjectMetaV.updated in Hmeta; tauto. }
  assert ((KObjectV.objectmeta stored).(ObjectMetaV.OwnerReferences') =
      (KObjectV.objectmeta input).(ObjectMetaV.OwnerReferences')) as Howners.
  { destruct input, stored;
      rewrite /KObjectV.status_updated /PodV.status_updated /ReplicaSetV.status_updated
        /PersistentVolumeClaimV.status_updated /StatefulSetV.status_updated
        /DeploymentV.status_updated /= in Hupdated |- *;
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
      [tm1 meta1 spec1 status1]|[tm1 meta1 spec1 status1]|
      [tm1 meta1 spec1 status1]|[tm1 meta1 spec1 status1]],
    obj2 as [[tm2 meta2 spec2 status2]|[tm2 meta2 spec2 status2]|
      [tm2 meta2 spec2 status2]|[tm2 meta2 spec2 status2]|
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
      ?/PersistentVolumeClaimV.valid_update ?/StatefulSetV.valid_update
      ?/DeploymentV.valid_update ?/ControllerRevisionV.valid_update in Hvalid_update;
    try contradiction; tauto.
Qed.

(** A valid status update carries a valid TypeMeta. *)
Lemma valid_status_update_typemeta kind namespace kmeta kstatus kobj :
  KObjectV.valid_status_update kind namespace kmeta kstatus kobj →
  valid_typemeta (KObjectV.kind kobj) (KObjectV.typemeta kobj).
Proof.
  intros Hvalid_status_update.
  destruct kstatus, kobj; rewrite /KObjectV.valid_status_update /= in Hvalid_status_update;
    rewrite ?/PodV.valid_status_update ?/ReplicaSetV.valid_status_update
      ?/PersistentVolumeClaimV.valid_status_update ?/StatefulSetV.valid_status_update
      ?/DeploymentV.valid_status_update
      /ObjectMetaV.valid_update in Hvalid_status_update;
    try contradiction; tauto.
Qed.

(** A valid status update carries a valid resource version. *)
Lemma valid_status_update_resource_version kind namespace kmeta kstatus kobj :
  KObjectV.valid_status_update kind namespace kmeta kstatus kobj →
  valid_resource_version (KObjectV.objectmeta kobj).(ObjectMetaV.ResourceVersion').
Proof.
  intros Hvalid_status_update.
  destruct kstatus, kobj; rewrite /KObjectV.valid_status_update /= in Hvalid_status_update;
    rewrite ?/PodV.valid_status_update ?/ReplicaSetV.valid_status_update
      ?/PersistentVolumeClaimV.valid_status_update ?/StatefulSetV.valid_status_update
      ?/DeploymentV.valid_status_update
      /ObjectMetaV.valid_update in Hvalid_status_update;
    try contradiction; simpl; tauto.
Qed.

(** A valid status update names the object. *)
Lemma valid_status_update_name_nonempty kind namespace kmeta kstatus kobj :
  KObjectV.valid_status_update kind namespace kmeta kstatus kobj →
  (KObjectV.objectmeta kobj).(ObjectMetaV.Name') ≠ ""%go.
Proof.
  intros Hvalid_status_update.
  destruct kstatus, kobj; rewrite /KObjectV.valid_status_update /= in Hvalid_status_update;
    rewrite ?/PodV.valid_status_update ?/ReplicaSetV.valid_status_update
      ?/PersistentVolumeClaimV.valid_status_update ?/StatefulSetV.valid_status_update
      ?/DeploymentV.valid_status_update
      /ObjectMetaV.valid_update in Hvalid_status_update;
    try contradiction; simpl; tauto.
Qed.

(** A valid status update names the object's kind. *)
Lemma valid_status_update_kind kind namespace kmeta kstatus kobj :
  KObjectV.valid_status_update kind namespace kmeta kstatus kobj →
  kind = KObjectV.kind kobj.
Proof.
  intros Hvalid_status_update.
  destruct kstatus, kobj; rewrite /KObjectV.valid_status_update /= in Hvalid_status_update;
    rewrite ?/PodV.valid_status_update ?/ReplicaSetV.valid_status_update
      ?/PersistentVolumeClaimV.valid_status_update ?/StatefulSetV.valid_status_update
      ?/DeploymentV.valid_status_update
      /ObjectMetaV.valid_update in Hvalid_status_update;
    try contradiction; simpl; tauto.
Qed.

(** A valid status update is sent to the object's namespace. *)
Lemma valid_status_update_namespace kind namespace kmeta kstatus kobj :
  KObjectV.valid_status_update kind namespace kmeta kstatus kobj →
  namespace = (KObjectV.objectmeta kobj).(ObjectMetaV.Namespace').
Proof.
  intros Hvalid_status_update.
  destruct kstatus, kobj; rewrite /KObjectV.valid_status_update /= in Hvalid_status_update;
    rewrite ?/PodV.valid_status_update ?/ReplicaSetV.valid_status_update
      ?/PersistentVolumeClaimV.valid_status_update ?/StatefulSetV.valid_status_update
      ?/DeploymentV.valid_status_update
      /ObjectMetaV.valid_update in Hvalid_status_update;
    try contradiction; simpl; tauto.
Qed.

(** Every object kind allows an update without a resource version. *)
Lemma wp_allowUnconditionalUpdate_kind (kobj : KObjectV.t) :
  {{{ is_pkg_init apimodel }}}
    @! apimodel.allowUnconditionalUpdate #(KObjectV.kind kobj)
  {{{ RET (#true, #interface.nil); True }}}.
Proof.
  wp_start. wp_auto.
  destruct kobj; simpl; rewrite ?/PodV.kind ?/ReplicaSetV.kind ?/PersistentVolumeClaimV.kind
    ?/StatefulSetV.kind ?/DeploymentV.kind; wp_auto; by iApply "HΦ".
Qed.

(** The status-update guard depends on the stored metadata only up to its
    resource version. *)
Lemma valid_status_update_equiv_except_resource_version kind namespace m1 m2 kstatus input :
  ObjectMetaV.equiv_except_resource_version m1 m2 →
  KObjectV.valid_status_update kind namespace m1 kstatus input →
  KObjectV.valid_status_update kind namespace m2 kstatus input.
Proof.
  intros Heq Hvalid.
  assert (ObjectMetaV.valid_update m1 (KObjectV.objectmeta input) →
      ObjectMetaV.valid_update m2 (KObjectV.objectmeta input)) as Htransfer.
  { revert Heq.
    rewrite /ObjectMetaV.equiv_except_resource_version /ObjectMetaV.without_resource_version.
    destruct m1, m2; simpl. intros Heq. inversion Heq; subst. done. }
  destruct kstatus, input; rewrite /KObjectV.valid_status_update /= in Hvalid Htransfer |- *;
    rewrite ?/PodV.valid_status_update ?/ReplicaSetV.valid_status_update
      ?/PersistentVolumeClaimV.valid_status_update ?/StatefulSetV.valid_status_update
      ?/DeploymentV.valid_status_update in Hvalid |- *;
    try contradiction; intuition.
Qed.

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
        ?/DeploymentV.valid_status_update
        /ObjectMetaV.valid_update in Hvalid_status_update;
      try contradiction; tauto. }
  destruct Hprepared as (_ & _ & _ & ->).
  rewrite KObjectV.kind_update_objectmeta KObjectV.typemeta_update_objectmeta.
  exact Hvalid_typemeta_input.
Qed.

End proof.
