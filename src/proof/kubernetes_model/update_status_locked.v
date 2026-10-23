From New.proof Require Import prelude empty_ffi.
From New.proof.kubernetes_model Require Export update_status.
From New.proof Require Import wp_helpers.

Section proof.
Context `{hG: !heapGS Σ} `{!ffi_semantics _ _}.
Context {sem : go.Semantics} {package_sem : apimodel.Assumptions}.
Context `{!kubernetesModelG Σ}.
Local Set Default Proof Using "All".

(** The key that [updateStatusLocked] reads and writes: the request names the
    kind and namespace, and the object names itself. In
    kubernetes_model/apimodel/api_model.go:
<<
    name := metadata.GetName()
    key := KKey{Kind: kind, Name: name, Namespace: namespace}
>> *)
Definition update_status_key (kind namespace : go_string) (kobj : KObjectV.t) : KKey.t :=
  {| KKey.Kind' := kind;
     KKey.Name' := (KObjectV.objectmeta kobj).(ObjectMetaV.Name');
     KKey.Namespace' := namespace |}.

(** The request as validation sees it: in the request namespace and at the
    stored resource version. This is [objCopy] when validation runs:
<<
    rest.EnsureObjectNamespaceMatchesRequestNamespace(namespace, metadata) // sets the namespace
    if rv == "" { ...; metadata.SetResourceVersion(existingRv) }          // or rv == existingRv below
    applyValidationAndDefaultingOnStatusUpdate(objCopy, existingObjCopy, namespace)
>> *)
Definition update_status_prepared (namespace : go_string) (old kobj : KObjectV.t) : KObjectV.t :=
  KObjectV.update_objectmeta kobj
    ((KObjectV.objectmeta kobj) <| ObjectMetaV.Namespace' := namespace |>
       <| ObjectMetaV.ResourceVersion' := (KObjectV.objectmeta old).(ObjectMetaV.ResourceVersion') |>).

(** The stored object after a write: the validated request at the fresh
    resource version [rv].
<<
    metadata.SetResourceVersion(s.generateNewRVAndUpdate())
    s.m[key] = objCopy
>> *)
Definition update_status_stored (updated : KObjectV.t) (rv : go_string) : KObjectV.t :=
  KObjectV.update_objectmeta updated
    ((KObjectV.objectmeta updated) <| ObjectMetaV.ResourceVersion' := rv |>).

(** The store's interfaces own the abstract objects, as in [kubernetes_inv]. *)
Definition phys_abs_rep (phys_state : gmap KKey.t interface.t)
    (abs_state : gmap KKey.t KObjectV.t) : iProp Σ :=
  [∗ map] i; obj ∈ phys_state; abs_state,
    match i with
    | interface.ok i_ok => KObjectV.deepown_i i_ok obj 1
    | interface.nil => False%I
    end.

(** The reasons other than a conflict for which [updateStatusLocked] rejects a
    request: the namespaces differ, the name is empty, the key holds no object,
    the resource version is not valid, or the request is not a valid status
    update of the stored object. Each disjunct is a necessary condition of one
    error return. *)
Definition update_status_rejected (kind namespace : go_string) (kobj : KObjectV.t)
    (abs_state : gmap KKey.t KObjectV.t) : Prop :=
  (* if err = rest.EnsureObjectNamespaceMatchesRequestNamespace(namespace, metadata); err != nil {
       return nil, err
     }
     rejects only an object namespace that is set and differs from the request's. *)
  ((KObjectV.objectmeta kobj).(ObjectMetaV.Namespace') ≠ ""%go ∧
    (KObjectV.objectmeta kobj).(ObjectMetaV.Namespace') ≠ namespace) ∨
  (* if name == "" { return nil, errors.NewBadRequest(...) } *)
  (KObjectV.objectmeta kobj).(ObjectMetaV.Name') = ""%go ∨
  (* existingObj, exists := s.m[key]
     if !exists { return nil, errors.NewNotFound(...) } *)
  abs_state !! update_status_key kind namespace kobj = None ∨
  (* if rv == "" {
       allowUnconditional, err := allowUnconditionalUpdate(kind)
       if err != nil { return nil, err }
       ...
     } else {
       if _, err = parseResourceVersion(rv); err != nil {
         return nil, malformedUpdateResourceVersionError(err)
       }
     }
     rejects an empty resource version only for a kind without unconditional
     updates, and a non-empty one only when it does not parse. *)
  ¬ valid_resource_version (KObjectV.objectmeta kobj).(ObjectMetaV.ResourceVersion') ∨
  (* if err = applyValidationAndDefaultingOnStatusUpdate(objCopy, existingObjCopy, namespace); err != nil {
       return nil, err
     } *)
  (∃ old, abs_state !! update_status_key kind namespace kobj = Some old ∧
    ¬ KObjectV.valid_status_update kind namespace (KObjectV.objectmeta old) (KObjectV.status old) kobj).

(** What holds once [updateStatusLocked] has validated a request: [old] is
    stored at the request's key with the request's UID and kind, and validation
    turned the prepared request into [updated]. Each conjunct records a check
    that passed.

    Compare [KObjectV.valid_status_update], which a caller proves about its
    request before the call. This instead records what one call did, and
    neither implies the other: a valid request can still conflict, and Go may
    accept a request that the model does not call valid. A request that is also
    valid gets [KObjectV.status_updated] from the first conjunct of
    [applyValidationAndDefaultingOnStatusUpdate_updated]. *)
Definition update_status_validated (kind namespace : go_string) (kobj : KObjectV.t)
    (abs_state : gmap KKey.t KObjectV.t) (old updated : KObjectV.t) : Prop :=
  (* existingObj, exists := s.m[key]   // exists *)
  abs_state !! update_status_key kind namespace kobj = Some old ∧
  (* Not a check: every stored object is valid. *)
  KObjectV.valid old ∧
  (* Not a check: follows from [Hkind] once the UID check passes. *)
  KObjectV.kind kobj = kind ∧
  (* if uid := metadata.GetUID(); uidPrecondition && uid != "" && uid != existingMetadata.GetUID() {
       return nil, errors.NewConflict(...)
     }
     passes a non-empty request UID only when it is the stored one. *)
  (KObjectV.objectmeta old).(ObjectMetaV.UID') = (KObjectV.objectmeta kobj).(ObjectMetaV.UID') ∧
  (* rest.EnsureObjectNamespaceMatchesRequestNamespace(namespace, metadata) and
     if rv == "" { ...; metadata.SetResourceVersion(existingRv) }
     if rv != existingRv { return nil, errors.NewConflict(...) }
     prepare [objCopy] for validation as the helper contract expects, when the
     object namespace is unset or the request's. *)
  (((KObjectV.objectmeta kobj).(ObjectMetaV.Namespace') = ""%go ∨
    (KObjectV.objectmeta kobj).(ObjectMetaV.Namespace') = namespace) →
    update_prepared_for_helper namespace old kobj (update_status_prepared namespace old kobj)) ∧
  (* if err = applyValidationAndDefaultingOnStatusUpdate(objCopy, existingObjCopy, namespace); err != nil {
       return nil, err
     }
     returned nil and turned [objCopy] into [updated]. *)
  applyValidationAndDefaultingOnStatusUpdate_updated namespace old
    (update_status_prepared namespace old kobj) updated ∧
  applyValidationAndDefaultingOnStatusUpdate_meta_preserved namespace old
    (update_status_prepared namespace old kobj) updated.

Lemma update_status_prepared_key namespace old kobj :
  KObjectV.key (update_status_prepared namespace old kobj) =
    update_status_key (KObjectV.kind kobj) namespace kobj.
Proof. destruct kobj; done. Qed.

Lemma update_status_prepared_same_kind namespace old kobj o :
  KObjectV.kind o = KObjectV.kind kobj →
  KObjectV.same_kind o (update_status_prepared namespace old kobj).
Proof.
  intros Hkind. destruct o, kobj; simpl in Hkind |- *; try done;
    rewrite ?/PodV.kind ?/ReplicaSetV.kind ?/PersistentVolumeClaimV.kind
      ?/StatefulSetV.kind ?/DeploymentV.kind in Hkind; congruence.
Qed.

(** A write changes only the resource version of the validated object. *)
Lemma update_status_stored_equiv updated rv :
  update_objects_equiv_except_resource_version updated (update_status_stored updated rv).
Proof.
  rewrite /update_status_stored /update_objects_equiv_except_resource_version.
  destruct updated; simpl; split_and!; try done.
  all: rewrite /ObjectMetaV.equiv_except_resource_version
    /ObjectMetaV.without_resource_version; destruct ObjectMeta'; done.
Qed.

(** [allowUnconditionalUpdate] refuses only with an error. *)
Lemma wp_allowUnconditionalUpdate_nil_true (kind : go_string) :
  {{{ is_pkg_init apimodel }}}
    @! apimodel.allowUnconditionalUpdate #kind
  {{{ (ret : bool) (err : interface.t), RET (#ret, #err);
      ⌜ err = interface.nil → ret = true ⌝
  }}}.
Proof.
  wp_start as "#Hinit".
  wp_auto.
  do 7 (wp_if_destruct; first (iApply "HΦ"; done)).
  wp_apply wp_slice_literal. iSplitR; first done.
  iIntros (args_sl) "[Hargs _]". wp_auto.
  wp_apply (wp_Errorf with "[$Hargs]").
  iIntros (err) "_". wp_auto.
  iApply "HΦ". done.
Qed.

(** [wp_applyValidationAndDefaultingOnStatusUpdate_ok_same_meta] and
    [wp_applyValidationAndDefaultingOnStatusUpdate_general_same_meta] together:
    validation rejects only a request that is not a valid status update. *)
Lemma wp_applyValidationAndDefaultingOnStatusUpdate_same_meta_classic
    new_i new_l new_obj old_i old_l old_obj dq (request_kind namespace : go_string) input :
  {{{ is_pkg_init apimodel ∗
      ⌜ KObjectV.valid_interface new_i new_l new_obj ⌝ ∗
      ⌜ KObjectV.valid_interface old_i old_l old_obj ⌝ ∗
      ⌜ KObjectV.valid old_obj ⌝ ∗
      ⌜ KObjectV.same_kind old_obj new_obj ⌝ ∗
      ⌜ KObjectV.valid_status_update request_kind namespace
          (KObjectV.objectmeta old_obj) (KObjectV.status old_obj) input →
        update_prepared_for_helper namespace old_obj input new_obj ⌝ ∗
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
              namespace old_obj new_obj updated_obj ⌝ ∗
          ⌜ applyValidationAndDefaultingOnStatusUpdate_meta_preserved
              namespace old_obj new_obj updated_obj ⌝) ∨
      (⌜ err ≠ interface.nil ∧
          ¬ KObjectV.valid_status_update request_kind namespace
            (KObjectV.objectmeta old_obj) (KObjectV.status old_obj) input ⌝ ∗
        ∃ failed_obj,
          KObjectV.deepown_l new_l failed_obj 1 ∗
          KObjectV.deepown_l old_l old_obj dq ∗
          ⌜ KObjectV.valid_interface new_i new_l failed_obj ⌝)
  }}}.
Proof.
  iIntros (Φ) "(#Hpkg & %Hnew_i & %Hold_i & %Hvalid_old & %Hsame_kind & %Hprepared & Hnew & Hold) HΦ".
  destruct (Classical_Prop.classic (KObjectV.valid_status_update request_kind namespace
      (KObjectV.objectmeta old_obj) (KObjectV.status old_obj) input)) as [Hvalid|Hinvalid].
  - wp_apply (wp_applyValidationAndDefaultingOnStatusUpdate_ok_same_meta _ _ _ _ _ _ _
      request_kind namespace input with "[$Hnew $Hold]").
    { iFrame "#". iPureIntro. split_and!; try done. by apply Hprepared. }
    iIntros (updated_obj) "(Hnew & Hold & %Hupdated_i & %Hupdated & %Hpreserved)".
    iApply "HΦ". iLeft. iSplit; first done. iExists updated_obj. iFrame. done.
  - wp_apply (wp_applyValidationAndDefaultingOnStatusUpdate_general_same_meta with "[$Hnew $Hold]").
    { iFrame "#". iPureIntro. split_and!; done. }
    iIntros (err) "[(%Herr & H) | (%Herr & _ & H)]".
    + iApply "HΦ". iLeft. iSplit; first done. iExact "H".
    + iApply "HΦ". iRight. iSplit; first done. iExact "H".
Qed.

(** [updateStatusLocked] on the store's resources, without the lock or ghost
    fragments. The request UID must be non-empty, so the UID check applies, and
    a request that passes it must name the object's kind ([Hkind]), as
    validation compares objects of one kind. The call rejects the request and
    leaves the store unchanged, or validates it and then keeps the stored
    object, removes an object that is being deleted, or writes the validated
    object at a fresh resource version. The abstract state in [own_kview_auth]
    is left for the caller to update. [updateStatus] calls it as
<<
    s.mu.Lock()
    defer s.mu.Unlock()
    return s.updateStatusLocked(kind, namespace, obj, true)
>> *)
Lemma wp_State__updateStatusLocked γ l (kind namespace : go_string) i kobj
    phys_state_l phys_state abs_state used_uid used_rv_l used_rv :
  {{{ is_pkg_init apimodel ∗
      (* uid != "" in the UID check, so the check applies. *)
      "%Huid_nonempty" ∷ ⌜ (KObjectV.objectmeta kobj).(ObjectMetaV.UID') ≠ ""%go ⌝ ∗
      (* applyValidationAndDefaultingOnStatusUpdate(objCopy, existingObjCopy, namespace)
         gets objects of one kind: the request names the object's kind, or the
         UID check rejects every object at the requested key. *)
      "%Hkind" ∷ ⌜ kind = KObjectV.kind kobj ∨
        ∀ old, abs_state !! update_status_key kind namespace kobj = Some old →
          (KObjectV.objectmeta old).(ObjectMetaV.UID') ≠ (KObjectV.objectmeta kobj).(ObjectMetaV.UID') ⌝ ∗
      "Hdeepown_i" ∷ KObjectV.deepown_i i kobj 1 ∗
      "Hstate_m_addr" ∷ l.[(apimodel.State.t), "m"] ↦ phys_state_l ∗
      "Hstate_used_rv_addr" ∷ l.[(apimodel.State.t), "usedRV"] ↦ used_rv_l ∗
      "Hown_phys" ∷ phys_state_l ↦$ phys_state ∗
      "Hown_used_rv" ∷ used_rv_l ↦$ used_rv ∗
      "Hown_abs" ∷ own_kview_auth γ abs_state used_uid ∗
      "Hphys_abs_rep" ∷ phys_abs_rep phys_state abs_state
  }}}
    l @! (go.PointerType apimodel.State) @! "updateStatusLocked" #kind #namespace #(interface.ok i) #true
  {{{ (ret err : interface.t), RET (#ret, #err);
      KObjectV.deepown_i i kobj 1 ∗
      l.[(apimodel.State.t), "m"] ↦ phys_state_l ∗
      l.[(apimodel.State.t), "usedRV"] ↦ used_rv_l ∗
      own_kview_auth γ abs_state used_uid ∗
      (* return nil, err: a conflict from the UID check or from
         if rv != existingRv { return nil, errors.NewConflict(...) }
         or one of the other rejections. *)
      ((⌜ ret = interface.nil ∧ err ≠ interface.nil ∧
          (conflict_error err ∨ update_status_rejected kind namespace kobj abs_state) ⌝ ∗
        phys_state_l ↦$ phys_state ∗
        used_rv_l ↦$ used_rv ∗
        phys_abs_rep phys_state abs_state) ∨
       (* if storageObjectDeepEqual(objCopy, existingObjCopy) { return existingObjCopy, nil } *)
       (∃ i' old updated,
        ⌜ ret = interface.ok i' ∧ err = interface.nil ∧
          update_status_validated kind namespace kobj abs_state old updated ∧
          storage_object_normalize updated = storage_object_normalize old ⌝ ∗
        KObjectV.deepown_i i' old 1 ∗
        phys_state_l ↦$ phys_state ∗
        used_rv_l ↦$ used_rv ∗
        phys_abs_rep phys_state abs_state) ∨
       (* if shouldDeleteDuringUpdate(objCopy, existingObjCopy) {
            delete(s.m, key)
            return objCopy, nil
          } *)
       (∃ i' old updated,
        ⌜ ret = interface.ok i' ∧ err = interface.nil ∧
          update_status_validated kind namespace kobj abs_state old updated ∧
          (KObjectV.objectmeta old).(ObjectMetaV.DeletionTimestamp') ≠ None ⌝ ∗
        KObjectV.deepown_i i' updated 1 ∗
        phys_state_l ↦$ delete (update_status_key kind namespace kobj) phys_state ∗
        used_rv_l ↦$ used_rv ∗
        phys_abs_rep (delete (update_status_key kind namespace kobj) phys_state)
          (delete (update_status_key kind namespace kobj) abs_state)) ∨
       (* metadata.SetResourceVersion(s.generateNewRVAndUpdate())
          s.m[key] = objCopy
          return deepCopy(objCopy), nil *)
       (∃ i' i_new old updated rv,
        ⌜ ret = interface.ok i' ∧ err = interface.nil ∧
          update_status_validated kind namespace kobj abs_state old updated ∧
          used_rv !! rv = None ∧ valid_resource_version rv ⌝ ∗
        KObjectV.deepown_i i' (update_status_stored updated rv) 1 ∗
        phys_state_l ↦$ <[update_status_key kind namespace kobj := interface.ok i_new]> phys_state ∗
        used_rv_l ↦$ <[rv := ()]> used_rv ∗
        phys_abs_rep (<[update_status_key kind namespace kobj := interface.ok i_new]> phys_state)
          (<[update_status_key kind namespace kobj := update_status_stored updated rv]> abs_state)))
  }}}.
Proof.
  wp_start as "H". iNamed "H".
  wp_auto.
  wp_apply (wp_deepCopy i kobj (DfracOwn 1) with "[Hdeepown_i]").
  { iFrame "#". iExact "Hdeepown_i". }
  iIntros (i1) "[Hdeepown_i1 Hdeepown_i]". wp_auto.
  iDestruct "Hdeepown_i1" as (l1) "[%Hvalid_interface Hdeepown_l]".
  wp_apply wp_Accessor. 1: iPureIntro; done.
  iPoseProof (KObjectV.deepown_l_split with "Hdeepown_l") as
    "(%Hl1_not_null & Hdeepown_t_l & Hdeepown_m_l & Hdeepown_s_l & Hdeepown_st_l)".
  wp_apply (wp_EnsureObjectNamespaceMatchesRequestNamespace_general with "[$Hdeepown_m_l]").
  { iPureIntro. done. }
  iIntros (err_ns) "[[%Herr_ns_nil Hdeepown_m_l] | (%Herr_ns_ne & %Hns_set & %Hns_ne)]".
  2: {
    (* Namespaces that are both set and differ are rejected. *)
    destruct err_ns as [err_ns_ok|]; [|done]. wp_auto.
    iApply "HΦ". iFrame. iLeft. iFrame. iPureIntro.
    split_and!; [done|done|]. right. left. done. }
  subst err_ns. wp_auto.
  wp_apply (wp_GetName_deepown_kobject i1 l1 kobj with "[$Hdeepown_m_l]"). 1: done.
  iIntros "Hdeepown_m_l". wp_auto.
  simpl.
  destruct (decide (ObjectMetaV.Name' (KObjectV.objectmeta kobj) = ""%go)) as [Hname_empty|Hname_nonempty].
  { (* A request without a name is rejected as a bad request before the lookup. *)
    rewrite (bool_decide_true _ Hname_empty). wp_auto.
    wp_apply wp_slice_literal. iSplitR; first done.
    iIntros (reason_args_sl) "[Hreason_args _]". wp_auto.
    wp_apply (wp_fmt_Sprintf with "[$Hreason_args]").
    iIntros (reason) "_". wp_auto.
    wp_apply wp_NewBadRequest.
    iIntros (err_l) "_". wp_auto.
    iApply "HΦ". iFrame. iLeft. iFrame. iPureIntro.
    split_and!; [done|done|]. right. right. left. done. }
  rewrite bool_decide_false //. wp_auto.
  wp_apply (wp_map_lookup2 apimodel.KKey (go.InterfaceType []) with "[$Hown_phys]").
  iIntros "Hown_phys". wp_auto.
  iDestruct (big_sepM2_dom with "Hphys_abs_rep") as %Hdom_eq.
  set key := {|
    KKey.Kind' := kind;
    KKey.Name' := ObjectMetaV.Name' (KObjectV.objectmeta kobj);
    KKey.Namespace' := namespace
  |}.
  assert (update_status_key kind namespace kobj = key) as Hkey_eq by done.
  rewrite Hkey_eq in Hkind |- *.
  destruct (bool_decide (is_Some (phys_state !! key))) eqn:Hdecide.
  2: {
    (* The requested key holds no object. *)
    apply bool_decide_eq_false in Hdecide.
    assert (abs_state !! key = None) as Hlookup_abs_none.
    { apply not_elem_of_dom. rewrite <- Hdom_eq. apply not_elem_of_dom.
      destruct (phys_state !! key) eqn:Hlookup_phys; [|done].
      exfalso. apply Hdecide. done. }
    wp_auto.
    wp_apply (wp_NewNotFound
      {| schema.GroupResource.Group' := ""%go;
         schema.GroupResource.Resource' := kind |}
      (ObjectMetaV.Name' (KObjectV.objectmeta kobj))).
    iIntros (err_l) "%Hnot_found". wp_auto.
    pose proof (not_found_error_not_nil _ Hnot_found) as Herr_not_nil.
    iApply "HΦ". iFrame. iLeft. iFrame. iPureIntro.
    split_and!; [done|done|]. right. right. right. left. done. }
  assert (∃ old_i, phys_state !! key = Some old_i) as [old_i Hlookup_phys].
  { apply bool_decide_eq_true in Hdecide. done. }
  assert (∃ old_kobj, abs_state !! key = Some old_kobj) as [old_kobj Hlookup_abs].
  { apply elem_of_dom. rewrite <- Hdom_eq. apply elem_of_dom. eexists. done. }
  iDestruct (big_sepM2_lookup_acc _ _ _ _ _ _ Hlookup_phys Hlookup_abs with "Hphys_abs_rep")
    as "(Hdeepown_old_i & Hrep_close)".
  destruct old_i as [old_i|].
  2: { iExFalso. iExact "Hdeepown_old_i". }
  rewrite Hlookup_phys. wp_auto.
  wp_apply (wp_deepCopy old_i old_kobj (DfracOwn 1) with "[Hdeepown_old_i]").
  { iFrame "#". iExact "Hdeepown_old_i". }
  iIntros (old_i1) "[Hdeepown_old_i1 Hdeepown_old_i]". wp_auto.
  iDestruct ("Hrep_close" with "Hdeepown_old_i") as "Hphys_abs_rep".
  iDestruct "Hdeepown_old_i1" as (old_l1) "[%Hvalid_interface_old Hdeepown_old_l]".
  wp_apply wp_Accessor. 1: iPureIntro; done.
  iPoseProof (KObjectV.deepown_l_split with "Hdeepown_old_l") as
    "(%Hold_l1_not_null & Hdeepown_t_old_l & Hdeepown_m_old_l & Hdeepown_s_old_l & Hdeepown_st_old_l)".
  iPoseProof (kview.own_auth_valid2 key old_kobj with "Hown_abs") as "%Hauth_old".
  1: done.
  destruct Hauth_old as (Hkey_old & Hvalid_old_kobj & _ & _ & _).
  wp_apply (wp_GetUID_deepown_kobject i1 l1 kobj with "[$Hdeepown_m_l]"). 1: done.
  iIntros "Hdeepown_m_l". wp_auto.
  simpl.
  wp_if_destruct.
  1: { exfalso. done. }
  rewrite bool_decide_false //. wp_auto.
  wp_apply (wp_GetUID_deepown_kobject old_i1 old_l1 old_kobj with
    "[$Hdeepown_m_old_l]"). 1: done.
  iIntros "Hdeepown_m_old_l". wp_auto.
  wp_if_destruct.
  2: {
    (* The UID check reports a conflict. *)
    wp_apply (wp_GetUID_deepown_kobject old_i1 old_l1 old_kobj with
      "[$Hdeepown_m_old_l]"). 1: done.
    iIntros "Hdeepown_m_old_l". wp_auto.
    wp_apply wp_slice_literal. iSplitR; first done.
    iIntros (error_args_sl) "[Herror_args _]". wp_auto.
    wp_apply (wp_Errorf with "[$Herror_args]").
    iIntros (error_cause) "_". wp_auto.
    wp_apply (wp_NewConflict
      {| schema.GroupResource.Group' := ""%go;
         schema.GroupResource.Resource' := kind |}
      (ObjectMetaV.Name' (KObjectV.objectmeta kobj)) (interface.ok error_cause)).
    iIntros (err_l) "%Herr_conflict". wp_auto.
    pose proof (conflict_error_not_nil _ Herr_conflict) as Herr_not_nil.
    iApply "HΦ". iFrame. iLeft. iFrame. iPureIntro.
    split_and!; [done|done|]. left. done. }
  (* A request that passes the UID check carries the stored UID, so it names
     the stored object's kind. *)
  assert (KObjectV.kind kobj = kind) as Hkind_eq.
  { destruct Hkind as [Hkind|Hkind]; first done.
    exfalso. apply (Hkind old_kobj Hlookup_abs). symmetry. exact e. }
  wp_apply (wp_GetResourceVersion_deepown_kobject i1 l1 kobj with
    "[$Hdeepown_m_l]"). 1: done.
  iIntros "Hdeepown_m_l". wp_auto.
  wp_apply (wp_GetResourceVersion_deepown_kobject old_i1 old_l1 old_kobj with
    "[$Hdeepown_m_old_l]"). 1: done.
  iIntros "Hdeepown_m_old_l". wp_auto.
  (* An empty request resource version is replaced by the stored one, and any
     other one must parse; both branches continue at some resource version. *)
  wp_bind (If _ _ _).
  iApply (wp_wand _ _ _ (λ v,
    (⌜ v = execute_val ⌝ ∗ ∃ (rv_cur : go_string) (err_v : interface.t),
      "rv" ∷ rv_ptr ↦ ObjectMetaV.ResourceVersion' (KObjectV.objectmeta kobj) ∗
      "kind" ∷ kind_ptr ↦ kind ∗
      "metadata" ∷ metadata_ptr ↦ interface.ok i1 ∗
      "existingRv" ∷ existingRv_ptr ↦ ObjectMetaV.ResourceVersion' (KObjectV.objectmeta old_kobj) ∗
      "err" ∷ err_ptr ↦ err_v ∗
      "Hdeepown_m_l" ∷ ObjectMetaV.deepown_l (KObjectV.objectmeta_ptr l1 kobj)
        (KObjectV.objectmeta kobj <| ObjectMetaV.Namespace' := namespace |>
          <| ObjectMetaV.ResourceVersion' := rv_cur |>) (DfracOwn 1) ∗
      "%Hrv_cur" ∷ ⌜ ObjectMetaV.ResourceVersion' (KObjectV.objectmeta kobj) = ""%go ∨
        rv_cur = ObjectMetaV.ResourceVersion' (KObjectV.objectmeta kobj) ⌝) ∨
    (∃ err_v, ⌜ v = return_val (#interface.nil, #err_v)%V ⌝ ∗ ⌜ err_v ≠ interface.nil ⌝ ∗
      ⌜ ¬ valid_resource_version (ObjectMetaV.ResourceVersion' (KObjectV.objectmeta kobj)) ⌝))%I
    with "[rv kind metadata existingRv err Hdeepown_m_l]").
  { assert (KObjectV.objectmeta kobj <| ObjectMetaV.Namespace' := namespace |>
        <| ObjectMetaV.ResourceVersion' := ObjectMetaV.ResourceVersion' (KObjectV.objectmeta kobj) |> =
      KObjectV.objectmeta kobj <| ObjectMetaV.Namespace' := namespace |>) as Hrv_noop.
    { destruct (KObjectV.objectmeta kobj). done. }
    destruct (decide (ObjectMetaV.ResourceVersion' (KObjectV.objectmeta kobj) = ""%go))
      as [Hrv_empty|Hrv_nonempty].
    - rewrite (bool_decide_eq_true_2 _ Hrv_empty). wp_auto.
      (* This branch declares its own [err], which [wp_auto] does not allocate. *)
      wp_alloc err_branch_ptr as "err_branch". wp_auto.
      wp_apply wp_allowUnconditionalUpdate_nil_true.
      iIntros (allow err_allow) "%Hallow". wp_auto.
      destruct err_allow as [err_allow_ok|].
      + (* The kind does not allow an update without a resource version. *)
        wp_auto. iRight. iExists (interface.ok err_allow_ok). iPureIntro.
        split_and!; [done|done|].
        intros Hrv_valid. apply (valid_resource_version_non_empty _ Hrv_valid). exact Hrv_empty.
      + rewrite (Hallow eq_refl). wp_auto.
        wp_apply (wp_SetResourceVersion_deepown_kobject i1 l1 kobj with "[$Hdeepown_m_l]"). 1: done.
        iIntros "Hdeepown_m_l". wp_auto.
        iLeft. iSplit; first done. iExists _, interface.nil. iFrame. iPureIntro. left. done.
    - rewrite (bool_decide_eq_false_2 _ Hrv_nonempty). wp_auto.
      destruct (Classical_Prop.classic (valid_resource_version
          (ObjectMetaV.ResourceVersion' (KObjectV.objectmeta kobj)))) as [Hrv_valid|Hrv_invalid].
      + wp_apply wp_parseResourceVersion.
        { iPureIntro. exact Hrv_valid. }
        iIntros (ret) "_". wp_auto.
        iLeft. iSplit; first done.
        iExists (ObjectMetaV.ResourceVersion' (KObjectV.objectmeta kobj)), interface.nil.
        rewrite Hrv_noop. iFrame. iPureIntro. right. done.
      + wp_apply wp_parseResourceVersion_general.
        iIntros (ret err_parse) "_". wp_auto.
        destruct err_parse as [err_parse_ok|]; wp_auto.
        * (* A resource version that does not parse is rejected. *)
          wp_apply (wp_malformedUpdateResourceVersionError (interface.ok err_parse_ok)).
          { iPureIntro. done. }
          iIntros (err_malformed) "%Herr_malformed_ne". wp_auto.
          iRight. iExists err_malformed. done.
        * iLeft. iSplit; first done.
          iExists (ObjectMetaV.ResourceVersion' (KObjectV.objectmeta kobj)), interface.nil.
          rewrite Hrv_noop. iFrame. iPureIntro. right. done. }
  iIntros (v) "[(-> & %rv_cur & %err_v & H) | (%err_v & -> & %Herr_v_ne & %Hrv_invalid)]".
  2: {
    wp_auto.
    iApply "HΦ". iFrame. iLeft. iFrame. iPureIntro.
    split_and!; [done|done|]. right. right. right. right. left. done. }
  iNamed "H". wp_auto.
  wp_apply (wp_GetResourceVersion_deepown_kobject i1 l1 kobj with
    "[$Hdeepown_m_l]"). 1: done.
  iIntros "Hdeepown_m_l". wp_auto.
  wp_if_destruct.
  2: {
    (* The resource version check reports a conflict. *)
    wp_apply wp_slice_literal. iSplitR; first done.
    iIntros (error_args_sl) "[Herror_args _]". wp_auto.
    wp_apply (wp_Errorf with "[$Herror_args]").
    iIntros (error_cause) "_". wp_auto.
    wp_apply (wp_NewConflict
      {| schema.GroupResource.Group' := ""%go;
         schema.GroupResource.Resource' := KObjectV.kind kobj |}
      (ObjectMetaV.Name' (KObjectV.objectmeta kobj)) (interface.ok error_cause)).
    iIntros (err_l) "%Herr_conflict". wp_auto.
    pose proof (conflict_error_not_nil _ Herr_conflict) as Herr_not_nil.
    iApply "HΦ". iFrame. iLeft. iFrame. iPureIntro.
    split_and!; [done|done|]. left. done. }
  (* Validation sees the request in the request namespace and at the stored
     resource version. *)
  iPoseProof (KObjectV.deepown_l_restore _ _ _ Hold_l1_not_null with
    "[$Hdeepown_t_old_l $Hdeepown_m_old_l $Hdeepown_s_old_l $Hdeepown_st_old_l]") as "Hdeepown_old_l".
  iPoseProof (KObjectV.deepown_l_merge _ _ _ _ Hl1_not_null with
    "[$Hdeepown_t_l $Hdeepown_m_l $Hdeepown_s_l $Hdeepown_st_l]") as "Hdeepown_l".
  assert (KObjectV.kind old_kobj = KObjectV.kind kobj) as Hkind_old.
  { assert (KKey.Kind' (KObjectV.key old_kobj) = KObjectV.kind old_kobj) as Hkind_key
      by (destruct old_kobj; done).
    rewrite -Hkind_key -Hkey_old. done. }
  assert (((KObjectV.objectmeta kobj).(ObjectMetaV.Namespace') = ""%go ∨
      (KObjectV.objectmeta kobj).(ObjectMetaV.Namespace') = namespace) →
    update_prepared_for_helper namespace old_kobj kobj (update_status_prepared namespace old_kobj kobj))
    as Hprepared.
  { intros Hns. rewrite /update_prepared_for_helper. split_and!.
    - exact Hns.
    - destruct Hrv_cur as [Hrv_empty|Hrv_eq]; [left; exact Hrv_empty|right; symmetry; exact Hrv_eq].
    - rewrite update_status_prepared_key -Hkey_old. done.
    - done. }
  wp_apply (wp_applyValidationAndDefaultingOnStatusUpdate_same_meta_classic
    i1 l1 (update_status_prepared namespace old_kobj kobj) old_i1 old_l1 old_kobj (DfracOwn 1)
    (KObjectV.kind kobj) namespace kobj with "[$Hdeepown_l $Hdeepown_old_l]").
  { iFrame "#". iPureIntro. split_and!.
    - rewrite /update_status_prepared. destruct kobj; exact Hvalid_interface.
    - done.
    - done.
    - apply update_status_prepared_same_kind. exact Hkind_old.
    - intros Hvalid_status_update. apply Hprepared. right. symmetry.
      eapply valid_status_update_namespace. exact Hvalid_status_update. }
  iIntros (err) "[(-> & %updated & Hdeepown_l & Hdeepown_old_l & %Hvalid_interface_updated &
    %Hupdated & %Hpreserved) | ((%Herr_ne & %Hinvalid) & %failed & Hdeepown_l & Hdeepown_old_l & _)]".
  2: {
    (* Validation rejects a request that is not a valid status update. *)
    destruct err as [err_ok|]; [|done]. wp_auto.
    iApply "HΦ". iFrame. iLeft. iFrame. iPureIntro.
    split_and!; [done|done|]. right. right. right. right. right.
    exists old_kobj. split; done. }
  wp_auto.
  assert (update_status_validated (KObjectV.kind kobj) namespace kobj abs_state old_kobj updated)
    as Hvalidated.
  { rewrite /update_status_validated. split_and!; done. }
  wp_apply (wp_shouldDeleteDuringUpdate_general with "[$Hdeepown_l $Hdeepown_old_l]").
  { iFrame "#". iPureIntro. split; done. }
  iIntros (should_delete) "(Hdeepown_l & Hdeepown_old_l & %Hshould_delete)".
  destruct should_delete; wp_auto.
  { (* An object that is being deleted is removed. *)
    iDestruct (big_sepM2_delete _ phys_state abs_state key _ _ Hlookup_phys Hlookup_abs
      with "Hphys_abs_rep") as "(_ & Hother_rep)".
    wp_apply (wp_map_delete _ _ key apimodel.KKey (go.InterfaceType []) with "[$Hown_phys]").
    iIntros "Hown_phys". wp_auto.
    iAssert (KObjectV.deepown_i i1 updated 1) with "[Hdeepown_l]" as "Hdeepown_i1".
    { iExists l1. iFrame. done. }
    iApply "HΦ". iFrame. iRight. iRight. iLeft. iExists i1, old_kobj, updated. iFrame.
    iPureIntro. split_and!; try done. by apply Hshould_delete. }
  wp_apply (wp_storageObjectDeepEqual with "[$Hdeepown_l $Hdeepown_old_l]").
  { iPureIntro. split_and!. all: done. }
  iIntros (v) "(Hdeepown_i1 & Hdeepown_old_i1 & %Hifv)".
  wp_if_destruct.
  { (* The validated object stores the same as the stored one, which is kept. *)
    iApply "HΦ". iFrame. iRight. iLeft. iExists old_i1, old_kobj, updated. iFrame.
    iPureIntro. split_and!; try done. by apply Hifv. }
  wp_apply (wp_State__generateNewRVAndUpdate with "[$Hstate_used_rv_addr $Hown_used_rv]").
  iIntros (rv) "(%Hlookup_used_rv & %Hvalid_rv & Hstate_used_rv_addr & Hown_used_rv)". wp_auto.
  iPoseProof (KObjectV.deepown_i_yields_deepown_l with "[$Hdeepown_i1]") as "Hdeepown_l". 1: done.
  iPoseProof (KObjectV.deepown_l_split with "Hdeepown_l") as
    "(%Hl1_not_null1 & Hdeepown_t_l & Hdeepown_m_l & Hdeepown_s_l & Hdeepown_st_l)".
  wp_apply (wp_SetResourceVersion_deepown_kobject i1 l1 updated with
    "[$Hdeepown_m_l]"). 1: done.
  iIntros "Hdeepown_m_l". wp_auto.
  wp_apply (wp_map_insert apimodel.KKey with "[$Hown_phys]"). iIntros "Hown_phys". wp_auto.
  iPoseProof (KObjectV.deepown_l_merge _ _ _ _ Hl1_not_null1 with
    "[$Hdeepown_t_l $Hdeepown_m_l $Hdeepown_s_l $Hdeepown_st_l]") as "Hdeepown_l".
  wp_apply (wp_deepCopy i1 (update_status_stored updated rv) (DfracOwn 1) with "[Hdeepown_l]").
  { iFrame. iPureIntro. rewrite /update_status_stored. destruct updated; done. }
  iIntros (i1') "[Hdeepown_i1' Hdeepown_i1]". wp_auto.
  iDestruct (big_sepM2_delete _ phys_state abs_state key _ _ Hlookup_phys Hlookup_abs
    with "Hphys_abs_rep") as "(_ & Hother_rep)".
  iApply "HΦ". iFrame. iRight. iRight. iRight. iExists i1', i1, old_kobj, updated, rv. iFrame.
  iSplit; first (iPureIntro; split_and!; done).
  rewrite /phys_abs_rep big_sepM2_insert_delete. iFrame.
Unshelve.
all: try apply _.
all: try done.
Qed.

End proof.
