From New.proof Require Import prelude empty_ffi.
From New.proof.kubernetes_model Require Export update_status_locked.
From New.proof Require Import wp_helpers.

Section proof.
Context `{hG: !heapGS Σ} `{!ffi_semantics _ _}.
Context {sem : go.Semantics} {package_sem : apimodel.Assumptions}.
Context `{!kubernetesModelG Σ}.
Local Set Default Proof Using "All".

(** Metadata that agrees except for the resource version is a simple update. *)
Lemma equiv_except_resource_version_valid_simple_update m m' :
  ObjectMetaV.equiv_except_resource_version m' m →
  ObjectMetaV.valid_simple_update m m'.
Proof.
  rewrite /ObjectMetaV.equiv_except_resource_version /ObjectMetaV.without_resource_version
    /ObjectMetaV.valid_simple_update.
  destruct m, m'; simpl. intros Heq. inversion Heq; subst. split_and!; done.
Qed.

(** Identity facts a status writer can read off a metadata fragment at any
    fraction, when the submitted metadata keeps the stored metadata except for
    the resource version. *)
Lemma own_meta_frag_status_identity γ key uid dq kmeta kobj :
  ObjectMetaV.equiv_except_resource_version (KObjectV.objectmeta kobj) kmeta →
  own_meta_frag γ key uid dq kmeta -∗
  ⌜ uid = (KObjectV.objectmeta kobj).(ObjectMetaV.UID') ∧
    kmeta.(ObjectMetaV.DeletionTimestamp') = None ⌝.
Proof.
  iIntros (Hmeta_same) "Hmeta".
  rewrite /own_meta_frag.
  iPoseProof (kview.own_meta_valid with "Hmeta") as
    "(_ & _ & %Huid_meta & _ & %Hmeta_living)".
  iPureIntro. split; last done.
  rewrite Huid_meta.
  pose proof (equiv_except_resource_version_valid_simple_update _ _ Hmeta_same) as Hsimple.
  rewrite /ObjectMetaV.valid_simple_update in Hsimple. symmetry. tauto.
Qed.

(** A request that keeps the stored metadata except for the resource version
    carries the stored UID, which is non-empty. *)
Lemma own_meta_frag_request_uid_nonempty γ key uid dq kmeta kobj :
  ObjectMetaV.equiv_except_resource_version (KObjectV.objectmeta kobj) kmeta →
  own_meta_frag γ key uid dq kmeta -∗
  ⌜ (KObjectV.objectmeta kobj).(ObjectMetaV.UID') ≠ ""%go ⌝.
Proof.
  iIntros (Hmeta_same) "Hmeta".
  iDestruct (own_meta_frag_status_identity _ _ _ _ _ kobj Hmeta_same with "Hmeta") as
    %[Huid_kobj _].
  rewrite /own_meta_frag.
  iPoseProof (kview.own_meta_valid with "Hmeta") as
    "(_ & _ & %Huid_meta & %Hvalid_meta & _)".
  iPureIntro. rewrite -Huid_kobj Huid_meta.
  destruct Hvalid_meta as (_ & _ & _ & _ & _ & Hvalid_uid & _).
  apply valid_uid_non_empty. exact Hvalid_uid.
Qed.

(** What a request that names its own key and keeps the stored metadata except
    for the resource version learns once [updateStatusLocked] has validated it
    against [old]: [old] is the object that the fragments describe. *)
Lemma update_status_same_meta_validated γ (kind namespace : go_string) kobj abs_state used_uid
    old updated uid dq kmeta kstatus :
  update_status_key kind namespace kobj = KObjectV.key kobj →
  ObjectMetaV.equiv_except_resource_version (KObjectV.objectmeta kobj) kmeta →
  update_status_validated kind namespace kobj abs_state old updated →
  own_kview_auth γ abs_state used_uid -∗
  own_meta_frag γ (KObjectV.key kobj) uid dq kmeta -∗
  own_status_frag γ (KObjectV.key kobj) uid 1 kstatus -∗
  ⌜ abs_state !! KObjectV.key kobj = Some old ∧
    uid = (KObjectV.objectmeta kobj).(ObjectMetaV.UID') ∧
    (KObjectV.objectmeta old).(ObjectMetaV.DeletionTimestamp') = None ∧
    ObjectMetaV.equiv_except_resource_version (KObjectV.objectmeta old) kmeta ∧
    KObjectV.status old = kstatus ∧
    update_prepared_for_helper namespace old kobj (update_status_prepared namespace old kobj) ∧
    (KObjectV.objectmeta kobj).(ObjectMetaV.Namespace') = namespace ∧
    ObjectMetaV.valid_simple_update (KObjectV.objectmeta old) (KObjectV.objectmeta kobj) ⌝.
Proof.
  iIntros (Hkey Hmeta_same Hvalidated) "Hown_abs Hown_meta_frag Hown_status_frag".
  destruct Hvalidated as (Hlookup & _ & _ & _ & Hprepared & _ & _).
  rewrite Hkey in Hlookup.
  assert ((KObjectV.objectmeta kobj).(ObjectMetaV.Namespace') = namespace) as Hns.
  { pose proof (f_equal KKey.Namespace' Hkey) as Hns.
    rewrite /update_status_key in Hns. destruct kobj; simpl in Hns; done. }
  iDestruct (own_meta_frag_status_identity _ _ _ _ _ kobj Hmeta_same with "Hown_meta_frag")
    as %[Huid_eq _].
  iDestruct (kview.own_meta_exists2 Hlookup with "Hown_abs Hown_meta_frag")
    as %(Huid_obj & Hmeta_eq & _).
  iDestruct (kview.own_meta_living Hlookup with "Hown_abs Hown_meta_frag") as %Hold_living.
  iDestruct (kview.own_status_exists with "Hown_abs Hown_status_frag") as %Hstatus_found.
  iPureIntro. split_and!; try done.
  - eapply Hstatus_found; done.
  - apply Hprepared. right. done.
  - apply equiv_except_resource_version_valid_simple_update.
    rewrite /ObjectMetaV.equiv_except_resource_version in Hmeta_eq Hmeta_same |- *.
    congruence.
Qed.

(** When [updateStatusLocked] keeps the stored object for such a request, the
    validated request equals the stored object up to its resource version. *)
Lemma update_status_same_meta_kept (kind namespace : go_string) kobj abs_state old updated :
  valid_typemeta (KObjectV.kind kobj) (KObjectV.typemeta kobj) →
  update_status_validated kind namespace kobj abs_state old updated →
  update_prepared_for_helper namespace old kobj (update_status_prepared namespace old kobj) →
  (KObjectV.objectmeta kobj).(ObjectMetaV.Namespace') = namespace →
  ObjectMetaV.valid_simple_update (KObjectV.objectmeta old) (KObjectV.objectmeta kobj) →
  storage_object_normalize updated = storage_object_normalize old →
  update_objects_equiv_except_resource_version updated old ∧ KObjectV.same_kind kobj old.
Proof.
  intros Hvalid_typemeta Hvalidated Hprepared Hns Hvalid_meta_old Hstorage_eq.
  destruct Hvalidated as (_ & Hvalid_old & _ & _ & _ & Hupdated & Hpreserved).
  assert (KObjectV.valid updated) as Hvalid_updated.
  { apply (proj2 Hupdated Hvalid_old).
    rewrite /update_status_prepared KObjectV.kind_update_objectmeta
      KObjectV.typemeta_update_objectmeta.
    exact Hvalid_typemeta. }
  pose proof (storage_object_normalize_eq_implies_update_objects_equiv_except_resource_version
    updated old Hvalid_updated Hvalid_old Hstorage_eq) as Hequiv.
  split; first done.
  by destruct (Hpreserved kobj old Hprepared Hns Hvalid_meta_old Hequiv) as (? & _).
Qed.

(** The ghost update for a write by [updateStatusLocked] of such a request: only
    the status changes, so the other views take the new object as it is, and
    the metadata fragment stays valid. *)
Lemma update_status_same_meta_written_vs γ (kind namespace : go_string) kobj abs_state used_uid
    used_reference old updated rv uid dq kmeta kstatus :
  update_status_key kind namespace kobj = KObjectV.key kobj →
  valid_typemeta (KObjectV.kind kobj) (KObjectV.typemeta kobj) →
  ObjectMetaV.equiv_except_resource_version (KObjectV.objectmeta kobj) kmeta →
  update_status_validated kind namespace kobj abs_state old updated →
  valid_resource_version rv →
  own_kview_auth γ abs_state used_uid -∗
  own_children_auth γ abs_state used_reference -∗
  own_terminating_children_auth γ abs_state -∗
  own_deletion_observation_auth γ abs_state used_uid -∗
  own_meta_frag γ (KObjectV.key kobj) uid dq kmeta -∗
  own_status_frag γ (KObjectV.key kobj) uid 1 kstatus ==∗
  ⌜ KObjectV.valid (update_status_stored updated rv) ∧
    KObjectV.same_kind kobj (update_status_stored updated rv) ∧
    ObjectMetaV.equiv_except_resource_version
      (KObjectV.objectmeta (update_status_stored updated rv)) kmeta ⌝ ∗
  own_kview_auth γ (<[KObjectV.key kobj := update_status_stored updated rv]> abs_state) used_uid ∗
  own_children_auth γ (<[KObjectV.key kobj := update_status_stored updated rv]> abs_state)
    used_reference ∗
  own_terminating_children_auth γ
    (<[KObjectV.key kobj := update_status_stored updated rv]> abs_state) ∗
  own_deletion_observation_auth γ
    (<[KObjectV.key kobj := update_status_stored updated rv]> abs_state) used_uid ∗
  own_meta_frag γ (KObjectV.key kobj) uid dq kmeta ∗
  own_status_frag γ (KObjectV.key kobj) uid 1 (KObjectV.status (update_status_stored updated rv)).
Proof.
  iIntros (Hkey Hvalid_typemeta Hmeta_same Hvalidated Hvalid_rv)
    "Hown_abs Hown_children Hown_terminating_children Hown_deletion_observations
      Hown_meta_frag Hown_status_frag".
  iDestruct (update_status_same_meta_validated _ _ _ _ _ _ _ _ _ _ _ _ Hkey Hmeta_same Hvalidated
    with "Hown_abs Hown_meta_frag Hown_status_frag")
    as %(Hlookup_abs & Huid_eq & Hold_living & Hmeta_eq & Hstatus_eq & Hprepared & Hns &
      Hvalid_meta_old).
  pose proof Hvalidated as (_ & Hvalid_old_kobj & _ & _ & _ & Hupdated & Hpreserved).
  iPoseProof (kview.own_auth_valid2 _ old Hlookup_abs with "Hown_abs") as "%Hauth_old".
  destruct Hauth_old as (_ & _ & _ & Hno_speculative_parent_reference_old & _).
  iPoseProof (kview.own_auth_extra_valid_forall with "Hown_abs") as "%Habs_extra_valid".
  pose proof (Habs_extra_valid _ _ Hlookup_abs) as Hextra_valid_old.
  assert (KObjectV.valid updated) as Hvalid_updated_kobj.
  { apply (proj2 Hupdated Hvalid_old_kobj).
    rewrite /update_status_prepared KObjectV.kind_update_objectmeta
      KObjectV.typemeta_update_objectmeta.
    exact Hvalid_typemeta. }
  set new_kobj := update_status_stored updated rv.
  pose proof (Hpreserved kobj new_kobj Hprepared Hns Hvalid_meta_old
    (update_status_stored_equiv updated rv)) as (Hsame_kind_new & _ & Hmeta_new & Hspec_eq).
  unfold new_kobj, update_status_stored in Hspec_eq.
  rewrite KObjectV.spec_update_objectmeta in Hspec_eq.
  assert ((KObjectV.objectmeta new_kobj).(ObjectMetaV.Name') =
        (KObjectV.objectmeta kobj).(ObjectMetaV.Name') ∧
      (KObjectV.objectmeta new_kobj).(ObjectMetaV.Namespace') =
        (KObjectV.objectmeta kobj).(ObjectMetaV.Namespace') ∧
      (KObjectV.objectmeta new_kobj).(ObjectMetaV.UID') =
        (KObjectV.objectmeta kobj).(ObjectMetaV.UID') ∧
      (KObjectV.objectmeta new_kobj).(ObjectMetaV.DeletionTimestamp') =
        (KObjectV.objectmeta kobj).(ObjectMetaV.DeletionTimestamp') ∧
      obj_parent_ref new_kobj = obj_parent_ref kobj)
    as (Hname_new & Hnamespace_stored_new & Huid_new & Hdeletion_timestamp_new &
      Hparent_ref_new_input).
  { rewrite /obj_parent_ref /meta_parent_ref.
    rewrite /ObjectMetaV.equiv_except_resource_version
      /ObjectMetaV.without_resource_version in Hmeta_new.
    destruct (KObjectV.objectmeta new_kobj), (KObjectV.objectmeta kobj); simpl in *.
    inversion Hmeta_new; subst. done. }
  assert ((KObjectV.objectmeta kobj).(ObjectMetaV.UID') =
      (KObjectV.objectmeta old).(ObjectMetaV.UID') ∧
      (KObjectV.objectmeta kobj).(ObjectMetaV.DeletionTimestamp') =
        (KObjectV.objectmeta old).(ObjectMetaV.DeletionTimestamp') ∧
      (KObjectV.objectmeta kobj).(ObjectMetaV.Namespace') =
        (KObjectV.objectmeta old).(ObjectMetaV.Namespace') ∧
      meta_parent_ref (KObjectV.objectmeta old) =
        meta_parent_ref (KObjectV.objectmeta kobj))
    as (Hinput_uid_old & Hinput_deletion_timestamp_old & Hinput_namespace_old &
      Hinput_parent_ref_old).
  { rewrite /ObjectMetaV.valid_simple_update /meta_parent_ref in Hvalid_meta_old |- *.
    remember (KObjectV.objectmeta old) as old_meta.
    remember (KObjectV.objectmeta kobj) as input_meta.
    destruct old_meta, input_meta; simpl in *.
    decompose [and] Hvalid_meta_old. subst. done. }
  assert ((KObjectV.objectmeta new_kobj).(ObjectMetaV.UID') =
      (KObjectV.objectmeta old).(ObjectMetaV.UID')) as Huid_new_old.
  { rewrite Huid_new. exact Hinput_uid_old. }
  assert ((KObjectV.objectmeta old).(ObjectMetaV.DeletionTimestamp') =
      (KObjectV.objectmeta new_kobj).(ObjectMetaV.DeletionTimestamp'))
    as Hdeletion_timestamp_old_new.
  { rewrite Hdeletion_timestamp_new. symmetry. exact Hinput_deletion_timestamp_old. }
  assert (obj_parent_ref old = obj_parent_ref new_kobj) as Hparent_ref_old_new.
  { rewrite Hparent_ref_new_input. exact Hinput_parent_ref_old. }
  assert ((KObjectV.objectmeta old).(ObjectMetaV.Namespace') =
      (KObjectV.objectmeta new_kobj).(ObjectMetaV.Namespace')) as Hnamespace_old_new.
  { rewrite Hnamespace_stored_new. symmetry. exact Hinput_namespace_old. }
  assert (kview.valid_k_uid_obj (KObjectV.key kobj) uid new_kobj) as Hvalid_kuid_new.
  { unfold kview.valid_k_uid_obj.
    split.
    - rewrite /KObjectV.key Hname_new Hnamespace_stored_new.
      destruct kobj, new_kobj; simpl in Hsame_kind_new |- *; try done.
    - split.
      + rewrite Huid_eq. symmetry. exact Huid_new.
      + unfold new_kobj, update_status_stored.
        split.
        * pose proof Hvalid_updated_kobj as
            (Hupdated_valid_typemeta & _ & Hupdated_valid_meta & Hupdated_valid_spec &
              Hupdated_valid_status).
          split_and!.
          -- rewrite KObjectV.kind_update_objectmeta KObjectV.typemeta_update_objectmeta.
             exact Hupdated_valid_typemeta.
          -- rewrite objectmeta_update_objectmeta. exact Hvalid_rv.
          -- rewrite KObjectV.kind_update_objectmeta objectmeta_update_objectmeta.
             destruct (KObjectV.objectmeta updated); simpl in *; done.
          -- rewrite KObjectV.spec_update_objectmeta. exact Hupdated_valid_spec.
          -- rewrite KObjectV.status_update_objectmeta. exact Hupdated_valid_status.
        * apply KObjectV.extra_valid_update_objectmeta.
          rewrite /KObjectV.extra_valid Hspec_eq.
          exact Hextra_valid_old. }
  (* The metadata is unchanged except for the resource version, so only the
     status fragment is updated and metadata fragments at any fraction stay valid. *)
  iMod (kview.update_status_kobj_same_meta_vs old new_kobj with
    "[$Hown_abs] [$Hown_status_frag]") as "(Hown_abs & Hown_status_frag)".
  { exact Hvalid_kuid_new. }
  { rewrite -Hdeletion_timestamp_old_new. exact Hold_living. }
  { intros kind' name' uid' Hparent.
    eapply Hno_speculative_parent_reference_old.
    unfold meta_parent_ref_is in Hparent |- *.
    unfold obj_parent_ref in Hparent_ref_old_new.
    rewrite Hparent_ref_old_new Hnamespace_old_new. exact Hparent. }
  { exact Hlookup_abs. }
  { rewrite /ObjectMetaV.equiv_except_resource_version in Hmeta_eq Hmeta_new Hmeta_same.
    congruence. }
  { unfold new_kobj, update_status_stored. rewrite KObjectV.spec_update_objectmeta.
    symmetry. exact Hspec_eq. }
  iMod (cview.simple_update_vs (KObjectV.key kobj) old new_kobj with "[$Hown_children]")
    as "Hown_children".
  { done. }
  { unfold living_obj_parent_ref, obj_parent_ref.
    rewrite Hdeletion_timestamp_old_new.
    destruct ((KObjectV.objectmeta new_kobj).(ObjectMetaV.DeletionTimestamp')); [done|].
    exact Hparent_ref_old_new. }
  { symmetry. exact Huid_new_old. }
  iMod (terminating_children.update_same_parent_vs
    γ.(γ_terminating_children) abs_state (KObjectV.key kobj) old new_kobj with
    "Hown_terminating_children") as "Hown_terminating_children".
  { exact Hlookup_abs. }
  { unfold terminating_children.terminating_obj_parent_ref, obj_parent_ref.
    rewrite Hdeletion_timestamp_old_new.
    destruct ((KObjectV.objectmeta new_kobj).(ObjectMetaV.DeletionTimestamp')); [|done].
    exact Hparent_ref_old_new. }
  iMod (deletion_observation.update_vs (KObjectV.key kobj) old new_kobj with
    "Hown_deletion_observations") as "Hown_deletion_observations".
  { exact Hlookup_abs. }
  { symmetry. exact Huid_new_old. }
  { intros Hold_terminating.
    rewrite -Hdeletion_timestamp_old_new. exact Hold_terminating. }
  iModIntro. iFrame.
  iPureIntro. split_and!.
  - destruct Hvalid_kuid_new as (_ & _ & Hvalid_new_kobj & _). exact Hvalid_new_kobj.
  - exact Hsame_kind_new.
  - rewrite /ObjectMetaV.equiv_except_resource_version in Hmeta_new Hmeta_same |- *.
    congruence.
Qed.

(* A variant of [wp_State__update_status_au] for a request that keeps the stored
   metadata except for the resource version ([Hmeta_same]). The write then
   leaves the metadata unchanged, so the metadata fragment may be held at any
   fraction and is returned unchanged. The request must be valid against the
   stored metadata and status, so it succeeds unless another writer advanced the
   resource version. *)
Lemma wp_State__update_status_same_meta_au γ l kind namespace i kobj :
  ∀ Φ,
    is_pkg_init apimodel ∗
    is_kubernetes γ l ∗
    "Hdeepown_i" ∷ KObjectV.deepown_i i kobj 1 ∗
    (|={⊤, ∅}=> ∃ uid dq kmeta kstatus,
      "Hown_meta_frag" ∷ own_meta_frag γ (KObjectV.key kobj) uid dq kmeta ∗
      "Hown_status_frag" ∷ own_status_frag γ (KObjectV.key kobj) uid 1 kstatus ∗
      "%Hvalid_status_update" ∷ ⌜ KObjectV.valid_status_update kind namespace kmeta kstatus kobj ⌝ ∗
      "%Hmeta_same" ∷ ⌜ ObjectMetaV.equiv_except_resource_version (KObjectV.objectmeta kobj) kmeta ⌝ ∗
      "Hclose" ∷ (
        (∀ i' kobj',
          ( ⌜ KObjectV.valid kobj' ⌝ ∗
            ⌜ KObjectV.status_updated kobj kobj' ⌝ ∗
            ⌜ KObjectV.same_kind kobj kobj' ∧
              ObjectMetaV.equiv_except_resource_version (KObjectV.objectmeta kobj') kmeta ⌝ ∗
            KObjectV.deepown_i i' kobj' 1 ∗
            own_meta_frag γ (KObjectV.key kobj) uid dq kmeta ∗
            own_status_frag γ (KObjectV.key kobj) uid 1 (KObjectV.status kobj'))
            ={∅,⊤}=∗ ▷ Φ (#(interface.ok i'), #interface.nil)%V) ∧
        (∀ err,
          ( ⌜ conflict_error err ⌝ ∗
            own_meta_frag γ (KObjectV.key kobj) uid dq kmeta ∗
            own_status_frag γ (KObjectV.key kobj) uid 1 kstatus)
            ={∅,⊤}=∗ ▷ Φ (#interface.nil, #err)%V)
      )%I
    ) -∗ WP l @! (go.PointerType apimodel.State) @! "updateStatus" #kind #namespace #(interface.ok i) {{ Φ }}.
Proof.
  iIntros (Φ) "(#Hpkg & #Hkinv & Hau)". iNamed "Hau". iNamed "Hkinv".
  destruct (Classical_Prop.classic (kind = KObjectV.kind kobj ∧
    valid_resource_version (KObjectV.objectmeta kobj).(ObjectMetaV.ResourceVersion') ∧
    valid_typemeta (KObjectV.kind kobj) (KObjectV.typemeta kobj) ∧
    namespace = (KObjectV.objectmeta kobj).(ObjectMetaV.Namespace') ∧
    (KObjectV.objectmeta kobj).(ObjectMetaV.Name') ≠ ""%go))
    as [Hvalid_status_update_input|Hinvalid_status_update_input].
  2: {
    iApply fupd_wp.
    iMod "Hau" as (uid dq kmeta kstatus) "H". iNamed "H".
    exfalso. apply Hinvalid_status_update_input. split_and!.
    - eapply valid_status_update_kind. exact Hvalid_status_update.
    - eapply valid_status_update_resource_version. exact Hvalid_status_update.
    - eapply valid_status_update_typemeta. exact Hvalid_status_update.
    - eapply valid_status_update_namespace. exact Hvalid_status_update.
    - eapply valid_status_update_name_nonempty. exact Hvalid_status_update.
  }
  destruct Hvalid_status_update_input as
    (Hkind_matches & Hrv_valid & Hvalid_typemeta & Hns_matches & Hname_nonempty).
  (* The request keeps the stored UID, which is non-empty. *)
  destruct (decide ((KObjectV.objectmeta kobj).(ObjectMetaV.UID') = ""%go)) as [Huid_empty|Huid_nonempty].
  { iApply fupd_wp.
    iMod "Hau" as (uid dq kmeta kstatus) "H". iNamed "H".
    iPoseProof (own_meta_frag_request_uid_nonempty _ _ _ _ _ kobj Hmeta_same with "Hown_meta_frag")
      as "%Huid_nonempty".
    exfalso. done. }
  wp_method_call. rewrite /apimodel.State__updateStatusⁱᵐᵖˡ. wp_call.
  wp_apply wp_with_defer as "%defer Hdefer". simpl subst. wp_auto.
  wp_apply wp_Mutex__Lock; [done|]. iIntros "[Hown_Mutex H]". iNamedPrefix "H" "Hinv_". wp_auto.
  assert (update_status_key kind namespace kobj = KObjectV.key kobj) as Hkey.
  { rewrite /update_status_key Hkind_matches Hns_matches. destruct kobj; done. }
  wp_apply (wp_State__updateStatusLocked γ l kind namespace i kobj with
    "[$Hdeepown_i $Hinv_Hstate_m_addr $Hinv_Hstate_used_rv_addr $Hinv_Hown_phys $Hinv_Hown_used_rv
      $Hinv_Hown_abs $Hinv_Hphys_abs_rep]").
  { iFrame "#". iPureIntro. split; first done. left. exact Hkind_matches. }
  iIntros (ret err) "(Hdeepown_i & Hinv_Hstate_m_addr & Hinv_Hstate_used_rv_addr & Hinv_Hown_abs & Hout)".
  rewrite Hkey.
  iDestruct "Hout" as "[(%Hfail & Hinv_Hown_phys & Hinv_Hown_used_rv & Hinv_Hphys_abs_rep) |
    [(%i' & %old & %updated & %Hkept & Hdeepown_i' & Hinv_Hown_phys & Hinv_Hown_used_rv &
      Hinv_Hphys_abs_rep) |
    [(%i' & %old & %updated & %Hdeleted & _) |
    (%i' & %i_new & %old & %updated & %rv & %Hwritten & Hdeepown_i' & Hinv_Hown_phys &
      Hinv_Hown_used_rv & Hinv_Hphys_abs_rep)]]]".
  - (* Only the resource version check rejects a valid request. *)
    destruct Hfail as (-> & Herr_ne & Hreason).
    wp_auto.
    iApply fupd_wp.
    iMod "Hau" as (uid dq kmeta kstatus) "H". iNamed "H".
    iDestruct (kview.own_meta_exists with "Hinv_Hown_abs Hown_meta_frag")
      as %(obj & Hlookup_obj & Huid_obj & Hmeta_eq & _).
    iDestruct (kview.own_meta_living Hlookup_obj with "Hinv_Hown_abs Hown_meta_frag")
      as %Hobj_living.
    iDestruct (kview.own_status_exists with "Hinv_Hown_abs Hown_status_frag") as %Hstatus_found.
    assert (conflict_error err) as Hconflict.
    { destruct Hreason as [Hconflict|Hrejected]; first done. exfalso.
      rewrite /update_status_rejected Hkey in Hrejected.
      destruct Hrejected as
        [[_ Hns_ne]|[Hname_empty|[Hnot_found|[Hrv_invalid|(old & Hlookup_old & Hinvalid)]]]].
      - apply Hns_ne. symmetry. exact Hns_matches.
      - exact (Hname_nonempty Hname_empty).
      - rewrite Hlookup_obj in Hnot_found. done.
      - exact (Hrv_invalid Hrv_valid).
      - rewrite Hlookup_obj in Hlookup_old. injection Hlookup_old as <-.
        apply Hinvalid.
        rewrite (Hstatus_found obj Hlookup_obj Huid_obj Hobj_living).
        eapply valid_status_update_equiv_except_resource_version; last exact Hvalid_status_update.
        symmetry. exact Hmeta_eq. }
    iDestruct "Hclose" as "[_ Hclose_err]".
    iMod ("Hclose_err" $! err with "[$Hown_meta_frag $Hown_status_frag]") as "HΦ".
    { done. }
    iModIntro.
    iCombineNamed "Hinv_*" as "H".
    wp_apply (wp_Mutex__Unlock _ (kubernetes_inv γ l) with "[$Hown_Mutex H]").
    { iNamed "H". iFrame. iFrame "#". done. }
    iExact "HΦ".
  - (* The validated request stores the same as the stored object, which is kept. *)
    destruct Hkept as (-> & -> & Hvalidated & Hstorage_eq).
    wp_auto.
    iApply fupd_wp.
    iMod "Hau" as (uid dq kmeta kstatus) "H". iNamed "H".
    iDestruct (update_status_same_meta_validated _ _ _ _ _ _ _ _ _ _ _ _ Hkey Hmeta_same Hvalidated
      with "Hinv_Hown_abs Hown_meta_frag Hown_status_frag")
      as %(_ & _ & _ & Hmeta_eq & Hstatus_eq & Hprepared & Hns_kobj & Hvalid_meta_old).
    destruct (update_status_same_meta_kept _ _ _ _ _ _ Hvalid_typemeta Hvalidated Hprepared Hns_kobj
      Hvalid_meta_old Hstorage_eq) as [Hequiv_updated_old Hsame_kind_old].
    pose proof Hvalidated as (_ & Hvalid_old & _ & _ & _ & Hupdated & _).
    iDestruct "Hclose" as "[Hclose_success _]".
    iMod ("Hclose_success" $! i' old with "[Hdeepown_i' Hown_meta_frag Hown_status_frag]") as "HΦ".
    { iSplit; first done.
      iSplit.
      { iPureIntro.
        assert (KObjectV.valid_status_update kind namespace
            (KObjectV.objectmeta old) (KObjectV.status old) kobj) as Hvalid_actual.
        { rewrite Hstatus_eq.
          eapply valid_status_update_equiv_except_resource_version; last exact Hvalid_status_update.
          symmetry. exact Hmeta_eq. }
        by destruct (proj1 Hupdated _ kobj old Hvalid_old Hvalid_actual Hprepared Hequiv_updated_old). }
      iSplit; first (iPureIntro; split; done).
      iFrame "Hdeepown_i' Hown_meta_frag".
      rewrite Hstatus_eq. iFrame. }
    iModIntro.
    iCombineNamed "Hinv_*" as "H".
    wp_apply (wp_Mutex__Unlock _ (kubernetes_inv γ l) with "[$Hown_Mutex H]").
    { iNamed "H". iFrame. iFrame "#". done. }
    iExact "HΦ".
  - (* The fragments describe an object that is not being deleted. *)
    destruct Hdeleted as (_ & _ & Hvalidated & Hterminating).
    iApply fupd_wp.
    iMod "Hau" as (uid dq kmeta kstatus) "H". iNamed "H".
    iDestruct (update_status_same_meta_validated _ _ _ _ _ _ _ _ _ _ _ _ Hkey Hmeta_same Hvalidated
      with "Hinv_Hown_abs Hown_meta_frag Hown_status_frag") as %(_ & _ & Hold_living & _).
    exfalso. exact (Hterminating Hold_living).
  - (* The validated request is written at a fresh resource version. *)
    destruct Hwritten as (-> & -> & Hvalidated & _ & Hvalid_rv).
    wp_auto.
    iApply fupd_wp.
    iMod "Hau" as (uid dq kmeta kstatus) "H". iNamed "H".
    iDestruct (update_status_same_meta_validated _ _ _ _ _ _ _ _ _ _ _ _ Hkey Hmeta_same Hvalidated
      with "Hinv_Hown_abs Hown_meta_frag Hown_status_frag")
      as %(_ & _ & _ & Hmeta_eq & Hstatus_eq & Hprepared & _).
    iMod (update_status_same_meta_written_vs _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hkey Hvalid_typemeta
      Hmeta_same Hvalidated Hvalid_rv with "Hinv_Hown_abs Hinv_Hown_children
      Hinv_Hown_terminating_children Hinv_Hown_deletion_observations Hown_meta_frag Hown_status_frag")
      as "(%Hnew & Hinv_Hown_abs & Hinv_Hown_children & Hinv_Hown_terminating_children &
        Hinv_Hown_deletion_observations & Hown_meta_frag & Hown_status_frag)".
    destruct Hnew as (Hvalid_new & Hsame_kind_new & Hmeta_new).
    pose proof Hvalidated as (_ & Hvalid_old & _ & _ & _ & Hupdated & _).
    assert (KObjectV.valid_status_update kind namespace
        (KObjectV.objectmeta old) (KObjectV.status old) kobj) as Hvalid_actual.
    { rewrite Hstatus_eq.
      eapply valid_status_update_equiv_except_resource_version; last exact Hvalid_status_update.
      symmetry. exact Hmeta_eq. }
    destruct (proj1 Hupdated _ kobj _ Hvalid_old Hvalid_actual Hprepared
      (update_status_stored_equiv updated rv)) as [Hstatus_updated _].
    iDestruct "Hclose" as "[Hclose_success _]".
    iMod ("Hclose_success" $! i' (update_status_stored updated rv) with
      "[$Hdeepown_i' $Hown_meta_frag $Hown_status_frag]") as "HΦ".
    { iPureIntro. split_and!; done. }
    iModIntro.
    iCombineNamed "Hinv_*" as "H".
    wp_apply (wp_Mutex__Unlock _ (kubernetes_inv γ l) with "[$Hown_Mutex H]").
    { iNamed "H".
      iFrame "#". iFrame. iNext. iFrame. iPureIntro. split_and!.
      all: try done.
    }
    iExact "HΦ".
Unshelve.
all: try apply _.
all: try done.
Qed.

(** A status write whose request carries the UID of the object at [key] but
    names another key fails and leaves the store unchanged: the requested key
    holds no object, or one with another UID. *)
Lemma wp_State__update_status_other_key_au γ l kind namespace i kobj key :
  ∀ Φ,
    is_pkg_init apimodel ∗
    is_kubernetes γ l ∗
    "%Hkey_ne" ∷ ⌜ {| KKey.Kind' := kind; KKey.Name' := (KObjectV.objectmeta kobj).(ObjectMetaV.Name');
                     KKey.Namespace' := namespace |} ≠ key ⌝ ∗
    "Hdeepown_i" ∷ KObjectV.deepown_i i kobj 1 ∗
    (|={⊤, ∅}=> ∃ uid dq kmeta,
      "Hown_meta_frag" ∷ own_meta_frag γ key uid dq kmeta ∗
      "%Huid" ∷ ⌜ (KObjectV.objectmeta kobj).(ObjectMetaV.UID') = uid ⌝ ∗
      "Hclose" ∷ (∀ err,
        ⌜ err ≠ interface.nil ⌝ ∗ own_meta_frag γ key uid dq kmeta ={∅,⊤}=∗ ▷ Φ (#interface.nil, #err)%V)
    ) -∗ WP l @! (go.PointerType apimodel.State) @! "updateStatus" #kind #namespace #(interface.ok i) {{ Φ }}.
Proof.
  iIntros (Φ) "(#Hpkg & #Hkinv & Hau)". iNamed "Hau". iNamed "Hkinv".
  (* The request carries the stored UID, which is non-empty. *)
  destruct (decide ((KObjectV.objectmeta kobj).(ObjectMetaV.UID') = ""%go)) as [Huid_empty|Huid_nonempty].
  { iApply fupd_wp.
    iMod "Hau" as (uid dq kmeta) "H". iNamed "H".
    rewrite /own_meta_frag.
    iPoseProof (kview.own_meta_valid with "Hown_meta_frag") as
      "(_ & _ & %Huid_meta & %Hvalid_meta & _)".
    exfalso. destruct Hvalid_meta as (_ & _ & _ & _ & _ & Hvalid_uid & _).
    apply (valid_uid_non_empty _ Hvalid_uid). rewrite -Huid_meta -Huid. exact Huid_empty. }
  wp_method_call. rewrite /apimodel.State__updateStatusⁱᵐᵖˡ. wp_call.
  wp_apply wp_with_defer as "%defer Hdefer". simpl subst. wp_auto.
  wp_apply wp_Mutex__Lock; [done|]. iIntros "[Hown_Mutex H]". iNamedPrefix "H" "Hinv_". wp_auto.
  (* No object at the requested key carries the request's UID: UIDs are unique,
     and the object at [key] carries it. *)
  destruct (Classical_Prop.classic (∃ old, abs_state !! update_status_key kind namespace kobj = Some old ∧
      (KObjectV.objectmeta old).(ObjectMetaV.UID') = (KObjectV.objectmeta kobj).(ObjectMetaV.UID')))
    as [(old & Hlookup_old & Huid_old)|Hno_uid].
  { iApply fupd_wp.
    iMod "Hau" as (uid dq kmeta) "H". iNamed "H".
    iDestruct (kview.own_meta_exists with "Hinv_Hown_abs Hown_meta_frag")
      as %(obj & Hlookup_obj & Huid_obj & _ & _).
    iPoseProof (kview.own_auth_valid2 _ old with "Hinv_Hown_abs") as "%Hauth_old".
    1: done.
    destruct Hauth_old as (_ & _ & _ & _ & Huid_unique_old).
    exfalso. apply Hkey_ne.
    apply (map_Forall_lookup_1 _ _ _ _ Huid_unique_old Hlookup_obj).
    rewrite Huid_old Huid_obj. exact Huid. }
  wp_apply (wp_State__updateStatusLocked γ l kind namespace i kobj with
    "[$Hdeepown_i $Hinv_Hstate_m_addr $Hinv_Hstate_used_rv_addr $Hinv_Hown_phys $Hinv_Hown_used_rv
      $Hinv_Hown_abs $Hinv_Hphys_abs_rep]").
  { iFrame "#". iPureIntro. split; first done.
    right. intros old Hlookup Huid_eq. apply Hno_uid. exists old. done. }
  iIntros (ret err) "(Hdeepown_i & Hinv_Hstate_m_addr & Hinv_Hstate_used_rv_addr & Hinv_Hown_abs & Hout)".
  iDestruct "Hout" as "[(%Hfail & Hinv_Hown_phys & Hinv_Hown_used_rv & Hinv_Hphys_abs_rep) | Hout]".
  2: {
    (* An accepted request carries the UID of the object at the requested key. *)
    iExFalso.
    iDestruct "Hout" as "[(%i' & %old & %updated & %Hout & _) | [(%i' & %old & %updated & %Hout & _) |
      (%i' & %i_new & %old & %updated & %rv & %Hout & _)]]";
      destruct Hout as (_ & _ & (Hlookup & _ & _ & Huid_eq & _) & _);
      iPureIntro; apply Hno_uid; eauto. }
  destruct Hfail as (-> & Herr_ne & _).
  wp_auto.
  iApply fupd_wp.
  iMod "Hau" as (uid dq kmeta) "H". iNamed "H".
  iMod ("Hclose" $! err with "[$Hown_meta_frag]") as "HΦ".
  { done. }
  iModIntro.
  iCombineNamed "Hinv_*" as "H".
  wp_apply (wp_Mutex__Unlock _ (kubernetes_inv γ l) with "[$Hown_Mutex H]").
  { iNamed "H". iFrame. iFrame "#". done. }
  iExact "HΦ".
Unshelve.
all: try apply _.
all: try done.
Qed.

(* A variant of [wp_State__update_status_same_meta_au] that does not require the
   request status to be valid, nor the request kind and namespace to name the
   object's key, nor the request resource version to be valid. Validation may
   then reject the write, which leaves the stored object and both fragments
   unchanged; a success does not describe the stored status beyond its validity.

   [Hvalid_typemeta] is the request-level part of [KObjectV.valid_status_update]
   that a status write needs even when the submitted status may be invalid: a
   valid TypeMeta keeps the stored object valid, as the write stores the
   request's TypeMeta unchecked. An empty name, or a request kind or namespace
   other than the object's, need not be ruled out: the write then fails, with a
   bad request or because the requested key holds no object with the request's
   UID. Neither does the resource version: an empty one is replaced by the
   stored one, and any other one fails to parse, conflicts, or is the stored
   one. The other metadata, the UID included, need not be checked: the request
   keeps the stored metadata up to the resource version, so it is valid
   already. *)
Lemma wp_State__update_status_same_meta_general_au γ l (kind namespace : go_string) i kobj :
  ∀ Φ,
    is_pkg_init apimodel ∗
    is_kubernetes γ l ∗
    "%Hvalid_typemeta" ∷ ⌜ valid_typemeta (KObjectV.kind kobj) (KObjectV.typemeta kobj) ⌝ ∗
    "Hdeepown_i" ∷ KObjectV.deepown_i i kobj 1 ∗
    (|={⊤, ∅}=> ∃ uid dq kmeta kstatus,
      "Hown_meta_frag" ∷ own_meta_frag γ (KObjectV.key kobj) uid dq kmeta ∗
      "Hown_status_frag" ∷ own_status_frag γ (KObjectV.key kobj) uid 1 kstatus ∗
      "%Hmeta_same" ∷ ⌜ ObjectMetaV.equiv_except_resource_version (KObjectV.objectmeta kobj) kmeta ⌝ ∗
      "Hclose" ∷ (
        (∀ i' kobj',
          ( ⌜ KObjectV.valid kobj' ⌝ ∗
            ⌜ KObjectV.same_kind kobj kobj' ∧
              ObjectMetaV.equiv_except_resource_version (KObjectV.objectmeta kobj') kmeta ⌝ ∗
            KObjectV.deepown_i i' kobj' 1 ∗
            own_meta_frag γ (KObjectV.key kobj) uid dq kmeta ∗
            own_status_frag γ (KObjectV.key kobj) uid 1 (KObjectV.status kobj'))
            ={∅,⊤}=∗ ▷ Φ (#(interface.ok i'), #interface.nil)%V) ∧
        (∀ err,
          ( ⌜ err ≠ interface.nil ⌝ ∗
            own_meta_frag γ (KObjectV.key kobj) uid dq kmeta ∗
            own_status_frag γ (KObjectV.key kobj) uid 1 kstatus)
            ={∅,⊤}=∗ ▷ Φ (#interface.nil, #err)%V)
      )%I
    ) -∗ WP l @! (go.PointerType apimodel.State) @! "updateStatus" #kind #namespace #(interface.ok i) {{ Φ }}.
Proof.
  iIntros (Φ) "(#Hpkg & #Hkinv & Hau)". iNamed "Hau".
  destruct (decide ({| KKey.Kind' := kind; KKey.Name' := ObjectMetaV.Name' (KObjectV.objectmeta kobj);
      KKey.Namespace' := namespace |} = KObjectV.key kobj)) as [Hkey_matches|Hkey_ne].
  2: {
    (* Another kind or namespace names another key, where no object carries
       the request's UID. *)
    iApply (wp_State__update_status_other_key_au γ l kind namespace i kobj (KObjectV.key kobj)).
    iFrame "#". iFrame "Hdeepown_i".
    iSplit; first done.
    iMod "Hau" as (uid dq kmeta kstatus) "H". iNamed "H".
    iDestruct (own_meta_frag_status_identity _ _ _ _ _ kobj Hmeta_same with "Hown_meta_frag") as
      %[Huid_kobj _].
    iModIntro. iExists uid, dq, kmeta. iFrame "Hown_meta_frag".
    iSplit; first done.
    iIntros (err) "[%Herr_ne Hown_meta_frag]".
    iDestruct "Hclose" as "[_ Hclose_err]".
    iApply ("Hclose_err" $! err with "[$Hown_meta_frag $Hown_status_frag]"). done. }
  assert (kind = KObjectV.kind kobj ∧ namespace = (KObjectV.objectmeta kobj).(ObjectMetaV.Namespace'))
    as [Hkind_matches Hns_matches].
  { pose proof (f_equal KKey.Kind' Hkey_matches) as Hkind_eq.
    pose proof (f_equal KKey.Namespace' Hkey_matches) as Hns_eq.
    destruct kobj; simpl in Hkind_eq, Hns_eq; split; done. }
  iNamed "Hkinv".
  (* The request keeps the stored UID, which is non-empty. *)
  destruct (decide ((KObjectV.objectmeta kobj).(ObjectMetaV.UID') = ""%go)) as [Huid_empty|Huid_nonempty].
  { iApply fupd_wp.
    iMod "Hau" as (uid dq kmeta kstatus) "H". iNamed "H".
    iPoseProof (own_meta_frag_request_uid_nonempty _ _ _ _ _ kobj Hmeta_same with "Hown_meta_frag")
      as "%Huid_nonempty".
    exfalso. done. }
  wp_method_call. rewrite /apimodel.State__updateStatusⁱᵐᵖˡ. wp_call.
  wp_apply wp_with_defer as "%defer Hdefer". simpl subst. wp_auto.
  wp_apply wp_Mutex__Lock; [done|]. iIntros "[Hown_Mutex H]". iNamedPrefix "H" "Hinv_". wp_auto.
  assert (update_status_key kind namespace kobj = KObjectV.key kobj) as Hkey by exact Hkey_matches.
  wp_apply (wp_State__updateStatusLocked γ l kind namespace i kobj with
    "[$Hdeepown_i $Hinv_Hstate_m_addr $Hinv_Hstate_used_rv_addr $Hinv_Hown_phys $Hinv_Hown_used_rv
      $Hinv_Hown_abs $Hinv_Hphys_abs_rep]").
  { iFrame "#". iPureIntro. split; first done. left. exact Hkind_matches. }
  iIntros (ret err) "(Hdeepown_i & Hinv_Hstate_m_addr & Hinv_Hstate_used_rv_addr & Hinv_Hown_abs & Hout)".
  rewrite Hkey.
  iDestruct "Hout" as "[(%Hfail & Hinv_Hown_phys & Hinv_Hown_used_rv & Hinv_Hphys_abs_rep) |
    [(%i' & %old & %updated & %Hkept & Hdeepown_i' & Hinv_Hown_phys & Hinv_Hown_used_rv &
      Hinv_Hphys_abs_rep) |
    [(%i' & %old & %updated & %Hdeleted & _) |
    (%i' & %i_new & %old & %updated & %rv & %Hwritten & Hdeepown_i' & Hinv_Hown_phys &
      Hinv_Hown_used_rv & Hinv_Hphys_abs_rep)]]]".
  - (* A rejected request leaves the stored object and both fragments unchanged. *)
    destruct Hfail as (-> & Herr_ne & _).
    wp_auto.
    iApply fupd_wp.
    iMod "Hau" as (uid dq kmeta kstatus) "H". iNamed "H".
    iDestruct "Hclose" as "[_ Hclose_err]".
    iMod ("Hclose_err" $! err with "[$Hown_meta_frag $Hown_status_frag]") as "HΦ".
    { done. }
    iModIntro.
    iCombineNamed "Hinv_*" as "H".
    wp_apply (wp_Mutex__Unlock _ (kubernetes_inv γ l) with "[$Hown_Mutex H]").
    { iNamed "H". iFrame. iFrame "#". done. }
    iExact "HΦ".
  - (* The validated request stores the same as the stored object, which is kept. *)
    destruct Hkept as (-> & -> & Hvalidated & Hstorage_eq).
    wp_auto.
    iApply fupd_wp.
    iMod "Hau" as (uid dq kmeta kstatus) "H". iNamed "H".
    iDestruct (update_status_same_meta_validated _ _ _ _ _ _ _ _ _ _ _ _ Hkey Hmeta_same Hvalidated
      with "Hinv_Hown_abs Hown_meta_frag Hown_status_frag")
      as %(_ & _ & _ & Hmeta_eq & Hstatus_eq & Hprepared & Hns_kobj & Hvalid_meta_old).
    destruct (update_status_same_meta_kept _ _ _ _ _ _ Hvalid_typemeta Hvalidated Hprepared Hns_kobj
      Hvalid_meta_old Hstorage_eq) as [_ Hsame_kind_old].
    pose proof Hvalidated as (_ & Hvalid_old & _).
    iDestruct "Hclose" as "[Hclose_success _]".
    iMod ("Hclose_success" $! i' old with "[Hdeepown_i' Hown_meta_frag Hown_status_frag]") as "HΦ".
    { iSplit; first done.
      iSplit; first (iPureIntro; split; done).
      iFrame "Hdeepown_i' Hown_meta_frag".
      rewrite Hstatus_eq. iFrame. }
    iModIntro.
    iCombineNamed "Hinv_*" as "H".
    wp_apply (wp_Mutex__Unlock _ (kubernetes_inv γ l) with "[$Hown_Mutex H]").
    { iNamed "H". iFrame. iFrame "#". done. }
    iExact "HΦ".
  - (* The fragments describe an object that is not being deleted. *)
    destruct Hdeleted as (_ & _ & Hvalidated & Hterminating).
    iApply fupd_wp.
    iMod "Hau" as (uid dq kmeta kstatus) "H". iNamed "H".
    iDestruct (update_status_same_meta_validated _ _ _ _ _ _ _ _ _ _ _ _ Hkey Hmeta_same Hvalidated
      with "Hinv_Hown_abs Hown_meta_frag Hown_status_frag") as %(_ & _ & Hold_living & _).
    exfalso. exact (Hterminating Hold_living).
  - (* The validated request is written at a fresh resource version. *)
    destruct Hwritten as (-> & -> & Hvalidated & _ & Hvalid_rv).
    wp_auto.
    iApply fupd_wp.
    iMod "Hau" as (uid dq kmeta kstatus) "H". iNamed "H".
    iMod (update_status_same_meta_written_vs _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hkey Hvalid_typemeta
      Hmeta_same Hvalidated Hvalid_rv with "Hinv_Hown_abs Hinv_Hown_children
      Hinv_Hown_terminating_children Hinv_Hown_deletion_observations Hown_meta_frag Hown_status_frag")
      as "(%Hnew & Hinv_Hown_abs & Hinv_Hown_children & Hinv_Hown_terminating_children &
        Hinv_Hown_deletion_observations & Hown_meta_frag & Hown_status_frag)".
    destruct Hnew as (Hvalid_new & Hsame_kind_new & Hmeta_new).
    iDestruct "Hclose" as "[Hclose_success _]".
    iMod ("Hclose_success" $! i' (update_status_stored updated rv) with
      "[$Hdeepown_i' $Hown_meta_frag $Hown_status_frag]") as "HΦ".
    { iPureIntro. split_and!; done. }
    iModIntro.
    iCombineNamed "Hinv_*" as "H".
    wp_apply (wp_Mutex__Unlock _ (kubernetes_inv γ l) with "[$Hown_Mutex H]").
    { iNamed "H".
      iFrame "#". iFrame. iNext. iFrame. iPureIntro. split_and!.
      all: try done.
    }
    iExact "HΦ".
Unshelve.
all: try apply _.
all: try done.
Qed.

End proof.
