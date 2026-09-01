From New.proof Require Import prelude empty_ffi.
From New.proof.kubernetes_model Require Export common_create.

Section proof.
Context `{hG: !heapGS Σ} `{!ffi_semantics _ _}.
Context {sem : go.Semantics} {package_sem : apimodel.Assumptions}.
Context `{!kubernetesModelG Σ}.
Context `{!KObjectV.ObjectInterfaceAssumptions}.
Local Set Default Proof Using "All".

Lemma wp_State__create_named_au γ l kind namespace key i kobj parent_key parent_uid :
  ∀ Φ,
  ( is_pkg_init apimodel ∗
    is_kubernetes γ l ∗
    "%Hvalid" ∷ ⌜ KObjectV.valid_create kind namespace kobj ⌝ ∗
    "%Hname_nonempty" ∷ ⌜ (KObjectV.objectmeta kobj).(ObjectMetaV.Name') ≠ ""%go ⌝ ∗
    "%Hextra_valid" ∷ ⌜ KObjectV.extra_valid kobj ⌝ ∗
    "%Hns_eq" ∷ ⌜ namespace = parent_key.(KKey.Namespace') ⌝ ∗
    "%Hkey_eq" ∷ ⌜ key = {|
      KKey.Kind' := KObjectV.kind kobj;
      KKey.Name' := (KObjectV.objectmeta kobj).(ObjectMetaV.Name');
      KKey.Namespace' := namespace
    |} ⌝ ∗
    "%Hpr" ∷ ⌜ obj_parent_ref_is kobj parent_key.(KKey.Kind') parent_key.(KKey.Name') parent_uid ⌝ ∗
    "Hdeepown_i" ∷ KObjectV.deepown_i i kobj 1 ∗
    |={⊤,∅}=> ∃ reservation children,
      "%Hreservation_status" ∷ ⌜ reservation = Available ∨ ∃ old_uid, reservation = Deleting old_uid ⌝ ∗
      "Hown_reserved_frag" ∷ own_reserved_frag γ key 1 reservation ∗
      "Hown_children_frag" ∷ own_children_frag γ parent_key parent_uid 1 children ∗
      "Hclose" ∷
        ((∀ i' kobj' uid,
          ⌜ KObjectV.valid kobj' ⌝ ∗
          ⌜ KObjectV.created namespace kobj kobj' ⌝ ∗
          ⌜ key = (KObjectV.key kobj') ⌝ ∗
          ⌜ key ∉ children ⌝ ∗
          ⌜ uid = (KObjectV.objectmeta kobj').(ObjectMetaV.UID') ⌝ ∗
          KObjectV.deepown_i i' kobj' 1 ∗
          own_meta_frag γ key uid 1 (KObjectV.objectmeta kobj') ∗
          own_spec_frag γ key uid 1 (KObjectV.spec kobj') ∗
          own_status_frag γ key uid 1 (KObjectV.status kobj') ∗
          own_occupied_reserved_frag γ 1 key uid ∗
          own_children_frag γ parent_key parent_uid 1 (children ∪ {[key]}) ∗
          own_children_frag γ key uid 1 ∅
            ={∅,⊤}=∗ ▷ Φ (#(interface.ok i'), #interface.nil)%V) ∧
        (∀ old_uid err,
          ⌜ reservation = Deleting old_uid ⌝ ∗
          ⌜ already_exists_error err ⌝ ∗
          own_deleting_reserved_frag γ 1 key old_uid ∗
          own_children_frag γ parent_key parent_uid 1 children
            ={∅,⊤}=∗ ▷ Φ (#interface.nil, #err)%V))
  ) -∗ WP l @! (go.PointerType apimodel.State) @! "create" #kind #namespace #(interface.ok i) {{ Φ }}.
Proof.
  iIntros (Φ) "(#Hpkg & #Hkinv & Hau)". iNamed "Hau". iNamed "Hkinv".
  assert (kind = KObjectV.kind kobj ∧ namespace ≠ ""%go ∧ valid_namespace namespace ∧
      ObjectMetaV.valid_create (KObjectV.kind kobj) namespace (KObjectV.objectmeta kobj)) as
    (Hkind_matches & Hns_nonempty & Hns_valid & Hvalid_meta_create).
  { destruct kobj; rewrite /KObjectV.valid_create /= in Hvalid;
      rewrite ?/PodV.valid_create ?/ReplicaSetV.valid_create
        ?/PersistentVolumeClaimV.valid_create ?/StatefulSetV.valid_create
        ?/DeploymentV.valid_create in Hvalid;
      tauto. }
  assert (key = {|
      KKey.Kind' := kind;
      KKey.Name' := (KObjectV.objectmeta kobj).(ObjectMetaV.Name');
      KKey.Namespace' := namespace
    |}) as Hrequest_key_eq.
  { rewrite Hkey_eq Hkind_matches. done. }
  wp_method_call. rewrite /apimodel.State__createⁱᵐᵖˡ. wp_call.
  wp_apply wp_with_defer as "%defer Hdefer". simpl subst. wp_auto.
  wp_apply wp_Mutex__Lock; [done|]. iIntros "[Hown_Mutex H]". iNamedPrefix "H" "Hinv_". wp_auto.
  wp_apply (wp_deepCopy i kobj with "[Hdeepown_i]").
  { iFrame "#". iExact "Hdeepown_i". }
  iIntros (i1) "[Hdeepown_i1 Hdeepown_i]". wp_auto.
  iDestruct "Hdeepown_i1" as (l1) "[%Hvalid_interface Hdeepown_l]".
  wp_apply wp_Accessor. 1: iPureIntro; done.
  iPoseProof (KObjectV.deepown_l_split with "Hdeepown_l") as
    "(%Hl1_not_null & Hdeepown_t_l & Hdeepown_m_l & Hdeepown_s_l & Hdeepown_st_l)".
  wp_apply (wp_WipeObjectMetaSystemFields with "[$Hdeepown_m_l]"). 1: done.
  iIntros (time) "Hdeepown_m_l". wp_auto.
  wp_apply (wp_EnsureObjectNamespaceMatchesRequestNamespace with "[$Hdeepown_m_l]").
  { iPureIntro.
    rewrite /ObjectMetaV.valid_create in Hvalid_meta_create.
    rewrite decide_False in Hvalid_meta_create.
    1: exact Hname_nonempty.
    destruct Hvalid_meta_create as (_ & Hns & _).
    destruct Hns as [Hns|(_ & Hns)]; rewrite Hns; auto.
  }
  iIntros "Hdeepown_m_l". wp_auto.
  wp_apply v1.wp_Now. iIntros (now_time now_timev) "Hdeepown_time". wp_auto.
  wp_apply (wp_SetCreationTimestamp_deepown_kobject i1 l1 kobj _ now_time now_timev
    with "[$Hdeepown_m_l $Hdeepown_time]"). 1: done.
  iIntros "Hdeepown_m_l". wp_auto.
  wp_apply (wp_State__generateNewUIDAndUpdate with "[$Hinv_Hstate_used_uid_addr $Hinv_Hown_used_uid]").
  iIntros (generated_uid) "(%Hgenerated_uid_is_not_used & %Hgenerated_uid_valid & Hinv_Hstate_used_uid_addr & Hinv_Hown_used_uid)". wp_auto.
  wp_apply (wp_SetUID_deepown_kobject i1 l1 kobj with "[$Hdeepown_m_l]"). 1: done.
  iIntros "Hdeepown_m_l". wp_auto.
  wp_apply (wp_GetName_deepown_kobject i1 l1 kobj with "[$Hdeepown_m_l]"). 1: done.
  iIntros "Hdeepown_m_l". wp_auto.
  wp_apply (wp_GetGenerateName_deepown_kobject i1 l1 kobj with
    "[$Hdeepown_m_l]"). 1: done.
  iIntros "Hdeepown_m_l". wp_auto.
  rewrite bool_decide_false //. wp_auto.
  iPoseProof (KObjectV.deepown_l_merge _ _ _ _ Hl1_not_null with "[$Hdeepown_t_l $Hdeepown_m_l $Hdeepown_s_l $Hdeepown_st_l]") as "Hdeepown_l".
  wp_apply (wp_applyValidationAndDefaulting_ok _ _ _ kind namespace
    (KObjectV.objectmeta kobj).(ObjectMetaV.Name') kobj with "[Hdeepown_l]").
  { iFrame "#". iFrame. iPureIntro. split_and!.
    - destruct kobj; done.
    - exact Hvalid.
    - rewrite /create_prepared_for_helper /=.
      rewrite decide_False.
      1: exact Hname_nonempty.
      rewrite /ObjectMetaV.valid_create in Hvalid_meta_create.
      rewrite decide_False in Hvalid_meta_create.
      1: exact Hname_nonempty.
      destruct Hvalid_meta_create as ((Hgn & Hname_valid) & _).
      destruct kobj; simpl in *; split_and!; try done.
  }
  iIntros (kobj1) "(Hdeepown_l & %Hvalid_interface1 & %Hhelper_result)". wp_auto.
  destruct Hhelper_result as
    (Hcreated1 & Hvalid_without_rv1 & Hname1 & Huid1).
  pose proof Hvalid_without_rv1 as
    (Hvalid_typemeta & Hvalid_meta & Hvalid_spec & Hvalid_status).
  iPoseProof (KObjectV.deepown_l_split with "Hdeepown_l") as
    "(%Hl1_not_null1 & Hdeepown_t_l & Hdeepown_m_l & Hdeepown_s_l & Hdeepown_st_l)".
  assert (KObjectV.kind kobj1 = kind) as Hkind1.
  { destruct kobj, kobj1; simpl in *; subst; done. }
  wp_apply (wp_validateObjectMeta with "[$Hdeepown_m_l]").
  { iSplit; first done. iPureIntro.
    rewrite -Hkind1. exact Hvalid_meta. }
  iIntros "Hdeepown_m_l". wp_auto.
  iAssert (⌜ dom phys_state = dom abs_state ⌝%I) as "%Hdom_eq".
  { iDestruct (big_sepM2_dom with "Hinv_Hphys_abs_rep") as %Hdom_eq. iPureIntro. done. }
  destruct (decide (abs_state !! key = None)) as
    [Hkey_not_in_abs|Hkey_present].
  2: {
    assert (∃ old_i, phys_state !! key = Some old_i) as
      [old_i Hlookup_phys].
    { apply elem_of_dom. rewrite Hdom_eq. apply elem_of_dom.
      rewrite /is_Some. apply not_eq_None_Some. exact Hkey_present. }
    wp_apply (wp_map_lookup2 apimodel.KKey (go.InterfaceType [])
      with "[$Hinv_Hown_phys]").
    iIntros "Hinv_Hown_phys". wp_auto.
    rewrite <-Hrequest_key_eq. rewrite Hlookup_phys. wp_auto.
    wp_apply (wp_NewAlreadyExistsError
      {| schema.GroupResource.Group' := ""%go;
         schema.GroupResource.Resource' := kind |}
      (KObjectV.objectmeta kobj).(ObjectMetaV.Name')).
    iIntros (err_l) "%Halready_exists". wp_auto.
    iApply fupd_wp.
    iMod "Hau" as (reservation children) "H". iNamed "H".
    iPoseProof (kview.own_reservation_valid
      with "[$Hinv_Hown_abs] [$Hown_reserved_frag]") as
      "%Hreservation_valid".
    assert (∃ old_uid old_obj,
        reservation = Deleting old_uid ∧
        abs_state !! key = Some old_obj ∧
        (KObjectV.objectmeta old_obj).(ObjectMetaV.UID') = old_uid ∧
        (KObjectV.objectmeta old_obj).(ObjectMetaV.DeletionTimestamp') ≠ None)
      as (old_uid & old_obj & Hreservation_eq & Hlookup_abs &
          Hold_uid & Hold_terminating).
    { destruct Hreservation_status as
        [Havailable|(old_uid & Hdeleting)].
      - subst reservation.
        destruct Hreservation_valid as [_ Habsent]. contradiction.
      - subst reservation.
        destruct Hreservation_valid as
          [_ [Habsent|(old_obj & Hlookup & Huid & Hterminating)]].
        { contradiction. }
        eexists _, _. split_and!; done. }
    iDestruct "Hclose" as "[_ Hclose]".
    set err := interface.mk_ok
      (go.PointerType api_errors.StatusError) #err_l.
    iMod ("Hclose" $! old_uid err with
      "[Hown_reserved_frag Hown_children_frag]") as "HΦ".
    { subst err reservation. iFrame. done. }
    assert (generated_uid ∉ used_uid) as Hgenerated_uid_fresh.
    { rewrite Hinv_Hused_uid_eq_dom_phys_used_uid.
      apply not_elem_of_dom. exact Hgenerated_uid_is_not_used. }
    iMod (kview.extend_used_uid_vs generated_uid with
      "Hinv_Hown_abs") as "Hinv_Hown_abs".
    iMod (cview.extend_used_reference_vs (key, generated_uid) with
      "Hinv_Hown_children") as "Hinv_Hown_children".
    iMod (deletion_observation.extend_used_uid_vs generated_uid with
      "Hinv_Hown_deletion_observations") as
      "Hinv_Hown_deletion_observations".
    iModIntro.
    iCombineNamed "Hinv_*" as "H".
    wp_apply (wp_Mutex__Unlock _ (kubernetes_inv γ l)
      with "[$Hown_Mutex H]").
    { iNamed "H". iFrame "#". iNext.
      iExists phys_state_l, phys_used_uid_l, phys_used_rv_l,
        phys_state, (<[generated_uid := ()]> phys_used_uid), phys_used_rv,
        abs_state, (used_uid ∪ {[generated_uid]}),
        (used_reference ∪ {[(key, generated_uid)]}).
      iFrame.
      iPureIntro. split_and!.
      - rewrite dom_insert_L Hinv_Hused_uid_eq_dom_phys_used_uid.
        rewrite union_comm_L. done.
      - rewrite set_map_union_L set_map_singleton_L.
        rewrite Hinv_Hused_uid_eq_set_map_used_reference. done. }
    iApply "HΦ". }
  assert (Hkey_not_in_phys : phys_state !! key = None).
  { apply not_elem_of_dom.
    apply not_elem_of_dom in Hkey_not_in_abs.
    rewrite Hdom_eq.
    done.
  }
  wp_apply (wp_map_lookup2 apimodel.KKey (go.InterfaceType []) with "[$Hinv_Hown_phys]").
  iIntros "Hinv_Hown_phys". wp_auto.
  rewrite /is_Some.
  rewrite <-Hrequest_key_eq.
  rewrite Hkey_not_in_phys.
  wp_auto.
  wp_apply (wp_State__generateNewRVAndUpdate with "[$Hinv_Hstate_used_rv_addr $Hinv_Hown_used_rv]").
  iIntros (generated_rv) "(%Hgenerated_rv_is_not_used & %Hgenerated_rv_valid & Hinv_Hstate_used_rv_addr & Hinv_Hown_used_rv)".
  wp_auto.
  wp_apply (wp_SetResourceVersion_deepown_kobject i1 l1 kobj1 with
    "[$Hdeepown_m_l]"). 1: done.
  iIntros "Hdeepown_m_l". wp_auto.
  wp_apply (wp_map_insert apimodel.KKey with "[$Hinv_Hown_phys]"). iIntros "Hinv_Hown_phys". wp_auto.
  iPoseProof (KObjectV.deepown_l_merge _ _ _ _ Hl1_not_null1 with "[$Hdeepown_t_l $Hdeepown_m_l $Hdeepown_s_l $Hdeepown_st_l]") as "Hdeepown_l".
  iAssert (KObjectV.deepown_i i1
    (KObjectV.update_objectmeta kobj1
      ((KObjectV.objectmeta kobj1) <| ObjectMetaV.ResourceVersion' :=
        generated_rv |>)) 1)
    with "[Hdeepown_l]" as "Hdeepown_i1".
  { iExists l1. iSplit.
    { iPureIntro. destruct kobj, kobj1. all: done. }
    iFrame.
  }
  wp_apply (wp_deepCopy with "[$Hpkg $Hdeepown_i1]").
  iIntros (i2) "[Hdeepown_i2 Hdeepown_i1]". wp_auto.
  set kobj2 := (KObjectV.update_objectmeta kobj1
    (KObjectV.objectmeta kobj1 <| ObjectMetaV.ResourceVersion' :=
      generated_rv |>)).
  iApply fupd_wp.
  iMod "Hau" as (reservation children) "H". iNamed "H".
  iPoseProof (kview.own_reservation_valid
    with "[$Hinv_Hown_abs] [$Hown_reserved_frag]") as
    "%Hreservation_valid".
  iPoseProof (cview.own_auth_frag_valid (pk := parent_key) (puid := parent_uid)
    with "[$Hinv_Hown_children] [$Hown_children_frag]")
    as "[%Hchildren_eq_dom %Hin_used_reference]".
  assert (create_stored_from_helper_result kobj1 kobj2) as Hstored2.
  { subst kobj2. rewrite /create_stored_from_helper_result.
    destruct kobj1; simpl; split_and!; try done.
    all: rewrite /ObjectMetaV.equiv_except_resource_version
      /ObjectMetaV.without_resource_version; destruct ObjectMeta'; done. }
  pose proof (create_stored_from_helper_result_created
    namespace kobj kobj1 kobj2 Hcreated1 Hstored2) as Hcreated2.
  pose proof (create_stored_from_helper_result_valid
    kobj1 kobj2 Hvalid_without_rv1 Hstored2) as Hvalid2.
  assert (KObjectV.kind kobj2 = KObjectV.kind kobj) as Hkind2.
  { destruct kobj, kobj2; simpl in *; done. }
  assert ((KObjectV.objectmeta kobj2).(ObjectMetaV.Name') =
      (KObjectV.objectmeta kobj).(ObjectMetaV.Name')) as Hname2.
  { subst kobj2. rewrite objectmeta_update_objectmeta Hname1. destruct kobj; done. }
  assert ((KObjectV.objectmeta kobj2).(ObjectMetaV.Namespace') = namespace ∧
      (KObjectV.objectmeta kobj2).(ObjectMetaV.OwnerReferences') =
        (KObjectV.objectmeta kobj).(ObjectMetaV.OwnerReferences') ∧
      (KObjectV.objectmeta kobj2).(ObjectMetaV.DeletionTimestamp') = None)
    as (Hnamespace2 & Howner_references2 & Hdeletion_timestamp2).
  { destruct kobj, kobj2; rewrite /KObjectV.created /= in Hcreated2; try contradiction;
      rewrite ?/PodV.created ?/ReplicaSetV.created ?/PersistentVolumeClaimV.created
        ?/StatefulSetV.created ?/DeploymentV.created
        /ObjectMetaV.created in Hcreated2;
      simpl; tauto. }
  assert (KObjectV.extra_valid kobj2) as Hextra_valid2.
  { rewrite /KObjectV.extra_valid.
    eapply ObjectSpecV.extra_valid_created.
    - exact Hextra_valid.
    - destruct kobj, kobj2; simpl in Hcreated2 |- *; try done;
        destruct Hcreated2 as (_ & _ & _ & Hspec_created & _); exact Hspec_created. }
  iPoseProof (kview.own_auth_valid_forall with "[$Hinv_Hown_abs]")
    as "%Habs_state_valid".
  assert (generated_uid ∉ used_uid) as Hgenerated_uid_fresh.
  { rewrite Hinv_Hused_uid_eq_dom_phys_used_uid.
    apply not_elem_of_dom. done. }
  assert ((KObjectV.objectmeta kobj2).(ObjectMetaV.UID') = generated_uid)
    as Hkobj2_uid.
  { subst kobj2. rewrite objectmeta_update_objectmeta Huid1. destruct kobj; done. }
  assert (kview.valid_k_uid_obj key generated_uid kobj2)
    as Hvalid_kuid.
  { unfold kview.valid_k_uid_obj.
    rewrite Hkey_eq.
    split_and!.
    - rewrite /KObjectV.key Hkind2 Hname2 Hnamespace2. done.
    - symmetry. exact Hkobj2_uid.
    - exact Hvalid2.
    - exact Hextra_valid2.
  }
  assert ((KObjectV.objectmeta kobj2).(ObjectMetaV.DeletionTimestamp') =
      None) as Hliving.
  { exact Hdeletion_timestamp2. }
  assert (no_speculative_parent_reference
      (KObjectV.objectmeta kobj2) used_uid) as Hno_speculative_parent.
  { intros kind' name' uid' Hparent.
    assert (uid' = parent_uid) as ->.
    { unfold obj_parent_ref_is, meta_parent_ref_is, meta_parent_ref in Hpr, Hparent.
      rewrite Howner_references2 in Hparent.
      destruct ((KObjectV.objectmeta kobj).(ObjectMetaV.OwnerReferences')) as [orefs|] eqn:Horefs;
        simpl in Hpr, Hparent; [|done].
      destruct (list_find (λ oref, oref.(OwnerReferenceV.Controller') = Some true) orefs)
        as [[idx oref]|] eqn:Hfind; [|done].
      inversion Hpr; inversion Hparent; done.
    }
    rewrite Hinv_Hused_uid_eq_set_map_used_reference.
    apply elem_of_map.
    exists (parent_key, parent_uid).
    split; [done | exact Hin_used_reference].
  }
  iAssert (|==>
      kview.own_auth γ.(γ_state)
        (<[key := kobj2]> abs_state) (used_uid ∪ {[generated_uid]}) ∗
      own_meta_frag γ key generated_uid 1 (KObjectV.objectmeta kobj2) ∗
      own_spec_frag γ key generated_uid 1 (KObjectV.spec kobj2) ∗
      own_status_frag γ key generated_uid 1 (KObjectV.status kobj2) ∗
      own_occupied_reserved_frag γ 1 key generated_uid)%I
    with "[Hinv_Hown_abs Hown_reserved_frag]" as
      ">(Hinv_Hown_abs & Hown_meta & Hown_spec & Hown_status &
        Hown_reserved_frag)".
  { destruct Hreservation_status as
      [Havailable|(old_uid & Hdeleting)]; subst reservation.
    - iMod (kview.create_reserved_kobj_vs key generated_uid kobj2
        Hkey_not_in_abs Hgenerated_uid_fresh Hvalid_kuid Hliving
        Hno_speculative_parent with
        "Hinv_Hown_abs Hown_reserved_frag") as "H".
      iModIntro. iExact "H".
    - iMod (kview.create_reserved_from_deleting_kobj_vs
        (old_uid := old_uid) Hkey_not_in_abs Hgenerated_uid_fresh
        Hvalid_kuid Hliving Hno_speculative_parent with
        "Hinv_Hown_abs Hown_reserved_frag") as "H".
      iModIntro. iExact "H". }
  iMod (cview.create_child_vs2 (pk := parent_key) (puid := parent_uid)
    key generated_uid kobj2
    with "[$Hinv_Hown_children] [$Hown_children_frag]")
    as "(Hinv_Hown_children & Hown_children_frag & Hown_grandchildren)".
  { symmetry. exact Hkobj2_uid. }
  { exact Hkey_not_in_abs. }
  { rewrite /living_obj_parent_ref Hdeletion_timestamp2 /=
      /obj_parent_ref /meta_parent_ref Howner_references2.
    unfold obj_parent_ref_is, meta_parent_ref_is, meta_parent_ref in Hpr.
    destruct ((KObjectV.objectmeta kobj).(ObjectMetaV.OwnerReferences'))
      as [orefs|] eqn:Horefs; simpl in Hpr |- *; [|done].
    destruct (list_find
      (fun oref => oref.(OwnerReferenceV.Controller') = Some true) orefs)
      as [[idx oref]|] eqn:Hfind; simpl in Hpr |- *; [|done].
    injection Hpr as Hkey_eq_parent Huid_eq.
    destruct parent_key as [pk_kind pk_name pk_namespace].
    simpl in Hkey_eq_parent, Hns_eq. inversion Hkey_eq_parent; subst.
    rewrite Huid_eq. done. }
  { rewrite map_Forall_lookup.
    intros k' obj Hlookup.
    pose proof (Habs_state_valid _ _ Hlookup) as (_ & _ & _ & Hno_spec & _).
    rewrite Hinv_Hused_uid_eq_set_map_used_reference in Hno_spec.
    exact Hno_spec.
  }
  { intros Hin.
    assert (Huid_fresh : generated_uid ∉ used_uid).
    { apply not_elem_of_dom in Hgenerated_uid_is_not_used.
      rewrite <- Hinv_Hused_uid_eq_dom_phys_used_uid in Hgenerated_uid_is_not_used.
      done.
    }
    apply Huid_fresh. rewrite Hinv_Hused_uid_eq_set_map_used_reference.
    done.
  }
  iMod (terminating_children.create_living_vs
    γ.(γ_terminating_children) abs_state key kobj2 with
    "Hinv_Hown_terminating_children") as
    "Hinv_Hown_terminating_children".
  { exact Hkey_not_in_abs. }
  { unfold terminating_children.terminating_obj_parent_ref.
    rewrite Hdeletion_timestamp2. done. }
  iDestruct "Hclose" as "[Hclose _]".
  iMod ("Hclose" $! i2 kobj2 generated_uid with "[$Hdeepown_i2 $Hown_meta $Hown_spec $Hown_status $Hown_reserved_frag $Hown_children_frag $Hown_grandchildren]") as "HΦ".
  { iSplit.
    { iPureIntro. exact Hvalid2. }
    iPureIntro. split_and!.
    - exact Hcreated2.
    - rewrite Hkey_eq /KObjectV.key Hkind2 Hname2 Hnamespace2. done.
    - apply not_elem_of_dom in Hkey_not_in_abs.
      intro Hin.
      apply Hkey_not_in_abs.
      rewrite Hchildren_eq_dom in Hin.
      apply elem_of_dom in Hin as [obj Hlookup].
      apply map_lookup_filter_Some in Hlookup as [Hlookup _].
      apply elem_of_dom. eexists. done.
    - symmetry. exact Hkobj2_uid. }
  iMod (deletion_observation.create_vs key generated_uid kobj2
    Hgenerated_uid_fresh Hkobj2_uid with
    "Hinv_Hown_deletion_observations") as
    "Hinv_Hown_deletion_observations".
  iModIntro.
  iAssert (([∗ map] i; obj ∈ <[key:=interface.ok i1]> phys_state; <[key:=kobj2]> abs_state,
    match i with
    | interface.ok i_ok => KObjectV.deepown_i i_ok obj 1
    | interface.nil => False%I
    end)%I)
    with "[Hdeepown_i1 Hinv_Hphys_abs_rep]" as "Hinv_Hphys_abs_rep".
  { rewrite (big_sepM2_insert _ phys_state abs_state key (interface.ok i1) kobj2 Hkey_not_in_phys Hkey_not_in_abs).
    iSplitL "Hdeepown_i1".
    - iExact "Hdeepown_i1".
    - iExact "Hinv_Hphys_abs_rep".
  }
  iCombineNamed "Hinv_*" as "H".
  wp_apply (wp_Mutex__Unlock _ (kubernetes_inv γ l) with "[$Hown_Mutex H]").
  { iNamed "H". iFrame. iFrame "#".
    iNext. iFrame.
    iPureIntro. split_and!.
    - rewrite dom_insert_L.
      rewrite Hinv_Hused_uid_eq_dom_phys_used_uid.
      rewrite union_comm_L.
      done.
    - assert (Hobj_ref : obj_ref key kobj2 = (key, generated_uid)).
      { unfold obj_ref. rewrite Hkobj2_uid. reflexivity. }
      assert (Hobj_uid : generated_uid = snd (obj_ref key kobj2)).
      { rewrite Hobj_ref. done. }
      rewrite set_map_union_L.
      rewrite set_map_singleton_L.
      rewrite Hinv_Hused_uid_eq_set_map_used_reference.
      rewrite Hobj_uid.
      done.
  }
  iApply "HΦ".
Unshelve. all: try tc_solve. all: try apply _. all: try exact sem. all: try done.
Qed.

Lemma wp_State__create_named_available γ l kind namespace key i kobj parent_key parent_uid children :
  {{{ is_pkg_init apimodel ∗
      "#Hisk" ∷ is_kubernetes γ l ∗
      "%Hvalid" ∷ ⌜ KObjectV.valid_create kind namespace kobj ⌝ ∗
      "%Hname_nonempty" ∷ ⌜ (KObjectV.objectmeta kobj).(ObjectMetaV.Name') ≠ ""%go ⌝ ∗
      "%Hextra_valid" ∷ ⌜ KObjectV.extra_valid kobj ⌝ ∗
      "%Hns_eq" ∷ ⌜ namespace = parent_key.(KKey.Namespace') ⌝ ∗
      "%Hkey_eq" ∷ ⌜ key = {|
        KKey.Kind' := KObjectV.kind kobj;
        KKey.Name' := (KObjectV.objectmeta kobj).(ObjectMetaV.Name');
        KKey.Namespace' := namespace
      |} ⌝ ∗
      "%Hpr" ∷ ⌜ obj_parent_ref_is kobj parent_key.(KKey.Kind') parent_key.(KKey.Name') parent_uid ⌝ ∗
      "Hdeepown" ∷ KObjectV.deepown_i i kobj 1 ∗
      "Hown_reserved_frag" ∷ own_available_reserved_frag γ 1 key ∗
      "Hown_children_frag" ∷ own_children_frag γ parent_key parent_uid 1 children
  }}}
    l @! (go.PointerType apimodel.State) @! "create" #kind #namespace #(interface.ok i)
  {{{ i' kobj' uid, RET (#(interface.ok i'), #interface.nil);
      "%Hvalid'" ∷ ⌜ KObjectV.valid kobj' ⌝ ∗
      "%Hcreated" ∷ ⌜ KObjectV.created namespace kobj kobj' ⌝ ∗
      "%Hkey_eq'" ∷ ⌜ key = (KObjectV.key kobj') ⌝ ∗
      "%Hkey_fresh" ∷ ⌜ key ∉ children ⌝ ∗
      "%Huid_eq" ∷ ⌜ uid = (KObjectV.objectmeta kobj').(ObjectMetaV.UID') ⌝ ∗
      "Hdeepown_i" ∷ KObjectV.deepown_i i' kobj' 1 ∗
      "Hown_meta_frag" ∷ own_meta_frag γ key uid 1 (KObjectV.objectmeta kobj') ∗
      "Hown_spec_frag" ∷ own_spec_frag γ key uid 1 (KObjectV.spec kobj') ∗
      "Hown_status_frag" ∷ own_status_frag γ key uid 1 (KObjectV.status kobj') ∗
      "Hown_reserved_frag" ∷ own_occupied_reserved_frag γ 1 key uid ∗
      "Hown_children_frag" ∷ own_children_frag γ parent_key parent_uid 1 (children ∪ {[key]}) ∗
      "Hown_grandchildren_frag" ∷ own_children_frag γ key uid 1 ∅
  }}}.
Proof.
  iIntros (Φ) "(#Hinit & H) HΦ". iNamed "H".
  iApply (wp_State__create_named_au γ l kind namespace key i kobj
    parent_key parent_uid).
  iFrame "#". iFrame "%". iFrame "Hdeepown".
  iApply fupd_mask_intro.
  { Timeout 10 set_solver. }
  iIntros "Hmask".
  iExists Available, children.
  iFrame "Hown_reserved_frag Hown_children_frag".
  iSplit; first (iPureIntro; left; done).
  iSplit.
  - iIntros (i' kobj' uid) "Hpost".
    iMod "Hmask" as "_".
    iModIntro. iNext.
    iApply ("HΦ" $! i' kobj' uid with "Hpost").
  - iIntros (old_uid err) "(%Hstatus & _)".
    inversion Hstatus.
Qed.

Lemma wp_State__create_named γ l kind namespace key i kobj parent_key parent_uid children old_uid :
  {{{ is_pkg_init apimodel ∗
      "#Hisk" ∷ is_kubernetes γ l ∗
      "%Hvalid" ∷ ⌜ KObjectV.valid_create kind namespace kobj ⌝ ∗
      "%Hname_nonempty" ∷ ⌜ (KObjectV.objectmeta kobj).(ObjectMetaV.Name') ≠ ""%go ⌝ ∗
      "%Hextra_valid" ∷ ⌜ KObjectV.extra_valid kobj ⌝ ∗
      "%Hns_eq" ∷ ⌜ namespace = parent_key.(KKey.Namespace') ⌝ ∗
      "%Hkey_eq" ∷ ⌜ key = {|
        KKey.Kind' := KObjectV.kind kobj;
        KKey.Name' := (KObjectV.objectmeta kobj).(ObjectMetaV.Name');
        KKey.Namespace' := namespace
      |} ⌝ ∗
      "%Hpr" ∷ ⌜ obj_parent_ref_is kobj parent_key.(KKey.Kind') parent_key.(KKey.Name') parent_uid ⌝ ∗
      "Hdeepown" ∷ KObjectV.deepown_i i kobj 1 ∗
      "Hown_reserved_frag" ∷ own_deleting_reserved_frag γ 1 key old_uid ∗
      "Hown_children_frag" ∷ own_children_frag γ parent_key parent_uid 1 children
  }}}
    l @! (go.PointerType apimodel.State) @! "create" #kind #namespace #(interface.ok i)
  {{{ ret err, RET (#ret, #err);
      (∃ i' kobj' uid,
        ⌜ ret = interface.ok i' ⌝ ∗
        ⌜ err = interface.nil ⌝ ∗
        ⌜ KObjectV.valid kobj' ⌝ ∗
        ⌜ KObjectV.created namespace kobj kobj' ⌝ ∗
        ⌜ key = KObjectV.key kobj' ⌝ ∗
        ⌜ key ∉ children ⌝ ∗
        ⌜ uid = (KObjectV.objectmeta kobj').(ObjectMetaV.UID') ⌝ ∗
        KObjectV.deepown_i i' kobj' 1 ∗
        own_meta_frag γ key uid 1 (KObjectV.objectmeta kobj') ∗
        own_spec_frag γ key uid 1 (KObjectV.spec kobj') ∗
        own_status_frag γ key uid 1 (KObjectV.status kobj') ∗
        own_occupied_reserved_frag γ 1 key uid ∗
        own_children_frag γ parent_key parent_uid 1 (children ∪ {[key]}) ∗
        own_children_frag γ key uid 1 ∅) ∨
      (⌜ ret = interface.nil ⌝ ∗
        ⌜ already_exists_error err ⌝ ∗
        own_deleting_reserved_frag γ 1 key old_uid ∗
        own_children_frag γ parent_key parent_uid 1 children)
  }}}.
Proof.
  iIntros (Φ) "(#Hinit & H) HΦ". iNamed "H".
  iApply (wp_State__create_named_au γ l kind namespace key i kobj
    parent_key parent_uid).
  iFrame "#". iFrame "%". iFrame "Hdeepown".
  iApply fupd_mask_intro.
  { Timeout 10 set_solver. }
  iIntros "Hmask".
  iExists (Deleting old_uid), children.
  iFrame "Hown_reserved_frag Hown_children_frag".
  iSplit; first (iPureIntro; right; eexists; done).
  iSplit.
  - iIntros (i' kobj' uid) "Hpost".
    iMod "Hmask" as "_". iModIntro. iNext.
    iApply ("HΦ" $! (interface.ok i') interface.nil).
    iLeft. iExists i', kobj', uid. iFrame. done.
  - iIntros (returned_old_uid err) "Hpost".
    iDestruct "Hpost" as
      "(%Hstatus & %Halready_exists & Hown_reserved_frag &
        Hown_children_frag)".
    injection Hstatus as ->.
    iMod "Hmask" as "_". iModIntro. iNext.
    iApply ("HΦ" $! interface.nil err).
    iRight. iFrame. done.
Qed.

Lemma wp_State__PodCreate_named_available γ l namespace key pod_l pod parent_key parent_uid children :
  {{{ is_pkg_init apimodel ∗
      "#Hisk" ∷ is_kubernetes γ l ∗
      "%Hvalid" ∷ ⌜ PodV.valid_create PodV.kind namespace pod ⌝ ∗
      "%Hname_nonempty" ∷ ⌜ pod.(PodV.ObjectMeta').(ObjectMetaV.Name') ≠ ""%go ⌝ ∗
      "%Hns_eq" ∷ ⌜ namespace = parent_key.(KKey.Namespace') ⌝ ∗
      "%Hkey_eq" ∷ ⌜ key = {|
        KKey.Kind' := PodV.kind;
        KKey.Name' := pod.(PodV.ObjectMeta').(ObjectMetaV.Name');
        KKey.Namespace' := namespace
      |} ⌝ ∗
      "%Hpr" ∷ ⌜ obj_parent_ref_is (KObjectV.Pod pod) parent_key.(KKey.Kind') parent_key.(KKey.Name') parent_uid ⌝ ∗
      "Hdeepown_l" ∷ PodV.deepown_l pod_l pod 1 ∗
      "Hown_reserved_frag" ∷ own_available_reserved_frag γ 1 key ∗
      "Hown_children_frag" ∷ own_children_frag γ parent_key parent_uid 1 children
  }}}
    l @! (go.PointerType apimodel.State) @! "PodCreate" #namespace #pod_l
  {{{ pod_l' pod' uid, RET (#pod_l', #interface.nil);
      "%Hvalid'" ∷ ⌜ PodV.valid pod' ⌝ ∗
      "%Hcreated" ∷ ⌜ PodV.created namespace pod pod' ⌝ ∗
      "%Hkey_eq'" ∷ ⌜ key = PodV.key pod' ⌝ ∗
      "%Hkey_fresh" ∷ ⌜ key ∉ children ⌝ ∗
      "%Huid_eq" ∷ ⌜ uid = pod'.(PodV.ObjectMeta').(ObjectMetaV.UID') ⌝ ∗
      "Hdeepown_l" ∷ PodV.deepown_l pod_l' pod' 1 ∗
      "Hown_meta_frag" ∷ own_meta_frag γ key uid 1 pod'.(PodV.ObjectMeta') ∗
      "Hown_spec_frag" ∷ own_spec_frag γ key uid 1 (ObjectSpecV.PodSpec pod'.(PodV.Spec')) ∗
      "Hown_status_frag" ∷ own_status_frag γ key uid 1 (ObjectStatusV.PodStatus pod'.(PodV.Status')) ∗
      "Hown_reserved_frag" ∷ own_occupied_reserved_frag γ 1 key uid ∗
      "Hown_children_frag" ∷ own_children_frag γ parent_key parent_uid 1 (children ∪ {[key]}) ∗
      "Hown_grandchildren_frag" ∷ own_children_frag γ key uid 1 ∅
  }}}.
Proof.
  iIntros (Φ) "(#Hinit & H) HΦ". iNamed "H".
  wp_method_call. rewrite /apimodel.State__PodCreateⁱᵐᵖˡ. wp_call. wp_auto.
  iAssert (KObjectV.deepown_i
      (interface.mk (go.PointerType v1.Pod) #pod_l)
      (KObjectV.Pod pod) 1)
    with "[Hdeepown_l]" as "Hdeepown_i".
  { iExists pod_l. iSplit; [iPureIntro; apply KObjectV.valid_interface_Pod|]. iFrame. }
  wp_apply (wp_State__create_named_available
    γ l PodV.kind namespace key
    (interface.mk (go.PointerType v1.Pod) #pod_l)
    (KObjectV.Pod pod) parent_key parent_uid children
    with "[$Hinit $Hisk $Hdeepown_i
      $Hown_reserved_frag $Hown_children_frag]").
  { iPureIntro.
    split_and!; done. }
  iIntros (i' kobj' uid) "Hpost". iNamed "Hpost".
  destruct kobj' as [pod'|rs'|pvc'|sts'|d']; try done.
  iDestruct "Hdeepown_i" as (pod_l') "[%Hi' Hdeepown_l]".
  wp_auto.
  unfold KObjectV.valid_interface in Hi'. destruct Hi' as [Hi' _]. rewrite Hi'.
  change (go.PointerType api_core_v1.Pod) with (go.PointerType v1.Pod).
  cbn [interface.ty interface.v].
  replace
    (if decide (go.PointerType v1.Pod = go.PointerType v1.Pod)
     then #pod_l' else #null)%V
    with (#pod_l')%V by (rewrite decide_True; done).
  replace
    (bool_decide (go.PointerType v1.Pod = go.PointerType v1.Pod))
    with true by (symmetry; apply bool_decide_eq_true_2; done).
  wp_auto.
  iApply "HΦ". iFrame. iPureIntro. split_and!; done.
Qed.

Lemma wp_State__PodCreate_named γ l namespace key pod_l pod parent_key parent_uid children old_uid :
  {{{ is_pkg_init apimodel ∗
      "#Hisk" ∷ is_kubernetes γ l ∗
      "%Hvalid" ∷ ⌜ PodV.valid_create PodV.kind namespace pod ⌝ ∗
      "%Hname_nonempty" ∷ ⌜ pod.(PodV.ObjectMeta').(ObjectMetaV.Name') ≠ ""%go ⌝ ∗
      "%Hns_eq" ∷ ⌜ namespace = parent_key.(KKey.Namespace') ⌝ ∗
      "%Hkey_eq" ∷ ⌜ key = {|
        KKey.Kind' := PodV.kind;
        KKey.Name' := pod.(PodV.ObjectMeta').(ObjectMetaV.Name');
        KKey.Namespace' := namespace
      |} ⌝ ∗
      "%Hpr" ∷ ⌜ obj_parent_ref_is (KObjectV.Pod pod) parent_key.(KKey.Kind') parent_key.(KKey.Name') parent_uid ⌝ ∗
      "Hdeepown_l" ∷ PodV.deepown_l pod_l pod 1 ∗
      "Hown_reserved_frag" ∷ own_deleting_reserved_frag γ 1 key old_uid ∗
      "Hown_children_frag" ∷ own_children_frag γ parent_key parent_uid 1 children
  }}}
    l @! (go.PointerType apimodel.State) @! "PodCreate" #namespace #pod_l
  {{{ ret err, RET (#ret, #err);
      (∃ pod_l' pod' uid,
        ⌜ ret = pod_l' ⌝ ∗
        ⌜ err = interface.nil ⌝ ∗
        ⌜ PodV.valid pod' ⌝ ∗
        ⌜ PodV.created namespace pod pod' ⌝ ∗
        ⌜ key = PodV.key pod' ⌝ ∗
        ⌜ key ∉ children ⌝ ∗
        ⌜ uid = pod'.(PodV.ObjectMeta').(ObjectMetaV.UID') ⌝ ∗
        PodV.deepown_l pod_l' pod' 1 ∗
        own_meta_frag γ key uid 1 pod'.(PodV.ObjectMeta') ∗
        own_spec_frag γ key uid 1 (ObjectSpecV.PodSpec pod'.(PodV.Spec')) ∗
        own_status_frag γ key uid 1 (ObjectStatusV.PodStatus pod'.(PodV.Status')) ∗
        own_occupied_reserved_frag γ 1 key uid ∗
        own_children_frag γ parent_key parent_uid 1 (children ∪ {[key]}) ∗
        own_children_frag γ key uid 1 ∅) ∨
      (⌜ ret = null ⌝ ∗
        ⌜ already_exists_error err ⌝ ∗
        own_deleting_reserved_frag γ 1 key old_uid ∗
        own_children_frag γ parent_key parent_uid 1 children)
  }}}.
Proof.
  iIntros (Φ) "(#Hinit & H) HΦ". iNamed "H".
  wp_method_call. rewrite /apimodel.State__PodCreateⁱᵐᵖˡ. wp_call. wp_auto.
  iAssert (KObjectV.deepown_i
      (interface.mk (go.PointerType v1.Pod) #pod_l)
      (KObjectV.Pod pod) 1)
    with "[Hdeepown_l]" as "Hdeepown_i".
  { iExists pod_l. iSplit; [iPureIntro; apply KObjectV.valid_interface_Pod|]. iFrame. }
  wp_apply (wp_State__create_named
    γ l PodV.kind namespace key
    (interface.mk (go.PointerType v1.Pod) #pod_l)
    (KObjectV.Pod pod) parent_key parent_uid children old_uid
    with "[$Hinit $Hisk $Hdeepown_i
      $Hown_reserved_frag $Hown_children_frag]").
  { iPureIntro.
    split_and!; done. }
  iIntros (created err) "[Hsuccess|Herror]".
  - iDestruct "Hsuccess" as
      (i' kobj' uid) "(%Hcreated & %Herr & Hpost)".
    subst created err.
    iDestruct "Hpost" as
      "(%Hvalid' & %Hcreated & %Hkey_eq' & %Hkey_fresh & %Huid_eq &
        Hdeepown_i & Hown_meta_frag & Hown_spec_frag &
        Hown_status_frag & Hown_reserved_frag & Hown_children_frag &
        Hown_grandchildren_frag)".
    destruct kobj' as [pod'|rs'|pvc'|sts'|d']; try done.
    iDestruct "Hdeepown_i" as (pod_l') "[%Hi' Hdeepown_l]".
    wp_auto.
    unfold KObjectV.valid_interface in Hi'. destruct Hi' as [Hi' _]. rewrite Hi'.
    change (go.PointerType api_core_v1.Pod) with (go.PointerType v1.Pod).
    cbn [interface.ty interface.v].
    replace
      (if decide (go.PointerType v1.Pod = go.PointerType v1.Pod)
       then #pod_l' else #null)%V
      with (#pod_l')%V by (rewrite decide_True; done).
    replace
      (bool_decide (go.PointerType v1.Pod = go.PointerType v1.Pod))
      with true by (symmetry; apply bool_decide_eq_true_2; done).
    wp_auto. iApply "HΦ". iLeft. iExists pod_l', pod', uid.
    iFrame. iPureIntro. split_and!; done.
  - iDestruct "Herror" as
      "(%Hcreated & %Halready_exists & Hown_reserved_frag &
        Hown_children_frag)".
    subst created.
    pose proof (already_exists_error_not_nil err Halready_exists) as Herr.
    destruct err as [err_v|]; last contradiction.
    wp_auto.
    iApply ("HΦ" $! null (interface.ok err_v)).
    iRight. iFrame. done.
Qed.

(* The ReplicaSet counterpart of [wp_State__PodCreate_named_available].

   Only the Available variant is provided: the Deployment controller creates a
   ReplicaSet under a deterministic name while holding that name's available
   reservation, which is exactly what rules out the AlreadyExists return. If a
   caller ever needs the Deleting variant, mirror [wp_State__PodCreate_named]
   the same way.

   Unlike the Pod case this carries [ReplicaSetV.extra_valid] explicitly:
   [ObjectSpecV.extra_valid] is [True] for every kind except ReplicaSet, where
   it constrains the label selector. *)
Lemma wp_State__ReplicaSetCreate_named_available γ l namespace key rs_l rs
    parent_key parent_uid children :
  {{{ is_pkg_init apimodel ∗
      "#Hisk" ∷ is_kubernetes γ l ∗
      "%Hvalid" ∷ ⌜ ReplicaSetV.valid_create ReplicaSetV.kind namespace rs ⌝ ∗
      "%Hname_nonempty" ∷
        ⌜ rs.(ReplicaSetV.ObjectMeta').(ObjectMetaV.Name') ≠ ""%go ⌝ ∗
      "%Hextra_valid" ∷ ⌜ ReplicaSetV.extra_valid rs ⌝ ∗
      "%Hns_eq" ∷ ⌜ namespace = parent_key.(KKey.Namespace') ⌝ ∗
      "%Hkey_eq" ∷ ⌜ key = {|
        KKey.Kind' := ReplicaSetV.kind;
        KKey.Name' := rs.(ReplicaSetV.ObjectMeta').(ObjectMetaV.Name');
        KKey.Namespace' := namespace
      |} ⌝ ∗
      "%Hpr" ∷ ⌜ obj_parent_ref_is (KObjectV.ReplicaSet rs)
          parent_key.(KKey.Kind') parent_key.(KKey.Name') parent_uid ⌝ ∗
      "Hdeepown_l" ∷ ReplicaSetV.deepown_l rs_l rs 1 ∗
      "Hown_reserved_frag" ∷ own_available_reserved_frag γ 1 key ∗
      "Hown_children_frag" ∷ own_children_frag γ parent_key parent_uid 1 children
  }}}
    l @! (go.PointerType apimodel.State) @! "ReplicaSetCreate" #namespace #rs_l
  {{{ rs_l' rs' uid, RET (#rs_l', #interface.nil);
      "%Hvalid'" ∷ ⌜ ReplicaSetV.valid rs' ⌝ ∗
      "%Hmeta_created" ∷ ⌜ ObjectMetaV.created namespace
          rs.(ReplicaSetV.ObjectMeta') rs'.(ReplicaSetV.ObjectMeta') ⌝ ∗
      "%Hspec_created" ∷ ⌜ ObjectSpecV.created
          (ObjectSpecV.ReplicaSetSpec rs.(ReplicaSetV.Spec'))
          (ObjectSpecV.ReplicaSetSpec rs'.(ReplicaSetV.Spec')) ⌝ ∗
      "%Hstatus_created" ∷ ⌜ ObjectStatusV.created
          (ObjectStatusV.ReplicaSetStatus rs.(ReplicaSetV.Status'))
          (ObjectStatusV.ReplicaSetStatus rs'.(ReplicaSetV.Status')) ⌝ ∗
      "%Hkey_eq'" ∷ ⌜ key = ReplicaSetV.key rs' ⌝ ∗
      "%Hkey_fresh" ∷ ⌜ key ∉ children ⌝ ∗
      "%Huid_eq" ∷ ⌜ uid = rs'.(ReplicaSetV.ObjectMeta').(ObjectMetaV.UID') ⌝ ∗
      "Hdeepown_l" ∷ ReplicaSetV.deepown_l rs_l' rs' 1 ∗
      "Hown_meta_frag" ∷ own_meta_frag γ key uid 1 rs'.(ReplicaSetV.ObjectMeta') ∗
      "Hown_spec_frag" ∷ own_spec_frag γ key uid 1
        (ObjectSpecV.ReplicaSetSpec rs'.(ReplicaSetV.Spec')) ∗
      "Hown_status_frag" ∷ own_status_frag γ key uid 1
        (ObjectStatusV.ReplicaSetStatus rs'.(ReplicaSetV.Status')) ∗
      "Hown_reserved_frag" ∷ own_occupied_reserved_frag γ 1 key uid ∗
      "Hown_children_frag" ∷ own_children_frag γ parent_key parent_uid 1
        (children ∪ {[key]}) ∗
      "Hown_grandchildren_frag" ∷ own_children_frag γ key uid 1 ∅
  }}}.
Proof.
  iIntros (Φ) "(#Hinit & H) HΦ". iNamed "H".
  wp_method_call. rewrite /apimodel.State__ReplicaSetCreateⁱᵐᵖˡ. wp_call. wp_auto.
  iAssert (KObjectV.deepown_i
      (interface.mk (go.PointerType v1.ReplicaSet) #rs_l)
      (KObjectV.ReplicaSet rs) 1)
    with "[Hdeepown_l]" as "Hdeepown_i".
  { iExists rs_l. iSplit; [done|]. iFrame. }
  wp_apply (wp_State__create_named_available
    γ l ReplicaSetV.kind namespace key
    (interface.mk (go.PointerType v1.ReplicaSet) #rs_l)
    (KObjectV.ReplicaSet rs) parent_key parent_uid children
    with "[$Hinit $Hisk $Hdeepown_i
      $Hown_reserved_frag $Hown_children_frag]").
  { iPureIntro.
    split_and!; done. }
  iIntros (i' kobj' uid) "Hpost". iNamed "Hpost".
  destruct kobj' as [pod'|rs'|pvc'|sts'|d']; try done.
  simpl in Hcreated.
  destruct Hcreated as
    (_ & Hmeta_created & _ & Hspec_created & Hstatus_created).
  iDestruct "Hdeepown_i" as (rs_l') "[%Hi' Hdeepown_l]".
  wp_auto.
  unfold KObjectV.valid_interface in Hi'. rewrite Hi'.
  change (go.PointerType api_apps_v1.ReplicaSet) with (go.PointerType v1.ReplicaSet).
  cbn [interface.ty interface.v].
  replace
    (if decide (go.PointerType v1.ReplicaSet = go.PointerType v1.ReplicaSet)
     then #rs_l' else #null)%V
    with (#rs_l')%V by (rewrite decide_True; done).
  replace
    (bool_decide (go.PointerType v1.ReplicaSet = go.PointerType v1.ReplicaSet))
    with true by (symmetry; apply bool_decide_eq_true_2; done).
  wp_auto.
  iApply "HΦ". iFrame. iPureIntro. split_and!; done.
Qed.

End proof.
