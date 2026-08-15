From New.proof Require Import prelude empty_ffi.
From New.proof.kubernetes_model Require Export common_create.

Section proof.
Context `{hG: !heapGS Σ} `{!ffi_semantics _ _}.
Context {sem : go.Semantics} {package_sem : apimodel.Assumptions}.
Context `{!kubernetesModelG Σ}.
Local Set Default Proof Using "All".

Lemma wp_State__create_named_au γ l kind namespace key i kobj parent_key parent_uid reservation :
  ∀ Φ,
  ( is_pkg_init apimodel ∗
    is_kubernetes γ l ∗
    "%Hvalid" ∷ ⌜ KObjectV.valid_named_create kind namespace kobj ⌝ ∗
    "%Hns_nonempty" ∷ ⌜ namespace ≠ ""%go ⌝ ∗
    "%Hns_valid" ∷ ⌜ valid_namespace namespace ⌝ ∗
    "%Hns_eq" ∷ ⌜ namespace = parent_key.(KKey.Namespace') ⌝ ∗
    "%Hkey_eq" ∷ ⌜ key = {|
      KKey.Kind' := kind;
      KKey.Name' := (KObjectV.objectmeta kobj).(ObjectMetaV.Name');
      KKey.Namespace' := namespace
    |} ⌝ ∗
    "%Hpr" ∷ ⌜ obj_parent_ref_is kobj parent_key.(KKey.Kind') parent_key.(KKey.Name') parent_uid ⌝ ∗
    "Hdeepown_i" ∷ KObjectV.deepown_i i kobj 1 ∗
    "%Hreservation_status" ∷ ⌜ reservation = Available ∨ ∃ old_uid, reservation = Deleting old_uid ⌝ ∗
    "Hown_reserved_frag" ∷ own_reserved_frag γ key 1 reservation ∗
    |={⊤,∅}=> ∃ children,
      "Hown_children_frag" ∷ own_children_frag γ parent_key parent_uid 1 children ∗
      "Hclose" ∷
        ((∀ i' kobj' uid,
          ⌜ KObjectV.valid kobj' ⌝ ∗
          ⌜ KObjectV.same_kind kobj kobj' ⌝ ∗
          ⌜ ObjectMetaV.named_created namespace (KObjectV.objectmeta kobj) (KObjectV.objectmeta kobj') ⌝ ∗
          ⌜ ObjectSpecV.created (KObjectV.spec kobj) (KObjectV.spec kobj') ⌝ ∗
          ⌜ ObjectStatusV.created (KObjectV.status kobj) (KObjectV.status kobj') ⌝ ∗
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
    destruct Hvalid as (_ & _ & Hmeta & _).
    destruct Hmeta as (_ & _ & _ & Hns & _).
    destruct Hns as [Hns|(_ & Hns)]; rewrite Hns; auto.
  }
  iIntros "Hdeepown_m_l". wp_auto.
  wp_apply v1.wp_Now. iIntros (now_time now_timev) "Hdeepown_time". wp_auto.
  wp_apply (wp_SetCreationTimestamp_deepown with "[$Hdeepown_m_l $Hdeepown_time]"). iIntros "Hdeepown_m_l". wp_auto.
  wp_apply (wp_State__generateNewUIDAndUpdate with "[$Hinv_Hstate_used_uid_addr $Hinv_Hown_used_uid]").
  iIntros (generated_uid) "(%Hgenerated_uid_is_not_used & %Hgenerated_uid_valid & Hinv_Hstate_used_uid_addr & Hinv_Hown_used_uid)". wp_auto.
  wp_apply (wp_SetUID_deepown with "[$Hdeepown_m_l]"). iIntros "Hdeepown_m_l". wp_auto.
  wp_apply (wp_GetName_deepown with "[$Hdeepown_m_l]"). iIntros "Hdeepown_m_l". wp_auto.
  wp_apply (wp_GetGenerateName_deepown with "[$Hdeepown_m_l]"). iIntros "Hdeepown_m_l". wp_auto.
  assert ((KObjectV.objectmeta kobj).(ObjectMetaV.Name') ≠ ""%go) as Hname_nonempty.
  { destruct Hvalid as (_ & _ & Hmeta & _).
    destruct Hmeta as (_ & Hname_nonempty & _).
    done.
  }
  rewrite bool_decide_false //. wp_auto.
  iPoseProof (KObjectV.deepown_l_merge _ _ _ _ Hl1_not_null with "[$Hdeepown_t_l $Hdeepown_m_l $Hdeepown_s_l $Hdeepown_st_l]") as "Hdeepown_l".
  wp_apply (wp_applyValidationAndDefaulting with "[Hdeepown_l]").
  { iFrame.
    iPureIntro.
    destruct Hvalid as (Hkind & Hvalid_create_typemeta & Hmeta & _).
    destruct Hmeta as (Hgn_valid & Hname_nonempty' & Hname_valid & _ & Hlabels & Hannotations & Howner_refs & Hfinalizers & Hmanaged_fields).
    split.
    - destruct kobj; done.
    - split.
      + rewrite KObjectV.kind_update_objectmeta
          KObjectV.typemeta_update_objectmeta.
        exact Hvalid_create_typemeta.
      + destruct kobj; simpl in Hkind |- *; subst kind; split_and!; done.
  }
  iIntros (kobj1) "(Hdeepown_l & %Hsame_kind & %Hvalid_meta & %Hvalid_spec & %Hvalid_status & %Hvalid_typemeta & %Hm_eq &
    %Hcreated_spec & %Hcreated_status)". wp_auto.
  iPoseProof (KObjectV.deepown_l_split with "Hdeepown_l") as
    "(%Hl1_not_null1 & Hdeepown_t_l & Hdeepown_m_l & Hdeepown_s_l & Hdeepown_st_l)".
  assert (KObjectV.objectmeta_ptr l1 kobj = KObjectV.objectmeta_ptr l1 kobj1) as ->.
  { destruct kobj, kobj1; done. }
  assert (KObjectV.kind kobj1 = kind) as Hkind1.
  { destruct Hvalid as (Hkind & _).
    destruct kobj, kobj1; simpl in *; subst; done. }
  wp_apply (wp_validateObjectMeta with "[$Hdeepown_m_l]").
  { iSplit; first done. iPureIntro.
    rewrite -Hkind1. exact Hvalid_meta. }
  iIntros "Hdeepown_m_l". wp_auto.
  iAssert (⌜ dom phys_state = dom abs_state ⌝%I) as "%Hdom_eq".
  { iDestruct (big_sepM2_dom with "Hinv_Hphys_abs_rep") as %Hdom_eq. iPureIntro. done. }
  iPoseProof (kview.own_reservation_valid
    with "[$Hinv_Hown_abs] [$Hown_reserved_frag]") as
    "%Hreservation_valid".
  destruct (decide (abs_state !! key = None)) as
    [Hkey_not_in_abs|Hkey_present].
  2: {
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
    assert (∃ old_i, phys_state !! key = Some old_i) as
      [old_i Hlookup_phys].
    { apply elem_of_dom. rewrite Hdom_eq. apply elem_of_dom.
      eexists. exact Hlookup_abs. }
    wp_apply (wp_map_lookup2 apimodel.KKey (go.InterfaceType [])
      with "[$Hinv_Hown_phys]").
    iIntros "Hinv_Hown_phys". wp_auto.
    rewrite <- Hkey_eq. rewrite Hlookup_phys. wp_auto.
    wp_apply (wp_NewAlreadyExistsError
      {| schema.GroupResource.Group' := ""%go;
         schema.GroupResource.Resource' := kind |}
      (KObjectV.objectmeta kobj).(ObjectMetaV.Name')).
    iIntros (err_l) "%Halready_exists". wp_auto.
    iApply fupd_wp.
    iMod "Hau" as (children) "H". iNamed "H".
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
  rewrite <- Hkey_eq.
  rewrite Hkey_not_in_phys.
  wp_auto.
  wp_apply (wp_State__generateNewRVAndUpdate with "[$Hinv_Hstate_used_rv_addr $Hinv_Hown_used_rv]").
  iIntros (generated_rv) "(%Hgenerated_rv_is_not_used & %Hgenerated_rv_valid & Hinv_Hstate_used_rv_addr & Hinv_Hown_used_rv)".
  wp_auto.
  wp_apply (wp_SetResourceVersion_deepown with "[$Hdeepown_m_l]"). iIntros "Hdeepown_m_l". wp_auto.
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
  iMod "Hau" as (children) "H". iNamed "H".
  iPoseProof (cview.own_auth_frag_valid (pk := parent_key) (puid := parent_uid)
    with "[$Hinv_Hown_children] [$Hown_children_frag]")
    as "[%Hchildren_eq_dom %Hin_used_reference]".
  assert (KObjectV.valid kobj2) as Hvalid2.
  { subst kobj2.
    destruct Hvalid as (Hkind_eq & _).
    destruct kobj; destruct kobj1; try done.
    all: solve_update_objectmeta_valid
      Hvalid_typemeta Hgenerated_rv_valid Hvalid_meta Hvalid_spec
      Hvalid_status.
  }
  iPoseProof (kview.own_auth_valid_forall with "[$Hinv_Hown_abs]")
    as "%Habs_state_valid".
  assert (generated_uid ∉ used_uid) as Hgenerated_uid_fresh.
  { rewrite Hinv_Hused_uid_eq_dom_phys_used_uid.
    apply not_elem_of_dom. done. }
  assert ((KObjectV.objectmeta kobj2).(ObjectMetaV.UID') = generated_uid)
    as Hkobj2_uid.
  { subst kobj2. destruct kobj; destruct kobj1; try done;
      rewrite Hm_eq; done. }
  assert (kview.valid_k_uid_obj key generated_uid kobj2)
    as Hvalid_kuid.
  { unfold kview.valid_k_uid_obj.
    rewrite Hkey_eq.
    subst kobj2.
    split_and!.
    - destruct Hvalid as (Hkind_eq & _).
      destruct kobj; destruct kobj1; try done;
      rewrite Hm_eq; simpl; rewrite Hkind_eq; done.
    - symmetry. exact Hkobj2_uid.
    - exact Hvalid2.
  }
  assert ((KObjectV.objectmeta kobj2).(ObjectMetaV.DeletionTimestamp') =
      None) as Hliving.
  { subst kobj2.
    destruct kobj; destruct kobj1; try done;
      rewrite Hm_eq; done. }
  assert (no_speculative_parent_reference
      (KObjectV.objectmeta kobj2) used_uid) as Hno_speculative_parent.
  { intros kind' name' uid' Hparent.
    assert (uid' = parent_uid) as ->.
    { subst kobj2.
      destruct kobj; destruct kobj1;
      try done.
      all: rewrite Hm_eq in Hparent;
        unfold obj_parent_ref_is, meta_parent_ref_is, meta_parent_ref in Hpr, Hparent;
        simpl in Hpr, Hparent;
        lazymatch goal with
          | Hpr : context [ObjectMetaV.OwnerReferences' ?meta],
            Hparent : context [ObjectMetaV.OwnerReferences' ?meta] |- _ =>
              destruct (ObjectMetaV.OwnerReferences' meta) as [orefs|] eqn:Horefs
          end;
          [|done];
        lazymatch goal with
          | Hpr : context [list_find ?f ?orefs],
            Hparent : context [list_find ?f ?orefs] |- _ =>
              destruct (list_find f orefs) as [[idx oref]|] eqn:Hfind
          end;
          [|done];
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
  { subst kobj2.
    destruct kobj; destruct kobj1;
    try done; rewrite Hm_eq; done.
  }
  { exact Hkey_not_in_abs. }
  { subst kobj2.
    destruct kobj; destruct kobj1;
    try done.
    all: rewrite Hm_eq;
      unfold obj_parent_ref_is, meta_parent_ref_is, meta_parent_ref in Hpr |- *;
      simpl in Hpr |- *;
      lazymatch goal with
        | Hpr : context [ObjectMetaV.OwnerReferences' ?meta] |- _ =>
            destruct (ObjectMetaV.OwnerReferences' meta) as [orefs|] eqn:Horefs
        end;
        simpl in Hpr |- *;
        [|done];
      lazymatch goal with
        | Hpr : context [list_find ?f ?orefs] |- _ =>
            destruct (list_find f orefs) as [[idx oref]|] eqn:Hfind
        end;
        simpl in Hpr |- *;
        [|done];
      injection Hpr as Hkey_eq_parent Huid_eq;
      destruct parent_key as [pk_kind pk_name pk_namespace];
      simpl in Hkey_eq_parent; inversion Hkey_eq_parent; subst;
      unfold living_obj_parent_ref; simpl;
      unfold obj_parent_ref, meta_parent_ref; simpl;
      rewrite Hfind Huid_eq; done.
  }
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
    subst kobj2. destruct kobj; destruct kobj1; try done;
      rewrite Hm_eq; done. }
  iDestruct "Hclose" as "[Hclose _]".
  iMod ("Hclose" $! i2 kobj2 generated_uid with "[$Hdeepown_i2 $Hown_meta $Hown_spec $Hown_status $Hown_reserved_frag $Hown_children_frag $Hown_grandchildren]") as "HΦ".
  { iSplit.
    { iPureIntro. exact Hvalid2. }
    iPureIntro. split_and!.
    - subst kobj2.
      destruct kobj; destruct kobj1; done.
    - unfold ObjectMetaV.named_created.
      subst kobj2.
      destruct kobj; destruct kobj1;
      simpl in Hm_eq |- *;
      try done; rewrite Hm_eq; split_and!; done.
    - subst kobj2.
      rewrite KObjectV.spec_update_objectmeta.
      rewrite KObjectV.spec_update_objectmeta in Hcreated_spec.
      done.
    - subst kobj2.
      rewrite KObjectV.status_update_objectmeta.
      rewrite KObjectV.status_update_objectmeta in Hcreated_status.
      done.
    - subst kobj2.
      rewrite Hkey_eq.
      destruct Hvalid as (Hkind_eq & _).
      destruct kobj; destruct kobj1;
      simpl in Hsame_kind, Hm_eq, Hkind_eq |- *;
      try done; rewrite Hm_eq; rewrite Hkind_eq; done.
    - apply not_elem_of_dom in Hkey_not_in_abs.
      intro Hin.
      apply Hkey_not_in_abs.
      rewrite Hchildren_eq_dom in Hin.
      apply elem_of_dom in Hin as [obj Hlookup].
      apply map_lookup_filter_Some in Hlookup as [Hlookup _].
      apply elem_of_dom. eexists. done.
    - subst kobj2.
      destruct kobj; destruct kobj1;
      simpl in Hm_eq |- *;
      try done; rewrite Hm_eq; done. }
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
      { unfold obj_ref. subst kobj2.
        rewrite Hkey_eq.
        destruct kobj; destruct kobj1;
        simpl in Hsame_kind, Hm_eq |- *;
        try done; rewrite Hm_eq; reflexivity.
      }
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
      "%Hvalid" ∷ ⌜ KObjectV.valid_named_create kind namespace kobj ⌝ ∗
      "%Hns_nonempty" ∷ ⌜ namespace ≠ ""%go ⌝ ∗
      "%Hns_valid" ∷ ⌜ valid_namespace namespace ⌝ ∗
      "%Hns_eq" ∷ ⌜ namespace = parent_key.(KKey.Namespace') ⌝ ∗
      "%Hkey_eq" ∷ ⌜ key = {|
        KKey.Kind' := kind;
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
      "%Hsame_kind" ∷ ⌜ KObjectV.same_kind kobj kobj' ⌝ ∗
      "%Hmeta_created" ∷
        ⌜ ObjectMetaV.named_created namespace (KObjectV.objectmeta kobj) (KObjectV.objectmeta kobj') ⌝ ∗
      "%Hspec_created" ∷ ⌜ ObjectSpecV.created (KObjectV.spec kobj) (KObjectV.spec kobj') ⌝ ∗
      "%Hstatus_created" ∷ ⌜ ObjectStatusV.created (KObjectV.status kobj) (KObjectV.status kobj') ⌝ ∗
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
    parent_key parent_uid Available).
  iFrame "#". iFrame "%". iFrame "Hdeepown".
  iSplit; first (iPureIntro; left; done).
  iFrame "Hown_reserved_frag".
  iApply fupd_mask_intro.
  { Timeout 10 set_solver. }
  iIntros "Hmask".
  iExists children.
  iFrame "Hown_children_frag".
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
      "%Hvalid" ∷ ⌜ KObjectV.valid_named_create kind namespace kobj ⌝ ∗
      "%Hns_nonempty" ∷ ⌜ namespace ≠ ""%go ⌝ ∗
      "%Hns_valid" ∷ ⌜ valid_namespace namespace ⌝ ∗
      "%Hns_eq" ∷ ⌜ namespace = parent_key.(KKey.Namespace') ⌝ ∗
      "%Hkey_eq" ∷ ⌜ key = {|
        KKey.Kind' := kind;
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
        ⌜ KObjectV.same_kind kobj kobj' ⌝ ∗
        ⌜ ObjectMetaV.named_created namespace (KObjectV.objectmeta kobj) (KObjectV.objectmeta kobj') ⌝ ∗
        ⌜ ObjectSpecV.created (KObjectV.spec kobj) (KObjectV.spec kobj') ⌝ ∗
        ⌜ ObjectStatusV.created (KObjectV.status kobj) (KObjectV.status kobj') ⌝ ∗
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
    parent_key parent_uid (Deleting old_uid)).
  iFrame "#". iFrame "%". iFrame "Hdeepown".
  iSplit; first (iPureIntro; right; eexists; done).
  iFrame "Hown_reserved_frag".
  iApply fupd_mask_intro.
  { Timeout 10 set_solver. }
  iIntros "Hmask".
  iExists children. iFrame "Hown_children_frag".
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
      "%Hvalid" ∷ ⌜ PodV.valid_named_create namespace pod ⌝ ∗
      "%Hns_nonempty" ∷ ⌜ namespace ≠ ""%go ⌝ ∗
      "%Hns_valid" ∷ ⌜ valid_namespace namespace ⌝ ∗
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
      "%Hmeta_created" ∷ ⌜ ObjectMetaV.named_created namespace pod.(PodV.ObjectMeta') pod'.(PodV.ObjectMeta') ⌝ ∗
      "%Hspec_created" ∷
        ⌜ ObjectSpecV.created (ObjectSpecV.PodSpec pod.(PodV.Spec')) (ObjectSpecV.PodSpec pod'.(PodV.Spec')) ⌝ ∗
      "%Hstatus_created" ∷
        ⌜ ObjectStatusV.created
          (ObjectStatusV.PodStatus pod.(PodV.Status'))
          (ObjectStatusV.PodStatus pod'.(PodV.Status')) ⌝ ∗
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
  { iExists pod_l. iSplit; [done|]. iFrame. }
  wp_apply (wp_State__create_named_available
    γ l PodV.kind namespace key
    (interface.mk (go.PointerType v1.Pod) #pod_l)
    (KObjectV.Pod pod) parent_key parent_uid children
    with "[$Hinit $Hisk $Hdeepown_i
      $Hown_reserved_frag $Hown_children_frag]").
  { iPureIntro.
    rewrite KObjectV.valid_named_create_eq_valid_named_create2 /=.
    split_and!; done. }
  iIntros (i' kobj' uid) "Hpost". iNamed "Hpost".
  destruct kobj' as [pod'|rs'|pvc'|sts']; try done.
  iDestruct "Hdeepown_i" as (pod_l') "[%Hi' Hdeepown_l]".
  wp_auto.
  unfold KObjectV.valid_interface in Hi'. rewrite Hi'.
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
      "%Hvalid" ∷ ⌜ PodV.valid_named_create namespace pod ⌝ ∗
      "%Hns_nonempty" ∷ ⌜ namespace ≠ ""%go ⌝ ∗
      "%Hns_valid" ∷ ⌜ valid_namespace namespace ⌝ ∗
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
        ⌜ ObjectMetaV.named_created namespace pod.(PodV.ObjectMeta') pod'.(PodV.ObjectMeta') ⌝ ∗
        ⌜ ObjectSpecV.created (ObjectSpecV.PodSpec pod.(PodV.Spec')) (ObjectSpecV.PodSpec pod'.(PodV.Spec')) ⌝ ∗
        ⌜ ObjectStatusV.created
          (ObjectStatusV.PodStatus pod.(PodV.Status'))
          (ObjectStatusV.PodStatus pod'.(PodV.Status')) ⌝ ∗
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
  { iExists pod_l. iSplit; [done|]. iFrame. }
  wp_apply (wp_State__create_named
    γ l PodV.kind namespace key
    (interface.mk (go.PointerType v1.Pod) #pod_l)
    (KObjectV.Pod pod) parent_key parent_uid children old_uid
    with "[$Hinit $Hisk $Hdeepown_i
      $Hown_reserved_frag $Hown_children_frag]").
  { iPureIntro.
    rewrite KObjectV.valid_named_create_eq_valid_named_create2 /=.
    split_and!; done. }
  iIntros (created err) "[Hsuccess|Herror]".
  - iDestruct "Hsuccess" as
      (i' kobj' uid) "(%Hcreated & %Herr & Hpost)".
    subst created err.
    iDestruct "Hpost" as
      "(%Hvalid' & %Hsame_kind & %Hmeta_created & %Hspec_created &
        %Hstatus_created & %Hkey_eq' & %Hkey_fresh & %Huid_eq &
        Hdeepown_i & Hown_meta_frag & Hown_spec_frag &
        Hown_status_frag & Hown_reserved_frag & Hown_children_frag &
        Hown_grandchildren_frag)".
    destruct kobj' as [pod'|rs'|pvc'|sts']; try done.
    iDestruct "Hdeepown_i" as (pod_l') "[%Hi' Hdeepown_l]".
    wp_auto.
    unfold KObjectV.valid_interface in Hi'. rewrite Hi'.
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

End proof.
