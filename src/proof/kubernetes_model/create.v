From New.proof Require Import prelude empty_ffi.
From New.proof.kubernetes_model Require Export common_create.

Section proof.
Context `{hG: !heapGS Σ} `{!ffi_semantics _ _}.
Context {sem : go.Semantics} {package_sem : apimodel.Assumptions}.
Context `{!kubernetesModelG Σ}.
Context `{!KObjectV.ObjectInterfaceAssumptions}.
Local Set Default Proof Using "All".

Lemma wp_State__create_nameless_au γ l kind namespace i kobj parent_key parent_uid :
  ∀ Φ,
  ( is_pkg_init apimodel ∗
    is_kubernetes γ l ∗
    "%Hvalid" ∷ ⌜ KObjectV.valid_create kind namespace kobj ⌝ ∗
    "%Hname_empty" ∷ ⌜ (KObjectV.objectmeta kobj).(ObjectMetaV.Name') = ""%go ⌝ ∗
    "%Hextra_valid" ∷ ⌜ KObjectV.extra_valid kobj ⌝ ∗
    "%Hns_eq" ∷ ⌜ namespace = parent_key.(KKey.Namespace') ⌝ ∗
    "%Hpr" ∷ ⌜ obj_parent_ref_is kobj parent_key.(KKey.Kind') parent_key.(KKey.Name') parent_uid ⌝ ∗
    "Hdeepown_i" ∷ KObjectV.deepown_i i kobj 1 ∗
    |={⊤,∅}=> ∃ children,
      "Hown_children_frag" ∷ own_children_frag γ parent_key parent_uid 1 children ∗
      "Hclose" ∷ ( ∀ i' kobj' key uid,
        ⌜ KObjectV.valid kobj' ⌝ ∗
        ⌜ KObjectV.created namespace kobj kobj' ⌝ ∗
        ⌜ key = (KObjectV.key kobj') ⌝ ∗
        ⌜ key ∉ children ⌝ ∗
        ⌜ uid = (KObjectV.objectmeta kobj').(ObjectMetaV.UID') ⌝ ∗
        KObjectV.deepown_i i' kobj' 1 ∗
        own_meta_frag γ key uid 1 (KObjectV.objectmeta kobj') ∗
        own_spec_frag γ key uid 1 (KObjectV.spec kobj') ∗
        own_status_frag γ key uid 1 (KObjectV.status kobj') ∗
        own_unreserved_key_frag γ key ∗
        own_children_frag γ parent_key parent_uid 1 (children ∪ {[key]}) ∗
        own_children_frag γ key uid 1 ∅
          ={∅,⊤}=∗ ▷ Φ (#(interface.ok i'), #interface.nil)%V
      )
  ) -∗ WP l @! (go.PointerType apimodel.State) @! "create" #kind #namespace #(interface.ok i) {{ Φ }}.
Proof.
  iIntros (Φ) "(#Hpkg & #Hkinv & Hau)". iNamed "Hau". iNamed "Hkinv".
  assert (kind = KObjectV.kind kobj ∧ namespace ≠ ""%go ∧ valid_namespace namespace ∧
      ObjectMetaV.valid_create (KObjectV.kind kobj) namespace (KObjectV.objectmeta kobj)) as
    (Hkind_matches & Hns_nonempty & Hns_valid & Hvalid_meta_create).
  { destruct kobj; rewrite /KObjectV.valid_create /= in Hvalid;
      rewrite ?/PodV.valid_create ?/ReplicaSetV.valid_create
        ?/PersistentVolumeClaimV.valid_create ?/StatefulSetV.valid_create in Hvalid;
      tauto. }
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
    rewrite /ObjectMetaV.valid_create Hname_empty in Hvalid_meta_create.
    destruct Hvalid_meta_create as (_ & Hns & _).
    destruct Hns as [Hns|(_ & Hns)]; rewrite Hns; auto.
  }
  iIntros "Hdeepown_m_l". wp_auto.
  wp_apply v1.wp_Now. iIntros (now_time now_timev) "Hdeepown_time". wp_auto.
  wp_apply (wp_SetCreationTimestamp_deepown_kobject i1 l1 kobj _ now_time now_timev with
    "[$Hdeepown_m_l $Hdeepown_time]"). 1: done.
  iIntros "Hdeepown_m_l". wp_auto.
  wp_apply (wp_State__generateNewUIDAndUpdate with "[$Hinv_Hstate_used_uid_addr $Hinv_Hown_used_uid]").
  iIntros (generated_uid) "(%Hgenerated_uid_is_not_used & %Hgenerated_uid_valid & Hinv_Hstate_used_uid_addr & Hinv_Hown_used_uid)". wp_auto.
  wp_apply (wp_SetUID_deepown_kobject i1 l1 kobj with "[$Hdeepown_m_l]"). 1: done.
  iIntros "Hdeepown_m_l". wp_auto.
  wp_apply (wp_GetName_deepown_kobject i1 l1 kobj with "[$Hdeepown_m_l]"). 1: done.
  iIntros "Hdeepown_m_l". wp_auto.
  wp_apply (wp_GetGenerateName_deepown_kobject i1 l1 kobj with "[$Hdeepown_m_l]"). 1: done.
  iIntros "Hdeepown_m_l". wp_auto.
  rewrite Hname_empty.
  rewrite bool_decide_true //. wp_auto.
  assert ((KObjectV.objectmeta kobj).(ObjectMetaV.GenerateName') ≠ ""%go) as Hgn_nonempty.
  { rewrite /ObjectMetaV.valid_create Hname_empty in Hvalid_meta_create.
    destruct Hvalid_meta_create as ((Hgn & _) & _).
    by apply valid_generate_name_nonempty in Hgn.
  }
  rewrite bool_decide_false //. wp_auto.
  wp_apply (wp_State__generateNewName with "[$Hinv_Hstate_m_addr $Hinv_Hown_phys]").
  { rewrite /ObjectMetaV.valid_create Hname_empty in Hvalid_meta_create.
    destruct Hvalid_meta_create as ((Hgn & Hlen) & _).
    rewrite Hkind_matches. done. }
  iIntros (new_name) "(%Hnn_nonempty & %Hnn_valid & %Hnn_fresh & %Hnn_not_reservedP & Hinv_Hstate_m_addr & Hinv_Hown_phys)". wp_auto.
  wp_apply (wp_SetName_deepown_kobject i1 l1 kobj with "[$Hdeepown_m_l]"). 1: done.
  iIntros "Hdeepown_m_l". wp_auto.
  iPoseProof (KObjectV.deepown_l_merge _ _ _ _ Hl1_not_null with "[$Hdeepown_t_l $Hdeepown_m_l $Hdeepown_s_l $Hdeepown_st_l]") as "Hdeepown_l".
  wp_apply (wp_applyValidationAndDefaulting_ok _ _ _ kind namespace new_name kobj
    with "[Hdeepown_l]").
  { iFrame "#". iFrame. iPureIntro. split_and!.
    - destruct kobj; done.
    - exact Hvalid.
    - rewrite /create_prepared_for_helper /= Hname_empty.
      rewrite Hkind_matches in Hnn_valid.
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
  wp_apply (wp_map_lookup2 apimodel.KKey (go.InterfaceType []) with "[$Hinv_Hown_phys]").
  iIntros "Hinv_Hown_phys". wp_auto.
  rewrite /is_Some Hnn_fresh. wp_auto.
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
      ((KObjectV.objectmeta kobj1) <| ObjectMetaV.ResourceVersion' := generated_rv |>)) 1)
    with "[Hdeepown_l]" as "Hdeepown_i1".
  { iExists l1. iSplit.
    { iPureIntro. destruct kobj, kobj1. all: done. }
    iFrame.
  }
  wp_apply (wp_deepCopy with "[$Hpkg $Hdeepown_i1]").
  iIntros (i2) "[Hdeepown_i2 Hdeepown_i1]". wp_auto.
  set key := {|
    KKey.Kind' := kind;
    KKey.Name' := new_name;
    KKey.Namespace' := namespace
  |}.
  set kobj2 := (KObjectV.update_objectmeta kobj1
    (KObjectV.objectmeta kobj1 <| ObjectMetaV.ResourceVersion' :=
      generated_rv |>)).
  iApply fupd_wp.
  iMod "Hau" as (children) "H". iNamed "H".
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
  assert (KObjectV.kind kobj2 = kind) as Hkind2.
  { destruct kobj, kobj2; simpl in *; subst; done. }
  assert ((KObjectV.objectmeta kobj2).(ObjectMetaV.Name') = new_name) as Hname2.
  { subst kobj2. rewrite objectmeta_update_objectmeta Hname1. destruct kobj; done. }
  assert ((KObjectV.objectmeta kobj2).(ObjectMetaV.Namespace') = namespace ∧
      (KObjectV.objectmeta kobj2).(ObjectMetaV.OwnerReferences') =
        (KObjectV.objectmeta kobj).(ObjectMetaV.OwnerReferences') ∧
      (KObjectV.objectmeta kobj2).(ObjectMetaV.DeletionTimestamp') = None)
    as (Hnamespace2 & Howner_references2 & Hdeletion_timestamp2).
  { destruct kobj, kobj2; rewrite /KObjectV.created /= in Hcreated2; try contradiction;
      rewrite ?/PodV.created ?/ReplicaSetV.created ?/PersistentVolumeClaimV.created
        ?/StatefulSetV.created /ObjectMetaV.created in Hcreated2;
      simpl; tauto. }
  assert (KObjectV.extra_valid kobj2) as Hextra_valid2.
  { rewrite /KObjectV.extra_valid.
    eapply ObjectSpecV.extra_valid_created.
    - exact Hextra_valid.
    - destruct kobj, kobj2; simpl in Hcreated2 |- *; try done;
        destruct Hcreated2 as (_ & _ & _ & Hspec_created & _); exact Hspec_created. }
  iAssert (⌜ dom phys_state = dom abs_state ⌝%I) as "%Hdom_eq".
  { iDestruct (big_sepM2_dom with "Hinv_Hphys_abs_rep") as %Hdom_eq. iPureIntro. done. }
  assert (¬ reserved_key_pred key) as Hkey_not_reserved.
  { subst key. apply Hnn_not_reservedP. }
  iPoseProof (kview.own_auth_valid_forall with "[$Hinv_Hown_abs]")
    as "%Habs_state_valid".
  assert (generated_uid ∉ used_uid) as Hgenerated_uid_fresh.
  { rewrite Hinv_Hused_uid_eq_dom_phys_used_uid.
    apply not_elem_of_dom. done. }
  assert ((KObjectV.objectmeta kobj2).(ObjectMetaV.UID') = generated_uid)
    as Hkobj2_uid.
  { subst kobj2. rewrite objectmeta_update_objectmeta Huid1.
    destruct kobj; done. }
  iMod (kview.create_kobj_vs key generated_uid kobj2 with "[$Hinv_Hown_abs]")
    as "(Hinv_Hown_abs & Hown_meta & Hown_spec & Hown_status & #Hown_unreserved_key_frag)".
  { fold key in Hnn_fresh.
    apply not_elem_of_dom.
    apply not_elem_of_dom in Hnn_fresh.
    rewrite -Hdom_eq.
    exact Hnn_fresh.
  }
  { exact Hkey_not_reserved. }
  { exact Hgenerated_uid_fresh. }
  { unfold kview.valid_k_uid_obj.
    subst key.
    split_and!.
    - rewrite /KObjectV.key Hkind2 Hname2 Hnamespace2. done.
    - symmetry. exact Hkobj2_uid.
    - exact Hvalid2.
    - exact Hextra_valid2.
  }
  { exact Hdeletion_timestamp2. }
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
  iMod (cview.create_child_vs2 (pk := parent_key) (puid := parent_uid)
    key generated_uid kobj2
    with "[$Hinv_Hown_children] [$Hown_children_frag]")
    as "(Hinv_Hown_children & Hown_children_frag & Hown_grandchildren)".
  { symmetry. exact Hkobj2_uid. }
  { apply not_elem_of_dom.
    apply not_elem_of_dom in Hnn_fresh.
    rewrite Hdom_eq in Hnn_fresh.
    done.
  }
  { rewrite /living_obj_parent_ref Hdeletion_timestamp2 /=
      /obj_parent_ref /meta_parent_ref Howner_references2.
    unfold obj_parent_ref_is, meta_parent_ref_is, meta_parent_ref in Hpr.
    destruct ((KObjectV.objectmeta kobj).(ObjectMetaV.OwnerReferences')) as [orefs|] eqn:Horefs;
      simpl in Hpr |- *; [|done].
    destruct (list_find (λ oref, oref.(OwnerReferenceV.Controller') = Some true) orefs)
      as [[idx oref]|] eqn:Hfind; simpl in Hpr |- *; [|done].
    injection Hpr as Hkey_eq Huid_eq.
    destruct parent_key as [pk_kind pk_name pk_namespace].
    simpl in Hkey_eq, Hns_eq. inversion Hkey_eq; subst.
    rewrite Huid_eq. done.
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
  { apply not_elem_of_dom in Hnn_fresh.
    rewrite Hdom_eq in Hnn_fresh.
    apply not_elem_of_dom in Hnn_fresh. exact Hnn_fresh. }
  { unfold terminating_children.terminating_obj_parent_ref.
    rewrite Hdeletion_timestamp2. done. }
  iMod ("Hclose" $! i2 kobj2 with
    "[$Hdeepown_i2 $Hown_meta $Hown_spec $Hown_status
      $Hown_unreserved_key_frag $Hown_children_frag $Hown_grandchildren]") as "HΦ".
  { iSplit.
    { iPureIntro. exact Hvalid2. }
    iPureIntro. split_and!.
    - exact Hcreated2.
    - subst key. rewrite /KObjectV.key Hkind2 Hname2 Hnamespace2. done.
    - apply not_elem_of_dom in Hnn_fresh.
      rewrite Hdom_eq in Hnn_fresh.
      intro Hin.
      apply Hnn_fresh.
      apply elem_of_dom.
      rewrite Hchildren_eq_dom in Hin.
      apply elem_of_dom in Hin as [obj Hlookup].
      apply map_lookup_filter_Some in Hlookup as [Hlookup _].
      eexists. done.
    - symmetry. exact Hkobj2_uid. }
  assert (Hkey_not_in_abs : abs_state !! key = None).
  { apply not_elem_of_dom.
    apply not_elem_of_dom in Hnn_fresh.
    rewrite Hdom_eq in Hnn_fresh.
    done.
  }
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
  { pose proof Hnn_fresh as Hkey_not_in_phys.
    rewrite (big_sepM2_insert _ phys_state abs_state key (interface.ok i1) kobj2 Hkey_not_in_phys Hkey_not_in_abs).
    iSplitL "Hdeepown_i1".
    - iExact "Hdeepown_i1".
    - iExact "Hinv_Hphys_abs_rep".
  }
  iCombineNamed "Hinv_*" as "H".
  wp_apply (wp_Mutex__Unlock _ (kubernetes_inv γ l) with "[$Hown_Mutex H]").
  { iNamed "H". iFrame. iFrame "#".
    iNext. iFrame. iPureIntro. split_and!.
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

Lemma wp_State__create_nameless γ l kind namespace i kobj parent_key parent_uid children :
  {{{ is_pkg_init apimodel ∗
      "#Hisk" ∷ is_kubernetes γ l ∗
      "%Hvalid" ∷ ⌜ KObjectV.valid_create kind namespace kobj ⌝ ∗
      "%Hname_empty" ∷ ⌜ (KObjectV.objectmeta kobj).(ObjectMetaV.Name') = ""%go ⌝ ∗
      "%Hextra_valid" ∷ ⌜ KObjectV.extra_valid kobj ⌝ ∗
      "%Hns_eq" ∷ ⌜ namespace = parent_key.(KKey.Namespace') ⌝ ∗
      "%Hpr" ∷ ⌜ obj_parent_ref_is kobj parent_key.(KKey.Kind') parent_key.(KKey.Name') parent_uid ⌝ ∗
      "Hdeepown" ∷ KObjectV.deepown_i i kobj 1 ∗
      "Hown_children_frag" ∷ own_children_frag γ parent_key parent_uid 1 children
  }}}
    l @! (go.PointerType apimodel.State) @! "create" #kind #namespace #(interface.ok i)
  {{{ i' kobj' key uid, RET (#(interface.ok i'), #interface.nil);
      "%Hvalid'" ∷ ⌜ KObjectV.valid kobj' ⌝ ∗
      "%Hcreated" ∷ ⌜ KObjectV.created namespace kobj kobj' ⌝ ∗
      "%Hkey_eq" ∷ ⌜ key = (KObjectV.key kobj') ⌝ ∗
      "%Hkey_fresh" ∷ ⌜ key ∉ children ⌝ ∗
      "%Huid_eq" ∷ ⌜ uid = (KObjectV.objectmeta kobj').(ObjectMetaV.UID') ⌝ ∗
      "Hdeepown_i" ∷ KObjectV.deepown_i i' kobj' 1 ∗
      "Hown_meta_frag" ∷ own_meta_frag γ key uid 1 (KObjectV.objectmeta kobj') ∗
      "Hown_spec_frag" ∷ own_spec_frag γ key uid 1 (KObjectV.spec kobj') ∗
      "Hown_status_frag" ∷ own_status_frag γ key uid 1 (KObjectV.status kobj') ∗
      "#Hown_unreserved_key_frag" ∷ own_unreserved_key_frag γ key ∗
      "Hown_children_frag" ∷ own_children_frag γ parent_key parent_uid 1 (children ∪ {[key]}) ∗
      "Hown_grandchildren_frag" ∷ own_children_frag γ key uid 1 ∅
  }}}.
Proof.
  iIntros (Φ) "(#Hinit & H) HΦ". iNamed "H".
  iApply wp_State__create_nameless_au.
  iFrame "#". iFrame "%". iFrame.
  iApply fupd_mask_intro; [ timeout 10 set_solver | iIntros "Hmask" ].
  iIntros (i' kobj' key uid) "Hpost".
  iMod "Hmask" as "_".
  iModIntro. iNext.
  iApply ("HΦ" $! i' kobj' key uid with "Hpost").
Qed.

Lemma wp_State__PodCreate_nameless γ l namespace pod_l pod parent_key parent_uid children :
  {{{ is_pkg_init apimodel ∗
      "#Hisk" ∷ is_kubernetes γ l ∗
      "%Hvalid" ∷ ⌜ PodV.valid_create PodV.kind namespace pod ⌝ ∗
      "%Hname_empty" ∷ ⌜ pod.(PodV.ObjectMeta').(ObjectMetaV.Name') = ""%go ⌝ ∗
      "%Hns_eq" ∷ ⌜ namespace = parent_key.(KKey.Namespace') ⌝ ∗
      "%Hpr" ∷ ⌜ obj_parent_ref_is (KObjectV.Pod pod) parent_key.(KKey.Kind') parent_key.(KKey.Name') parent_uid ⌝ ∗
      "Hdeepown_l" ∷ PodV.deepown_l pod_l pod 1 ∗
      "Hown_children_frag" ∷ own_children_frag γ parent_key parent_uid 1 children
  }}}
    l @! (go.PointerType apimodel.State) @! "PodCreate" #namespace #pod_l
  {{{ pod_l' pod' key uid, RET (#pod_l', #interface.nil);
      "%Hvalid'" ∷ ⌜ PodV.valid pod' ⌝ ∗
      "%Hcreated" ∷ ⌜ PodV.created namespace pod pod' ⌝ ∗
      "%Hkey_eq" ∷ ⌜ key = PodV.key pod' ⌝ ∗
      "%Hkey_fresh" ∷ ⌜ key ∉ children ⌝ ∗
      "%Huid_eq" ∷ ⌜ uid = pod'.(PodV.ObjectMeta').(ObjectMetaV.UID') ⌝ ∗
      "Hdeepown_l" ∷ PodV.deepown_l pod_l' pod' 1 ∗
      "Hown_meta_frag" ∷ own_meta_frag γ key uid 1 pod'.(PodV.ObjectMeta') ∗
      "Hown_spec_frag" ∷ own_spec_frag γ key uid 1 (ObjectSpecV.PodSpec pod'.(PodV.Spec')) ∗
      "Hown_status_frag" ∷ own_status_frag γ key uid 1 (ObjectStatusV.PodStatus pod'.(PodV.Status')) ∗
      "#Hown_unreserved_key_frag" ∷ own_unreserved_key_frag γ key ∗
      "Hown_children_frag" ∷ own_children_frag γ parent_key parent_uid 1 (children ∪ {[key]}) ∗
      "Hown_grandchildren_frag" ∷ own_children_frag γ key uid 1 ∅
  }}}.
Proof.
  iIntros (Φ) "(#Hinit & H) HΦ". iNamed "H".
  wp_method_call. rewrite /apimodel.State__PodCreateⁱᵐᵖˡ. wp_call. wp_auto.
  iAssert (KObjectV.deepown_i (interface.mk (go.PointerType v1.Pod) #pod_l) (KObjectV.Pod pod) 1)
    with "[Hdeepown_l]" as "Hdeepown_i".
  { iExists pod_l. iSplit; [iPureIntro; apply KObjectV.valid_interface_Pod|]. iFrame. }
  wp_apply (wp_State__create_nameless
    γ l "Pod"%go namespace (interface.mk (go.PointerType v1.Pod) #pod_l)
    (KObjectV.Pod pod) parent_key parent_uid children
    with "[$Hinit $Hisk $Hdeepown_i $Hown_children_frag]").
  { iPureIntro. split_and!; done. }
  iIntros (i' kobj' key uid) "Hpost". iNamed "Hpost".
  destruct kobj' as [pod'|rs'|pvc'|sts']; try done.
  iDestruct "Hdeepown_i" as (pod_l') "[%Hi' Hdeepown_l]". wp_auto.
  unfold KObjectV.valid_interface in Hi'. destruct Hi' as [Hi' _]. rewrite Hi'.
  change (go.PointerType api_core_v1.Pod) with (go.PointerType v1.Pod).
  cbn [interface.ty interface.v].
  replace (if decide (go.PointerType v1.Pod = go.PointerType v1.Pod)
           then #pod_l' else #null)%V with (#pod_l')%V by
    (rewrite decide_True; done).
  replace (bool_decide (go.PointerType v1.Pod = go.PointerType v1.Pod)) with true by
    (symmetry; apply bool_decide_eq_true_2; done).
  wp_auto.
  iApply "HΦ". iFrame. iFrame "#". iPureIntro. split_and!; done.
Qed.

End proof.
