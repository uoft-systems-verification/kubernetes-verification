From New.proof Require Import prelude empty_ffi.
From New.proof.kubernetes_model Require Export inv common.
From New.proof.k8s_io.apiserver.pkg.registry Require Export rest.

Section proof.
Context `{hG: !heapGS Σ} {go_ctx: GoContext}.
Context `{!kubernetesModelG Σ}.

Lemma wp_State__create_nameless_au γ l kind namespace i kobj parent_key parent_uid :
  ∀ Φ,
  ( is_pkg_init apimodel ∗
    is_kubernetes γ l ∗
    "%Hvalid" ∷ ⌜ KObjectV.valid_nameless_create kind namespace kobj ⌝ ∗
    "%Hns_nonempty" ∷ ⌜ namespace ≠ ""%go ⌝ ∗
    "%Hns_valid" ∷ ⌜ valid_namespace namespace ⌝ ∗
    "%Hns_eq" ∷ ⌜ namespace = parent_key.(KKey.Namespace') ⌝ ∗
    "%Hpr" ∷ ⌜ obj_parent_ref_is kobj parent_key.(KKey.Kind') parent_key.(KKey.Name') parent_uid ⌝ ∗
    "Hdeepown_i" ∷ KObjectV.deepown_i i kobj 1 ∗
    |={⊤,∅}=> ∃ children,
      "Hown_children_frag" ∷ own_children_frag γ parent_key parent_uid 1 children ∗
      "Hclose" ∷ ( ∀ i' kobj' key uid,
        ⌜ KObjectV.valid kobj' ⌝ ∗
        ⌜ KObjectV.same_kind kobj kobj' ⌝ ∗
        ⌜ ObjectMetaV.nameless_created namespace (KObjectV.objectmeta kobj) (KObjectV.objectmeta kobj') ⌝ ∗
        ⌜ ObjectSpecV.created (KObjectV.spec kobj) (KObjectV.spec kobj') ⌝ ∗
        ⌜ ObjectStatusV.created (KObjectV.status kobj) (KObjectV.status kobj') ⌝ ∗
        ⌜ key = (KObjectV.key kobj') ⌝ ∗
        ⌜ key ∉ children ⌝ ∗
        ⌜ uid = (KObjectV.objectmeta kobj').(ObjectMetaV.UID') ⌝ ∗
        KObjectV.deepown_i i' kobj' 1 ∗
        own_meta_frag γ key uid 1 (KObjectV.objectmeta kobj') ∗
        own_spec_frag γ key uid 1 (KObjectV.spec kobj') ∗
        own_status_frag γ key uid 1 (KObjectV.status kobj') ∗
        own_children_frag γ parent_key parent_uid 1 (children ∪ {[key]}) ∗
        own_children_frag γ key uid 1 ∅
          ={∅,⊤}=∗ ▷ Φ (#i', #interface.nil)%V
      )
  ) -∗ WP l @ (ptrT.id apimodel.State.id) @ "create" #kind #namespace #i {{ Φ }}.
Proof.
  iIntros (Φ) "(#? & #Hkinv & Hau)". iNamed "Hau". iNamed "Hkinv".
  wp_method_call. wp_call.
  wp_apply wp_with_defer. iIntros (defer) "Hdefer". simpl subst. wp_auto.
  wp_apply wp_Mutex__Lock; [done|]. iIntros "[Hown_Mutex H]". iNamedPrefix "H" "Hinv_". wp_auto.
  wp_apply (wp_deepCopy with "[$Hdeepown_i]"). iIntros (i1) "[Hdeepown_i1 Hdeepown_i]". wp_auto.
  iDestruct "Hdeepown_i1" as (l1) "[%Hvalid_interface Hdeepown_l]".
  wp_apply wp_Accessor. 1: iPureIntro; done.
  rewrite bool_decide_true //. wp_auto.
  iPoseProof (KObjectV.deepown_l_split with "Hdeepown_l") as
    "(Hdeepown_t_l & Hdeepown_m_l & Hdeepown_s_l & Hdeepown_st_l)".
  wp_apply (wp_WipeObjectMetaSystemFields with "[$Hdeepown_m_l]"). 1: done.
  iIntros (time) "Hdeepown_m_l". wp_auto.
  wp_apply (wp_EnsureObjectNamespaceMatchesRequestNamespace with "[$Hdeepown_m_l]").
  { iPureIntro.
    destruct Hvalid as (_ & _ & Hmeta & _).
    destruct Hmeta as (_ & _ & _ & Hns & _).
    destruct Hns as [Hns|(_ & Hns)]; rewrite Hns; auto.
  }
  iIntros "Hdeepown_m_l". wp_auto.
  rewrite bool_decide_true //. wp_auto.
  wp_apply v1.wp_Now. iIntros (now_time now_timev) "Hdeepown_time". wp_auto.
  wp_apply (wp_SetCreationTimestamp_deepown with "[$Hdeepown_m_l $Hdeepown_time]"). iIntros "Hdeepown_m_l". wp_auto.
  wp_apply (wp_State__generateNewUIDAndUpdate with "[$Hinv_Hstate_used_uid_addr $Hinv_Hown_used_uid]").
  iIntros (generated_uid) "(%Hgenerated_uid_is_not_used & %Hgenerated_uid_valid & Hinv_Hstate_used_uid_addr & Hinv_Hown_used_uid)". wp_auto.
  wp_apply (wp_SetUID_deepown with "[$Hdeepown_m_l]"). iIntros "Hdeepown_m_l". wp_auto.
  wp_apply (wp_GetName_deepown with "[$Hdeepown_m_l]"). iIntros "Hdeepown_m_l". wp_auto.
  wp_apply (wp_GetGenerateName_deepown with "[$Hdeepown_m_l]"). iIntros "Hdeepown_m_l". wp_auto.
  assert ((KObjectV.objectmeta kobj).(ObjectMetaV.Name') = ""%go) as ->.
  { destruct Hvalid as (_ & _ & Hmeta & _). destruct Hmeta as (_ & _ & Hn & _ & _). done. }
  rewrite bool_decide_true //. wp_auto.
  assert ((KObjectV.objectmeta kobj).(ObjectMetaV.GenerateName') ≠ ""%go) as Hgn_nonempty.
  { destruct Hvalid as (_ & _ & Hmeta & _).
    destruct Hmeta as (Hgn & _ & _ & _ & _).
    destruct Hgn as (prefix & -> & Hprefix_nonempty & _).
    intro Hcontra. apply app_eq_nil in Hcontra as [Hprefix _]. done.
  }
  rewrite bool_decide_false //. wp_auto.
  wp_apply (wp_State__generateNewName with "[$Hinv_Hstate_m_addr $Hinv_Hown_phys]").
  { destruct Hvalid as (_ & _ & Hmeta & _).
    destruct Hmeta as (Hgn1 & Hgn2 & _ & _ & _). done. }
  iIntros (new_name) "(%Hnn_nonempty & %Hnn_valid & %Hnn_fresh & Hinv_Hstate_m_addr & Hinv_Hown_phys)". wp_auto.
  wp_apply (wp_SetName_deepown with "[$Hdeepown_m_l]"). iIntros "Hdeepown_m_l". wp_auto.
  iPoseProof (KObjectV.deepown_l_merge with "[$Hdeepown_t_l $Hdeepown_m_l $Hdeepown_s_l $Hdeepown_st_l]") as "Hdeepown_l".
  wp_apply (wp_applyValidationAndDefaulting with "[Hdeepown_l]").
  { iFrame.
    iPureIntro.
    destruct Hvalid as (_ & _ & Hmeta & _).
    destruct Hmeta as (Hgn_valid & _ & _ & _ & Hlabels & Hannotations & Howner_refs & Hfinalizers & Hmanaged_fields).
    split_and!. all: destruct kobj; done.
  }
  iIntros (kobj1) "(Hdeepown_l & %Hsame_kind & %Hvalid_meta & %Hvalid_spec & %Hvalid_status & %Htypemeta_eq & %Hm_eq &
    %Hcreated_spec & %Hcreated_status)". wp_auto.
  rewrite bool_decide_true //. wp_auto.
  iPoseProof (KObjectV.deepown_l_split with "Hdeepown_l") as
    "(Hdeepown_t_l & Hdeepown_m_l & Hdeepown_s_l & Hdeepown_st_l)".
  assert (KObjectV.objectmeta_ptr l1 kobj = KObjectV.objectmeta_ptr l1 kobj1) as ->.
  { destruct kobj, kobj1; done. }
  wp_apply (wp_validateObjectMeta with "[$Hdeepown_m_l]"). 1: done.
  iIntros "Hdeepown_m_l". wp_auto.
  rewrite bool_decide_true //. wp_auto.
  wp_apply (wp_map_get with "[$Hinv_Hown_phys]"). iIntros "Hinv_Hown_phys". wp_auto.
  rewrite /is_Some Hnn_fresh. wp_auto.
  wp_apply (wp_State__generateNewRVAndUpdate with "[$Hinv_Hstate_used_rv_addr $Hinv_Hown_used_rv]").
  iIntros (generated_rv) "(%Hgenerated_rv_is_not_used & %Hgenerated_rv_valid & Hinv_Hstate_used_rv_addr & Hinv_Hown_used_rv)".
  wp_auto.
  wp_apply (wp_SetResourceVersion_deepown with "[$Hdeepown_m_l]"). iIntros "Hdeepown_m_l". wp_auto.
  wp_apply (wp_map_insert with "[$Hinv_Hown_phys]"). iIntros "Hinv_Hown_phys". wp_auto.
  iPoseProof (KObjectV.deepown_l_merge with "[$Hdeepown_t_l $Hdeepown_m_l $Hdeepown_s_l $Hdeepown_st_l]") as "Hdeepown_l".
  iAssert (KObjectV.deepown_i i1
    (KObjectV.update_objectmeta kobj1
      ((KObjectV.objectmeta kobj1) <| ObjectMetaV.ResourceVersion' := generated_rv |>)) 1)
    with "[Hdeepown_l]" as "Hdeepown_i1".
  { iExists l1. iSplit.
    { iPureIntro. destruct kobj, kobj1. all: done. }
    iFrame.
  }
  wp_apply (wp_deepCopy with "[$Hdeepown_i1]").
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
  assert (KObjectV.valid kobj2) as Hvalid2.
  { subst kobj2.
    destruct Hvalid as (Hkind_eq & Hvalid_typemeta & _ & _ & _).
    destruct kobj; destruct kobj1; try done.
    all: (
      lazymatch goal with
      | Hvalid_typemeta : KObjectV.valid_typemeta ?kind ?tm_old,
        Htypemeta_eq : ?tm_new = ?tm_old |- _ =>
          assert (KObjectV.valid_typemeta kind tm_new) as Hvalid_typemeta1
            by (rewrite Htypemeta_eq; done)
      end;
      solve_update_objectmeta_valid
        Hvalid_typemeta1 Hgenerated_rv_valid Hvalid_meta Hvalid_spec Hvalid_status
    ).
  }
  iAssert (⌜ dom phys_state = dom abs_state ⌝%I) as "%Hdom_eq".
  { iDestruct (big_sepM2_dom with "Hinv_Hphys_abs_rep") as %Hdom_eq. iPureIntro. done. }
  iPoseProof (kview.own_auth_valid_forall with "[$Hinv_Hown_abs]") as "%Habs_state_valid".
  iMod (kview.create_kobj_vs key generated_uid kobj2 with "[$Hinv_Hown_abs]")
    as "(Hinv_Hown_abs & Hown_meta & Hown_spec & Hown_status)".
  { fold key in Hnn_fresh. apply not_elem_of_dom. apply not_elem_of_dom in Hnn_fresh. set_solver.
  }
  { rewrite Hinv_Hused_uid_eq_dom_phys_used_uid. apply not_elem_of_dom. done.
  }
  { unfold kview.valid_k_uid_obj.
    subst kobj2 key.
    split_and!.
    - destruct Hvalid as (Hkind_eq & _).
      destruct kobj; destruct kobj1; try done;
      rewrite Hm_eq; simpl; rewrite Hkind_eq; done.
    - destruct kobj; destruct kobj1; try done;
      rewrite Hm_eq; done.
    - done.
  }
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
    set_solver.
  }
  iMod (cview.create_child_vs2 (pk := parent_key) (puid := parent_uid)
    key generated_uid kobj2
    with "[$Hinv_Hown_children] [$Hown_children_frag]")
    as "(Hinv_Hown_children & Hown_children_frag & Hown_grandchildren)".
  { subst kobj2.
    destruct kobj; destruct kobj1;
    try done; rewrite Hm_eq; done.
  }
  { apply not_elem_of_dom.
    apply not_elem_of_dom in Hnn_fresh.
    rewrite Hdom_eq in Hnn_fresh.
    done.
  }
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
      inversion Hpr; subst; unfold obj_parent_ref, meta_parent_ref; simpl;
      rewrite Hfind H0 H1; destruct parent_key; done.
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
  iMod ("Hclose" $! i2 kobj2 with "[$Hdeepown_i2 $Hown_meta $Hown_spec $Hown_status $Hown_children_frag $Hown_grandchildren]") as "HΦ".
  { iPureIntro. split_and!.
    - done.
    - subst kobj2.
      destruct kobj; destruct kobj1; done.
    - unfold ObjectMetaV.nameless_created.
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
    - subst key kobj2.
      destruct Hvalid as (Hkind_eq & _).
      destruct kobj; destruct kobj1;
      simpl in Hsame_kind, Hm_eq, Hkind_eq |- *;
      try done; rewrite Hm_eq; rewrite Hkind_eq; done.
    - apply not_elem_of_dom in Hnn_fresh.
      rewrite Hdom_eq in Hnn_fresh.
      intro Hin.
      apply Hnn_fresh.
      apply elem_of_dom.
      rewrite Hchildren_eq_dom in Hin.
      apply elem_of_dom in Hin as [obj Hlookup].
      apply map_lookup_filter_Some in Hlookup as [Hlookup _].
      eexists. done.
    - subst kobj2.
      destruct kobj; destruct kobj1;
      simpl in Hm_eq |- *;
      try done; rewrite Hm_eq; done. }
  iModIntro.
  iAssert (([∗ map] i; obj ∈ <[key:=i1]> phys_state; <[key:=kobj2]> abs_state, KObjectV.deepown_i i obj 1)%I)
    with "[Hdeepown_i1 Hinv_Hphys_abs_rep]" as "Hinv_Hphys_abs_rep".
  { pose proof Hnn_fresh as Hkey_not_in_phys.
    assert (Hkey_not_in_abs : abs_state !! key = None).
    { apply not_elem_of_dom.
      pose proof Hnn_fresh as Hkey_not_in_phys_dom.
      apply not_elem_of_dom in Hkey_not_in_phys_dom.
      rewrite Hdom_eq in Hkey_not_in_phys_dom.
      done.
    }
    rewrite (big_sepM2_insert _ phys_state abs_state key i1 kobj2 Hkey_not_in_phys Hkey_not_in_abs).
    iSplitL "Hdeepown_i1".
    - iExact "Hdeepown_i1".
    - iExact "Hinv_Hphys_abs_rep".
  }
  iCombineNamed "Hinv_*" as "H".
  wp_apply (wp_Mutex__Unlock _ (kubernetes_inv γ l) with "[$Hown_Mutex H]").
  { iNamed "H". iFrame. iFrame "#". iPureIntro. split_and!.
    - rewrite dom_insert_L.
      rewrite Hinv_Hused_uid_eq_dom_phys_used_uid.
      rewrite union_comm_L.
      done.
    - assert (Hobj_ref : obj_ref key kobj2 = (key, generated_uid)).
      { unfold obj_ref. subst kobj2.
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
    - assert (Hkey_not_in_abs : abs_state !! key = None).
      { apply not_elem_of_dom.
        apply not_elem_of_dom in Hnn_fresh.
        rewrite Hdom_eq in Hnn_fresh.
        done.
      }
      assert (Hobj_uid : generated_uid = (KObjectV.objectmeta kobj2).(ObjectMetaV.UID')).
      { subst kobj2.
        destruct kobj; destruct kobj1;
        simpl in Hm_eq |- *;
        try done; rewrite Hm_eq; done.
      }
      assert (Huid_fresh : generated_uid ∉ used_uid).
      { apply not_elem_of_dom in Hgenerated_uid_is_not_used.
        rewrite <- Hinv_Hused_uid_eq_dom_phys_used_uid in Hgenerated_uid_is_not_used.
        done.
      }
      rewrite (map_to_set_insert_L
        (λ _ obj, (KObjectV.objectmeta obj).(ObjectMetaV.UID'))
        abs_state key kobj2 Hkey_not_in_abs).
      rewrite Hinv_Htombed_uid_eq_used_uid_sub.
      rewrite Hobj_uid.
      apply set_eq. intros uid.
      rewrite !elem_of_difference !elem_of_union !elem_of_singleton.
      set_solver. }
  iApply "HΦ".
Qed.

Lemma wp_State__create_nameless γ l kind namespace i kobj parent_key parent_uid children :
  {{{ is_pkg_init apimodel ∗
      "#Hisk" ∷ is_kubernetes γ l ∗
      "%Hvalid" ∷ ⌜ KObjectV.valid_nameless_create kind namespace kobj ⌝ ∗
      "%Hns_nonempty" ∷ ⌜ namespace ≠ ""%go ⌝ ∗
      "%Hns_valid" ∷ ⌜ valid_namespace namespace ⌝ ∗
      "%Hns_eq" ∷ ⌜ namespace = parent_key.(KKey.Namespace') ⌝ ∗
      "%Hpr" ∷ ⌜ obj_parent_ref_is kobj parent_key.(KKey.Kind') parent_key.(KKey.Name') parent_uid ⌝ ∗
      "Hdeepown" ∷ KObjectV.deepown_i i kobj 1 ∗
      "Hown_children_frag" ∷ own_children_frag γ parent_key parent_uid 1 children
  }}}
    l @ (ptrT.id apimodel.State.id) @ "create" #kind #namespace #i
  {{{ i' kobj' key uid, RET (#i', #interface.nil);
      "%Hvalid'" ∷ ⌜ KObjectV.valid kobj' ⌝ ∗
      "%Hsame_kind" ∷ ⌜ KObjectV.same_kind kobj kobj' ⌝ ∗
      "%Hmeta_created" ∷ ⌜ ObjectMetaV.nameless_created namespace (KObjectV.objectmeta kobj) (KObjectV.objectmeta kobj') ⌝ ∗
      "%Hspec_created" ∷ ⌜ ObjectSpecV.created (KObjectV.spec kobj) (KObjectV.spec kobj') ⌝ ∗
      "%Hstatus_created" ∷ ⌜ ObjectStatusV.created (KObjectV.status kobj) (KObjectV.status kobj') ⌝ ∗
      "%Hkey_eq" ∷ ⌜ key = (KObjectV.key kobj') ⌝ ∗
      "%Hkey_fresh" ∷ ⌜ key ∉ children ⌝ ∗
      "%Huid_eq" ∷ ⌜ uid = (KObjectV.objectmeta kobj').(ObjectMetaV.UID') ⌝ ∗
      "Hdeepown_i" ∷ KObjectV.deepown_i i' kobj' 1 ∗
      "Hown_meta" ∷ own_meta_frag γ key uid 1 (KObjectV.objectmeta kobj') ∗
      "Hown_spec" ∷ own_spec_frag γ key uid 1 (KObjectV.spec kobj') ∗
      "Hown_status" ∷ own_status_frag γ key uid 1 (KObjectV.status kobj') ∗
      "Hown_children" ∷ own_children_frag γ parent_key parent_uid 1 (children ∪ {[key]}) ∗
      "Hown_grandchildren" ∷ own_children_frag γ key uid 1 ∅
  }}}.
Proof.
  iIntros (Φ) "(#Hinit & H) HΦ". iNamed "H".
  iApply wp_State__create_nameless_au.
  iFrame "#". iFrame "%". iFrame.
  iApply fupd_mask_intro; [ set_solver | iIntros "Hmask" ].
  iIntros (i' kobj' key uid) "Hpost".
  iMod "Hmask" as "_".
  iModIntro. iNext.
  iApply ("HΦ" $! i' kobj' key uid with "Hpost").
Qed.

Lemma wp_State__PodCreate_nameless γ l namespace pod_l pod parent_key parent_uid children :
  {{{ is_pkg_init apimodel ∗
      "#Hisk" ∷ is_kubernetes γ l ∗
      "%Hvalid" ∷ ⌜ KObjectV.valid_nameless_create "Pod"%go namespace (KObjectV.Pod pod) ⌝ ∗
      "%Hns_nonempty" ∷ ⌜ namespace ≠ ""%go ⌝ ∗
      "%Hns_valid" ∷ ⌜ valid_namespace namespace ⌝ ∗
      "%Hns_eq" ∷ ⌜ namespace = parent_key.(KKey.Namespace') ⌝ ∗
      "%Hpr" ∷ ⌜ obj_parent_ref_is (KObjectV.Pod pod) parent_key.(KKey.Kind') parent_key.(KKey.Name') parent_uid ⌝ ∗
      "Hdeepown_l" ∷ PodV.deepown_l pod_l pod 1 ∗
      "Hown_children_frag" ∷ own_children_frag γ parent_key parent_uid 1 children
  }}}
    l @ (ptrT.id apimodel.State.id) @ "PodCreate" #namespace #pod_l
  {{{ pod_l' pod' key uid, RET (#pod_l', #interface.nil);
      "%Hvalid'" ∷ ⌜ KObjectV.valid (KObjectV.Pod pod') ⌝ ∗
      "%Hmeta_created" ∷ ⌜ ObjectMetaV.nameless_created namespace pod.(PodV.ObjectMeta') pod'.(PodV.ObjectMeta') ⌝ ∗
      "%Hspec_created" ∷ ⌜ ObjectSpecV.created (ObjectSpecV.PodSpec pod.(PodV.Spec')) (ObjectSpecV.PodSpec pod'.(PodV.Spec')) ⌝ ∗
      "%Hstatus_created" ∷ ⌜ ObjectStatusV.created (ObjectStatusV.PodStatus pod.(PodV.Status')) (ObjectStatusV.PodStatus pod'.(PodV.Status')) ⌝ ∗
      "%Hkey_eq" ∷ ⌜ key = PodV.key pod' ⌝ ∗
      "%Hkey_fresh" ∷ ⌜ key ∉ children ⌝ ∗
      "%Huid_eq" ∷ ⌜ uid = pod'.(PodV.ObjectMeta').(ObjectMetaV.UID') ⌝ ∗
      "Hdeepown_l" ∷ PodV.deepown_l pod_l' pod' 1 ∗
      "Hown_meta" ∷ own_meta_frag γ key uid 1 pod'.(PodV.ObjectMeta') ∗
      "Hown_spec" ∷ own_spec_frag γ key uid 1 (ObjectSpecV.PodSpec pod'.(PodV.Spec')) ∗
      "Hown_status" ∷ own_status_frag γ key uid 1 (ObjectStatusV.PodStatus pod'.(PodV.Status')) ∗
      "Hown_children" ∷ own_children_frag γ parent_key parent_uid 1 (children ∪ {[key]}) ∗
      "Hown_grandchildren" ∷ own_children_frag γ key uid 1 ∅
  }}}.
Proof.
  iIntros (Φ) "(#Hinit & H) HΦ". iNamed "H".
  wp_method_call. wp_call. wp_auto.
  iAssert (KObjectV.deepown_i (interface.mk (ptrT.id v1.Pod.id) #pod_l) (KObjectV.Pod pod) 1)
    with "[Hdeepown_l]" as "Hdeepown_i".
  { iExists pod_l. iSplit; [done|]. iFrame. }
  wp_apply (wp_State__create_nameless
    γ l "Pod"%go namespace (interface.mk (ptrT.id v1.Pod.id) #pod_l)
    (KObjectV.Pod pod) parent_key parent_uid children
    with "[$Hinit $Hisk $Hdeepown_i $Hown_children_frag]").
  { iPureIntro. split_and!; done. }
  iIntros (i' kobj' key uid) "Hpost". iNamed "Hpost".
  destruct kobj' as [pod'|]; [|done].
  iDestruct "Hdeepown_i" as (pod_l') "[%Hi' Hdeepown_l]". wp_auto.
  rewrite bool_decide_true //. wp_auto.
  unfold KObjectV.valid_interface in Hi'. rewrite Hi'.
  unshelve wp_apply wp_interface_checked_type_assert; try tc_solve.
  { iPureIntro. intros ptr_id. exists pod_l'. done. }
  iIntros (y ok) "%if_ok".
  assert (ok = true) as ->.
  { destruct ok; [done|]. intuition. }
  wp_auto.
  assert (pod_l' = y) as ->.
  { inversion if_ok. apply (inj to_val). done. }
  iApply "HΦ". iFrame. iPureIntro. split_and!; done.
Qed.

End proof.
