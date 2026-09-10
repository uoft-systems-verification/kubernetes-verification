From New.proof Require Import prelude empty_ffi.
From New.proof.kubernetes_model Require Export list_weak.
From New.proof.k8s_io.api.apps Require Import v1.

Section proof.
Context `{hG: !heapGS Σ} `{!ffi_semantics _ _}.
Context {sem : go.Semantics} {package_sem : apimodel.Assumptions}.
Context `{!kubernetesModelG Σ}.
Local Set Default Proof Using "All".

Definition replica_set_has_controller_uid (uid : go_string) (rs : ReplicaSetV.t) : Prop :=
  ∃ parent_key, obj_parent_ref (KObjectV.ReplicaSet rs) = Some (parent_key, uid).

Definition controllerUID_indexed_values (rs : ReplicaSetV.t) : list go_string :=
  match meta_parent_ref rs.(ReplicaSetV.ObjectMeta') with
  | Some (_, uid) => [uid]
  | None => []
  end.

Lemma wp_index_of_controllerUID i rs dq :
  {{{ is_pkg_init apimodel ∗
      "%Hvalid" ∷ ⌜ ReplicaSetV.valid rs ⌝ ∗
      "Hrs" ∷ KObjectV.deepown_i i (KObjectV.ReplicaSet rs) dq
  }}}
    @! apimodel.index_of #"controllerUID"%go #(interface.ok i)
  {{{ sl, RET (#sl, #interface.nil);
      sl ↦* controllerUID_indexed_values rs ∗
      KObjectV.deepown_i i (KObjectV.ReplicaSet rs) dq
  }}}.
Proof.
  wp_start as "H". iNamed "H".
  iAssert (is_pkg_init v1) as "#Hmeta_init".
  { iPkgInit. }
  iDestruct "Hrs" as (rs_l) "[%Hi Hrs]".
  pose proof Hi as Hrs_interface.
  unfold KObjectV.valid_interface in Hi.
  destruct Hi as [Hi Hobject]. subst i.
  wp_auto.
  rewrite decide_True;
    [change (go.PointerType api_apps_v1.ReplicaSet) with
      (go.PointerType v1.ReplicaSet); reflexivity|].
  wp_auto.
  rewrite bool_decide_true;
    [change (go.PointerType api_apps_v1.ReplicaSet) with
      (go.PointerType v1.ReplicaSet); reflexivity|].
  wp_auto.
  wp_bind (@! v1.GetControllerOf
    #(interface.mk_ok (go.PointerType api_apps_v1.ReplicaSet) #rs_l))%E.
  wp_apply (wp_GetControllerOf_kobject_exact
    (interface.mk_ok (go.PointerType api_apps_v1.ReplicaSet) #rs_l)
    (interface.mk (go.PointerType api_apps_v1.ReplicaSet) #rs_l)
    rs_l (KObjectV.ReplicaSet rs) dq with
    "[$Hmeta_init $Hrs //]").
  iIntros (controller_ref_l) "(Hrs & Hcontroller_ref)".
  iDestruct "Hcontroller_ref" as
    "[%Hcontroller_ref|Hcontroller_ref]".
  - destruct Hcontroller_ref as [Hcontroller_ref_null Hparent_none].
    subst controller_ref_l. wp_auto.
    iApply ("HΦ" $! slice.nil).
    iPoseProof (own_slice_nil (V:=go_string)) as "Hnil".
    unfold controllerUID_indexed_values. simpl in Hparent_none.
    rewrite Hparent_none. iFrame "Hnil".
    iExists rs_l. iFrame. done.
  - iDestruct "Hcontroller_ref" as (controller_ref)
      "(%Hcontroller_ref & Hcontroller_ref)".
    destruct Hcontroller_ref as
      [Hcontroller_ref_nonnull Hcontroller_ref_of].
    wp_auto.
    rewrite -> bool_decide_false by exact Hcontroller_ref_nonnull.
    wp_auto.
    iDestruct "Hcontroller_ref" as (controller_ref_c)
      "[Hcontroller_ref_l Hcontroller_ref]".
    iDestruct (struct_fields_split (V:=v1.OwnerReference.t)
      with "Hcontroller_ref_l") as
      "[Hcontroller_ref_fields %Hcontroller_ref_l_nonnull]".
    iNamedPrefix "Hcontroller_ref_fields" "Hcontroller_ref_field_".
    iNamedPrefix "Hcontroller_ref" "Hcontroller_ref_deepown_".
    wp_auto.
    rewrite Hcontroller_ref_deepown_Hdeepown_uid.
    wp_apply wp_slice_literal. iSplitR; first done.
    iIntros "%sl_ptr [Hsl _]". wp_auto.
    assert (meta_parent_ref rs.(ReplicaSetV.ObjectMeta') = Some ({|
      KKey.Kind' := controller_ref.(OwnerReferenceV.Kind');
      KKey.Namespace' := rs.(ReplicaSetV.ObjectMeta').(ObjectMetaV.Namespace');
      KKey.Name' := controller_ref.(OwnerReferenceV.Name')
    |}, controller_ref.(OwnerReferenceV.UID'))) as Hparent.
    { destruct Hcontroller_ref_of as
        (owner_references & Howner_references & Hcontroller_ref_in &
          Hcontroller_ref_controller).
      assert (valid_owner_references
        rs.(ReplicaSetV.ObjectMeta').(ObjectMetaV.OwnerReferences')) as
        Hvalid_owner_references.
      { unfold ReplicaSetV.valid, ObjectMetaV.valid in Hvalid. tauto. }
      rewrite Howner_references in Hvalid_owner_references.
      destruct Hvalid_owner_references as [Hcontroller_unique _].
      unfold meta_parent_ref. rewrite Howner_references.
      destruct (list_find
        (λ owner_reference : OwnerReferenceV.t,
          owner_reference.(OwnerReferenceV.Controller') = Some true)
        owner_references) as [[found_i found_ref]|] eqn:Hfind.
      - apply list_find_Some in Hfind as
          (Hfound_lookup & Hfound_controller & _).
        apply list_elem_of_lookup_1 in Hcontroller_ref_in as
          [controller_ref_i Hcontroller_ref_lookup].
        assert (controller_ref_i = found_i) as ->.
        { eapply Hcontroller_unique; eauto. }
        rewrite Hcontroller_ref_lookup in Hfound_lookup.
        injection Hfound_lookup as ->.
        reflexivity.
      - apply list_find_None in Hfind.
        rewrite Forall_forall in Hfind.
        exfalso. apply (Hfind controller_ref).
        + rewrite -list_elem_of_In. exact Hcontroller_ref_in.
        + exact Hcontroller_ref_controller. }
    iApply ("HΦ" $! (slice.mk sl_ptr (W64 1) (W64 1))).
    unfold controllerUID_indexed_values. rewrite Hparent.
    iFrame "Hsl". iExists rs_l. iFrame. done.
Qed.

(** Logically atomic, read-only specification for the ReplicaSet informer's
    controller-UID index. The result contains owned deep copies, just like
    other model list operations; every returned object has a controller owner
    reference whose UID equals [controller_uid]. *)
Lemma wp_State__ByIndex_controllerUID_au γ l controller_uid :
  ∀ Φ,
  ( is_pkg_init apimodel ∗
    is_kubernetes γ l ∗
    |={⊤,∅}=>
      "Hclose" ∷ (∀ sl interfaces replica_sets,
        "Hsl" ∷ sl ↦* (interface.ok <$> interfaces) ∗
        "Hreplica_sets" ∷ ([∗ list] i;rs ∈ interfaces;replica_sets, KObjectV.deepown_i i (KObjectV.ReplicaSet rs) 1) ∗
        "%Hvalid" ∷ ⌜ Forall ReplicaSetV.valid replica_sets ⌝ ∗
        "%Hextra_valid" ∷ ⌜ Forall ReplicaSetV.extra_valid replica_sets ⌝ ∗
        "%Hcontroller_uid" ∷ ⌜ Forall (replica_set_has_controller_uid controller_uid) replica_sets ⌝ ∗
        "%Hnodup" ∷ ⌜ NoDup (ReplicaSetV.key <$> replica_sets) ⌝
        ={∅,⊤}=∗ ▷ Φ (#sl, #interface.nil)%V)
  ) -∗
  WP l @! (go.PointerType apimodel.State) @! "ByIndex" #"ReplicaSet"%go #"controllerUID"%go #controller_uid {{ Φ }}.
Proof.
  iIntros (Φ) "(#Hpkg & #Hisk & Hau)". iNamed "Hisk".
  iAssert (is_pkg_init sync) as "#Hsync".
  { iPkgInit. }
  wp_method_call. rewrite /apimodel.State__ByIndexⁱᵐᵖˡ. wp_call.
  wp_apply wp_with_defer as "%defer Hdefer". simpl subst. wp_auto.
  wp_apply wp_Mutex__Lock; [iFrame "#"|].
  iIntros "[Hown_Mutex H]".
  iDestruct "H" as (phys_state_l phys_used_uid_l phys_used_rv_l phys_state
    phys_used_uid phys_used_rv abs_state used_uid used_reference) "H".
  iNamedPrefix "H" "Hinv_". wp_auto.
  wp_apply (wp_State__objListLocked γ l ReplicaSetV.kind ""%go
    phys_state_l phys_state abs_state used_uid with
    "[$Hpkg $Hinv_Hstate_m_addr $Hinv_Hown_phys $Hinv_Hown_abs
      $Hinv_Hphys_abs_rep]").
  iIntros (listed_sl interfaces objs)
    "(Hlisted_sl & Hobjs & %Hperm & %Hvalid & %Hextra_valid & %Hnodup &
      Hinv_Hstate_m_addr & Hinv_Hown_phys & Hinv_Hown_abs &
      Hinv_Hphys_abs_rep)".
  iPoseProof (kview.own_auth_valid_forall with "Hinv_Hown_abs")
    as "%Habs_valid".
  assert (Forall (λ obj, KObjectV.kind obj = ReplicaSetV.kind) objs)
    as Hkind.
  { eapply Permutation_Forall; [symmetry; exact Hperm|].
    apply Forall_forall. intros obj Hobj.
    rewrite <-list_elem_of_In in Hobj.
    apply list_elem_of_fmap_1 in Hobj as [[key obj'] [Hobj_eq Hkey]].
    simpl in Hobj_eq. subst obj'.
    apply elem_of_map_to_list in Hkey.
    apply map_lookup_filter_Some in Hkey as [Hlookup [Hkey_kind _]].
    pose proof (Habs_valid key obj Hlookup) as Hobj_valid.
    destruct Hobj_valid as [Hkey_eq _].
    rewrite Hkey_eq in Hkey_kind.
    destruct obj; exact Hkey_kind. }
  destruct (kobject_list_to_replica_sets objs Hkind) as
    [replica_sets ->].
  rewrite Forall_fmap in Hvalid.
  rewrite Forall_fmap in Hextra_valid.
  change (Forall ReplicaSetV.extra_valid replica_sets) in Hextra_valid.
  assert (KObjectV.key <$> (KObjectV.ReplicaSet <$> replica_sets) =
      ReplicaSetV.key <$> replica_sets) as Hkeys_eq.
  { rewrite -list_fmap_compose.
    apply list_fmap_ext. intros list_i rs Hlookup.
    unfold compose, KObjectV.key, ReplicaSetV.key, KObjectV.kind,
      ReplicaSetV.kind. done. }
  rewrite Hkeys_eq in Hnodup.
  iEval (rewrite big_sepL2_fmap_r) in "Hobjs".
  wp_auto.
  iPoseProof (own_slice_nil (V:=interface.t)) as "Hresult_nil".
  iPoseProof (own_slice_cap_nil (V:=interface.t)) as "Hresult_cap_nil".
  iDestruct (own_slice_len with "Hlisted_sl") as
    %(Hlisted_len & Hlisted_nonnegative).
  rewrite map_length in Hlisted_len.
  iDestruct (big_sepL2_length with "Hobjs") as %Hobjs_len.
  set I := (∃ (i : w64) (val : interface.t) (result_sl : slice.t)
      (result_interfaces : list interface.t_ok)
      (result_replica_sets : list ReplicaSetV.t),
    "Hi_ptr" ∷ i_ptr ↦ i ∗
    "Hval_ptr" ∷ val_ptr ↦ val ∗
    "Hitems_ptr" ∷ items_ptr ↦ result_sl ∗
    "Hresult_sl" ∷ result_sl ↦* (interface.ok <$> result_interfaces) ∗
    "Hresult_cap" ∷ own_slice_cap interface.t result_sl (DfracOwn 1) ∗
    "Hremaining" ∷ ([∗ list] interface_i;rs ∈
      drop (sint.nat i) interfaces;drop (sint.nat i) replica_sets,
      KObjectV.deepown_i interface_i (KObjectV.ReplicaSet rs) 1) ∗
    "Hresult_replica_sets" ∷ ([∗ list] interface_i;rs ∈
      result_interfaces;result_replica_sets,
      KObjectV.deepown_i interface_i (KObjectV.ReplicaSet rs) 1) ∗
    "%Hresult_valid" ∷ ⌜ Forall ReplicaSetV.valid result_replica_sets ⌝ ∗
    "%Hresult_extra_valid" ∷
      ⌜ Forall ReplicaSetV.extra_valid result_replica_sets ⌝ ∗
    "%Hresult_controller_uid" ∷
      ⌜ Forall (replica_set_has_controller_uid controller_uid)
        result_replica_sets ⌝ ∗
    "%Hresult_sublist" ∷
      ⌜ result_replica_sets `sublist_of` take (sint.nat i) replica_sets ⌝ ∗
    "%Hi_bounds" ∷ ⌜ 0 ≤ sint.Z i ≤ sint.Z (slice.len listed_sl) ⌝)%I.
  iAssert I with
    "[i val items Hresult_nil Hresult_cap_nil Hobjs]" as "Hloop".
  { iExists (W64 0), (zero_val interface.t), slice.nil, [], [].
    rewrite !drop_0 take_0 !big_sepL2_nil /=.
    iFrame "i val items Hobjs".
    iSplitL "Hresult_nil"; first iExact "Hresult_nil".
    iSplitL "Hresult_cap_nil"; first iExact "Hresult_cap_nil".
    iSplit; first done.
    iPureIntro. split_and!; try constructor; word. }
  wp_for "Hloop". wp_if_destruct.
  - assert (0 ≤ sint.Z i < sint.Z (slice.len listed_sl)) as Hibounds
      by word.
    list_elem interfaces (sint.Z i) as this_interface.
    assert (∃ this_rs, replica_sets !! sint.nat i = Some this_rs) as
      [this_rs Hthis_rs_lookup].
    { apply lookup_lt_is_Some_2. rewrite -Hobjs_len Hlisted_len. word. }
    assert ((interface.ok <$> interfaces) !! sint.nat i =
      Some (interface.ok this_interface)) as Hthis_value_lookup.
    { rewrite list_lookup_fmap Hthis_interface_lookup. done. }
    rewrite decide_True.
    { exact Hibounds. }
    wp_apply (wp_load_slice_index (V:=interface.t)
      (t:=go.InterfaceType []) listed_sl (sint.Z i)
      (interface.ok <$> interfaces) (DfracOwn 1)
      (interface.ok this_interface) with "[$Hlisted_sl]");
      [word|iPureIntro; exact Hthis_value_lookup|].
    iIntros "Hlisted_sl". wp_auto.
    assert (ReplicaSetV.valid this_rs) as Hthis_valid.
    { rewrite Forall_forall in Hvalid. apply Hvalid.
      rewrite <-list_elem_of_In. eapply list_elem_of_lookup_2.
      exact Hthis_rs_lookup. }
    assert (ReplicaSetV.extra_valid this_rs) as Hthis_extra_valid.
    { rewrite Forall_forall in Hextra_valid. apply Hextra_valid.
      rewrite <-list_elem_of_In. eapply list_elem_of_lookup_2.
      exact Hthis_rs_lookup. }
    iPoseProof (big_sepL2_head_tail _ _ _ this_interface this_rs with
      "Hremaining") as "[Hthis Hremaining]".
    { split; rewrite lookup_drop Nat.add_0_r; done. }
    wp_apply (wp_index_of_controllerUID this_interface this_rs 1 with
      "[$Hpkg $Hthis //]").
    iIntros (values_sl) "(Hvalues_sl & Hthis)".
    wp_auto.
    wp_alloc j_ptr as "Hj_ptr". wp_auto.
    iDestruct (own_slice_len with "Hvalues_sl") as
      %(Hvalues_len & Hvalues_nonnegative).
    set I0 := (∃ (j : w64) (v : go_string) (result_sl0 : slice.t),
      "Hj_ptr" ∷ j_ptr ↦ j ∗
      "Hv_ptr" ∷ v_ptr ↦ v ∗
      "Hitems_ptr" ∷ items_ptr ↦ result_sl0 ∗
      "Hresult_sl" ∷ result_sl0 ↦*
        (interface.ok <$> result_interfaces) ∗
      "Hresult_cap" ∷ own_slice_cap interface.t result_sl0 (DfracOwn 1) ∗
      "%Hj_bounds" ∷
        ⌜ 0 ≤ sint.Z j ≤ sint.Z (slice.len values_sl) ⌝)%I.
    iAssert I0 with
      "[Hj_ptr v Hitems_ptr Hresult_sl Hresult_cap]" as "Hinner".
    { iExists (W64 0), (zero_val go_string), result_sl.
      iFrame. iPureIntro. word. }
    wp_for "Hinner". wp_if_destruct.
    + assert (0 ≤ sint.Z j < sint.Z (slice.len values_sl)) as Hjbounds
        by word.
      list_elem (controllerUID_indexed_values this_rs) (sint.Z j) as
        this_uid.
      rewrite decide_True.
      { exact Hjbounds. }
      wp_apply (wp_load_slice_index (V:=go_string) (t:=go.string)
        values_sl (sint.Z j) (controllerUID_indexed_values this_rs)
        (DfracOwn 1) this_uid with
        "[$Hvalues_sl]"); [word|iPureIntro; exact Hthis_uid_lookup|].
      iIntros "Hvalues_sl". wp_auto.
      destruct (bool_decide (this_uid = controller_uid)) as [|]
        eqn:Huid_eq; wp_auto.
      * apply bool_decide_eq_true in Huid_eq. subst this_uid.
        assert (replica_set_has_controller_uid controller_uid this_rs)
          as Hthis_controller_uid.
        { apply list_elem_of_lookup_2 in Hthis_uid_lookup.
          unfold controllerUID_indexed_values in Hthis_uid_lookup.
          destruct (meta_parent_ref this_rs.(ReplicaSetV.ObjectMeta'))
            as [[parent_key parent_uid]|] eqn:Hparent; simpl in Hthis_uid_lookup.
          - apply list_elem_of_singleton in Hthis_uid_lookup.
            subst parent_uid. exists parent_key.
            unfold obj_parent_ref. simpl. exact Hparent.
          - rewrite elem_of_nil in Hthis_uid_lookup. contradiction. }
        wp_apply wp_slice_literal. iSplitR; first done.
        iIntros "%one_ptr [Hone _]". wp_auto.
        wp_apply (wp_slice_append with
          "[$Hresult_sl $Hresult_cap $Hone]").
        iIntros (result_sl')
          "(Hresult_sl & Hresult_cap & Hone)". wp_auto.
        wp_for_post.
        wp_for_post.
        iAssert I with
          "[Hi_ptr Hval_ptr Hitems_ptr Hresult_sl Hresult_cap
            Hremaining Hresult_replica_sets Hthis]" as "Hloop".
        { iExists (word.add i (W64 1)),
            (interface.ok this_interface), result_sl',
            (result_interfaces ++ [this_interface]),
            (result_replica_sets ++ [this_rs]).
          rewrite fmap_app /=.
          assert (sint.nat (word.add i (W64 1)) = S (sint.nat i))
            as -> by word.
          rewrite !drop_drop Nat.add_1_r.
          iFrame.
          iSplit; first done.
          iPureIntro. split_and!; try word.
          - apply Forall_app. split; [done|constructor; done].
          - apply Forall_app. split; [done|constructor; done].
          - apply Forall_app. split; [done|constructor; done].
          - rewrite (take_S_r _ _ this_rs Hthis_rs_lookup).
            apply sublist_app; [exact Hresult_sublist|].
            constructor; constructor. }
        iFrame.
      * wp_for_post.
        iAssert I0 with
          "[Hj_ptr Hv_ptr Hitems_ptr Hresult_sl Hresult_cap]" as
          "Hinner".
        { iExists (word.add j (W64 1)), this_uid, result_sl0.
          iFrame. iPureIntro. word. }
        iFrame.
    + wp_for_post.
      iAssert I with
        "[Hi_ptr Hval_ptr Hitems_ptr Hresult_sl Hresult_cap Hremaining
          Hresult_replica_sets]" as "Hloop".
      { iExists (word.add i (W64 1)),
          (interface.ok this_interface), result_sl0,
          result_interfaces, result_replica_sets.
        assert (sint.nat (word.add i (W64 1)) = S (sint.nat i))
          as -> by word.
        rewrite !drop_drop Nat.add_1_r.
        iFrame. iPureIntro. split_and!; try word; try done.
        rewrite (take_S_r _ _ this_rs Hthis_rs_lookup).
        apply sublist_inserts_r. exact Hresult_sublist. }
      iFrame.
  - clear I.
    assert (sint.nat i = length replica_sets) as Hi_len.
    { rewrite -Hobjs_len Hlisted_len. word. }
    assert (take (sint.nat i) replica_sets = replica_sets) as Htake.
    { rewrite Hi_len. apply take_ge. lia. }
    assert (NoDup (ReplicaSetV.key <$> result_replica_sets))
      as Hresult_nodup.
    { eapply sublist_NoDup; [exact Hnodup|].
      apply fmap_sublist. rewrite -Htake. exact Hresult_sublist. }
    iApply fupd_wp.
    iMod "Hau" as "Hclose".
    iMod ("Hclose" $! result_sl result_interfaces result_replica_sets
      with "[Hresult_sl Hresult_replica_sets]") as "HΦ".
    { iFrame. done. }
    iModIntro.
    iCombineNamed "Hinv_*" as "Hinv".
    wp_apply (wp_Mutex__Unlock _ (kubernetes_inv γ l)
      with "[$Hown_Mutex Hinv]").
    { iNamed "Hinv". iFrame. iFrame "#". done. }
    iApply "HΦ".
Qed.

(** Hoare-triple interface used by clients that do not need to choose an
    atomic linearization point. *)
Lemma wp_State__ByIndex_controllerUID γ l controller_uid :
  {{{ is_pkg_init apimodel ∗
      "#Hisk" ∷ is_kubernetes γ l
  }}}
    l @! (go.PointerType apimodel.State) @! "ByIndex" #"ReplicaSet"%go #"controllerUID"%go #controller_uid
  {{{ sl interfaces replica_sets, RET (#sl, #interface.nil);
      "Hsl" ∷ sl ↦* (interface.ok <$> interfaces) ∗
      "Hreplica_sets" ∷ ([∗ list] i;rs ∈ interfaces;replica_sets, KObjectV.deepown_i i (KObjectV.ReplicaSet rs) 1) ∗
      "%Hvalid" ∷ ⌜ Forall ReplicaSetV.valid replica_sets ⌝ ∗
      "%Hextra_valid" ∷ ⌜ Forall ReplicaSetV.extra_valid replica_sets ⌝ ∗
      "%Hcontroller_uid" ∷ ⌜ Forall (replica_set_has_controller_uid controller_uid) replica_sets ⌝ ∗
      "%Hnodup" ∷ ⌜ NoDup (ReplicaSetV.key <$> replica_sets) ⌝
  }}}.
Proof.
  iIntros (Φ) "(#Hpkg & #Hisk) HΦ".
  iApply wp_State__ByIndex_controllerUID_au.
  iFrame "#".
  iApply fupd_mask_intro.
  { Timeout 10 set_solver. }
  iIntros "Hmask".
  iIntros (sl interfaces replica_sets) "Hpost".
  iMod "Hmask" as "_".
  iModIntro. iNext.
  iApply ("HΦ" $! sl interfaces replica_sets with "Hpost").
Qed.

End proof.
