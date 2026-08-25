From New.proof Require Import prelude empty_ffi.
From New.proof.kubernetes_model Require Export list.
From New.proof.k8s_io.apimachinery.pkg Require Export labels.

Section proof.
Context `{hG: !heapGS Σ} `{!ffi_semantics _ _}.
Context {sem : go.Semantics} {package_sem : apimodel.Assumptions}.
Context `{!kubernetesModelG Σ}.
Local Set Default Proof Using "All".

(** A fragment-free Hoare interface to the type-general list operation.  The
    returned objects are deep copies, so callers own them independently of the
    objects protected by the Kubernetes invariant. *)
Lemma wp_State__objList_weak γ l (kind namespace : go_string) :
  {{{ is_pkg_init apimodel ∗
      "#Hisk" ∷ is_kubernetes γ l
  }}}
    l @! (go.PointerType apimodel.State) @! "objList" #kind #namespace
  {{{ sl interfaces objs, RET #sl;
      sl ↦* (interface.ok <$> interfaces) ∗
      ([∗ list] i;obj ∈ interfaces;objs, KObjectV.deepown_i i obj 1) ∗
      ⌜ Forall KObjectV.valid objs ⌝ ∗
      ⌜ Forall KObjectV.extra_valid objs ⌝ ∗
      ⌜ Forall (λ obj, KObjectV.kind obj = kind) objs ⌝
  }}}.
Proof.
  iIntros (Φ) "(#Hpkg & #Hisk) HΦ".
  iDestruct "Hisk" as (mu_l) "[#Hmu #Hkinv]".
  iAssert (is_pkg_init sync) as "#Hsync".
  { iPkgInit. }
  wp_method_call. rewrite /apimodel.State__objListⁱᵐᵖˡ. wp_call.
  wp_apply wp_with_defer as "%defer Hdefer". simpl subst. wp_auto.
  wp_apply wp_Mutex__Lock.
  { iFrame "#". }
  iIntros "[Hown_Mutex H]".
  iDestruct "H" as (phys_state_l phys_used_uid_l phys_used_rv_l phys_state
    phys_used_uid phys_used_rv abs_state used_uid used_reference) "H".
  iNamedPrefix "H" "Hinv_". wp_auto.
  wp_apply (wp_State__objListLocked γ l kind namespace
    phys_state_l phys_state abs_state used_uid with
    "[$Hpkg $Hinv_Hstate_m_addr $Hinv_Hown_phys $Hinv_Hown_abs
      $Hinv_Hphys_abs_rep]").
  iIntros (sl interfaces objs)
    "(Hsl & Hobjs & %Hperm & %Hvalid & %Hextra_valid & %Hnodup &
      Hinv_Hstate_m_addr &
      Hinv_Hown_phys & Hinv_Hown_abs & Hinv_Hphys_abs_rep)".
  iPoseProof (kview.own_auth_valid_forall with "Hinv_Hown_abs")
    as "%Habs_valid".
  assert (Forall (λ obj, KObjectV.kind obj = kind) objs) as Hkind.
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
  wp_auto.
  iCombineNamed "Hinv_*" as "H".
  wp_apply (wp_Mutex__Unlock _ (kubernetes_inv γ l)
    with "[$Hown_Mutex H]").
  { iNamed "H". iFrame. iFrame "#". done. }
  iApply "HΦ". iFrame. done.
Qed.

(** Borrow the labels map from an owned ObjectMeta. The wand returns the map
    ownership to the enclosing metadata object after [Matches] has inspected
    it. *)
Lemma wp_ObjectMeta__GetLabels_deepown meta_l meta dq :
  {{{ is_pkg_init v1 ∗
      ObjectMetaV.deepown_l meta_l meta dq
  }}}
    meta_l @! (go.PointerType v1.ObjectMeta) @! "GetLabels" #()
  {{{ labels_l, RET #labels_l;
      labels_set_rep labels_l meta.(ObjectMetaV.Labels') dq ∗
      (labels_set_rep labels_l meta.(ObjectMetaV.Labels') dq -∗
        ObjectMetaV.deepown_l meta_l meta dq)
  }}}.
Proof.
  wp_start as "Hmeta".
  iDestruct "Hmeta" as (meta_c) "[Hmeta_l Hmeta]".
  iDestruct (struct_fields_split (V:=v1.ObjectMeta.t) with "Hmeta_l") as
    "[Hmeta_fields %Hmeta_nonnull]".
  iNamedPrefix "Hmeta_fields" "Hfield_".
  iNamed "Hmeta".
  wp_auto.
  iApply "HΦ".
  destruct meta.(ObjectMetaV.Labels') as [label_map|] eqn:Hlabels.
  - iDestruct "Hdeepown_labels_some" as (label_map_c)
      "[Hlabel_map %Hlabel_map]". subst label_map_c.
    iAssert (labels_set_rep meta_c.(v1.ObjectMeta.Labels')
      (Some label_map) dq) with "[Hlabel_map]" as "Hlabels_rep".
    { rewrite /labels_set_rep. iFrame.
      iPureIntro. exact Hdeepown_labels_none. }
    iFrame "Hlabels_rep".
    iIntros "Hlabels_rep_back".
    iEval (rewrite /labels_set_rep) in "Hlabels_rep_back".
    iDestruct "Hlabels_rep_back" as "[_ Hlabel_map]".
    iCombineNamed "Hfield_*" as "Hmeta_fields".
    iAssert (typed_pointsto_def meta_l meta_c dq) with
      "[Hmeta_fields]" as "Hmeta_l".
    { iNamed "Hmeta_fields". simpl. rewrite /named. iFrame. }
    iDestruct (struct_fields_combine (V:=v1.ObjectMeta.t) meta_l meta_c dq
      Hmeta_nonnull with "Hmeta_l") as "Hmeta_l".
    iExists meta_c. iFrame "Hmeta_l".
    rewrite /ObjectMetaV.deepown /named Hlabels. iFrame. iFrame "%".
    done.
  - iAssert (labels_set_rep meta_c.(v1.ObjectMeta.Labels') None dq)
      as "Hlabels_rep".
    { rewrite /labels_set_rep. iSplit; last done.
      iPureIntro. split; [intros _; done|].
      intros _. apply Hdeepown_labels_none. done. }
    iFrame "Hlabels_rep".
    iIntros "_".
    iCombineNamed "Hfield_*" as "Hmeta_fields".
    iAssert (typed_pointsto_def meta_l meta_c dq) with
      "[Hmeta_fields]" as "Hmeta_l".
    { iNamed "Hmeta_fields". simpl. rewrite /named. iFrame. }
    iDestruct (struct_fields_combine (V:=v1.ObjectMeta.t) meta_l meta_c dq
      Hmeta_nonnull with "Hmeta_l") as "Hmeta_l".
    iExists meta_c. iFrame "Hmeta_l".
    rewrite /ObjectMetaV.deepown /named Hlabels. iFrame. iFrame "%".
Qed.

(** Filtering uses the semantic selector representation from the labels
    package. The weak list API intentionally forgets which valid objects
    matched once the filter has run. *)
Lemma wp_filterByLabelSelector_weak (kind : go_string) sl interfaces objs
    (selector : labels.Selector.t) P `{!∀ ls, Decision (P ls)} :
  Forall KObjectV.valid objs →
  Forall KObjectV.extra_valid objs →
  Forall (λ obj, KObjectV.kind obj = kind) objs →
  {{{ is_pkg_init apimodel ∗
      "#Hselector" ∷ is_selector selector P ∗
      "Hitems" ∷ sl ↦* (interface.ok <$> interfaces) ∗
      "Hobjects" ∷ ([∗ list] i;obj ∈ interfaces;objs,
        KObjectV.deepown_i i obj 1)
  }}}
    @! apimodel.filterByLabelSelector #sl #selector
  {{{ sl' interfaces' objs', RET (#sl', #interface.nil);
      sl' ↦* (interface.ok <$> interfaces') ∗
      ([∗ list] i;obj ∈ interfaces';objs', KObjectV.deepown_i i obj 1) ∗
      ⌜ Forall KObjectV.valid objs' ⌝ ∗
      ⌜ Forall KObjectV.extra_valid objs' ⌝ ∗
      ⌜ Forall (λ obj, KObjectV.kind obj = kind) objs' ⌝
  }}}.
Proof.
  intros Hvalid Hextra_valid Hkind.
  wp_start as "H". iNamed "H".
  iAssert (is_pkg_init code.k8s_io.apimachinery.pkg.api.meta.pkg_id.meta)
    as "#Hmeta_init".
  { iPkgInit. }
  iAssert (is_pkg_init v1) as "#Hv1_init".
  { iPkgInit. }
  wp_auto.
  iDestruct (own_slice_len with "Hitems") as %[Hitems_len Hitems_nonneg].
  rewrite map_length in Hitems_len.
  iDestruct (big_sepL2_length with "Hobjects") as %Hobjects_len.
  iPoseProof (own_slice_nil (V:=interface.t)) as "Hfiltered".
  iPoseProof (own_slice_cap_nil (V:=interface.t)) as "Hfiltered_cap".
  set I := (∃ (i : w64) (val : interface.t) (filtered_sl : slice.t)
      (filtered_interfaces : list interface.t_ok)
      (filtered_objs : list KObjectV.t),
    "Hi" ∷ i_ptr ↦ i ∗
    "Hval" ∷ val_ptr ↦ val ∗
    "Hfiltered_items" ∷ filtered_items_ptr ↦ filtered_sl ∗
    "Hfiltered" ∷ filtered_sl ↦* (interface.ok <$> filtered_interfaces) ∗
    "Hfiltered_cap" ∷ own_slice_cap interface.t filtered_sl (DfracOwn 1) ∗
    "Hremaining" ∷ ([∗ list] interface_i;obj ∈
      drop (sint.nat i) interfaces;drop (sint.nat i) objs,
      KObjectV.deepown_i interface_i obj 1) ∗
    "Hfiltered_objects" ∷ ([∗ list] interface_i;obj ∈
      filtered_interfaces;filtered_objs, KObjectV.deepown_i interface_i obj 1) ∗
    "%Hi_bounds" ∷ ⌜ 0 ≤ sint.Z i ≤ sint.Z (slice.len sl) ⌝ ∗
    "%Hfiltered_valid" ∷ ⌜ Forall KObjectV.valid filtered_objs ⌝ ∗
    "%Hfiltered_extra_valid" ∷
      ⌜ Forall KObjectV.extra_valid filtered_objs ⌝ ∗
    "%Hfiltered_kind" ∷
      ⌜ Forall (λ obj, KObjectV.kind obj = kind) filtered_objs ⌝)%I.
  iAssert I with
    "[i val filtered_items Hfiltered Hfiltered_cap Hobjects]"
    as "Hloop".
  { iExists (W64 0), (zero_val interface.t), slice.nil, [], [].
    rewrite !drop_0 !big_sepL2_nil /=.
    iFrame "i val filtered_items Hfiltered Hfiltered_cap Hobjects".
    iPureIntro. repeat split; try constructor; word. }
  iClear "Hfiltered Hfiltered_cap".
  wp_for "Hloop". wp_if_destruct.
  -
    assert (0 ≤ sint.Z i < sint.Z (slice.len sl)) as Hibounds by word.
    list_elem interfaces (sint.Z i) as this_interface.
    assert (∃ this_obj, objs !! sint.nat i = Some this_obj) as
      [this_obj Hthis_obj_lookup].
    { apply lookup_lt_is_Some_2. rewrite -Hobjects_len Hitems_len. word. }
    assert ((interface.ok <$> interfaces) !! sint.nat i =
      Some (interface.ok this_interface)) as Hthis_value_lookup.
    { rewrite list_lookup_fmap Hthis_interface_lookup. done. }
    rewrite decide_True.
    { exact Hibounds. }
    wp_apply (wp_load_slice_index (V:=interface.t)
      (t:=go.InterfaceType []) sl (sint.Z i)
      (interface.ok <$> interfaces) (DfracOwn 1)
      (interface.ok this_interface) with "[$Hitems]");
      [word|iPureIntro; exact Hthis_value_lookup|].
    iIntros "Hitems". wp_auto.
    assert (drop (sint.nat i) interfaces =
      this_interface :: drop (S (sint.nat i)) interfaces) as Hdrop_interfaces.
    { apply drop_S. exact Hthis_interface_lookup. }
    assert (drop (sint.nat i) objs =
      this_obj :: drop (S (sint.nat i)) objs) as Hdrop_objs.
    { apply drop_S. exact Hthis_obj_lookup. }
    iEval (rewrite Hdrop_interfaces Hdrop_objs) in "Hremaining".
    iDestruct "Hremaining" as "[Hthis Hremaining]".
    iDestruct "Hthis" as (this_l) "[%Hthis_interface Hthis]".
    wp_apply wp_Accessor; first (iPureIntro; exact Hthis_interface).
    iPoseProof (KObjectV.deepown_l_split with "Hthis") as
      "(%Hthis_l_nonnull & Hthis_type & Hthis_meta & Hthis_spec & Hthis_status)".
    wp_apply (wp_ObjectMeta__GetLabels_deepown with "[$Hv1_init $Hthis_meta]").
    iIntros (labels_l) "[Hlabels Hrestore_meta]". wp_auto.
    wp_bind ((match selector with
      | interface.ok selector_i =>
          Val (#(methods selector_i.(interface.ty) "Matches"
            selector_i.(interface.v)))
      | interface.nil => Panic "nil interface"
      end)
      #(interface.ok (interface.mk labels.Set' #labels_l)))%E.
    iApply (wp_Selector__Matches_resolved selector P labels_l
      (KObjectV.objectmeta this_obj).(ObjectMetaV.Labels') 1
      with "[$Hselector $Hlabels]").
    iNext. iIntros (matches) "(#Hselector_again & Hlabels & %Hmatches)".
    iPoseProof ("Hrestore_meta" with "Hlabels") as "Hthis_meta".
    iPoseProof (KObjectV.deepown_l_restore _ _ _ Hthis_l_nonnull with
      "[$Hthis_type $Hthis_meta $Hthis_spec $Hthis_status]") as "Hthis".
    iAssert (KObjectV.deepown_i this_interface this_obj 1)
      with "[Hthis]" as "Hthis".
    { iExists this_l. iFrame "Hthis". iPureIntro. exact Hthis_interface. }
    destruct matches.
    + wp_auto.
      wp_apply wp_slice_literal. iSplitR; first done.
      iIntros (one_sl) "[Hone _]". wp_auto.
      wp_apply (wp_slice_append with
        "[$Hfiltered $Hfiltered_cap $Hone]").
      iIntros (filtered_sl') "(Hfiltered & Hfiltered_cap & Hone)".
      wp_auto. iApply wp_for_post_do. wp_auto.
      iFrame "HΦ Hitems selector".
      iExists (word.add i (W64 1)), (interface.ok this_interface),
        filtered_sl', (filtered_interfaces ++ [this_interface]),
        (filtered_objs ++ [this_obj]).
      assert (sint.nat (word.add i (W64 1)) = S (sint.nat i)) as Hnext by word.
      rewrite Hnext fmap_app /=.
      iFrame.
      simpl.
      iPureIntro. repeat split; try word.
      * apply Forall_app. split; [done|constructor; [|constructor]].
        rewrite Forall_forall in Hvalid. apply Hvalid.
        rewrite <-list_elem_of_In. eapply list_elem_of_lookup_2.
        exact Hthis_obj_lookup.
      * apply Forall_app. split; [done|constructor; [|constructor]].
        rewrite Forall_forall in Hextra_valid. apply Hextra_valid.
        rewrite <-list_elem_of_In. eapply list_elem_of_lookup_2.
        exact Hthis_obj_lookup.
      * apply Forall_app. split; [done|constructor; [|constructor]].
        rewrite Forall_forall in Hkind. apply Hkind.
        rewrite <-list_elem_of_In. eapply list_elem_of_lookup_2.
        exact Hthis_obj_lookup.
    + wp_auto. iApply wp_for_post_do. wp_auto.
      iFrame "HΦ Hitems selector".
      iExists (word.add i (W64 1)), (interface.ok this_interface),
        filtered_sl, filtered_interfaces, filtered_objs.
      assert (sint.nat (word.add i (W64 1)) = S (sint.nat i)) as -> by word.
      iFrame. simpl. iFrame. iPureIntro.
      repeat split; try word; done.
  -
    assert (sint.nat i = length interfaces) as Hi_len.
    { rewrite Hitems_len. word. }
    iApply ("HΦ" $! filtered_sl filtered_interfaces filtered_objs).
    iFrame. done.
Qed.

(** Type-general weak Hoare specification for selector-based list calls. *)
Lemma wp_State__objListBySelector_weak γ l (kind namespace : go_string)
    (selector : labels.Selector.t) P `{!∀ ls, Decision (P ls)} :
  {{{ is_pkg_init apimodel ∗
      "#Hselector" ∷ is_selector selector P ∗
      "#Hisk" ∷ is_kubernetes γ l
  }}}
    l @! (go.PointerType apimodel.State) @! "objListBySelector" #kind #namespace #selector
  {{{ sl interfaces objs, RET (#sl, #interface.nil);
      sl ↦* (interface.ok <$> interfaces) ∗
      ([∗ list] i;obj ∈ interfaces;objs, KObjectV.deepown_i i obj 1) ∗
      ⌜ Forall KObjectV.valid objs ⌝ ∗
      ⌜ Forall KObjectV.extra_valid objs ⌝ ∗
      ⌜ Forall (λ obj, KObjectV.kind obj = kind) objs ⌝
  }}}.
Proof.
  iIntros (Φ) "(#Hpkg & #Hselector & #Hisk) HΦ".
  wp_method_call. rewrite /apimodel.State__objListBySelectorⁱᵐᵖˡ. wp_call.
  wp_auto.
  wp_apply (wp_State__objList_weak γ l kind namespace with
    "[$Hpkg $Hisk]").
  iIntros (sl interfaces objs)
    "(Hsl & Hobjs & %Hvalid & %Hextra_valid & %Hkind)".
  wp_auto.
  wp_bind (@! apimodel.filterByLabelSelector #sl #selector)%E.
  iApply (wp_filterByLabelSelector_weak kind sl interfaces objs selector P
    Hvalid Hextra_valid Hkind with "[$Hpkg $Hselector $Hsl $Hobjs]").
  iNext. iIntros (sl' interfaces' objs') "Hpost". wp_auto.
  iApply "HΦ". iExact "Hpost".
Qed.

Lemma kobject_list_to_replica_sets objs :
  Forall (λ obj, KObjectV.kind obj = ReplicaSetV.kind) objs →
  ∃ replica_sets, objs = KObjectV.ReplicaSet <$> replica_sets.
Proof.
  induction 1 as [|obj objs Hkind _ [replica_sets ->]].
  - exists []. done.
  - destruct obj as [pod|replica_set|pvc|stateful_set];
      simpl in Hkind; try discriminate.
    exists (replica_set :: replica_sets). done.
Qed.

Lemma replica_set_interfaces_to_ptrs interfaces replica_sets :
  ([∗ list] i;rs ∈ interfaces;replica_sets,
    KObjectV.deepown_i i (KObjectV.ReplicaSet rs) 1) -∗
  ∃ ptrs,
    ⌜ interfaces = (λ ptr, interface.mk
      (go.PointerType v1.ReplicaSet) #ptr) <$> ptrs ⌝ ∗
    ([∗ list] ptr;rs ∈ ptrs;replica_sets,
      ReplicaSetV.deepown_l ptr rs 1).
Proof.
  revert replica_sets.
  induction interfaces as [|i interfaces IH]; intros [|rs replica_sets]; simpl.
  - iIntros "_". iExists []. iSplit; done.
  - iIntros "H". iDestruct "H" as %[].
  - iIntros "H". iDestruct "H" as %[].
  - iIntros "[Hi Hrest]".
    iDestruct "Hi" as (ptr) "[%Hi Hrs]".
    simpl in Hi. subst i.
    iDestruct (IH with "Hrest") as (ptrs) "[%Hinterfaces Hrest]".
    iExists (ptr :: ptrs). iFrame. iPureIntro. simpl. f_equal. done.
Qed.

Local Lemma wp_State__ReplicaSetMutList_weak γ l (namespace : go_string)
    (selector : labels.Selector.t) P `{!∀ ls, Decision (P ls)} :
  {{{ is_pkg_init apimodel ∗
      "#Hselector" ∷ is_selector selector P ∗
      "#Hisk" ∷ is_kubernetes γ l
  }}}
    l @! (go.PointerType apimodel.State) @! "ReplicaSetMutList" #namespace #selector
  {{{ sl ptrs replica_sets, RET (#sl, #interface.nil);
      sl ↦* ptrs ∗
      ([∗ list] ptr;rs ∈ ptrs;replica_sets, ReplicaSetV.deepown_l ptr rs 1) ∗
      ⌜ Forall ReplicaSetV.valid replica_sets ⌝ ∗
      ⌜ Forall ReplicaSetV.extra_valid replica_sets ⌝
  }}}.
Proof.
  iIntros (Φ) "(#Hpkg & #Hselector & #Hisk) HΦ".
  wp_method_call. rewrite /apimodel.State__ReplicaSetMutListⁱᵐᵖˡ. wp_call.
  wp_auto.
  wp_apply (wp_State__objListBySelector_weak γ l ReplicaSetV.kind
    namespace selector P with "[$Hpkg $Hselector $Hisk]").
  iIntros (objs_sl interfaces objs)
    "(Hobjs_sl & Hobjs & %Hvalid & %Hextra_valid & %Hkind)".
  destruct (kobject_list_to_replica_sets objs Hkind) as [replica_sets ->].
  rewrite Forall_fmap in Hvalid.
  rewrite Forall_fmap in Hextra_valid.
  change (Forall ReplicaSetV.extra_valid replica_sets) in Hextra_valid.
  iEval (rewrite big_sepL2_fmap_r) in "Hobjs".
  iDestruct (replica_set_interfaces_to_ptrs with "Hobjs") as
    (ptrs) "[%Hinterfaces Hreplica_sets]".
  subst interfaces.
  wp_auto.
  iDestruct (own_slice_len with "Hobjs_sl") as %(Hobjs_len1 & Hobjs_len2).
  rewrite !map_length in Hobjs_len1.
  iDestruct (own_slice_wf with "Hobjs_sl") as %Hobjs_cap.
  iDestruct (big_sepL2_length with "Hreplica_sets") as %Hptrs_len.
  wp_apply (wp_slice_make3 (V:=loc) (t:=go.PointerType v1.ReplicaSet)); first word.
  iIntros (rss_sl) "(Hrss & Hrss_cap & %Hrss_cap_eq)".
  wp_auto.
  set I := (∃ (i : w64) (obj : interface.t) (rss_sl' : slice.t)
      (ptrs' : list loc),
    "Hi_ptr" ∷ i_ptr ↦ i ∗
    "Hobj_ptr" ∷ obj_ptr ↦ obj ∗
    "Hrss_ptr" ∷ rss_ptr ↦ rss_sl' ∗
    "Hrss" ∷ rss_sl' ↦* ptrs' ∗
    "Hrss_cap" ∷ own_slice_cap loc rss_sl' (DfracOwn 1) ∗
    "%Hptrs'" ∷ ⌜ ptrs' = take (sint.nat i) ptrs ⌝ ∗
    "%Hi" ∷ ⌜ 0 ≤ sint.Z i ≤ sint.Z (slice.len objs_sl) ⌝)%I.
  iAssert I with "[i obj rss Hrss Hrss_cap]" as "Hloop".
  { iExists (W64 0), (zero_val interface.t), rss_sl, [].
    iFrame. iPureIntro. split; [done|word]. }
  wp_for "Hloop". wp_if_destruct.
  1: {
    destruct (decide (0 ≤ sint.Z i < sint.Z (slice.len objs_sl))) as [_|Hbounds]; last word.
    assert (∃ this_ptr, ptrs !! sint.nat i = Some this_ptr) as
      [this_ptr Hthis_ptr_lookup].
    { apply lookup_lt_is_Some_2. rewrite Hobjs_len1. word. }
    assert ((interface.ok <$> ((λ ptr, interface.mk
        (go.PointerType v1.ReplicaSet) #ptr) <$> ptrs)) !! sint.nat i =
      Some (interface.ok (interface.mk
        (go.PointerType v1.ReplicaSet) #this_ptr))) as Hinterface_lookup.
    { rewrite !list_lookup_fmap Hthis_ptr_lookup. done. }
    wp_apply (wp_load_slice_index (V:=interface.t) (t:=go.InterfaceType [])
      objs_sl (sint.Z i)
      (interface.ok <$> ((λ ptr, interface.mk
        (go.PointerType v1.ReplicaSet) #ptr) <$> ptrs))
      (DfracOwn 1)
      (interface.ok (interface.mk
        (go.PointerType v1.ReplicaSet) #this_ptr)) with "[$Hobjs_sl]");
      [word|iPureIntro; exact Hinterface_lookup|].
    iIntros "Hobjs_sl". wp_auto.
    rewrite decide_True;
      [change (go.PointerType api_apps_v1.ReplicaSet)
        with (go.PointerType v1.ReplicaSet); reflexivity|].
    wp_auto.
    rewrite bool_decide_true;
      [change (go.PointerType api_apps_v1.ReplicaSet)
        with (go.PointerType v1.ReplicaSet); reflexivity|].
    wp_auto.
    wp_apply wp_slice_literal. iSplitR; first done.
    iIntros (sl_one) "[Hsl_one _]". wp_auto.
    wp_apply (wp_slice_append with "[$Hrss $Hrss_cap $Hsl_one]").
    iIntros (rss_sl'') "(Hrss & Hrss_cap & Hsl_one)". wp_auto.
    iApply wp_for_post_do. wp_auto.
    iFrame "Hobjs_sl HΦ Hreplica_sets".
    iExists (word.add i (W64 1)),
      (interface.ok (interface.mk (go.PointerType v1.ReplicaSet) #this_ptr)),
      rss_sl'', (take (sint.nat i) ptrs ++ [this_ptr]).
    iFrame.
    iPureIntro. split.
    + assert (sint.nat (word.add i (W64 1)) = S (sint.nat i)) as -> by word.
      rewrite (take_S_r _ _ this_ptr Hthis_ptr_lookup). done.
    + word. }
  clear I.
  assert (sint.nat i = length ptrs) as Hi_len.
  { rewrite Hobjs_len1. word. }
  assert (take (sint.nat i) ptrs = ptrs) as Htake by (apply take_ge; lia).
  iApply ("HΦ" $! rss_sl' ptrs replica_sets).
  iEval (rewrite Htake) in "Hrss".
  iFrame. done.
Qed.

(** Weak typed list specification used by controllers that only inspect the
    returned deep copies and rely on their API validity. *)
Lemma wp_State__ReplicaSetList_weak γ l (namespace : go_string)
    (selector : labels.Selector.t) P `{!∀ ls, Decision (P ls)} :
  {{{ is_pkg_init apimodel ∗
      "#Hselector" ∷ is_selector selector P ∗
      "#Hisk" ∷ is_kubernetes γ l
  }}}
    l @! (go.PointerType apimodel.State) @! "ReplicaSetList" #namespace #selector
  {{{ sl ptrs replica_sets, RET (#sl, #interface.nil);
      sl ↦* ptrs ∗
      ([∗ list] ptr;rs ∈ ptrs;replica_sets, ReplicaSetV.deepown_l ptr rs 1) ∗
      ⌜ Forall ReplicaSetV.valid replica_sets ⌝ ∗
      ⌜ Forall ReplicaSetV.extra_valid replica_sets ⌝
  }}}.
Proof.
  iIntros (Φ) "(#Hpkg & #Hselector & #Hisk) HΦ".
  wp_method_call. rewrite /apimodel.State__ReplicaSetListⁱᵐᵖˡ. wp_call.
  wp_auto.
  wp_bind (l @! (go.PointerType apimodel.State) @! "ReplicaSetMutList"
    #namespace #selector)%E.
  iApply (wp_State__ReplicaSetMutList_weak γ l namespace selector P
    with "[$Hpkg $Hselector $Hisk]").
  iNext. iIntros (sl ptrs replica_sets) "Hpost". wp_auto.
  iApply "HΦ". iExact "Hpost".
Qed.

Lemma kobject_list_to_pods objs :
  Forall (λ obj, KObjectV.kind obj = PodV.kind) objs →
  ∃ pods, objs = KObjectV.Pod <$> pods.
Proof.
  induction 1 as [|obj objs Hkind _ [pods ->]].
  - exists []. done.
  - destruct obj as [pod|replica_set|pvc|stateful_set];
      simpl in Hkind; try discriminate.
    exists (pod :: pods). done.
Qed.

Lemma pod_interfaces_to_ptrs interfaces pods :
  ([∗ list] i;pod ∈ interfaces;pods,
    KObjectV.deepown_i i (KObjectV.Pod pod) 1) -∗
  ∃ ptrs,
    ⌜ interfaces = (λ ptr, interface.mk
      (go.PointerType v1.Pod) #ptr) <$> ptrs ⌝ ∗
    ([∗ list] ptr;pod ∈ ptrs;pods, PodV.deepown_l ptr pod 1).
Proof.
  revert pods.
  induction interfaces as [|i interfaces IH]; intros [|pod pods]; simpl.
  - iIntros "_". iExists []. iSplit; done.
  - iIntros "H". iDestruct "H" as %[].
  - iIntros "H". iDestruct "H" as %[].
  - iIntros "[Hi Hrest]".
    iDestruct "Hi" as (ptr) "[%Hi Hpod]".
    simpl in Hi. subst i.
    iDestruct (IH with "Hrest") as (ptrs) "[%Hinterfaces Hrest]".
    iExists (ptr :: ptrs). iFrame. iPureIntro. simpl. f_equal. done.
Qed.

Local Lemma wp_State__PodMutList_weak γ l (namespace : go_string)
    (selector : labels.Selector.t) P `{!∀ ls, Decision (P ls)} :
  {{{ is_pkg_init apimodel ∗
      "#Hselector" ∷ is_selector selector P ∗
      "#Hisk" ∷ is_kubernetes γ l
  }}}
    l @! (go.PointerType apimodel.State) @! "PodMutList" #namespace #selector
  {{{ sl ptrs pods, RET (#sl, #interface.nil);
      sl ↦* ptrs ∗
      ([∗ list] ptr;pod ∈ ptrs;pods, PodV.deepown_l ptr pod 1) ∗
      ⌜ Forall PodV.valid pods ⌝
  }}}.
Proof.
  iIntros (Φ) "(#Hpkg & #Hselector & #Hisk) HΦ".
  wp_method_call. rewrite /apimodel.State__PodMutListⁱᵐᵖˡ. wp_call.
  wp_auto.
  wp_apply (wp_State__objListBySelector_weak γ l PodV.kind
    namespace selector P with "[$Hpkg $Hselector $Hisk]").
  iIntros (objs_sl interfaces objs)
    "(Hobjs_sl & Hobjs & %Hvalid & %Hextra_valid & %Hkind)".
  destruct (kobject_list_to_pods objs Hkind) as [pods ->].
  rewrite Forall_fmap in Hvalid.
  iEval (rewrite big_sepL2_fmap_r) in "Hobjs".
  iDestruct (pod_interfaces_to_ptrs with "Hobjs") as
    (ptrs) "[%Hinterfaces Hpods]".
  subst interfaces.
  wp_auto.
  iDestruct (own_slice_len with "Hobjs_sl") as %(Hobjs_len1 & Hobjs_len2).
  rewrite !map_length in Hobjs_len1.
  iDestruct (own_slice_wf with "Hobjs_sl") as %Hobjs_cap.
  iDestruct (big_sepL2_length with "Hpods") as %Hptrs_len.
  wp_apply (wp_slice_make3 (V:=loc) (t:=go.PointerType v1.Pod)); first word.
  iIntros (pods_sl) "(Hpods_sl & Hpods_cap & %Hpods_cap_eq)".
  wp_auto.
  set I := (∃ (i : w64) (obj : interface.t) (pods_sl' : slice.t)
      (ptrs' : list loc),
    "Hi_ptr" ∷ i_ptr ↦ i ∗
    "Hobj_ptr" ∷ obj_ptr ↦ obj ∗
    "Hpods_ptr" ∷ pods_ptr ↦ pods_sl' ∗
    "Hpods_sl" ∷ pods_sl' ↦* ptrs' ∗
    "Hpods_cap" ∷ own_slice_cap loc pods_sl' (DfracOwn 1) ∗
    "%Hptrs'" ∷ ⌜ ptrs' = take (sint.nat i) ptrs ⌝ ∗
    "%Hi" ∷ ⌜ 0 ≤ sint.Z i ≤ sint.Z (slice.len objs_sl) ⌝)%I.
  iAssert I with "[i obj pods Hpods_sl Hpods_cap]" as "Hloop".
  { iExists (W64 0), (zero_val interface.t), pods_sl, [].
    iFrame. iPureIntro. split; [done|word]. }
  wp_for "Hloop". wp_if_destruct.
  1: {
    destruct (decide (0 ≤ sint.Z i < sint.Z (slice.len objs_sl))) as
      [_|Hbounds]; last word.
    assert (∃ this_ptr, ptrs !! sint.nat i = Some this_ptr) as
      [this_ptr Hthis_ptr_lookup].
    { apply lookup_lt_is_Some_2. rewrite Hobjs_len1. word. }
    assert ((interface.ok <$> ((λ ptr, interface.mk
        (go.PointerType v1.Pod) #ptr) <$> ptrs)) !! sint.nat i =
      Some (interface.ok (interface.mk
        (go.PointerType v1.Pod) #this_ptr))) as Hinterface_lookup.
    { rewrite !list_lookup_fmap Hthis_ptr_lookup. done. }
    wp_apply (wp_load_slice_index (V:=interface.t) (t:=go.InterfaceType [])
      objs_sl (sint.Z i)
      (interface.ok <$> ((λ ptr, interface.mk
        (go.PointerType v1.Pod) #ptr) <$> ptrs))
      (DfracOwn 1)
      (interface.ok (interface.mk
        (go.PointerType v1.Pod) #this_ptr)) with "[$Hobjs_sl]");
      [word|iPureIntro; exact Hinterface_lookup|].
    iIntros "Hobjs_sl". wp_auto.
    rewrite decide_True;
      [change (go.PointerType api_core_v1.Pod)
        with (go.PointerType v1.Pod); reflexivity|].
    wp_auto.
    rewrite bool_decide_true;
      [change (go.PointerType api_core_v1.Pod)
        with (go.PointerType v1.Pod); reflexivity|].
    wp_auto.
    wp_apply wp_slice_literal. iSplitR; first done.
    iIntros (sl_one) "[Hsl_one _]". wp_auto.
    wp_apply (wp_slice_append with "[$Hpods_sl $Hpods_cap $Hsl_one]").
    iIntros (pods_sl'') "(Hpods_sl & Hpods_cap & Hsl_one)". wp_auto.
    iApply wp_for_post_do. wp_auto.
    iFrame "Hobjs_sl HΦ Hpods".
    iExists (word.add i (W64 1)),
      (interface.ok (interface.mk (go.PointerType v1.Pod) #this_ptr)),
      pods_sl'', (take (sint.nat i) ptrs ++ [this_ptr]).
    iFrame.
    iPureIntro. split.
    + assert (sint.nat (word.add i (W64 1)) = S (sint.nat i)) as -> by word.
      rewrite (take_S_r _ _ this_ptr Hthis_ptr_lookup). done.
    + word. }
  clear I.
  assert (sint.nat i = length ptrs) as Hi_len.
  { rewrite Hobjs_len1. word. }
  assert (take (sint.nat i) ptrs = ptrs) as Htake by (apply take_ge; lia).
  iApply ("HΦ" $! pods_sl' ptrs pods).
  iEval (rewrite Htake) in "Hpods_sl".
  iFrame. done.
Qed.

Lemma wp_State__PodList_weak γ l (namespace : go_string)
    (selector : labels.Selector.t) P `{!∀ ls, Decision (P ls)} :
  {{{ is_pkg_init apimodel ∗
      "#Hselector" ∷ is_selector selector P ∗
      "#Hisk" ∷ is_kubernetes γ l
  }}}
    l @! (go.PointerType apimodel.State) @! "PodList" #namespace #selector
  {{{ sl ptrs pods, RET (#sl, #interface.nil);
      sl ↦* ptrs ∗
      ([∗ list] ptr;pod ∈ ptrs;pods, PodV.deepown_l ptr pod 1) ∗
      ⌜ Forall PodV.valid pods ⌝
  }}}.
Proof.
  iIntros (Φ) "(#Hpkg & #Hselector & #Hisk) HΦ".
  wp_method_call. rewrite /apimodel.State__PodListⁱᵐᵖˡ. wp_call.
  wp_auto.
  wp_bind (l @! (go.PointerType apimodel.State) @! "PodMutList"
    #namespace #selector)%E.
  iApply (wp_State__PodMutList_weak γ l namespace selector P
    with "[$Hpkg $Hselector $Hisk]").
  iNext. iIntros (sl ptrs pods) "Hpost". wp_auto.
  iApply "HΦ". iExact "Hpost".
Qed.

End proof.
