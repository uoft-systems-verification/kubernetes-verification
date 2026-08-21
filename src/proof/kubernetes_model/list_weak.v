From New.proof Require Import prelude empty_ffi.
From New.proof.kubernetes_model Require Export list.

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
    "(Hsl & Hobjs & %Hperm & %Hvalid & %Hnodup & Hinv_Hstate_m_addr &
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

(** The weak property required of a selector by the fragment-free list API.
    It deliberately exposes no matching semantics: filtering may retain any
    subset, but it must preserve ownership, validity, and object kind. *)
Definition weak_selector (selector : labels.Selector.t) : Prop :=
  ∀ (kind : go_string) sl interfaces objs,
  Forall KObjectV.valid objs →
  Forall (λ obj, KObjectV.kind obj = kind) objs →
  {{{ is_pkg_init apimodel ∗
      sl ↦* (interface.ok <$> interfaces) ∗
      ([∗ list] i;obj ∈ interfaces;objs, KObjectV.deepown_i i obj 1)
  }}}
    @! apimodel.filterByLabelSelector #sl #selector
  {{{ sl' interfaces' objs', RET (#sl', #interface.nil);
      sl' ↦* (interface.ok <$> interfaces') ∗
      ([∗ list] i;obj ∈ interfaces';objs', KObjectV.deepown_i i obj 1) ∗
      ⌜ Forall KObjectV.valid objs' ⌝ ∗
      ⌜ Forall (λ obj, KObjectV.kind obj = kind) objs' ⌝
  }}}.

(** [Everything] returns the immutable empty selector. Its generated global
    initializer is opaque, so this is the single trusted bridge from that
    package boundary to the fragment-free selector interface. *)
(** TODO: Revisit this specification so it captures that [Everything]
    preserves every input object, and prove it by modeling the opaque global
    empty selector instead of admitting the result. *)
Lemma wp_Everything_weak :
  {{{ is_pkg_init labels }}}
    @! labels.Everything #()
  {{{ selector, RET #selector; ⌜ weak_selector selector ⌝ }}}.
Proof. Admitted.

(** Type-general weak Hoare specification for selector-based list calls. *)
Lemma wp_State__objListBySelector_weak γ l (kind namespace : go_string)
    (selector : labels.Selector.t) :
  weak_selector selector →
  {{{ is_pkg_init apimodel ∗
      "#Hisk" ∷ is_kubernetes γ l
  }}}
    l @! (go.PointerType apimodel.State) @! "objListBySelector" #kind #namespace #selector
  {{{ sl interfaces objs, RET (#sl, #interface.nil);
      sl ↦* (interface.ok <$> interfaces) ∗
      ([∗ list] i;obj ∈ interfaces;objs, KObjectV.deepown_i i obj 1) ∗
      ⌜ Forall KObjectV.valid objs ⌝ ∗
      ⌜ Forall (λ obj, KObjectV.kind obj = kind) objs ⌝
  }}}.
Proof.
  intros Hselector.
  iIntros (Φ) "(#Hpkg & #Hisk) HΦ".
  wp_method_call. rewrite /apimodel.State__objListBySelectorⁱᵐᵖˡ. wp_call.
  wp_auto.
  wp_apply (wp_State__objList_weak γ l kind namespace with
    "[$Hpkg $Hisk]").
  iIntros (sl interfaces objs) "(Hsl & Hobjs & %Hvalid & %Hkind)".
  wp_auto.
  wp_bind (@! apimodel.filterByLabelSelector #sl #selector)%E.
  iApply (Hselector kind sl interfaces objs Hvalid Hkind with
    "[$Hpkg $Hsl $Hobjs]").
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
    (selector : labels.Selector.t) :
  weak_selector selector →
  {{{ is_pkg_init apimodel ∗
      "#Hisk" ∷ is_kubernetes γ l
  }}}
    l @! (go.PointerType apimodel.State) @! "ReplicaSetMutList" #namespace #selector
  {{{ sl ptrs replica_sets, RET (#sl, #interface.nil);
      sl ↦* ptrs ∗
      ([∗ list] ptr;rs ∈ ptrs;replica_sets, ReplicaSetV.deepown_l ptr rs 1) ∗
      ⌜ Forall ReplicaSetV.valid replica_sets ⌝
  }}}.
Proof.
  intros Hselector.
  iIntros (Φ) "(#Hpkg & #Hisk) HΦ".
  wp_method_call. rewrite /apimodel.State__ReplicaSetMutListⁱᵐᵖˡ. wp_call.
  wp_auto.
  wp_apply (wp_State__objListBySelector_weak γ l ReplicaSetV.kind
    namespace selector Hselector with "[$Hpkg $Hisk]").
  iIntros (objs_sl interfaces objs)
    "(Hobjs_sl & Hobjs & %Hvalid & %Hkind)".
  destruct (kobject_list_to_replica_sets objs Hkind) as [replica_sets ->].
  rewrite Forall_fmap in Hvalid.
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
    (selector : labels.Selector.t) :
  weak_selector selector →
  {{{ is_pkg_init apimodel ∗
      "#Hisk" ∷ is_kubernetes γ l
  }}}
    l @! (go.PointerType apimodel.State) @! "ReplicaSetList" #namespace #selector
  {{{ sl ptrs replica_sets, RET (#sl, #interface.nil);
      sl ↦* ptrs ∗
      ([∗ list] ptr;rs ∈ ptrs;replica_sets, ReplicaSetV.deepown_l ptr rs 1) ∗
      ⌜ Forall ReplicaSetV.valid replica_sets ⌝
  }}}.
Proof.
  intros Hselector.
  iIntros (Φ) "(#Hpkg & #Hisk) HΦ".
  wp_method_call. rewrite /apimodel.State__ReplicaSetListⁱᵐᵖˡ. wp_call.
  wp_auto.
  wp_bind (l @! (go.PointerType apimodel.State) @! "ReplicaSetMutList"
    #namespace #selector)%E.
  iApply (wp_State__ReplicaSetMutList_weak γ l namespace selector
    Hselector with "[$Hpkg $Hisk]").
  iNext. iIntros (sl ptrs replica_sets) "Hpost". wp_auto.
  iApply "HΦ". iExact "Hpost".
Qed.

End proof.
