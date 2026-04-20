From New.proof Require Import prelude empty_ffi.
From New.proof.kubernetes_model Require Export inv common list.

Section proof.
Context `{hG: !heapGS Σ} {go_ctx: GoContext}.
Context `{!kviewG Σ}.
Context `{!cviewG Σ}.
Context `{!mono_gsetG types.UID.t Σ}.

Definition podController_indexed_value pod : go_string :=
  match meta_parent_ref pod.(PodV.ObjectMeta') with
  | Some (parent_key, parent_uid) =>
    pod.(PodV.ObjectMeta').(ObjectMetaV.Namespace') ++ "/"%go ++
    parent_key.(KKey.Kind') ++ "/"%go ++ parent_key.(KKey.Name') ++ "/"%go ++ parent_uid
  | None => pod.(PodV.ObjectMeta').(ObjectMetaV.Namespace')
  end.

Lemma wp_index_of_podController i pod dq:
  {{{ is_pkg_init apimodel ∗
      KObjectV.deepown_i i (KObjectV.Pod pod) dq
  }}}
    @! apimodel.index_of #"podController"%go #i
  {{{ sl, RET (#sl, #interface.nil);
      sl ↦* [podController_indexed_value pod] ∗
      KObjectV.deepown_i i (KObjectV.Pod pod) dq
  }}}.
Proof. Admitted.

Lemma matching_podController_indexed_value_implies_being_children_pods pods parent_key parent_uid :
slash_free parent_key.(KKey.Kind') →
slash_free parent_key.(KKey.Namespace') →
slash_free parent_key.(KKey.Name') →
slash_free parent_uid →
Forall PodV.valid pods →
filter (λ pod, podController_indexed_value pod = parent_key.(KKey.Namespace') ++ "/"%go ++
  parent_key.(KKey.Kind') ++ "/"%go ++ parent_key.(KKey.Name') ++ "/"%go ++ parent_uid) pods =
filter (λ pod, obj_parent_ref (KObjectV.Pod pod) = Some (parent_key, parent_uid)) pods.
Proof.
  intros Hparent_kind_sf Hparent_ns_sf Hparent_name_sf Hparent_uid_sf Hpods_valid.
  induction Hpods_valid as [|pod pods Hpod_valid Hpods_valid IH]; simpl; [done|].
  rewrite !filter_cons.
  case_decide as Hindexed.
  - case_decide as Hparent.
    + simpl. f_equal. exact IH.
    + exfalso.
      apply Hparent.
      clear IH Hpods_valid Hparent.
      unfold podController_indexed_value, meta_parent_ref in Hindexed.
      unfold obj_parent_ref, meta_parent_ref.
      destruct Hpod_valid as [Hmeta_valid _].
      assert (Hpod_ns_sf : slash_free pod.(PodV.ObjectMeta').(ObjectMetaV.Namespace')).
      { unfold ObjectMetaV.valid in Hmeta_valid.
        destruct Hmeta_valid as (_ & _ & _ & _ & Hns_valid & _).
        eapply valid_namespace_slash_free; exact Hns_valid. }
      destruct (ObjectMetaV.OwnerReferences' (PodV.ObjectMeta' pod)) as [orefs|] eqn:Horefs in Hindexed |- *.
      * destruct (list_find (λ oref : OwnerReferenceV.t, oref.(OwnerReferenceV.Controller') = Some true) orefs)
          as [[idx oref]|] eqn:Hfind in Hindexed |- *.
        -- pose proof (pod_controller_index_key_inj_right
             pod.(PodV.ObjectMeta').(ObjectMetaV.Namespace')
             oref.(OwnerReferenceV.Kind')
             oref.(OwnerReferenceV.Name')
             oref.(OwnerReferenceV.UID')
             parent_key.(KKey.Namespace')
             parent_key.(KKey.Kind')
             parent_key.(KKey.Name')
             parent_uid
             Hpod_ns_sf
             Hparent_ns_sf
             Hparent_kind_sf
             Hparent_name_sf
             Hparent_uid_sf
             Hindexed) as (Hns_eq & Hkind_eq & Hname_eq & Huid_eq).
           unfold obj_parent_ref, meta_parent_ref.
           simpl.
           rewrite Horefs Hfind.
           destruct parent_key as [parent_kind parent_name parent_ns].
           simpl in *.
           subst.
           reflexivity.
        -- exfalso.
           eapply pod_controller_index_key_inequality1; [exact Hpod_ns_sf|exact Hparent_ns_sf|].
           exact Hindexed.
      * exfalso.
        eapply pod_controller_index_key_inequality1; [exact Hpod_ns_sf|exact Hparent_ns_sf|].
        exact Hindexed.
  - case_decide as Hparent.
    + exfalso.
      apply Hindexed.
      clear IH Hpods_valid Hindexed.
      unfold obj_parent_ref, meta_parent_ref in Hparent.
      unfold podController_indexed_value, meta_parent_ref.
      simpl.
      destruct (ObjectMetaV.OwnerReferences' (PodV.ObjectMeta' pod)) as [orefs|] eqn:Horefs.
      * destruct (list_find (λ oref : OwnerReferenceV.t, oref.(OwnerReferenceV.Controller') = Some true) orefs)
          as [[idx oref]|] eqn:Hfind.
        -- rewrite Horefs Hfind in Hparent |- *.
           inversion Hparent as [[Hkey_eq Huid_eq]]; clear Hparent.
           destruct parent_key as [parent_kind parent_name parent_ns].
           simpl in Hkey_eq, Huid_eq.
           inversion Hkey_eq; subst.
           reflexivity.
        -- rewrite Horefs Hfind in Hparent.
           discriminate.
      * rewrite Horefs in Hparent.
        discriminate.
    + simpl. exact IH.
Qed.

Lemma perm_filter {A} (P : A → Prop) `{!∀ x, Decision (P x)} l1 l2 :
  l1 ≡ₚ l2 →
  filter P l1 ≡ₚ filter P l2.
Proof.
  intros Hperm.
  induction Hperm.
  - done.
  - rewrite !filter_cons.
    destruct (decide (P x)); simpl.
    + apply perm_skip. exact IHHperm.
    + exact IHHperm.
  - rewrite !filter_cons.
    destruct (decide (P y)); destruct (decide (P x)); simpl; try done.
    apply perm_swap.
  - eapply Permutation_trans; done.
Qed.

Lemma filter_pod_parent_ref_fmap (pods : list PodV.t) parent_key parent_uid :
  filter (λ obj : KObjectV.t, obj_parent_ref obj = Some (parent_key, parent_uid))
    (KObjectV.Pod <$> pods) =
  KObjectV.Pod <$> filter (λ pod, obj_parent_ref (KObjectV.Pod pod) = Some (parent_key, parent_uid)) pods.
Proof.
  induction pods as [|pod pods IH]; simpl; [done|].
  rewrite !filter_cons.
  destruct (decide (obj_parent_ref (KObjectV.Pod pod) = Some (parent_key, parent_uid))); simpl; by rewrite IH.
Qed.

Lemma map_to_list_filter_perm {A} (m : gmap KKey.t A) (P : KKey.t * A → Prop) `{!∀ x, Decision (P x)} :
  map_to_list (filter P m) ≡ₚ filter P (map_to_list m).
Proof.
  rewrite map_filter_alt.
  apply map_to_list_to_map.
  apply NoDup_fmap_2_strong.
  - intros [k1 v1] [k2 v2] Hin1 Hin2 Hk_eq. simpl in Hk_eq.
    apply list_elem_of_filter in Hin1 as [_ Hin1].
    apply list_elem_of_filter in Hin2 as [_ Hin2].
    apply elem_of_map_to_list in Hin1, Hin2.
    subst k2.
    rewrite Hin1 in Hin2.
    inversion Hin2.
    reflexivity.
  - apply list.NoDup_filter.
    apply NoDup_map_to_list.
Qed.

Lemma filter_map_to_list_values {A} (P : A → Prop) `{!∀ x, Decision (P x)} (l : list (KKey.t * A)) :
  (filter (λ '(_, x), P x) l).*2 = filter P l.*2.
Proof.
  induction l as [|[k x] l IH]; simpl; [done|].
  rewrite !filter_cons.
  destruct (decide (P x)); simpl.
  - f_equal. exact IH.
  - exact IH.
Qed.

Lemma prod_map_id_fmap_values {A B} (f : A → B) (l : list (KKey.t * A)) :
  (prod_map id f <$> l).*2 = f <$> l.*2.
Proof.
  induction l as [|[k x] l IH]; simpl; [done|].
  f_equal.
  exact IH.
Qed.

Lemma pod_objectmeta_fmap (pods : list PodV.t) :
  map KObjectV.objectmeta (KObjectV.Pod <$> pods) = PodV.ObjectMeta' <$> pods.
Proof.
  induction pods as [|pod pods IH]; simpl; [done|].
  f_equal.
  exact IH.
Qed.

Lemma filter_map_to_list_values_perm {A} (m : gmap KKey.t A) (P : A → Prop) `{!∀ x, Decision (P x)} :
  filter P (map_to_list m).*2 ≡ₚ (map_to_list (filter (λ '(_, x), P x) m)).*2.
Proof.
  rewrite <- filter_map_to_list_values.
  apply Permutation_sym.
  change ((map_to_list (filter (λ '(_, x), P x) m)).*2 ≡ₚ (filter (λ '(_, x), P x) (map_to_list m)).*2).
  apply Permutation_map.
  apply map_to_list_filter_perm.
Qed.

Lemma pods_is_permutation_of_meta_map_for_meta (pods : list PodV.t) (meta_map : gmap KKey.t ObjectMetaV.t) (abs_state : gmap KKey.t KObjectV.t)
  parent_key parent_uid :
KObjectV.Pod <$> pods ≡ₚ (map_to_list (filter (λ kv, KKey.Kind' kv.1 = "Pod"%go) abs_state)).*2 →
dom meta_map = filter (λ key, KKey.Kind' key = "Pod"%go)
  (dom (filter (λ '(_, v), obj_parent_ref v = Some (parent_key, parent_uid)) abs_state)) →
map_Forall (λ k meta, ∃ obj, abs_state !! k = Some obj ∧ KObjectV.objectmeta obj = meta) meta_map →
PodV.ObjectMeta' <$> (filter (λ pod, obj_parent_ref (KObjectV.Pod pod) = Some (parent_key, parent_uid)) pods) ≡ₚ
  (map_to_list meta_map).*2.
Proof.
  intros Hperm Hdom Hmeta_lookup.
  set pod_state := filter (λ kv, KKey.Kind' kv.1 = "Pod"%go) abs_state.
  set child_pod_state := filter (λ '(_, obj), obj_parent_ref obj = Some (parent_key, parent_uid)) pod_state.
  assert (Hdom_child : dom meta_map = dom child_pod_state).
  { rewrite Hdom /child_pod_state /pod_state.
    apply set_eq; intros k.
    split.
    - intros Hk.
      apply elem_of_filter in Hk as [Hkind Hk_dom].
      apply elem_of_dom in Hk_dom as [obj Hlookup].
      apply map_lookup_filter_Some in Hlookup as [Hlookup_abs Hparent].
      apply elem_of_dom.
      exists obj.
      apply map_lookup_filter_Some. split.
      + apply map_lookup_filter_Some. split; done.
      + done.
    - intros Hk.
      apply elem_of_dom in Hk as [obj Hlookup].
      apply map_lookup_filter_Some in Hlookup as [Hlookup_pod Hparent].
      apply map_lookup_filter_Some in Hlookup_pod as [Hlookup_abs Hkind].
      apply elem_of_filter.
      split.
      + done.
      + apply elem_of_dom.
        exists obj. apply map_lookup_filter_Some. split; done.
  }
  assert (Hmeta_map_eq : meta_map = KObjectV.objectmeta <$> child_pod_state).
  { apply map_eq. intros k.
    destruct (meta_map !! k) as [meta|] eqn:Hlookup_meta.
    - pose proof (map_Forall_lookup_1 _ _ _ _ Hmeta_lookup Hlookup_meta) as [obj [Hlookup_abs Hmeta_eq]].
      assert (k ∈ dom child_pod_state) as Hk_in_child.
      { rewrite <- Hdom_child. apply elem_of_dom. eexists. exact Hlookup_meta. }
      apply elem_of_dom in Hk_in_child as [obj' Hlookup_child].
      pose proof Hlookup_child as Hlookup_child'.
      apply map_lookup_filter_Some in Hlookup_child as [Hlookup_pod Hparent].
      apply map_lookup_filter_Some in Hlookup_pod as [Hlookup_abs' Hkind].
      rewrite lookup_fmap Hlookup_child' /=.
      rewrite Hlookup_abs in Hlookup_abs'. injection Hlookup_abs' as <-.
      by rewrite Hmeta_eq.
    - symmetry.
      rewrite lookup_fmap.
      destruct (child_pod_state !! k) as [obj|] eqn:Hlookup_child; [|done].
      apply not_elem_of_dom in Hlookup_meta.
      exfalso. apply Hlookup_meta.
      rewrite Hdom_child.
      apply elem_of_dom. eexists. exact Hlookup_child.
  }
  assert (Hpod_perm :
    KObjectV.Pod <$> filter (λ pod, obj_parent_ref (KObjectV.Pod pod) = Some (parent_key, parent_uid)) pods
      ≡ₚ (map_to_list child_pod_state).*2).
  { pose proof (perm_filter
      (λ obj : KObjectV.t, obj_parent_ref obj = Some (parent_key, parent_uid))
      (KObjectV.Pod <$> pods)
      (map_to_list pod_state).*2
      Hperm) as Hperm_filtered.
    rewrite filter_pod_parent_ref_fmap in Hperm_filtered.
    eapply Permutation_trans; [exact Hperm_filtered|].
    apply filter_map_to_list_values_perm.
  }
  pose proof (Permutation_map KObjectV.objectmeta Hpod_perm) as Hmeta_perm.
  rewrite pod_objectmeta_fmap in Hmeta_perm.
  rewrite Hmeta_map_eq.
  rewrite map_to_list_fmap.
  rewrite prod_map_id_fmap_values.
  exact Hmeta_perm.
Qed.

(* Definition ByIndex_podController_map_list_rel
  (parent_key : KKey.t) (pod_map : gmap KKey.t PodV.t) (pods : list PodV.t) : Prop :=
  (* every pod in the list is valid *)
  (Forall PodV.valid pods) ∧
  (* no dup keys in the list *)
  NoDup (PodV.key <$> pods) ∧
  (* every pod in the list is also in the map *)
  (Forall (λ pod, pod_map !! (PodV.key pod) = Some pod) pods) ∧
  (* every pod in the map is also in the list *)
  map_Forall (λ _ pod, pod ∈ pods) pod_map ∧
  (* every pod in the map has the right key *)
  map_Forall (λ key pod, key = PodV.key pod) pod_map ∧
  (* children keys are the same as the parent key *)
  map_Forall (λ key _, key.(KKey.Namespace') = parent_key.(KKey.Namespace')) pod_map. *)


Lemma wp_State__ByIndex_podController_au γ l indexed_value :
  ∀ Φ,
  ( is_pkg_init apimodel ∗
    is_kubernetes γ l ∗
    |={⊤,∅}=> ∃ meta_map parent_key parent_uid children_keys dq,
      "Hown_meta_frags" ∷ ([∗ map] key ↦ meta ∈ meta_map, own_meta_frag γ key meta.(ObjectMetaV.UID') dq meta) ∗
      "Hown_children_frag" ∷ own_children_frag γ parent_key parent_uid dq children_keys ∗
      "%Hindexed_value_eq" ∷ ⌜ indexed_value = parent_key.(KKey.Namespace') ++ "/"%go ++
        parent_key.(KKey.Kind') ++ "/"%go ++ parent_key.(KKey.Name') ++ "/"%go ++ parent_uid ⌝ ∗
      "%Hdom_eq" ∷ ⌜ dom meta_map = filter (λ key, key.(KKey.Kind') = "Pod"%go) children_keys ⌝ ∗
      "%Hslash_free" ∷ ⌜ slash_free parent_key.(KKey.Kind') ∧ slash_free parent_key.(KKey.Namespace') ∧ slash_free parent_key.(KKey.Name') ∧ slash_free parent_uid ⌝ ∗
      "Hclose" ∷ (∀ sl interfaces pods dq',
        sl ↦* interfaces ∗
        ([∗ list] i;pod ∈ interfaces;pods, KObjectV.deepown_i i (KObjectV.Pod pod) dq') ∗
        ⌜ PodV.ObjectMeta' <$> pods ≡ₚ (map_to_list meta_map).*2 ⌝ ∗
        ([∗ map] key ↦ meta ∈ meta_map, own_meta_frag γ key meta.(ObjectMetaV.UID') dq meta) ∗
        own_children_frag γ parent_key parent_uid dq children_keys
          ={∅,⊤}=∗ ▷ Φ (#sl, #interface.nil)%V
      )
  ) -∗ WP l @ (ptrT.id apimodel.State.id) @ "ByIndex" #"Pod"%go #"podController"%go #indexed_value {{ Φ }}.
Proof.
  iIntros (Φ) "(#? & #Hkinv & Hau)". iNamed "Hau". iNamed "Hkinv".
  wp_method_call. wp_call.
  wp_apply wp_with_defer. iIntros (defer) "Hdefer". simpl subst. wp_auto.
  wp_apply wp_Mutex__Lock; [done|]. iIntros "[Hown_Mutex H]". iNamedPrefix "H" "Hinv_". wp_auto.
  wp_apply (wp_State__objListLocked_Pod_NamespaceAll with "[$Hinv_Hstate_m_addr $Hinv_Hown_phys $Hinv_Hown_abs
    $Hinv_Hphys_abs_rep]").
  iIntros (sl interfaces pods) "(Hsl & Hdeepown_i_interfaces & %Hlist_result & %Hpods_valid & Hinv_Hstate_m_addr &
    Hinv_Hown_phys & Hinv_Hown_abs & Hinv_Hphys_abs_rep)". wp_auto.
  iPoseProof own_slice_nil as "Hslice_nil".
  iPoseProof own_slice_cap_nil as "Hown_slice_nil_cap".
  iDestruct (own_slice_len with "Hsl") as %(Hsl_len1 & Hsl_len2).
  iDestruct (own_slice_wf with "Hsl") as %Hsl_cap.
  iDestruct (big_sepL2_length with "Hdeepown_i_interfaces") as %Hlen_pods.
  set P := (λ pod, podController_indexed_value pod = indexed_value).
  set I := (∃ (i: w64) (val: interface.t) (sl': slice.t) (interfaces': list interface.t) (pods': list PodV.t),
    "Hi_ptr" ∷ i_ptr ↦ i ∗
    "Hval_ptr" ∷ val_ptr ↦ val ∗
    "Hitems_ptr" ∷ items_ptr ↦ sl' ∗
    "Hsl'" ∷ sl' ↦* interfaces' ∗
    "Hlist_pre" ∷ ([∗ list] i;pod ∈ interfaces';pods', KObjectV.deepown_i i (KObjectV.Pod pod) 1) ∗
    "Hlist_post" ∷ ([∗ list] i;pod ∈ (drop (sint.nat i) interfaces);(drop (sint.nat i) pods),
      KObjectV.deepown_i i (KObjectV.Pod pod) 1) ∗
    "Hcap_sl'" :: own_slice_cap interface.t sl' (DfracOwn 1) ∗
    "%Hfilter" ∷ ⌜ pods' = filter P (take (sint.nat i) pods) ⌝ ∗
    "%Hi" ∷ ⌜ 0 ≤ sint.Z i ≤ sint.Z (slice.len_f sl) ⌝
  )%I.
  iAssert (I) with "[i val items Hdeepown_i_interfaces]" as "Hloop_inv".
  { iExists (W64 0), (default_val interface.t), (default_val slice.t), [], [].
    iFrame. iFrame "#". rewrite !big_sepL2_nil. done. }
  wp_for "Hloop_inv". wp_if_destruct.
  - wp_pure; first word.
    list_elem interfaces (sint.Z i) as this_interface.
    wp_apply (wp_load_slice_elem with "[$Hsl]"); [word|eauto| ]. iIntros "Hsl". wp_auto.
    assert (∃ this_pod, pods !! sint.nat i = Some this_pod) as [this_pod Hthis_pod_lookup].
    { apply lookup_lt_is_Some_2. word. }
    iPoseProof (big_sepL2_head_tail _ _ _ this_interface this_pod with "Hlist_post") as "[Hthis_i_pod Hother_i_pod]".
    { split. all: rewrite lookup_drop Nat.add_0_r; done. }
    wp_apply (wp_index_of_podController with "[$Hthis_i_pod]").
    iIntros (sl0) "(Hsl0 & Hthis_i_pod)". wp_auto.
    rewrite bool_decide_true //. wp_auto.
    wp_alloc j_ptr as "Hj_ptr". wp_auto.
    iDestruct (own_slice_len with "Hsl0") as %(Hsl0_len1 & _). simpl in Hsl0_len1.
    set I0 := (∃ (j: w64) (v: go_string) (sl': slice.t),
      "Hj_ptr" ∷ j_ptr ↦ j ∗
      "Hv_ptr" ∷ v_ptr ↦ v ∗
      "Hitems_ptr" ∷ items_ptr ↦ sl' ∗
      "Hsl'" ∷ sl' ↦* interfaces' ∗
      "Hcap_sl'" :: own_slice_cap interface.t sl' (DfracOwn 1) ∗
      "%Hneg_P" ∷ ⌜ sint.Z j = sint.Z (slice.len_f sl0) → ¬ P this_pod ⌝ ∗
      "%Hj" ∷ ⌜ 0 ≤ sint.Z j ≤ sint.Z (slice.len_f sl0) ⌝
    )%I.
    iAssert (I0) with "[Hj_ptr v Hitems_ptr Hsl' Hcap_sl']" as "Hloop_inv0".
    { iExists (W64 0), (default_val go_string), sl'.
      iFrame. iPureIntro. simpl. word. }
    wp_for "Hloop_inv0". wp_if_destruct.
    + wp_pure; first word.
      wp_apply (wp_load_slice_elem with "[$Hsl0]"); [word| | ].
      { iPureIntro. assert (sint.nat j = 0%nat) as -> by word. done. }
      iIntros "Hsl0". wp_auto.
      destruct (bool_decide (podController_indexed_value this_pod = indexed_value)) as [|] eqn:Heq; wp_auto.
      * wp_apply wp_slice_literal. iIntros (sl1) "Hsl1". wp_auto.
        wp_apply (wp_slice_append with "[$Hsl' $Hcap_sl' $Hsl1]").
        iIntros (sl'') "(Hsl'' & Hcap_sl'' & Hsl1)". wp_auto.
        wp_for_post.
        wp_for_post.
        iAssert (I) with "[Hi_ptr Hval_ptr Hitems_ptr Hsl'' Hlist_pre Hthis_i_pod Hother_i_pod Hcap_sl'']" as "Hloop_inv".
        { iExists (word.add i (W64 1)), this_interface, sl'', (interfaces' ++ [this_interface]),
            ((filter P (take (sint.nat i) pods)) ++ [this_pod]).
          iFrame.
          rewrite !big_sepL2_nil.
          assert (sint.nat (word.add i (W64 1)) = S (sint.nat i)) as -> by word.
          rewrite !drop_drop Nat.add_1_r.
          iFrame. iPureIntro. split; [|word].
          rewrite (take_S_r _ _ this_pod Hthis_pod_lookup).
          rewrite list.filter_app. f_equal. unfold filter. simpl.
          destruct (decide (P this_pod)); [done|].
          exfalso. apply n. unfold P. apply bool_decide_eq_true in Heq. done.
        }
        iFrame.
      * wp_for_post.
        iAssert (I0) with "[Hj_ptr Hv_ptr Hitems_ptr Hsl' Hcap_sl']" as "Hloop_inv0".
        { iExists (word.add j (W64 1)), (podController_indexed_value this_pod), sl'0.
          iFrame. iPureIntro. split;[|word]. intros. unfold P. intros Hcontra.
          apply bool_decide_eq_false in Heq. done.
        }
        iFrame.
    + wp_for_post.
      iAssert (I) with "[Hi_ptr Hval_ptr Hitems_ptr Hsl' Hlist_pre Hthis_i_pod Hother_i_pod Hcap_sl']" as "Hloop_inv".
      { iExists (word.add i (W64 1)), this_interface, sl'0, interfaces', (filter P (take (sint.nat i) pods)).
        iFrame.
        assert (sint.nat (word.add i (W64 1)) = S (sint.nat i)) as -> by word.
        rewrite !drop_drop Nat.add_1_r.
        iFrame. iPureIntro. split; [|word].
        rewrite (take_S_r _ _ this_pod Hthis_pod_lookup).
        rewrite list.filter_app. unfold filter. simpl.
        assert (¬ P this_pod) as Hnot_P.
        { apply Hneg_P. word. }
        destruct (decide (P this_pod)); [done|].
        rewrite filter_nil app_nil_r. done.
      }
      iFrame.
  - iApply fupd_wp.
    iMod "Hau" as (meta_map parent_key parent_uid children_keys dq) "H". iNamed "H".
    assert (sint.nat i = length pods) as -> by word.
    rewrite take_ge. 1: done.
    iPoseProof (cview.own_auth_frag_valid with "Hinv_Hown_children Hown_children_frag") as "(-> & %Hin_used_reference)".
    iPoseProof (kview.own_meta_map_exists with "Hinv_Hown_abs Hown_meta_frags") as "(%Hlook_up & %Hin_used_uid)".
    destruct Hslash_free as (Hkind_slash_free & Hns_slash_free & Hname_slash_free & Huid_slash_free).
    unfold P. subst indexed_value.
    rewrite (matching_podController_indexed_value_implies_being_children_pods pods parent_key parent_uid). all: try done.
    set returned_pods := filter (λ pod, obj_parent_ref (KObjectV.Pod pod) = Some (parent_key, parent_uid)) pods.
    iMod ("Hclose" $! sl' interfaces' returned_pods (DfracOwn 1) with "[Hown_meta_frags Hown_children_frag Hsl' Hlist_pre]") as "HΦ".
    { iFrame. iPureIntro. 
      apply (pods_is_permutation_of_meta_map_for_meta pods meta_map abs_state).
      all: done.
    }
    iModIntro.
    iCombineNamed "Hinv_*" as "H".
    wp_apply (wp_Mutex__Unlock _ (kubernetes_inv γ l) with "[$Hown_Mutex H]").
    { iNamed "H". iFrame. iFrame "#". iPureIntro. split_and!. all: done. }
    iApply "HΦ".
Qed.

End proof.
