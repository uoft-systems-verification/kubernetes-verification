From New.proof Require Import prelude empty_ffi.
From New.proof.map Require Import for_range.
From New.proof.kubernetes_model Require Export inv common.

Section proof.
Context `{hG: !heapGS Σ} `{!ffi_semantics _ _}.
Context {sem : go.Semantics} {package_sem : apimodel.Assumptions}.
Context `{!kubernetesModelG Σ}.
Local Set Default Proof Using "All".

Lemma kobject_list_to_pods objs :
  Forall (λ obj, ∃ pod, obj = KObjectV.Pod pod) objs →
  ∃ pods, objs = KObjectV.Pod <$> pods.
Proof.
  induction 1 as [|obj objs [pod ->] _ [pods ->]].
  - exists []. done.
  - exists (pod :: pods). done.
Qed.

Definition processed_map `{Countable K} {A}
    (keys : list K) (i : Z) (m : gmap K A) : gmap K A :=
  filter (λ '(k, _), k ∈ list_to_set (C:=gset K) (take (Z.to_nat i) keys)) m.

Lemma current_key_not_in_take `{EqDecision A} `{Countable A} (keys : list A) i key :
  NoDup keys →
  keys !! Z.to_nat i = Some key →
  (0 ≤ i)%Z →
  key ∉ list_to_set (C:=gset A) (take (Z.to_nat i) keys).
Proof.
  intros Hnodup Hlookup Hi_nonneg Hin.
  rewrite elem_of_list_to_set in Hin.
  apply list_elem_of_lookup_1 in Hin as [j Htake_lookup].
  apply lookup_take_Some in Htake_lookup as [Hlookup_j Hj].
  pose proof (NoDup_lookup _ _ _ _ Hnodup Hlookup_j Hlookup) as ->.
  lia.
Qed.

Lemma processed_map_empty `{Countable K} {A} (keys : list K) (m : gmap K A) :
  processed_map keys 0 m = ∅.
Proof.
  apply map_eq. intros key.
  rewrite /processed_map map_lookup_filter lookup_empty take_0.
  destruct (m !! key); simpl; [|done].
  destruct (decide (key ∈ list_to_set (C:=gset K) [])); [|done].
  rewrite elem_of_list_to_set elem_of_nil in e. done.
Qed.

Lemma processed_map_lookup_not_current `{Countable K} {A}
    (keys : list K) i key (m : gmap K A) :
  NoDup keys →
  keys !! Z.to_nat i = Some key →
  (0 ≤ i)%Z →
  processed_map keys i m !! key = None.
Proof.
  intros Hnodup Hlookup Hi_nonneg.
  rewrite /processed_map. apply map_lookup_filter_None_2. right.
  intros x Hx Hin. simpl in Hin.
  exact ((current_key_not_in_take keys i key Hnodup Hlookup Hi_nonneg) Hin).
Qed.

Lemma processed_map_insert `{Countable K} {A}
    (keys : list K) i key (m : gmap K A) v :
  NoDup keys →
  (0 ≤ i)%Z →
  keys !! Z.to_nat i = Some key →
  m !! key = Some v →
  processed_map keys (i + 1) m = <[key:=v]> (processed_map keys i m).
Proof.
  intros Hnodup Hi_nonneg Hkey_lookup Hm_lookup.
  apply map_eq. intros key'.
  destruct (decide (key' = key)) as [->|Hne].
  - rewrite lookup_insert_eq /processed_map.
    apply map_lookup_filter_Some_2; [done|].
    simpl.
    replace (Z.to_nat (i + 1)) with (S (Z.to_nat i)) by lia.
    rewrite (take_S_r _ _ _ Hkey_lookup).
    rewrite elem_of_list_to_set elem_of_app /=. right. Timeout 10 set_solver.
  - replace (<[key:=v]> (processed_map keys i m) !! key') with
      (processed_map keys i m !! key').
    2:{ symmetry. apply lookup_insert_ne.
        intro Heq. apply Hne. symmetry. exact Heq. }
    assert (Hin_iff : key' ∈ list_to_set (C:=gset K)
        (take (Z.to_nat (i + 1)) keys) ↔
      key' ∈ list_to_set (C:=gset K) (take (Z.to_nat i) keys)).
    { replace (Z.to_nat (i + 1)) with (S (Z.to_nat i)) by lia.
      rewrite (take_S_r _ _ _ Hkey_lookup).
      rewrite !elem_of_list_to_set elem_of_app /= elem_of_cons elem_of_nil.
      split; intros Hin.
      - destruct Hin as [Hin|Hin]; [done|].
        destruct Hin as [Heq|[]]. subst. contradiction.
      - left. done. }
    destruct (m !! key') as [v'|] eqn:Hm_lookup'.
    + destruct (decide (key' ∈ list_to_set (C:=gset K)
        (take (Z.to_nat i) keys))) as [Hin|Hnot].
      * rewrite /processed_map.
        transitivity (Some v').
        -- apply map_lookup_filter_Some_2; [done|].
           simpl. apply Hin_iff. done.
        -- symmetry. apply map_lookup_filter_Some_2; [done|done].
      * rewrite /processed_map.
        transitivity (@None A).
        -- apply map_lookup_filter_None_2. right.
           intros x Hx Hin_succ. simpl in Hin_succ.
           apply Hnot. apply Hin_iff. done.
        -- symmetry. apply map_lookup_filter_None_2. right.
           intros x Hx Hin_old. done.
    + rewrite /processed_map.
      transitivity (@None A).
      * apply map_lookup_filter_None_2. left. done.
      * symmetry. apply map_lookup_filter_None_2. left. done.
Qed.

Lemma processed_map_all `{Countable K} {A} (keys : list K) (m : gmap K A) :
  list_to_set keys = dom m →
  length keys = size m →
  processed_map keys (Z.of_nat (size m)) m = m.
Proof.
  intros Hdom Hlen. apply map_eq. intros key.
  destruct (m !! key) as [v|] eqn:Hlookup.
  - rewrite /processed_map. apply map_lookup_filter_Some_2; [done|].
    simpl. rewrite Nat2Z.id. replace (size m) with (length keys) by done.
    replace (take (length keys) keys) with keys
      by (symmetry; apply take_ge; lia).
    rewrite Hdom elem_of_dom. eexists. exact Hlookup.
  - rewrite /processed_map. apply map_lookup_filter_None_2. left. done.
Qed.

Definition obj_list_match (kind namespace : go_string) (kv : KKey.t * KObjectV.t) : Prop :=
  kv.1.(KKey.Kind') = kind ∧
  v1.namespace_matches #namespace #(kv.1.(KKey.Namespace')).

Lemma filtered_processed_map_insert_true kind namespace keys i key abs_state obj :
  NoDup keys →
  (0 ≤ i)%Z →
  keys !! Z.to_nat i = Some key →
  abs_state !! key = Some obj →
  obj_list_match kind namespace (key, obj) →
  filter (obj_list_match kind namespace) (processed_map keys (i + 1) abs_state) =
    <[key:=obj]> (filter (obj_list_match kind namespace) (processed_map keys i abs_state)).
Proof.
  intros Hnodup Hi Hkey_lookup Hobj_lookup Hmatch.
  rewrite (processed_map_insert keys i key abs_state obj Hnodup Hi Hkey_lookup Hobj_lookup).
  apply map_filter_insert_True. exact Hmatch.
Qed.

Lemma filtered_processed_map_insert_false kind namespace keys i key abs_state obj :
  NoDup keys →
  (0 ≤ i)%Z →
  keys !! Z.to_nat i = Some key →
  abs_state !! key = Some obj →
  ¬ obj_list_match kind namespace (key, obj) →
  filter (obj_list_match kind namespace) (processed_map keys (i + 1) abs_state) =
    filter (obj_list_match kind namespace) (processed_map keys i abs_state).
Proof.
  intros Hnodup Hi Hkey_lookup Hobj_lookup Hnot_match.
  rewrite (processed_map_insert keys i key abs_state obj Hnodup Hi Hkey_lookup Hobj_lookup).
  apply map_filter_insert_not'.
  - exact Hnot_match.
  - intros y Hy. rewrite (processed_map_lookup_not_current keys i key abs_state Hnodup Hkey_lookup Hi) in Hy. done.
Qed.

Lemma filtered_map_values_valid kind namespace
    (abs_state : gmap KKey.t KObjectV.t) (used_uid : gset types.UID.t) :
  (∀ k obj, abs_state !! k = Some obj →
    k = KObjectV.key obj ∧ KObjectV.valid obj ∧
    (KObjectV.objectmeta obj).(ObjectMetaV.UID') ∈ used_uid ∧
    no_speculative_parent_reference (KObjectV.objectmeta obj) used_uid ∧
    map_Forall (λ k' obj',
      (KObjectV.objectmeta obj).(ObjectMetaV.UID') =
        (KObjectV.objectmeta obj').(ObjectMetaV.UID') → k = k') abs_state) →
  Forall KObjectV.valid
    (map_to_list (filter (obj_list_match kind namespace) abs_state)).*2.
Proof.
  intros Hvalid.
  rewrite Forall_forall.
  intros obj Hobj_in.
  rewrite <- list_elem_of_In in Hobj_in.
  apply list_elem_of_fmap_1 in Hobj_in as [[k obj'] [Hobj_eq Hkv_in]].
  simpl in Hobj_eq. subst obj'.
  apply elem_of_map_to_list in Hkv_in.
  apply map_lookup_filter_Some in Hkv_in as [Hlookup _].
  exact (proj1 (proj2 (Hvalid k obj Hlookup))).
Qed.

Lemma filtered_map_values_key_eq kind namespace
    (abs_state : gmap KKey.t KObjectV.t) (used_uid : gset types.UID.t) :
  (∀ k obj, abs_state !! k = Some obj →
    k = KObjectV.key obj ∧ KObjectV.valid obj ∧
    (KObjectV.objectmeta obj).(ObjectMetaV.UID') ∈ used_uid ∧
    no_speculative_parent_reference (KObjectV.objectmeta obj) used_uid ∧
    map_Forall (λ k' obj',
      (KObjectV.objectmeta obj).(ObjectMetaV.UID') =
        (KObjectV.objectmeta obj').(ObjectMetaV.UID') → k = k') abs_state) →
  KObjectV.key <$> (map_to_list (filter (obj_list_match kind namespace) abs_state)).*2 =
    (map_to_list (filter (obj_list_match kind namespace) abs_state)).*1.
Proof.
  intros Hvalid.
  apply list_eq. intros n.
  rewrite list_lookup_fmap.
  destruct ((map_to_list (filter (obj_list_match kind namespace) abs_state)).*2 !! n)
    as [obj|] eqn:Hobj_lookup.
  - apply list_lookup_fmap_Some_1 in Hobj_lookup as [[k obj'] [Hobj_eq Hkv_lookup]].
    simpl in Hobj_eq. subst obj'.
    rewrite list_lookup_fmap Hkv_lookup /=.
    apply list_elem_of_lookup_2 in Hkv_lookup.
    apply elem_of_map_to_list in Hkv_lookup.
    apply map_lookup_filter_Some in Hkv_lookup as [Hlookup _].
    rewrite (proj1 (Hvalid k obj Hlookup)). done.
  - destruct ((map_to_list (filter (obj_list_match kind namespace) abs_state)).*1 !! n)
      as [k|] eqn:Hkey_lookup; [|done].
    apply list_lookup_fmap_Some_1 in Hkey_lookup as [[k' obj'] [Hkey_eq Hkv_lookup]].
    simpl in Hkey_eq. subst k'.
    rewrite list_lookup_fmap Hkv_lookup /= in Hobj_lookup. done.
Qed.

Lemma filtered_map_values_nodup kind namespace
    (abs_state : gmap KKey.t KObjectV.t) (used_uid : gset types.UID.t) :
  (∀ k obj, abs_state !! k = Some obj →
    k = KObjectV.key obj ∧ KObjectV.valid obj ∧
    (KObjectV.objectmeta obj).(ObjectMetaV.UID') ∈ used_uid ∧
    no_speculative_parent_reference (KObjectV.objectmeta obj) used_uid ∧
    map_Forall (λ k' obj',
      (KObjectV.objectmeta obj).(ObjectMetaV.UID') =
        (KObjectV.objectmeta obj').(ObjectMetaV.UID') → k = k') abs_state) →
  NoDup (KObjectV.key <$> (map_to_list (filter (obj_list_match kind namespace) abs_state)).*2).
Proof.
  intros Hvalid.
  rewrite (filtered_map_values_key_eq kind namespace abs_state used_uid Hvalid).
  apply NoDup_fst_map_to_list.
Qed.

Lemma wp_State__objListLocked γ l (kind namespace : go_string) phys_state_l phys_state abs_state used_uid :
  {{{ is_pkg_init apimodel ∗
      "Hstate_m_addr" ∷ l.[(apimodel.State.t), "m"] ↦ phys_state_l ∗
      "Hown_phys" ∷ phys_state_l ↦$ phys_state ∗
      "Hown_abs" ∷ own_kview_auth γ abs_state used_uid ∗
      "Hphys_abs_rep" ∷ ([∗ map] i; obj ∈ phys_state; abs_state,
        match i with
        | interface.ok i_ok => KObjectV.deepown_i i_ok obj 1
        | interface.nil => False%I
        end)
  }}}
    l @! (go.PointerType apimodel.State) @! "objListLocked" #kind #namespace
  {{{ sl interfaces objs, RET #sl;
      sl ↦* (interface.ok <$> interfaces) ∗
      ([∗ list] i;obj ∈ interfaces;objs, KObjectV.deepown_i i obj 1) ∗
      ⌜ objs ≡ₚ (map_to_list (filter
          (λ kv, kv.1.(KKey.Kind') = kind ∧ v1.namespace_matches #namespace #(kv.1.(KKey.Namespace')))
          abs_state)).*2 ⌝ ∗
      ⌜ Forall KObjectV.valid objs ⌝ ∗
      ⌜ NoDup (KObjectV.key <$> objs) ⌝ ∗
      l.[(apimodel.State.t), "m"] ↦ phys_state_l ∗
      phys_state_l ↦$ phys_state ∗
      own_kview_auth γ abs_state used_uid ∗
      ([∗ map] i; obj ∈ phys_state; abs_state,
        match i with
        | interface.ok i_ok => KObjectV.deepown_i i_ok obj 1
        | interface.nil => False%I
        end)
  }}}.
Proof.
  wp_start as "H".
  iNamed "H".
  iPoseProof (kview.own_auth_valid_forall with "Hown_abs")
    as "%Habs_valid".
  wp_auto.
  iPoseProof (own_slice_nil (V:=interface.t)) as "Hslice_nil".
  iPoseProof (own_slice_cap_nil (V:=interface.t)) as "Hcap_nil".
  wp_apply (wp_map_for_range_return_func (key_type:=apimodel.KKey)
    (λ (keys : list KKey.t) i,
      ∃ (last_val : interface.t) (last_key : KKey.t)
        (items_sl : slice.t) (interfaces : list interface.t_ok)
        (objs : list KObjectV.t),
        "val" ∷ val_ptr ↦ last_val ∗
        "key" ∷ key_ptr ↦ last_key ∗
        "items" ∷ items_ptr ↦ items_sl ∗
        "kind" ∷ kind_ptr ↦ kind ∗
        "namespace" ∷ namespace_ptr ↦ namespace ∗
        "Hitems" ∷ items_sl ↦* (interface.ok <$> interfaces) ∗
        "Hitems_cap" ∷ own_slice_cap interface.t items_sl (DfracOwn 1) ∗
        "Hout" ∷ ([∗ list] i; obj ∈ interfaces; objs, KObjectV.deepown_i i obj 1) ∗
        "Hphys_abs_rep" ∷ ([∗ map] i; obj ∈ phys_state; abs_state,
          match i with
          | interface.ok i_ok => KObjectV.deepown_i i_ok obj 1
          | interface.nil => False%I
          end) ∗
        "%Hperm" ∷ ⌜ objs ≡ₚ
          (map_to_list (filter (obj_list_match kind namespace)
            (processed_map keys i abs_state))).*2 ⌝)%I
    with "Hown_phys").
  { done. }
  iIntros (keys) "%Hkeys".
  iSplitL "val key items kind namespace Hslice_nil Hcap_nil Hphys_abs_rep".
  { iExists interface.nil, (zero_val KKey.t), slice.nil, [], [].
    iFrame. rewrite big_sepL2_nil.
    rewrite processed_map_empty map_filter_empty map_to_list_empty.
    iFrame "Hslice_nil Hcap_nil". done. }
  iSplitL "".
  { iModIntro. iIntros (i key phys_obj) "%Hiter Hloop".
    destruct Hkeys as [Hkeys_dom [Hkeys_len Hkeys_nodup]].
    destruct Hiter as [Hi_bounds [Hkey_lookup Hphys_lookup]].
    destruct Hi_bounds as [Hi_nonneg Hi_upper].
    iDestruct "Hloop" as (last_val last_key items_sl interfaces objs)
      "(val & key & items & kind & namespace & Hitems & Hitems_cap & Hout & Hphys_abs_rep & %Hperm)".
    iDestruct (big_sepM2_dom with "Hphys_abs_rep") as %Hdom_eq.
    assert (∃ obj, abs_state !! key = Some obj) as [obj Habs_lookup].
    { apply elem_of_dom. rewrite -Hdom_eq. apply elem_of_dom. eexists. done. }
    iDestruct (big_sepM2_lookup_acc _ _ _ key phys_obj obj
      Hphys_lookup Habs_lookup with "Hphys_abs_rep") as "[Hdeepown_i Hphys_abs_rep_close]".
    destruct phys_obj as [i_ok|].
    2:{ simpl. iDestruct "Hdeepown_i" as %[]. }
    wp_pures.
    simpl subst'.
    wp_auto.
    destruct (bool_decide (kind = key.(KKey.Kind'))) eqn:Hkind_dec; wp_auto.
    - destruct (bool_decide (namespace = ""%go)) eqn:Hnamespace_all; wp_auto.
      + assert (obj_list_match kind namespace (key, obj)) as Hmatch.
        { split.
          - apply bool_decide_eq_true in Hkind_dec. done.
          - unfold v1.namespace_matches.
            apply bool_decide_eq_true in Hnamespace_all. left. subst. done. }
        wp_apply (wp_deepCopy with "[$Hdeepown_i]").
        iIntros (i_copy) "[Hdeepown_copy Hdeepown_i]". wp_auto.
        wp_apply (wp_slice_literal (V:=interface.t) (t:=go.InterfaceType [])).
        iSplitR; first done.
        iIntros (sl_one) "[Hsl_one _]". wp_auto.
        wp_apply (wp_slice_append with "[$Hitems $Hitems_cap $Hsl_one]").
        iIntros (items_sl') "(Hitems & Hitems_cap & Hsl_one)". wp_auto.
        assert (Hsingle :
          <[sint.nat (W64 0):=interface.ok i_copy]> [interface.nil] =
          [interface.ok i_copy]).
        { replace (sint.nat (W64 0)) with 0%nat by word. done. }
        iEval (rewrite Hsingle) in "Hitems".
        iDestruct ("Hphys_abs_rep_close" with "Hdeepown_i") as "Hphys_abs_rep".
        iRight. iSplit; [done|].
        iExists (interface.ok i_ok), key, items_sl', (interfaces ++ [i_copy]), (objs ++ [obj]).
        rewrite fmap_app /=.
        iFrame "val key items kind namespace Hitems Hitems_cap Hphys_abs_rep".
        iSplitL "Hout Hdeepown_copy".
        { iApply (big_sepL2_app with "[$Hout]"). iFrame. done. }
        iPureIntro.
        assert (Hfiltered_insert :
          filter (obj_list_match kind namespace) (processed_map keys (i + 1) abs_state) =
            <[key:=obj]> (filter (obj_list_match kind namespace) (processed_map keys i abs_state))).
        { apply filtered_processed_map_insert_true; done. }
        rewrite Hfiltered_insert.
        assert (Hfiltered_old_lookup :
          filter (obj_list_match kind namespace) (processed_map keys i abs_state) !! key = None).
        { apply map_lookup_filter_None_2. left.
          apply processed_map_lookup_not_current; done. }
        pose proof (map_to_list_insert
          (filter (obj_list_match kind namespace) (processed_map keys i abs_state))
          key obj Hfiltered_old_lookup) as Hinsert_perm.
        eapply Permutation_trans.
        * apply Permutation_app; [exact Hperm|done].
        * etrans.
          -- symmetry. apply Permutation_middle.
          -- rewrite app_nil_r.
             change (((key, obj) :: map_to_list
                (filter (obj_list_match kind namespace) (processed_map keys i abs_state))).*2
              ≡ₚ (map_to_list
                (<[key:=obj]> (filter (obj_list_match kind namespace)
                  (processed_map keys i abs_state)))).*2).
             symmetry. apply Permutation_map. exact Hinsert_perm.
      + destruct (bool_decide (namespace = key.(KKey.Namespace'))) eqn:Hnamespace_eq; wp_auto.
        * assert (obj_list_match kind namespace (key, obj)) as Hmatch.
          { split.
            - apply bool_decide_eq_true in Hkind_dec. done.
            - unfold v1.namespace_matches.
              apply bool_decide_eq_true in Hnamespace_eq. right. subst. done. }
          wp_apply (wp_deepCopy with "[$Hdeepown_i]").
          iIntros (i_copy) "[Hdeepown_copy Hdeepown_i]". wp_auto.
          wp_apply (wp_slice_literal (V:=interface.t) (t:=go.InterfaceType [])).
          iSplitR; first done.
          iIntros (sl_one) "[Hsl_one _]". wp_auto.
          wp_apply (wp_slice_append with "[$Hitems $Hitems_cap $Hsl_one]").
          iIntros (items_sl') "(Hitems & Hitems_cap & Hsl_one)". wp_auto.
          assert (Hsingle :
            <[sint.nat (W64 0):=interface.ok i_copy]> [interface.nil] =
            [interface.ok i_copy]).
          { replace (sint.nat (W64 0)) with 0%nat by word. done. }
          iEval (rewrite Hsingle) in "Hitems".
          iDestruct ("Hphys_abs_rep_close" with "Hdeepown_i") as "Hphys_abs_rep".
          iRight. iSplit; [done|].
          iExists (interface.ok i_ok), key, items_sl', (interfaces ++ [i_copy]), (objs ++ [obj]).
          rewrite fmap_app /=.
          iFrame "val key items kind namespace Hitems Hitems_cap Hphys_abs_rep".
          iSplitL "Hout Hdeepown_copy".
          { iApply (big_sepL2_app with "[$Hout]"). iFrame. done. }
          iPureIntro.
          assert (Hfiltered_insert :
            filter (obj_list_match kind namespace) (processed_map keys (i + 1) abs_state) =
              <[key:=obj]> (filter (obj_list_match kind namespace) (processed_map keys i abs_state))).
          { apply filtered_processed_map_insert_true; done. }
          rewrite Hfiltered_insert.
          assert (Hfiltered_old_lookup :
            filter (obj_list_match kind namespace) (processed_map keys i abs_state) !! key = None).
          { apply map_lookup_filter_None_2. left.
            apply processed_map_lookup_not_current; done. }
          pose proof (map_to_list_insert
            (filter (obj_list_match kind namespace) (processed_map keys i abs_state))
            key obj Hfiltered_old_lookup) as Hinsert_perm.
          eapply Permutation_trans.
          -- apply Permutation_app; [exact Hperm|done].
          -- etrans.
             ++ symmetry. apply Permutation_middle.
             ++ rewrite app_nil_r.
                change (((key, obj) :: map_to_list
                  (filter (obj_list_match kind namespace) (processed_map keys i abs_state))).*2
                ≡ₚ (map_to_list
                  (<[key:=obj]> (filter (obj_list_match kind namespace)
                    (processed_map keys i abs_state)))).*2).
                symmetry. apply Permutation_map. exact Hinsert_perm.
        * assert (¬ obj_list_match kind namespace (key, obj)) as Hnot_match.
          { intros [_ Hns_match].
            unfold v1.namespace_matches in Hns_match.
            destruct Hns_match as [Hall'|Hns'].
            - apply bool_decide_eq_false in Hnamespace_all. apply Hnamespace_all.
              apply go.into_val_inj. rewrite Hall'. done.
            - apply bool_decide_eq_false in Hnamespace_eq. apply Hnamespace_eq.
              apply go.into_val_inj. exact Hns'. }
          iDestruct ("Hphys_abs_rep_close" with "Hdeepown_i") as "Hphys_abs_rep".
          iRight. iSplit; [done|].
          iExists (interface.ok i_ok), key, items_sl, interfaces, objs.
          iFrame. iPureIntro.
          rewrite (filtered_processed_map_insert_false kind namespace keys i key abs_state obj
            Hkeys_nodup Hi_nonneg Hkey_lookup Habs_lookup Hnot_match). done.
    - assert (¬ obj_list_match kind namespace (key, obj)) as Hnot_match.
      { intros [Hkind _].
        apply bool_decide_eq_false in Hkind_dec. done. }
      iDestruct ("Hphys_abs_rep_close" with "Hdeepown_i") as "Hphys_abs_rep".
      iRight. iSplit; [done|].
      iExists (interface.ok i_ok), key, items_sl, interfaces, objs.
      iFrame. iPureIntro.
      rewrite (filtered_processed_map_insert_false kind namespace keys i key abs_state obj
        Hkeys_nodup Hi_nonneg Hkey_lookup Habs_lookup Hnot_match). done. }
  iIntros "Hown_phys Hloop".
  iDestruct "Hloop" as (last_val last_key items_sl interfaces objs)
    "(val & key & items & kind & namespace & Hitems & Hitems_cap & Hout & Hphys_abs_rep & %Hperm)".
  destruct Hkeys as [Hkeys_dom [Hkeys_len Hkeys_nodup]].
  iDestruct (big_sepM2_dom with "Hphys_abs_rep") as %Hdom_eq.
  assert (Hkeys_dom_abs : list_to_set keys = dom abs_state).
  { rewrite Hkeys_dom Hdom_eq. done. }
  assert (Hkeys_len_abs : length keys = size abs_state).
  { rewrite Hkeys_len -(size_dom phys_state) Hdom_eq size_dom. done. }
  assert (Hsize_eq : size phys_state = size abs_state).
  { rewrite -(size_dom phys_state) Hdom_eq size_dom. done. }
  rewrite Hsize_eq in Hperm.
  rewrite (processed_map_all keys abs_state Hkeys_dom_abs Hkeys_len_abs) in Hperm.
  wp_auto.
  iApply ("HΦ" $! items_sl interfaces objs). iFrame.
  iPureIntro. split_and!.
  - exact Hperm.
  - eapply Permutation_Forall; [symmetry; exact Hperm|].
    exact (filtered_map_values_valid kind namespace abs_state used_uid Habs_valid).
  - rewrite (list_fmap_map KObjectV.key objs).
    rewrite (Permutation_map KObjectV.key Hperm).
    rewrite -(list_fmap_map KObjectV.key
      (map_to_list (filter (obj_list_match kind namespace) abs_state)).*2).
    exact (filtered_map_values_nodup kind namespace abs_state used_uid Habs_valid).
Qed.

Lemma wp_State__objListLocked_Pod γ l (namespace : go_string) phys_state_l phys_state abs_state used_uid :
  {{{ is_pkg_init apimodel ∗
      "Hstate_m_addr" ∷ l.[(apimodel.State.t), "m"] ↦ phys_state_l ∗
      "Hown_phys" ∷ phys_state_l ↦$ phys_state ∗
      "Hown_abs" ∷ own_kview_auth γ abs_state used_uid ∗
      "Hphys_abs_rep" ∷ ([∗ map] i; obj ∈ phys_state; abs_state,
        match i with
        | interface.ok i_ok => KObjectV.deepown_i i_ok obj 1
        | interface.nil => False%I
        end)
  }}}
    l @! (go.PointerType apimodel.State) @! "objListLocked" #"Pod"%go #namespace
  {{{ sl interfaces pods, RET #sl;
      sl ↦* (interface.ok <$> interfaces) ∗
      ([∗ list] i;pod ∈ interfaces;pods, KObjectV.deepown_i i (KObjectV.Pod pod) 1) ∗
      ⌜ KObjectV.Pod <$> pods ≡ₚ (map_to_list (filter
          (λ kv, kv.1.(KKey.Kind') = "Pod"%go ∧ v1.namespace_matches #namespace #(kv.1.(KKey.Namespace')))
          abs_state)).*2 ⌝ ∗
      ⌜ Forall PodV.valid pods ⌝ ∗
      ⌜ NoDup (PodV.key <$> pods) ⌝ ∗
      l.[(apimodel.State.t), "m"] ↦ phys_state_l ∗
      phys_state_l ↦$ phys_state ∗
      own_kview_auth γ abs_state used_uid ∗
      ([∗ map] i; obj ∈ phys_state; abs_state,
        match i with
        | interface.ok i_ok => KObjectV.deepown_i i_ok obj 1
        | interface.nil => False%I
        end)
  }}}.
Proof.
  iIntros (Φ) "(#Hinit & Hstate_m_addr & Hown_phys & Hown_abs & Hphys_abs_rep) HΦ".
  wp_apply (wp_State__objListLocked with "[$Hstate_m_addr $Hown_phys $Hown_abs $Hphys_abs_rep]").
  iIntros (sl interfaces objs)
    "(Hsl & Hlist & %Hperm & %Hvalid & %Hnodup & Hstate_m_addr & Hown_phys & Hown_abs & Hphys_abs_rep)".
  iPoseProof (kview.own_auth_valid_forall with "Hown_abs")
    as "%Habs_valid".
  assert (Forall (λ obj, ∃ pod, obj = KObjectV.Pod pod) objs) as Hobjs_are_pods.
  { rewrite Forall_forall.
    intros obj Hobj_in.
    rewrite Hperm in Hobj_in.
    rewrite <- list_elem_of_In in Hobj_in.
    apply list_elem_of_fmap_1 in Hobj_in as [[key obj'] [Hobj_eq Hin]].
    simpl in Hobj_eq. subst obj'.
    apply elem_of_map_to_list in Hin.
    apply map_lookup_filter_Some in Hin as [Hlookup_abs [Hkind _]].
    pose proof (Habs_valid key obj Hlookup_abs) as [Hkey_eq _].
    destruct obj as [pod|rs|pvc|sts].
    - eexists. done.
    - exfalso. subst key. simpl in Hkind. done.
    - exfalso. subst key. simpl in Hkind. done.
    - exfalso. subst key. simpl in Hkind. done.
  }
  destruct (kobject_list_to_pods _ Hobjs_are_pods) as [pods ->].
  iEval (rewrite big_sepL2_fmap_r) in "Hlist".
  iApply "HΦ". iFrame.
  iPureIntro. split_and!.
  - exact Hperm.
  - rewrite Forall_fmap in Hvalid.
    rewrite Forall_forall in Hvalid.
    apply Forall_forall.
    intros pod Hpod_in.
    specialize (Hvalid pod Hpod_in).
    change (KObjectV.valid2 (KObjectV.Pod pod)).
    rewrite -KObjectV.valid_eq_valid2. exact Hvalid.
  - assert (KObjectV.key <$> (KObjectV.Pod <$> pods) = PodV.key <$> pods) as Hkeys_eq.
    { rewrite -list_fmap_compose.
      apply list_fmap_ext. intros i pod Hlookup.
      unfold compose, KObjectV.key, PodV.key, KObjectV.kind, PodV.kind. done. }
    rewrite Hkeys_eq in Hnodup. exact Hnodup.
Qed.

Lemma wp_State__objListLocked_Pod_NamespaceAll γ l phys_state_l phys_state abs_state used_uid :
  {{{ is_pkg_init apimodel ∗
      "Hstate_m_addr" ∷ l.[(apimodel.State.t), "m"] ↦ phys_state_l ∗
      "Hown_phys" ∷ phys_state_l ↦$ phys_state ∗
      "Hown_abs" ∷ own_kview_auth γ abs_state used_uid ∗
      "Hphys_abs_rep" ∷ ([∗ map] i; obj ∈ phys_state; abs_state,
        match i with
        | interface.ok i_ok => KObjectV.deepown_i i_ok obj 1
        | interface.nil => False%I
        end)
  }}}
    l @! (go.PointerType apimodel.State) @! "objListLocked" #"Pod"%go #""%go
  {{{ sl interfaces pods, RET #sl;
      sl ↦* (interface.ok <$> interfaces) ∗
      ([∗ list] i;pod ∈ interfaces;pods, KObjectV.deepown_i i (KObjectV.Pod pod) 1) ∗
      ⌜ KObjectV.Pod <$> pods ≡ₚ (map_to_list (filter (λ kv, kv.1.(KKey.Kind') = "Pod"%go) abs_state)).*2 ⌝ ∗
      ⌜ Forall PodV.valid pods ⌝ ∗
      ⌜ NoDup (PodV.key <$> pods) ⌝ ∗
      l.[(apimodel.State.t), "m"] ↦ phys_state_l ∗
      phys_state_l ↦$ phys_state ∗
      own_kview_auth γ abs_state used_uid ∗
      ([∗ map] i; obj ∈ phys_state; abs_state,
        match i with
        | interface.ok i_ok => KObjectV.deepown_i i_ok obj 1
        | interface.nil => False%I
        end)
  }}}.
Proof.
  iIntros (Φ) "(#Hinit & Hstate_m_addr & Hown_phys & Hown_abs & Hphys_abs_rep) HΦ".
  wp_apply (wp_State__objListLocked_Pod with "[$Hstate_m_addr $Hown_phys $Hown_abs $Hphys_abs_rep]").
  iIntros (sl interfaces pods)
    "(Hsl & Hlist & %Hperm & %Hpods_valid & Hstate_m_addr & Hown_phys & Hown_abs & Hphys_abs_rep)".
  iApply "HΦ". iFrame.
  iPureIntro.
  assert (filter
    (λ kv, kv.1.(KKey.Kind') = "Pod"%go ∧
      v1.namespace_matches v1.NamespaceAll #(kv.1.(KKey.Namespace'))) abs_state =
    filter (λ kv, kv.1.(KKey.Kind') = "Pod"%go) abs_state) as Hfilter_eq.
  { apply map_eq. intros k.
    destruct (abs_state !! k) as [obj|] eqn:Hlookup.
    - destruct (decide (k.(KKey.Kind') = "Pod"%go)) as [Hkind|Hkind].
      + transitivity (Some obj).
        * apply map_lookup_filter_Some_2; [done|].
          split; [done|left; done].
        * symmetry. apply map_lookup_filter_Some_2; [done|].
          done.
      + transitivity (@None KObjectV.t).
        * apply map_lookup_filter_None_2. right.
          intros x Hlookup' [Hkind' _].
          apply Hkind. exact Hkind'.
        * symmetry. apply map_lookup_filter_None_2. right.
          intros x Hlookup' Hpred.
          apply Hkind. exact Hpred.
    - transitivity (@None KObjectV.t).
      + apply map_lookup_filter_None_2. left. done.
      + symmetry. apply map_lookup_filter_None_2. left. done.
  }
  rewrite Hfilter_eq in Hperm.
  split; [exact Hperm|exact Hpods_valid].
Qed.

End proof.
