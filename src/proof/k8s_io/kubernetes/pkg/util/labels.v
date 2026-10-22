From New.proof Require Import prelude empty_ffi.
From New.proof.map Require Import for_range.
From New.object_specs Require Export labelselector.
From New.proof.k8s_io.kubernetes.pkg.util Require Export labels_init.

Section proof.
Context `{hG: !heapGS Σ} `{!ffi_semantics _ _}.
Context {sem : go.Semantics}
  {package_sem : labels.Assumptions}
  {labels_meta_v1_sem : code.k8s_io.apimachinery.pkg.apis.meta.v1.v1.Assumptions}.
Collection W := sem + package_sem.
Local Set Default Proof Using "All".

(* As in controller.v, take the meta v1 assumptions as a separate variable so
   callers' instances are used for LabelSelector ownership. *)
#[local] Existing Instance labels_meta_v1_sem.

(* Ownership of a possibly-nil map[string]string argument.  ObjectMetaV models
   an absent label/annotation map as None, and Go ranges over a nil map without
   faulting, so CloneAndAddLabel must accept both. *)
Definition labels_opt_own (l : loc)
    (m_o : option (gmap go_string go_string)) dq : iProp Σ :=
  match m_o with
  | Some m => l ↦${dq} m
  | None => ⌜ l = null ⌝
  end.

(* CloneAndAddLabel returns a fresh map holding [existing] plus one binding.
   [existing] is only read, and a nil map ranges as empty, hence [default ∅].
   The result is fully owned: it is a map literal the callee just built. With an
   empty key it would return [existing] itself instead; the only caller passes
   the non-empty pod-template-hash key, so the spec rules that case out. *)
Lemma wp_CloneAndAddLabel existing_l (existing : option (gmap go_string go_string))
    (key value : go_string) dq :
  {{{ is_pkg_init labels ∗
      "Hexisting" ∷ labels_opt_own existing_l existing dq ∗
      "%Hkey" ∷ ⌜ key ≠ ""%go ⌝
  }}}
    @! labels.CloneAndAddLabel #existing_l #key #value
  {{{ (result_l : loc), RET #result_l;
      labels_opt_own existing_l existing dq ∗
      result_l ↦$ (<[key := value]> (default ∅ existing))
  }}}.
Proof.
  wp_start as "H". iNamed "H". wp_auto.
  rewrite bool_decide_eq_false_2 //. wp_auto.
  wp_apply wp_map_make1. iIntros (result_l) "Hresult".
  wp_auto.
  destruct existing as [m|].
  - (* The copy loop fills [result] with the map_prefix of the keys seen so far. *)
    wp_apply (wp_map_for_range_return_func (key_type:=go.string)
      (λ (keys : list go_string) i,
        ∃ (last_value last_key : go_string),
          "value" ∷ value_ptr ↦ last_value ∗
          "key" ∷ key_ptr ↦ last_key ∗
          "newLabels" ∷ newLabels_ptr ↦ result_l ∗
          "Hresult" ∷ result_l ↦$ map_prefix keys i m)%I
      with "Hexisting").
    { done. }
    iIntros (keys) "%Hkeys".
    iSplitL "value key newLabels Hresult".
    { iExists ""%go, ""%go. iFrame. rewrite map_prefix_empty. iFrame. }
    iSplitL "".
    { iModIntro. iIntros (i k0 v0) "%Hiter Hloop".
      destruct Hkeys as [Hkeys_dom [Hkeys_len Hkeys_nodup]].
      destruct Hiter as [Hi_bounds [Hkey_lookup Hvalue_lookup]].
      destruct Hi_bounds as [Hi_nonneg Hi_upper].
      iDestruct "Hloop" as (last_value last_key) "(value & key & newLabels & Hresult)".
      wp_pures. simpl subst'. wp_auto.
      wp_apply (wp_map_insert (K:=go_string) (V:=go_string)
        go.string result_l (map_prefix keys i m) k0 v0 with "Hresult") as "Hresult".
      iRight. iSplit; [done|].
      iExists v0, k0. iFrame.
      rewrite -map_prefix_insert; done. }
    iIntros "Hexisting Hloop".
    iDestruct "Hloop" as (last_value last_key) "(value & key & newLabels & Hresult)".
    destruct Hkeys as [Hkeys_dom [Hkeys_len Hkeys_nodup]].
    rewrite (map_prefix_all keys m Hkeys_dom Hkeys_len).
    wp_auto.
    wp_apply (wp_map_insert (K:=go_string) (V:=go_string)
      go.string result_l m key value with "Hresult") as "Hresult".
    iApply ("HΦ" $! result_l). iFrame.
  - (* A nil source map ranges zero times, leaving [result] empty. *)
    iDestruct "Hexisting" as %->.
    wp_apply (wp_map_for_range_nil go.string go.string).
    wp_apply (wp_map_insert (K:=go_string) (V:=go_string)
      go.string result_l ∅ key value with "Hresult") as "Hresult".
    iApply ("HΦ" $! result_l). iFrame. done.
Qed.

(* CloneSelectorAndAddLabel returns a copy of [selector] whose MatchLabels are
   [selector]'s plus one binding. MatchLabels is always freshly made, so it is
   always Some. *)
Definition selector_with_label (selector : LabelSelectorV.t)
    (key value : go_string) : LabelSelectorV.t :=
  LabelSelectorV.mk
    (Some (<[key := value]>
      (default ∅ selector.(LabelSelectorV.MatchLabels'))))
    selector.(LabelSelectorV.MatchExpressions').

(* Identify nil and non-nil empty slices, which the LabelSelector model already
   treats as the same semantic value (see [LabelSelectorV.match_expressions_list]
   and [LabelSelectorRequirementV.values_list]). CloneSelectorAndAddLabel copies
   slices with [make(T, len)], and Perennial does not fix whether a
   zero-length [make] is nil, so its result is determined only up to this. *)
Definition requirement_norm (r : LabelSelectorRequirementV.t) :
    LabelSelectorRequirementV.t :=
  LabelSelectorRequirementV.mk r.(LabelSelectorRequirementV.Key')
    r.(LabelSelectorRequirementV.Operator')
    (match r.(LabelSelectorRequirementV.Values') with
     | Some [] => None
     | values => values
     end).

Definition selector_norm (selector : LabelSelectorV.t) : LabelSelectorV.t :=
  LabelSelectorV.mk selector.(LabelSelectorV.MatchLabels')
    (match selector.(LabelSelectorV.MatchExpressions') with
     | Some [] | None => None
     | Some es => Some (requirement_norm <$> es)
     end).

(* CloneSelectorAndAddLabel copies [selector] field by field and adds one
   MatchLabels binding. The source is only read, and the result is freshly
   owned. With an empty key it would return [selector] itself; callers pass a
   non-empty key, so the spec rules that case out. *)
Lemma wp_CloneSelectorAndAddLabel selector_l (selector : LabelSelectorV.t)
    (key value : go_string) dq :
  {{{ is_pkg_init labels ∗
      "Hselector" ∷ LabelSelectorV.deepown_l selector_l selector dq ∗
      "%Hkey" ∷ ⌜ key ≠ ""%go ⌝
  }}}
    @! labels.CloneSelectorAndAddLabel #selector_l #key #value
  {{{ (result_l : loc) (result : LabelSelectorV.t), RET #result_l;
      LabelSelectorV.deepown_l selector_l selector dq ∗
      LabelSelectorV.deepown_l result_l result 1 ∗
      ⌜ selector_norm result = selector_norm (selector_with_label selector key value) ⌝
  }}}.
Proof.
  wp_start as "H". iNamed "H". wp_auto.
  rewrite bool_decide_eq_false_2 //. wp_auto.
  wp_alloc new_l as "Hnew". wp_auto.
  iDestruct (struct_fields_split (V:=v1.LabelSelector.t) with "Hnew") as "[Hnew %Hnew_nn]".
  iNamedPrefix "Hnew" "Hnew_".
  iDestruct "Hselector" as (sel_c) "[Hsel_l Hsel]".
  iDestruct (struct_fields_split (V:=v1.LabelSelector.t) with "Hsel_l") as "[Hsel_l %Hsel_nn]".
  iNamedPrefix "Hsel_l" "Hself_".
  iNamedPrefix "Hsel" "Hsel_".
  wp_apply wp_map_make1. iIntros (ml_l) "Hml". wp_auto.
  (* Copy MatchLabels. Afterwards both cases hold the same resources: the new
     map with the extra binding, and the source map given back. *)
  iAssert (∀ Ψ, (ml_l ↦$ (default ∅ selector.(LabelSelectorV.MatchLabels')) -∗
      "Hsel_Hdeepown_matchlabels_some" ∷ (match selector.(LabelSelectorV.MatchLabels') with
        | Some match_labels => ∃ match_labels_c,
            v1.LabelSelector.MatchLabels' sel_c ↦${dq} match_labels_c ∗
            ⌜match_labels_c = match_labels⌝
        | None => True end) -∗
      "newSelector" ∷ newSelector_ptr ↦ new_l -∗
      "Hnew_MatchLabels" ∷ new_l.[v1.LabelSelector.t, "MatchLabels"] ↦ ml_l -∗
      "selector" ∷ selector_ptr ↦ selector_l -∗
      "Hself_MatchLabels" ∷ selector_l.[v1.LabelSelector.t, "MatchLabels"] ↦{dq}
        v1.LabelSelector.MatchLabels' sel_c -∗ Ψ execute_val) -∗
    WP (if: # (negb (bool_decide (v1.LabelSelector.MatchLabels' sel_c = map.nil)))
       then let: "$range" := ![go.MapType go.string go.string]
                             (StructFieldRef v1.LabelSelector "MatchLabels"
                                ![go.PointerType v1.LabelSelector] (# selector_ptr)) in
            let: "val" := GoAlloc go.string (GoZeroVal go.string (# ())) in
            let: "key" := GoAlloc go.string (GoZeroVal go.string (# ())) in
            map.for_range go.string go.string "$range"
              (λ: "$key" "$value",
                 (do: "val" <-[go.string] "$value") ;;;
                 (do: "key" <-[go.string] "$key") ;;;
                 let: "$r0" := ![go.string] "val" in
                 do: map.insert go.string
                       ![go.MapType go.string go.string]
                       (StructFieldRef v1.LabelSelector "MatchLabels"
                          ![go.PointerType v1.LabelSelector] (# newSelector_ptr))
                       ![go.string] "key" "$r0")
       else do: # ())%E {{ Ψ }})%I
    with "[Hml Hsel_Hdeepown_matchlabels_some newSelector Hnew_MatchLabels selector Hself_MatchLabels]"
    as "Hcopy_labels".
  { iIntros (Ψ) "HΨ".
    destruct selector.(LabelSelectorV.MatchLabels') as [m|] eqn:Hml.
    - iDestruct "Hsel_Hdeepown_matchlabels_some" as (mc) "[Hsel_ml ->]".
      assert (v1.LabelSelector.MatchLabels' sel_c ≠ null) as Hml_nn.
      { intros Hn. apply Hsel_Hdeepown_matchlabels_none in Hn. congruence. }
      rewrite (bool_decide_eq_false_2 _ Hml_nn). wp_auto.
      wp_apply (wp_map_for_range_return_func (key_type:=go.string)
        (λ (keys : list go_string) i,
          ∃ (last_value last_key : go_string),
            "val" ∷ val_ptr ↦ last_value ∗
            "key" ∷ key_ptr ↦ last_key ∗
            "newSelector" ∷ newSelector_ptr ↦ new_l ∗
            "Hnew_MatchLabels" ∷ new_l.[v1.LabelSelector.t, "MatchLabels"] ↦ ml_l ∗
            "Hml" ∷ ml_l ↦$ map_prefix keys i m)%I
        with "Hsel_ml").
      { done. }
      iIntros (keys) "%Hkeys".
      iSplitL "val key newSelector Hnew_MatchLabels Hml".
      { iExists ""%go, ""%go. iFrame. rewrite map_prefix_empty. iFrame. }
      iSplitL "".
      { iModIntro. iIntros (i k0 v0) "%Hiter Hloop".
        destruct Hkeys as [Hkeys_dom [Hkeys_len Hkeys_nodup]].
        destruct Hiter as [Hi_bounds [Hkey_lookup Hvalue_lookup]].
        iDestruct "Hloop" as (last_value last_key) "(val & key & newSelector & Hnew_MatchLabels & Hml)".
        wp_pures. simpl subst'. wp_auto.
        wp_apply (wp_map_insert (K:=go_string) (V:=go_string)
          go.string ml_l (map_prefix keys i m) k0 v0 with "Hml") as "Hml".
        iRight. iSplit; [done|].
        iExists v0, k0. iFrame.
        rewrite -(map_prefix_insert keys i k0 m v0); [lia|done|done|iFrame]. }
      iIntros "Hsel_ml Hloop".
      iDestruct "Hloop" as (last_value last_key) "(val & key & newSelector & Hnew_MatchLabels & Hml)".
      destruct Hkeys as [Hkeys_dom [Hkeys_len Hkeys_nodup]].
      rewrite (map_prefix_all keys m Hkeys_dom Hkeys_len).
      iApply ("HΨ" with "[$Hml] [Hsel_ml] [$] [$] [$] [$]").
      iExists m. iFrame. done.
    - assert (v1.LabelSelector.MatchLabels' sel_c = null) as Hml_null.
      { apply Hsel_Hdeepown_matchlabels_none. done. }
      rewrite (bool_decide_eq_true_2 _ Hml_null). wp_auto.
      iApply ("HΨ" with "[$Hml] [//] [$] [$] [$] [$]"). }
  wp_bind (If _ _ _). iApply "Hcopy_labels".
  iIntros "Hml Hsel_Hdeepown_matchlabels_some newSelector Hnew_MatchLabels selector Hself_MatchLabels".
  wp_auto.
  wp_apply (wp_map_insert (K:=go_string) (V:=go_string) go.string ml_l _ key value
    with "Hml") as "Hml".
  iDestruct (own_map_not_nil with "Hml") as %Hml_l_nn.
  iDestruct "Hsel_Hdeepown_matchexpressions" as
    "(%Hsel_Hdeepown_matchexpressions_none & %es_c &
      Hes_sl & Hsel_Hdeepown_matchexpressions_cap & Hes)".
  destruct selector.(LabelSelectorV.MatchExpressions') as [es|] eqn:Hes.
  - assert (v1.LabelSelector.MatchExpressions' sel_c ≠ slice.nil) as Hes_nn.
    { intros Hn. apply Hsel_Hdeepown_matchexpressions_none in Hn. congruence. }
    iDestruct (own_slice_len with "Hes_sl") as %[Hes_len Hes_len_nn].
    iDestruct (big_sepL2_length with "Hes") as %Hes_models_len.
    rewrite (bool_decide_eq_false_2 _ Hes_nn). wp_auto.
    wp_apply (wp_slice_make2 (V:=v1.LabelSelectorRequirement.t)); first word.
    iIntros (new_sl) "[Hnew_sl Hnew_cap]".
    iDestruct (own_slice_len with "Hnew_sl") as %[Hnew_sl_len _].
    rewrite length_replicate in Hnew_sl_len.
    wp_auto.
    (* The range loop's own index shares the name "i" with the Go loop
       variable, so wp_auto does not allocate it. *)
    wp_alloc i_ptr0 as "i0". wp_auto.
    set n := slice.len (v1.LabelSelector.MatchExpressions' sel_c).
    (* The first j entries of the new slice are copies of the first j
       requirements, equal up to nil versus empty slices; the rest are still
       zero. *)
    set I := (∃ (j : w64) (me_v : v1.LabelSelectorRequirement.t) (i_v : w64)
        (new_cs : list v1.LabelSelectorRequirement.t)
        (new_rs : list LabelSelectorRequirementV.t),
      "i0" ∷ i_ptr0 ↦ j ∗
      "me" ∷ me_ptr ↦ me_v ∗
      "i" ∷ i_ptr ↦ i_v ∗
      "newMExps" ∷ newMExps_ptr ↦ new_sl ∗
      "Hnew_sl" ∷ new_sl ↦* (new_cs ++
        replicate (sint.nat n - sint.nat j) (zero_val v1.LabelSelectorRequirement.t)) ∗
      "Hnew_rs" ∷ ([∗ list] c;v ∈ new_cs;new_rs,
        LabelSelectorRequirementV.deepown c v (DfracOwn 1)) ∗
      "Hes_sl" ∷ v1.LabelSelector.MatchExpressions' sel_c ↦*{dq} es_c ∗
      "Hes" ∷ ([∗ list] c;v ∈ es_c;es, LabelSelectorRequirementV.deepown c v dq) ∗
      "%Hnew_len" ∷ ⌜ length new_cs = sint.nat j ⌝ ∗
      "%Hnew_norm" ∷ ⌜ requirement_norm <$> new_rs =
        requirement_norm <$> take (sint.nat j) es ⌝ ∗
      "%Hj" ∷ ⌜ 0 ≤ sint.Z j ≤ sint.Z n ⌝)%I.
    iAssert I with "[i0 me i newMExps Hnew_sl Hes_sl Hes]" as "Hloop".
    { iExists (W64 0), _, _, [], []. iFrame. simpl.
      replace (sint.nat n - sint.nat (W64 0))%nat with (sint.nat n) by word.
      iFrame. iPureIntro. split_and!; [done|word|replace (sint.nat (W64 0)) with 0%nat by word; done|word|word]. }
    wp_for "Hloop". wp_if_destruct.
    + (* Copy requirement j. *)
      list_elem es_c (sint.Z j) as e_c.
      assert (∃ e, es !! sint.nat j = Some e) as [e He_lookup].
      { apply lookup_lt_is_Some_2. rewrite -Hes_models_len. word. }
      destruct (decide (0 ≤ sint.Z j < sint.Z (slice.len _))) as [_|Hbounds]; last word.
      wp_apply (wp_load_slice_index with "[$Hes_sl]"); [word| |].
      { iPureIntro. exact He_c_lookup. }
      iIntros "Hes_sl". wp_auto.
      iDestruct (big_sepL2_lookup_acc with "Hes") as "[He Hes_restore]";
        [exact He_c_lookup|exact He_lookup|].
      iNamedPrefix "He" "He_".
      (* The new slice's entry j is still zero. *)
      iDestruct (own_slice_elem_acc (sint.Z j) (zero_val v1.LabelSelectorRequirement.t)
        with "Hnew_sl") as "[Helem Hnew_restore]"; [word| |].
      { rewrite lookup_app_r; [lia|]. rewrite Hnew_len Nat.sub_diag. apply lookup_replicate. split; [done|word]. }
      iDestruct (struct_fields_split (V:=v1.LabelSelectorRequirement.t) with "Helem")
        as "[Helem %Helem_nn]".
      iNamedPrefix "Helem" "Helem_".
      rewrite decide_True; try word. wp_auto.
      rewrite decide_True; try word. wp_auto.
      (* Copy Values. Both branches end with the entry's Values field set and a
         model [r'] of the copied requirement. *)
      wp_bind (If _ _ _).
      iApply (wp_wand _ _ _ (λ v, ⌜ v = execute_val ⌝ ∗
          ∃ (vals_c : slice.t) (r' : LabelSelectorRequirementV.t),
            "me" ∷ me_ptr ↦ e_c ∗
            "i" ∷ i_ptr ↦ j ∗
            "newMExps" ∷ newMExps_ptr ↦ new_sl ∗
            "Helem_Values" ∷ (slice_index_ref v1.LabelSelectorRequirement.t
                (sint.Z j) new_sl).[v1.LabelSelectorRequirement.t, "Values"] ↦ vals_c ∗
            "He_Hdeepown_values_some" ∷ (match LabelSelectorRequirementV.Values' e with
              | Some values => v1.LabelSelectorRequirement.Values' e_c ↦*{dq} values
              | None => True end) ∗
            "Hr'" ∷ LabelSelectorRequirementV.deepown
              {| v1.LabelSelectorRequirement.Key' := v1.LabelSelectorRequirement.Key' e_c;
                 v1.LabelSelectorRequirement.Operator' := v1.LabelSelectorRequirement.Operator' e_c;
                 v1.LabelSelectorRequirement.Values' := vals_c |} r' (DfracOwn 1) ∗
            "%Hr'_norm" ∷ ⌜ requirement_norm r' = requirement_norm e ⌝)%I
        with "[me i newMExps Helem_Values He_Hdeepown_values_some]").
      { destruct (LabelSelectorRequirementV.Values' e) as [vs|] eqn:Hvals.
        - (* Non-nil Values: a fresh slice of the same length, then copy. *)
          assert (v1.LabelSelectorRequirement.Values' e_c ≠ slice.nil) as Hvals_nn.
          { intros Hn. apply He_Hdeepown_values_none in Hn. congruence. }
          rewrite (bool_decide_eq_false_2 _ Hvals_nn). wp_auto.
          iDestruct (own_slice_len with "He_Hdeepown_values_some") as %[Hvs_len Hvs_len_nn].
          wp_apply (wp_slice_make2 (V:=go_string)); first word.
          iIntros (vals_sl) "[Hvals_sl Hvals_cap]". wp_auto.
          rewrite decide_True; try word. wp_auto.
          rewrite decide_True; try word. wp_auto.
          wp_apply (wp_slice_copy with "[$Hvals_sl $He_Hdeepown_values_some]").
          iIntros (ncopied) "(_ & Hvals_sl & Hsrc)".
          rewrite length_replicate.
          rewrite (take_ge vs); [lia|].
          rewrite (drop_ge (replicate _ _)); [rewrite length_replicate; lia|].
          rewrite app_nil_r.
          wp_auto.
          iSplitR; [done|].
          iExists vals_sl, (LabelSelectorRequirementV.mk (LabelSelectorRequirementV.Key' e)
            (LabelSelectorRequirementV.Operator' e)
            (if decide (vals_sl = slice.nil) then None else Some vs)).
          iFrame "me i newMExps Helem_Values Hsrc".
          iDestruct (own_slice_len with "Hvals_sl") as %[Hvals_sl_len _].
          rewrite /LabelSelectorRequirementV.deepown /=.
          destruct (decide (vals_sl = slice.nil)) as [Hnil|Hnnil].
          + iFrame "Hvals_cap". iPureIntro. split_and!; try done.
            rewrite /requirement_norm Hvals /=.
            subst vals_sl. simpl in Hvals_sl_len.
            destruct vs; [done|simpl in Hvals_sl_len; word].
          + iFrame. iPureIntro. split_and!; try done.
            rewrite /requirement_norm Hvals /=. done.
        - (* Nil Values: the copy's stays nil. *)
          assert (v1.LabelSelectorRequirement.Values' e_c = slice.nil) as Hvals_nil.
          { apply He_Hdeepown_values_none. done. }
          rewrite (bool_decide_eq_true_2 _ Hvals_nil). wp_auto.
          rewrite decide_True; try word. wp_auto.
          iSplitR; [done|].
          iAssert (own_slice_cap go_string slice.nil (DfracOwn 1)) as "Hnil_cap".
          { iApply own_slice_cap_nil. }
          iExists slice.nil, (LabelSelectorRequirementV.mk (LabelSelectorRequirementV.Key' e)
            (LabelSelectorRequirementV.Operator' e) None).
          iFrame.
          iSplitL.
          { rewrite /LabelSelectorRequirementV.deepown /=.
            iSplit; first done. iSplit; first done. iSplit; first done. iSplit; first done.
            iApply own_slice_cap_nil. }
          iPureIntro. rewrite /requirement_norm Hvals /=. done. }
      iIntros (v) "(-> & H)". iNamed "H".
      (* Put entry j of the new slice and requirement j of the source back. *)
      set c' := {| v1.LabelSelectorRequirement.Key' := v1.LabelSelectorRequirement.Key' e_c;
                   v1.LabelSelectorRequirement.Operator' := v1.LabelSelectorRequirement.Operator' e_c;
                   v1.LabelSelectorRequirement.Values' := vals_c |}.
      iCombineNamed "Helem_*" as "Helem".
      iAssert (typed_pointsto_def (slice_index_ref v1.LabelSelectorRequirement.t (sint.Z j) new_sl)
          c' (DfracOwn 1)) with "[Helem]" as "Helem".
      { iNamed "Helem". simpl. iFrame. }
      iDestruct (struct_fields_combine _ _ _ Helem_nn with "Helem") as "Helem".
      iSpecialize ("Hnew_restore" with "Helem").
      iAssert (LabelSelectorRequirementV.deepown e_c e dq)
        with "[He_Hdeepown_values_some He_Hdeepown_values_cap]" as "He".
      { rewrite /LabelSelectorRequirementV.deepown. iFrame. iPureIntro. split_and!; done. }
      iSpecialize ("Hes_restore" with "He").
      assert (<[Z.to_nat (sint.Z j) := c']>
          (new_cs ++ replicate (sint.nat n - sint.nat j) (zero_val v1.LabelSelectorRequirement.t)) =
        (new_cs ++ [c']) ++
          replicate (sint.nat n - sint.nat (word.add j (W64 1))) (zero_val v1.LabelSelectorRequirement.t))
        as Hins.
      { rewrite insert_app_r_alt; [lia|].
        replace (sint.nat j - length new_cs)%nat with 0%nat by lia.
        replace (sint.nat n - sint.nat j)%nat
          with (S (sint.nat n - sint.nat (word.add j (W64 1)))) by word.
        simpl. rewrite -app_assoc. done. }
      iEval (rewrite Hins) in "Hnew_restore".
      iApply wp_for_post_do. wp_auto.
      iFrame "∗#".
      iExists (new_rs ++ [r']).
      iFrame.
      iSplitR; [by rewrite big_sepL2_nil|].
      iPureIntro. split_and!.
      * rewrite length_app Hnew_len /=. word.
      * replace (sint.nat (word.add j (W64 1))) with (S (sint.nat j)) by word.
        rewrite (take_S_r _ _ e He_lookup) !fmap_app Hnew_norm /= Hr'_norm. done.
      * word.
      * word.
    + (* All requirements copied: the new slice holds exactly the copies. *)
      assert (sint.nat j = length es) as Hj_len by (rewrite -Hes_models_len Hes_len; word).
      rewrite Hj_len firstn_all in Hnew_norm.
      replace (sint.nat n - sint.nat j)%nat with 0%nat in * by word.
      rewrite /= app_nil_r.
      set new_me := (if decide (new_sl = slice.nil) then None else Some new_rs).
      iApply ("HΦ" $! new_l (LabelSelectorV.mk
        (Some (<[key:=value]> (default ∅ selector.(LabelSelectorV.MatchLabels')))) new_me)).
      iSplitL "Hself_MatchLabels Hself_MatchExpressions Hsel_Hdeepown_matchlabels_some Hsel_Hdeepown_matchexpressions_cap Hes_sl Hes".
      { iExists sel_c.
        iSplitL "Hself_MatchLabels Hself_MatchExpressions".
        { iCombineNamed "Hself_*" as "Hsel_fields".
          iAssert (typed_pointsto_def selector_l sel_c dq) with "[Hsel_fields]" as "Hsel_fields".
          { iNamed "Hsel_fields". destruct sel_c. simpl. iFrame. }
          iApply (struct_fields_combine _ _ _ Hsel_nn with "Hsel_fields"). }
        rewrite /LabelSelectorV.deepown /deepown_slice Hes. iFrame "∗%". }
      iSplitL.
      { iExists {| v1.LabelSelector.MatchLabels' := ml_l;
                   v1.LabelSelector.MatchExpressions' := new_sl |}.
        iSplitL "Hnew_MatchLabels Hnew_MatchExpressions".
        { iCombineNamed "Hnew_*" as "Hnew_fields".
          iAssert (typed_pointsto_def new_l {| v1.LabelSelector.MatchLabels' := ml_l;
                     v1.LabelSelector.MatchExpressions' := new_sl |} (DfracOwn 1))
            with "[Hnew_fields]" as "Hnew_fields".
          { iNamed "Hnew_fields". simpl. iFrame. }
          iApply (struct_fields_combine _ _ _ Hnew_nn with "Hnew_fields"). }
        rewrite /LabelSelectorV.deepown /= /new_me.
        iSplit.
        { iPureIntro. split; intros H; [contradiction|discriminate]. }
        iSplitL "Hml".
        { iExists (<[key:=value]> (default ∅ selector.(LabelSelectorV.MatchLabels'))). iFrame. done. }
        destruct (decide (new_sl = slice.nil)) as [Hnil|Hnnil].
        - subst new_sl. iApply deepown_slice_nil.
        - rewrite /deepown_slice. iSplit.
          { iPureIntro. split; intros H; [contradiction|discriminate]. }
          iExists new_cs. iFrame. }
      iPureIntro.
      rewrite /selector_norm /selector_with_label /= Hes /new_me.
      destruct (decide (new_sl = slice.nil)) as [Hnil|Hnnil].
      * (* A nil copy means there were no requirements. *)
        subst new_sl. simpl in Hnew_sl_len.
        assert (es = []) as ->.
        { apply nil_length_inv. rewrite -Hes_models_len Hes_len. word. }
        done.
      * pose proof (f_equal length Hnew_norm) as Hlen_eq.
        rewrite !length_fmap in Hlen_eq.
        destruct es as [|e0 es']; destruct new_rs as [|r0 rs']; simpl in Hlen_eq;
          try discriminate; [done|].
        rewrite Hnew_norm. done.
  - (* No MatchExpressions: the copy's stays nil. *)
    assert (v1.LabelSelector.MatchExpressions' sel_c = slice.nil) as Hes_nil.
    { apply Hsel_Hdeepown_matchexpressions_none. done. }
    rewrite Hes_nil bool_decide_eq_true_2 //. wp_auto.
    iAssert (own_slice_cap v1.LabelSelectorRequirement.t slice.nil (DfracOwn 1)) as "Hnil_cap".
    { iApply own_slice_cap_nil. }
    iApply ("HΦ" $! new_l (LabelSelectorV.mk
      (Some (<[key:=value]> (default ∅ selector.(LabelSelectorV.MatchLabels')))) None)).
    iSplitL "Hself_MatchLabels Hself_MatchExpressions Hsel_Hdeepown_matchlabels_some Hes_sl Hes Hsel_Hdeepown_matchexpressions_cap".
    { iExists sel_c.
      iSplitL "Hself_MatchLabels Hself_MatchExpressions".
      { iCombineNamed "Hself_*" as "Hsel_fields".
        iAssert (typed_pointsto_def selector_l sel_c dq) with "[Hsel_fields]" as "Hsel_fields".
        { iNamed "Hsel_fields". destruct sel_c. simpl in Hes_nil. subst. simpl. iFrame. }
        iApply (struct_fields_combine _ _ _ Hsel_nn with "Hsel_fields"). }
      rewrite /LabelSelectorV.deepown /deepown_slice Hes.
      iSplit; first done.
      iSplitL "Hsel_Hdeepown_matchlabels_some"; first iExact "Hsel_Hdeepown_matchlabels_some".
      iSplit; first (iPureIntro; rewrite Hes_nil; done).
      iExists es_c. rewrite Hes_nil. iFrame. }
    iSplitL.
    { iExists {| v1.LabelSelector.MatchLabels' := ml_l;
                 v1.LabelSelector.MatchExpressions' := slice.nil |}.
      iSplitL "Hnew_MatchLabels Hnew_MatchExpressions".
      { iCombineNamed "Hnew_*" as "Hnew_fields".
        iAssert (typed_pointsto_def new_l {| v1.LabelSelector.MatchLabels' := ml_l;
                   v1.LabelSelector.MatchExpressions' := slice.nil |} (DfracOwn 1))
          with "[Hnew_fields]" as "Hnew_fields".
        { iNamed "Hnew_fields". simpl. iFrame. }
        iApply (struct_fields_combine _ _ _ Hnew_nn with "Hnew_fields"). }
      rewrite /LabelSelectorV.deepown /=.
      iSplit.
      { iPureIntro. split; intros H; [contradiction|discriminate]. }
      iSplitL "Hml".
      { iExists (<[key:=value]> (default ∅ selector.(LabelSelectorV.MatchLabels'))). iFrame. done. }
      iApply deepown_slice_nil. }
    iPureIntro. rewrite /selector_norm /selector_with_label /= Hes. done.
Qed.

End proof.
