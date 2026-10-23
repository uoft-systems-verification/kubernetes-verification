From New.proof Require Import prelude empty_ffi util.
From New.proof.k8s_io.kubernetes.pkg.controller Require Export replicaset_init.
From New.object_specs Require Export prelude.

(* Specs for the upstream ReplicaSet condition helpers, which
   controllers/replicaset imports instead of copying. *)
Notation upstream_rs_pkg := code.k8s_io.kubernetes.pkg.controller.replicaset.pkg_id.replicaset.

Section proof.
Context `{hG: !heapGS Σ} `{!ffi_semantics _ _}.
Context {sem : go.Semantics}
  {package_sem : code.k8s_io.kubernetes.pkg.controller.replicaset.replicaset.Assumptions}.
Collection W := sem + package_sem.
#[local] Instance object_meta_v1_sem :
    code.k8s_io.apimachinery.pkg.apis.meta.v1.v1.Assumptions :=
  code.k8s_io.kubernetes.pkg.controller.replicaset.replicaset.import_meta_v1_Assumption.
#[local] Instance object_apps_v1_sem :
    code.k8s_io.api.apps.v1.v1.Assumptions :=
  code.k8s_io.kubernetes.pkg.controller.replicaset.replicaset.import_apps_v1_Assumption.
#[local] Instance object_core_v1_sem :
    code.k8s_io.api.core.v1.v1.Assumptions :=
  code.k8s_io.kubernetes.pkg.controller.replicaset.replicaset.import_core_v1_Assumption.
Local Set Default Proof Using "All".

Definition keep_condition_c (ct : go_string) (c : api_apps_v1.ReplicaSetCondition.t) : Prop :=
  c.(api_apps_v1.ReplicaSetCondition.Type') ≠ ct.

Lemma wp_filterOutCondition (sl : slice.t) (cs : list api_apps_v1.ReplicaSetCondition.t) dq
    (ct : go_string) :
  {{{ is_pkg_init upstream_rs_pkg ∗ sl ↦*{dq} cs }}}
    @! replicaset.filterOutCondition #sl #ct
  {{{ (sl' : slice.t), RET #sl';
      sl ↦*{dq} cs ∗
      sl' ↦* filter (keep_condition_c ct) cs ∗
      own_slice_cap api_apps_v1.ReplicaSetCondition.t sl' (DfracOwn 1) ∗
      ⌜ sl' = slice.nil ↔ filter (keep_condition_c ct) cs = [] ⌝
  }}}.
Proof.
  wp_start as "Hsl".
  wp_auto.
  iDestruct (own_slice_len with "Hsl") as %(Hsl_len1 & Hsl_len2).
  set I := (∃ (i : w64) (c : api_apps_v1.ReplicaSetCondition.t) (res : slice.t),
    "i" ∷ i_ptr ↦ i ∗
    "c" ∷ c_ptr ↦ c ∗
    "newConditions" ∷ newConditions_ptr ↦ res ∗
    "Hres" ∷ res ↦* filter (keep_condition_c ct) (take (sint.nat i) cs) ∗
    "Hres_cap" ∷ own_slice_cap api_apps_v1.ReplicaSetCondition.t res (DfracOwn 1) ∗
    "%Hres_nil" ∷ ⌜ res = slice.nil ↔ filter (keep_condition_c ct) (take (sint.nat i) cs) = [] ⌝ ∗
    "%Hi" ∷ ⌜ 0 ≤ sint.Z i ≤ sint.Z (slice.len sl) ⌝)%I.
  iAssert I with "[i c newConditions]" as "Hloop".
  { iExists (W64 0), (zero_val _), slice.nil. rewrite take_0 filter_nil.
    iFrame "i c newConditions".
    iSplitR; first iApply own_slice_nil.
    iSplitR; first iApply own_slice_cap_nil.
    iPureIntro. split; [done|word]. }
  wp_for "Hloop".
  wp_if_destruct.
  - list_elem cs (sint.Z i) as this.
    rewrite decide_True; first (pose proof (lookup_lt_Some _ _ _ Hthis_lookup); word).
    wp_apply (wp_load_slice_index with "[$Hsl]"); [word| |].
    { iPureIntro. exact Hthis_lookup. }
    iIntros "Hsl". wp_auto.
    assert (take (sint.nat (word.add i (W64 1))) cs = take (sint.nat i) cs ++ [this]) as Htake.
    { assert (sint.nat (word.add i (W64 1)) = S (sint.nat i)) as -> by word.
      rewrite (take_S_r _ _ this) //. }
    wp_if_destruct.
    + iApply wp_for_post_continue. wp_auto.
      iFrame "Hsl HΦ condType". iExists (word.add i (W64 1)), this, res.
      assert (¬ keep_condition_c (api_apps_v1.ReplicaSetCondition.Type' this) this) as Hdrop.
      { rewrite /keep_condition_c. tauto. }
      rewrite Htake list.filter_app (filter_singleton_False _ this [] Hdrop) app_nil_r.
      iFrame. iPureIntro. split; first done. word.
    + wp_apply wp_slice_literal. iSplitR; first done.
      iIntros (one_sl) "[Hone _]". wp_auto.
      wp_apply (wp_slice_append with "[$Hres $Hres_cap $Hone]").
      iIntros (res') "(Hres & Hres_cap & _)". wp_auto.
      iApply wp_for_post_do. wp_auto.
      iFrame "Hsl HΦ condType". iExists (word.add i (W64 1)), this, res'.
      assert (keep_condition_c ct this) as Hkeep.
      { rewrite /keep_condition_c. congruence. }
      rewrite Htake list.filter_app (filter_singleton_True _ this [] Hkeep).
      iDestruct (own_slice_len with "Hres") as %[Hres_len _].
      iFrame. iPureIntro. split; last word.
      split; intros Hcontra; last (destruct (filter _ _); done).
      subst res'. simpl in Hres_len. rewrite length_app length_insert /= in Hres_len. exfalso. word.
  - try wp_auto.
    assert (take (sint.nat i) cs = cs) as Htake_all.
    { apply take_ge. word. }
    rewrite Htake_all in Hres_nil |- *.
    iApply "HΦ". iFrame. done.
Qed.

Definition keep_condition (ct : go_string) (v : ReplicaSetConditionV.t) : Prop :=
  v.(ReplicaSetConditionV.Type') ≠ ct.

(* Extract the fields read by condition filtering from the pure condition view. *)
Lemma condition_types_agree cs vs :
  ([∗ list] c;v ∈ cs;vs, ReplicaSetConditionV.deepown (Σ:=Σ) c v DfracDiscarded) ⊢
  ⌜(api_apps_v1.ReplicaSetCondition.Type' <$> cs) = (ReplicaSetConditionV.Type' <$> vs)⌝.
Proof.
  iIntros "Hconditions".
  iAssert ([∗ list] c;v ∈ cs;vs,
    ⌜c.(api_apps_v1.ReplicaSetCondition.Type') = v.(ReplicaSetConditionV.Type')⌝)%I
    with "[Hconditions]" as "Htypes".
  { iApply (big_sepL2_impl with "Hconditions").
    iIntros "!#" (k c v Hc Hv) "Hcondition".
    rewrite /ReplicaSetConditionV.deepown. iDestruct "Hcondition" as %Hcondition.
    iPureIntro. by rewrite -Hcondition /ReplicaSetConditionV.of_go. }
  iDestruct (big_sepL2_pure with "Htypes") as %(Hlen & Hlookup).
  iPureIntro. apply list_eq. intros k. rewrite !list_lookup_fmap.
  destruct (cs !! k) as [c|] eqn:Hc; destruct (vs !! k) as [v|] eqn:Hv; simpl.
  - by rewrite (Hlookup k c v Hc Hv).
  - apply lookup_lt_Some in Hc. apply lookup_ge_None in Hv. lia.
  - apply lookup_ge_None in Hc. apply lookup_lt_Some in Hv. lia.
  - done.
Qed.

Lemma filter_condition_ownership ct cs vs :
  ([∗ list] c;v ∈ cs;vs, ReplicaSetConditionV.deepown (Σ:=Σ) c v DfracDiscarded) ⊢
  [∗ list] c;v ∈ filter (keep_condition_c ct) cs;filter (keep_condition ct) vs,
    ReplicaSetConditionV.deepown c v DfracDiscarded.
Proof.
  revert vs. induction cs as [|c cs IH]; intros [|v vs].
  - done.
  - iIntros "H". iDestruct (big_sepL2_nil_inv_l with "H") as %Hnil. discriminate.
  - iIntros "H". iDestruct (big_sepL2_nil_inv_r with "H") as %Hnil. discriminate.
  - rewrite big_sepL2_cons. iIntros "#[Hcondition Hrest]".
    iPoseProof "Hcondition" as "Hfields".
    iEval (rewrite /ReplicaSetConditionV.deepown) in "Hfields". iDestruct "Hfields" as %Hfields.
    assert (api_apps_v1.ReplicaSetCondition.Type' c = v.(ReplicaSetConditionV.Type')) as Htype.
    { by rewrite -Hfields /ReplicaSetConditionV.of_go. }
    rewrite !filter_cons /keep_condition_c /keep_condition -Htype.
    case_decide; case_decide; try contradiction; simpl.
    + iSplit; first iExact "Hcondition".
      iApply IH. iExact "Hrest".
    + iApply IH. iExact "Hrest".
Qed.

(* [filterOutCondition] returns nil when no condition survives. *)
Definition conditions_without (ct : go_string)
    (conds : option (list ReplicaSetConditionV.t)) : option (list ReplicaSetConditionV.t) :=
  match conds with
  | None => None
  | Some conds =>
      match filter (keep_condition ct) conds with
      | [] => None
      | kept => Some kept
      end
  end.

Lemma wp_RemoveCondition status_l (status_c : api_apps_v1.ReplicaSetStatus.t) status
    (ct : go_string) :
  {{{ is_pkg_init upstream_rs_pkg ∗
      status_l ↦ status_c ∗
      ReplicaSetStatusV.deepown status_c status DfracDiscarded
  }}}
    @! replicaset.RemoveCondition #status_l #ct
  {{{ status_c', RET #();
      status_l ↦ status_c' ∗
      ReplicaSetStatusV.deepown status_c'
        (status <| ReplicaSetStatusV.Conditions' :=
          conditions_without ct status.(ReplicaSetStatusV.Conditions') |>) DfracDiscarded
  }}}.
Proof.
  wp_start as "[Hl #Hdeepown]".
  iApply wp_fupd.
  wp_auto.
  iPoseProof "Hdeepown" as "Hdeepown'".
  rewrite {2}/ReplicaSetStatusV.deepown. iNamed "Hdeepown'".
  iDestruct "Hdeepown_conditions" as
    "(%Hdeepown_conditions_none & %cs & #Hsl & #Hcap & #Hvalues)".
  destruct status.(ReplicaSetStatusV.Conditions') as [conds|] eqn:Hconds.
  - wp_apply (wp_filterOutCondition with "[$Hsl]").
    iIntros (sl') "(_ & Hsl' & Hnew_cap & %Hsl'_nil)". wp_auto.
    iMod (own_slice_persist with "Hsl'") as "#Hsl'". iPersist "Hnew_cap".
    iPoseProof (filter_condition_ownership ct with "Hvalues") as "#Hfiltered".
    iDestruct (big_sepL2_length with "Hfiltered") as %Hfiltered_len.
    iModIntro. iApply "HΦ". iFrame "Hl".
    rewrite /ReplicaSetStatusV.deepown /conditions_without /= Hconds.
    destruct (filter (keep_condition ct) conds) as [|v kept] eqn:Hkept; simpl in Hfiltered_len |- *;
      rewrite Hkept /= in Hfiltered_len.
    + assert (filter (keep_condition_c ct) cs = []) as Hempty.
      { apply length_zero_iff_nil. exact Hfiltered_len. }
      assert (sl' = slice.nil) as -> by (by apply Hsl'_nil).
      iAssert (deepown_slice ReplicaSetConditionV.deepown slice.nil None DfracDiscarded)%I as "#Hnew_values".
      { iApply deepown_slice_nil. }
      iFrame "# %".
    + assert (sl' ≠ slice.nil) as Hnonnull.
      { intros Hnil. apply Hsl'_nil in Hnil. rewrite Hnil in Hfiltered_len. discriminate. }
      assert (sl' = slice.nil ↔ (Some (v :: kept) : option (list ReplicaSetConditionV.t)) = None) as Hnone.
      { split; intros H; [contradiction|discriminate]. }
      iAssert (deepown_slice ReplicaSetConditionV.deepown sl' (Some (v :: kept)) DfracDiscarded)
        as "#Hnew_values".
      { rewrite /deepown_slice. iSplit; first done.
        iExists (filter (keep_condition_c ct) cs). iFrame "#". }
      iFrame "# %".

  - assert (status_c.(api_apps_v1.ReplicaSetStatus.Conditions') = slice.nil) as Hnil.
    { by apply Hdeepown_conditions_none. }
    rewrite Hnil.
    wp_apply (wp_filterOutCondition slice.nil [] DfracDiscarded with "[]").
    { iApply own_slice_nil. }
    iIntros (sl') "(_ & _ & Hnew_cap & %Hsl'_nil)". wp_auto. iPersist "Hnew_cap".
    assert (sl' = slice.nil) as -> by (by apply Hsl'_nil).
    iModIntro. iApply "HΦ". iFrame "Hl".
    rewrite /ReplicaSetStatusV.deepown /conditions_without /=.
    iAssert (deepown_slice ReplicaSetConditionV.deepown slice.nil None DfracDiscarded)%I as "#Hnew_values".
    { iApply deepown_slice_nil. }
    iFrame "# %".
Qed.

(* [GetCondition] returns nil exactly when no condition has the given type. *)
Lemma wp_GetCondition (status_c : api_apps_v1.ReplicaSetStatus.t) status (ct : go_string) :
  {{{ is_pkg_init upstream_rs_pkg ∗
      ReplicaSetStatusV.deepown status_c status DfracDiscarded
  }}}
    @! replicaset.GetCondition #status_c #ct
  {{{ (p : loc), RET #p;
      ⌜ p = null ↔ Forall (keep_condition ct) (default [] status.(ReplicaSetStatusV.Conditions')) ⌝
  }}}.
Proof.
  wp_start as "#Hdeepown".
  rewrite /ReplicaSetStatusV.deepown. iNamed "Hdeepown".
  iDestruct "Hdeepown_conditions" as "(_ & %cs & #Hsl & _ & Hvalues)".
  iDestruct (condition_types_agree with "Hvalues") as %Htypes.
  assert (Forall (keep_condition_c ct) cs ↔
    Forall (keep_condition ct) (default [] status.(ReplicaSetStatusV.Conditions'))) as Hforall.
  { trans (Forall (λ ty, ty ≠ ct) (api_apps_v1.ReplicaSetCondition.Type' <$> cs)).
    - rewrite Forall_fmap. done.
    - rewrite Htypes Forall_fmap. done. }
  set sl := status_c.(api_apps_v1.ReplicaSetStatus.Conditions').
  iDestruct (own_slice_len with "Hsl") as %(Hsl_len1 & Hsl_len2).
  wp_auto.
  set I := (∃ (i : w64) (c : api_apps_v1.ReplicaSetCondition.t),
    "i" ∷ i_ptr ↦ i ∗
    "c" ∷ c_ptr ↦ c ∗
    "%Hprefix" ∷ ⌜ Forall (keep_condition_c ct) (take (sint.nat i) cs) ⌝ ∗
    "%Hi" ∷ ⌜ 0 ≤ sint.Z i ≤ sint.Z (slice.len sl) ⌝)%I.
  iAssert I with "[i c]" as "Hloop".
  { iExists (W64 0), (zero_val _). iFrame. rewrite take_0. iPureIntro. split; [constructor|word]. }
  wp_for "Hloop".
  wp_if_destruct.
  - list_elem cs (sint.Z i) as this.
    rewrite decide_True; first (pose proof (lookup_lt_Some _ _ _ Hthis_lookup); word).
    wp_apply (wp_load_slice_index with "[$Hsl]"); [word| |].
    { iPureIntro. exact Hthis_lookup. }
    iIntros "_". wp_auto.
    wp_if_destruct.
    + iApply wp_for_post_return. wp_auto.
      iDestruct (typed_pointsto_not_null with "c") as %Hc_nonnull.
      iApply "HΦ". iPureIntro. split; first done.
      intros Hall. exfalso.
      apply Hforall in Hall.
      rewrite Forall_lookup in Hall.
      specialize (Hall _ _ Hthis_lookup). apply Hall. done.
    + iApply wp_for_post_do. wp_auto.
      iFrame "HΦ condType". iExists (word.add i (W64 1)), this. iFrame.
      assert (sint.nat (word.add i (W64 1)) = S (sint.nat i)) as -> by word.
      rewrite (take_S_r _ _ this) // Forall_app Forall_singleton.
      iPureIntro. split; last word. split; first done. rewrite /keep_condition_c. congruence.
  - try wp_auto.
    assert (take (sint.nat i) cs = cs) as Htake_all.
    { apply take_ge. word. }
    rewrite Htake_all in Hprefix.
    iApply "HΦ". iPureIntro. split; first (intros _; by apply Hforall). done.
Qed.

End proof.
