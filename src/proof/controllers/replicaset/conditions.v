From New.proof Require Import prelude empty_ffi.
From New.proof.controllers.replicaset Require Export replicaset_init.
From New.proof.kubernetes_types Require Export prelude.

Section proof.
Context `{hG: !heapGS Σ} `{!ffi_semantics _ _}.
Context {sem : go.Semantics}
  {package_sem : code.controllers.replicaset.replicaset.Assumptions}.
Collection W := sem + package_sem.
#[local] Instance base_common_sem : common.Assumptions | 100 :=
  code.controllers.replicaset.replicaset.import_common_Assumption.
#[local] Instance base_apimodel_sem : apimodel.Assumptions | 100 :=
  common.import_apimodel_Assumption.
#[local] Instance object_meta_v1_sem :
    code.k8s_io.apimachinery.pkg.apis.meta.v1.v1.Assumptions :=
  apimodel.import_apis_meta_v1_Assumption.
#[local] Instance object_apps_v1_sem :
    code.k8s_io.api.apps.v1.v1.Assumptions :=
  apimodel.import_api_apps_v1_Assumption.
#[local] Instance object_core_v1_sem :
    code.k8s_io.api.core.v1.v1.Assumptions :=
  code.k8s_io.api.apps.v1.v1.import_core_v1_Assumption.
Local Set Default Proof Using "All".

Definition keep_condition_c (ct : go_string) (c : api_apps_v1.ReplicaSetCondition.t) : Prop :=
  c.(api_apps_v1.ReplicaSetCondition.Type') ≠ ct.

Lemma wp_filterOutCondition (sl : slice.t) (cs : list api_apps_v1.ReplicaSetCondition.t) dq
    (ct : go_string) :
  {{{ is_pkg_init code.controllers.replicaset.pkg_id.replicaset ∗ sl ↦*{dq} cs }}}
    @! replicaset.filterOutCondition #sl #ct
  {{{ (sl' : slice.t), RET #sl';
      sl ↦*{dq} cs ∗
      sl' ↦* filter (keep_condition_c ct) cs ∗
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

Lemma big_sepL2_conditions_filter (cs : list api_apps_v1.ReplicaSetCondition.t)
    (conds : list ReplicaSetConditionV.t) ct :
  ([∗ list] c;v ∈ cs;conds, ReplicaSetConditionV.deepown (Σ:=Σ) c v DfracDiscarded) ⊢
  ([∗ list] c;v ∈ filter (keep_condition_c ct) cs; filter (keep_condition ct) conds,
    ReplicaSetConditionV.deepown c v DfracDiscarded).
Proof.
  iIntros "H".
  iInduction cs as [|c cs] "IH" forall (conds); destruct conds as [|v conds].
  - done.
  - iDestruct (big_sepL2_nil_inv_l with "H") as %Hnil. discriminate Hnil.
  - iDestruct (big_sepL2_nil_inv_r with "H") as %Hnil. discriminate Hnil.
  - rewrite big_sepL2_cons. iDestruct "H" as "[#Hcv H]".
    iAssert (⌜ c.(api_apps_v1.ReplicaSetCondition.Type') = v.(ReplicaSetConditionV.Type') ⌝)%I
      as %Htype.
    { iDestruct "Hcv" as "(%Htype & _)". done. }
    rewrite !filter_cons.
    destruct (decide (keep_condition_c ct c)) as [Hkeep|Hdrop];
      [rewrite decide_True; first (rewrite /keep_condition -Htype; exact Hkeep)
      |rewrite decide_False; first (rewrite /keep_condition -Htype; exact Hdrop)].
    + rewrite big_sepL2_cons. iFrame "Hcv". iApply ("IH" with "H").
    + iApply ("IH" with "H").
Qed.

Lemma wp_RemoveCondition status_l (status_c : api_apps_v1.ReplicaSetStatus.t) status
    (ct : go_string) :
  {{{ is_pkg_init code.controllers.replicaset.pkg_id.replicaset ∗
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
  destruct status.(ReplicaSetStatusV.Conditions') as [conds|] eqn:Hconds.
  - iDestruct "Hdeepown_conditions_some" as (cs) "[#Hsl #Hcs]".
    wp_apply (wp_filterOutCondition with "[$Hsl]").
    iIntros (sl') "(_ & Hsl' & %Hsl'_nil)". wp_auto.
    iMod (own_slice_persist with "Hsl'") as "#Hsl'".
    iDestruct (big_sepL2_conditions_filter _ _ ct with "Hcs") as "#Hcs'".
    iDestruct (big_sepL2_length with "Hcs'") as %Hlen'.
    iModIntro. iApply "HΦ". iFrame "Hl".
    rewrite /ReplicaSetStatusV.deepown /conditions_without /=.
    iFrame "# %".
    destruct (filter (keep_condition ct) conds) as [|v kept] eqn:Hkept.
    + iSplit; last done. iPureIntro.
      rewrite Hsl'_nil. split; first done. intros _.
      apply length_zero_iff_nil. rewrite Hlen'. done.
    + iSplit.
      { iPureIntro. rewrite Hsl'_nil. split; last done. intros Hnil.
        rewrite Hnil in Hlen'. done. }
      iExists (filter (keep_condition_c ct) cs). rewrite /deepown_list. iFrame "#".
  - assert (status_c.(api_apps_v1.ReplicaSetStatus.Conditions') = slice.nil) as Hnil.
    { by apply Hdeepown_conditions_none. }
    rewrite Hnil.
    wp_apply (wp_filterOutCondition slice.nil [] DfracDiscarded with "[]").
    { iApply own_slice_nil. }
    iIntros (sl') "(_ & _ & %Hsl'_nil)". wp_auto.
    assert (sl' = slice.nil) as -> by (by apply Hsl'_nil).
    iModIntro. iApply "HΦ". iFrame "Hl".
    rewrite /ReplicaSetStatusV.deepown /conditions_without /=.
    iFrame "# %". done.
Qed.

Lemma big_sepL2_conditions_forall (cs : list api_apps_v1.ReplicaSetCondition.t)
    (conds : list ReplicaSetConditionV.t) ct :
  ([∗ list] c;v ∈ cs;conds, ReplicaSetConditionV.deepown (Σ:=Σ) c v DfracDiscarded) ⊢
  ⌜ Forall (keep_condition_c ct) cs ↔ Forall (keep_condition ct) conds ⌝.
Proof.
  iIntros "H".
  iInduction cs as [|c cs] "IH" forall (conds); destruct conds as [|v conds].
  - done.
  - iDestruct (big_sepL2_nil_inv_l with "H") as %Hnil. discriminate Hnil.
  - iDestruct (big_sepL2_nil_inv_r with "H") as %Hnil. discriminate Hnil.
  - rewrite big_sepL2_cons. iDestruct "H" as "[Hcv H]".
    iDestruct "Hcv" as "(%Htype & _)".
    iDestruct ("IH" with "H") as %IH.
    iPureIntro. split; intros Hall; apply Forall_cons_1 in Hall as [Hhead Htail];
      apply Forall_cons_2.
    + rewrite /keep_condition -Htype. exact Hhead.
    + by apply IH.
    + rewrite /keep_condition_c Htype. exact Hhead.
    + by apply IH.
Qed.

(* [GetCondition] returns nil exactly when no condition has the given type. *)
Lemma wp_GetCondition (status_c : api_apps_v1.ReplicaSetStatus.t) status (ct : go_string) :
  {{{ is_pkg_init code.controllers.replicaset.pkg_id.replicaset ∗
      ReplicaSetStatusV.deepown status_c status DfracDiscarded
  }}}
    @! replicaset.GetCondition #status_c #ct
  {{{ (p : loc), RET #p;
      ⌜ p = null ↔ Forall (keep_condition ct) (default [] status.(ReplicaSetStatusV.Conditions')) ⌝
  }}}.
Proof.
  wp_start as "#Hdeepown".
  rewrite /ReplicaSetStatusV.deepown. iNamed "Hdeepown".
  iAssert (∃ cs, status_c.(api_apps_v1.ReplicaSetStatus.Conditions') ↦*□ cs ∗
    ([∗ list] c;v ∈ cs;default [] status.(ReplicaSetStatusV.Conditions'),
      ReplicaSetConditionV.deepown c v DfracDiscarded))%I as (cs) "[#Hsl #Hcs]".
  { destruct status.(ReplicaSetStatusV.Conditions') as [conds|] eqn:Hconds.
    - iDestruct "Hdeepown_conditions_some" as (cs) "[Hsl Hcs]". iExists cs. iFrame "#".
    - iExists []. rewrite (proj2 Hdeepown_conditions_none) //. iSplit; last done.
      iApply own_slice_nil. }
  iDestruct (big_sepL2_conditions_forall _ _ ct with "Hcs") as %Hforall.
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
