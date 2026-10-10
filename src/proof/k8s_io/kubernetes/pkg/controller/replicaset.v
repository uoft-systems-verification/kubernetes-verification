From New.proof Require Import prelude empty_ffi util.
From New.proof.k8s_io.kubernetes.pkg.controller Require Export replicaset_init.
From New.proof.kubernetes_types Require Export prelude.

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
  destruct status.(ReplicaSetStatusV.Conditions') as [conds|] eqn:Hconds.
  - iDestruct "Hdeepown_conditions_some" as (cs) "[#Hsl %Hcs]".
    wp_apply (wp_filterOutCondition with "[$Hsl]").
    iIntros (sl') "(_ & Hsl' & %Hsl'_nil)". wp_auto.
    iMod (own_slice_persist with "Hsl'") as "#Hsl'".
    iModIntro. iApply "HΦ". iFrame "Hl".
    assert (filter (keep_condition ct) (ReplicaSetConditionV.of_go <$> cs) =
      ReplicaSetConditionV.of_go <$> filter (keep_condition_c ct) cs) as Hfilter.
    { apply filter_fmap_comm. intros. rewrite /keep_condition_c /keep_condition //. }
    rewrite /ReplicaSetStatusV.deepown /conditions_without /= Hcs Hfilter.
    iFrame "# %".
    destruct (filter (keep_condition_c ct) cs) as [|c kept]; simpl.
    + iSplit; last done. iPureIntro. split; [done|intros _; by apply Hsl'_nil].
    + iSplit; first (iPureIntro; split; intros H; [apply Hsl'_nil in H|]; done).
      iExists (c :: kept). iFrame "#". done.
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
  iAssert (∃ cs, status_c.(api_apps_v1.ReplicaSetStatus.Conditions') ↦*□ cs ∗
    ⌜ default [] status.(ReplicaSetStatusV.Conditions') = ReplicaSetConditionV.of_go <$> cs ⌝)%I
    as (cs) "[#Hsl %Hcs]".
  { destruct status.(ReplicaSetStatusV.Conditions') as [conds|] eqn:Hconds.
    - iDestruct "Hdeepown_conditions_some" as (cs) "[Hsl %Hcs]". iExists cs. by iFrame "#".
    - iExists []. rewrite (proj2 Hdeepown_conditions_none) //. iSplit; last done.
      iApply own_slice_nil. }
  assert (Forall (keep_condition_c ct) cs ↔
    Forall (keep_condition ct) (default [] status.(ReplicaSetStatusV.Conditions'))) as Hforall.
  { by rewrite Hcs Forall_fmap. }
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
