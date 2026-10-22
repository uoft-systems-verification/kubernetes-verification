From New.proof Require Import prelude empty_ffi.
From New.proof.k8s_io.apimachinery.pkg.apis.meta.v1 Require Export validation_init.
From New.proof.k8s_io.apimachinery.pkg.util.validation Require Import field.
From New.proof.k8s_io.apimachinery.pkg.util Require Import sets.
From New.proof.k8s_io.utils Require Import ptr.
From New.object_specs Require Import delete_options.

Module metav1_validation := code.k8s_io.apimachinery.pkg.apis.meta.v1.validation.validation.

Section proof.
Context `{hG: !heapGS Σ} `{!ffi_semantics _ _}.
Context {sem : go.Semantics} {package_sem : metav1_validation.Assumptions}.
Collection W := sem + package_sem.
Local Set Default Proof Using "All".

Lemma wp_ValidateDryRun_valid (path : loc) sl directives dq :
  {{{ is_pkg_init code.k8s_io.apimachinery.pkg.apis.meta.v1.validation.pkg_id.validation ∗
      sl ↦*{dq} directives ∗
      ⌜ Forall (λ directive, directive = "All"%go) directives ⌝
  }}}
    @! metav1_validation.ValidateDryRun #path #sl
  {{{ errs, RET #errs;
      errs ↦* ([] : list loc) ∗
      own_slice_cap loc errs 1 ∗
      sl ↦*{dq} directives
  }}}.
Proof.
  wp_start as "[Hdirectives %Hvalid]". wp_auto.
  wp_apply wp_slice_literal. iSplitR; first done.
  iIntros (errs) "[Herrs Hcap]". wp_auto.
  iDestruct (is_pkg_init_access with "[$]") as "Hinit".
  iDestruct "Hinit" as (allowed_l) "[#Hallowed #Hallowed_map]".
  wp_method_call. wp_auto.
  wp_apply (wp_String__HasAll with "[$Hallowed_map $Hdirectives]").
  { iPureIntro. eapply Forall_impl; last exact Hvalid.
    intros directive ->. apply elem_of_dom. rewrite lookup_singleton. done. }
  iIntros "[_ Hdirectives]". wp_auto.
  iApply "HΦ". iFrame.
Qed.

Lemma wp_ValidateIgnoreStoreReadError_valid (path l : loc) options dq :
  {{{ is_pkg_init code.k8s_io.apimachinery.pkg.apis.meta.v1.validation.pkg_id.validation ∗
      DeleteOptionsV.deepown_l l options dq ∗
      ⌜ DeleteOptionsV.valid options ⌝
  }}}
    @! metav1_validation.ValidateIgnoreStoreReadError #path #l
  {{{ errs, RET #errs;
      errs ↦* ([] : list loc) ∗
      own_slice_cap loc errs 1 ∗
      DeleteOptionsV.deepown_l l options dq
  }}}.
Proof.
  wp_start as "[Hoptions %Hvalid]".
  iDestruct "Hoptions" as (c) "[Hoptions Hdeepown]". iNamed "Hdeepown".
  wp_auto.
  wp_apply wp_slice_literal. iSplitR; first done.
  iIntros (errs) "[Herrs Hcap]". wp_auto.
  iAssert (ptr.opt_ptr_rep c.(v1.DeleteOptions.IgnoreStoreReadErrorWithClusterBreakingPotential')
    options.(DeleteOptionsV.IgnoreStoreReadErrorWithClusterBreakingPotential') dq)
    with "[Hdeepown_ignorestorereaderror_some]" as "Hflag".
  { destruct options.(DeleteOptionsV.IgnoreStoreReadErrorWithClusterBreakingPotential') as [enabled|].
    - iDestruct "Hdeepown_ignorestorereaderror_some" as (enabled_c) "[Hflag ->]". done.
    - rewrite /ptr.opt_ptr_rep. iPureIntro. apply Hdeepown_ignorestorereaderror_none. done. }
  wp_apply (ptr.wp_Deref_bool with "Hflag"). iIntros "Hflag".
  iAssert ((match options.(DeleteOptionsV.IgnoreStoreReadErrorWithClusterBreakingPotential') with
    | Some enabled => ∃ enabled_c,
        c.(v1.DeleteOptions.IgnoreStoreReadErrorWithClusterBreakingPotential') ↦{dq} enabled_c ∗
        ⌜ enabled_c = enabled ⌝
    | None => True%I
    end)%I) with "[Hflag]" as "Hdeepown_ignorestorereaderror_some".
  { destruct options.(DeleteOptionsV.IgnoreStoreReadErrorWithClusterBreakingPotential') as [enabled|];
      rewrite /ptr.opt_ptr_rep; iFrame; done. }
  destruct options.(DeleteOptionsV.IgnoreStoreReadErrorWithClusterBreakingPotential')
    as [[|]|] eqn:Hflag; wp_auto.
  - destruct Hvalid as [_ [_ Hignore]].
    destruct (Hignore Hflag) as (Hdry & Hpolicy & Horphan & Hgrace & Hpreconditions).
    iDestruct (own_slice_len with "Hdeepown_dryrun") as %[Hlen Hlen_nonneg].
    assert (slice.len c.(v1.DeleteOptions.DryRun') = W64 0) as Hlen_zero.
    { rewrite Hdry in Hlen. simpl in Hlen. word. }
    assert (c.(v1.DeleteOptions.PropagationPolicy') = null) as Hpolicy_null by tauto.
    assert (c.(v1.DeleteOptions.OrphanDependents') = null) as Horphan_null by tauto.
    assert (c.(v1.DeleteOptions.GracePeriodSeconds') = null) as Hgrace_null by tauto.
    assert (c.(v1.DeleteOptions.Preconditions') = null) as Hpreconditions_null by tauto.
    rewrite Hlen_zero. wp_auto.
    rewrite Hpolicy_null. wp_auto.
    rewrite Horphan_null. wp_auto.
    rewrite Hgrace_null. wp_auto.
    rewrite Hpreconditions_null. wp_auto.
    iApply "HΦ". iFrame "Herrs Hcap". iExists c. iFrame "Hoptions".
    rewrite /DeleteOptionsV.deepown Hflag ?Hpolicy_null ?Horphan_null ?Hgrace_null ?Hpreconditions_null.
    iFrame. done.
  - iApply "HΦ". iFrame "Herrs Hcap". iExists c. iFrame "Hoptions".
    rewrite /DeleteOptionsV.deepown Hflag ?Hpolicy_null ?Horphan_null ?Hgrace_null ?Hpreconditions_null.
    iFrame. done.
  - iApply "HΦ". iFrame "Herrs Hcap". iExists c. iFrame "Hoptions".
    rewrite /DeleteOptionsV.deepown Hflag ?Hpolicy_null ?Horphan_null ?Hgrace_null ?Hpreconditions_null.
    iFrame. done.
Qed.

Lemma wp_ValidateDeleteOptions_valid l options dq :
  {{{ is_pkg_init code.k8s_io.apimachinery.pkg.apis.meta.v1.validation.pkg_id.validation ∗
      DeleteOptionsV.deepown_l l options dq ∗
      ⌜ DeleteOptionsV.valid options ⌝
  }}}
    @! metav1_validation.ValidateDeleteOptions #l
  {{{ (errs : field.ErrorList.t), RET #errs;
      ⌜ errs.(slice.len) = W64 0 ⌝ ∗
      DeleteOptionsV.deepown_l l options dq
  }}}.
Proof.
  wp_start as "[Hoptions %Hvalid]".
  iDestruct "Hoptions" as (c) "[Hoptions Hdeepown]". iNamed "Hdeepown".
  wp_auto.
  wp_apply wp_slice_literal. iSplitR; first done.
  iIntros (errs) "[Herrs Hcap]". wp_auto.
  pose proof Hvalid as [Hpolicy [Hdry Hignore]].
  assert (bool_decide (c.(v1.DeleteOptions.OrphanDependents') = null) =
    bool_decide (options.(DeleteOptionsV.OrphanDependents') = None)) as Horphan_bool.
  { apply bool_decide_ext. exact Hdeepown_orphandependents_none. }
  assert (bool_decide (c.(v1.DeleteOptions.PropagationPolicy') = null) =
    bool_decide (options.(DeleteOptionsV.PropagationPolicy') = None)) as Hpolicy_bool.
  { apply bool_decide_ext. exact Hdeepown_propagationpolicy_none. }
  destruct options.(DeleteOptionsV.OrphanDependents') as [orphan|] eqn:Horphan;
    destruct options.(DeleteOptionsV.PropagationPolicy') as [policy|] eqn:Hpolicy_opt;
    try contradiction.
  all: rewrite ?Horphan_bool ?Hpolicy_bool /=; wp_auto.
  all: try (rewrite Hpolicy_bool /=; wp_auto).
  all: try (rewrite Hpolicy_bool /=; wp_auto).
  all: try (iDestruct "Hdeepown_propagationpolicy_some" as (policy_c) "[Hpolicy ->]";
    destruct Hpolicy as [-> | [-> | ->]]; wp_auto).
  all: try (iAssert ((match options.(DeleteOptionsV.PropagationPolicy') with
    | Some policy => ∃ policy_c,
        c.(v1.DeleteOptions.PropagationPolicy') ↦{dq} policy_c ∗ ⌜ policy_c = policy ⌝
    | None => True%I
    end)%I) with "[Hpolicy]" as "Hdeepown_propagationpolicy_some";
    [rewrite Hpolicy_opt; iFrame; done|]).
  all: wp_apply wp_NewPath_single; iIntros (path) "_"; wp_auto.
  all: wp_apply (wp_ValidateDryRun_valid with "[$Hdeepown_dryrun]"); first done.
  all: iIntros (dry_errs) "(Hdry_errs & Hdry_cap & Hdeepown_dryrun)"; wp_auto.
  all: wp_apply (wp_slice_append with "[$Herrs $Hcap $Hdry_errs]");
    iIntros (errs') "(Herrs & Hcap & _)"; wp_auto.
  all: wp_apply wp_NewPath_single; iIntros (path') "_"; wp_auto.
  all: wp_apply (wp_ValidateIgnoreStoreReadError_valid path' l options dq with
    "[Hoptions Hdeepown_graceperiodseconds_some
    Hdeepown_preconditions_some Hdeepown_orphandependents_some Hdeepown_propagationpolicy_some
    Hdeepown_ignorestorereaderror_some Hdeepown_dryrun Hdeepown_dryrun_cap]").
  all: try (iFrame "#"; iSplitL; last (iPureIntro; exact Hvalid);
    iExists c; iFrame "Hoptions"; rewrite /DeleteOptionsV.deepown Horphan Hpolicy_opt; iFrame; done).
  all: iIntros (ignore_errs) "(Hignore_errs & Hignore_cap & Hoptions)"; wp_auto.
  all: wp_apply (wp_slice_append with "[$Herrs $Hcap $Hignore_errs]");
    iIntros (result) "(Herrs & Hcap & _)"; wp_auto.
  all: iDestruct (own_slice_len with "Herrs") as %[Hlen Hlen_nonneg].
  all: iApply "HΦ"; iFrame; iPureIntro; simpl in Hlen; word.
Qed.

End proof.
