From New.proof Require Import prelude empty_ffi.
From New.proof.kubernetes_model Require Export delete.
From New.proof.kubernetes_model Require Import get.
From New.proof.k8s_io.apimachinery.pkg.api Require Import errors.
From iris.bi.lib Require Import atomic.

Section proof.
Context `{hG: !heapGS Σ} `{!ffi_semantics _ _}.
Context {sem : go.Semantics} {package_sem : apimodel.Assumptions}.
Collection W := sem + package_sem.
Context `{!kubernetesModelG Σ}.
Local Set Default Proof Using "All".

Definition precondition_uid_mismatch (options : DeleteOptionsV.t) (metadata : ObjectMetaV.t) : bool :=
  match options.(DeleteOptionsV.Preconditions') with
  | Some preconditions =>
      match preconditions.(PreconditionsV.UID') with
      | Some uid => bool_decide (uid ≠ metadata.(ObjectMetaV.UID'))
      | None => false
      end
  | None => false
  end.

Lemma wp_preconditionUIDMismatch options_c options metadata_i metadata_l metadata dq :
  {{{ is_pkg_init apimodel ∗
      "%Hmetadata_i" ∷ ⌜ metadata_i = interface.mk (go.PointerType v1.ObjectMeta) #metadata_l ⌝ ∗
      "Hdeepown_options" ∷ DeleteOptionsV.deepown options_c options dq ∗
      "Hdeepown_metadata" ∷ ObjectMetaV.deepown_l metadata_l metadata dq
  }}}
    @! apimodel.preconditionUIDMismatch #options_c #(interface.ok metadata_i)
  {{{ mismatch, RET #mismatch;
      "%Hmismatch" ∷ ⌜ mismatch = precondition_uid_mismatch options metadata ⌝ ∗
      "Hdeepown_options" ∷ DeleteOptionsV.deepown options_c options dq ∗
      "Hdeepown_metadata" ∷ ObjectMetaV.deepown_l metadata_l metadata dq
  }}}.
Proof.
  wp_start as "H".
  iNamed "H". subst metadata_i.
  iNamed "Hdeepown_options".
  destruct options.(DeleteOptionsV.Preconditions') as [preconditions|] eqn:Hpreconditions.
  - iDestruct "Hdeepown_preconditions_some" as (preconditions_c)
      "[Hpreconditions_l Hdeepown_preconditions]".
    iNamed "Hdeepown_preconditions".
    assert (v1.DeleteOptions.Preconditions' options_c ≠ null) as Hpreconditions_not_null.
    { intros Hnull. apply (proj1 Hdeepown_preconditions_none) in Hnull. congruence. }
    assert (bool_decide (v1.DeleteOptions.Preconditions' options_c = null) = false)
      as Hpreconditions_nonnull_decide.
    { apply bool_decide_false. done. }
    wp_auto.
    rewrite Hpreconditions_nonnull_decide /=.
    wp_auto.
    destruct preconditions.(PreconditionsV.UID') as [uid|] eqn:Huid.
    + iDestruct "Hdeepown_uid_some" as (uid_c) "[Huid_l ->]".
      assert (v1.Preconditions.UID' preconditions_c ≠ null) as Huid_not_null.
      { intros Hnull. apply (proj1 Hdeepown_uid_none) in Hnull. congruence. }
      assert (bool_decide (v1.Preconditions.UID' preconditions_c = null) = false)
        as Huid_nonnull_decide.
      { apply bool_decide_false. done. }
      rewrite Huid_nonnull_decide /=.
      wp_auto.
      wp_apply (v1.wp_GetUID_deepown with "[$Hdeepown_metadata]").
      iIntros "Hdeepown_metadata".
      destruct (decide (uid = metadata.(ObjectMetaV.UID'))) as [Huid_eq|Huid_neq].
      * rewrite Huid_eq.
        wp_auto.
        iAssert ((match preconditions.(PreconditionsV.UID') with
          | Some vu => ∃ cu, v1.Preconditions.UID' preconditions_c ↦{dq} cu ∗ ⌜ cu = vu ⌝
          | None => True
          end)%I) with "[Huid_l]" as "Hdeepown_uid_some".
        { rewrite Huid /=. iExists metadata.(ObjectMetaV.UID'). iFrame. done. }
        iAssert (PreconditionsV.deepown preconditions_c preconditions dq)
          with "[Hdeepown_uid_some Hdeepown_resourceversion_some]" as "Hdeepown_preconditions".
        { rewrite /PreconditionsV.deepown Huid /=. iFrame. iPureIntro. done. }
        iAssert ((match options.(DeleteOptionsV.Preconditions') with
          | Some vp =>
              ∃ cp, v1.DeleteOptions.Preconditions' options_c ↦{dq} cp ∗
                PreconditionsV.deepown cp vp dq
          | None => True
          end)%I) with "[Hpreconditions_l Hdeepown_preconditions]"
          as "Hdeepown_preconditions_some".
        { rewrite Hpreconditions /=. iExists preconditions_c. iFrame. }
        iAssert (DeleteOptionsV.deepown options_c options dq)
          with "[Hdeepown_graceperiodseconds_some Hdeepown_preconditions_some Hdeepown_orphandependents_some Hdeepown_propagationpolicy_some]"
          as "Hdeepown_options".
        { rewrite /DeleteOptionsV.deepown Hpreconditions /=. iFrame. iPureIntro. done. }
        iApply "HΦ". iFrame. iPureIntro.
        rewrite /precondition_uid_mismatch Hpreconditions Huid /=.
        rewrite Huid_eq.
        replace (bool_decide (ObjectMetaV.UID' metadata = ObjectMetaV.UID' metadata)) with true
          by (symmetry; apply bool_decide_true; done).
        replace (bool_decide (ObjectMetaV.UID' metadata ≠ ObjectMetaV.UID' metadata)) with false
          by (symmetry; apply bool_decide_false; intros Hneq; apply Hneq; done).
        done.
      * wp_auto.
        iAssert ((match preconditions.(PreconditionsV.UID') with
          | Some vu => ∃ cu, v1.Preconditions.UID' preconditions_c ↦{dq} cu ∗ ⌜ cu = vu ⌝
          | None => True
          end)%I) with "[Huid_l]" as "Hdeepown_uid_some".
        { rewrite Huid /=. iExists uid. iFrame. done. }
        iAssert (PreconditionsV.deepown preconditions_c preconditions dq)
          with "[Hdeepown_uid_some Hdeepown_resourceversion_some]" as "Hdeepown_preconditions".
        { rewrite /PreconditionsV.deepown Huid /=. iFrame. iPureIntro. done. }
        iAssert ((match options.(DeleteOptionsV.Preconditions') with
          | Some vp =>
              ∃ cp, v1.DeleteOptions.Preconditions' options_c ↦{dq} cp ∗
                PreconditionsV.deepown cp vp dq
          | None => True
          end)%I) with "[Hpreconditions_l Hdeepown_preconditions]"
          as "Hdeepown_preconditions_some".
        { rewrite Hpreconditions /=. iExists preconditions_c. iFrame. }
        iAssert (DeleteOptionsV.deepown options_c options dq)
          with "[Hdeepown_graceperiodseconds_some Hdeepown_preconditions_some Hdeepown_orphandependents_some Hdeepown_propagationpolicy_some]"
          as "Hdeepown_options".
        { rewrite /DeleteOptionsV.deepown Hpreconditions /=. iFrame. iPureIntro. done. }
        iApply "HΦ". iFrame. iPureIntro.
        rewrite /precondition_uid_mismatch Hpreconditions Huid /=.
        replace (bool_decide (uid = ObjectMetaV.UID' metadata)) with false
          by (symmetry; apply bool_decide_false; done).
        replace (bool_decide (uid ≠ ObjectMetaV.UID' metadata)) with true
          by (symmetry; apply bool_decide_true; done).
        done.
    + assert (v1.Preconditions.UID' preconditions_c = null) as Huid_null.
      { apply (proj2 Hdeepown_uid_none). done. }
      assert (bool_decide (v1.Preconditions.UID' preconditions_c = null) = true)
        as Huid_null_decide.
      { apply bool_decide_true. done. }
      rewrite Huid_null_decide /=.
      wp_auto.
      iAssert (PreconditionsV.deepown preconditions_c preconditions dq)
        with "[Hdeepown_resourceversion_some]" as "Hdeepown_preconditions".
      { rewrite /PreconditionsV.deepown Huid /=. iFrame. iPureIntro. done. }
      iAssert ((match options.(DeleteOptionsV.Preconditions') with
        | Some vp =>
            ∃ cp, v1.DeleteOptions.Preconditions' options_c ↦{dq} cp ∗
              PreconditionsV.deepown cp vp dq
        | None => True
        end)%I) with "[Hpreconditions_l Hdeepown_preconditions]"
        as "Hdeepown_preconditions_some".
      { rewrite Hpreconditions /=. iExists preconditions_c. iFrame. }
      iAssert (DeleteOptionsV.deepown options_c options dq)
        with "[Hdeepown_graceperiodseconds_some Hdeepown_preconditions_some Hdeepown_orphandependents_some Hdeepown_propagationpolicy_some]"
        as "Hdeepown_options".
      { rewrite /DeleteOptionsV.deepown Hpreconditions /=. iFrame. iPureIntro. done. }
      iApply "HΦ". iFrame. iPureIntro.
      rewrite /precondition_uid_mismatch Hpreconditions Huid /=. done.
  - assert (v1.DeleteOptions.Preconditions' options_c = null) as Hpreconditions_null.
    { apply (proj2 Hdeepown_preconditions_none). done. }
    assert (bool_decide (v1.DeleteOptions.Preconditions' options_c = null) = true)
      as Hpreconditions_null_decide.
    { apply bool_decide_true. done. }
    wp_auto.
    rewrite Hpreconditions_null_decide /=.
    wp_auto.
    iAssert (DeleteOptionsV.deepown options_c options dq)
      with "[Hdeepown_graceperiodseconds_some Hdeepown_preconditions_some Hdeepown_orphandependents_some Hdeepown_propagationpolicy_some]"
      as "Hdeepown_options".
    { rewrite /DeleteOptionsV.deepown Hpreconditions /=. iFrame. iPureIntro. done. }
    iApply "HΦ". iFrame. iPureIntro.
    rewrite /precondition_uid_mismatch Hpreconditions /=. done.
Qed.

Definition delete_tx_preconditions_with_rv (options : DeleteOptionsV.t) (rv : go_string) :
    PreconditionsV.t :=
  match options.(DeleteOptionsV.Preconditions') with
  | None => {|
      PreconditionsV.UID' := None;
      PreconditionsV.ResourceVersion' := Some rv;
    |}
  | Some preconditions =>
      preconditions <| PreconditionsV.ResourceVersion' := Some rv |>
  end.

Definition delete_tx_options_with_rv (options : DeleteOptionsV.t) (rv : go_string) :
    DeleteOptionsV.t :=
  options <| DeleteOptionsV.Preconditions' :=
    Some (delete_tx_preconditions_with_rv options rv) |>.

Axiom delete_tx_options_with_rv_valid :
  ∀ options rv,
    DeleteOptionsV.valid options →
    DeleteOptionsV.valid (delete_tx_options_with_rv options rv).

Lemma delete_tx_options_with_rv_preconditions_match_uid options rv uid :
  delete_preconditions_match_uid options uid →
  delete_preconditions_match_uid (delete_tx_options_with_rv options rv) uid.
Proof.
  rewrite /delete_preconditions_match_uid /delete_tx_options_with_rv
    /delete_tx_preconditions_with_rv.
  destruct options.(DeleteOptionsV.Preconditions') as [preconditions|]; [|done].
  destruct preconditions as [uid_o rv_o].
  simpl.
  destruct uid_o; done.
Qed.

Lemma delete_tx_options_with_rv_preconditions_match_uid_iff options rv uid :
  delete_preconditions_match_uid (delete_tx_options_with_rv options rv) uid ↔
  delete_preconditions_match_uid options uid.
Proof.
  rewrite /delete_preconditions_match_uid /delete_tx_options_with_rv
    /delete_tx_preconditions_with_rv.
  destruct options.(DeleteOptionsV.Preconditions') as [preconditions|]; [|done].
  destruct preconditions as [uid_o rv_o].
  simpl.
  destruct uid_o; done.
Qed.

Lemma delete_tx_options_with_rv_preconditions_resource_version_not_none options rv :
  ¬ delete_options_preconditions_resource_version_none (delete_tx_options_with_rv options rv).
Proof.
  rewrite /delete_options_preconditions_resource_version_none /delete_tx_options_with_rv
    /delete_tx_preconditions_with_rv.
  destruct options.(DeleteOptionsV.Preconditions') as [[uid_o rv_o]|]; simpl; congruence.
Qed.

Lemma precondition_uid_mismatch_false options metadata uid :
  delete_preconditions_match_uid options uid →
  uid = metadata.(ObjectMetaV.UID') →
  precondition_uid_mismatch options metadata = false.
Proof.
  rewrite /delete_preconditions_match_uid /precondition_uid_mismatch.
  destruct options.(DeleteOptionsV.Preconditions') as [preconditions|]; [|done].
  destruct preconditions.(PreconditionsV.UID') as [precondition_uid|]; [|done].
  intros Hmatch Huid_eq.
  rewrite Hmatch Huid_eq.
  apply bool_decide_eq_false_2.
  intros Hneq. apply Hneq. done.
Qed.

Lemma wp_setPreconditionResourceVersion options_l options metadata_i metadata_l metadata :
  {{{ is_pkg_init apimodel ∗
      "%Hmetadata_i" ∷ ⌜ metadata_i = interface.mk (go.PointerType v1.ObjectMeta) #metadata_l ⌝ ∗
      "Hdeepown_options_l" ∷ DeleteOptionsV.deepown_l options_l options 1 ∗
      "Hdeepown_metadata" ∷ ObjectMetaV.deepown_l metadata_l metadata 1 }}}
    @! apimodel.setPreconditionResourceVersion #options_l #(interface.ok metadata_i)
  {{{ RET #();
      "Hdeepown_options_l" ∷ DeleteOptionsV.deepown_l options_l
        (delete_tx_options_with_rv options metadata.(ObjectMetaV.ResourceVersion')) 1 ∗
      "Hdeepown_metadata" ∷ ObjectMetaV.deepown_l metadata_l metadata 1 }}}.
Proof.
  wp_start as "H".
  iNamed "H". subst metadata_i.
  iDestruct "Hdeepown_options_l" as (options_c) "[Hoptions_l Hdeepown_options]".
  iNamed "Hdeepown_options".
  wp_auto.
  wp_apply (v1.wp_GetResourceVersion_deepown with "[$Hdeepown_metadata]").
  iIntros "Hdeepown_metadata".
  wp_auto.
  iAssert (⌜ rv_ptr ≠ null ⌝%I) as "%Hrv_ptr_not_null".
  { iDestruct (typed_pointsto_not_null with "rv") as %Hrv_ptr_not_null'. done. }
  destruct options.(DeleteOptionsV.Preconditions') as [preconditions|] eqn:Hpreconditions.
  - iDestruct "Hdeepown_preconditions_some" as (preconditions_c)
      "[Hpreconditions_l Hdeepown_preconditions]".
    iNamed "Hdeepown_preconditions".
    assert (v1.DeleteOptions.Preconditions' options_c ≠ null) as Hpreconditions_not_null.
    { intros Hnull.
      apply (proj1 Hdeepown_preconditions_none) in Hnull.
      congruence. }
    assert (bool_decide (v1.DeleteOptions.Preconditions' options_c = null) = false)
      as Hpreconditions_nonnull_decide.
    { apply bool_decide_false. done. }
    destruct preconditions.(PreconditionsV.UID') as [uid|] eqn:Huid.
    + iDestruct "Hdeepown_uid_some" as (uid_c) "[Huid_l ->]".
      rewrite Hpreconditions_nonnull_decide.
      wp_auto.
      iAssert (PreconditionsV.deepown
        (preconditions_c <| v1.Preconditions.ResourceVersion' := rv_ptr |>)
        (preconditions <| PreconditionsV.ResourceVersion' :=
          Some metadata.(ObjectMetaV.ResourceVersion') |>) 1)%I
        with "[Huid_l rv]" as "Hdeepown_preconditions".
      { rewrite /PreconditionsV.deepown Huid /=.
        iFrame. iPureIntro.
        split; first done.
        split; first done.
        split; last done.
        split; [intros Hnull; exfalso; apply Hrv_ptr_not_null; done|intros Hnone; congruence]. }
      iAssert ((match (delete_tx_options_with_rv options
          metadata.(ObjectMetaV.ResourceVersion')).(DeleteOptionsV.Preconditions') with
        | Some preconditions_v =>
            ∃ preconditions_c',
              (options_c.(v1.DeleteOptions.Preconditions') ↦ preconditions_c') ∗
              PreconditionsV.deepown preconditions_c' preconditions_v 1
        | None => True
        end)%I) with "[Hpreconditions_l Hdeepown_preconditions]" as
        "Hdeepown_preconditions_some".
      { rewrite /delete_tx_options_with_rv /delete_tx_preconditions_with_rv
          Hpreconditions /=.
        iExists (preconditions_c <| v1.Preconditions.ResourceVersion' := rv_ptr |>).
        iFrame. }
      iAssert (DeleteOptionsV.deepown_l options_l
        (delete_tx_options_with_rv options metadata.(ObjectMetaV.ResourceVersion')) 1)%I
        with "[Hoptions_l Hdeepown_graceperiodseconds_some Hdeepown_preconditions_some Hdeepown_orphandependents_some Hdeepown_propagationpolicy_some]"
        as "Hdeepown_options_l".
      { iExists options_c. iFrame "Hoptions_l".
        rewrite /DeleteOptionsV.deepown /delete_tx_options_with_rv
          /delete_tx_preconditions_with_rv Hpreconditions /=.
        iFrame. iFrame "%".
        iPureIntro.
        split; [intros Hnull; exfalso; apply Hpreconditions_not_null; done|intros Hnone; congruence]. }
      iApply "HΦ". iFrame.
    + rewrite Hpreconditions_nonnull_decide.
      wp_auto.
      iAssert (PreconditionsV.deepown
        (preconditions_c <| v1.Preconditions.ResourceVersion' := rv_ptr |>)
        (preconditions <| PreconditionsV.ResourceVersion' :=
          Some metadata.(ObjectMetaV.ResourceVersion') |>) 1)%I
        with "[rv]" as "Hdeepown_preconditions".
      { rewrite /PreconditionsV.deepown Huid /=.
        iFrame. iPureIntro.
        split; first done.
        split; last done.
        split; [intros Hnull; exfalso; apply Hrv_ptr_not_null; done|intros Hnone; congruence]. }
      iAssert ((match (delete_tx_options_with_rv options
          metadata.(ObjectMetaV.ResourceVersion')).(DeleteOptionsV.Preconditions') with
        | Some preconditions_v =>
            ∃ preconditions_c',
              (options_c.(v1.DeleteOptions.Preconditions') ↦ preconditions_c') ∗
              PreconditionsV.deepown preconditions_c' preconditions_v 1
        | None => True
        end)%I) with "[Hpreconditions_l Hdeepown_preconditions]" as
        "Hdeepown_preconditions_some".
      { rewrite /delete_tx_options_with_rv /delete_tx_preconditions_with_rv
          Hpreconditions /=.
        iExists (preconditions_c <| v1.Preconditions.ResourceVersion' := rv_ptr |>).
        iFrame. }
      iAssert (DeleteOptionsV.deepown_l options_l
        (delete_tx_options_with_rv options metadata.(ObjectMetaV.ResourceVersion')) 1)%I
        with "[Hoptions_l Hdeepown_graceperiodseconds_some Hdeepown_preconditions_some Hdeepown_orphandependents_some Hdeepown_propagationpolicy_some]"
        as "Hdeepown_options_l".
      { iExists options_c. iFrame "Hoptions_l".
        rewrite /DeleteOptionsV.deepown /delete_tx_options_with_rv
          /delete_tx_preconditions_with_rv Hpreconditions /=.
        iFrame. iFrame "%".
        iPureIntro.
        split; [intros Hnull; exfalso; apply Hpreconditions_not_null; done|intros Hnone; congruence]. }
      iApply "HΦ". iFrame.
  - assert (v1.DeleteOptions.Preconditions' options_c = null) as Hpreconditions_null.
    { apply (proj2 Hdeepown_preconditions_none).
      done. }
    assert (bool_decide (v1.DeleteOptions.Preconditions' options_c = null) = true)
      as Hpreconditions_null_decide.
    { apply bool_decide_true. done. }
    rewrite Hpreconditions_null_decide.
    wp_auto.
    wp_alloc preconditions_ptr as "Hpreconditions_l".
    wp_auto.
    iClear "Hdeepown_preconditions_some".
    iAssert (⌜ preconditions_ptr ≠ null ⌝%I) as "%Hpreconditions_ptr_not_null".
    { iDestruct (typed_pointsto_not_null with "Hpreconditions_l") as %Hpreconditions_ptr_not_null'. done. }
    iAssert (PreconditionsV.deepown
      (v1.Preconditions.mk null rv_ptr)
      (delete_tx_preconditions_with_rv options metadata.(ObjectMetaV.ResourceVersion')) 1)%I
      with "[rv]" as "Hdeepown_preconditions".
    { rewrite /PreconditionsV.deepown /delete_tx_preconditions_with_rv
        Hpreconditions /=.
      iFrame. iPureIntro.
      split; first done.
      split; last done.
      split; [intros Hnull; exfalso; apply Hrv_ptr_not_null; done|intros Hnone; congruence]. }
    iAssert ((match (delete_tx_options_with_rv options
        metadata.(ObjectMetaV.ResourceVersion')).(DeleteOptionsV.Preconditions') with
      | Some preconditions_v =>
          ∃ preconditions_c',
            ((options_c <| v1.DeleteOptions.Preconditions' := preconditions_ptr |>)
              .(v1.DeleteOptions.Preconditions') ↦ preconditions_c') ∗
            PreconditionsV.deepown preconditions_c' preconditions_v 1
      | None => True
      end)%I) with "[Hpreconditions_l Hdeepown_preconditions]" as
      "Hdeepown_preconditions_some".
    { rewrite /delete_tx_options_with_rv /delete_tx_preconditions_with_rv
        Hpreconditions /=.
      iExists (v1.Preconditions.mk null rv_ptr).
      iFrame. }
    iAssert (DeleteOptionsV.deepown_l options_l
      (delete_tx_options_with_rv options metadata.(ObjectMetaV.ResourceVersion')) 1)%I
      with "[Hoptions_l Hdeepown_graceperiodseconds_some Hdeepown_preconditions_some Hdeepown_orphandependents_some Hdeepown_propagationpolicy_some]"
      as "Hdeepown_options_l".
    { iExists (options_c <| v1.DeleteOptions.Preconditions' := preconditions_ptr |>).
      iFrame "Hoptions_l".
      rewrite /DeleteOptionsV.deepown /delete_tx_options_with_rv
        /delete_tx_preconditions_with_rv Hpreconditions /=.
      iFrame. iFrame "%".
      iPureIntro.
      split; [intros Hnull; exfalso; apply Hpreconditions_ptr_not_null; done|intros Hnone; congruence]. }
    iApply "HΦ". iFrame.
Qed.

Lemma wp_State__deleteTx_au γ l key options_c options:
  ∀ Φ,
    is_pkg_init apimodel ∗
    is_kubernetes γ l ∗
    "Hdeepown_options" ∷ DeleteOptionsV.deepown options_c options 1 ∗
    "%Hvalid_options" ∷ ⌜ DeleteOptionsV.valid options ⌝ ∗
    "Hau" ∷ AU <{ ∃∃ uid kmeta parent_key parent_uid children phase,
      "%Hkey_in" ∷ ⌜ key ∈ children ⌝ ∗
      "%Hdelete_preconditions_uid" ∷ ⌜ delete_preconditions_match_uid options uid ⌝ ∗
      "Hown_meta_frag" ∷ own_meta_frag γ key uid 1 kmeta ∗
      "#Hown_unreserved_key_frag" ∷ own_unreserved_key_frag γ key ∗
      "Hown_children_frag" ∷ own_children_frag γ parent_key parent_uid 1 children ∗
      "Hown_terminating_children_frag" ∷ own_terminating_children_frag γ parent_key parent_uid phase
    }> @ ⊤, ∅ <{ ∀∀ (_ : unit),
      "Hown_children_frag" ∷ own_children_frag γ parent_key parent_uid 1 (children ∖ {[key]}) ∗
      "Hdeletion_observed_frag" ∷ own_deletion_observed_frag γ key uid ∗
      "Hown_terminating_children_frag" ∷ own_terminating_children_frag γ parent_key parent_uid Mutable,
      COMM ▷ Φ #interface.nil
    }>
    -∗ WP l @! (go.PointerType apimodel.State) @! "deleteTx" #key #options_c {{ Φ }}.
Proof.
  iIntros (Φ) "(#Hinit & #Hkinv & H)".
  iNamed "H".
  wp_method_call. rewrite /apimodel.State__deleteTxⁱᵐᵖˡ. wp_call. wp_auto.
  set I := (∃ options_c_orig,
    "Hoptions_ptr" ∷ options_ptr ↦ options_c_orig ∗
    "Hdeepown_options_orig" ∷ DeleteOptionsV.deepown options_c_orig options 1 ∗
    "Hau" ∷ AU <{ ∃∃ uid kmeta parent_key parent_uid children phase,
      "%Hkey_in" ∷ ⌜ key ∈ children ⌝ ∗
      "%Hdelete_preconditions_uid" ∷ ⌜ delete_preconditions_match_uid options uid ⌝ ∗
      "Hown_meta_frag" ∷ own_meta_frag γ key uid 1 kmeta ∗
      "#Hown_unreserved_key_frag" ∷ own_unreserved_key_frag γ key ∗
      "Hown_children_frag" ∷ own_children_frag γ parent_key parent_uid 1 children ∗
      "Hown_terminating_children_frag" ∷ own_terminating_children_frag γ parent_key parent_uid phase
    }> @ ⊤, ∅ <{ ∀∀ (_ : unit),
      "Hown_children_frag" ∷ own_children_frag γ parent_key parent_uid 1 (children ∖ {[key]}) ∗
      "Hdeletion_observed_frag" ∷ own_deletion_observed_frag γ key uid ∗
      "Hown_terminating_children_frag" ∷ own_terminating_children_frag γ parent_key parent_uid Mutable,
      COMM ▷ Φ #interface.nil
    }>
  )%I.
  iAssert I with "[options Hdeepown_options Hau]" as "Hloop_inv".
  { iExists options_c. iFrame. }
  wp_for "Hloop_inv".
  wp_apply (wp_DeleteOptions__DeepCopy with
    "[Hoptions_ptr Hdeepown_options_orig]").
  { iFrame. }
  iIntros (options_copy_ptr) "[(%options_c_copy & Hoptions_copy_ptr & Hdeepown_options_copy)
    (%options_c' & Hoptions_ptr & Hdeepown_options_orig)]".
  wp_auto.
  wp_apply (wp_State__get_some_au γ l key).
  iFrame "#".
  iMod "Hau" as (uid kmeta parent_key parent_uid children phase) "[Hau_pre Hclose]".
  iNamed "Hau_pre".
  iDestruct "Hclose" as "[Habort _]".
  iModIntro.
  iExists uid, (DfracOwn 1), kmeta, None, None.
  iFrame "Hown_meta_frag".
  iSplit; first done.
  iSplit; first done.
  iIntros (i kobj) "Hget".
  iDestruct "Hget" as "(%Hvalid_kobj & %Hkey_eq & %Hmeta_eq & Hdeepown_i & Hown_meta_frag & _ & _)".
  iPoseProof (kview.own_meta_valid with "Hown_meta_frag") as "%Hmeta_valid".
  iMod ("Habort" with "[Hown_meta_frag Hown_children_frag Hown_terminating_children_frag]") as "Hau".
  { iFrame "Hown_unreserved_key_frag". iFrame. iFrame "%". }
  iModIntro. iNext. wp_auto.
  iDestruct "Hdeepown_i" as (kobj_l) "[%Hvalid_interface Hdeepown_l]".
  wp_apply wp_Accessor. 1: iPureIntro; done.
  iPoseProof (KObjectV.deepown_l_split with "Hdeepown_l") as
    "(%Hkobj_l_not_null & Htypemeta & Hdeepown_metadata & Hdeepown_spec & Hdeepown_status)".
  destruct Hmeta_valid as (_ & _ & Huid_kmeta & _ & _).
  assert (Huid_kobj : uid = (KObjectV.objectmeta kobj).(ObjectMetaV.UID')).
  { rewrite Huid_kmeta.
    symmetry. apply (ObjectMetaV.equiv_except_resource_version_uid _ _ Hmeta_eq). }
  assert (Hprecondition_uid_mismatch_false :
    precondition_uid_mismatch options (KObjectV.objectmeta kobj) = false).
  { eapply precondition_uid_mismatch_false; done. }
  wp_apply (wp_preconditionUIDMismatch with
    "[$Hinit $Hdeepown_options_copy $Hdeepown_metadata]").
  { done. }
  iIntros (mismatch) "(%Hmismatch & Hdeepown_options_copy & Hdeepown_metadata)".
  rewrite Hmismatch Hprecondition_uid_mismatch_false.
  wp_auto.
  wp_apply (wp_setPreconditionResourceVersion with
    "[optionsCopy Hdeepown_options_copy Hdeepown_metadata]").
  { iFrame "#".
    iSplit; first done.
    iSplitL "optionsCopy Hdeepown_options_copy".
    { iExists options_c_copy. iFrame. }
    iFrame. }
  iIntros "Hpost".
  iNamed "Hpost".
  iDestruct "Hdeepown_options_l" as (options_c_rv) "[optionsCopy Hdeepown_options_rv]".
  set (options_rv :=
    delete_tx_options_with_rv options
      (ObjectMetaV.ResourceVersion' (KObjectV.objectmeta kobj))).
  assert (Hvalid_options_rv : DeleteOptionsV.valid options_rv).
  { apply delete_tx_options_with_rv_valid. done. }
  assert (Hdelete_preconditions_uid_rv :
    delete_preconditions_match_uid options_rv uid).
  { subst options_rv.
    apply delete_tx_options_with_rv_preconditions_match_uid.
    done. }
  assert (Hdelete_preconditions_uid_equiv_rv :
    ∀ uid',
      delete_preconditions_match_uid options_rv uid' ↔
      delete_preconditions_match_uid options uid').
  { intros uid'.
    subst options_rv.
    apply delete_tx_options_with_rv_preconditions_match_uid_iff. }
  wp_auto.
  wp_apply (wp_State__delete_au γ l key options_c_rv options_rv).
  iFrame "#".
  iFrame "Hdeepown_options_rv".
  iSplit; first done.
  iMod "Hau" as (uid' kmeta' parent_key' parent_uid' children' phase') "[Hau_pre Hclose]".
  iRename "Hown_unreserved_key_frag" into "Hown_unreserved_key_frag_outer".
  iNamed "Hau_pre".
  iModIntro.
  iExists uid', kmeta', parent_key', parent_uid', children', phase'.
  iFrame "Hown_meta_frag Hown_children_frag Hown_terminating_children_frag".
  iSplit; first done.
  iSplit.
  { iPureIntro.
    apply (proj2 (Hdelete_preconditions_uid_equiv_rv uid')).
    done. }
  destruct (decide (delete_options_preconditions_resource_version_none options_rv))
    as [Hrv_none|Hrv_some].
  { exfalso.
    subst options_rv.
    apply delete_tx_options_with_rv_preconditions_resource_version_not_none in Hrv_none.
    done. }
  iIntros (err') "Hdelete_post".
  iDestruct "Hdelete_post" as "[Hsuccess|Hconflict]".
  - iDestruct "Hsuccess" as "[%Herr Hpost]". subst err'.
    iDestruct "Hclose" as "[_ Hcommit]".
    iMod ("Hcommit" $! tt with "Hpost") as "HΦ".
    iModIntro. iNext.
    wp_auto.
    wp_apply (wp_IsConflict interface.nil with "[]").
    replace (bool_decide (conflict_error interface.nil)) with false by
      (symmetry; apply bool_decide_false; exact conflict_error_nil).
    wp_auto.
    wp_for_post.
    iApply "HΦ".
  - iDestruct "Hconflict" as
      "(%Hconflict & Hown_meta_frag & Hown_children_frag & Hown_terminating_children_frag)".
    iDestruct "Hclose" as "[Habort _]".
    iMod ("Habort" with "[Hown_meta_frag Hown_children_frag Hown_terminating_children_frag]") as "Hau".
    { iFrame "Hown_unreserved_key_frag". iFrame. iFrame "%". }
    iModIntro. iNext.
    wp_auto.
    wp_apply (wp_IsConflict err' with "[]").
    replace (bool_decide (conflict_error err')) with true by
      (symmetry; apply bool_decide_true; done).
    wp_auto.
    wp_for_post.
    iFrame "s key".
    iExists options_c'. iFrame.
Qed.

Lemma wp_State__deleteTx γ l key options_c options uid kmeta parent_key parent_uid children phase :
  {{{ is_pkg_init apimodel ∗
      "#Hisk" ∷ is_kubernetes γ l ∗
      "Hdeepown_options" ∷ DeleteOptionsV.deepown options_c options 1 ∗
      "%Hvalid_options" ∷ ⌜ DeleteOptionsV.valid options ⌝ ∗
      "%Hkey_in" ∷ ⌜ key ∈ children ⌝ ∗
      "%Hdelete_preconditions_uid" ∷ ⌜ delete_preconditions_match_uid options uid ⌝ ∗
      "Hown_meta_frag" ∷ own_meta_frag γ key uid 1 kmeta ∗
      "#Hown_unreserved_key_frag" ∷ own_unreserved_key_frag γ key ∗
      "Hown_children_frag" ∷ own_children_frag γ parent_key parent_uid 1 children ∗
      "Hown_terminating_children_frag" ∷ own_terminating_children_frag γ parent_key parent_uid phase
  }}}
    l @! (go.PointerType apimodel.State) @! "deleteTx" #key #options_c
  {{{ RET #interface.nil;
      "Hown_children_frag" ∷ own_children_frag γ parent_key parent_uid 1 (children ∖ {[key]}) ∗
      "Hdeletion_observed_frag" ∷ own_deletion_observed_frag γ key uid ∗
      "Hown_terminating_children_frag" ∷ own_terminating_children_frag γ parent_key parent_uid Mutable
  }}}.
Proof.
  iIntros (Φ) "(#Hinit & H) HΦ".
  iNamed "H".
  iApply wp_State__deleteTx_au.
  iFrame "#".
  iFrame "%".
  iFrame "Hdeepown_options".
  iEval (rewrite {1}/named).
  iAuIntro.
  iAssert (("%Hkey_in" ∷ ⌜ key ∈ children ⌝ ∗
    "%Hdelete_preconditions_uid" ∷ ⌜ delete_preconditions_match_uid options uid ⌝ ∗
    "Hown_meta_frag" ∷ own_meta_frag γ key uid 1 kmeta ∗
    "#Hown_unreserved_key_frag" ∷ own_unreserved_key_frag γ key ∗
    "Hown_children_frag" ∷ own_children_frag γ parent_key parent_uid 1 children ∗
    "Hown_terminating_children_frag" ∷ own_terminating_children_frag γ parent_key parent_uid phase)%I)
    with "[Hown_meta_frag Hown_children_frag Hown_terminating_children_frag]" as "Hpre".
  { iFrame "Hown_unreserved_key_frag". iFrame. iFrame "%". }
  iAaccIntro with "Hpre".
  - iIntros "Hpre".
    iRename "Hown_unreserved_key_frag" into "Hown_unreserved_key_frag_outer".
    iNamed "Hpre".
    iFrame. done.
  - iIntros (_) "Hpost".
    iModIntro. iNext.
    iApply ("HΦ" with "Hpost").
Qed.

End proof.
