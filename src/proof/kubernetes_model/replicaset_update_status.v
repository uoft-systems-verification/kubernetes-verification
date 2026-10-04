From New.proof Require Import prelude empty_ffi.
From New.proof.kubernetes_model Require Export update_status.
From New.proof.kubernetes_model.tx Require Import update_status.

Section proof.
Context `{hG: !heapGS Σ} `{!ffi_semantics _ _}.
Context {sem : go.Semantics} {package_sem : apimodel.Assumptions}.
Context `{!kubernetesModelG Σ}.
Context `{!KObjectV.ObjectInterfaceAssumptions}.
Local Set Default Proof Using "All".

(* The ReplicaSet status write used through the trusted client-go UpdateStatus
   shim. The caller keeps shares of the unchanged metadata and spec. The input
   is the caller's own object: the model only reads a deep copy, so any fraction
   [dq_in] suffices and it is returned in both outcomes. Resource-version
   conflicts are retried, so a failure means the requested status is invalid. A
   request whose status is invalid may still succeed (for example when a
   disabled field is dropped), so the status relation on success is only
   guaranteed for a valid requested status. *)
Lemma wp_State__ReplicaSetUpdateStatusTx γ l namespace rs_l rs requested dq dq_in :
  {{{ is_pkg_init apimodel ∗
      "#Hisk" ∷ is_kubernetes γ l ∗
      "%Hnamespace" ∷ ⌜ namespace = rs.(ReplicaSetV.ObjectMeta').(ObjectMetaV.Namespace') ⌝ ∗
      "%Hvalid" ∷ ⌜ ReplicaSetV.valid rs ⌝ ∗
      "Hinput" ∷ ReplicaSetV.deepown_l rs_l (rs <| ReplicaSetV.Status' := requested |>) dq_in ∗
      "Hmeta" ∷ own_meta_frag γ (ReplicaSetV.key rs)
        rs.(ReplicaSetV.ObjectMeta').(ObjectMetaV.UID') dq rs.(ReplicaSetV.ObjectMeta') ∗
      "Hspec" ∷ own_spec_frag γ (ReplicaSetV.key rs)
        rs.(ReplicaSetV.ObjectMeta').(ObjectMetaV.UID') dq (ObjectSpecV.ReplicaSetSpec rs.(ReplicaSetV.Spec')) ∗
      "Hstatus" ∷ own_status_frag γ (ReplicaSetV.key rs)
        rs.(ReplicaSetV.ObjectMeta').(ObjectMetaV.UID') 1 (ObjectStatusV.ReplicaSetStatus rs.(ReplicaSetV.Status'))
  }}}
    l @! (go.PointerType apimodel.State) @! "ReplicaSetUpdateStatusTx" #namespace #rs_l
  {{{ result_l rs' err, RET (#result_l, #err);
      ⌜ ReplicaSetV.status_only_changed rs rs' ⌝ ∗
      ReplicaSetV.deepown_l rs_l (rs <| ReplicaSetV.Status' := requested |>) dq_in ∗
      own_meta_frag γ (ReplicaSetV.key rs)
        rs.(ReplicaSetV.ObjectMeta').(ObjectMetaV.UID') dq rs'.(ReplicaSetV.ObjectMeta') ∗
      own_spec_frag γ (ReplicaSetV.key rs)
        rs.(ReplicaSetV.ObjectMeta').(ObjectMetaV.UID') dq (ObjectSpecV.ReplicaSetSpec rs.(ReplicaSetV.Spec')) ∗
      own_status_frag γ (ReplicaSetV.key rs)
        rs.(ReplicaSetV.ObjectMeta').(ObjectMetaV.UID') 1 (ObjectStatusV.ReplicaSetStatus rs'.(ReplicaSetV.Status')) ∗
      ((⌜ err = interface.nil ⌝ ∗
        ⌜ ReplicaSetV.valid rs' ⌝ ∗
        ⌜ ReplicaSetStatusV.valid requested →
          ReplicaSetStatusV.updated requested rs'.(ReplicaSetV.Status') ⌝ ∗
        ReplicaSetV.deepown_l result_l rs' 1) ∨
       (⌜ err ≠ interface.nil ∧ result_l = null ∧ rs' = rs ∧ ¬ ReplicaSetStatusV.valid requested ⌝))
  }}}.
Proof.
  iIntros (Φ) "(#Hinit & H) HΦ". iNamed "H".
  set input := rs <| ReplicaSetV.Status' := requested |>.
  destruct Hvalid as (Hvalid_typemeta & Hvalid_rv & Hvalid_meta & _ & _).
  pose proof Hvalid_meta as (_ & Hname_nonempty & _ & _ & _ & Hvalid_uid & Hlabels &
    Hannotations & Howners & Hfinalizers & Hmanaged_fields & _).
  pose proof (valid_uid_non_empty _ Hvalid_uid) as Huid_nonempty.
  assert (ObjectMetaV.valid_simple_update rs.(ReplicaSetV.ObjectMeta') rs.(ReplicaSetV.ObjectMeta'))
    as Hsimple_refl.
  { rewrite /ObjectMetaV.valid_simple_update. split_and!; done. }
  (* A valid requested status makes the whole request valid. *)
  assert (ReplicaSetStatusV.valid requested →
    KObjectV.valid_status_update "ReplicaSet"%go namespace rs.(ReplicaSetV.ObjectMeta')
      (ObjectStatusV.ReplicaSetStatus rs.(ReplicaSetV.Status')) (KObjectV.ReplicaSet input))
    as Hvalid_request.
  { intros Hvalid_requested.
    rewrite /KObjectV.valid_status_update /ReplicaSetV.valid_status_update /=.
    split_and!; try done.
    rewrite /ObjectMetaV.valid_update. split_and!; try done. by left. }
  wp_method_call. rewrite /apimodel.State__ReplicaSetUpdateStatusTxⁱᵐᵖˡ. wp_call. wp_auto.
  iAssert (KObjectV.deepown_i (interface.mk (go.PointerType v1.ReplicaSet) #rs_l)
    (KObjectV.ReplicaSet input) dq_in) with "[Hinput]" as "Hdeepown_i".
  { iExists rs_l. iSplit; [iPureIntro; apply KObjectV.valid_interface_ReplicaSet|]. iFrame. }
  change (go.PointerType api_apps_v1.ReplicaSet) with (go.PointerType v1.ReplicaSet).
  wp_apply (wp_State__updateStatusTx_shared γ l "ReplicaSet"%go namespace
    (interface.mk (go.PointerType v1.ReplicaSet) #rs_l) (KObjectV.ReplicaSet input) dq_in
    rs.(ReplicaSetV.ObjectMeta').(ObjectMetaV.UID') dq rs.(ReplicaSetV.ObjectMeta')
    (Some (ObjectSpecV.ReplicaSetSpec rs.(ReplicaSetV.Spec')))
    (ObjectStatusV.ReplicaSetStatus rs.(ReplicaSetV.Status'))
    with "[$Hdeepown_i $Hmeta $Hspec $Hstatus]").
  { iFrame "#". iPureIntro. split_and!.
    - rewrite /status_update_request_ok /=. split_and!; done.
    - done.
    - by right. }
  iIntros (ret) "[Hdeepown_i [Hsuccess | Hfailure]]".
  - iDestruct "Hsuccess" as (i' kobj') "(-> & %Hvalid' & %Hupdated_if_valid & %Hpreserved & Hdeepown_i' &
      Hmeta & (Hspec & %Hspec_eq) & Hstatus)".
    destruct Hpreserved as (Hsame_kind & Htypemeta_eq & Hmeta_eq).
    destruct kobj' as [pod'|rs'|pvc'|sts'|d']; try done.
    iDestruct "Hdeepown_i'" as (rs_l') "[%Hi' Hdeepown_l']".
    iDestruct "Hdeepown_i" as (rs_l0) "[%Hi0 Hinput]".
    unfold KObjectV.valid_interface in Hi', Hi0.
    destruct Hi' as [Hi' _]. destruct Hi0 as [Hi0 _].
    inversion Hi0 as [Hl]. apply (inj _) in Hl. subst rs_l0.
    wp_auto.
    rewrite Hi'.
    cbn [interface.ty interface.v].
    replace (if decide (go.PointerType v1.ReplicaSet = go.PointerType v1.ReplicaSet)
             then #rs_l' else #null)%V with (#rs_l')%V by
      (rewrite decide_True; done).
    replace (bool_decide (go.PointerType v1.ReplicaSet = go.PointerType v1.ReplicaSet)) with true by
      (symmetry; apply bool_decide_eq_true_2; done).
    wp_auto.
    simpl in Hspec_eq, Htypemeta_eq, Hmeta_eq, Hvalid'.
    injection Hspec_eq as Hspec_eq.
    iApply ("HΦ" $! rs_l' rs' interface.nil).
    iFrame. iSplit.
    { iPureIntro. rewrite /ReplicaSetV.status_only_changed. split_and!; done. }
    iLeft. iFrame. iPureIntro. split_and!; try done.
    intros Hvalid_requested.
    pose proof (Hupdated_if_valid (Hvalid_request Hvalid_requested)) as Hupdated.
    rewrite /KObjectV.status_updated /ReplicaSetV.status_updated in Hupdated.
    destruct Hupdated as (_ & _ & Hstatus_updated). exact Hstatus_updated.
  - iDestruct "Hfailure" as (err) "(-> & [%Herr_ne %Hinvalid] & Hmeta & Hspec & Hstatus)".
    iDestruct "Hdeepown_i" as (rs_l0) "[%Hi0 Hinput]".
    unfold KObjectV.valid_interface in Hi0. destruct Hi0 as [Hi0 _].
    inversion Hi0 as [Hl]. apply (inj _) in Hl. subst rs_l0.
    destruct err as [err_ok|]; [|done].
    wp_auto.
    iApply ("HΦ" $! null rs (interface.ok err_ok)).
    iFrame. iSplit.
    { iPureIntro. rewrite /ReplicaSetV.status_only_changed. split_and!; done. }
    iRight. iPureIntro. split_and!; try done.
    intros Hvalid_requested. by apply Hinvalid, Hvalid_request.
Qed.

End proof.
