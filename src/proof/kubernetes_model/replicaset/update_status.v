From New.proof Require Import prelude empty_ffi.
From New.proof.kubernetes_model Require Export update_status.
From New.proof.kubernetes_model.tx Require Import update_status_same_meta.

Section proof.
Context `{hG: !heapGS Σ} `{!ffi_semantics _ _}.
Context {sem : go.Semantics} {package_sem : apimodel.Assumptions}.
Context `{!kubernetesModelG Σ}.
Context `{!KObjectV.ObjectInterfaceAssumptions}.
Local Set Default Proof Using "All".

(* The ReplicaSet instance of [wp_State__updateStatusTx_same_meta], through the
   typed wrapper [ReplicaSetUpdateStatusTx]: the request keeps the stored
   metadata except for the resource version ([Hmeta_same]), so the metadata
   fragment may be held at any fraction and is returned unchanged. Each attempt
   writes at the currently stored resource version and conflicts are retried;
   the request must be valid, so the write always succeeds. The input is only
   read, at fraction [dq_in]. *)
Lemma wp_State__ReplicaSetUpdateStatusTx_same_meta γ l namespace rs_l rs dq_in uid dq kmeta kstatus :
  {{{ is_pkg_init apimodel ∗
      "#Hisk" ∷ is_kubernetes γ l ∗
      "%Hvalid_status_update" ∷ ⌜ ReplicaSetV.valid_status_update ReplicaSetV.kind namespace kmeta kstatus rs ⌝ ∗
      "%Hmeta_same" ∷ ⌜ ObjectMetaV.equiv_except_resource_version rs.(ReplicaSetV.ObjectMeta') kmeta ⌝ ∗
      "Hdeepown_l" ∷ ReplicaSetV.deepown_l rs_l rs dq_in ∗
      "Hown_meta_frag" ∷ own_meta_frag γ (ReplicaSetV.key rs) uid dq kmeta ∗
      "Hown_status_frag" ∷ own_status_frag γ (ReplicaSetV.key rs) uid 1 (ObjectStatusV.ReplicaSetStatus kstatus)
  }}}
    l @! (go.PointerType apimodel.State) @! "ReplicaSetUpdateStatusTx" #namespace #rs_l
  {{{ (rs_l' : loc) rs', RET (#rs_l', #interface.nil);
      ReplicaSetV.deepown_l rs_l rs dq_in ∗
      own_meta_frag γ (ReplicaSetV.key rs) uid dq kmeta ∗
      ⌜ ReplicaSetV.valid rs' ⌝ ∗
      ⌜ ReplicaSetV.status_updated rs rs' ⌝ ∗
      ⌜ ObjectMetaV.equiv_except_resource_version rs'.(ReplicaSetV.ObjectMeta') kmeta ⌝ ∗
      ReplicaSetV.deepown_l rs_l' rs' 1 ∗
      own_status_frag γ (ReplicaSetV.key rs) uid 1 (ObjectStatusV.ReplicaSetStatus rs'.(ReplicaSetV.Status'))
  }}}.
Proof.
  iIntros (Φ) "(#Hinit & H) HΦ". iNamed "H".
  wp_method_call. rewrite /apimodel.State__ReplicaSetUpdateStatusTxⁱᵐᵖˡ. wp_call. wp_auto.
  iAssert (KObjectV.deepown_i (interface.mk (go.PointerType v1.ReplicaSet) #rs_l)
    (KObjectV.ReplicaSet rs) dq_in) with "[Hdeepown_l]" as "Hdeepown_i".
  { iExists rs_l. iSplit; [iPureIntro; apply KObjectV.valid_interface_ReplicaSet|]. iFrame. }
  change (go.PointerType api_apps_v1.ReplicaSet) with (go.PointerType v1.ReplicaSet).
  wp_apply (wp_State__updateStatusTx_same_meta γ l "ReplicaSet"%go namespace
    (interface.mk (go.PointerType v1.ReplicaSet) #rs_l) (KObjectV.ReplicaSet rs) dq_in
    uid dq kmeta (ObjectStatusV.ReplicaSetStatus kstatus)
    with "[$Hdeepown_i $Hown_meta_frag $Hown_status_frag]").
  { iFrame "#". iPureIntro. split; done. }
  iIntros (i' kobj') "(Hdeepown_i & Hown_meta_frag & %Hvalid' & %Hupdated & %Hpreserved & Hdeepown_i' &
    Hown_status_frag)".
  destruct Hpreserved as (Hsame_kind & Hmeta_eq).
  destruct kobj' as [pod'|rs'|pvc'|sts'|d']; try done.
  iDestruct "Hdeepown_i'" as (rs_l') "[%Hi' Hdeepown_l']".
  iDestruct "Hdeepown_i" as (rs_l0) "[%Hi0 Hdeepown_l]".
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
  iApply ("HΦ" $! rs_l' rs').
  iFrame. iPureIntro. split_and!; done.
Qed.

(* A variant of [wp_State__ReplicaSetUpdateStatusTx_same_meta] that does not
   require the requested status to be valid: the write either succeeds as there,
   without a description of the stored status beyond its validity, or returns
   an error and leaves the status fragment unchanged. *)
Lemma wp_State__ReplicaSetUpdateStatusTx_same_meta_general γ l (namespace : go_string) rs_l rs dq_in
    uid dq kmeta kstatus :
  {{{ is_pkg_init apimodel ∗
      "#Hisk" ∷ is_kubernetes γ l ∗
      "%Hvalid_typemeta" ∷ ⌜ valid_typemeta ReplicaSetV.kind rs.(ReplicaSetV.TypeMeta') ⌝ ∗
      "%Hmeta_same" ∷ ⌜ ObjectMetaV.equiv_except_resource_version rs.(ReplicaSetV.ObjectMeta') kmeta ⌝ ∗
      "Hdeepown_l" ∷ ReplicaSetV.deepown_l rs_l rs dq_in ∗
      "Hown_meta_frag" ∷ own_meta_frag γ (ReplicaSetV.key rs) uid dq kmeta ∗
      "Hown_status_frag" ∷ own_status_frag γ (ReplicaSetV.key rs) uid 1 (ObjectStatusV.ReplicaSetStatus kstatus)
  }}}
    l @! (go.PointerType apimodel.State) @! "ReplicaSetUpdateStatusTx" #namespace #rs_l
  {{{ (rs_l' : loc) (err : interface.t), RET (#rs_l', #err);
      ReplicaSetV.deepown_l rs_l rs dq_in ∗
      own_meta_frag γ (ReplicaSetV.key rs) uid dq kmeta ∗
      ((⌜ err = interface.nil ⌝ ∗
        ∃ rs',
          ⌜ ReplicaSetV.valid rs' ⌝ ∗
          ⌜ ObjectMetaV.equiv_except_resource_version rs'.(ReplicaSetV.ObjectMeta') kmeta ⌝ ∗
          ReplicaSetV.deepown_l rs_l' rs' 1 ∗
          own_status_frag γ (ReplicaSetV.key rs) uid 1 (ObjectStatusV.ReplicaSetStatus rs'.(ReplicaSetV.Status'))) ∨
       (⌜ err ≠ interface.nil ⌝ ∗
        own_status_frag γ (ReplicaSetV.key rs) uid 1 (ObjectStatusV.ReplicaSetStatus kstatus)))
  }}}.
Proof.
  iIntros (Φ) "(#Hinit & H) HΦ". iNamed "H".
  wp_method_call. rewrite /apimodel.State__ReplicaSetUpdateStatusTxⁱᵐᵖˡ. wp_call. wp_auto.
  iAssert (KObjectV.deepown_i (interface.mk (go.PointerType v1.ReplicaSet) #rs_l)
    (KObjectV.ReplicaSet rs) dq_in) with "[Hdeepown_l]" as "Hdeepown_i".
  { iExists rs_l. iSplit; [iPureIntro; apply KObjectV.valid_interface_ReplicaSet|]. iFrame. }
  change (go.PointerType api_apps_v1.ReplicaSet) with (go.PointerType v1.ReplicaSet).
  wp_apply (wp_State__updateStatusTx_same_meta_general γ l "ReplicaSet"%go namespace
    (interface.mk (go.PointerType v1.ReplicaSet) #rs_l) (KObjectV.ReplicaSet rs) dq_in
    uid dq kmeta (ObjectStatusV.ReplicaSetStatus kstatus)
    with "[$Hdeepown_i $Hown_meta_frag $Hown_status_frag]").
  { iFrame "#". iPureIntro. split; done. }
  iIntros (ret err) "(Hdeepown_i & Hown_meta_frag & Hpost)".
  iDestruct "Hdeepown_i" as (rs_l0) "[%Hi0 Hdeepown_l]".
  unfold KObjectV.valid_interface in Hi0. destruct Hi0 as [Hi0 _].
  inversion Hi0 as [Hl]. apply (inj _) in Hl. subst rs_l0.
  iDestruct "Hpost" as "[(-> & Hsuccess) | (%Herr_ne & Hown_status_frag)]".
  2: {
    destruct err as [err_ok|]; [|done]. wp_auto.
    iApply ("HΦ" $! null (interface.ok err_ok)). iFrame. iRight. iFrame. done. }
  iDestruct "Hsuccess" as (i' kobj') "(-> & %Hvalid' & %Hpreserved & Hdeepown_i' & Hown_status_frag)".
  destruct Hpreserved as (Hsame_kind & Hmeta_eq).
  destruct kobj' as [pod'|rs'|pvc'|sts'|d']; try done.
  iDestruct "Hdeepown_i'" as (rs_l') "[%Hi' Hdeepown_l']".
  unfold KObjectV.valid_interface in Hi'. destruct Hi' as [Hi' _].
  wp_auto.
  rewrite Hi'.
  cbn [interface.ty interface.v].
  replace (if decide (go.PointerType v1.ReplicaSet = go.PointerType v1.ReplicaSet)
           then #rs_l' else #null)%V with (#rs_l')%V by
    (rewrite decide_True; done).
  replace (bool_decide (go.PointerType v1.ReplicaSet = go.PointerType v1.ReplicaSet)) with true by
    (symmetry; apply bool_decide_eq_true_2; done).
  wp_auto.
  iApply ("HΦ" $! rs_l' interface.nil).
  iFrame. iLeft. iSplit; first done. iExists rs'. iFrame. iPureIntro. split; done.
Qed.

End proof.
