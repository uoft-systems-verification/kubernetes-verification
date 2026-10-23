From New.proof Require Import wp_keep.
From New.proof Require Import prelude empty_ffi.
From New.proof.kubernetes_model.tx Require Export update.
From New.proof Require Export util.
From New.proof Require Export wp_helpers.
From New.object_specs Require Export prelude.
From New.proof.controllers.deployment Require Export deployment_init.
From New.proof.k8s_io.api.apps Require Export v1.
From New.proof.k8s_io.kubernetes.pkg Require Export controller.
From New.proof.k8s_io.apimachinery.pkg.api Require Export errors.
From New.proof.controllers.deployment Require Export common replica_sets.


Local Transparent ObjectMetaV.deepown ObjectMetaView.ObjectMetaV.deepown.
Section proof.
Context `{hG: !heapGS Σ}.
Context {sem : go.Semantics}
  {package_sem : code.controllers.deployment.deployment.Assumptions}.
Collection W := sem + package_sem.
#[local] Instance controller_sem : controller.Assumptions :=
  code.controllers.deployment.deployment.import_controller_Assumption.
#[local] Instance base_apimodel_sem : apimodel.Assumptions | 100 :=
  code.controllers.deployment.deployment.import_apimodel_Assumption.
#[local] Instance object_meta_v1_sem :
    code.k8s_io.apimachinery.pkg.apis.meta.v1.v1.Assumptions :=
  apimodel.import_apis_meta_v1_Assumption.
#[local] Instance object_apps_v1_sem :
    code.k8s_io.api.apps.v1.v1.Assumptions :=
  apimodel.import_api_apps_v1_Assumption.
#[local] Instance object_core_v1_sem :
    code.k8s_io.api.core.v1.v1.Assumptions :=
  code.k8s_io.api.apps.v1.v1.import_core_v1_Assumption.
#[local] Instance intstr_sem : intstr.Assumptions :=
  code.k8s_io.api.apps.v1.v1.import_intstr_Assumption.
#[local] Instance apimodel_sem : apimodel.Assumptions | 0.
Proof using package_sem.
  constructor; try exact object_core_v1_sem; try apply _.
Defined.
Context `{!kubernetesModelG Σ}.
Local Set Default Proof Using "All".
Context `{!KObjectV.ObjectInterfaceAssumptions}.

(* ---------------------------------------------------------------- *)
(* Specs for the state-touching half of the controller.              *)
(*                                                                   *)
(* scaleReplicaSet rests on the ReplicaSet-typed model wrapper        *)
(* ReplicaSetUpdateTx.                                                *)
(*                                                                   *)
(* Convention, following the ReplicaSet and StatefulSet controllers:  *)
(* the preconditions are strong enough to rule out API failure, so    *)
(* every spec returns a nil error.                                    *)
(* ---------------------------------------------------------------- *)

(* scaleReplicaSet is a no-op when the count already matches; otherwise it
   submits a spec that differs only in the replica count. The source object is
   read-only — the code deep-copies before mutating — so [rs] comes back at the
   same fraction, and the freshly-owned result appears only in the scaled
   branch, where it is a distinct object returned by the API. *)
Lemma wp_scaleReplicaSet γ model_l rs_l (rs : ReplicaSetV.t)
    (new_scale : w32) dq :
  {{{ "#Hpkg" ∷ is_pkg_init code.controllers.deployment.pkg_id.deployment ∗
      "#Hisk" ∷ is_kubernetes γ model_l ∗
      "#Hglobal_l" ∷ (global_addr apimodel.ModelState) ↦□ model_l ∗
      "Hrs" ∷ ReplicaSetV.deepown_l rs_l rs dq ∗
      "%Hrs_valid" ∷ ⌜ ReplicaSetV.valid rs ⌝ ∗
      "%Hscale_nonneg" ∷ ⌜ 0 ≤ sint.Z new_scale ⌝ ∗
      "Hown_meta" ∷ own_meta_frag γ (ReplicaSetV.key rs)
        rs.(ReplicaSetV.ObjectMeta').(ObjectMetaV.UID') 1
        rs.(ReplicaSetV.ObjectMeta') ∗
      "Hown_spec" ∷ own_spec_frag γ (ReplicaSetV.key rs)
        rs.(ReplicaSetV.ObjectMeta').(ObjectMetaV.UID') 1
        (ObjectSpecV.ReplicaSetSpec rs.(ReplicaSetV.Spec'))
  }}}
    @! deployment.scaleReplicaSet #rs_l #new_scale
  {{{ (scaled : bool) (rs'_l : loc) (rs' : ReplicaSetV.t),
      RET (#scaled, #rs'_l, #interface.nil);
      "Hrs" ∷ ReplicaSetV.deepown_l rs_l rs dq ∗
      "%Hkey" ∷ ⌜ ReplicaSetV.key rs' = ReplicaSetV.key rs ⌝ ∗
      "%Huid" ∷ ⌜ rs'.(ReplicaSetV.ObjectMeta').(ObjectMetaV.UID') =
          rs.(ReplicaSetV.ObjectMeta').(ObjectMetaV.UID') ⌝ ∗
      "Hown_meta" ∷ own_meta_frag γ (ReplicaSetV.key rs)
        rs.(ReplicaSetV.ObjectMeta').(ObjectMetaV.UID') 1
        rs'.(ReplicaSetV.ObjectMeta') ∗
      "Hown_spec" ∷ own_spec_frag γ (ReplicaSetV.key rs)
        rs.(ReplicaSetV.ObjectMeta').(ObjectMetaV.UID') 1
        (ObjectSpecV.ReplicaSetSpec rs'.(ReplicaSetV.Spec')) ∗
      ( ("%Hnoop" ∷ ⌜ rs_replicas rs = new_scale ∧ scaled = false ∧
             rs' = rs ∧ rs'_l = rs_l ⌝)
        ∨
        ( "%Hscaled" ∷ ⌜ rs_replicas rs ≠ new_scale ∧ scaled = true ⌝ ∗
          "Hrs'" ∷ ReplicaSetV.deepown_l rs'_l rs' 1 ∗
          "%Hspec_updated" ∷ ⌜ ObjectSpecV.updated
              (ObjectSpecV.ReplicaSetSpec rs.(ReplicaSetV.Spec'))
              (ObjectSpecV.ReplicaSetSpec (rs_scaled_spec rs new_scale))
              (ObjectSpecV.ReplicaSetSpec rs'.(ReplicaSetV.Spec')) ⌝))
  }}}.
Proof.
  wp_start as "H". iNamed "H". wp_auto_keep.
  wp_apply (wp_replicasOfRS rs_l (Some rs) dq with "[$Hrs]").
  iIntros "Hrs". simpl. wp_auto_keep.
  wp_if_destruct.
  - (* Already at the target count: scaleReplicaSet returns before the deep
       copy, so no fragment at 1 is needed and nothing is written. *)
    iApply ("HΦ" $! false rs_l rs). iFrame.
    iSplit; [iPureIntro; done|]. iSplit; [iPureIntro; done|].
    iLeft. iPureIntro. split_and!; done.
  - iAssert (is_pkg_init code.k8s_io.api.apps.v1.pkg_id.v1) as "#Happsv1".
    { iPkgInit. }
    iAssert (is_pkg_init apimodel) as "#Hapimodel". { iPkgInit. }
    iEval (rewrite /named /rs_opt_own) in "Hrs".
    iDestruct "Hrs" as (rs_phy) "[Hrs_ptr Hrs]".
    wp_apply (wp_ReplicaSet__DeepCopy rs_l rs_phy rs dq dq with "[$Happsv1 $Hrs_ptr $Hrs]").
    iIntros (copy_l) "(Hcopy & Hrs_ptr & Hrs)".
    iAssert (ReplicaSetV.deepown_l rs_l rs dq) with "[Hrs_ptr Hrs]" as "Hrs".
    { iExists rs_phy. iFrame. }
    wp_auto_keep.
    iPoseProof (ReplicaSetV.deepown_l_split with "Hcopy") as
      "(%Hcopy_nn & Hc_tm & Hc_om & Hc_spec & Hc_st)".
    iDestruct "Hc_spec" as (spec_c) "[Hspec_field Hspec]".
    iNamedPrefix "Hspec" "Hsp_".
    wp_auto_keep.
    (* The store put the *local* newScale cell into the copy's Spec.Replicas
       field, so ownership of that local moves into the object. Nothing reads
       it again. *)
    iAssert ⌜ newScale_ptr ≠ null ⌝%I as %Hscale_ptr_nn.
    { iApply (typed_pointsto_not_null with "newScale"). }
    iAssert (ReplicaSetSpecV.deepown
        (spec_c <| v1.ReplicaSetSpec.Replicas' := newScale_ptr |>)
        (rs_scaled_spec rs new_scale) 1)
      with "[newScale Hsp_Hdeepown_selector_some Hsp_Hdeepown_template]"
      as "Hspec_new".
    { rewrite /ReplicaSetSpecV.deepown /rs_scaled_spec /=.
      iFrame "Hsp_Hdeepown_selector_some Hsp_Hdeepown_template".
      iSplit; [iPureIntro; split;
        [intros Hnull; exfalso; exact (Hscale_ptr_nn Hnull)
        |intros Hcontra; discriminate]|].
      iSplitL "newScale"; [iExists new_scale; iFrame; done|].
      iPureIntro. split_and!; done. }
    iAssert (ReplicaSetSpecV.deepown_l (ReplicaSetV.spec_ptr copy_l)
        (rs_scaled rs new_scale).(ReplicaSetV.Spec') 1)
      with "[Hspec_field Hspec_new]" as "Hc_spec".
    { iExists (spec_c <| v1.ReplicaSetSpec.Replicas' := newScale_ptr |>).
      iFrame. }
    (* The namespace argument is read off the copy; the equality is pure, so
       the metadata stays sealed. *)
    iDestruct "Hc_om" as (meta_c) "[Hmeta_field Hmeta]".
    iAssert ⌜ meta_c.(v1.ObjectMeta.Namespace') =
        rs.(ReplicaSetV.ObjectMeta').(ObjectMetaV.Namespace') ⌝%I as %Hns.
    { iNamed "Hmeta". iPureIntro. exact Hdeepown_namespace. }
    wp_auto_keep.
    rewrite Hns.
    iAssert (ObjectMetaV.deepown_l (ReplicaSetV.objectmeta_ptr copy_l)
        (rs_scaled rs new_scale).(ReplicaSetV.ObjectMeta') 1)
      with "[Hmeta_field Hmeta]" as "Hc_om".
    { iExists meta_c. iFrame. }
    iPoseProof (ReplicaSetV.deepown_l_restore _ (rs_scaled rs new_scale) _
      Hcopy_nn with "[$Hc_tm $Hc_om $Hc_spec $Hc_st]") as "Hcopy".
    (* Holding the metadata fragment rules out a deletion timestamp, which is
       what the update needs. *)
    iPoseProof (kview.own_meta_valid with "Hown_meta") as "%Hmeta_frag_valid".
    destruct Hmeta_frag_valid as (_ & _ & _ & Hmeta_valid & Hdeletion).
    destruct Hrs_valid as (Htm_valid & Hrv_valid & Hom_valid & Hspec_valid & Hst_valid).
    pose proof Hom_valid as (_ & Hname_nonempty & _ & _ & _ & Huid_valid & _).
    wp_apply (wp_State__ReplicaSetUpdateTx γ model_l
      rs.(ReplicaSetV.ObjectMeta').(ObjectMetaV.Namespace')
      copy_l (rs_scaled rs new_scale) (ReplicaSetV.key rs)
      rs.(ReplicaSetV.ObjectMeta').(ObjectMetaV.UID')
      rs.(ReplicaSetV.ObjectMeta')
      (ObjectSpecV.ReplicaSetSpec rs.(ReplicaSetV.Spec'))
      with "[$Hcopy $Hown_meta $Hown_spec]").
    { iFrame "#". iPureIntro. split_and!.
      - apply rs_scaled_valid_create; [split_and!; done|done|done|done].
      - exact Hname_nonempty.
      - eapply valid_uid_non_empty. exact Huid_valid.
      - exact Hrv_valid.
      - exact Htm_valid.
      - done.
      - done.
      - done.
      - rewrite /ObjectMetaV.valid_simple_update. split_and!; done.
      - rewrite /ObjectSpecV.valid_update /ReplicaSetSpecV.valid_update
          /rs_scaled /=.
        split; [|rewrite /rs_scaled_spec /=; done].
        apply rs_scaled_spec_valid_create; [exact (proj1 Hspec_valid)|done].
      - exact Hdeletion. }
    iIntros (rs'_l rs') "Hupd". iNamedPrefix "Hupd" "Hu_".
    wp_auto_keep.
    iApply ("HΦ" $! true rs'_l rs').
    iFrame "Hrs Hu_Hown_meta_frag Hu_Hown_spec_frag".
    iSplit; [iPureIntro; exact Hu_Hkey_eq'|].
    iSplit; [iPureIntro; exact Hu_Huid_eq'|].
    iRight. iFrame "Hu_Hdeepown_l". iSplit.
    + iPureIntro. split; [exact n|done].
    + iPureIntro. exact Hu_Hspec_updated.
Qed.

End proof.
