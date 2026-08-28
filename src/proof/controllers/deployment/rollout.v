From New.proof Require Import prelude empty_ffi.
From New.proof.kubernetes_model Require Export get create_named update.
From New.proof.kubernetes_model.tx Require Export update.
From New.proof Require Export util.
From New.proof Require Export wp_helpers.
From New.proof.kubernetes_types Require Export prelude.
From New.proof.controllers.deployment Require Export deployment_init.
From New.proof.k8s_io.api.apps Require Export v1.
From New.proof.k8s_io.kubernetes.pkg Require Export controller.
From New.proof.k8s_io.apimachinery.pkg.api Require Export errors.
From New.proof.controllers.deployment Require Export common replica_sets.

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

(* ---------------------------------------------------------------- *)
(* Specs for the state-touching half of the controller.              *)
(*                                                                   *)
(* All five are stated and Admitted. Discharging them needs the      *)
(* ReplicaSet-typed model wrappers (ReplicaSetUpdate / Create), which *)
(* do not exist yet — see notes/spec-remaining.md §4.3. Stating them  *)
(* first is deliberate: the ownership footprints below are what fix   *)
(* the shape those wrappers have to take.                            *)
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
              (ObjectSpecV.ReplicaSetSpec (rs_scaled_spec rs new_scale))
              (ObjectSpecV.ReplicaSetSpec rs'.(ReplicaSetV.Spec')) ⌝))
  }}}.
Proof.
  wp_start as "H". iNamed "H". wp_auto.
  wp_apply (wp_replicasOfRS rs_l (Some rs) dq with "[$Hrs]").
  iIntros "Hrs". simpl. wp_auto.
  wp_if_destruct.
  - (* Already at the target count: deployment.go:104 returns before the deep
       copy, so no fragment at 1 is needed and nothing is written. *)
    iApply ("HΦ" $! false rs_l rs). iFrame.
    iSplit; [iPureIntro; done|]. iSplit; [iPureIntro; done|].
    iLeft. iPureIntro. split_and!; done.
  - iAssert (is_pkg_init code.k8s_io.api.apps.v1.pkg_id.v1) as "#Happsv1".
    { iPkgInit. }
    iAssert (is_pkg_init apimodel) as "#Hapimodel". { iPkgInit. }
    iEval (rewrite /named) in "Hrs".
    iDestruct "Hrs" as (rs_phy) "[Hrs_ptr Hrs_deep]".
    wp_apply (wp_ReplicaSet__DeepCopy rs_l rs_phy rs dq dq
      with "[$Happsv1 $Hrs_ptr $Hrs_deep]").
    iIntros (copy_l) "(Hcopy & Hrs_ptr & Hrs_deep)".
    iAssert (ReplicaSetV.deepown_l rs_l rs dq) with "[Hrs_ptr Hrs_deep]" as "Hrs".
    { iExists rs_phy. iFrame. }
    wp_auto.
    iPoseProof (ReplicaSetV.deepown_l_split with "Hcopy") as
      "(%Hcopy_nn & Hc_tm & Hc_om & Hc_spec & Hc_st)".
    iDestruct "Hc_spec" as (spec_c) "[Hspec_field Hspec]".
    iNamedPrefix "Hspec" "Hsp_".
    wp_auto.
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
    wp_auto.
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
    wp_apply (wp_State__ReplicaSetUpdateTx γ model_l
      rs.(ReplicaSetV.ObjectMeta').(ObjectMetaV.Namespace')
      copy_l (rs_scaled rs new_scale) (ReplicaSetV.key rs)
      rs.(ReplicaSetV.ObjectMeta').(ObjectMetaV.UID')
      rs.(ReplicaSetV.ObjectMeta')
      (ObjectSpecV.ReplicaSetSpec rs.(ReplicaSetV.Spec'))
      with "[$Hcopy $Hown_meta $Hown_spec]").
    { iFrame "#". iPureIntro. split_and!.
      - apply rs_scaled_valid_named_create; [split_and!; done|done|done].
      - eapply valid_uid_non_empty. eapply ObjectMetaV.valid_uid_of_valid.
        exact Hom_valid.
      - done.
      - done.
      - done.
      - apply valid_simple_update_refl.
      - rewrite /ObjectSpecV.valid_update /ReplicaSetSpecV.valid_update
          /rs_scaled /rs_scaled_spec /=. done.
      - exact Hdeletion. }
    iIntros (rs'_l rs') "Hupd". iNamedPrefix "Hupd" "Hu_".
    wp_auto.
    iApply ("HΦ" $! true rs'_l rs').
    iFrame "Hrs Hu_Hown_meta_frag Hu_Hown_spec_frag".
    iSplit; [iPureIntro; exact Hu_Hkey_eq'|].
    iSplit; [iPureIntro; exact Hu_Huid_eq'|].
    iRight. iFrame "Hu_Hdeepown_l". iSplit.
    + iPureIntro. split; [exact n|done].
    + iPureIntro. exact Hu_Hspec_updated.
Qed.

(* getNewReplicaSet adopts the existing template-matching ReplicaSet if there is
   one, and otherwise creates it under the deterministic name [new_rs_name d].
   The reserved fragment is what licenses the named create; the children
   fragment is what the new key is added to.

   The IsAlreadyExists path in the Go code re-reads the object rather than
   failing. Under the no-collision assumption that object holds the same
   template, so it is folded into the "adopted" branch here rather than given a
   third outcome — see deployment.go's header and notes/deployment-spec.md §2b. *)
Lemma wp_getNewReplicaSet γ model_l d_l (d : DeploymentV.t)
    sl ptrs (rss : list ReplicaSetV.t) (children : gset KKey.t)
    dq_d dq_rss :
  {{{ "#Hpkg" ∷ is_pkg_init code.controllers.deployment.pkg_id.deployment ∗
      "#Hisk" ∷ is_kubernetes γ model_l ∗
      "#Hglobal_l" ∷ (global_addr apimodel.ModelState) ↦□ model_l ∗
      "Hd" ∷ DeploymentV.deepown_l d_l d dq_d ∗
      "Hsl" ∷ sl ↦*{dq_rss} ptrs ∗
      "Hrss" ∷ ([∗ list] ptr;rs ∈ ptrs;rss, ReplicaSetV.deepown_l ptr rs dq_rss) ∗
      "%Hd_valid" ∷ ⌜ DeploymentV.valid d ⌝ ∗
      "%Hnamespace_valid" ∷ ⌜ valid_namespace
          d.(DeploymentV.ObjectMeta').(ObjectMetaV.Namespace') ⌝ ∗
      "%Hnew_rs_name_valid" ∷ ⌜ valid_dns1123_subdomain (new_rs_name d) ⌝ ∗
      "Hreserved" ∷ own_available_reserved_frag γ 1 (new_rs_key d) ∗
      "Hown_children" ∷ own_children_frag γ (DeploymentV.key d)
        d.(DeploymentV.ObjectMeta').(ObjectMetaV.UID') 1 children
  }}}
    @! deployment.getNewReplicaSet #d_l #sl
  {{{ (new_rs_l : loc) (new_rs : ReplicaSetV.t),
      RET (#new_rs_l, #interface.nil);
      "Hd" ∷ DeploymentV.deepown_l d_l d dq_d ∗
      "Hsl" ∷ sl ↦*{dq_rss} ptrs ∗
      "Hrss" ∷ ([∗ list] ptr;rs ∈ ptrs;rss, ReplicaSetV.deepown_l ptr rs dq_rss) ∗
      "%Hnew_rs_matches" ∷ ⌜ template_matches (rs_template new_rs)
          (deployment_template d) ⌝ ∗
      ( (* Adopted: an existing ReplicaSet already matched, nothing was written. *)
        ( "%Hadopted" ∷ ⌜ ∃ i, find_new_replica_set d rss = Some (i, new_rs) ∧
              ptrs !! i = Some new_rs_l ⌝ ∗
          "Hreserved" ∷ own_available_reserved_frag γ 1 (new_rs_key d) ∗
          "Hown_children" ∷ own_children_frag γ (DeploymentV.key d)
            d.(DeploymentV.ObjectMeta').(ObjectMetaV.UID') 1 children)
        ∨
        (* Created: no ReplicaSet matched, so one was submitted and stored. *)
        ( "%Hcreated" ∷ ⌜ find_new_replica_set d rss = None ⌝ ∗
          "Hnew_rs" ∷ ReplicaSetV.deepown_l new_rs_l new_rs 1 ∗
          "%Hnew_rs_valid" ∷ ⌜ ReplicaSetV.valid new_rs ⌝ ∗
          "%Hnew_rs_key" ∷ ⌜ ReplicaSetV.key new_rs = new_rs_key d ⌝ ∗
          "%Hnew_rs_shape" ∷ ⌜ ∃ submitted,
              is_new_replica_set d submitted ∧
              ObjectSpecV.created
                (ObjectSpecV.ReplicaSetSpec submitted.(ReplicaSetV.Spec'))
                (ObjectSpecV.ReplicaSetSpec new_rs.(ReplicaSetV.Spec')) ⌝ ∗
          "Hown_meta" ∷ own_meta_frag γ (new_rs_key d)
            new_rs.(ReplicaSetV.ObjectMeta').(ObjectMetaV.UID') 1
            new_rs.(ReplicaSetV.ObjectMeta') ∗
          "Hown_spec" ∷ own_spec_frag γ (new_rs_key d)
            new_rs.(ReplicaSetV.ObjectMeta').(ObjectMetaV.UID') 1
            (ObjectSpecV.ReplicaSetSpec new_rs.(ReplicaSetV.Spec')) ∗
          "Hreserved" ∷ own_occupied_reserved_frag γ 1 (new_rs_key d)
            new_rs.(ReplicaSetV.ObjectMeta').(ObjectMetaV.UID') ∗
          "Hown_children" ∷ own_children_frag γ (DeploymentV.key d)
            d.(DeploymentV.ObjectMeta').(ObjectMetaV.UID') 1
            ({[ new_rs_key d ]} ∪ children)))
  }}}.
Proof.
Admitted.

(* reconcileNewReplicaSet scales the new ReplicaSet straight to the
   deployment's replica count — there is no surge pacing in this controller. *)
Lemma wp_reconcileNewReplicaSet γ model_l new_rs_l d_l
    (new_rs : ReplicaSetV.t) (d : DeploymentV.t) dq_rs dq_d :
  {{{ "#Hpkg" ∷ is_pkg_init code.controllers.deployment.pkg_id.deployment ∗
      "#Hisk" ∷ is_kubernetes γ model_l ∗
      "#Hglobal_l" ∷ (global_addr apimodel.ModelState) ↦□ model_l ∗
      "Hnew_rs" ∷ ReplicaSetV.deepown_l new_rs_l new_rs dq_rs ∗
      "Hd" ∷ DeploymentV.deepown_l d_l d dq_d ∗
      "%Hnew_rs_valid" ∷ ⌜ ReplicaSetV.valid new_rs ⌝ ∗
      "%Hd_valid" ∷ ⌜ DeploymentV.valid d ⌝ ∗
      "Hown_meta" ∷ own_meta_frag γ (ReplicaSetV.key new_rs)
        new_rs.(ReplicaSetV.ObjectMeta').(ObjectMetaV.UID') 1
        new_rs.(ReplicaSetV.ObjectMeta') ∗
      "Hown_spec" ∷ own_spec_frag γ (ReplicaSetV.key new_rs)
        new_rs.(ReplicaSetV.ObjectMeta').(ObjectMetaV.UID') 1
        (ObjectSpecV.ReplicaSetSpec new_rs.(ReplicaSetV.Spec'))
  }}}
    @! deployment.reconcileNewReplicaSet #new_rs_l #d_l
  {{{ (scaled : bool) (new_rs' : ReplicaSetV.t),
      RET (#scaled, #interface.nil);
      "Hnew_rs" ∷ ReplicaSetV.deepown_l new_rs_l new_rs dq_rs ∗
      "Hd" ∷ DeploymentV.deepown_l d_l d dq_d ∗
      "Hown_meta" ∷ own_meta_frag γ (ReplicaSetV.key new_rs)
        new_rs.(ReplicaSetV.ObjectMeta').(ObjectMetaV.UID') 1
        new_rs'.(ReplicaSetV.ObjectMeta') ∗
      "Hown_spec" ∷ own_spec_frag γ (ReplicaSetV.key new_rs)
        new_rs.(ReplicaSetV.ObjectMeta').(ObjectMetaV.UID') 1
        (ObjectSpecV.ReplicaSetSpec new_rs'.(ReplicaSetV.Spec')) ∗
      (* Whether or not a write happened, the stored replica count now matches
         the deployment's. This is the postcondition [rollout] actually needs. *)
      "%Hreplicas" ∷ ⌜ new_rs'.(ReplicaSetV.Spec').(ReplicaSetSpecV.Replicas') =
          Some (deployment_replicas d) ⌝ ∗
      "%Hscaled" ∷ ⌜ scaled = bool_decide (rs_replicas new_rs ≠ deployment_replicas d) ⌝
  }}}.
Proof.
  wp_start as "H". iNamed "H". wp_auto.
  wp_apply (wp_replicasOf d_l d dq_d with "[$Hd]").
  iIntros "Hd". wp_auto.
  wp_apply (wp_scaleReplicaSet γ model_l new_rs_l new_rs (deployment_replicas d) dq_rs
    with "[$Hnew_rs $Hown_meta $Hown_spec]").
  { iFrame "#". iPureIntro. split; [done|].
    apply deployment_replicas_nonneg. exact Hd_valid. }
  iIntros (scaled rs'_l new_rs')
    "(Hrs & %Hkey & %Huid & Hown_meta & Hown_spec & Hdisj)".
  wp_auto.
  iApply ("HΦ" $! scaled new_rs').
  (* The fragments already come back keyed on [new_rs], which is what the
     caller frames. *)
  iFrame "Hrs Hd Hown_meta Hown_spec".
  iDestruct "Hdisj" as "[%Hnoop|(%Hscaled & Hrs' & %Hspec_updated)]".
  - (* Already at the deployment's count: nothing was written, and validity
       says the stored count is explicit rather than defaulted. *)
    destruct Hnoop as (Hcount & -> & -> & _).
    iPureIntro. split.
    + rewrite (rs_replicas_of_valid _ Hnew_rs_valid) Hcount. done.
    + assert (bool_decide (rs_replicas new_rs ≠ deployment_replicas d) = false)
        as ->; [|done].
      apply bool_decide_eq_false_2. intros Hcontra. exact (Hcontra Hcount).
  - destruct Hscaled as (Hne & ->).
    iPureIntro. split.
    + eapply rs_scaled_spec_updated_replicas. exact Hspec_updated.
    + assert (bool_decide (rs_replicas new_rs ≠ deployment_replicas d) = true)
        as ->; [|done].
      apply bool_decide_eq_true_2. exact Hne.
Qed.

(* reconcileOldReplicaSets drains every old ReplicaSet to zero in one pass. *)
Lemma wp_reconcileOldReplicaSets γ model_l sl ptrs
    (old_rss : list ReplicaSetV.t) dq_sl dq_rss :
  {{{ "#Hpkg" ∷ is_pkg_init code.controllers.deployment.pkg_id.deployment ∗
      "#Hisk" ∷ is_kubernetes γ model_l ∗
      "#Hglobal_l" ∷ (global_addr apimodel.ModelState) ↦□ model_l ∗
      "Hsl" ∷ sl ↦*{dq_sl} ptrs ∗
      "Hrss" ∷ ([∗ list] ptr;rs ∈ ptrs;old_rss,
        ReplicaSetV.deepown_l ptr rs dq_rss) ∗
      "%Hrss_valid" ∷ ⌜ Forall ReplicaSetV.valid old_rss ⌝ ∗
      "%Hkeys_nodup" ∷ ⌜ NoDup (ReplicaSetV.key <$> old_rss) ⌝ ∗
      "Hown_frags" ∷ ([∗ list] rs ∈ old_rss,
        own_meta_frag γ (ReplicaSetV.key rs)
          rs.(ReplicaSetV.ObjectMeta').(ObjectMetaV.UID') 1
          rs.(ReplicaSetV.ObjectMeta') ∗
        own_spec_frag γ (ReplicaSetV.key rs)
          rs.(ReplicaSetV.ObjectMeta').(ObjectMetaV.UID') 1
          (ObjectSpecV.ReplicaSetSpec rs.(ReplicaSetV.Spec')))
  }}}
    @! deployment.reconcileOldReplicaSets #sl
  {{{ (scaled_down : bool) (old_rss' : list ReplicaSetV.t),
      RET (#scaled_down, #interface.nil);
      "Hsl" ∷ sl ↦*{dq_sl} ptrs ∗
      "Hrss" ∷ ([∗ list] ptr;rs ∈ ptrs;old_rss,
        ReplicaSetV.deepown_l ptr rs dq_rss) ∗
      "%Hlen" ∷ ⌜ length old_rss' = length old_rss ⌝ ∗
      "Hown_frags" ∷ ([∗ list] rs;rs' ∈ old_rss;old_rss',
        own_meta_frag γ (ReplicaSetV.key rs)
          rs.(ReplicaSetV.ObjectMeta').(ObjectMetaV.UID') 1
          rs'.(ReplicaSetV.ObjectMeta') ∗
        own_spec_frag γ (ReplicaSetV.key rs)
          rs.(ReplicaSetV.ObjectMeta').(ObjectMetaV.UID') 1
          (ObjectSpecV.ReplicaSetSpec rs'.(ReplicaSetV.Spec'))) ∗
      (* Every old ReplicaSet is at zero once this returns. *)
      "%Hdrained" ∷ ⌜ Forall (λ rs',
          rs'.(ReplicaSetV.Spec').(ReplicaSetSpecV.Replicas') = Some (W32 0))
          old_rss' ⌝ ∗
      "%Hscaled_down" ∷ ⌜ scaled_down =
          bool_decide (Exists (λ rs, rs_replicas rs ≠ W32 0) old_rss) ⌝
  }}}.
Proof.
  wp_start as "H". iNamed "H". wp_auto.
  iDestruct (own_slice_len with "Hsl") as %(Hsl_len1 & Hsl_len2).
  iDestruct (big_sepL2_length with "Hrss") as %Hlen_eq.
  (* The loop has drained [old_rss] up to [i]; [done_rss] accumulates the
     post-states, which is what the postcondition's [big_sepL2] is over. *)
  set FRAG := (λ (rs rs' : ReplicaSetV.t),
    (own_meta_frag γ (ReplicaSetV.key rs)
       rs.(ReplicaSetV.ObjectMeta').(ObjectMetaV.UID') 1
       rs'.(ReplicaSetV.ObjectMeta') ∗
     own_spec_frag γ (ReplicaSetV.key rs)
       rs.(ReplicaSetV.ObjectMeta').(ObjectMetaV.UID') 1
       (ObjectSpecV.ReplicaSetSpec rs'.(ReplicaSetV.Spec')))%I).
  set I := (∃ (i : w64) (done_rss : list ReplicaSetV.t) (rs_v : loc),
    "Hi_ptr" ∷ i_ptr ↦ i ∗
    "Hrs_ptr" ∷ rs_ptr ↦ rs_v ∗
    "HscaledDown" ∷ scaledDown_ptr ↦
      (bool_decide (Exists (λ rs, rs_replicas rs ≠ W32 0)
        (take (sint.nat i) old_rss))) ∗
    "Hsl" ∷ sl ↦*{dq_sl} ptrs ∗
    "Hrss" ∷ ([∗ list] ptr;rs ∈ ptrs;old_rss, ReplicaSetV.deepown_l ptr rs dq_rss) ∗
    "%Hdone_len" ∷ ⌜ length done_rss = sint.nat i ⌝ ∗
    "%Hdone_drained" ∷ ⌜ Forall (λ rs',
        rs'.(ReplicaSetV.Spec').(ReplicaSetSpecV.Replicas') = Some (W32 0))
        done_rss ⌝ ∗
    "Hdone" ∷ ([∗ list] rs;rs' ∈ take (sint.nat i) old_rss;done_rss, FRAG rs rs') ∗
    "Hrest" ∷ ([∗ list] rs ∈ drop (sint.nat i) old_rss, FRAG rs rs) ∗
    "%Hi" ∷ ⌜ 0 ≤ sint.Z i ≤ sint.Z (slice.len sl) ⌝
  )%I.
  iAssert I with "[i rs scaledDown Hsl Hrss Hown_frags]" as "Hloop_inv".
  { iExists (W64 0), [], null. rewrite /named !drop_0 !take_0.
    replace (bool_decide (Exists (λ rs, rs_replicas rs ≠ W32 0) [])) with false
      by (symmetry; apply bool_decide_eq_false_2; inversion 1).
    iFrame "i rs scaledDown Hsl Hrss Hown_frags".
    iSplit; [iPureIntro; done|].
    iSplit; [iPureIntro; constructor|].
    iSplit; [done|].
    iPureIntro. word. }
  wp_for "Hloop_inv".
  wp_if_destruct.
  - assert (∃ this_ptr, ptrs !! sint.nat i = Some this_ptr) as
      [this_ptr Hthis_ptr].
    { apply lookup_lt_is_Some_2. rewrite Hsl_len1. word. }
    assert (∃ this_rs, old_rss !! sint.nat i = Some this_rs) as [this_rs Hthis_rs].
    { apply lookup_lt_is_Some_2. rewrite -Hlen_eq.
      pose proof (lookup_lt_Some _ _ _ Hthis_ptr). done. }
    destruct (decide (0 ≤ sint.Z i < sint.Z (slice.len sl))) as [_|Hbounds]; last word.
    wp_apply (wp_load_slice_index with "[$Hsl]"); [word| |].
    { iPureIntro. exact Hthis_ptr. }
    iIntros "Hsl". wp_auto.
    (* Lend the element's deepown and its fragments for one scale call. *)
    iDestruct (big_sepL2_lookup_acc with "Hrss") as "[Hthis Hrss_restore]";
      [exact Hthis_ptr|exact Hthis_rs|].
    rewrite (drop_S _ _ _ Hthis_rs).
    iDestruct "Hrest" as "[Hthis_frag Hrest]".
    iDestruct "Hthis_frag" as "[Hthis_meta Hthis_spec]".
    assert (ReplicaSetV.valid this_rs) as Hthis_valid.
    { rewrite Forall_lookup in Hrss_valid. eapply Hrss_valid. exact Hthis_rs. }
    wp_apply (wp_scaleReplicaSet γ model_l this_ptr this_rs (W32 0) dq_rss
      with "[$Hthis $Hthis_meta $Hthis_spec]").
    { iFrame "#". iPureIntro. split; [done|word]. }
    iIntros (scaled rs'_l this_rs')
      "(Hthis & %Hkey & %Huid & Hthis_meta & Hthis_spec & Hdisj)".
    iDestruct ("Hrss_restore" with "Hthis") as "Hrss".
    wp_auto.
    (* Either way the element is now at zero, and [scaled] reports whether it
       had to be moved. *)
    iAssert ⌜ this_rs'.(ReplicaSetV.Spec').(ReplicaSetSpecV.Replicas') = Some (W32 0)
        ∧ scaled = bool_decide (rs_replicas this_rs ≠ W32 0) ⌝%I
      as %[Hzero Hscaled_eq].
    { iDestruct "Hdisj" as "[%Hnoop|(%Hscaled & _ & %Hspec_updated)]".
      - destruct Hnoop as (Hcount & -> & -> & _). iPureIntro. split.
        + rewrite (rs_replicas_of_valid _ Hthis_valid) Hcount. done.
        + symmetry. apply bool_decide_eq_false_2. intros Hne. exact (Hne Hcount).
      - destruct Hscaled as (Hne & ->). iPureIntro. split.
        + eapply rs_scaled_spec_updated_replicas. exact Hspec_updated.
        + symmetry. apply bool_decide_eq_true_2. exact Hne. }
    (* The accumulator advances by exactly this element's contribution. *)
    assert (bool_decide (Exists (λ rs, rs_replicas rs ≠ W32 0)
        (take (sint.nat (word.add i (W64 1))) old_rss))
      = orb (bool_decide (Exists (λ rs, rs_replicas rs ≠ W32 0)
          (take (sint.nat i) old_rss))) scaled) as Hacc.
    { assert (sint.nat (word.add i (W64 1)) = S (sint.nat i)) as -> by word.
      rewrite (bool_decide_ext _ _ (exists_take_S _ _ _ _ Hthis_rs)).
      rewrite bool_decide_or -Hscaled_eq. done. }
    iAssert (([∗ list] rs;rs' ∈ take (sint.nat (word.add i (W64 1))) old_rss;
        done_rss ++ [this_rs'], FRAG rs rs') ∗
      ([∗ list] rs ∈ drop (sint.nat (word.add i (W64 1))) old_rss, FRAG rs rs))%I
      with "[Hdone Hthis_meta Hthis_spec Hrest]" as "[Hdone Hrest]".
    { assert (sint.nat (word.add i (W64 1)) = S (sint.nat i)) as -> by word.
      rewrite (take_S_r _ _ _ Hthis_rs).
      iFrame "Hrest".
      iApply (big_sepL2_app with "[$Hdone]").
      unfold FRAG. rewrite big_sepL2_singleton. iFrame. }
    assert (length (done_rss ++ [this_rs']) = sint.nat (word.add i (W64 1)))
      as Hdone_len'.
    { rewrite app_length Hdone_len /=. word. }
    assert (Forall (λ rs',
        rs'.(ReplicaSetV.Spec').(ReplicaSetSpecV.Replicas') = Some (W32 0))
        (done_rss ++ [this_rs'])) as Hdrained'.
    { apply Forall_app. split; [exact Hdone_drained|].
      constructor; [exact Hzero|constructor]. }
    destruct scaled.
    + wp_auto.
      iApply wp_for_post_do. wp_auto.
      iAssert I with "[Hi_ptr Hrs_ptr HscaledDown Hsl Hrss Hdone Hrest]"
        as "Hloop_inv".
      { iExists (word.add i (W64 1)), (done_rss ++ [this_rs']), this_ptr.
        rewrite Hacc orb_true_r.
        iFrame "Hi_ptr Hrs_ptr HscaledDown Hsl Hrss Hdone Hrest".
        iPureIntro. split_and!;
          [exact Hdone_len'|exact Hdrained'|word|word]. }
      iFrame.
    + wp_auto.
      iApply wp_for_post_do. wp_auto.
      iAssert I with "[Hi_ptr Hrs_ptr HscaledDown Hsl Hrss Hdone Hrest]"
        as "Hloop_inv".
      { iExists (word.add i (W64 1)), (done_rss ++ [this_rs']), this_ptr.
        rewrite Hacc orb_false_r.
        iFrame "Hi_ptr Hrs_ptr HscaledDown Hsl Hrss Hdone Hrest".
        iPureIntro. split_and!;
          [exact Hdone_len'|exact Hdrained'|word|word]. }
      iFrame.
  - (* Done: the whole list is drained. *)
    assert (take (sint.nat i) old_rss = old_rss) as Htake.
    { apply take_ge. word. }
    iEval (rewrite Htake) in "Hdone".
    iApply ("HΦ" $! _ done_rss).
    iFrame "Hsl Hrss Hdone". iPureIntro. split_and!.
    + word.
    + exact Hdone_drained.
    + rewrite Htake. done.
Qed.

(* rollout performs one reconciliation step: ensure the new ReplicaSet exists
   and sits at the deployment's replica count, and drain every other one.
   Without pacing this reaches the desired state in a single sync, which is why
   the postcondition is an equality rather than a progress measure. *)
Lemma wp_rollout γ model_l d_l (d : DeploymentV.t)
    sl ptrs (rss : list ReplicaSetV.t) (children : gset KKey.t)
    dq_d dq_sl dq_rss :
  {{{ "#Hpkg" ∷ is_pkg_init code.controllers.deployment.pkg_id.deployment ∗
      "#Hisk" ∷ is_kubernetes γ model_l ∗
      "#Hglobal_l" ∷ (global_addr apimodel.ModelState) ↦□ model_l ∗
      "Hd" ∷ DeploymentV.deepown_l d_l d dq_d ∗
      "Hsl" ∷ sl ↦*{dq_sl} ptrs ∗
      "Hrss" ∷ ([∗ list] ptr;rs ∈ ptrs;rss, ReplicaSetV.deepown_l ptr rs dq_rss) ∗
      "%Hd_valid" ∷ ⌜ DeploymentV.valid d ⌝ ∗
      "%Hrss_valid" ∷ ⌜ Forall ReplicaSetV.valid rss ⌝ ∗
      "%Hkeys_nodup" ∷ ⌜ NoDup (ReplicaSetV.key <$> rss) ⌝ ∗
      "%Hnamespace_valid" ∷ ⌜ valid_namespace
          d.(DeploymentV.ObjectMeta').(ObjectMetaV.Namespace') ⌝ ∗
      "%Hnew_rs_name_valid" ∷ ⌜ valid_dns1123_subdomain (new_rs_name d) ⌝ ∗
      (* The no-collision assumption, made explicit. Without it findNewReplicaSet
         may pick either of two matching ReplicaSets and stability fails —
         see notes/deployment-spec.md §2b. *)
      "%Hunique_new" ∷ ⌜ unique_new_replica_set d rss ⌝ ∗
      "Hreserved" ∷ own_available_reserved_frag γ 1 (new_rs_key d) ∗
      "Hown_children" ∷ own_children_frag γ (DeploymentV.key d)
        d.(DeploymentV.ObjectMeta').(ObjectMetaV.UID') 1 children ∗
      "Hown_frags" ∷ ([∗ list] rs ∈ rss,
        own_meta_frag γ (ReplicaSetV.key rs)
          rs.(ReplicaSetV.ObjectMeta').(ObjectMetaV.UID') 1
          rs.(ReplicaSetV.ObjectMeta') ∗
        own_spec_frag γ (ReplicaSetV.key rs)
          rs.(ReplicaSetV.ObjectMeta').(ObjectMetaV.UID') 1
          (ObjectSpecV.ReplicaSetSpec rs.(ReplicaSetV.Spec')))
  }}}
    @! deployment.rollout #d_l #sl
  {{{ (new_rs : ReplicaSetV.t) (rss' : list ReplicaSetV.t), RET #interface.nil;
      "Hd" ∷ DeploymentV.deepown_l d_l d dq_d ∗
      "Hsl" ∷ sl ↦*{dq_sl} ptrs ∗
      "Hrss" ∷ ([∗ list] ptr;rs ∈ ptrs;rss, ReplicaSetV.deepown_l ptr rs dq_rss) ∗
      (* The new ReplicaSet matches the template and sits at the deployment's
         count. *)
      "%Hnew_rs_matches" ∷ ⌜ template_matches (rs_template new_rs)
          (deployment_template d) ⌝ ∗
      "%Hnew_rs_replicas" ∷
        ⌜ new_rs.(ReplicaSetV.Spec').(ReplicaSetSpecV.Replicas') =
            Some (deployment_replicas d) ⌝ ∗
      (* Every *other* owned ReplicaSet is at zero. Keyed rather than
         positional, because the new one may or may not be in [rss]. *)
      "%Hold_drained" ∷ ⌜ Forall (λ rs',
          ReplicaSetV.key rs' = ReplicaSetV.key new_rs ∨
          rs'.(ReplicaSetV.Spec').(ReplicaSetSpecV.Replicas') = Some (W32 0))
          rss' ⌝ ∗
      (* [rss'] is the post-state of exactly the ReplicaSets passed in, so
         these fragments cover [rss] and nothing else. *)
      "Hown_frags" ∷ ([∗ list] rs;rs' ∈ rss;rss',
        own_meta_frag γ (ReplicaSetV.key rs)
          rs.(ReplicaSetV.ObjectMeta').(ObjectMetaV.UID') 1
          rs'.(ReplicaSetV.ObjectMeta') ∗
        own_spec_frag γ (ReplicaSetV.key rs)
          rs.(ReplicaSetV.ObjectMeta').(ObjectMetaV.UID') 1
          (ObjectSpecV.ReplicaSetSpec rs'.(ReplicaSetV.Spec'))) ∗
      (* The new ReplicaSet's own fragments are handed back separately only
         when it was created; when it was adopted it is already one of [rss'],
         and claiming its fragments again would duplicate them. *)
      ( ( "%Hadopted" ∷ ⌜ ∃ i, rss' !! i = Some new_rs ⌝ ∗
          "Hreserved" ∷ own_available_reserved_frag γ 1 (new_rs_key d) ∗
          "Hown_children" ∷ own_children_frag γ (DeploymentV.key d)
            d.(DeploymentV.ObjectMeta').(ObjectMetaV.UID') 1 children)
        ∨
        ( "%Hcreated" ∷ ⌜ ReplicaSetV.key new_rs = new_rs_key d ∧
              new_rs_key d ∉ (ReplicaSetV.key <$> rss) ⌝ ∗
          "Hnew_rs_meta" ∷ own_meta_frag γ (new_rs_key d)
            new_rs.(ReplicaSetV.ObjectMeta').(ObjectMetaV.UID') 1
            new_rs.(ReplicaSetV.ObjectMeta') ∗
          "Hnew_rs_spec" ∷ own_spec_frag γ (new_rs_key d)
            new_rs.(ReplicaSetV.ObjectMeta').(ObjectMetaV.UID') 1
            (ObjectSpecV.ReplicaSetSpec new_rs.(ReplicaSetV.Spec')) ∗
          "Hreserved" ∷ own_occupied_reserved_frag γ 1 (new_rs_key d)
            new_rs.(ReplicaSetV.ObjectMeta').(ObjectMetaV.UID') ∗
          "Hown_children" ∷ own_children_frag γ (DeploymentV.key d)
            d.(DeploymentV.ObjectMeta').(ObjectMetaV.UID') 1
            ({[ new_rs_key d ]} ∪ children)))
  }}}.
Proof.
Admitted.

End proof.
