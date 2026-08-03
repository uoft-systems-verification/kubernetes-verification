From New.proof Require Import prelude empty_ffi.
From New.proof Require Export util.
From New.proof Require Export wp_helpers.
From New.proof.kubernetes_types Require Export prelude.
From New.proof.controllers.deployment Require Export deployment_init.
From New.proof.k8s_io.api.apps Require Export v1.
From New.proof.k8s_io.kubernetes.pkg Require Export controller.
From New.proof.k8s_io.apimachinery.pkg.api Require Export errors.
From New.proof.controllers.deployment Require Export model.

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
Local Set Default Proof Using "All".
Lemma wp_replicasOf d_l (d : DeploymentV.t) dq :
  {{{ is_pkg_init code.controllers.deployment.pkg_id.deployment ∗
      "Hd" ∷ DeploymentV.deepown_l d_l d dq
  }}}
    @! deployment.replicasOf #d_l
  {{{ RET #(deployment_replicas d);
      DeploymentV.deepown_l d_l d dq
  }}}.
Proof.
  wp_start as "H". iNamed "H".
  iPoseProof (DeploymentV.deepown_l_split with "Hd") as
    "(%Hnot_null & Htypemeta & Hobjectmeta & Hspec_l & Hstatus_l)".
  iDestruct "Hspec_l" as (spec_c) "[Hspec_field Hspec]".
  iNamed "Hspec".
  unfold deployment_replicas.
  destruct d.(DeploymentV.Spec').(DeploymentSpecV.Replicas') as [replicas|] eqn:Hreplicas.
  - iDestruct "Hdeepown_replicas_some" as (replicas_c) "[Hreplicas ->]".
    assert (spec_c.(v1.DeploymentSpec.Replicas') ≠ null) as Hptr_not_null.
    { intros Hnull. apply Hdeepown_replicas_none in Hnull. congruence. }
    wp_auto.
    wp_if_destruct; [exfalso; done|].
    wp_pures.
    iApply "HΦ".
    iApply (DeploymentV.deepown_l_restore _ _ _ Hnot_null).
    iFrame "Htypemeta Hobjectmeta Hstatus_l".
    iExists spec_c. iFrame "Hspec_field".
    rewrite /DeploymentSpecV.deepown Hreplicas.
    iSplit; [iPureIntro; exact Hdeepown_replicas_none|].
    iSplitL "Hreplicas"; [iExists replicas; iFrame "Hreplicas"; done|].
    iFrame "%". iFrame.
  - assert (spec_c.(v1.DeploymentSpec.Replicas') = null) as Hptr_null.
    { apply Hdeepown_replicas_none. done. }
    wp_auto.
    rewrite Hptr_null.
    wp_if_destruct; [|exfalso; congruence].
    wp_pures.
    iApply "HΦ".
    iApply (DeploymentV.deepown_l_restore _ _ _ Hnot_null).
    iFrame "Htypemeta Hobjectmeta Hstatus_l".
    iExists spec_c. iFrame "Hspec_field".
    rewrite /DeploymentSpecV.deepown Hreplicas.
    iSplit; [iPureIntro; split; [done|intros _; exact Hptr_null]|].
    iSplitR; [done|].
    iFrame "%". iFrame.
Qed.

Lemma wp_replicasOfRS rs_l (rs_o : option ReplicaSetV.t) dq :
  {{{ is_pkg_init code.controllers.deployment.pkg_id.deployment ∗
      "Hrs" ∷ rs_opt_own rs_l rs_o dq
  }}}
    @! deployment.replicasOfRS #rs_l
  {{{ RET #(rs_opt_replicas rs_o);
      rs_opt_own rs_l rs_o dq
  }}}.
Proof.
  wp_start as "H". iNamed "H".
  unfold rs_opt_replicas, rs_opt_own.
  destruct rs_o as [rs|].
  - iPoseProof (ReplicaSetV.deepown_l_split with "Hrs") as
      "(%Hnn & Htm & Hom & Hspec_l & Hstatus_l)".
    iDestruct "Hspec_l" as (spec_c) "[Hspec_field Hspec]".
    iNamed "Hspec".
    unfold rs_replicas.
    destruct rs.(ReplicaSetV.Spec').(ReplicaSetSpecV.Replicas') as [replicas|] eqn:Hrepl.
    + iDestruct "Hdeepown_replicas_some" as (rc) "[Hr ->]".
      assert (spec_c.(v1.ReplicaSetSpec.Replicas') ≠ null) as Hpnn.
      { intros Hnull. apply Hdeepown_replicas_none in Hnull. congruence. }
      wp_auto.
      wp_if_destruct; [exfalso; done|].
      wp_if_destruct; [exfalso; done|].
      wp_pures.
      iApply "HΦ".
      iApply (ReplicaSetV.deepown_l_restore _ _ _ Hnn).
      iFrame "Htm Hom Hstatus_l".
      iExists spec_c. iFrame "Hspec_field".
      rewrite /ReplicaSetSpecV.deepown Hrepl.
      iSplit; [iPureIntro; exact Hdeepown_replicas_none|].
      iSplitL "Hr"; [iExists replicas; iFrame "Hr"; done|].
      iFrame "%". iFrame.
    + assert (spec_c.(v1.ReplicaSetSpec.Replicas') = null) as Hpn.
      { apply Hdeepown_replicas_none. done. }
      wp_auto.
      wp_if_destruct; [exfalso; done|].
      rewrite Hpn.
      wp_if_destruct; [|exfalso; congruence].
      wp_pures.
      iApply "HΦ".
      iApply (ReplicaSetV.deepown_l_restore _ _ _ Hnn).
      iFrame "Htm Hom Hstatus_l".
      iExists spec_c. iFrame "Hspec_field".
      rewrite /ReplicaSetSpecV.deepown Hrepl.
      iSplit; [iPureIntro; split; [done|intros _; exact Hpn]|].
      iSplitR; [done|].
      iFrame "%". iFrame.
  - iDestruct "Hrs" as %Hrs_null.
    wp_auto. rewrite Hrs_null.
    wp_if_destruct; [|exfalso; congruence].
    wp_pures.
    iApply "HΦ". done.
Qed.

Lemma wp_findOldReplicaSets sl ptrs (rss : list ReplicaSetV.t)
    new_rs_l (new_rs_o : option ReplicaSetV.t) dq1 dq2 dq3 :
  {{{ is_pkg_init code.controllers.deployment.pkg_id.deployment ∗
      "Hsl" ∷ sl ↦*{dq1} ptrs ∗
      "Hrss" ∷ ([∗ list] ptr;rs ∈ ptrs;rss, ReplicaSetV.deepown_l ptr rs dq2) ∗
      "Hnew" ∷ rs_opt_own new_rs_l new_rs_o dq3
  }}}
    @! deployment.findOldReplicaSets #sl #new_rs_l
  {{{ sl', RET #sl';
      sl ↦*{dq1} ptrs ∗
      sl' ↦* ((old_replica_set_pairs ptrs rss new_rs_o).*1) ∗
      own_slice_cap loc sl' (DfracOwn 1) ∗
      ([∗ list] ptr;rs ∈ ptrs;rss, ReplicaSetV.deepown_l ptr rs dq2) ∗
      rs_opt_own new_rs_l new_rs_o dq3
  }}}.
Proof.
Admitted.

Lemma wp_equalIgnoreHash t1_l t2_l c1 c2 tv1 tv2 dq1 dq2 :
  {{{ is_pkg_init code.controllers.deployment.pkg_id.deployment ∗
      "Ht1_l" ∷ t1_l ↦{dq1} c1 ∗
      "Ht1" ∷ PodTemplateSpecV.deepown c1 tv1 dq1 ∗
      "Ht2_l" ∷ t2_l ↦{dq2} c2 ∗
      "Ht2" ∷ PodTemplateSpecV.deepown c2 tv2 dq2
  }}}
    @! deployment.equalIgnoreHash #t1_l #t2_l
  {{{ RET #(bool_decide (template_matches tv1 tv2));
      t1_l ↦{dq1} c1 ∗
      PodTemplateSpecV.deepown c1 tv1 dq1 ∗
      t2_l ↦{dq2} c2 ∗
      PodTemplateSpecV.deepown c2 tv2 dq2
  }}}.
Proof.
Admitted.

Lemma wp_findNewReplicaSet d_l (d : DeploymentV.t) sl ptrs (rss : list ReplicaSetV.t)
    dq1 dq2 dq3 :
  {{{ is_pkg_init code.controllers.deployment.pkg_id.deployment ∗
      "Hd" ∷ DeploymentV.deepown_l d_l d dq1 ∗
      "Hsl" ∷ sl ↦*{dq2} ptrs ∗
      "Hrss" ∷ ([∗ list] ptr;rs ∈ ptrs;rss, ReplicaSetV.deepown_l ptr rs dq3)
  }}}
    @! deployment.findNewReplicaSet #d_l #sl
  {{{ (rs_l : loc), RET #rs_l;
      (match find_new_replica_set d rss with
       | Some (i, _) => ⌜ ptrs !! i = Some rs_l ⌝
       | None => ⌜ rs_l = null ⌝
       end) ∗
      DeploymentV.deepown_l d_l d dq1 ∗
      sl ↦*{dq2} ptrs ∗
      ([∗ list] ptr;rs ∈ ptrs;rss, ReplicaSetV.deepown_l ptr rs dq3)
  }}}.
Proof.
Admitted.

End proof.
