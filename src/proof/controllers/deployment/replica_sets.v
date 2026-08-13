From New.proof Require Import prelude empty_ffi.
From New.proof Require Export util.
From New.proof Require Export wp_helpers.
From New.proof.kubernetes_types Require Export prelude.
From New.proof.controllers.deployment Require Export deployment_init.
From New.proof.k8s_io.api.apps Require Export v1.
From New.proof.k8s_io.kubernetes.pkg Require Export controller.
From New.proof.k8s_io.apimachinery.pkg.api Require Export errors.
From New.proof.controllers.deployment Require Export common.

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
  wp_start as "H". iNamed "H". wp_auto.
  iDestruct (own_slice_len with "Hsl") as %(Hsl_len1 & Hsl_len2).
  iDestruct (own_slice_wf with "Hsl") as %Hsl_cap.
  iDestruct (big_sepL2_length with "Hrss") as %Hptrs_rss_len.
  set P := (λ rs, template_matches (rs_template rs) (deployment_template d)).
  (* The loop has scanned rss[0..i) without finding a matching template. *)
  set I := (∃ (i : w64) (rs_ptr_value : loc),
    "Hi_ptr" ∷ i_ptr ↦ i ∗
    "Hd_ptr" ∷ d_ptr ↦ d_l ∗
    "Hd" ∷ DeploymentV.deepown_l d_l d dq1 ∗
    "Hrs_ptr" ∷ rs_ptr ↦ rs_ptr_value ∗
    "Hrss" ∷ ([∗ list] ptr;rs ∈ ptrs;rss, ReplicaSetV.deepown_l ptr rs dq3) ∗
    "%Hi" ∷ ⌜ 0 ≤ sint.Z i ≤ sint.Z (slice.len sl) ⌝ ∗
    "%Hnot_found" ∷ ⌜ ∀ j r, (j < sint.nat i)%nat → rss !! j = Some r → ¬ P r ⌝
  )%I.
  iAssert I with "[i d Hd rs Hrss]" as "Hloop_inv".
  { iExists (W64 0), null. iFrame.
    iPureIntro. split; [word|]. intros j r Hj. exfalso. word. }
  wp_for "Hloop_inv". wp_if_destruct.
  - list_elem ptrs (sint.Z i) as this_ptr.
    destruct (decide (0 ≤ sint.Z i < sint.Z (slice.len sl))) as [_|Hbounds]; last word.
    wp_apply (wp_load_slice_index with "[$Hsl]"); [word| |].
    { iPureIntro. exact Hthis_ptr_lookup. }
    iIntros "Hsl". wp_auto.
    assert (∃ this_rs, rss !! sint.nat i = Some this_rs) as [this_rs Hthis_rs_lookup].
    { apply lookup_lt_is_Some_2. rewrite -Hptrs_rss_len Hsl_len1. word. }
    iDestruct (big_sepL2_lookup_acc with "Hrss") as "[Hthis Hrss_restore]";
      [exact Hthis_ptr_lookup|exact Hthis_rs_lookup|].
    (* equalIgnoreHash takes &rs.Spec.Template and &d.Spec.Template, so both
       specs have to be split all the way down to their Template fields. *)
    iPoseProof (ReplicaSetV.deepown_l_split with "Hthis") as
      "(%Hthis_not_null & Hthis_typemeta & Hthis_objectmeta_l & Hthis_spec_l & Hthis_status_l)".
    iDestruct "Hthis_spec_l" as (rs_spec_c) "[Hthis_spec_field Hthis_spec]".
    iDestruct (struct_fields_split (V:=v1.ReplicaSetSpec.t) with "Hthis_spec_field") as
      "[Hrs_spec_fields %Hrs_spec_not_null]".
    iNamedPrefix "Hrs_spec_fields" "Hrsf_".
    iPoseProof (DeploymentV.deepown_l_split with "Hd") as
      "(%Hd_not_null & Hd_typemeta & Hd_objectmeta_l & Hd_spec_l & Hd_status_l)".
    iDestruct "Hd_spec_l" as (d_spec_c) "[Hd_spec_field Hd_spec]".
    iDestruct (struct_fields_split (V:=v1.DeploymentSpec.t) with "Hd_spec_field") as
      "[Hd_spec_fields %Hd_spec_not_null]".
    iNamedPrefix "Hd_spec_fields" "Hdf_".
    iNamedPrefix "Hthis_spec" "Hrs_".
    iNamedPrefix "Hd_spec" "Hd_".
    wp_apply (wp_equalIgnoreHash with
      "[$Hrsf_Template $Hrs_Hdeepown_template $Hdf_Template $Hd_Hdeepown_template]").
    iIntros "(Hrsf_Template & Hrs_Hdeepown_template & Hdf_Template & Hd_Hdeepown_template)".
    (* Put both objects back together before branching. *)
    iCombineNamed "Hrsf_*" as "Hrs_spec_fields".
    iAssert (typed_pointsto_def (ReplicaSetV.spec_ptr this_ptr) rs_spec_c dq3)
      with "[Hrs_spec_fields]" as "Hrs_spec_fields".
    { iNamed "Hrs_spec_fields". destruct rs_spec_c. simpl. iFrame. }
    iDestruct (struct_fields_combine _ _ _ Hrs_spec_not_null with "Hrs_spec_fields")
      as "Hthis_spec_field".
    iCombineNamed "Hdf_*" as "Hd_spec_fields".
    iAssert (typed_pointsto_def (DeploymentV.spec_ptr d_l) d_spec_c dq1)
      with "[Hd_spec_fields]" as "Hd_spec_fields".
    { iNamed "Hd_spec_fields". destruct d_spec_c. simpl. iFrame. }
    iDestruct (struct_fields_combine _ _ _ Hd_spec_not_null with "Hd_spec_fields")
      as "Hd_spec_field".
    iCombineNamed "Hrs_Hdeepown_*" as "Hthis_spec_parts".
    iAssert (ReplicaSetSpecV.deepown rs_spec_c (ReplicaSetV.Spec' this_rs) dq3)
      with "[Hthis_spec_parts]" as "Hthis_spec".
    { iNamed "Hthis_spec_parts". iFrame. done. }
    iCombineNamed "Hd_Hdeepown_*" as "Hd_spec_parts".
    iAssert (DeploymentSpecV.deepown d_spec_c (DeploymentV.Spec' d) dq1)
      with "[Hd_spec_parts]" as "Hd_spec".
    { iNamed "Hd_spec_parts". iFrame. done. }
    iPoseProof (ReplicaSetV.deepown_l_restore _ _ _ Hthis_not_null
      with "[$Hthis_typemeta $Hthis_objectmeta_l $Hthis_status_l Hthis_spec_field Hthis_spec]")
      as "Hthis".
    { iExists rs_spec_c. iFrame. }
    iPoseProof (DeploymentV.deepown_l_restore _ _ _ Hd_not_null
      with "[$Hd_typemeta $Hd_objectmeta_l $Hd_status_l Hd_spec_field Hd_spec]") as "Hd".
    { iExists d_spec_c. iFrame. }
    iSpecialize ("Hrss_restore" with "Hthis").
    iRename "Hrss_restore" into "Hrss".
    wp_if_destruct.
    + (* This template matches, and Hnot_found rules out every earlier one, so
         this index is the one list_find picks. *)
      iApply wp_for_post_return. wp_auto.
      assert (find_new_replica_set d rss = Some (sint.nat i, this_rs)) as Hfind.
      { apply list_find_Some. split_and!.
        - exact Hthis_rs_lookup.
        - assumption.
        - intros j r Hlookup Hj HP.
          eapply (Hnot_found j r); [lia|exact Hlookup|exact HP]. }
      iApply ("HΦ" $! this_ptr). rewrite Hfind. iFrame. done.
    + iApply wp_for_post_do. wp_auto.
      iFrame "Hsl HΦ".
      iExists (word.add i (W64 1)), this_ptr.
      iFrame.
      iPureIntro. split; [word|].
      intros j r Hj Hlookup HP.
      destruct (decide (j < sint.nat i)%nat) as [Hj_old|Hj_not_old].
      * eapply (Hnot_found j r); done.
      * assert (j = sint.nat i) as -> by word.
        rewrite Hthis_rs_lookup in Hlookup.
        injection Hlookup as <-.
        contradiction.
  - (* The loop ran off the end, so no template matched. *)
    assert (sint.nat i = length rss) as Hi_len.
    { rewrite -Hptrs_rss_len Hsl_len1. word. }
    assert (find_new_replica_set d rss = None) as Hfind.
    { apply list_find_None. apply Forall_forall.
      intros r Hr HP.
      rewrite -list_elem_of_In in Hr.
      apply list_elem_of_lookup_1 in Hr as [j Hlookup].
      eapply (Hnot_found j r); [|exact Hlookup|exact HP].
      rewrite Hi_len. apply lookup_lt_Some in Hlookup. lia. }
    iApply ("HΦ" $! null). rewrite Hfind. iFrame. done.
Qed.

End proof.
