From New.proof Require Import wp_keep.
From New.proof Require Import prelude empty_ffi.
From New.proof Require Export util.
From New.proof Require Export wp_helpers.
From New.object_specs Require Export prelude.
From New.proof.controllers.deployment Require Export deployment_init.
From New.proof.k8s_io.api.apps Require Export v1.
From New.proof.k8s_io.kubernetes.pkg Require Export controller.
From New.proof.k8s_io.apimachinery.pkg.api Require Export errors.
From New.proof.controllers.deployment Require Export common.


Local Transparent ObjectMetaV.deepown ObjectMetaView.ObjectMetaV.deepown.
(* Collect transient allocations from imports before checking large program proofs. *)
Optimize Heap.

Section proof.
Context `{hG: !heapGS Σ}.
Context {sem : go.Semantics}
  {package_sem : code.controllers.deployment.deployment.Assumptions}.
Context {model_sem : apimodel.Assumptions}.
Collection W := sem + package_sem + model_sem.
#[local] Instance controller_sem : controller.Assumptions :=
  code.controllers.deployment.deployment.import_controller_Assumption.
#[local] Instance base_apimodel_sem : apimodel.Assumptions | 100 :=
  model_sem.
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
Proof using package_sem model_sem.
  constructor; try exact object_core_v1_sem; try apply _.
Defined.
Local Set Default Proof Using "All".
Context `{!KObjectV.ObjectInterfaceAssumptions}.
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
    wp_auto_keep.
    wp_if_destruct; [exfalso; done|].
    wp_pures_keep.
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
    wp_auto_keep.
    rewrite Hptr_null.
    wp_if_destruct; [|exfalso; congruence].
    wp_pures_keep.
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
      wp_auto_keep.
      wp_if_destruct; [exfalso; done|].
      wp_if_destruct; [exfalso; done|].
      wp_pures_keep.
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
      wp_auto_keep.
      wp_if_destruct; [exfalso; done|].
      rewrite Hpn.
      wp_if_destruct; [|exfalso; congruence].
      wp_pures_keep.
      iApply "HΦ".
      iApply (ReplicaSetV.deepown_l_restore _ _ _ Hnn).
      iFrame "Htm Hom Hstatus_l".
      iExists spec_c. iFrame "Hspec_field".
      rewrite /ReplicaSetSpecV.deepown Hrepl.
      iSplit; [iPureIntro; split; [done|intros _; exact Hpn]|].
      iSplitR; [done|].
      iFrame "%". iFrame.
  - iDestruct "Hrs" as %Hrs_null.
    wp_auto_keep. rewrite Hrs_null.
    wp_if_destruct; [|exfalso; congruence].
    wp_pures_keep.
    iApply "HΦ". done.
Qed.

(* findOldReplicaSets finds the new ReplicaSet itself with upstream's
   FindNewReplicaSet, which sorts [rsList] in place, and keeps every other
   entry of the sorted list. [newRS] is either nil or an entry of that list, so
   its UID is read by opening that entry. *)
Lemma wp_findOldReplicaSets d_l (d : DeploymentV.t) sl ptrs
    (rss : list ReplicaSetV.t) dq1 dq3 :
  {{{ is_pkg_init code.controllers.deployment.pkg_id.deployment ∗
      "Hd" ∷ DeploymentV.deepown_l d_l d dq1 ∗
      "Hsl" ∷ sl ↦* ptrs ∗
      "Hrss" ∷ ([∗ list] ptr;rs ∈ ptrs;rss, ReplicaSetV.deepown_l ptr rs dq3) ∗
      "%Hlabels" ∷ ⌜ template_has_labels (deployment_template d) ∧
        Forall (λ rs, template_has_labels (rs_template rs)) rss ⌝ ∗
      "%Htimes" ∷ ⌜ creation_times_comparable rss ⌝
  }}}
    @! deployment.findOldReplicaSets #d_l #sl
  {{{ sl' ptrs' rss', RET #sl';
      ⌜ zip ptrs rss ≡ₚ zip ptrs' rss' ∧ sorted_by rs_created_before rss' ⌝ ∗
      sl' ↦* ((old_replica_set_pairs ptrs' rss'
        (snd <$> find_new_replica_set d rss')).*1) ∗
      own_slice_cap loc sl' (DfracOwn 1) ∗
      DeploymentV.deepown_l d_l d dq1 ∗
      sl ↦* ptrs' ∗
      ([∗ list] ptr;rs ∈ ptrs';rss', ReplicaSetV.deepown_l ptr rs dq3)
  }}}.
Proof.
  wp_start as "H". iNamed "H". wp_auto_keep.
  (* allRSs starts as a nil slice. *)
  iPoseProof (own_slice_nil (V:=loc) (DfracOwn 1)) as "Hnil_sl".
  iPoseProof (own_slice_cap_nil (V:=loc)) as "Hnil_cap".
  iAssert (is_pkg_init util) as "#Hutil". { iPkgInit. }
  rename ptrs into ptrs0. rename rss into rss0.
  wp_apply (wp_FindNewReplicaSet with "[$Hutil $Hd $Hsl $Hrss]"); first done.
  iIntros (new_rs_l ptrs rss) "(%Hsorted & Hfind & Hd & Hsl & Hrss)".
  iAssert (match find_new_replica_set d rss with
      | Some (i, _) => ⌜ ptrs !! i = Some new_rs_l ⌝
      | None => ⌜ new_rs_l = null ⌝
      end)%I with "[Hfind]" as "Hfind"; first iExact "Hfind".
  clear Hlabels Htimes. wp_auto_keep.
  remember (snd <$> find_new_replica_set d rss) as new_rs_o eqn:Hnew_rs_o.
  (* [newRS] is nil exactly when no template matches; otherwise it is the
     matching entry of the list. *)
  iAssert (⌜ match new_rs_o with
      | Some new_rs => ∃ j, ptrs !! j = Some new_rs_l ∧ rss !! j = Some new_rs
      | None => new_rs_l = null
      end ⌝)%I with "[Hfind]" as %Hnew.
  { subst new_rs_o.
    destruct (find_new_replica_set d rss) as [[j new_rs]|] eqn:Hfound; simpl.
    - iDestruct "Hfind" as %Hj_ptr. iPureIntro. exists j. split; [exact Hj_ptr|].
      unfold find_new_replica_set in Hfound.
      apply list_find_Some in Hfound as (Hj_rs & _ & _). exact Hj_rs.
    - iDestruct "Hfind" as %Hnull. iPureIntro. exact Hnull. }
  iClear "Hfind".
  iDestruct (own_slice_len with "Hsl") as %(Hsl_len1 & Hsl_len2).
  iDestruct (big_sepL2_length with "Hrss") as %Hptrs_rss_len.
  (* A list entry is never nil, so [newRS] is nil exactly when there is no
     new ReplicaSet. *)
  iAssert (([∗ list] ptr;rs ∈ ptrs;rss, ReplicaSetV.deepown_l ptr rs dq3) ∗
      ⌜ new_rs_l = null ↔ new_rs_o = None ⌝)%I
    with "[Hrss]" as "[Hrss %Hnew_null]".
  { destruct new_rs_o as [new_rs|].
    - destruct Hnew as (j & Hj_ptr & Hj_rs).
      iDestruct (big_sepL2_lookup_acc with "Hrss") as "[Hj Hrss_restore]";
        [exact Hj_ptr|exact Hj_rs|].
      iDestruct "Hj" as (j_c) "[Hj_l Hj]".
      iDestruct (typed_pointsto_not_null with "Hj_l") as %Hnn.
      iDestruct ("Hrss_restore" with "[Hj_l Hj]") as "Hrss".
      { iExists j_c. iFrame. }
      iFrame "Hrss". iPureIntro. split; [done|discriminate].
    - iFrame "Hrss". iPureIntro. split; [done|]. intros _. exact Hnew. }
  set Q := (λ pr : loc * ReplicaSetV.t, rs_is_old new_rs_o pr.2).
  (* [allRSs] holds exactly the old ReplicaSets found among the first i entries. *)
  set I := (∃ (i : w64) (rs_ptr_value : loc) (old_sl : slice.t),
    "Hi_ptr" ∷ i_ptr ↦ i ∗
    "Hold_ptr" ∷ allRSs_ptr ↦ old_sl ∗
    "Hrs_ptr" ∷ rs_ptr ↦ rs_ptr_value ∗
    "HnewRS_ptr" ∷ newRS_ptr ↦ new_rs_l ∗
    "Hold_sl" ∷ old_sl ↦* ((filter Q (take (sint.nat i) (zip ptrs rss))).*1) ∗
    "Hold_cap" ∷ own_slice_cap loc old_sl (DfracOwn 1) ∗
    "Hrss" ∷ ([∗ list] ptr;rs ∈ ptrs;rss, ReplicaSetV.deepown_l ptr rs dq3) ∗
    "%Hi" ∷ ⌜ 0 ≤ sint.Z i ≤ sint.Z (slice.len sl) ⌝
  )%I.
  iAssert I with "[i allRSs rs newRS Hrss]" as "Hloop_inv".
  { iExists (W64 0), null, slice.nil. iFrame.
    replace (sint.nat (W64 0)) with 0%nat by word. rewrite take_0 /=.
    iFrame "Hnil_sl Hnil_cap". iPureIntro. word. }
  iClear "Hnil_sl Hnil_cap".
  wp_for "Hloop_inv". wp_if_destruct.
  - list_elem ptrs (sint.Z i) as this_ptr.
    destruct (decide (0 ≤ sint.Z i < sint.Z (slice.len sl))) as [_|Hbounds]; last word.
    wp_apply (wp_load_slice_index with "[$Hsl]"); [word| |].
    { iPureIntro. exact Hthis_ptr_lookup. }
    iIntros "Hsl". wp_auto_keep.
    assert (∃ this_rs, rss !! sint.nat i = Some this_rs) as [this_rs Hthis_rs_lookup].
    { apply lookup_lt_is_Some_2. rewrite -Hptrs_rss_len Hsl_len1. word. }
    assert (zip ptrs rss !! sint.nat i = Some (this_ptr, this_rs)) as Hzip_lookup.
    { rewrite lookup_zip_with Hthis_ptr_lookup Hthis_rs_lookup. done. }
    assert (sint.nat (word.add i (W64 1)) = S (sint.nat i)) as Hnext by word.
    destruct (decide (new_rs_l = null)) as [Hnull|Hnot_null].
    + (* No new ReplicaSet: the guard fails before any UID is read, and every
         entry is old. *)
      rewrite (bool_decide_eq_true_2 _ Hnull). simpl.
      assert (snd <$> find_new_replica_set d rss = None) as Hnone by (apply Hnew_null; exact Hnull).
      wp_auto_keep.
      wp_apply wp_slice_literal. iSplitR; first done.
      iIntros (one_sl) "[Hone_sl _]". wp_auto_keep.
      wp_apply (wp_slice_append with "[$Hold_sl $Hold_cap $Hone_sl]").
      iIntros (old_sl') "(Hold_sl & Hold_cap & _)". wp_auto_keep.
      iApply wp_for_post_do. wp_auto_keep.
      assert (Q (this_ptr, this_rs)) as HQ.
      { unfold Q. rewrite Hnone. exact Logic.I. }
      assert (filter Q (take (sint.nat (word.add i (W64 1))) (zip ptrs rss)) =
        filter Q (take (sint.nat i) (zip ptrs rss)) ++ [(this_ptr, this_rs)]) as Hfilter_eq.
      { rewrite Hnext (take_S_r _ _ (this_ptr, this_rs) Hzip_lookup) list.filter_app.
        rewrite (filter_singleton_True Q (this_ptr, this_rs) [] HQ). done. }
      iFrame "Hsl HΦ Hd".
      iExists (word.add i (W64 1)), this_ptr, old_sl'.
      rewrite Hfilter_eq fmap_app. iFrame. iPureIntro. word.
    + assert (∃ new_rs, snd <$> find_new_replica_set d rss = Some new_rs) as [new_rs Hsome].
      { destruct (snd <$> find_new_replica_set d rss) as [new_rs|]; [by eexists|].
        exfalso. apply Hnot_null. apply Hnew_null. done. }
      rewrite Hsome in Hnew. destruct Hnew as (j & Hj_ptr & Hj_rs).
      rewrite (bool_decide_eq_false_2 _ Hnot_null). simpl.
      (* First operand: the current entry's UID, with only that entry open. *)
      iDestruct (big_sepL2_lookup_acc with "Hrss") as "[Hthis Hrss_restore]";
        [exact Hthis_ptr_lookup|exact Hthis_rs_lookup|].
      iPoseProof (ReplicaSetV.deepown_l_split with "Hthis") as
        "(%Hthis_not_null & Hthis_typemeta & Hthis_objectmeta_l & Hthis_spec_l & Hthis_status_l)".
      iDestruct "Hthis_objectmeta_l" as (this_meta_c) "[Hthis_meta_field Hthis_meta]".
      iNamedPrefix "Hthis_meta" "Hthis_meta_".
      wp_auto_keep.
      rewrite Hthis_meta_Hdeepown_uid.
      iCombineNamed "Hthis_meta_Hdeepown_*" as "Hthis_meta_parts".
      iAssert (ObjectMetaV.deepown this_meta_c (ReplicaSetV.ObjectMeta' this_rs) dq3)
        with "[Hthis_meta_parts]" as "Hthis_meta".
      { iNamed "Hthis_meta_parts". iFrame. done. }
      iPoseProof (ReplicaSetV.deepown_l_restore _ _ _ Hthis_not_null
        with "[$Hthis_typemeta $Hthis_spec_l $Hthis_status_l Hthis_meta_field Hthis_meta]")
        as "Hthis".
      { iExists this_meta_c. iFrame. }
      iSpecialize ("Hrss_restore" with "Hthis").
      iRename "Hrss_restore" into "Hrss".
      (* Splitting an ObjectMeta leaves ~15 spent pure facts behind; dropping
         them keeps the tactics below from crawling. *)
      clear Hthis_meta_Hdeepown_name Hthis_meta_Hdeepown_generatename
        Hthis_meta_Hdeepown_namespace Hthis_meta_Hdeepown_selflink
        Hthis_meta_Hdeepown_uid Hthis_meta_Hdeepown_resourceversion
        Hthis_meta_Hdeepown_generation Hthis_meta_Hdeepown_deletiontimestamp_none
        Hthis_meta_Hdeepown_deletiongraceperiodseconds_none
        Hthis_meta_Hdeepown_labels_none Hthis_meta_Hdeepown_annotations_none
        Hthis_meta_Hdeepown_finalizers_none this_meta_c.
      (* Second operand: newRS's UID, read from its own entry of the list. The
         entry above is already restored, so newRS being the entry just
         inspected is fine. *)
      iDestruct (big_sepL2_lookup_acc with "Hrss") as "[Hnew_own Hrss_restore]";
        [exact Hj_ptr|exact Hj_rs|].
      iPoseProof (ReplicaSetV.deepown_l_split with "Hnew_own") as
        "(%Hnew_nn & Hnew_typemeta & Hnew_objectmeta_l & Hnew_spec_l & Hnew_status_l)".
      iDestruct "Hnew_objectmeta_l" as (new_meta_c) "[Hnew_meta_field Hnew_meta]".
      iNamedPrefix "Hnew_meta" "Hnew_meta_".
      wp_auto_keep.
      rewrite Hnew_meta_Hdeepown_uid.
      iCombineNamed "Hnew_meta_Hdeepown_*" as "Hnew_meta_parts".
      iAssert (ObjectMetaV.deepown new_meta_c (ReplicaSetV.ObjectMeta' new_rs) dq3)
        with "[Hnew_meta_parts]" as "Hnew_meta".
      { iNamed "Hnew_meta_parts". iFrame. done. }
      iPoseProof (ReplicaSetV.deepown_l_restore _ _ _ Hnew_nn
        with "[$Hnew_typemeta $Hnew_spec_l $Hnew_status_l Hnew_meta_field Hnew_meta]")
        as "Hnew_own".
      { iExists new_meta_c. iFrame. }
      iSpecialize ("Hrss_restore" with "Hnew_own").
      iRename "Hrss_restore" into "Hrss".
      clear Hnew_meta_Hdeepown_name Hnew_meta_Hdeepown_generatename
        Hnew_meta_Hdeepown_namespace Hnew_meta_Hdeepown_selflink
        Hnew_meta_Hdeepown_uid Hnew_meta_Hdeepown_resourceversion
        Hnew_meta_Hdeepown_generation Hnew_meta_Hdeepown_deletiontimestamp_none
        Hnew_meta_Hdeepown_deletiongraceperiodseconds_none
        Hnew_meta_Hdeepown_labels_none Hnew_meta_Hdeepown_annotations_none
        Hnew_meta_Hdeepown_finalizers_none new_meta_c.
      wp_if_destruct.
      * (* Same UID as newRS: skip it, so the filter drops this entry. *)
        iApply wp_for_post_continue. wp_auto_keep.
        assert (¬ Q (this_ptr, this_rs)) as HnotQ.
        { unfold Q. rewrite Hsome. unfold rs_is_old, rs_uid. simpl.
          intros Hne. apply Hne. congruence. }
        assert (filter Q (take (sint.nat (word.add i (W64 1))) (zip ptrs rss)) =
          filter Q (take (sint.nat i) (zip ptrs rss))) as Hfilter_eq.
        { rewrite Hnext (take_S_r _ _ (this_ptr, this_rs) Hzip_lookup) list.filter_app.
          rewrite (filter_singleton_False Q (this_ptr, this_rs) [] HnotQ) app_nil_r. done. }
        iFrame "Hsl HΦ Hd".
        iExists (word.add i (W64 1)), this_ptr, old_sl.
        rewrite Hfilter_eq. iFrame. iPureIntro. word.
      * wp_apply wp_slice_literal. iSplitR; first done.
        iIntros (one_sl) "[Hone_sl _]". wp_auto_keep.
        wp_apply (wp_slice_append with "[$Hold_sl $Hold_cap $Hone_sl]").
        iIntros (old_sl') "(Hold_sl & Hold_cap & _)". wp_auto_keep.
        iApply wp_for_post_do. wp_auto_keep.
        assert (Q (this_ptr, this_rs)) as HQ.
        { unfold Q. rewrite Hsome. unfold rs_is_old, rs_uid. simpl. congruence. }
        assert (filter Q (take (sint.nat (word.add i (W64 1))) (zip ptrs rss)) =
          filter Q (take (sint.nat i) (zip ptrs rss)) ++ [(this_ptr, this_rs)]) as Hfilter_eq.
        { rewrite Hnext (take_S_r _ _ (this_ptr, this_rs) Hzip_lookup) list.filter_app.
          rewrite (filter_singleton_True Q (this_ptr, this_rs) [] HQ). done. }
        iFrame "Hsl HΦ Hd".
        iExists (word.add i (W64 1)), this_ptr, old_sl'.
        rewrite Hfilter_eq fmap_app. iFrame. iPureIntro. word.
  - (* The whole list was scanned, so the prefix is all of it. *)
    assert (sint.nat i = length ptrs) as Hi_len by (rewrite Hsl_len1; word).
    assert (take (sint.nat i) (zip ptrs rss) = zip ptrs rss) as Htake.
    { apply take_ge. rewrite length_zip_with Hi_len -Hptrs_rss_len. lia. }
    iApply ("HΦ" $! old_sl ptrs rss). rewrite Htake. iFrame. done.
Qed.

End proof.
