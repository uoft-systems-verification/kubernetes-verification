From New.proof Require Import prelude empty_ffi.
From New.proof.kubernetes_model Require Export get create_named update.
From New.proof.kubernetes_model Require Export index_replicaset.
From New.proof Require Export util.
From New.proof Require Export wp_helpers.
From New.proof.kubernetes_types Require Export prelude.
From New.proof.controllers.deployment Require Export deployment_init.
From New.proof.k8s_io.api.apps Require Export v1.
From New.proof.k8s_io.kubernetes.pkg Require Export controller.
From New.proof.k8s_io.apimachinery.pkg.api Require Export errors.
From New.proof.controllers.deployment Require Export
  common replica_sets rollout top_level.

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
(* Top-level specs: the controller's entry point and its listing.    *)
(* ---------------------------------------------------------------- *)

(* filterReplicaSetsByOwner fetches the deployment's ReplicaSets through the
   replicaSetController index (deployment.go:211), mirroring how
   controllers/common's FilterPodsByOwner fetches Pods.

   It used to list the namespace and filter in Go. That shape was
   unprovable, not merely unproved: the listing specs in
   kubernetes_model/list_weak.v are fragment-free, so nothing related what
   they returned to the deployment's [own_children_frag]. Q3 settled on the
   index, whose key *is* the owner reference. The remaining semantic core is
   isolated in [wp_State__ByIndex_replicaSetController]
   (kubernetes_model/index_replicaset.v), the one trusted lemma left in H2.

   Fractions are uniform over the ReplicaSets, which is what both callers
   have: stability holds everything at [dq], progress at 1. *)
Lemma wp_filterReplicaSetsByOwner γ model_l d_l (d : DeploymentV.t)
    (rss : list ReplicaSetV.t) (children_keys : gset KKey.t)
    dq_d dq_rs children_dq :
  {{{ is_pkg_init code.controllers.deployment.pkg_id.deployment ∗
      "#Hisk" ∷ is_kubernetes γ model_l ∗
      "#Hglobal_l" ∷ (global_addr apimodel.ModelState) ↦□ model_l ∗
      "Hd" ∷ DeploymentV.deepown_l d_l d dq_d ∗
      "%Hslash_free" ∷ ⌜ slash_free DeploymentV.kind ∧
        slash_free d.(DeploymentV.ObjectMeta').(ObjectMetaV.Namespace') ∧
        slash_free d.(DeploymentV.ObjectMeta').(ObjectMetaV.Name') ∧
        slash_free d.(DeploymentV.ObjectMeta').(ObjectMetaV.UID') ⌝ ∗
      "%Hnodup" ∷ ⌜ NoDup (ReplicaSetV.key <$> rss) ⌝ ∗
      (* The caller's [rss] is exactly the ReplicaSet part of the children. *)
      "%Hdom_eq" ∷ ⌜ list_to_set (ReplicaSetV.key <$> rss) =
          filter (λ key, key.(KKey.Kind') = ReplicaSetV.kind) children_keys ⌝ ∗
      "Hown_children" ∷ own_children_frag γ (DeploymentV.key d)
        d.(DeploymentV.ObjectMeta').(ObjectMetaV.UID') children_dq children_keys ∗
      "Hown_meta_frags" ∷ ([∗ list] rs ∈ rss,
        own_meta_frag γ (ReplicaSetV.key rs)
          rs.(ReplicaSetV.ObjectMeta').(ObjectMetaV.UID') dq_rs
          rs.(ReplicaSetV.ObjectMeta')) ∗
      "Hown_spec_frags" ∷ ([∗ list] rs ∈ rss,
        own_spec_frag γ (ReplicaSetV.key rs)
          rs.(ReplicaSetV.ObjectMeta').(ObjectMetaV.UID') dq_rs
          (ObjectSpecV.ReplicaSetSpec rs.(ReplicaSetV.Spec')))
  }}}
    @! deployment.filterReplicaSetsByOwner #d_l
  {{{ sl ptrs (rss' : list ReplicaSetV.t) dq', RET (#sl, #interface.nil);
      "Hd" ∷ DeploymentV.deepown_l d_l d dq_d ∗
      "Hsl" ∷ sl ↦* ptrs ∗
      "Hrss'" ∷ ([∗ list] ptr;rs ∈ ptrs;rss',
        ReplicaSetV.deepown_l ptr rs dq') ∗
      (* [rss'] is the same set of objects as [rss], up to resource version.
         The view, not just the metadata: [deployment_realized] reads specs. *)
      "%Hview_perm" ∷ ⌜ rs_storage_view <$> rss' ≡ₚ rs_storage_view <$> rss ⌝ ∗
      "%Hrss'_valid" ∷ ⌜ Forall ReplicaSetV.valid rss' ⌝ ∗
      "%Hnodup'" ∷ ⌜ NoDup (ReplicaSetV.key <$> rss') ⌝ ∗
      (* Every returned ReplicaSet is controlled by this deployment — the
         filter's whole purpose. *)
      "%Hparent_refs" ∷ ⌜ Forall (λ rs,
          obj_parent_ref (KObjectV.ReplicaSet rs) =
            Some (DeploymentV.key d,
                  d.(DeploymentV.ObjectMeta').(ObjectMetaV.UID'))) rss' ⌝ ∗
      "Hown_children" ∷ own_children_frag γ (DeploymentV.key d)
        d.(DeploymentV.ObjectMeta').(ObjectMetaV.UID') children_dq children_keys ∗
      "Hown_meta_frags" ∷ ([∗ list] rs ∈ rss,
        own_meta_frag γ (ReplicaSetV.key rs)
          rs.(ReplicaSetV.ObjectMeta').(ObjectMetaV.UID') dq_rs
          rs.(ReplicaSetV.ObjectMeta')) ∗
      "Hown_spec_frags" ∷ ([∗ list] rs ∈ rss,
        own_spec_frag γ (ReplicaSetV.key rs)
          rs.(ReplicaSetV.ObjectMeta').(ObjectMetaV.UID') dq_rs
          (ObjectSpecV.ReplicaSetSpec rs.(ReplicaSetV.Spec')))
  }}}.
Proof.
  wp_start as "H". iNamed "H". wp_auto.
  iDestruct "Hd" as (d_c) "[Hdptr Hdeepown_d]".
  iNamedPrefix "Hdeepown_d" "Hdep_".
  iNamedPrefix "Hdep_Hdeepown_objectmeta" "Hdm_".
  wp_apply wp_slice_literal. iSplitR; first done.
  iIntros (result_sl) "[Hresult_sl Hown_result_cap]".
  set result0 := {|
    slice.ptr := result_sl;
    slice.len := W64 (go.array_literal_size []);
    slice.cap := W64 (go.array_literal_size []);
  |}.
  wp_auto.
  wp_alloc owner_reference as "Howner_reference". wp_auto.
  wp_apply (controller.wp_PodControllerIndexKey with "[$Howner_reference]").
  iIntros (index_key) "->". wp_auto.
  (* Every read off the deployment is done; put it back together so it can be
     handed straight back to the caller. The field equalities it supplied are
     pure and survive. *)
  iCombineNamed "Hdm_*" as "Hmeta".
  iAssert (ObjectMetaV.deepown d_c.(v1.Deployment.ObjectMeta')
      d.(DeploymentV.ObjectMeta') dq_d) with "[Hmeta]" as "Hdeepown_objectmeta".
  { iNamed "Hmeta". iFrame. done. }
  iAssert (DeploymentV.deepown_l d_l d dq_d)
    with "[Hdptr Hdeepown_objectmeta Hdep_Hdeepown_spec Hdep_Hdeepown_status]"
    as "Hd".
  { iExists d_c. iFrame. done. }
  (* Convert the uniform fragment lists into the [big_sepL2] shape the index
     lemma wants. *)
  set rs_dqs := replicate (length rss) dq_rs.
  iAssert (([∗ list] rs;rs_dq ∈ rss;rs_dqs,
    own_meta_frag γ (ReplicaSetV.key rs)
      rs.(ReplicaSetV.ObjectMeta').(ObjectMetaV.UID') rs_dq
      rs.(ReplicaSetV.ObjectMeta')))%I
    with "[Hown_meta_frags]" as "Hown_meta_frags2".
  { subst rs_dqs. rewrite big_sepL2_replicate_r; [done|].
    iExact "Hown_meta_frags". }
  iAssert (([∗ list] rs;rs_dq ∈ rss;rs_dqs,
    own_spec_frag γ (ReplicaSetV.key rs)
      rs.(ReplicaSetV.ObjectMeta').(ObjectMetaV.UID') rs_dq
      (ObjectSpecV.ReplicaSetSpec rs.(ReplicaSetV.Spec'))))%I
    with "[Hown_spec_frags]" as "Hown_spec_frags2".
  { subst rs_dqs. rewrite big_sepL2_replicate_r; [done|].
    iExact "Hown_spec_frags". }
  wp_apply (wp_State__ByIndex_replicaSetController
    γ model_l _ rss rs_dqs (DeploymentV.key d)
    d.(DeploymentV.ObjectMeta').(ObjectMetaV.UID') children_keys children_dq
    with "[$Hown_meta_frags2 $Hown_spec_frags2 $Hown_children]").
  { iFrame "#". iFrame "%". iPureIntro.
    rewrite /DeploymentV.key /DeploymentV.meta_key /=.
    rewrite Hdm_Hdeepown_namespace Hdm_Hdeepown_name Hdm_Hdeepown_uid. done. }
  iIntros (sl interfaces rss' dq') "H". iNamedPrefix "H" "Hindex_". wp_auto.
  iDestruct (own_slice_len with "Hindex_Hsl") as %(Hsl_len1 & Hsl_len2).
  iDestruct (own_slice_wf with "Hindex_Hsl") as %Hsl_cap.
  iDestruct (big_sepL2_length with "Hindex_Hrss") as %Hlen.
  set I := (∃ (i: w64) (result: slice.t) (ptrs: list loc) (v: interface.t),
    "Hi_ptr" ∷ i_ptr ↦ i ∗
    "Hresult_ptr" ∷ result_ptr ↦ result ∗
    "Hresult" ∷ result ↦* ptrs ∗
    "Hdeepown_l_rss" ∷ ([∗ list] ptr;rs ∈ ptrs;take (sint.nat i) rss',
      ReplicaSetV.deepown_l ptr rs dq') ∗
    "Hdeepown_i_rss" ∷ ([∗ list] i;rs ∈ drop (sint.nat i) interfaces;drop (sint.nat i) rss',
      KObjectV.deepown_i i (KObjectV.ReplicaSet rs) dq') ∗
    "Hobj" ∷ obj_ptr ↦ v ∗
    "Hown_result_cap" ∷ own_slice_cap loc result (DfracOwn 1) ∗
    "%Hi" ∷ ⌜ 0 ≤ sint.Z i ≤ sint.Z (slice.len sl) ⌝
  )%I.
  iAssert (I) with "[i result obj Hindex_Hrss Hresult_sl Hown_result_cap]" as "Hloop_inv".
  { iExists (W64 0), result0, [], (zero_val interface.t).
    rewrite /named !drop_0.
    iFrame "i result obj Hresult_sl Hown_result_cap". iFrame "#". iSplit.
    - rewrite take_0 big_sepL2_nil. done.
    - iSplitL "Hindex_Hrss".
      + iExactEq "Hindex_Hrss". reflexivity.
      + iPureIntro. word.
  }
  wp_for "Hloop_inv".
  wp_if_destruct.
  - assert (∃ this_interface, interfaces !! sint.nat i = Some this_interface) as
      [this_interface Hthis_interface_lookup].
    { apply lookup_lt_is_Some_2.
      rewrite <- (map_length interface.ok interfaces).
      rewrite Hsl_len1. word. }
    destruct (decide (0 ≤ sint.Z i < sint.Z (slice.len sl))) as [_|Hbounds]; last word.
    wp_apply (wp_load_slice_index with "[$Hindex_Hsl]"); [word| |].
    { iPureIntro. rewrite list_lookup_fmap Hthis_interface_lookup. done. }
    iIntros "Hindex_Hsl". wp_auto.
    assert (∃ this_rs, rss' !! sint.nat i = Some this_rs) as [this_rs Hthis_rs_lookup].
    { apply lookup_lt_is_Some_2.
      pose proof (lookup_lt_Some _ _ _ Hthis_interface_lookup) as Hlt.
      rewrite -Hlen. done. }
    iPoseProof (big_sepL2_head_tail _ _ _ this_interface this_rs with "Hdeepown_i_rss")
      as "[Hthis_i_rs Hother_i_rs]".
    { split. all: rewrite lookup_drop Nat.add_0_r; done. }
    iDestruct "Hthis_i_rs" as (this_ptr) "[%Hthis_i Hdeepown_l]".
    unfold KObjectV.valid_interface in Hthis_i. rewrite Hthis_i.
    rewrite decide_True; [change (go.PointerType deployment.apps_v1.ReplicaSet) with (go.PointerType v1.ReplicaSet); reflexivity|].
    wp_auto.
    rewrite bool_decide_true; [change (go.PointerType deployment.apps_v1.ReplicaSet) with (go.PointerType v1.ReplicaSet); reflexivity|].
    wp_auto.
    wp_apply wp_slice_literal. iSplitR; first done. iIntros (sl0) "[Hsl0 _]". wp_auto.
    wp_apply (wp_slice_append with "[$Hresult $Hown_result_cap $Hsl0]").
    iIntros (result') "(Hresult & Hown_result_cap & Hsl0)". wp_auto.
    iApply wp_for_post_do. wp_auto.
    iAssert (I) with "[Hi_ptr Hresult Hresult_ptr Hobj Hown_result_cap Hother_i_rs Hdeepown_l Hdeepown_l_rss]" as
      "Hloop_inv".
    { iExists (word.add i (W64 1)), result', (ptrs ++ [this_ptr]). iFrame. iSplitR "Hother_i_rs". 2: iSplitL.
      - assert (sint.nat (word.add i (W64 1)) = S (sint.nat i)) as -> by word.
        rewrite (take_S_r _ _ this_rs Hthis_rs_lookup).
        iApply (big_sepL2_app with "[$Hdeepown_l_rss]"). iFrame. done.
      - assert (sint.nat (word.add i (W64 1)) = S (sint.nat i)) as -> by word.
        rewrite !drop_drop. replace (S (sint.nat i)) with (sint.nat i + 1)%nat by lia. iFrame.
      - iPureIntro. word.
    }
    iFrame.
  - iApply "HΦ".
    assert (take (sint.nat i) rss' = rss') as ->.
    { assert (sint.nat i = length interfaces) as ->.
      { rewrite <- (map_length interface.ok interfaces). rewrite Hsl_len1. word. }
      rewrite Hlen. apply take_ge. lia. }
    subst rs_dqs.
    iEval (rewrite big_sepL2_replicate_r; [done|]) in "Hindex_Hown_meta_frags".
    iEval (rewrite big_sepL2_replicate_r; [done|]) in "Hindex_Hown_spec_frags".
    iFrame "Hd Hresult Hdeepown_l_rss Hindex_Hown_meta_frags
      Hindex_Hown_spec_frags Hindex_Hown_children_frag".
    iFrame "%".
Qed.

(* Transferring the Gallina predicates across what the index returned.

   [deployment_realized] and [unique_new_replica_set] read only replica counts
   and templates, both of which live in the spec — so both are determined by
   [rs_storage_view], and both survive a permutation of views. This is the
   step that would fail if the index only related metadata. *)
Lemma deployment_realized_view_perm d rss rss' :
  rs_storage_view <$> rss' ≡ₚ rs_storage_view <$> rss →
  deployment_realized d rss →
  deployment_realized d rss'.
Proof.
  intros Hperm (new_rs & Hin & Hmatches & Hcount & Hothers).
  (* The witness has a counterpart in [rss'] with the same view. *)
  destruct (rs_storage_view_perm_elem_of rss rss' new_rs
    (Permutation_sym Hperm) Hin) as (new_rs' & Hin' & Hview_eq).
  destruct (rs_storage_view_eq_inv _ _ Hview_eq) as [Hkey_eq Hspec_eq].
  exists new_rs'. split_and!.
  - exact Hin'.
  - rewrite /rs_template Hspec_eq. exact Hmatches.
  - rewrite Hspec_eq. exact Hcount.
  - apply Forall_lookup. intros k rs' Hk.
    destruct (rs_storage_view_perm_elem_of rss' rss rs' Hperm
      (list_elem_of_lookup_2 _ _ _ Hk)) as (rs & Hrs_in & Hrs_view).
    destruct (rs_storage_view_eq_inv _ _ Hrs_view) as [Hrs_key Hrs_spec].
    apply list_elem_of_lookup_1 in Hrs_in as (kk & Hkk).
    rewrite Forall_lookup in Hothers.
    destruct (Hothers _ _ Hkk) as [Hleft|Hright].
    + left. rewrite -Hrs_key Hleft -Hkey_eq. done.
    + right. rewrite -Hrs_spec. exact Hright.
Qed.

Lemma unique_new_replica_set_view_perm d rss rss' :
  rs_storage_view <$> rss' ≡ₚ rs_storage_view <$> rss →
  NoDup (ReplicaSetV.key <$> rss') →
  unique_new_replica_set d rss →
  unique_new_replica_set d rss'.
Proof.
  intros Hperm Hnodup' Huniq i j rs_i rs_j Hi Hj Hmi Hmj.
  (* Pull both back to [rss], where uniqueness holds. *)
  destruct (rs_storage_view_perm_elem_of rss' rss rs_i Hperm
    (list_elem_of_lookup_2 _ _ _ Hi)) as (rs_i' & Hi'_in & Hi'_view).
  destruct (rs_storage_view_perm_elem_of rss' rss rs_j Hperm
    (list_elem_of_lookup_2 _ _ _ Hj)) as (rs_j' & Hj'_in & Hj'_view).
  destruct (rs_storage_view_eq_inv _ _ Hi'_view) as [Hi_key Hi_spec].
  destruct (rs_storage_view_eq_inv _ _ Hj'_view) as [Hj_key Hj_spec].
  apply list_elem_of_lookup_1 in Hi'_in as (ki & Hki).
  apply list_elem_of_lookup_1 in Hj'_in as (kj & Hkj).
  assert (ki = kj) as Hkk.
  { eapply Huniq; [exact Hki|exact Hkj| |].
    - rewrite /rs_template Hi_spec. exact Hmi.
    - rewrite /rs_template Hj_spec. exact Hmj. }
  subst kj. rewrite Hki in Hkj. injection Hkj as ->.
  (* Same element of [rss] on both sides, so [rs_i] and [rs_j] share a key;
     [NoDup] on the returned keys then forces the indices to coincide. *)
  assert (ReplicaSetV.key rs_i = ReplicaSetV.key rs_j) as Hkey.
  { rewrite -Hi_key -Hj_key. done. }
  eapply NoDup_lookup; [exact Hnodup'| |].
  - rewrite list_lookup_fmap Hi /=. reflexivity.
  - rewrite list_lookup_fmap Hj /= Hkey. reflexivity.
Qed.

(* The Deployment value read back from the store differs from the framed one
   in its resource version. Both predicates read only the spec, so neither
   notices. *)
Lemma deployment_realized_spec_eq d1 d2 rss :
  d1.(DeploymentV.Spec') = d2.(DeploymentV.Spec') →
  deployment_realized d1 rss → deployment_realized d2 rss.
Proof.
  intros Hspec.
  rewrite /deployment_realized /deployment_template /deployment_replicas Hspec.
  done.
Qed.

Lemma unique_new_replica_set_spec_eq d1 d2 rss :
  d1.(DeploymentV.Spec') = d2.(DeploymentV.Spec') →
  unique_new_replica_set d1 rss → unique_new_replica_set d2 rss.
Proof.
  intros Hspec.
  rewrite /unique_new_replica_set /deployment_template Hspec.
  done.
Qed.

(* syncDeployment is the controller's entry point: read the deployment, gather
   its ReplicaSets, and — unless the deployment is being deleted — roll out.

   The postcondition is [deployment_realized] rather than a progress measure:
   this controller has no surge pacing, so one sync reaches the desired state.
   [rss_post] is existential because the new ReplicaSet may have been created
   during the sync, in which case it is not among the [rss] the caller framed. *)
Lemma wp_syncDeployment γ model_l (namespace name : go_string)
    (d : DeploymentV.t) (rss : list ReplicaSetV.t)
    (children_keys : gset KKey.t) uid kmeta dq_d children_dq :
  ⊢ progress_spec γ model_l namespace name d rss children_keys uid kmeta
      dq_d children_dq.
Proof.
Admitted.

End proof.
