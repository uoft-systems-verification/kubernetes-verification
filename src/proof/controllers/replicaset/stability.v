From New.proof Require Import wp_keep.

From New.proof Require Import prelude empty_ffi.
From New.proof.kubernetes_model Require Export get by_index_pod_controller create delete.
From New.proof Require Export util.
From New.proof Require Export wp_helpers.
From New.proof.controllers Require Export common.
From New.proof.controllers.replicaset Require Export top_level.
From New.proof.controllers.replicaset Require Export common claim_pods.
From New.proof.controllers.replicaset Require Import update_replicaset_status.
From New.proof.k8s_io.kubernetes.pkg Require Export controller.
From New.proof.k8s_io.apimachinery.pkg.runtime Require Export schema.
From New.proof.k8s_io.apimachinery.pkg.api Require Export errors.

Local Transparent ObjectMetaV.deepown ObjectMetaView.ObjectMetaV.deepown.

Module client_apps_v1 := code.k8s_io.client_go.kubernetes.typed.apps.v1.v1.
Module client_core_v1 := code.k8s_io.client_go.kubernetes.typed.core.v1.v1.
Module client_gentype := code.k8s_io.client_go.gentype.gentype.
Module generic_listers := code.k8s_io.client_go.listers.listers.
Module trusted_client_apps_v1 := trusted_code.k8s_io.client_go.kubernetes.typed.apps.v1.v1.
Module trusted_client_gentype := trusted_code.k8s_io.client_go.gentype.gentype.
Module trusted_app_listers := trusted_code.k8s_io.client_go.listers.apps.v1.v1.
Module trusted_generic_listers := trusted_code.k8s_io.client_go.listers.listers.
Transparent client_gentype.Client.

(* Collect transient allocations from imports before checking large program proofs. *)
Optimize Heap.

Section proof.
Context `{hG: !heapGS Σ} `{!ffi_semantics _ _}.
Context {sem : go.Semantics}
  {package_sem : code.controllers.replicaset.replicaset.Assumptions}.
Collection W := sem + package_sem.
#[local] Instance base_common_sem : common.Assumptions | 100 :=
  code.controllers.replicaset.replicaset.import_common_Assumption.
#[local] Instance controller_sem : controller.Assumptions :=
  code.controllers.replicaset.replicaset.import_controller_Assumption.
#[local] Instance clientset_sem : kubernetes.Assumptions :=
  code.controllers.replicaset.replicaset.import_kubernetes_Assumption.
#[local] Instance client_core_v1_sem : client_core_v1.Assumptions :=
  kubernetes.import_core_v1_Assumption.
#[local] Instance client_apps_v1_sem : client_apps_v1.Assumptions :=
  kubernetes.import_apps_v1_Assumption.
#[local] Instance client_gentype_sem : client_gentype.Assumptions :=
  client_core_v1.import_gentype_Assumption.
#[local] Instance app_listers_sem : app_listers.Assumptions :=
  code.controllers.replicaset.replicaset.import_listers_apps_v1_Assumption.
#[local] Instance generic_listers_sem : generic_listers.Assumptions :=
  app_listers.import_listers_Assumption.
#[local] Instance runtime_sem : code.k8s_io.apimachinery.pkg.runtime.runtime.Assumptions :=
  controller.import_runtime_Assumption.
#[local] Instance runtime_object_underlying_eq :
  runtime.Object ≤u runtime.Objectⁱᵐᵖˡ.
Proof using package_sem. apply _. Qed.
#[local] Instance meta_object_underlying_eq :
  meta_v1.Object ≤u meta_v1.Objectⁱᵐᵖˡ.
Proof using package_sem. apply _. Qed.
#[local] Instance base_apimodel_sem : apimodel.Assumptions | 100 :=
  common.import_apimodel_Assumption.
#[local] Instance object_meta_v1_sem :
    code.k8s_io.apimachinery.pkg.apis.meta.v1.v1.Assumptions :=
  apimodel.import_apis_meta_v1_Assumption.
#[local] Instance object_apps_v1_sem :
    code.k8s_io.api.apps.v1.v1.Assumptions :=
  apimodel.import_api_apps_v1_Assumption.
#[local] Instance object_core_v1_sem :
    code.k8s_io.api.core.v1.v1.Assumptions :=
  code.k8s_io.api.apps.v1.v1.import_core_v1_Assumption.
#[local] Instance apimodel_sem : apimodel.Assumptions | 0.
Proof using package_sem.
  constructor; try exact object_core_v1_sem; try apply _.
Defined.
#[local] Instance common_sem : common.Assumptions | 0.
Proof using package_sem.
  constructor; try exact apimodel_sem; try apply _.
Defined.
Context `{!kubernetesModelG Σ}.
Local Set Default Proof Using "All".

Context `{!KObjectV.ObjectInterfaceAssumptions}.

Lemma wp_manageReplicas_stability (ctx : context.Context.t) (kube_client : loc) (burst : w64)
    sl rs_l ptrs active_pods rs n dq1 dq2 :
  {{{ "#Hpkg" ∷ is_pkg_init code.controllers.replicaset.pkg_id.replicaset ∗
      "Hsl" ∷ sl ↦* ptrs ∗
      "Hdeepown_l_active_pods" ∷ ([∗ list] ptr;pod ∈ ptrs;active_pods, PodV.deepown_l ptr pod dq1) ∗
      "Hdeepown_l_rs" ∷ ReplicaSetV.deepown_l rs_l rs dq2 ∗
      "%Hreplicas_eq" ∷ ⌜ rs.(ReplicaSetV.Spec').(ReplicaSetSpecV.Replicas') = Some n ⌝ ∗
      "%Hn_nonneg" ∷ ⌜ 0 ≤ sint.Z n ⌝ ∗
      "%Hlen_active" ∷ ⌜ length active_pods = sint.nat n ⌝
  }}}
    @! replicaset.manageReplicas #ctx #kube_client #burst #sl #rs_l
  {{{ RET #interface.nil;
      sl ↦* ptrs ∗
      ([∗ list] ptr;pod ∈ ptrs;active_pods, PodV.deepown_l ptr pod dq1) ∗
      ReplicaSetV.deepown_l rs_l rs dq2
  }}}.
Proof.
  wp_start as "H". iNamed "H".
  wp_auto_keep.
  iPoseProof (ReplicaSetV.deepown_l_split with "Hdeepown_l_rs") as
    "(%Hrs_l_not_null & Hdeepown_t_l_rs & Hdeepown_m_l_rs & Hdeepown_s_l_rs & Hdeepown_st_l_rs)".
  iDestruct "Hdeepown_s_l_rs" as "(%rs_spec_c & Hrs_spec_l & Hdeepown_rs_spec)".
  iNamedPrefix "Hdeepown_rs_spec" "Hrs_".
  iAssert ((rs_spec_c.(v1.ReplicaSetSpec.Replicas') ↦{dq2} n)%I) with "[Hrs_Hdeepown_replicas_some]"
    as "Hrs_Hdeepown_replicas".
  { rewrite Hreplicas_eq. iDestruct "Hrs_Hdeepown_replicas_some" as "(%replicas & Hreplicas & ->)".
    done. }
  wp_auto_keep.
  iDestruct (own_slice_len with "Hsl") as %(Hsl_len1 & Hsl_len2).
  iDestruct (own_slice_wf with "Hsl") as %Hsl_cap.
  iDestruct (big_sepL2_length with "Hdeepown_l_active_pods") as %Hlen.
  wp_if_destruct.
  - exfalso. rewrite -Hlen Hsl_len1 in Hlen_active. word.
  - wp_if_destruct.
    + exfalso. rewrite -Hlen Hsl_len1 in Hlen_active. word.
    + iApply "HΦ". iFrame.
      iApply (ReplicaSetV.deepown_l_restore _ _ _ Hrs_l_not_null). iFrame.
      iSplitR. 1: done. iSplitL. 2: done.
      rewrite Hreplicas_eq. iExists n. iSplitL; done.
Qed.

Lemma wp_syncReplicaSet_stability γ l (ctx : context.Context.t) (kube_client : loc) (burst : w64)
    (rsc_clock : interface.t) (controller_features : upstreamrs.ReplicaSetControllerFeatures.t) namespace name rs dq
    pods orphan_pods :
  ⊢ stability_spec γ l ctx kube_client burst rsc_clock controller_features namespace name rs dq pods orphan_pods.
Proof.
  unfold stability_spec.
  wp_start as "H". iNamed "H". iNamed "Hresources".
  iEval (simpl) in "Hown_rs_meta_frag Hown_rs_spec_frag Hown_rs_status_frag Hown_pod_meta_frags
    Hown_pod_spec_frags Hown_children_frag Hown_terminating_children_frag Hown_orphan_pod_frags
    Hown_pod_orphans".
  unfold input_requirement in Hinput_requirement.
  destruct Hinput_requirement as (_ & _ & Hlabels_bound & Hgeneration_nonneg).
  iAssert (is_pkg_init common) as "#Hcommon_init".
  { iPkgInit. }
  iAssert (is_pkg_init apimodel) as "#Hapimodel".
  { iPkgInit. }
  wp_auto_keep.
  wp_bind (null @! (go.PointerType app_listers.replicaSetLister) @! "ReplicaSets" #namespace)%E.
  wp_method_call. rewrite /trusted_app_listers.replicaSetLister__ReplicaSetsⁱᵐᵖˡ. wp_call.
  wp_method_call. rewrite /trusted_generic_listers.ResourceIndexer__Getⁱᵐᵖˡ decide_True; [reflexivity|].
  rewrite /trusted_generic_listers.resourceIndexerGet. wp_pures_keep.
  wp_auto_keep.
  wp_apply (wp_State__ReplicaSetGet with "[$Hown_rs_meta_frag $Hown_rs_spec_frag $Hown_rs_status_frag]").
  { iFrame "#".
    iPureIntro.
    rewrite /ReplicaSetV.key /ReplicaSetV.meta_key Hnamespace_eq Hname_eq.
    done. }
  iIntros (rs_l rs_get) "Hget". iNamedPrefix "Hget" "Hget_".
  iRename "Hget_Hdeepown_l" into "Hdeepown_l_rs".
  iRename "Hget_Hown_meta_frag" into "Hown_rs_meta_frag".
  iRename "Hget_Hown_spec_frag" into "Hown_rs_spec_frag".
  iRename "Hget_Hown_status_frag" into "Hown_rs_status_frag".
  pose proof Hget_Hvalid' as Hrs_get_valid.
  assert (ReplicaSetSpecV.valid rs_get.(ReplicaSetV.Spec')) as Hrs_get_spec_valid.
  { destruct Hget_Hvalid' as (_ & _ & _ & Hrs_get_spec_valid & _).
    exact Hrs_get_spec_valid. }
  assert (ReplicaSetSpecV.valid rs.(ReplicaSetV.Spec')) as Hrs_spec_valid.
  { rewrite Hget_Hspec_eq. exact Hrs_get_spec_valid. }
  wp_auto_keep.
  rewrite decide_True; [reflexivity|].
  wp_auto_keep.
  wp_apply (wp_IsNotFound interface.nil with "[]").
  replace (bool_decide (not_found_error interface.nil)) with false by
    (symmetry; apply bool_decide_false; exact not_found_error_nil).
  wp_auto_keep.
  iPoseProof (ReplicaSetV.deepown_l_split with "Hdeepown_l_rs") as
    "(%Hrs_l_not_null & Hdeepown_t_l_rs & Hdeepown_m_l_rs & Hdeepown_s_l_rs & Hdeepown_st_l_rs)".
  iPoseProof (kview.own_meta_valid with "Hown_rs_meta_frag") as "%Hrs_meta_frag_valid".
  destruct Hrs_meta_frag_valid as (_ & _ & _ & Hrs_meta_valid & Hdeletion_timestamp_eq).
  (* selector, err := metav1.LabelSelectorAsSelector(rs.Spec.Selector): a valid
     ReplicaSet has a valid selector, so the conversion succeeds. *)
  pose proof Hrs_get_spec_valid as Hrs_get_selector.
  destruct Hrs_get_selector as [(_ & _ & (sel & Hsel_eq & Hsel_valid & _ & Hsel_template) & _) _].
  iDestruct "Hdeepown_s_l_rs" as (rs_spec_c) "[Hrs_spec_l Hrs_spec]".
  iNamedPrefix "Hrs_spec" "Hrs_spec_".
  iEval (rewrite Hsel_eq) in "Hrs_spec_Hdeepown_selector_some".
  wp_auto_keep.
  wp_apply_keep (wp_LabelSelectorAsSelector with "[$Hrs_spec_Hdeepown_selector_some]").
  { iSplit; iPureIntro; [exact Hsel_valid|]. apply Hget_Hextra_valid. exact Hsel_eq. }
  iIntros (selector) "(Hrs_spec_Hdeepown_selector_some & #Hselector)".
  iAssert (ReplicaSetSpecV.deepown rs_spec_c rs_get.(ReplicaSetV.Spec') 1)
    with "[Hrs_spec_Hdeepown_replicas_some Hrs_spec_Hdeepown_selector_some Hrs_spec_Hdeepown_template]"
    as "Hrs_spec".
  { rewrite /ReplicaSetSpecV.deepown /named Hsel_eq.
    iFrame. iFrame "%". iPureIntro.
    rewrite Hsel_eq in Hrs_spec_Hdeepown_selector_none.
    exact Hrs_spec_Hdeepown_selector_none. }
  iAssert (ReplicaSetSpecV.deepown_l (ReplicaSetV.spec_ptr rs_l) rs_get.(ReplicaSetV.Spec') 1)
    with "[Hrs_spec_l Hrs_spec]" as "Hdeepown_s_l_rs".
  { iExists rs_spec_c. iFrame. }
  wp_auto_keep.
  assert (ObjectMetaV.valid ReplicaSetV.kind rs_get.(ReplicaSetV.ObjectMeta')) as Hrs_get_meta_valid.
  { destruct Hget_Hvalid' as (_ & _ & Hvalid_meta & _). exact Hvalid_meta. }
  pose proof Hget_Hmeta_eq as Hget_Hmeta_fields.
  rewrite /ObjectMetaV.equiv_except_resource_version
    /ObjectMetaV.without_resource_version in Hget_Hmeta_fields.
  pose proof (f_equal ObjectMetaV.UID' Hget_Hmeta_fields) as Hget_Huid_eq.
  pose proof (f_equal ObjectMetaV.DeletionTimestamp' Hget_Hmeta_fields)
    as Hget_Hdeletion_timestamp_eq.
  simpl in Hget_Huid_eq, Hget_Hdeletion_timestamp_eq.
  destruct Hget_Hvalid' as [Hrs_valid_typemeta _].
  destruct Hrs_valid_typemeta as (_ & Hrs_kind_valid & _).
  pose proof (valid_kind_slash_free _ Hrs_kind_valid) as Hrs_kind_slash_free.
  assert (valid_namespace rs_get.(ReplicaSetV.ObjectMeta').(ObjectMetaV.Namespace'))
    as Hrs_namespace_valid by (unfold ObjectMetaV.valid in Hrs_get_meta_valid; tauto).
  assert (valid_name ReplicaSetV.kind rs_get.(ReplicaSetV.ObjectMeta').(ObjectMetaV.Name'))
    as Hrs_name_valid by (unfold ObjectMetaV.valid in Hrs_get_meta_valid; tauto).
  assert (valid_uid rs_get.(ReplicaSetV.ObjectMeta').(ObjectMetaV.UID'))
    as Hrs_uid_valid by (unfold ObjectMetaV.valid in Hrs_get_meta_valid; tauto).
  pose proof (valid_namespace_slash_free _ Hrs_namespace_valid) as Hrs_namespace_slash_free.
  pose proof (valid_name_slash_free _ Hrs_name_valid) as Hrs_name_slash_free.
  pose proof (valid_uid_slash_free _ Hrs_uid_valid) as Hrs_uid_slash_free.
  assert (list_to_set (C:=gset KKey.t) (PodV.key <$> pods) =
      filter (λ key, key.(KKey.Kind') = "Pod"%go)
        (list_to_set (C:=gset KKey.t) (PodV.key <$> pods))) as Hdom_eq.
  { apply set_eq. intros key.
    rewrite elem_of_filter.
    split.
    - intros Hkey_in. split; [|done].
      apply elem_of_list_to_set in Hkey_in.
      apply list_elem_of_fmap_1 in Hkey_in as (pod & Hkey_eq & _).
      subst key.
      rewrite /PodV.key /PodV.meta_key /PodV.kind //.
    - intros [_ Hkey_in]. done. }
  assert (ReplicaSetV.key rs = ReplicaSetV.key rs_get) as Hrs_key_eq.
  { exact Hget_Hkey_eq. }
  assert (rs.(ReplicaSetV.ObjectMeta').(ObjectMetaV.UID') =
      rs_get.(ReplicaSetV.ObjectMeta').(ObjectMetaV.UID')) as Hrs_uid_eq.
  { symmetry. exact Hget_Huid_eq. }
  iEval (rewrite Hrs_key_eq Hrs_uid_eq) in "Hown_children_frag".
  iEval (rewrite Hrs_key_eq Hrs_uid_eq) in "Hown_terminating_children_frag".
  assert (rs.(ReplicaSetV.ObjectMeta').(ObjectMetaV.Namespace') =
      rs_get.(ReplicaSetV.ObjectMeta').(ObjectMetaV.Namespace')) as Hrs_ns_eq.
  { pose proof (f_equal KKey.Namespace' Hrs_key_eq) as Hns.
    rewrite /ReplicaSetV.key /ReplicaSetV.meta_key /= in Hns. exact Hns. }
  iEval (rewrite Hrs_ns_eq) in "Hown_pod_orphans".
  (* allRSPods: the ReplicaSet's pods [all_pods], then the orphans of its
     namespace [orphan_list]. *)
  wp_apply (common.wp_FilterPodsByOwner_orphans with
    "[$Hdeepown_m_l_rs $Hown_pod_meta_frags $Hown_pod_spec_frags $Hown_children_frag
      $Hown_terminating_children_frag $Hown_orphan_pod_frags $Hown_pod_orphans]").
  { iFrame "#".
    iPureIntro. split_and!; done. }
  iIntros (all_sl all_ptrs all_pods orphan_list dq') "(Hall_sl & Hall_deepown_pods & %Hall_alive_meta_perm &
    %Hall_alive_view_perm & %Hall_len_bound & %Hall_controlled & %Horphans_perm & %Horphan_list & %Hall_valid & %Hall_orphans_nodup &
    Hdeepown_m_l_rs & _ & Hall_alive_meta_frags & Hall_alive_spec_frags & Hown_children_frag &
    Hown_terminating_children_frag &
    Hown_orphan_pod_frags & Hown_pod_orphans)".
  (* With no terminating children, every listed pod of the ReplicaSet is alive. *)
  assert (∀ pod, pod ∈ all_pods → is_pod_alive pod) as Hall_alive.
  { apply (filter_length_eq_all is_pod_alive).
    pose proof (Permutation_length Hall_alive_meta_perm) as Hlen. rewrite !length_fmap in Hlen.
    pose proof (length_filter is_pod_alive all_pods). lia. }
  rewrite (filter_all is_pod_alive all_pods Hall_alive) in Hall_alive_meta_perm.
  rename Hall_alive_meta_perm into Hall_meta_perm.
  rewrite (filter_all is_pod_alive all_pods Hall_alive) in Hall_alive_view_perm.
  rename Hall_alive_view_perm into Hall_view_perm.
  iEval (rewrite (filter_all is_pod_alive all_pods Hall_alive)) in "Hall_alive_meta_frags Hall_alive_spec_frags".
  iRename "Hall_alive_meta_frags" into "Hall_meta_frags".
  iRename "Hall_alive_spec_frags" into "Hall_spec_frags".
  wp_auto_keep.
  (* The pods are only read: share them between the filters, the claim and
     the status calculation. *)
  iMod (big_sepL2_persist PodV.deepown_l with "Hall_deepown_pods") as "#Hall_deepown_pods".
  { intros. apply PodV.deepown_l_persist. }
  wp_apply (common.wp_FilterActivePods with "[$Hall_sl $Hall_deepown_pods]").
  iIntros (active_sl active_ptrs) "(Hactive_sl & #Hactive_deepown_pods & Hall_sl)".
  iEval (rewrite list.filter_app (filter_all is_pod_alive all_pods Hall_alive)) in "Hactive_deepown_pods".
  wp_auto_keep.
  (* The claim only reads the ReplicaSet. *)
  iPoseProof (ReplicaSetV.deepown_l_restore _ _ _ Hrs_l_not_null with
    "[$Hdeepown_t_l_rs $Hdeepown_m_l_rs $Hdeepown_s_l_rs $Hdeepown_st_l_rs]") as "Hdeepown_l_rs".
  iMod (ReplicaSetV.deepown_l_persist with "Hdeepown_l_rs") as "#Hdeepown_l_rs".
  assert (∀ pod, rs_selects rs pod ↔ rs_selects rs_get pod) as Hselects.
  { intros pod. rewrite /rs_selects /rs_selects_meta Hget_Hspec_eq. done. }
  (* No listed orphan is selected: the living ones are [orphan_pods]. *)
  assert (Forall (λ pod, ¬ rs_selects rs_get pod) (filter is_pod_alive orphan_list)) as Horphans_unselected.
  { apply (Forall_storage_view_perm (λ m, ¬ rs_selects_meta rs_get m) (filter is_pod_alive orphan_list) orphan_pods).
    - intros m. rewrite /rs_selects_meta /ObjectMetaV.without_resource_version /=. done.
    - exact Horphans_perm.
    - eapply Forall_impl; [|exact Hno_selected_orphans].
      intros pod Hnot Hselected. apply Hnot. apply Hselects. exact Hselected. }
  (* activePods, err := claimPods(ctx, kubeClient, rs, selector, allActivePods) *)
  wp_apply (wp_claimPods_no_adoption ctx kube_client rs_l rs_get sel selector active_sl active_ptrs
    all_pods (filter is_pod_alive orphan_list) with "[$Hactive_sl]").
  { iFrame "#". iPureIntro. split_and!.
    - exact Hsel_eq.
    - exact Hall_controlled.
    - apply (Forall_rs_selects_erased_meta_perm rs_get all_pods pods Hall_meta_perm).
      eapply Forall_impl; [|exact Hpods_selected]. intros pod. apply Hselects.
    - apply list.Forall_forall. intros pod Hpod.
      split; [|rewrite list.Forall_forall in Horphans_unselected; by apply Horphans_unselected].
      apply list_elem_of_filter in Hpod as [_ Hpod].
      rewrite list.Forall_forall in Horphan_list.
      by destruct (Horphan_list pod Hpod). }
  iIntros (claimed_sl claimed_ptrs) "(Hclaimed_sl & #Hclaimed_deepown_pods & Hactive_sl)".
  wp_auto_keep.
  (* Terminating pods are collected only when the feature is enabled; either way
     only the length of the result matters. FilterClaimedPods keeps pods whose
     controller has the ReplicaSet's UID, so the listed orphans never count. *)
  iAssert (is_pkg_init controller) as "#Hcontroller_init".
  { iPkgInit. }
  wp_bind (if: _ then _ else do: #())%E.
  iApply (wp_wand _ _ _ (λ v, ⌜ v = execute_val ⌝ ∗
      ∃ (term_sl : slice.t) (term_ptrs : list loc),
        "terminatingPods" ∷ terminatingPods_ptr ↦ term_sl ∗
        "Hterm_sl" ∷ term_sl ↦* term_ptrs ∗
        "%Hterm_len" ∷ ⌜ length term_ptrs ≤ length all_pods ⌝ ∗
        "Hall_sl" ∷ all_sl ↦* all_ptrs ∗
        "allRSPods" ∷ allRSPods_ptr ↦ all_sl ∗
        "rs" ∷ rs_ptr ↦ rs_l ∗
        "selector" ∷ selector_ptr ↦ selector ∗
        "controllerFeatures" ∷ controllerFeatures_ptr ↦ controller_features)%I
    with "[terminatingPods Hall_sl allRSPods rs selector controllerFeatures]").
  { wp_bind (MethodResolve featuregate.FeatureGate "Enabled"%go
      (![featuregate.FeatureGate] #(global_addr utilfeature.DefaultFeatureGate)) _)%E.
    iApply wp_DefaultFeatureGate_Enabled; first iPkgInit.
    iNext. iIntros (gate) "_".
    destruct gate; wp_auto_keep;
      [destruct (upstreamrs.ReplicaSetControllerFeatures.EnableStatusTerminatingReplicas'
        controller_features); wp_auto_keep|].
    - wp_apply (wp_FilterTerminatingPods_kept with "[$Hall_sl $Hall_deepown_pods]").
      iIntros (kept_sl kept_ptrs kept_pods) "(Hkept_sl & #Hkept_deepown_pods & %Hkept_sub & Hall_sl)".
      wp_auto_keep.
      wp_apply (wp_FilterClaimedPods_rs rs_l rs_get selector (LabelSelectorV.matches sel) with
        "[$Hkept_sl $Hdeepown_l_rs $Hselector $Hkept_deepown_pods]").
      iIntros (term_sl term_ptrs term_pods)
        "(Hterm_sl & %Hterm_len_eq & %Hterm_sub & %Hterm_controlled & Hkept_sl)".
      wp_auto_keep.
      iSplit; first done. iExists term_sl, term_ptrs. iFrame. iPureIntro.
      assert (∀ pod, pod ∈ term_pods → is_Some (meta_parent_ref pod.(PodV.ObjectMeta'))) as Hterm_parent.
      { intros pod Hpod. rewrite list.Forall_forall in Hterm_controlled.
        destruct (Hterm_controlled pod Hpod) as [parent_key Hparent]. rewrite Hparent. by eexists. }
      assert (filter (λ pod : PodV.t, is_Some (meta_parent_ref pod.(PodV.ObjectMeta'))) orphan_list = [])
        as Horphans_unclaimed.
      { apply filter_none. intros pod Hpod Hparent.
        rewrite list.Forall_forall in Horphan_list.
        destruct (Horphan_list pod Hpod) as [Hnone _].
        rewrite Hnone in Hparent. by destruct Hparent. }
      assert (filter (λ pod : PodV.t, is_Some (meta_parent_ref pod.(PodV.ObjectMeta'))) term_pods `sublist_of`
          filter (λ pod : PodV.t, is_Some (meta_parent_ref pod.(PodV.ObjectMeta'))) (all_pods ++ orphan_list))
        as Hsub.
      { apply sublist_filter_mono. etrans; [exact Hterm_sub|exact Hkept_sub]. }
      apply sublist_length in Hsub.
      rewrite (filter_all _ term_pods Hterm_parent) list.filter_app Horphans_unclaimed app_nil_r in Hsub.
      pose proof (length_filter (λ pod : PodV.t, is_Some (meta_parent_ref pod.(PodV.ObjectMeta'))) all_pods).
      lia.
    - iSplit; first done. iExists slice.nil, []. iFrame.
      iSplitR; first iApply own_slice_nil. iPureIntro. simpl. lia.
    - iSplit; first done. iExists slice.nil, []. iFrame.
      iSplitR; first iApply own_slice_nil. iPureIntro. simpl. lia. }
  iIntros (v) "(-> & H)". iNamed "H".
  wp_auto_keep.
  (* if rs.DeletionTimestamp == nil: holding its meta fragment, the ReplicaSet
     is not being deleted. *)
  iPoseProof (ReplicaSetV.deepown_l_split with "Hdeepown_l_rs") as "(_ & _ & Hdeepown_m_l_rs & _ & _)".
  iDestruct "Hdeepown_m_l_rs" as (rs_meta_c) "[Hrs_meta_l Hdeepown_m_rs]".
  iNamedPrefix "Hdeepown_m_rs" "Hrs_meta_".
  assert (rs_meta_c.(v1.ObjectMeta.DeletionTimestamp') = null) as Hrs_deletion_timestamp_null.
  { apply Hrs_meta_Hdeepown_deletiontimestamp_none.
    rewrite Hget_Hdeletion_timestamp_eq.
    exact Hdeletion_timestamp_eq. }
  wp_auto_keep.
  rewrite Hrs_deletion_timestamp_null.
  wp_auto_keep.
  pose proof (ReplicaSetSpecV.valid_replicas _ Hrs_spec_valid) as
    (n & Hreplicas_eq & Hn_nonneg).
  assert (rs_get.(ReplicaSetV.Spec').(ReplicaSetSpecV.Replicas') = Some n) as Hreplicas_eq_get.
  { rewrite <-Hget_Hspec_eq. exact Hreplicas_eq. }
  assert (length all_pods = sint.nat n) as Hactive_len.
  { unfold current_state_matches in Hmatch.
    rewrite Hreplicas_eq in Hmatch. simpl in Hmatch.
    rewrite -(filter_all is_pod_alive all_pods Hall_alive).
    rewrite (active_pod_count_erased_meta_perm all_pods pods Hall_meta_perm).
    exact Hmatch. }
  wp_apply (wp_manageReplicas_stability ctx kube_client burst claimed_sl rs_l claimed_ptrs
    all_pods rs_get n DfracDiscarded DfracDiscarded with
    "[$Hclaimed_sl $Hclaimed_deepown_pods $Hdeepown_l_rs]").
  { iFrame "#".
    iPureIntro. split_and!; done. }
  iIntros "(Hclaimed_sl & _ & _)".
  wp_auto_keep.
  (* rs = rs.DeepCopy() *)
  iDestruct "Hdeepown_l_rs" as (rs_phy) "[Hrs_l Hrs]".
  wp_apply (wp_ReplicaSet__DeepCopy with "[$Hrs_l $Hrs]").
  iIntros (copy_l) "(Hcopy & _ & _)".
  wp_pures_keep. wp_store. wp_pures_keep. wp_alloc now_ptr as "now". wp_pures_keep. wp_load.
  (* now := rscClock.Now(), before the interface call is resolved. *)
  wp_bind (MethodResolve clock.PassiveClock "Now" _ _)%E.
  rewrite Hclock. iApply (wp_RealClock__Now with "[//]"). iNext. iIntros (now) "_". wp_auto_keep.
  iDestruct "Hcopy" as (copy_phy) "[Hcopy_l Hcopy]".
  wp_apply (wp_calculateStatus_no_manage_error with
    "[$Hcopy_l $Hcopy $Hclaimed_sl $Hclaimed_deepown_pods $Hterm_sl]").
  { iPureIntro. split; first exact Hrs_get_valid.
    rewrite -Hget_Hspec_eq. exact Hlabels_bound. }
  iIntros (status_c status) "(Hcopy_l & Hcopy & #Hstatus & Hclaimed_sl & _ & Hterm_sl &
    %Hstatus_replicas & %Hstatus_og & %Hstatus_valid)".
  wp_auto_keep.
  (* updateReplicaSetStatus(kubeClient.AppsV1().ReplicaSets(rs.Namespace), rs, newStatus) *)
  iAssert (⌜ copy_phy.(v1.ReplicaSet.ObjectMeta').(v1.ObjectMeta.Namespace') =
    rs_get.(ReplicaSetV.ObjectMeta').(ObjectMetaV.Namespace') ⌝)%I as %Hcopy_ns.
  { iNamed "Hcopy". iNamed "Hdeepown_objectmeta". done. }
  rewrite Hcopy_ns.
  wp_bind (MethodResolve _ "ReplicaSets"%go _ _)%E.
  (* Instantiated explicitly: applying the lemma directly fails to unify. *)
  iPoseProof (wp_AppsV1_ReplicaSets kube_client
    rs_get.(ReplicaSetV.ObjectMeta').(ObjectMetaV.Namespace')) as "Hrs_client".
  iApply ("Hrs_client" with "[//]"). iNext. iIntros (c) "#Hclient". wp_auto_keep.
  iEval (rewrite Hrs_key_eq Hrs_uid_eq) in "Hown_rs_meta_frag Hown_rs_spec_frag Hown_rs_status_frag".
  iPoseProof (kview.own_meta_frag_equiv_except_resource_version Hget_Hmeta_eq with "Hown_rs_meta_frag") as "Hown_rs_meta_frag".
  iEval (rewrite Hget_Hspec_eq) in "Hown_rs_spec_frag".
  iEval (rewrite Hget_Hstatus_eq) in "Hown_rs_status_frag".
  (* The written status is valid: the claimed pods are a permutation of [pods],
     which are fewer than 2^31, so both counts fit in int32, and the observed
     generation is the non-negative generation of [rs]. *)
  assert (ReplicaSetStatusV.valid_request (status <| ReplicaSetStatusV.ObservedGeneration' :=
      rs_get.(ReplicaSetV.ObjectMeta').(ObjectMetaV.Generation') |>)) as Hstatus_valid_gen.
  { pose proof (Permutation_length Hall_meta_perm) as Hall_pods_len.
    rewrite !length_fmap in Hall_pods_len.
    apply Hstatus_valid.
    - lia.
    - lia.
    - pose proof (f_equal ObjectMetaV.Generation' Hget_Hmeta_fields) as Hgen.
      simpl in Hgen. rewrite Hgen. exact Hgeneration_nonneg. }
  wp_apply (wp_updateReplicaSetStatus γ l c copy_l copy_phy rs_get status_c status dq
    with "[$Hcopy_l $Hcopy $Hown_rs_meta_frag $Hown_rs_spec_frag $Hown_rs_status_frag]").
  { iFrame "#". iPureIntro. split; [done|exact Hstatus_valid_gen]. }
  iIntros (result_l rs') "(%Hchanged & Hown_rs_meta_frag & Hown_rs_spec_frag & Hown_rs_status_frag)".
  destruct Hchanged as (Hmeta_changed & Hspec_changed).
  wp_auto_keep.
  (* The listed pods' fragments, moved back onto [pods] by their storage views. *)
  iAssert ([∗ list] pod ∈ all_pods,
      own_meta_frag γ (PodV.key pod) pod.(PodV.ObjectMeta').(ObjectMetaV.UID') dq pod.(PodV.ObjectMeta') ∗
      own_spec_frag γ (PodV.key pod) pod.(PodV.ObjectMeta').(ObjectMetaV.UID') dq
        (ObjectSpecV.PodSpec pod.(PodV.Spec')))%I
    with "[Hall_meta_frags Hall_spec_frags]" as "Hall_frags".
  { rewrite big_sepL_sep. iFrame. }
  iEval (rewrite own_pod_frags_as_storage_views (big_sepL_permutation _ _ _ Hall_view_perm)
    -own_pod_frags_as_storage_views) in "Hall_frags".
  iDestruct (big_sepL_sep with "Hall_frags") as "[Hown_pod_meta_frags Hown_pod_spec_frags]".
  assert (owner_ref_key ReplicaSetV.kind rs_get.(ReplicaSetV.ObjectMeta') =
      ReplicaSetV.key rs_get) as Howner_key_eq.
  { rewrite /owner_ref_key /ReplicaSetV.key /ReplicaSetV.meta_key /ReplicaSetV.kind. done. }
  iEval (rewrite Howner_key_eq -Hrs_key_eq -Hrs_uid_eq) in "Hown_children_frag".
  iEval (rewrite Howner_key_eq -Hrs_key_eq -Hrs_uid_eq) in "Hown_terminating_children_frag".
  (* The ReplicaSet after the sync: the stored one, [rs'] with [rs]'s TypeMeta. *)
  set rs'' := rs' <| ReplicaSetV.TypeMeta' := rs.(ReplicaSetV.TypeMeta') |>.
  assert (rs'.(ReplicaSetV.Spec') = rs.(ReplicaSetV.Spec')) as Hspec_changed'.
  { rewrite Hspec_changed Hget_Hspec_eq. done. }
  iEval (rewrite -Hrs_ns_eq) in "Hown_pod_orphans".
  iDestruct (owned_resources_after_status_update γ rs rs_get rs'
      pods orphan_pods (stability_fractions dq) true
      Hrs_key_eq Hrs_uid_eq Hmeta_changed Hspec_changed' Hpods_nodup Hpods_bound Horphans_nodup
    with "Hown_rs_meta_frag Hown_rs_spec_frag Hown_rs_status_frag Hown_pod_meta_frags Hown_pod_spec_frags
      Hown_pod_unreserved_key_frags
      Hown_children_frag [$Hown_terminating_children_frag] Hown_orphan_pod_frags
      Hown_orphan_unreserved_key_frags Hown_pod_orphans")
    as "Hresources".
  iApply ("HΦ" $! rs'' with "[$Hresources]").
Qed.

End proof.
