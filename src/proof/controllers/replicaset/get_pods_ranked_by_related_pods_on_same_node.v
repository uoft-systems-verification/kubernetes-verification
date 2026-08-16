From New.proof Require Import prelude empty_ffi.
From New.proof.controllers.replicaset Require Export replicaset_init.
From New.proof.k8s_io.kubernetes.pkg Require Export controller.
From New.proof.kubernetes_types Require Export prelude.

Section proof.
Context `{hG: !heapGS Σ} `{!ffi_semantics _ _}.
Context {sem : go.Semantics}
  {package_sem : code.controllers.replicaset.replicaset.Assumptions}.
Collection W := sem + package_sem.
#[local] Instance base_common_sem : common.Assumptions | 100 :=
  code.controllers.replicaset.replicaset.import_common_Assumption.
#[local] Instance controller_sem : controller.Assumptions :=
  code.controllers.replicaset.replicaset.import_controller_Assumption.
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
Local Set Default Proof Using "All".

Lemma wp_getPodsRankedByRelatedPodsOnSameNode pods_sl pods_ptrs pods
    related_sl related_ptrs related_pods dq1 dq2 :
  {{{ is_pkg_init code.controllers.replicaset.pkg_id.replicaset ∗
      "Hpods_sl" ∷ pods_sl ↦* pods_ptrs ∗
      "Hpods" ∷ ([∗ list] ptr;pod ∈ pods_ptrs;pods, PodV.deepown_l ptr pod dq1) ∗
      "Hrelated_sl" ∷ related_sl ↦* related_ptrs ∗
      "Hrelated" ∷ ([∗ list] ptr;pod ∈ related_ptrs;related_pods, PodV.deepown_l ptr pod dq2)
  }}}
    @! replicaset.getPodsRankedByRelatedPodsOnSameNode #pods_sl #related_sl
  {{{ (ranked : controller.ActivePodsWithRanks.t) (ranks : list w64), RET #ranked;
      "%Hranked_pods" ∷ ⌜ ranked.(controller.ActivePodsWithRanks.Pods') = pods_sl ⌝ ∗
      "%Hranked_len" ∷ ⌜ sint.Z (slice.len ranked.(controller.ActivePodsWithRanks.Rank')) =
        sint.Z (slice.len pods_sl) ⌝ ∗
      ranked.(controller.ActivePodsWithRanks.Rank') ↦* ranks ∗
      pods_sl ↦* pods_ptrs ∗
      ([∗ list] ptr;pod ∈ pods_ptrs;pods, PodV.deepown_l ptr pod dq1) ∗
      related_sl ↦* related_ptrs ∗
      ([∗ list] ptr;pod ∈ related_ptrs;related_pods, PodV.deepown_l ptr pod dq2)
  }}}.
Proof.
  wp_start as "H". iNamed "H". wp_auto.
  wp_apply wp_map_make1 as "%pods_on_node_l Hpods_on_node".
  iDestruct (own_slice_len with "Hrelated_sl") as %(Hrelated_len1 & Hrelated_len2).
  iDestruct (big_sepL2_length with "Hrelated") as %Hrelated_len.
  set I := (∃ (i : w64) (pod_l : loc) (counts : gmap go_string w64),
    "i" ∷ i_ptr ↦ i ∗ "pod" ∷ pod_ptr ↦ pod_l ∗
    "podsOnNode" ∷ podsOnNode_ptr ↦ pods_on_node_l ∗
    "Hpods_on_node" ∷ pods_on_node_l ↦$ counts ∗
    "Hrelated" ∷ ([∗ list] ptr;pod ∈ related_ptrs;related_pods,
      PodV.deepown_l ptr pod dq2) ∗
    "%Hi" ∷ ⌜ 0 ≤ sint.Z i ≤ sint.Z (slice.len related_sl) ⌝)%I.
  iAssert I with "[i pod podsOnNode Hpods_on_node Hrelated]" as "Hloop".
  { iExists (W64 0), null, ∅. iFrame. iPureIntro. word. }
  wp_for "Hloop". wp_if_destruct.
  - list_elem related_ptrs (sint.Z i) as this_ptr.
    destruct (decide (0 ≤ sint.Z i < sint.Z (slice.len related_sl))) as [_|Hbounds]; last word.
    wp_apply (wp_load_slice_index with "[$Hrelated_sl]"); [word|iPureIntro; exact Hthis_ptr_lookup|].
    iIntros "Hrelated_sl". wp_auto.
    assert (∃ this_pod, related_pods !! sint.nat i = Some this_pod) as
      [this_pod Hthis_pod_lookup].
    { apply lookup_lt_is_Some_2. rewrite -Hrelated_len Hrelated_len1. word. }
    iDestruct (big_sepL2_lookup_acc with "Hrelated") as "[Hthis Hrestore]";
      [exact Hthis_ptr_lookup|exact Hthis_pod_lookup|].
    wp_apply (wp_IsPodActive with "[$Hthis]"). iIntros (active) "Hthis".
    wp_if_destruct.
    + iPoseProof (PodV.deepown_l_split with "Hthis") as
        "(%Hthis_not_null & Htype & Hmeta & Hspec & Hstatus)".
      iDestruct "Hspec" as (spec_c) "[Hspec_l Hspec]".
      iDestruct (struct_fields_split with "Hspec_l") as "[Hspec_fields %Hspec_not_null]".
      iNamedPrefix "Hspec_fields" "Hspec_". wp_auto.
      wp_apply (wp_map_lookup1 with "Hpods_on_node") as "Hpods_on_node".
      wp_apply (wp_map_insert go.string with "Hpods_on_node") as "Hpods_on_node".
      iDestruct (struct_fields_combine (V:=v1.PodSpec.t) _ spec_c dq2 Hspec_not_null
        with "[Hspec_Volumes Hspec_InitContainers Hspec_Containers Hspec_EphemeralContainers
          Hspec_RestartPolicy Hspec_TerminationGracePeriodSeconds Hspec_ActiveDeadlineSeconds
          Hspec_DNSPolicy Hspec_NodeSelector Hspec_ServiceAccountName Hspec_DeprecatedServiceAccount
          Hspec_AutomountServiceAccountToken Hspec_NodeName Hspec_HostNetwork Hspec_HostPID
          Hspec_HostIPC Hspec_ShareProcessNamespace Hspec_SecurityContext Hspec_ImagePullSecrets
          Hspec_Hostname Hspec_Subdomain Hspec_Affinity Hspec_SchedulerName Hspec_Tolerations
          Hspec_HostAliases Hspec_PriorityClassName Hspec_Priority Hspec_DNSConfig Hspec_ReadinessGates
          Hspec_RuntimeClassName Hspec_EnableServiceLinks Hspec_PreemptionPolicy Hspec_Overhead
          Hspec_TopologySpreadConstraints Hspec_SetHostnameAsFQDN Hspec_OS Hspec_HostUsers
          Hspec_SchedulingGates Hspec_ResourceClaims Hspec_Resources Hspec_HostnameOverride]") as "Hspec_l".
      all: try iFrame.
      iAssert (PodSpecV.deepown_l (PodV.spec_ptr this_ptr) this_pod.(PodV.Spec') dq2)
        with "[Hspec_l Hspec]" as "Hspec".
      { iExists spec_c. iFrame. }
      iAssert (PodV.deepown_l this_ptr this_pod dq2) with
        "[Htype Hmeta Hspec Hstatus]" as "Hthis".
      { iApply (PodV.deepown_l_restore _ _ _ Hthis_not_null). iFrame. }
      iPoseProof ("Hrestore" with "Hthis") as "Hrelated".
      iApply wp_for_post_do. wp_auto. iFrame "Hrelated_sl HΦ Hpods_sl Hpods podsToRank".
      iExists (word.add i (W64 1)), this_ptr, _. iFrame. iPureIntro. word.
    + iPoseProof ("Hrestore" with "Hthis") as "Hrelated".
      iApply wp_for_post_do. wp_auto. iFrame "Hrelated_sl HΦ Hpods_sl Hpods podsToRank".
      iExists (word.add i (W64 1)), this_ptr, _. iFrame. iPureIntro. word.
  - clear I.
    iDestruct (own_slice_len with "Hpods_sl") as %(Hpods_len1 & Hpods_len2).
    iDestruct (big_sepL2_length with "Hpods") as %Hpods_len.
    wp_apply wp_slice_make2; first word.
    iIntros (ranks_sl) "[Hranks Hranks_cap]".
    iDestruct (own_slice_len with "Hranks") as %(Hranks_len1 & Hranks_len2).
    assert (Hranks_sl_len : sint.Z (slice.len ranks_sl) = sint.Z (slice.len pods_sl)).
    { rewrite length_replicate in Hranks_len1. word. }
    wp_auto.
    wp_alloc loop_i_ptr as "loop_i".
    set J := (∃ (j rank_i : w64) (pod_l : loc) (ranks : list w64),
      "loop_i" ∷ loop_i_ptr ↦ j ∗ "i" ∷ i_ptr ↦ rank_i ∗ "pod" ∷ pod_ptr ↦ pod_l ∗
      "ranks" ∷ ranks_ptr ↦ ranks_sl ∗ "Hranks" ∷ ranks_sl ↦* ranks ∗
      "Hpods" ∷ ([∗ list] ptr;pod ∈ pods_ptrs;pods, PodV.deepown_l ptr pod dq1) ∗
      "%Hranks_len" ∷ ⌜ length ranks = sint.nat (slice.len ranks_sl) ⌝ ∗
      "%Hj" ∷ ⌜ 0 ≤ sint.Z j ≤ sint.Z (slice.len pods_sl) ⌝)%I.
    iAssert J with "[loop_i i pod ranks Hranks Hpods]" as "Hloop".
    { iExists (W64 0), (W64 0), null,
        (replicate (sint.nat (slice.len pods_sl)) (W64 0)).
      iFrame. iPureIntro. split; [exact Hranks_len1|word]. }
    wp_auto.
    wp_for "Hloop". wp_if_destruct.
    + list_elem pods_ptrs (sint.Z j) as this_ptr.
      destruct (decide (0 ≤ sint.Z j < sint.Z (slice.len pods_sl))) as [_|Hbounds]; last word.
      wp_apply (wp_load_slice_index with "[$Hpods_sl]");
        [word|iPureIntro; exact Hthis_ptr_lookup|].
      iIntros "Hpods_sl". wp_auto.
      assert (∃ this_pod, pods !! sint.nat j = Some this_pod) as
        [this_pod Hthis_pod_lookup].
      { apply lookup_lt_is_Some_2. rewrite -Hpods_len Hpods_len1. word. }
      iDestruct (big_sepL2_lookup_acc with "Hpods") as "[Hthis Hrestore]";
        [exact Hthis_ptr_lookup|exact Hthis_pod_lookup|].
      iPoseProof (PodV.deepown_l_split with "Hthis") as
        "(%Hthis_not_null & Htype & Hmeta & Hspec & Hstatus)".
      iDestruct "Hspec" as (spec_c) "[Hspec_l Hspec]".
      iDestruct (struct_fields_split with "Hspec_l") as "[Hspec_fields %Hspec_not_null]".
      iNamedPrefix "Hspec_fields" "Hspec_". wp_auto.
      wp_apply (wp_map_lookup1 with "Hpods_on_node") as "Hpods_on_node".
      assert (Hj_rank : 0 ≤ sint.Z j < sint.Z (slice.len ranks_sl)) by
        (rewrite Hranks_sl_len; word).
      rewrite decide_True; [exact Hj_rank|].
      wp_auto.
      wp_apply (wp_store_slice_index with "[$Hranks]") as "Hranks"; first word.
      iDestruct (struct_fields_combine (V:=v1.PodSpec.t) _ spec_c dq1 Hspec_not_null
        with "[Hspec_Volumes Hspec_InitContainers Hspec_Containers Hspec_EphemeralContainers
          Hspec_RestartPolicy Hspec_TerminationGracePeriodSeconds Hspec_ActiveDeadlineSeconds
          Hspec_DNSPolicy Hspec_NodeSelector Hspec_ServiceAccountName Hspec_DeprecatedServiceAccount
          Hspec_AutomountServiceAccountToken Hspec_NodeName Hspec_HostNetwork Hspec_HostPID
          Hspec_HostIPC Hspec_ShareProcessNamespace Hspec_SecurityContext Hspec_ImagePullSecrets
          Hspec_Hostname Hspec_Subdomain Hspec_Affinity Hspec_SchedulerName Hspec_Tolerations
          Hspec_HostAliases Hspec_PriorityClassName Hspec_Priority Hspec_DNSConfig Hspec_ReadinessGates
          Hspec_RuntimeClassName Hspec_EnableServiceLinks Hspec_PreemptionPolicy Hspec_Overhead
          Hspec_TopologySpreadConstraints Hspec_SetHostnameAsFQDN Hspec_OS Hspec_HostUsers
          Hspec_SchedulingGates Hspec_ResourceClaims Hspec_Resources Hspec_HostnameOverride]") as "Hspec_l".
      all: try iFrame.
      iAssert (PodSpecV.deepown_l (PodV.spec_ptr this_ptr) this_pod.(PodV.Spec') dq1)
        with "[Hspec_l Hspec]" as "Hspec".
      { iExists spec_c. iFrame. }
      iAssert (PodV.deepown_l this_ptr this_pod dq1) with
        "[Htype Hmeta Hspec Hstatus]" as "Hthis".
      { iApply (PodV.deepown_l_restore _ _ _ Hthis_not_null). iFrame. }
      iPoseProof ("Hrestore" with "Hthis") as "Hpods".
      iApply wp_for_post_do. wp_auto.
      iFrame "Hpods_sl Hrelated_sl Hrelated HΦ podsToRank podsOnNode Hpods_on_node ranks Hranks_cap".
      iExists (word.add j (W64 1)), j, this_ptr, _. iFrame.
      iPureIntro. split; [rewrite length_insert; exact Hranks_len|word].
    + clear J. wp_auto.
      wp_apply v1.wp_Now. iIntros (now_c now) "Hnow". wp_auto.
      iApply "HΦ". iFrame.
      iSplit; first done. iPureIntro. exact Hranks_sl_len.
Unshelve. all: try tc_solve.
Qed.

End proof.
