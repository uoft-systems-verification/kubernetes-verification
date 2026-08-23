From New.proof Require Import prelude empty_ffi.
From New.proof.controllers.replicaset Require Export get_pods_ranked_by_related_pods_on_same_node.

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

Lemma wp_getPodsToDelete pods_sl pods_ptrs pods related_sl related_ptrs
    related_pods diff dq1 dq2 :
  {{{ is_pkg_init code.controllers.replicaset.pkg_id.replicaset ∗
      "Hpods_sl" ∷ pods_sl ↦* pods_ptrs ∗
      "Hpods" ∷ ([∗ list] ptr;pod ∈ pods_ptrs;pods, PodV.deepown_l ptr pod dq1) ∗
      "Hrelated_sl" ∷ related_sl ↦* related_ptrs ∗
      "Hrelated" ∷ ([∗ list] ptr;pod ∈ related_ptrs;related_pods, PodV.deepown_l ptr pod dq2) ∗
      "%Hdiff" ∷ ⌜ 0 ≤ sint.Z diff ≤ sint.Z (slice.len pods_sl) ⌝
  }}}
    @! replicaset.getPodsToDelete #pods_sl #related_sl #diff
  {{{ sorted_ptrs sorted_pods, RET #(slice.slice pods_sl loc (W64 0) diff);
      "Hbefore" ∷ (slice.slice pods_sl loc (W64 0) (W64 0)) ↦* ([] : list loc) ∗
      "Hdelete" ∷ (slice.slice pods_sl loc (W64 0) diff) ↦* take (sint.nat diff) sorted_ptrs ∗
      "Hafter" ∷ (slice.slice pods_sl loc diff (slice.len pods_sl)) ↦* drop (sint.nat diff) sorted_ptrs ∗
      "Hpods" ∷ ([∗ list] ptr;pod ∈ sorted_ptrs;sorted_pods, PodV.deepown_l ptr pod dq1) ∗
      "%Hptrs_perm" ∷ ⌜ pods_ptrs ≡ₚ sorted_ptrs ⌝ ∗
      "%Hpods_perm" ∷ ⌜ pods ≡ₚ sorted_pods ⌝
  }}}.
Proof.
  wp_start as "H". iNamed "H". wp_auto.
  iDestruct (own_slice_len with "Hpods_sl") as %(Hpods_len1 & Hpods_len2).
  wp_if_destruct.
  - wp_apply (wp_getPodsRankedByRelatedPodsOnSameNode with
      "[$Hpods_sl $Hpods $Hrelated_sl $Hrelated]").
    iIntros (ranked ranks)
      "(%Hranked_pods & %Hranked_len & Hranks & Hpods_sl & Hpods & Hrelated_sl & Hrelated)".
    (* Stop before the intentionally opaque [sort.Sort]; [wp_Sort] below is
       its trusted semantic boundary. *)
    wp_pures. wp_store. wp_pures. wp_load.
    iDestruct (big_sepL2_length with "Hpods") as %Hpods_len.
    iDestruct (own_slice_len with "Hranks") as %(Hranks_len1 & Hranks_len2).
    assert (Hptrs_ranks_len : length pods_ptrs = length ranks).
    { rewrite Hranks_len1 Hpods_len1.
      change (Z.to_nat (word.signed (slice.len pods_sl)) =
        Z.to_nat (word.signed (slice.len ranked.(controller.ActivePodsWithRanks.Rank')))).
      rewrite Hranked_len. reflexivity. }
    set (entries := active_pods_with_ranks_entries pods_ptrs pods ranks).
    wp_bind ((let: "$a0" := Convert controller.ActivePodsWithRanks sort.Interface #ranked in
      (FuncResolve sort.Sort [] #()) "$a0")%E).
    iApply (wp_Sort controller.ActivePodsWithRanks
      (active_pods_with_ranks_contents dq1) ranked entries
      with "[Hpods_sl Hranks Hpods]").
    { rewrite /active_pods_with_ranks_contents Hranked_pods.
      rewrite /entries.
      rewrite (active_pods_with_ranks_entries_ptrs _ _ _ Hpods_len Hptrs_ranks_len).
      rewrite (active_pods_with_ranks_entries_pods _ _ _ Hpods_len Hptrs_ranks_len).
      rewrite (active_pods_with_ranks_entries_ranks _ _ _ Hpods_len Hptrs_ranks_len).
      iSplit; first iPkgInit. iFrame. }
    iNext. iIntros (sorted_entries) "[Hcontents %Hentries_perm]".
    iEval (rewrite /active_pods_with_ranks_contents Hranked_pods) in "Hcontents".
    iDestruct "Hcontents" as "(Hpods_sl & Hranks & Hpods)".
    subst entries.
    pose proof (Permutation_map active_pod_ptr Hentries_perm) as Hptrs_perm.
    pose proof (Permutation_map active_pod_value Hentries_perm) as Hpods_perm.
    change (active_pod_ptr <$> active_pods_with_ranks_entries pods_ptrs pods ranks ≡ₚ
      active_pod_ptr <$> sorted_entries) in Hptrs_perm.
    change (active_pod_value <$> active_pods_with_ranks_entries pods_ptrs pods ranks ≡ₚ
      active_pod_value <$> sorted_entries) in Hpods_perm.
    rewrite (active_pods_with_ranks_entries_ptrs _ _ _ Hpods_len Hptrs_ranks_len) in Hptrs_perm.
    rewrite (active_pods_with_ranks_entries_pods _ _ _ Hpods_len Hptrs_ranks_len) in Hpods_perm.
    set (sorted_ptrs := active_pod_ptr <$> sorted_entries) in *.
    set (sorted_pods := active_pod_value <$> sorted_entries) in *.
    wp_auto.
    iDestruct (own_slice_wf with "Hpods_sl") as %Hpods_cap.
    iDestruct (own_slice_split_all diff with "Hpods_sl") as "[Hdelete Hafter]".
    { word. }
    iDestruct (own_slice_split (W64 0) pods_sl (DfracOwn 1)
      (take (sint.nat diff) sorted_ptrs) (W64 0) diff with "Hdelete")
      as "[Hbefore Hdelete]".
    { word. }
    replace (sint.nat (W64 0) - sint.nat (W64 0))%nat with 0%nat by word.
    iEval (simpl) in "Hbefore Hdelete".
    rewrite decide_True; [word|]. wp_auto.
    iApply "HΦ". iFrame. done.
  -
    iDestruct (own_slice_wf with "Hpods_sl") as %Hpods_cap.
    iDestruct (own_slice_split_all diff with "Hpods_sl") as "[Hdelete Hafter]".
    { word. }
    iDestruct (own_slice_split (W64 0) pods_sl (DfracOwn 1)
      (take (sint.nat diff) pods_ptrs) (W64 0) diff with "Hdelete")
      as "[Hbefore Hdelete]".
    { word. }
    replace (sint.nat (W64 0) - sint.nat (W64 0))%nat with 0%nat by word.
    iEval (simpl) in "Hbefore Hdelete".
    rewrite decide_True; [word|]. wp_auto.
    iApply "HΦ". iFrame. done.
Qed.

End proof.
