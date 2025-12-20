From Perennial.algebra Require Export auth_map.
From New.proof.github_com.goose_lang.goose.model.channel Require Export auth_set.
Require Export New.proof.sync.

From proof.kubernetes_model Require Export apimodel_init.
From proof.k8s_io.apimachinery.pkg.api Require Export meta.
From proof.k8s_io.apimachinery.pkg.apis.meta Require Export v1.
From proof Require Import prelude empty_ffi.
From proof Require Export apimodel.
From proof.big_op Require Import big_sepL big_sepM.
Export apimodel.apimodel.

Section proof.
Context `{hG: !heapGS Σ} {go_ctx: GoContext}.
Context `{!mapG Σ KKey.t interface.t}.
Context `{!mapG Σ KKey.t PureKObject.t}.
Context `{!mapG Σ KKey.t (gset KKey.t)}.
Context `{!auth_setG Σ KKey.t}.

(* TODO: revisit this spec *)
Lemma wp_ByIndex_pod_ptsto_mut kind index_name indexed_value
  γ_state γ_children γ_fresh_keys parent_key owned_parent owned_pod_map owned_child_keys:
  {{{ is_pkg_init apimodel ∗
      "#inv" ∷ is_kubernetes_state γ_state γ_children γ_fresh_keys ∗
      "own_parent" ∷ parent_key [[ γ_state ]]↦ owned_parent ∗
      "own_pods" ∷ ([∗ map] key ↦ pod ∈ owned_pod_map, key [[ γ_state ]]↦ PureKObject.Pod pod) ∗
      "own_child_keys" ∷ parent_key [[ γ_children ]]↦ owned_child_keys ∗
      "%owned_child_keys_equal_dom_owned_pods" ∷ ⌜ owned_child_keys = dom owned_pod_map ⌝ ∗
      "%indexed_value" ∷ ⌜ indexed_value = (PureKObject.metadata owned_parent).(PureObjectMeta.UID') ⌝ ∗
      "%kind" ∷ ⌜ kind = "Pod"%go ⌝ ∗
      "%index_name" ∷ ⌜ index_name = "podControllerUID"%go ⌝
  }}}
    @! apimodel.ByIndex #kind #index_name #indexed_value
  {{{ (l: slice.t) (err: error.t) (objs: list interface.t) (pods: list v1.Pod.t), RET (#l, #err);
      "l" ∷ l ↦* objs ∗
      "%err_is_nil" ∷ ⌜ err = interface.nil ⌝ ∗
      "obj_pts_to_pod" ∷ ([∗ list] obj ; pod ∈ objs ; pods, ∃ (ptr : loc) (owned_pod : PurePod.t),
        ⌜ obj = interface.mk (ptrT.id v1.Pod.id) #ptr ⌝ ∗
        ptr ↦ pod ∗
        PurePod.deepown pod owned_pod 1 ∗
        ⌜ ∃ k, owned_pod_map !! k = Some owned_pod ⌝ ∗
        ⌜ obj_has_controller_parent_of (PureKObject.Pod owned_pod) parent_key.(KKey.Kind') parent_key.(KKey.Name') indexed_value ⌝ ∗
        ⌜ PurePod.well_formed owned_pod ⌝
      ) ∗
      "%key_set_equal_dom_owned_pods" ∷  ⌜ list_to_set (extract_pod_key <$> pods) = dom owned_pod_map ⌝ ∗
      "own_parent" ∷ parent_key [[ γ_state ]]↦ owned_parent ∗
      "own_pods" ∷ ([∗ map] key ↦ pod ∈ owned_pod_map, key [[ γ_state ]]↦ PureKObject.Pod pod) ∗
      "own_child_keys" ∷ parent_key [[ γ_children ]]↦ owned_child_keys
  }}}.
Proof.
Admitted.

End proof.
