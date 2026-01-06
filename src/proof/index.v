From New.proof Require Import prelude empty_ffi.
From New.proof Require Export apimodel.

Section proof.
Context `{hG: !heapGS Σ} {go_ctx: GoContext}.
Context `{!mapG Σ KKey.t interface.t}.
Context `{!mapG Σ KKey.t PureKObject.t}.
Context `{!mapG Σ KKey.t (gset KKey.t)}.
Context `{!auth_setG Σ KKey.t}.

(* TODO: revisit this spec *)
Lemma wp_State__ByIndex_pod γ l kind index_name indexed_value
  parent_key owned_parent pod_map owned_child_keys:
  {{{ is_pkg_init apimodel ∗
      "#Hisk" ∷ is_kubernetes γ l ∗
      "%Hkind" ∷ ⌜ kind = "Pod"%go ⌝ ∗
      "%Hindex_name" ∷ ⌜ index_name = "podController"%go ⌝ ∗
      "%Hindexed_value" ∷ ⌜ indexed_value = parent_key.(KKey.Namespace') ++ "/"%go ++
                                            parent_key.(KKey.Kind') ++ "/"%go ++
                                            parent_key.(KKey.Name') ++ "/"%go ++
                                            (PureKObject.metadata owned_parent).(PureObjectMeta.UID') ⌝ ∗
      "Hown_parent" ∷ parent_key [[ γ.(γ_state) ]]↦ owned_parent ∗
      "Hown_pod_list" ∷ ([∗ map] key ↦ pod ∈ pod_map, key [[ γ.(γ_state) ]]↦ PureKObject.Pod pod) ∗
      "Hown_child_keys" ∷ parent_key [[ γ.(γ_children) ]]↦ owned_child_keys ∗
      "%Hdom_eq" ∷ ⌜ owned_child_keys = dom pod_map ⌝
  }}}
    l @ (ptrT.id apimodel.State.id) @ "ByIndex" #kind #index_name #indexed_value
  {{{ objs_l (ptr_list: list loc) (pod_list: list v1.Pod.t) (pure_pod_list: list PurePod.t) dq, RET (#objs_l, #interface.nil);
      "Hobjs_l" ∷ objs_l ↦* map (λ ptr, interface.mk (ptrT.id v1.Pod.id) #ptr) ptr_list∗
      "Hptrs_pods" ∷ ([∗ list] ptr;pod ∈ ptr_list;pod_list, ptr ↦{dq} pod) ∗
      "Hpods_purepods" ∷ ([∗ list] pod;pure_pod ∈ pod_list;pure_pod_list, PurePod.deepown pod pure_pod dq) ∗
      "%Hwell_formed_pure_pod_list" ∷ ⌜ ∀ p, p ∈ pure_pod_list → PurePod.well_formed p ⌝ ∗
      "%Hlen_size_eq" ∷ ⌜ length pure_pod_list = size pod_map ⌝ ∗
      "%Hlist_in_map" ∷  ⌜ ∀ p, p ∈ pure_pod_list → pod_map !! (PurePod.key p) = Some p ⌝ ∗
      "%Hmap_in_list" ∷ ⌜ ∀ k p, pod_map !! k = Some p → p ∈ pure_pod_list ⌝ ∗
      "%Hown_pod_keys_eq" ∷ ⌜ ∀ key pod, pod_map !! key = Some pod → key = PurePod.key pod ⌝ ∗
      "%Hown_pod_list_namespace_eq" ∷ ⌜ ∀ key, key ∈ dom pod_map → key.(KKey.Namespace') = parent_key.(KKey.Namespace') ⌝ ∗
      "%Hno_dup" ∷ ⌜ ∀ i j p1 p2, i ≠ j → pure_pod_list !! i = Some p1 → pure_pod_list !! j = Some p2 → (PurePod.key p1) ≠ (PurePod.key p2) ⌝ ∗
      "Hown_parent" ∷ parent_key [[ γ.(γ_state) ]]↦ owned_parent ∗
      "Hown_pod_list" ∷ ([∗ map] key ↦ pod ∈ pod_map, key [[ γ.(γ_state) ]]↦ PureKObject.Pod pod) ∗
      "Hown_child_keys" ∷ parent_key [[ γ.(γ_children) ]]↦ owned_child_keys
  }}}.
Proof.
Admitted.

End proof.
