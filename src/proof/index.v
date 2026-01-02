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
  parent_key owned_parent owned_pod_map owned_child_keys:
  {{{ is_pkg_init apimodel ∗
      "#Hisk" ∷ is_kubernetes γ l ∗
      "%Hkind" ∷ ⌜ kind = "Pod"%go ⌝ ∗
      "%Hindex_name" ∷ ⌜ index_name = "podController"%go ⌝ ∗
      "%Hindexed_value" ∷ ⌜ indexed_value = parent_key.(KKey.Namespace') ++ "/"%go ++
                                            parent_key.(KKey.Kind') ++ "/"%go ++
                                            parent_key.(KKey.Name') ++ "/"%go ++
                                            (PureKObject.metadata owned_parent).(PureObjectMeta.UID') ⌝ ∗
      "Hown_parent" ∷ parent_key [[ γ.(γ_state) ]]↦ owned_parent ∗
      "Hown_pods" ∷ ([∗ map] key ↦ pod ∈ owned_pod_map, key [[ γ.(γ_state) ]]↦ PureKObject.Pod pod) ∗
      "Hown_child_keys" ∷ parent_key [[ γ.(γ_children) ]]↦ owned_child_keys ∗
      "%Hdom_eq" ∷ ⌜ owned_child_keys = dom owned_pod_map ⌝
  }}}
    l @ (ptrT.id apimodel.State.id) @ "ByIndex" #kind #index_name #indexed_value
  {{{ objs_l (ptrs: list loc) (pods: list v1.Pod.t) (pure_pods: list PurePod.t) dq, RET (#objs_l, #interface.nil);
      "Hobjs_l" ∷ objs_l ↦* map (λ ptr, interface.mk (ptrT.id v1.Pod.id) #ptr) ptrs∗
      "Hptrs_pods" ∷ ([∗ list] ptr;pod ∈ ptrs;pods, ptr ↦{dq} pod) ∗
      "Hpods_purepods" ∷ ([∗ list] pod;pure_pod ∈ pods;pure_pods, PurePod.deepown pod pure_pod dq) ∗
      "%Hwell_formed_pure_pods" ∷ ⌜ ∀ pure_pod, pure_pod ∈ pure_pods → PurePod.well_formed pure_pod ⌝ ∗
      "%Hlen_pure_pods" ∷ ⌜ length pure_pods = size owned_pod_map ⌝ ∗
      "%Hkey_set_equal_dom_owned_pods" ∷  ⌜ ∀ pure_pod, pure_pod ∈ pure_pods → ∃ k, owned_pod_map !! k = Some pure_pod ⌝ ∗
      "Hown_parent" ∷ parent_key [[ γ.(γ_state) ]]↦ owned_parent ∗
      "Hown_pods" ∷ ([∗ map] key ↦ pod ∈ owned_pod_map, key [[ γ.(γ_state) ]]↦ PureKObject.Pod pod) ∗
      "Hown_child_keys" ∷ parent_key [[ γ.(γ_children) ]]↦ owned_child_keys ∗
      "%Hown_pod_keys_eq" ∷ ⌜ ∀ key pod, owned_pod_map !! key = Some pod → key = PurePod.key pod ⌝ ∗
      "%Hown_pods_namespace_eq" ∷ ⌜ ∀ key, key ∈ dom owned_pod_map → key.(KKey.Namespace') = parent_key.(KKey.Namespace') ⌝
  }}}.
Proof.
Admitted.

End proof.
