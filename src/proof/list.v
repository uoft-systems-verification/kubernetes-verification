From New.proof Require Import prelude empty_ffi.
From New.proof Require Export apimodel.

Section proof.
Context `{hG: !heapGS Σ} {go_ctx: GoContext}.
Context `{!mapG Σ KKey.t interface.t}.
Context `{!mapG Σ KKey.t PureKObject.t}.
Context `{!mapG Σ KKey.t (gset KKey.t)}.
Context `{!auth_setG Σ KKey.t}.

Lemma wp_State__objListLocked_pod γ l phys_state_l phys_state abs_state kind namespace pure_pod_map:
  {{{ is_pkg_init apimodel ∗
      "%Hkind_eq" ∷ ⌜ kind = "Pod"%go ⌝ ∗
      "Hstate_m_addr" ∷ l ↦s[apimodel.State :: "m"] phys_state_l ∗
      "Hown_phys" ∷ phys_state_l ↦$ phys_state ∗
      "Hown_abs" ∷ map_ctx γ.(γ_state) 1 abs_state ∗
      "Hphys_abs_rep" ∷ state_rep phys_state abs_state ∗
      "Hghostpods" ∷ ([∗ map] key ↦ pod ∈ pure_pod_map, key [[ γ.(γ_state) ]]↦ PureKObject.Pod pod) ∗
      "%Habs_state_well_formed" ∷ ⌜ ∀ k obj, abs_state !! k = Some obj → k = PureKObject.key obj ∧ PureKObject.well_formed obj ⌝
  }}}
    l @ (ptrT.id apimodel.State.id) @ "objListLocked" #kind #namespace
  {{{ sl ptr_list pure_pod_list, RET #sl;
      sl ↦* map (λ ptr, interface.mk (ptrT.id v1.Pod.id) #ptr) ptr_list ∗
      ([∗ list] ptr;pure_pod ∈ ptr_list;pure_pod_list, ∃ pod, PurePod.deepown_l ptr pod pure_pod 1) ∗
      ⌜ ∀ p, p ∈ pure_pod_list → PurePod.well_formed p ⌝ ∗
      ⌜ ∀ p, p ∈ pure_pod_list → abs_state !! PurePod.key p = Some (PureKObject.Pod p) ⌝ ∗
      ⌜ ∀ p, p ∈ pure_pod_list → v1.namespace_matches namespace p.(PurePod.ObjectMeta').(PureObjectMeta.Namespace') ⌝ ∗
      ⌜ ∀ k p, pure_pod_map !! k = Some p →
        v1.namespace_matches namespace p.(PurePod.ObjectMeta').(PureObjectMeta.Namespace') →
        p ∈ pure_pod_list ⌝ ∗
      l ↦s[apimodel.State :: "m"] phys_state_l ∗
      phys_state_l ↦$ phys_state ∗
      map_ctx γ.(γ_state) 1 abs_state ∗
      state_rep phys_state abs_state ∗
      ([∗ map] key ↦ pod ∈ pure_pod_map, key [[ γ.(γ_state) ]]↦ PureKObject.Pod pod)
  }}}.
Proof.
Admitted.

End proof.
