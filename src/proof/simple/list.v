From New.proof Require Import prelude empty_ffi.
From New.proof.simple Require Export apimodel.

Section proof.
Context `{hG: !heapGS Σ} {go_ctx: GoContext}.
Context `{!mapG Σ KKey.t interface.t}.
Context `{!mapG Σ KKey.t KObjectV.t}.
Context `{!mapG Σ KKey.t (gset KKey.t)}.
Context `{!auth_setG Σ KKey.t}.

Lemma wp_State__objListLocked_pod γ l phys_state_l phys_state abs_state kind namespace pure_pod_map:
  {{{ is_pkg_init apimodel ∗
      "%Hkind_eq" ∷ ⌜ kind = "Pod"%go ⌝ ∗
      "Hstate_m_addr" ∷ l ↦s[apimodel.State :: "m"] phys_state_l ∗
      "Hown_phys" ∷ phys_state_l ↦$ phys_state ∗
      "Hown_abs" ∷ map_ctx γ.(γ_state) 1 abs_state ∗
      "Hphys_abs_rep" ∷ state_rep phys_state abs_state ∗
      "Hghostpods" ∷ ([∗ map] key ↦ pod ∈ pure_pod_map, key [[ γ.(γ_state) ]]↦ KObjectV.Pod pod) ∗
      "%Habs_state_valid" ∷ ⌜ ∀ k obj, abs_state !! k = Some obj → k = KObjectV.key obj ∧ KObjectV.valid obj ⌝
  }}}
    l @ (ptrT.id apimodel.State.id) @ "objListLocked" #kind #namespace
  {{{ sl ptr_list pure_pod_list, RET #sl;
      sl ↦* map (λ ptr, interface.mk (ptrT.id v1.Pod.id) #ptr) ptr_list ∗
      ([∗ list] ptr;pure_pod ∈ ptr_list;pure_pod_list, PodV.deepown_l ptr pure_pod 1) ∗
      ⌜ ∀ p, p ∈ pure_pod_list → PodV.valid p ⌝ ∗
      ⌜ ∀ p, p ∈ pure_pod_list → abs_state !! PodV.key p = Some (KObjectV.Pod p) ⌝ ∗
      ⌜ ∀ i j p1 p2, i ≠ j → pure_pod_list !! i = Some p1 → pure_pod_list !! j = Some p2 → PodV.key p1 ≠ PodV.key p2 ⌝ ∗
      ⌜ ∀ p, p ∈ pure_pod_list → v1.namespace_matches namespace p.(PodV.ObjectMeta').(ObjectMetaV.Namespace') ⌝ ∗
      ⌜ ∀ k p, pure_pod_map !! k = Some p →
        v1.namespace_matches namespace p.(PodV.ObjectMeta').(ObjectMetaV.Namespace') →
        p ∈ pure_pod_list ⌝ ∗
      l ↦s[apimodel.State :: "m"] phys_state_l ∗
      phys_state_l ↦$ phys_state ∗
      map_ctx γ.(γ_state) 1 abs_state ∗
      state_rep phys_state abs_state ∗
      ([∗ map] key ↦ pod ∈ pure_pod_map, key [[ γ.(γ_state) ]]↦ KObjectV.Pod pod)
  }}}.
Proof.
Admitted.

End proof.
