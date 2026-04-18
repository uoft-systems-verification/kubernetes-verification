From New.proof Require Import prelude empty_ffi.
From New.proof.kubernetes_model Require Export inv common.

Section proof.
Context `{hG: !heapGS Σ} {go_ctx: GoContext}.
Context `{!kviewG Σ}.
Context `{!cviewG Σ}.
Context `{!mono_gsetG types.UID.t Σ}.

Lemma wp_index_of_podController i l pod dq:
  {{{ is_pkg_init apimodel ∗
      ⌜ i = interface.mk (ptrT.id v1.Pod.id) #l ⌝ ∗
      PodV.deepown_l l pod dq ∗
      ⌜ PodV.valid pod ⌝
  }}}
    @! apimodel.index_of #"podController"%go #i
  {{{ sl idx_val, RET (#sl, #interface.nil);
      sl ↦* [idx_val] ∗
      ⌜ idx_val =
        match meta_parent_ref pod.(PodV.ObjectMeta') with
        | Some (parent_key, parent_uid) =>
          pod.(PodV.ObjectMeta').(ObjectMetaV.Namespace') ++ "/"%go ++
          parent_key.(KKey.Kind') ++ "/"%go ++ parent_key.(KKey.Name') ++ "/"%go ++ parent_uid
        | None => pod.(PodV.ObjectMeta').(ObjectMetaV.Namespace')
        end ⌝ ∗
      PodV.deepown_l l pod dq
  }}}.
Proof. Admitted.

Lemma wp_State__ByIndex_podController_au γ l indexed_value :
  ∀ Φ,
  ( is_pkg_init apimodel ∗
    is_kubernetes γ l ∗
    |={⊤,∅}=> ∃ pod_map has_kspec has_kstatus parent_key parent_uid children_keys dq,
      "Hown_meta_frags" ∷ ([∗ map] key ↦ pod ∈ pod_map,
        own_meta_frag γ key pod.(PodV.ObjectMeta').(ObjectMetaV.UID') dq pod.(PodV.ObjectMeta')) ∗
      "Hown_spec_frags" ∷ match has_kspec with
      | true => ([∗ map] key ↦ pod ∈ pod_map,
        own_spec_frag γ key pod.(PodV.ObjectMeta').(ObjectMetaV.UID') dq (ObjectSpecV.PodSpec pod.(PodV.Spec')))
      | false => True
      end ∗
      "Hown_status_frags" ∷ match has_kstatus with
      | true => ([∗ map] key ↦ pod ∈ pod_map,
        own_status_frag γ key pod.(PodV.ObjectMeta').(ObjectMetaV.UID') dq (ObjectStatusV.PodStatus pod.(PodV.Status')))
      | false => True
      end ∗
      "Hown_children_frag" ∷ own_children_frag γ parent_key parent_uid dq children_keys ∗
      "%Hindexed_value_eq" ∷ ⌜ indexed_value = parent_key.(KKey.Namespace') ++ "/"%go ++
        parent_key.(KKey.Kind') ++ "/"%go ++ parent_key.(KKey.Name') ++ "/"%go ++ parent_uid ⌝ ∗
      "%Hdom_subset" ∷ ⌜ dom pod_map ⊆ children_keys ⌝ ∗
      "Hclose" ∷ (∀ interfaces pods dq',
        ([∗ list] i;pod ∈ interfaces;pods, KObjectV.deepown_i i (KObjectV.Pod pod) dq') ∗
        (* every returned pod is valid *)
        ⌜ ∀ pod, pod ∈ pods → PodV.valid pod ⌝ ∗
        (* every pod in the map has the right key *)
        ⌜ map_Forall (λ key pod, key = PodV.key pod) pod_map ⌝ ∗
        (* every pod in the map is also in the list *)
        ⌜ ∀ pod, pod ∈ pods → pod_map !! (PodV.key pod) = Some pod ⌝ ∗
        (* every pod in the list is also in the map *)
        ⌜ map_Forall (λ _ pod, pod ∈ pods) pod_map ⌝ ∗
        (* no dup keys in the list *)
        ⌜ NoDup (PodV.key <$> pods) ⌝ ∗
        (* children keys are the same as the parent key *)
        ⌜ map_Forall (λ key _, key.(KKey.Namespace') = parent_key.(KKey.Namespace')) pod_map ⌝ ∗
        (* return the input fragments *)
        ([∗ map] key ↦ pod ∈ pod_map,
            own_meta_frag γ key pod.(PodV.ObjectMeta').(ObjectMetaV.UID') dq pod.(PodV.ObjectMeta')) ∗
        match has_kspec with
        | true => ([∗ map] key ↦ pod ∈ pod_map,
          own_spec_frag γ key pod.(PodV.ObjectMeta').(ObjectMetaV.UID') dq (ObjectSpecV.PodSpec pod.(PodV.Spec')))
        | false => True
        end ∗
        match has_kstatus with
        | true => ([∗ map] key ↦ pod ∈ pod_map,
          own_status_frag γ key pod.(PodV.ObjectMeta').(ObjectMetaV.UID') dq (ObjectStatusV.PodStatus pod.(PodV.Status')))
        | false => True
        end ∗
        own_children_frag γ parent_key parent_uid dq children_keys
          ={∅,⊤}=∗ ▷ Φ (#interfaces, #interface.nil)%V
      )
  ) -∗ WP l @ (ptrT.id apimodel.State.id) @ "ByIndex" #"Pod"%go #"podController"%go #indexed_value {{ Φ }}.
Proof. Admitted.


End proof.
