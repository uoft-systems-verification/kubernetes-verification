From New.proof Require Import prelude empty_ffi.
Require Export New.generatedproof.benchmark.client.
From New.proof.kubernetes_model Require Export create get delete.

Set Default Proof Using "Type".

Section init.
Context `{hG: heapGS Σ} `{!ffi_semantics _ _} {go_ctx: GoContext}.

#[global] Instance : IsPkgInit code.benchmark.client.client := define_is_pkg_init True%I.
#[global] Instance : GetIsPkgInitWf code.benchmark.client.client := build_get_is_pkg_init_wf.

End init.

Section proof.
Context `{hG: !heapGS Σ} {go_ctx: GoContext}.
Context `{!kviewG Σ}.
Context `{!cviewG Σ}.
Context `{!tombstoneG Σ}.

Definition pod_without_name (pod : PodV.t) : PodV.t :=
  pod <| PodV.ObjectMeta' := (pod.(PodV.ObjectMeta') <| ObjectMetaV.Name' := ""%go |>) |>.

Definition input_pod_ready parent_key parent_uid (pod : PodV.t) : Prop :=
  let pod_to_create := pod_without_name pod in
  let namespace := pod_to_create.(PodV.ObjectMeta').(ObjectMetaV.Namespace') in
  KObjectV.valid_nameless_create "Pod"%go namespace (KObjectV.Pod pod_to_create) ∧
  namespace ≠ ""%go ∧
  valid_namespace namespace ∧
  namespace = parent_key.(KKey.Namespace') ∧
  obj_parent_ref_is
    (KObjectV.Pod pod_to_create)
    parent_key.(KKey.Kind')
    parent_key.(KKey.Name')
    parent_uid.

Lemma wp_CreateThenDeletePods γ state_l pods_sl pod_ls pods parent_key parent_uid children :
  {{{ is_pkg_init client ∗
      is_pkg_init apimodel ∗
      "#Hisk" ∷ is_kubernetes γ state_l ∗
      "Hpods_sl" ∷ pods_sl ↦* pod_ls ∗
      "%Hlen_safe" ∷ ⌜ Z.of_nat (length pod_ls) < 2^63 ⌝ ∗
      "Hpods" ∷ ([∗ list] pod_l; pod ∈ pod_ls; pods, PodV.deepown_l pod_l pod 1) ∗
      "%Hready" ∷ ⌜ Forall (input_pod_ready parent_key parent_uid) pods ⌝ ∗
      "Hown_children_frag" ∷ own_children_frag γ parent_key parent_uid 1 children
  }}}
    @! client.CreateThenDeletePods #state_l #pods_sl
  {{{ RET #interface.nil; True }}}.
Proof. Admitted.

End proof.
