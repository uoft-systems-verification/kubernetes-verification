From verification Require Import prelude empty_ffi simpleapiserver.
From verification.kubernetes_model Require Export simplereplicaset_init.

Section proof.
Context `{!mapG Σ KKey.t KObject.t}.
Context `{!mapG Σ KKey.t (gset KKey.t)}.
Context `{!auth_setG Σ KKey.t}.
Context `{hG: !heapGS Σ} {go_ctx: GoContext}.

Definition active_pod (pod: v1.Pod.t) : bool :=
  true.

Definition active_child_count (child_pods: gmap KKey.t v1.Pod.t) : nat :=
  length (filter (λ kv, active_pod (snd kv)) (map_to_list child_pods)).

Lemma wp_syncReplicaSet namespace name
  γ_state γ_children γ_fresh_keys rs_key rs child_keys child_pods (n: w32):
  {{{ is_pkg_init simplereplicaset ∗
      is_kubernetes_state γ_state γ_children γ_fresh_keys ∗
      ⌜ rs_key = mk_replicaset_key namespace name ⌝ ∗
      rs_key [[ γ_state ]]↦ KObject.ReplicaSet rs ∗
      ([∗ map] key ↦ v ∈ child_pods,
        key [[ γ_state ]]↦ KObject.Pod v ∗
        ⌜ key ∈ child_keys ⌝) ∗
      rs_key [[ γ_children ]]↦ child_keys ∗
      ⌜ size child_pods = size child_keys ⌝ ∗
      rs.(v1.ReplicaSet.Spec').(v1.ReplicaSetSpec.Replicas') ↦ n
  }}}
  @! simplereplicaset.syncReplicaSet #namespace #name
  {{{ (err : error.t) child_keys' child_pods', RET #err;
      rs_key [[ γ_state ]]↦ KObject.ReplicaSet rs ∗
      ([∗ map] key ↦ v ∈ child_pods',
        key [[ γ_state ]]↦ KObject.Pod v ∗
        ⌜ key ∈ child_keys' ⌝) ∗
      rs_key [[ γ_children ]]↦ child_keys' ∗
      ⌜ size child_pods' = size child_keys' ⌝ ∗
      if decide (err = interface.nil) then
        ⌜ size child_keys' = sint.nat n ⌝
      else
        ⌜ Z.abs (Z.of_nat (active_child_count child_pods) - sint.Z n) <
          Z.abs (Z.of_nat (active_child_count child_pods') - sint.Z n) ⌝
  }}}.
Proof. Admitted.


End proof.