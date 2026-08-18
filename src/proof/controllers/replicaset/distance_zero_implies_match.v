From New.proof.controllers.replicaset Require Export top_level.

Section proof.
Context `{hG: !heapGS Σ} `{!ffi_semantics _ _}.
Context {sem : go.Semantics}
  {package_sem : code.controllers.replicaset.replicaset.Assumptions}.
Collection W := sem + package_sem.
Context `{!kubernetesModelG Σ}.
Local Set Default Proof Using "All".

Lemma distance_zero_implies_match γ rs pods dqs ready :
  owned_resources γ rs pods dqs ready -∗
  ⌜ match_distance rs pods = 0%nat ↔ current_state_matches rs pods ⌝.
Proof.
  iIntros "_". iPureIntro.
  unfold match_distance, current_state_matches.
  destruct rs.(ReplicaSetV.Spec').(ReplicaSetSpecV.Replicas') as [replicas|]; simpl; lia.
Qed.

End proof.
