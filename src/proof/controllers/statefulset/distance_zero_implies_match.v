From New.proof.controllers.statefulset Require Export common.

Section proof.
Context `{hG: !heapGS Σ} `{!ffi_semantics _ _}.
Context {sem : go.Semantics}
  {package_sem : code.controllers.statefulset.statefulset.Assumptions}.
Collection W := sem + package_sem.
Context `{!kubernetesModelG Σ}.
Local Set Default Proof Using "All".

Lemma distance_zero_implies_match γ sts revision_name state spec_dq dq ready :
  owned_resources γ sts state spec_dq dq ready -∗
  ⌜ match_distance sts revision_name state = 0%nat ↔ current_state_matches sts revision_name state ⌝.
Proof.
  iIntros "(_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & %Hwf)".
  destruct Hwf as [[_ [Hnodup _]] _].
  iPureIntro. by apply match_distance_zero_matches_of_nodup.
Qed.

End proof.
