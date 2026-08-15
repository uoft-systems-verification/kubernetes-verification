From New.proof.controllers.statefulset Require Export distance.
From New.proof.controllers.statefulset Require Import common.

Section proof.
Context `{hG: !heapGS Σ} `{!ffi_semantics _ _}.
Context {sem : go.Semantics}
  {package_sem : code.controllers.statefulset.statefulset.Assumptions}.
Collection W := sem + package_sem.
Context `{!kubernetesModelG Σ}.
Local Set Default Proof Using "All".

Lemma distance_zero_implies_match γ sts pods pvcs dqs ready :
  statefulset_owned_resources γ sts pods pvcs dqs ready -∗
  ⌜ match_distance sts pods pvcs = 0%nat ↔ current_state_matches sts pods pvcs ⌝.
Proof.
  iIntros "Hresources". iNamed "Hresources".
  iPoseProof (own_pod_frags_living with "Hown_pod_frags") as "%Hpods_living".
  iPureIntro.
  apply match_distance_zero_matches_of_living_nodup; last exact Hpods_nodup.
  intros pod Hpod. rewrite Forall_forall in Hpods_living.
  apply Hpods_living. by rewrite -list_elem_of_In.
Qed.

End proof.
