From New.proof.controllers.statefulset Require Export top_level.

Section proof.
Context `{hG: !heapGS Σ} `{!kubernetesModelG Σ}.
Local Set Default Proof Using "All".

Lemma own_occupied_pods_as_identities γ pods :
  own_occupied_pods γ pods ⊣⊢
    [∗ list] identity ∈ pod_reservation_identity <$> pods,
      own_occupied_pod_identity γ identity.
Proof.
  rewrite big_sepL_fmap /own_occupied_pods /own_occupied_pod_identity.
  done.
Qed.

Lemma own_pod_frags_living γ dq pods :
  ([∗ list] pod ∈ pods,
    own_meta_frag γ (PodV.key pod)
      pod.(PodV.ObjectMeta').(ObjectMetaV.UID') dq
      pod.(PodV.ObjectMeta') ∗
    own_spec_frag γ (PodV.key pod)
      pod.(PodV.ObjectMeta').(ObjectMetaV.UID') dq
      (ObjectSpecV.PodSpec pod.(PodV.Spec'))) -∗
  ⌜ Forall is_pod_alive pods ⌝.
Proof.
  iIntros "Hpods". iInduction pods as [|pod pods] "IH".
  { iPureIntro. constructor. }
  rewrite big_sepL_cons. iDestruct "Hpods" as "[(Hmeta & _) Hpods]".
  iPoseProof (kview.own_meta_valid with "Hmeta") as "%Hmeta".
  iPoseProof ("IH" with "Hpods") as "%Hpods".
  iPureIntro. constructor; last exact Hpods.
  unfold is_pod_alive. destruct Hmeta as (_ & _ & _ & _ & Hliving).
  exact Hliving.
Qed.

End proof.
