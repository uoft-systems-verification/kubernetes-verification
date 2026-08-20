From New.proof.controllers.statefulset Require Export top_level.

Definition phase_after_deletion phase
    (deletion : option (KKey.t * types.UID.t)) :=
  match deletion with
  | None => phase
  | Some _ => Mutable
  end.

Section proof.
Context `{hG: !heapGS Σ} `{!kubernetesModelG Σ}.
Local Set Default Proof Using "All".

Definition own_started_deletion γ
    (deletion : option (KKey.t * types.UID.t)) : iProp Σ :=
  match deletion with
  | None => emp
  | Some (key, uid) => own_deleting_reserved_frag γ 1 key uid
  end.

Lemma own_occupied_pods_as_identities γ dq pods :
  ([∗ list] pod ∈ pods,
    own_occupied_reserved_frag γ dq (PodV.key pod)
      pod.(PodV.ObjectMeta').(ObjectMetaV.UID')) ⊣⊢
    [∗ list] identity ∈ pod_reservation_identity <$> pods,
      own_occupied_reserved_frag γ dq identity.1 identity.2.
Proof.
  rewrite big_sepL_fmap. done.
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
