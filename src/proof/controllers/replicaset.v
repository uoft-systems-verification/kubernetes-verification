From New.proof Require Import prelude empty_ffi.
From New.proof.kubernetes_model Require Export get index create delete.
From New.proof Require Export util.
From New.proof.controllers Require Export replicaset_init.
From New.proof.k8s_io.kubernetes.pkg Require Export controller.
From New.proof.k8s_io.apimachinery.pkg.runtime Require Export schema.
From New.proof.k8s_io.apimachinery.pkg.api Require Export errors.

Section proof.
Context `{hG: !heapGS Σ} {go_ctx: GoContext}.
Context `{!kviewG Σ}.
Context `{!cviewG Σ}.
Context `{!mono_gsetG types.UID.t Σ}.

Definition is_pod_active (pod: PodV.t): Prop :=
  pod.(PodV.ObjectMeta').(ObjectMetaV.DeletionTimestamp') = None.

Definition mk_pod_key (namespace name: go_string) : KKey.t :=
  {| KKey.Kind' := "Pod"%go; KKey.Namespace' := namespace; KKey.Name' := name;|}.

Definition mk_replicaset_key (namespace name: go_string) : KKey.t :=
  {| KKey.Kind' := "ReplicaSet"%go; KKey.Namespace' := namespace; KKey.Name' := name;|}.

Lemma wp_syncReplicaSet γ l (gv: schema.GroupVersion.t) namespace name uid rs meta_map n:
  {{{ is_pkg_init replicaset ∗
      "#Hisk" ∷ is_kubernetes γ l ∗
      "#Hglobal_l" ∷ (global_addr replicaset.state) ↦□ l ∗
      "#Hglobal_gv" ∷ (global_addr v1.SchemeGroupVersion) ↦□ gv ∗
      "Hown_rs_meta_frag" ∷ own_meta_frag γ (mk_replicaset_key namespace name) uid 1 rs.(ReplicaSetV.ObjectMeta') ∗
      "Hown_pod_meta_frags" ∷ ([∗ map] k ↦ meta ∈ meta_map, own_meta_frag γ k meta.(ObjectMetaV.UID') 1 meta) ∗
      "Hown_children_frag" ∷ own_children_frag γ (mk_replicaset_key namespace name) uid 1 (dom meta_map) ∗
      "%Hpod_meta" ∷ ⌜ set_Forall (λ key, key.(KKey.Kind') = "Pod"%go) (dom meta_map) ⌝ ∗
      "%Hrs_name_short" ∷ ⌜ length rs.(ReplicaSetV.ObjectMeta').(ObjectMetaV.Name') < 58 ⌝ ∗
      "%Hdeletion_timestamp_eq" ∷ ⌜ rs.(ReplicaSetV.ObjectMeta').(ObjectMetaV.DeletionTimestamp') = None ⌝ ∗
      "%Hreplicas_eq" ∷ ⌜ rs.(ReplicaSetV.Spec').(ReplicaSetSpecV.Replicas') = Some n ⌝
  }}}
  @! replicaset.syncReplicaSet #namespace #name
  {{{ meta_map', RET #interface.nil;
      ⌜ size (filter (λ kv, kv.2.(ObjectMetaV.DeletionTimestamp') = None) meta_map') = sint.nat n ⌝ ∗
      own_meta_frag γ (mk_replicaset_key namespace name) uid 1 rs.(ReplicaSetV.ObjectMeta') ∗
      ([∗ map] k ↦ meta ∈ meta_map', own_meta_frag γ k meta.(ObjectMetaV.UID') 1 meta) ∗
      own_children_frag γ (mk_replicaset_key namespace name) uid 1 (dom meta_map')
  }}}.
Proof. Admitted.

End proof.
