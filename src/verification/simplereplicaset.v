From verification Require Import prelude empty_ffi simpleapiserver.
From verification.kubernetes_model Require Export simplereplicaset_init.

Section proof.
Context `{!mapG Σ KKey.t KObject.t}.
Context `{!mapG Σ KKey.t (gset KKey.t)}.
Context `{!auth_setG Σ KKey.t}.
Context `{hG: !heapGS Σ} {go_ctx: GoContext}.

Lemma wp_syncReplicaSet (namespace name: go_string) γ_state γ_children γ_fresh_keys rs_key rs s (n: w32):
  {{{ is_pkg_init simplereplicaset ∗
      is_kubernetes_state γ_state γ_children γ_fresh_keys ∗
      ⌜ rs_key = mk_replicaset_key namespace name ⌝ ∗
      rs_key [[ γ_state ]]↦ KObject.ReplicaSet rs ∗
      rs_key [[ γ_children ]]↦ s ∗
      rs.(v1.ReplicaSet.Spec').(v1.ReplicaSetSpec.Replicas') ↦ n
  }}}
  @! simplereplicaset.syncReplicaSet #namespace #name
  {{{ (err : error.t) s', RET #err;
      rs_key [[ γ_children ]]↦ s' ∗
      if decide (err = interface.nil) then
        ⌜ size s' = sint.nat n ⌝
      else
        ⌜ Z.abs (Z.of_nat (size s') - sint.Z n) <
          Z.abs (Z.of_nat (size s) - sint.Z n) ⌝
  }}}.
Proof. Admitted.


End proof.