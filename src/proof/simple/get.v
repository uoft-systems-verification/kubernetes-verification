From New.proof Require Import prelude empty_ffi.
From New.proof.simple Require Export apimodel.

Section proof.
Context `{hG: !heapGS Σ} {go_ctx: GoContext}.
Context `{!mapG Σ KKey.t interface.t}.
Context `{!mapG Σ KKey.t KObjectV.t}.
Context `{!mapG Σ KKey.t (gset KKey.t)}.
Context `{!auth_setG Σ KKey.t}.

Lemma wp_State__objGet γ l key pure_kobj:
  {{{ is_pkg_init apimodel ∗
      "#Hisk" ∷ is_kubernetes γ l ∗
      "Hghost" ∷ key [[ γ.(γ_state) ]]↦ pure_kobj
  }}}
    l @ (ptrT.id apimodel.State.id) @ "objGet" #key
  {{{ obj ptr, RET (#obj, #true);
      ⌜ KObjectV.valid_interface obj ptr pure_kobj ⌝ ∗
      KObjectV.deepown_l ptr pure_kobj 1 ∗
      ⌜ KObjectV.valid_old pure_kobj ⌝ ∗
      ⌜ key.(KKey.Namespace') = (KObjectV.objectmeta pure_kobj).(ObjectMetaV.Namespace') ⌝ ∗
      ⌜ key.(KKey.Name') = (KObjectV.objectmeta pure_kobj).(ObjectMetaV.Name') ⌝ ∗
      key [[ γ.(γ_state) ]]↦ pure_kobj
  }}}.
Proof. Admitted.

Lemma wp_State__ReplicaSetMutGet γ l key namespace name pure_rs:
  {{{ is_pkg_init apimodel ∗
      "#Hisk" ∷ is_kubernetes γ l ∗
      "%Hkey_eq" ∷ ⌜ key = (mk_replicaset_key namespace name) ⌝ ∗
      "Hghost" ∷ key [[ γ.(γ_state) ]]↦ (KObjectV.ReplicaSet pure_rs)
  }}}
    l @ (ptrT.id apimodel.State.id) @ "ReplicaSetMutGet" #namespace #name
  {{{ ptr rs, RET (#ptr, #interface.nil);
      ptr ↦ rs ∗ ReplicaSetV.deepown rs pure_rs 1 ∗
      ⌜ ReplicaSetV.valid pure_rs ⌝ ∗
      ⌜ namespace = pure_rs.(ReplicaSetV.ObjectMeta').(ObjectMetaV.Namespace') ⌝ ∗
      ⌜ name = pure_rs.(ReplicaSetV.ObjectMeta').(ObjectMetaV.Name') ⌝ ∗
      (mk_replicaset_key namespace name) [[ γ.(γ_state) ]]↦ (KObjectV.ReplicaSet pure_rs)
  }}}.
Proof. Admitted.

Lemma wp_State__ReplicaSetGet γ l key namespace name pure_rs:
  {{{ is_pkg_init apimodel ∗
      "#Hisk" ∷ is_kubernetes γ l ∗
      "%Hkey_eq" ∷ ⌜ key = (mk_replicaset_key namespace name) ⌝ ∗
      "Hghost" ∷ key [[ γ.(γ_state) ]]↦ (KObjectV.ReplicaSet pure_rs)
  }}}
    l @ (ptrT.id apimodel.State.id) @ "ReplicaSetGet" #namespace #name
  {{{ ptr rs dq, RET (#ptr, #interface.nil);
      ptr ↦{dq} rs ∗ ReplicaSetV.deepown rs pure_rs dq ∗
      ⌜ ReplicaSetV.valid pure_rs ⌝ ∗
      ⌜ namespace = pure_rs.(ReplicaSetV.ObjectMeta').(ObjectMetaV.Namespace') ⌝ ∗
      ⌜ name = pure_rs.(ReplicaSetV.ObjectMeta').(ObjectMetaV.Name') ⌝ ∗
      (mk_replicaset_key namespace name) [[ γ.(γ_state) ]]↦ (KObjectV.ReplicaSet pure_rs)
  }}}.
Proof. Admitted.

End proof.
