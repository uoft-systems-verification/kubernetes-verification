From New.proof Require Import prelude empty_ffi.
From New.proof.simple Require Export apimodel.
From New.proof Require Export external_wp.

Section proof.
Context `{hG: !heapGS Σ} {go_ctx: GoContext}.
Context `{!mapG Σ KKey.t interface.t}.
Context `{!mapG Σ KKey.t KObjectV.t}.
Context `{!mapG Σ KKey.t (gset KKey.t)}.
Context `{!auth_setG Σ KKey.t}.

Lemma wp_State__objDelete γ l key
  pure_kobj parent_key children_keys owned_grandchild_keys:
  {{{ is_pkg_init apimodel ∗
      "#Hisk" ∷ is_kubernetes γ l ∗
      "%Hkind_eq" ∷ ⌜ KKey.Kind' key = KObjectV.kind pure_kobj ⌝ ∗
      "%His_child" ∷ ⌜ key ∈ children_keys ⌝ ∗
      "Hghost_pure_kobj" ∷ key [[ γ.(γ_state) ]]↦ pure_kobj ∗
      "Hghost_children_keys" ∷ parent_key [[ γ.(γ_children) ]]↦ children_keys ∗
      "Hghost_grandchildren_keys" ∷ key [[ γ.(γ_children) ]]↦ owned_grandchild_keys
  }}}
    l @ (ptrT.id apimodel.State.id) @ "objDelete" #key
  {{{ (pure_kobj': KObjectV.t), RET #interface.nil;
      (("%Hsame_cons" ∷ ⌜ KObjectV.same_kind pure_kobj pure_kobj' ⌝ ∗
        "%Hts" ∷ ⌜ (KObjectV.objectmeta pure_kobj').(ObjectMetaV.DeletionTimestamp') ≠ None ⌝ ∗
        "Hghost_pure_kobj" ∷ key [[ γ.(γ_state) ]]↦ pure_kobj' ∗
        "Hghost_children_keys" ∷ parent_key [[ γ.(γ_children) ]]↦ children_keys ∗
        "Hghost_grandchildren_keys" ∷ key [[ γ.(γ_children) ]]↦ owned_grandchild_keys
      ) ∨
      parent_key [[ γ.(γ_children) ]]↦ (children_keys ∖ {[key]}))
  }}}.
Proof. Admitted.

Lemma wp_State__PodDelete γ l namespace name
  key pure_pod parent_key children_keys owned_grandchild_keys:
  {{{ is_pkg_init apimodel ∗
      "#inv" ∷ is_kubernetes γ l ∗
      "%Hkey_eq" ∷ ⌜ key = mk_pod_key namespace name ⌝ ∗
      "Hghost_pure_pod" ∷ key [[ γ.(γ_state) ]]↦ (KObjectV.Pod pure_pod) ∗
      "Hghost_children_keys" ∷ parent_key [[ γ.(γ_children) ]]↦ children_keys ∗
      "Hghost_grandchildren_keys" ∷ key [[ γ.(γ_children) ]]↦ owned_grandchild_keys ∗
      "%His_child" ∷ ⌜ key ∈ children_keys ⌝
  }}}
    l @ (ptrT.id apimodel.State.id) @ "PodDelete" #namespace #name
  {{{ pure_pod', RET #interface.nil;
      (("%Hts" ∷ ⌜ pure_pod'.(PodV.ObjectMeta').(ObjectMetaV.DeletionTimestamp') ≠ None ⌝ ∗
        "Hghost_pure_pod" ∷ key [[ γ.(γ_state) ]]↦ (KObjectV.Pod pure_pod') ∗
        "Hghost_children_keys" ∷ parent_key [[ γ.(γ_children) ]]↦ children_keys ∗
        "Hghost_grandchildren_keys" ∷ key [[ γ.(γ_children) ]]↦ owned_grandchild_keys
      ) ∨
      parent_key [[ γ.(γ_children) ]]↦ (children_keys ∖ {[key]}))
  }}}.
Proof. Admitted.

End proof.
