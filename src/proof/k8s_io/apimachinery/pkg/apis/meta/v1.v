Require Export New.proof.sync.

From proof.k8s_io.apimachinery.pkg.apis.meta Require Export v1_init.
From proof.k8s_io.api.core Require Export v1_init.
From proof Require Import prelude empty_ffi.

Section proof.
Context `{hG: !heapGS Σ} {go_ctx: GoContext}.

Lemma wp_Now:
  {{{ is_pkg_init code.k8s_io.apimachinery.pkg.apis.meta.v1.v1 }}}
    @! v1.Now #()
  {{{ (v: v1.Time.t), RET #v;
    True
  }}}.
Proof.
Admitted.

Lemma wp_GetDeletionTimestamp (ptr: loc) (meta: v1.ObjectMeta.t):
  {{{ is_pkg_init code.k8s_io.apimachinery.pkg.apis.meta.v1.v1 ∗
      "ptr" ∷ ptr ↦ meta
  }}}
    ptr @ (ptrT.id v1.ObjectMeta.id) @ "GetDeletionTimestamp" #()
  {{{ (deletion_timestamp: loc), RET #deletion_timestamp;
      ⌜ deletion_timestamp = meta.(v1.ObjectMeta.DeletionTimestamp') ⌝ ∗
      ptr ↦ meta
  }}}.
Proof.
  wp_start as "H". iNamed "H". wp_auto. iApply "HΦ". iFrame. done.
Qed.

Lemma wp_SetDeletionTimestamp (ptr: loc) (meta: v1.ObjectMeta.t) (deletion_timestamp: loc):
  {{{ is_pkg_init code.k8s_io.apimachinery.pkg.apis.meta.v1.v1 ∗
      "ptr" ∷ ptr ↦ meta
  }}}
    ptr @ (ptrT.id v1.ObjectMeta.id) @ "SetDeletionTimestamp" #deletion_timestamp
  {{{ (meta': v1.ObjectMeta.t), RET #();
      ⌜ meta' = meta <| v1.ObjectMeta.DeletionTimestamp' := deletion_timestamp |> ⌝ ∗
      ptr ↦ meta'
  }}}.
Proof.
  wp_start as "H". iNamed "H". wp_auto. iApply "HΦ". iFrame. done.
Qed.

Lemma wp_SetResourceVersion (ptr: loc) (meta: v1.ObjectMeta.t) (resource_version: go_string):
  {{{ is_pkg_init code.k8s_io.apimachinery.pkg.apis.meta.v1.v1 ∗
      "ptr" ∷ ptr ↦ meta
  }}}
    ptr @ (ptrT.id v1.ObjectMeta.id) @ "SetResourceVersion" #resource_version
  {{{ (meta': v1.ObjectMeta.t), RET #();
      ⌜ meta' = meta <| v1.ObjectMeta.ResourceVersion' := resource_version |> ⌝ ∗
      ptr ↦ meta'
  }}}.
Proof.
  wp_start as "H". iNamed "H". wp_auto. iApply "HΦ". iFrame. done.
Qed.

Lemma wp_GetFinalizers (ptr: loc) (meta: v1.ObjectMeta.t):
  {{{ is_pkg_init code.k8s_io.apimachinery.pkg.apis.meta.v1.v1 ∗
      "ptr" ∷ ptr ↦ meta
  }}}
    ptr @ (ptrT.id v1.ObjectMeta.id) @ "GetFinalizers" #()
  {{{ (finalizers: slice.t), RET #finalizers;
      ⌜ finalizers = meta.(v1.ObjectMeta.Finalizers') ⌝ ∗
      ptr ↦ meta
  }}}.
Proof.
  wp_start as "H". iNamed "H". wp_auto. iApply "HΦ". iFrame. done.
Qed.

End proof.
