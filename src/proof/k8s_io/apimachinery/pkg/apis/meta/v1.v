Require Export New.proof.sync.

From proof.k8s_io.apimachinery.pkg.apis.meta Require Export v1_init.
From proof.k8s_io.api.core Require Export v1_init.
From proof Require Import prelude empty_ffi pure_objects.

Section proof.
Context `{hG: !heapGS Σ} {go_ctx: GoContext}.

Lemma wp_Now:
  {{{ is_pkg_init code.k8s_io.apimachinery.pkg.apis.meta.v1.v1 }}}
    @! v1.Now #()
  {{{ (c: v1.Time.t) v, RET #c;
    PureTime.own c v
  }}}.
Proof.
Admitted.

Lemma wp_GetName (ptr: loc) (meta: v1.ObjectMeta.t):
  {{{ is_pkg_init code.k8s_io.apimachinery.pkg.apis.meta.v1.v1 ∗
      ptr ↦ meta
  }}}
    ptr @ (ptrT.id v1.ObjectMeta.id) @ "GetName" #()
  {{{ RET #meta.(v1.ObjectMeta.Name');
      ptr ↦ meta
  }}}.
Proof.
  wp_start as "H". iNamed "H". wp_auto. iApply "HΦ". iFrame.
Qed.

Lemma wp_GetGenerateName (ptr: loc) (meta: v1.ObjectMeta.t):
  {{{ is_pkg_init code.k8s_io.apimachinery.pkg.apis.meta.v1.v1 ∗
      ptr ↦ meta
  }}}
    ptr @ (ptrT.id v1.ObjectMeta.id) @ "GetGenerateName" #()
  {{{ RET #meta.(v1.ObjectMeta.GenerateName');
      ptr ↦ meta
  }}}.
Proof.
  wp_start as "H". iNamed "H". wp_auto. iApply "HΦ". iFrame.
Qed.

Lemma wp_SetName (ptr: loc) (meta: v1.ObjectMeta.t) (name: go_string):
  {{{ is_pkg_init code.k8s_io.apimachinery.pkg.apis.meta.v1.v1 ∗
      ptr ↦ meta
  }}}
    ptr @ (ptrT.id v1.ObjectMeta.id) @ "SetName" #name
  {{{ RET #();
      ptr ↦ meta <| v1.ObjectMeta.Name' := name |>
  }}}.
Proof.
  wp_start as "H". iNamed "H". wp_auto. iApply "HΦ". iFrame.
Qed.

Lemma wp_SetNamespace (ptr: loc) (meta: v1.ObjectMeta.t) (namespace: go_string):
  {{{ is_pkg_init code.k8s_io.apimachinery.pkg.apis.meta.v1.v1 ∗
      ptr ↦ meta
  }}}
    ptr @ (ptrT.id v1.ObjectMeta.id) @ "SetNamespace" #namespace
  {{{ RET #();
      ptr ↦ meta <| v1.ObjectMeta.Namespace' := namespace |>
  }}}.
Proof.
  wp_start as "H". iNamed "H". wp_auto. iApply "HΦ". iFrame.
Qed.

Lemma wp_GetDeletionTimestamp (ptr: loc) (meta: v1.ObjectMeta.t):
  {{{ is_pkg_init code.k8s_io.apimachinery.pkg.apis.meta.v1.v1 ∗
      ptr ↦ meta
  }}}
    ptr @ (ptrT.id v1.ObjectMeta.id) @ "GetDeletionTimestamp" #()
  {{{ RET #meta.(v1.ObjectMeta.DeletionTimestamp');
      ptr ↦ meta
  }}}.
Proof.
  wp_start as "H". iNamed "H". wp_auto. iApply "HΦ". iFrame.
Qed.

Lemma wp_SetDeletionTimestamp (ptr: loc) (meta: v1.ObjectMeta.t) (deletion_timestamp: loc):
  {{{ is_pkg_init code.k8s_io.apimachinery.pkg.apis.meta.v1.v1 ∗
      ptr ↦ meta
  }}}
    ptr @ (ptrT.id v1.ObjectMeta.id) @ "SetDeletionTimestamp" #deletion_timestamp
  {{{ RET #();
      ptr ↦ meta <| v1.ObjectMeta.DeletionTimestamp' := deletion_timestamp |>
  }}}.
Proof.
  wp_start as "H". iNamed "H". wp_auto. iApply "HΦ". iFrame.
Qed.

Lemma wp_SetResourceVersion (ptr: loc) (meta: v1.ObjectMeta.t) (resource_version: go_string):
  {{{ is_pkg_init code.k8s_io.apimachinery.pkg.apis.meta.v1.v1 ∗
      ptr ↦ meta
  }}}
    ptr @ (ptrT.id v1.ObjectMeta.id) @ "SetResourceVersion" #resource_version
  {{{ RET #();
      ptr ↦ meta <| v1.ObjectMeta.ResourceVersion' := resource_version |>
  }}}.
Proof.
  wp_start as "H". iNamed "H". wp_auto. iApply "HΦ". iFrame.
Qed.

Lemma wp_GetFinalizers (ptr: loc) (meta: v1.ObjectMeta.t):
  {{{ is_pkg_init code.k8s_io.apimachinery.pkg.apis.meta.v1.v1 ∗
      ptr ↦ meta
  }}}
    ptr @ (ptrT.id v1.ObjectMeta.id) @ "GetFinalizers" #()
  {{{ RET #meta.(v1.ObjectMeta.Finalizers');
      ptr ↦ meta
  }}}.
Proof.
  wp_start as "H". iNamed "H". wp_auto. iApply "HΦ". iFrame.
Qed.

Lemma wp_SetUID (ptr: loc) (meta: v1.ObjectMeta.t) (uid: go_string):
  {{{ is_pkg_init code.k8s_io.apimachinery.pkg.apis.meta.v1.v1 ∗
      ptr ↦ meta
  }}}
    ptr @ (ptrT.id v1.ObjectMeta.id) @ "SetUID" #uid
  {{{ RET #();
      ptr ↦ meta <| v1.ObjectMeta.UID' := uid |>
  }}}.
Proof.
  wp_start as "H". iNamed "H". wp_auto. iApply "HΦ". iFrame.
Qed.

End proof.
