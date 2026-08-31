From New.proof.k8s_io.apiserver.pkg.registry Require Export rest_init.
From New.proof.k8s_io.apimachinery.pkg.apis.meta Require Export v1_init.
From New.proof Require Import prelude empty_ffi.
From New.proof.kubernetes_types Require Import prelude.

Section proof.
Context `{hG: !heapGS Σ} `{!ffi_semantics _ _}.
Context {sem : go.Semantics}
  {package_sem : rest.Assumptions}
  {meta_v1_sem : code.k8s_io.apimachinery.pkg.apis.meta.v1.v1.Assumptions}.
Local Set Default Proof Using "All".

Lemma wp_WipeObjectMetaSystemFields i l o m :
  {{{ is_pkg_init rest ∗
      ⌜ KObjectV.valid_interface i l o ⌝ ∗
      ObjectMetaV.deepown_l (KObjectV.objectmeta_ptr l o) m 1
  }}}
    @! rest.WipeObjectMetaSystemFields #(interface.ok i)
  {{{ time, RET #();
      ObjectMetaV.deepown_l (KObjectV.objectmeta_ptr l o)
        (m <| ObjectMetaV.CreationTimestamp' := time |>
           <| ObjectMetaV.UID' := ""%go |>
           <| ObjectMetaV.DeletionTimestamp' := None |>
           <| ObjectMetaV.DeletionGracePeriodSeconds' := None |>
           <| ObjectMetaV.SelfLink' := ""%go |>) 1
  }}}.
Proof. Admitted.

Lemma wp_FillObjectMetaSystemFields i l o m :
  {{{ is_pkg_init rest ∗
      ⌜ KObjectV.valid_interface i l o ⌝ ∗
      ObjectMetaV.deepown_l (KObjectV.objectmeta_ptr l o) m 1
  }}}
    @! rest.FillObjectMetaSystemFields #(interface.ok i)
  {{{ time uid, RET #();
      ObjectMetaV.deepown_l (KObjectV.objectmeta_ptr l o)
        (m <| ObjectMetaV.CreationTimestamp' := time |>
           <| ObjectMetaV.UID' := uid |>) 1
  }}}.
Proof. Admitted.

Lemma wp_EnsureObjectNamespaceMatchesRequestNamespace ns i l o m :
  {{{ is_pkg_init rest ∗
      ⌜ KObjectV.valid_interface i l o ⌝ ∗
      ObjectMetaV.deepown_l (KObjectV.objectmeta_ptr l o) m 1 ∗
      ⌜ m.(ObjectMetaV.Namespace') = ""%go ∨ m.(ObjectMetaV.Namespace') = ns ⌝
  }}}
    @! rest.EnsureObjectNamespaceMatchesRequestNamespace #ns #(interface.ok i)
  {{{ RET #interface.nil;
      ObjectMetaV.deepown_l (KObjectV.objectmeta_ptr l o)
        (m <| ObjectMetaV.Namespace' := ns |>) 1
  }}}.
Proof. Admitted.

End proof.
