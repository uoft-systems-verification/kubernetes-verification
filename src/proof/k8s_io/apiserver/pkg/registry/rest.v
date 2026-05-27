From New.proof.k8s_io.apiserver.pkg.registry Require Export rest_init.
From New.proof.k8s_io.apimachinery.pkg.apis.meta Require Export v1_init.
From New.proof Require Import prelude empty_ffi pure_objects.

Section proof.
Context `{hG: !heapGS Σ} `{!ffi_semantics _ _}.
Context {sem : go.Semantics}
  {package_sem : rest.Assumptions}
  {meta_v1_sem : code.k8s_io.apimachinery.pkg.apis.meta.v1.v1.Assumptions}.
Local Set Default Proof Using "All".

Lemma wp_WipeObjectMetaSystemFields i l m :
  {{{ is_pkg_init rest ∗
      ⌜ i = interface.mk (go.PointerType v1.ObjectMeta) #l ⌝ ∗
      ObjectMetaV.deepown_l l m 1
  }}}
    @! rest.WipeObjectMetaSystemFields #(interface.ok i)
  {{{ time, RET #();
      ObjectMetaV.deepown_l l (m <| ObjectMetaV.CreationTimestamp' := time |>
                                <| ObjectMetaV.UID' := ""%go |>
                                <| ObjectMetaV.DeletionTimestamp' := None |>
                                <| ObjectMetaV.DeletionGracePeriodSeconds' := None |>
                                <| ObjectMetaV.SelfLink' := ""%go |>) 1
  }}}.
Proof. Admitted.

Lemma wp_FillObjectMetaSystemFields i l m :
  {{{ is_pkg_init rest ∗
      ⌜ i = interface.mk (go.PointerType v1.ObjectMeta) #l ⌝ ∗
      ObjectMetaV.deepown_l l m 1
  }}}
    @! rest.FillObjectMetaSystemFields #(interface.ok i)
  {{{ time uid, RET #();
      ObjectMetaV.deepown_l l (m <| ObjectMetaV.CreationTimestamp' := time |>
                                 <| ObjectMetaV.UID' := uid |>) 1
  }}}.
Proof. Admitted.

Lemma wp_EnsureObjectNamespaceMatchesRequestNamespace ns i l m :
  {{{ is_pkg_init rest ∗
      ⌜ i = interface.mk (go.PointerType v1.ObjectMeta) #l ⌝ ∗
      ObjectMetaV.deepown_l l m 1 ∗
      ⌜ m.(ObjectMetaV.Namespace') = ""%go ∨ m.(ObjectMetaV.Namespace') = ns ⌝
  }}}
    @! rest.EnsureObjectNamespaceMatchesRequestNamespace #ns #(interface.ok i)
  {{{ RET #interface.nil;
      ObjectMetaV.deepown_l l (m <| ObjectMetaV.Namespace' := ns |>) 1
  }}}.
Proof. Admitted.

End proof.
