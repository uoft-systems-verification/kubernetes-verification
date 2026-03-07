From New.proof.k8s_io.apiserver.pkg.registry Require Export rest_init.
From New.proof.k8s_io.apimachinery.pkg.apis.meta Require Export v1_init.
From New.proof Require Import prelude empty_ffi pure_objects.

Section proof.
Context `{hG: !heapGS Σ} {go_ctx: GoContext}.

Lemma wp_WipeObjectMetaSystemFields l m :
  {{{ is_pkg_init rest ∗
      l ↦ m
  }}}
    @! rest.WipeObjectMetaSystemFields #l
  {{{ time, RET #();
      l ↦ m <| v1.ObjectMeta.CreationTimestamp' := time |>
            <| v1.ObjectMeta.UID' := ""%go |>
            <| v1.ObjectMeta.DeletionTimestamp' := null |>
            <| v1.ObjectMeta.DeletionGracePeriodSeconds' := null |>
            <| v1.ObjectMeta.SelfLink' := ""%go |>
  }}}.
Proof. Admitted.

Lemma wp_FillObjectMetaSystemFields l m :
  {{{ is_pkg_init rest ∗
      l ↦ m
  }}}
    @! rest.FillObjectMetaSystemFields #l
  {{{ time timev uid, RET #();
      l ↦ m <| v1.ObjectMeta.CreationTimestamp' := time |>
            <| v1.ObjectMeta.UID' := uid |> ∗
      TimeV.deepown time timev
  }}}.
Proof. Admitted.

Lemma wp_EnsureObjectNamespaceMatchesRequestNamespace ns l m :
  {{{ is_pkg_init rest ∗
      l ↦ m ∗
      ⌜ m.(v1.ObjectMeta.Namespace') = ""%go ∨ m.(v1.ObjectMeta.Namespace') = ns ⌝
  }}}
    @! rest.EnsureObjectNamespaceMatchesRequestNamespace #ns #l
  {{{ RET #interface.nil;
      l ↦ m <| v1.ObjectMeta.Namespace' := ns |>
  }}}.
Proof. Admitted.

End proof.