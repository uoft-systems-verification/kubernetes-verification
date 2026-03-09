From New.proof.k8s_io.apiserver.pkg.registry Require Export rest_init.
From New.proof.k8s_io.apimachinery.pkg.apis.meta Require Export v1_init.
From New.proof Require Import prelude empty_ffi pure_objects.

Section proof.
Context `{hG: !heapGS Σ} {go_ctx: GoContext}.

Lemma wp_WipeObjectMetaSystemFields i l m :
  {{{ is_pkg_init rest ∗
      ⌜ i = interface.mk (ptrT.id v1.ObjectMeta.id) #l ⌝ ∗
      ObjectMetaV.deepown_l l m 1
  }}}
    @! rest.WipeObjectMetaSystemFields #i
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
      ⌜ i = interface.mk (ptrT.id v1.ObjectMeta.id) #l ⌝ ∗
      ObjectMetaV.deepown_l l m 1
  }}}
    @! rest.FillObjectMetaSystemFields #i
  {{{ time uid, RET #();
      ObjectMetaV.deepown_l l (m <| ObjectMetaV.CreationTimestamp' := time |>
                                 <| ObjectMetaV.UID' := uid |>) 1
  }}}.
Proof. Admitted.

Lemma wp_EnsureObjectNamespaceMatchesRequestNamespace ns i l m :
  {{{ is_pkg_init rest ∗
      ⌜ i = interface.mk (ptrT.id v1.ObjectMeta.id) #l ⌝ ∗
      ObjectMetaV.deepown_l l m 1 ∗
      ⌜ m.(ObjectMetaV.Namespace') = ""%go ∨ m.(ObjectMetaV.Namespace') = ns ⌝
  }}}
    @! rest.EnsureObjectNamespaceMatchesRequestNamespace #ns #i
  {{{ RET #interface.nil;
      ObjectMetaV.deepown_l l (m <| ObjectMetaV.Namespace' := ns |>) 1
  }}}.
Proof. Admitted.

End proof.
