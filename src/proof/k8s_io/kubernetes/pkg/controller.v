From New.proof Require Import prelude empty_ffi.
From New.proof Require Export pure_objects.
From New.proof.k8s_io.kubernetes.pkg Require Export controller_init.


Section proof.
Context `{hG: !heapGS Σ} {go_ctx: GoContext}.

Lemma wp_PodControllerIndexKey namespace ownerReference owner_reference dq:
  {{{ is_pkg_init controller ∗
      ownerReference ↦{dq} owner_reference
  }}}
  @! controller.PodControllerIndexKey #namespace #ownerReference
  {{{ index_key, RET #index_key;
      ⌜ index_key =  namespace ++ "/"%go ++ 
        owner_reference.(v1.OwnerReference.Kind') ++ "/"%go ++ 
        owner_reference.(v1.OwnerReference.Name') ++ "/"%go ++
        owner_reference.(v1.OwnerReference.UID')⌝
  }}}.
Proof.
Admitted.

End proof.
