From New.proof.k8s_io.apimachinery.pkg.apis.meta Require Export v1_init.
From New.proof Require Import prelude empty_ffi pure_objects.

Section proof.
Context `{hG: !heapGS Σ} {go_ctx: GoContext}.

Lemma wp_Now:
  {{{ is_pkg_init v1 }}}
    @! v1.Now #()
  {{{ (c: v1.Time.t) v, RET #c;
    TimeV.deepown c v
  }}}.
Proof. Admitted.

Lemma wp_GetName l m :
  {{{ is_pkg_init v1 ∗
      l ↦ m
  }}}
    l @ (ptrT.id v1.ObjectMeta.id) @ "GetName" #()
  {{{ RET #m.(v1.ObjectMeta.Name');
      l ↦ m
  }}}.
Proof. wp_start as "H". wp_auto. iApply "HΦ". iFrame. Qed.

Lemma wp_SetName l m name :
  {{{ is_pkg_init v1 ∗
      l ↦ m
  }}}
    l @ (ptrT.id v1.ObjectMeta.id) @ "SetName" #name
  {{{ RET #();
      l ↦ m <| v1.ObjectMeta.Name' := name |>
  }}}.
Proof. wp_start as "H". wp_auto. iApply "HΦ". iFrame. Qed.

Lemma wp_GetGenerateName l m :
  {{{ is_pkg_init v1 ∗
      l ↦ m
  }}}
    l @ (ptrT.id v1.ObjectMeta.id) @ "GetGenerateName" #()
  {{{ RET #m.(v1.ObjectMeta.GenerateName');
      l ↦ m
  }}}.
Proof. wp_start as "H". wp_auto. iApply "HΦ". iFrame. Qed.

Lemma wp_SetNamespace l m namespace :
  {{{ is_pkg_init v1 ∗
      l ↦ m
  }}}
    l @ (ptrT.id v1.ObjectMeta.id) @ "SetNamespace" #namespace
  {{{ RET #();
      l ↦ m <| v1.ObjectMeta.Namespace' := namespace |>
  }}}.
Proof. wp_start as "H". wp_auto. iApply "HΦ". iFrame. Qed.

Lemma wp_SetCreationTimestamp l m creation_timestamp :
  {{{ is_pkg_init v1 ∗
      l ↦ m
  }}}
    l @ (ptrT.id v1.ObjectMeta.id) @ "SetCreationTimestamp" #creation_timestamp
  {{{ RET #();
      l ↦ m <| v1.ObjectMeta.CreationTimestamp' := creation_timestamp |>
  }}}.
Proof. wp_start as "H". wp_auto. iApply "HΦ". iFrame. Qed.

Lemma wp_GetDeletionTimestamp l m :
  {{{ is_pkg_init v1 ∗
      l ↦ m
  }}}
    l @ (ptrT.id v1.ObjectMeta.id) @ "GetDeletionTimestamp" #()
  {{{ RET #m.(v1.ObjectMeta.DeletionTimestamp');
      l ↦ m
  }}}.
Proof. wp_start as "H". iNamed "H". wp_auto. iApply "HΦ". iFrame. Qed.

Lemma wp_SetDeletionTimestamp l m deletion_timestamp :
  {{{ is_pkg_init v1 ∗
      l ↦ m
  }}}
    l @ (ptrT.id v1.ObjectMeta.id) @ "SetDeletionTimestamp" #deletion_timestamp
  {{{ RET #();
      l ↦ m <| v1.ObjectMeta.DeletionTimestamp' := deletion_timestamp |>
  }}}.
Proof. wp_start as "H". wp_auto. iApply "HΦ". iFrame. Qed.

Lemma wp_SetDeletionGracePeriodSeconds l m deletion_grace_period_seconds :
  {{{ is_pkg_init v1 ∗
      l ↦ m
  }}}
    l @ (ptrT.id v1.ObjectMeta.id) @ "SetDeletionGracePeriodSeconds" #deletion_grace_period_seconds
  {{{ RET #();
      l ↦ m <| v1.ObjectMeta.DeletionGracePeriodSeconds' := deletion_grace_period_seconds |>
  }}}.
Proof. wp_start as "H". wp_auto. iApply "HΦ". iFrame. Qed.

Lemma wp_SetSelfLink l m self_link :
  {{{ is_pkg_init v1 ∗
      l ↦ m
  }}}
    l @ (ptrT.id v1.ObjectMeta.id) @ "SetSelfLink" #self_link
  {{{ RET #();
      l ↦ m <| v1.ObjectMeta.SelfLink' := self_link |>
  }}}.
Proof. wp_start as "H". wp_auto. iApply "HΦ". iFrame. Qed.

Lemma wp_SetResourceVersion l m resource_version :
  {{{ is_pkg_init v1 ∗
      l ↦ m
  }}}
    l @ (ptrT.id v1.ObjectMeta.id) @ "SetResourceVersion" #resource_version
  {{{ RET #();
      l ↦ m <| v1.ObjectMeta.ResourceVersion' := resource_version |>
  }}}.
Proof. wp_start as "H". wp_auto. iApply "HΦ". iFrame. Qed.

Lemma wp_GetFinalizers l m :
  {{{ is_pkg_init v1 ∗
      l ↦ m
  }}}
    l @ (ptrT.id v1.ObjectMeta.id) @ "GetFinalizers" #()
  {{{ RET #m.(v1.ObjectMeta.Finalizers');
      l ↦ m
  }}}.
Proof. wp_start as "H". wp_auto. iApply "HΦ". iFrame. Qed.

Lemma wp_SetUID l m uid :
  {{{ is_pkg_init v1 ∗
      l ↦ m
  }}}
    l @ (ptrT.id v1.ObjectMeta.id) @ "SetUID" #uid
  {{{ RET #();
      l ↦ m <| v1.ObjectMeta.UID' := uid |>
  }}}.
Proof. wp_start as "H". wp_auto. iApply "HΦ". iFrame. Qed.

Definition new_controller_ref_valid controller_ref kind m : Prop :=
  controller_ref.(OwnerReferenceV.Kind') = kind ∧
  controller_ref.(OwnerReferenceV.Name') = m.(ObjectMetaV.Name') ∧
  controller_ref.(OwnerReferenceV.UID') = m.(ObjectMetaV.UID') ∧
  controller_ref.(OwnerReferenceV.BlockOwnerDeletion') = Some true ∧
  controller_ref.(OwnerReferenceV.Controller') = Some true.

Lemma wp_NewControllerRef_replicaset owner gvk rs_l m pure_m dq:
  {{{ is_pkg_init v1 ∗
      ⌜ owner = interface.mk (ptrT.id v1.ReplicaSet.id) (# rs_l) ⌝ ∗
      rs_l ↦s[v1.ReplicaSet :: "ObjectMeta"]{dq} m ∗
      ObjectMetaV.deepown m pure_m dq
  }}}
    @! v1.NewControllerRef #owner #gvk
  {{{ l pure_controller_ref, RET #l;
      OwnerReferenceV.deepown_l l pure_controller_ref 1 ∗
      ⌜ new_controller_ref_valid pure_controller_ref gvk.(schema.GroupVersionKind.Kind') pure_m ⌝ ∗
      rs_l ↦s[v1.ReplicaSet :: "ObjectMeta"]{dq} m ∗
      ObjectMetaV.deepown m pure_m dq
  }}}.
Proof. Admitted.

Definition namespace_matches ns_query ns: Prop :=
  ns_query = v1.NamespaceAll ∨ ns_query = ns.

End proof.
