From New.proof.k8s_io.apimachinery.pkg.apis.meta Require Export v1_init.
From New.proof Require Import prelude empty_ffi pure_objects.

Section proof.
Context `{hG: !heapGS Σ} {go_ctx: GoContext}.

Lemma wp_Now :
  {{{ is_pkg_init v1 }}}
    @! v1.Now #()
  {{{ c v, RET #c;
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

Lemma wp_GetName_deepown l m :
  {{{ is_pkg_init v1 ∗
      ObjectMetaV.deepown_l l m 1
  }}}
    l @ (ptrT.id v1.ObjectMeta.id) @ "GetName" #()
  {{{ RET #m.(ObjectMetaV.Name');
      ObjectMetaV.deepown_l l m 1
  }}}.
Proof.
  iIntros (Φ) "(#Hinit & Hdeepown_l) HΦ".
  iDestruct "Hdeepown_l" as (c) "[Hl Hdeepown]".
  wp_apply (wp_GetName with "[$Hinit $Hl]").
  iIntros "Hl".
  iNamed "Hdeepown".
  rewrite Hdeepown_name.
  iApply "HΦ".
  iExists c.
  iFrame.
  iPureIntro.
  done.
Qed.

Lemma wp_SetName l m name :
  {{{ is_pkg_init v1 ∗
      l ↦ m
  }}}
    l @ (ptrT.id v1.ObjectMeta.id) @ "SetName" #name
  {{{ RET #();
      l ↦ m <| v1.ObjectMeta.Name' := name |>
  }}}.
Proof. wp_start as "H". wp_auto. iApply "HΦ". iFrame. Qed.

Lemma wp_SetName_deepown l m name :
  {{{ is_pkg_init v1 ∗
      ObjectMetaV.deepown_l l m 1
  }}}
    l @ (ptrT.id v1.ObjectMeta.id) @ "SetName" #name
  {{{ RET #();
      ObjectMetaV.deepown_l l (m <| ObjectMetaV.Name' := name |>) 1
  }}}.
Proof.
  iIntros (Φ) "(#Hinit & Hdeepown_l) HΦ".
  iDestruct "Hdeepown_l" as (c) "[Hl Hdeepown]".
  wp_apply (wp_SetName with "[$Hinit $Hl]").
  iIntros "Hl".
  iNamed "Hdeepown".
  iApply "HΦ".
  iExists (c <| v1.ObjectMeta.Name' := name |>).
  iFrame.
  iPureIntro.
  done.
Qed.

Lemma wp_GetGenerateName l m :
  {{{ is_pkg_init v1 ∗
      l ↦ m
  }}}
    l @ (ptrT.id v1.ObjectMeta.id) @ "GetGenerateName" #()
  {{{ RET #m.(v1.ObjectMeta.GenerateName');
      l ↦ m
  }}}.
Proof. wp_start as "H". wp_auto. iApply "HΦ". iFrame. Qed.

Lemma wp_GetGenerateName_deepown l m :
  {{{ is_pkg_init v1 ∗
      ObjectMetaV.deepown_l l m 1
  }}}
    l @ (ptrT.id v1.ObjectMeta.id) @ "GetGenerateName" #()
  {{{ RET #m.(ObjectMetaV.GenerateName');
      ObjectMetaV.deepown_l l m 1
  }}}.
Proof.
  iIntros (Φ) "(#Hinit & Hdeepown_l) HΦ".
  iDestruct "Hdeepown_l" as (c) "[Hl Hdeepown]".
  wp_apply (wp_GetGenerateName with "[$Hinit $Hl]").
  iIntros "Hl".
  iNamed "Hdeepown".
  rewrite Hdeepown_generatename.
  iApply "HΦ".
  iExists c.
  iFrame.
  iPureIntro.
  done.
Qed.

Lemma wp_GetUID l m dq :
  {{{ is_pkg_init v1 ∗
      l ↦{dq} m
  }}}
    l @ (ptrT.id v1.ObjectMeta.id) @ "GetUID" #()
  {{{ RET #m.(v1.ObjectMeta.UID');
      l ↦{dq} m
  }}}.
Proof. wp_start as "H". wp_auto. iApply "HΦ". iFrame. Qed.

Lemma wp_GetUID_deepown l m dq :
  {{{ is_pkg_init v1 ∗
      ObjectMetaV.deepown_l l m dq
  }}}
    l @ (ptrT.id v1.ObjectMeta.id) @ "GetUID" #()
  {{{ RET #m.(ObjectMetaV.UID');
      ObjectMetaV.deepown_l l m dq
  }}}.
Proof.
  iIntros (Φ) "(#Hinit & Hdeepown_l) HΦ".
  iDestruct "Hdeepown_l" as (c) "[Hl Hdeepown]".
  wp_apply (wp_GetUID with "[$Hinit $Hl]").
  iIntros "Hl".
  iNamed "Hdeepown".
  rewrite Hdeepown_uid.
  iApply "HΦ".
  iExists c.
  iFrame.
  iPureIntro.
  done.
Qed.

Lemma wp_GetResourceVersion l m dq :
  {{{ is_pkg_init v1 ∗
      l ↦{dq} m
  }}}
    l @ (ptrT.id v1.ObjectMeta.id) @ "GetResourceVersion" #()
  {{{ RET #m.(v1.ObjectMeta.ResourceVersion');
      l ↦{dq} m
  }}}.
Proof. wp_start as "H". wp_auto. iApply "HΦ". iFrame. Qed.

Lemma wp_GetResourceVersion_deepown l m dq :
  {{{ is_pkg_init v1 ∗
      ObjectMetaV.deepown_l l m dq
  }}}
    l @ (ptrT.id v1.ObjectMeta.id) @ "GetResourceVersion" #()
  {{{ RET #m.(ObjectMetaV.ResourceVersion');
      ObjectMetaV.deepown_l l m dq
  }}}.
Proof.
  iIntros (Φ) "(#Hinit & Hdeepown_l) HΦ".
  iDestruct "Hdeepown_l" as (c) "[Hl Hdeepown]".
  wp_apply (wp_GetResourceVersion with "[$Hinit $Hl]").
  iIntros "Hl".
  iNamed "Hdeepown".
  rewrite Hdeepown_resourceversion.
  iApply "HΦ".
  iExists c.
  iFrame.
  iPureIntro.
  done.
Qed.

Lemma wp_SetNamespace l m namespace :
  {{{ is_pkg_init v1 ∗
      l ↦ m
  }}}
    l @ (ptrT.id v1.ObjectMeta.id) @ "SetNamespace" #namespace
  {{{ RET #();
      l ↦ m <| v1.ObjectMeta.Namespace' := namespace |>
  }}}.
Proof. wp_start as "H". wp_auto. iApply "HΦ". iFrame. Qed.

Lemma wp_SetNamespace_deepown l m namespace :
  {{{ is_pkg_init v1 ∗
      ObjectMetaV.deepown_l l m 1
  }}}
    l @ (ptrT.id v1.ObjectMeta.id) @ "SetNamespace" #namespace
  {{{ RET #();
      ObjectMetaV.deepown_l l (m <| ObjectMetaV.Namespace' := namespace |>) 1
  }}}.
Proof.
  iIntros (Φ) "(#Hinit & Hdeepown_l) HΦ".
  iDestruct "Hdeepown_l" as (c) "[Hl Hdeepown]".
  wp_apply (wp_SetNamespace with "[$Hinit $Hl]").
  iIntros "Hl".
  iNamed "Hdeepown".
  iApply "HΦ".
  iExists (c <| v1.ObjectMeta.Namespace' := namespace |>).
  iFrame.
  iPureIntro.
  done.
Qed.

Lemma wp_SetCreationTimestamp l m creation_timestamp :
  {{{ is_pkg_init v1 ∗
      l ↦ m
  }}}
    l @ (ptrT.id v1.ObjectMeta.id) @ "SetCreationTimestamp" #creation_timestamp
  {{{ RET #();
      l ↦ m <| v1.ObjectMeta.CreationTimestamp' := creation_timestamp |>
  }}}.
Proof. wp_start as "H". wp_auto. iApply "HΦ". iFrame. Qed.

Lemma wp_SetCreationTimestamp_deepown l m creation_timestamp pure_creation_timestamp :
  {{{ is_pkg_init v1 ∗
      ObjectMetaV.deepown_l l m 1 ∗
      TimeV.deepown creation_timestamp pure_creation_timestamp
  }}}
    l @ (ptrT.id v1.ObjectMeta.id) @ "SetCreationTimestamp" #creation_timestamp
  {{{ RET #();
      ObjectMetaV.deepown_l l (m <| ObjectMetaV.CreationTimestamp' := pure_creation_timestamp |>) 1
  }}}.
Proof.
  iIntros (Φ) "(#Hinit & Hdeepown_l & Hdeepown_time) HΦ".
  iDestruct "Hdeepown_l" as (c) "[Hl Hdeepown]".
  wp_apply (wp_SetCreationTimestamp with "[$Hinit $Hl]").
  iIntros "Hl".
  iNamed "Hdeepown".
  iApply "HΦ".
  iExists (c <| v1.ObjectMeta.CreationTimestamp' := creation_timestamp |>).
  iFrame.
  iPureIntro.
  done.
Qed.

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

Lemma wp_SetDeletionTimestamp_deepown l m deletion_timestamp pure_deletion_timestamp :
  {{{ is_pkg_init v1 ∗
      ObjectMetaV.deepown_l l m 1 ∗
      ⌜ deletion_timestamp = null ↔ pure_deletion_timestamp = None ⌝ ∗
      (match pure_deletion_timestamp with
       | Some vd => ∃ cd, deletion_timestamp ↦ cd ∗ TimeV.deepown cd vd
       | None => True
       end)
  }}}
    l @ (ptrT.id v1.ObjectMeta.id) @ "SetDeletionTimestamp" #deletion_timestamp
  {{{ RET #();
      ObjectMetaV.deepown_l l (m <| ObjectMetaV.DeletionTimestamp' := pure_deletion_timestamp |>) 1
  }}}.
Proof.
  iIntros (Φ) "(#Hinit & Hdeepown_l & %Hdeletiontimestamp_none & Hdeletiontimestamp_some) HΦ".
  iDestruct "Hdeepown_l" as (c) "[Hl Hdeepown]".
  wp_apply (wp_SetDeletionTimestamp with "[$Hinit $Hl]").
  iIntros "Hl".
  iNamed "Hdeepown".
  iApply "HΦ".
  iExists (c <| v1.ObjectMeta.DeletionTimestamp' := deletion_timestamp |>).
  iFrame.
  iPureIntro.
  done.
Qed.

Lemma wp_SetDeletionGracePeriodSeconds l m deletion_grace_period_seconds :
  {{{ is_pkg_init v1 ∗
      l ↦ m
  }}}
    l @ (ptrT.id v1.ObjectMeta.id) @ "SetDeletionGracePeriodSeconds" #deletion_grace_period_seconds
  {{{ RET #();
      l ↦ m <| v1.ObjectMeta.DeletionGracePeriodSeconds' := deletion_grace_period_seconds |>
  }}}.
Proof. wp_start as "H". wp_auto. iApply "HΦ". iFrame. Qed.

Lemma wp_SetDeletionGracePeriodSeconds_deepown
    l m deletion_grace_period_seconds pure_deletion_grace_period_seconds :
  {{{ is_pkg_init v1 ∗
      ObjectMetaV.deepown_l l m 1 ∗
      ⌜ deletion_grace_period_seconds = null ↔ pure_deletion_grace_period_seconds = None ⌝ ∗
      (match pure_deletion_grace_period_seconds with
       | Some vd => ∃ cd, deletion_grace_period_seconds ↦ cd ∗ ⌜ cd = vd ⌝
       | None => True
       end)
  }}}
    l @ (ptrT.id v1.ObjectMeta.id) @ "SetDeletionGracePeriodSeconds" #deletion_grace_period_seconds
  {{{ RET #();
      ObjectMetaV.deepown_l l (m <| ObjectMetaV.DeletionGracePeriodSeconds' := pure_deletion_grace_period_seconds |>) 1
  }}}.
Proof.
  iIntros (Φ) "(#Hinit & Hdeepown_l & %Hdeletion_grace_period_seconds_none & Hdeletion_grace_period_seconds_some) HΦ".
  iDestruct "Hdeepown_l" as (c) "[Hl Hdeepown]".
  wp_apply (wp_SetDeletionGracePeriodSeconds with "[$Hinit $Hl]").
  iIntros "Hl".
  iNamed "Hdeepown".
  iApply "HΦ".
  iExists (c <| v1.ObjectMeta.DeletionGracePeriodSeconds' := deletion_grace_period_seconds |>).
  iFrame.
  iPureIntro.
  done.
Qed.

Lemma wp_SetSelfLink l m self_link :
  {{{ is_pkg_init v1 ∗
      l ↦ m
  }}}
    l @ (ptrT.id v1.ObjectMeta.id) @ "SetSelfLink" #self_link
  {{{ RET #();
      l ↦ m <| v1.ObjectMeta.SelfLink' := self_link |>
  }}}.
Proof. wp_start as "H". wp_auto. iApply "HΦ". iFrame. Qed.

Lemma wp_SetSelfLink_deepown l m self_link :
  {{{ is_pkg_init v1 ∗
      ObjectMetaV.deepown_l l m 1
  }}}
    l @ (ptrT.id v1.ObjectMeta.id) @ "SetSelfLink" #self_link
  {{{ RET #();
      ObjectMetaV.deepown_l l (m <| ObjectMetaV.SelfLink' := self_link |>) 1
  }}}.
Proof.
  iIntros (Φ) "(#Hinit & Hdeepown_l) HΦ".
  iDestruct "Hdeepown_l" as (c) "[Hl Hdeepown]".
  wp_apply (wp_SetSelfLink with "[$Hinit $Hl]").
  iIntros "Hl".
  iNamed "Hdeepown".
  iApply "HΦ".
  iExists (c <| v1.ObjectMeta.SelfLink' := self_link |>).
  iFrame.
  iPureIntro.
  done.
Qed.

Lemma wp_SetResourceVersion l m resource_version :
  {{{ is_pkg_init v1 ∗
      l ↦ m
  }}}
    l @ (ptrT.id v1.ObjectMeta.id) @ "SetResourceVersion" #resource_version
  {{{ RET #();
      l ↦ m <| v1.ObjectMeta.ResourceVersion' := resource_version |>
  }}}.
Proof. wp_start as "H". wp_auto. iApply "HΦ". iFrame. Qed.

Lemma wp_SetResourceVersion_deepown l m resource_version :
  {{{ is_pkg_init v1 ∗
      ObjectMetaV.deepown_l l m 1
  }}}
    l @ (ptrT.id v1.ObjectMeta.id) @ "SetResourceVersion" #resource_version
  {{{ RET #();
      ObjectMetaV.deepown_l l (m <| ObjectMetaV.ResourceVersion' := resource_version |>) 1
  }}}.
Proof.
  iIntros (Φ) "(#Hinit & Hdeepown_l) HΦ".
  iDestruct "Hdeepown_l" as (c) "[Hl Hdeepown]".
  wp_apply (wp_SetResourceVersion with "[$Hinit $Hl]").
  iIntros "Hl".
  iNamed "Hdeepown".
  iApply "HΦ".
  iExists (c <| v1.ObjectMeta.ResourceVersion' := resource_version |>).
  iFrame.
  iPureIntro.
  done.
Qed.

Lemma wp_GetFinalizers l m dq :
  {{{ is_pkg_init v1 ∗
      l ↦{dq} m
  }}}
    l @ (ptrT.id v1.ObjectMeta.id) @ "GetFinalizers" #()
  {{{ RET #m.(v1.ObjectMeta.Finalizers');
      l ↦{dq} m
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

Lemma wp_SetUID_deepown l m uid :
  {{{ is_pkg_init v1 ∗
      ObjectMetaV.deepown_l l m 1
  }}}
    l @ (ptrT.id v1.ObjectMeta.id) @ "SetUID" #uid
  {{{ RET #();
      ObjectMetaV.deepown_l l (m <| ObjectMetaV.UID' := uid |>) 1
  }}}.
Proof.
  iIntros (Φ) "(#Hinit & Hdeepown_l) HΦ".
  iDestruct "Hdeepown_l" as (c) "[Hl Hdeepown]".
  wp_apply (wp_SetUID with "[$Hinit $Hl]").
  iIntros "Hl".
  iNamed "Hdeepown".
  iApply "HΦ".
  iExists (c <| v1.ObjectMeta.UID' := uid |>).
  iFrame.
  iPureIntro.
  done.
Qed.

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
