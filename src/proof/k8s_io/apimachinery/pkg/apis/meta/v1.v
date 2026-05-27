From New.proof.k8s_io.apimachinery.pkg.apis.meta Require Export v1_init.
From New.proof Require Import prelude empty_ffi pure_objects.

Section proof.
Context `{hG: !heapGS Σ}.
Context `{!ffi_semantics _ _}.
Context {sem : go.Semantics} {package_sem : v1.Assumptions}.
Local Set Default Proof Using "All".

Lemma wp_Now :
  {{{ is_pkg_init v1 }}}
    @! v1.Now #()
  {{{ c v, RET #c;
    TimeV.deepown c v
  }}}.
Proof. Admitted.

Lemma wp_GetName l m dq :
  {{{ is_pkg_init v1 ∗
      l ↦{dq} m
  }}}
    l @! (go.PointerType v1.ObjectMeta) @! "GetName" #()
  {{{ RET #m.(v1.ObjectMeta.Name');
      l ↦{dq} m
  }}}.
Proof. wp_start as "H". wp_auto. iApply "HΦ". iFrame. Qed.

Lemma wp_GetName_deepown l m dq:
  {{{ is_pkg_init v1 ∗
      ObjectMetaV.deepown_l l m dq
  }}}
    l @! (go.PointerType v1.ObjectMeta) @! "GetName" #()
  {{{ RET #m.(ObjectMetaV.Name');
      ObjectMetaV.deepown_l l m dq
  }}}.
Proof.
  iIntros (Φ) "(#Hinit & Hdeepown_l) HΦ".
  iDestruct "Hdeepown_l" as (c) "[Hl Hdeepown]".
  wp_apply (wp_GetName with "[$Hl]").
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
    l @! (go.PointerType v1.ObjectMeta) @! "SetName" #name
  {{{ RET #();
      l ↦ m <| v1.ObjectMeta.Name' := name |>
  }}}.
Proof. wp_start as "H". wp_auto. iApply "HΦ". iFrame. Qed.

Lemma wp_SetName_deepown l m name :
  {{{ is_pkg_init v1 ∗
      ObjectMetaV.deepown_l l m 1
  }}}
    l @! (go.PointerType v1.ObjectMeta) @! "SetName" #name
  {{{ RET #();
      ObjectMetaV.deepown_l l (m <| ObjectMetaV.Name' := name |>) 1
  }}}.
Proof.
  iIntros (Φ) "(#Hinit & Hdeepown_l) HΦ".
  iDestruct "Hdeepown_l" as (c) "[Hl Hdeepown]".
  wp_apply (wp_SetName with "[$Hl]").
  iIntros "Hl".
  iNamed "Hdeepown".
  iApply "HΦ".
  iExists (c <| v1.ObjectMeta.Name' := name |>).
  iFrame.
  iPureIntro.
  done.
Qed.

Lemma wp_GetGenerateName l m dq :
  {{{ is_pkg_init v1 ∗
      l ↦{dq} m
  }}}
    l @! (go.PointerType v1.ObjectMeta) @! "GetGenerateName" #()
  {{{ RET #m.(v1.ObjectMeta.GenerateName');
      l ↦{dq} m
  }}}.
Proof. wp_start as "H". wp_auto. iApply "HΦ". iFrame. Qed.

Lemma wp_GetGenerateName_deepown l m dq :
  {{{ is_pkg_init v1 ∗
      ObjectMetaV.deepown_l l m dq
  }}}
    l @! (go.PointerType v1.ObjectMeta) @! "GetGenerateName" #()
  {{{ RET #m.(ObjectMetaV.GenerateName');
      ObjectMetaV.deepown_l l m dq
  }}}.
Proof.
  iIntros (Φ) "(#Hinit & Hdeepown_l) HΦ".
  iDestruct "Hdeepown_l" as (c) "[Hl Hdeepown]".
  wp_apply (wp_GetGenerateName with "[$Hl]").
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
    l @! (go.PointerType v1.ObjectMeta) @! "GetUID" #()
  {{{ RET #m.(v1.ObjectMeta.UID');
      l ↦{dq} m
  }}}.
Proof. wp_start as "H". wp_auto. iApply "HΦ". iFrame. Qed.

Lemma wp_GetUID_deepown l m dq :
  {{{ is_pkg_init v1 ∗
      ObjectMetaV.deepown_l l m dq
  }}}
    l @! (go.PointerType v1.ObjectMeta) @! "GetUID" #()
  {{{ RET #m.(ObjectMetaV.UID');
      ObjectMetaV.deepown_l l m dq
  }}}.
Proof.
  iIntros (Φ) "(#Hinit & Hdeepown_l) HΦ".
  iDestruct "Hdeepown_l" as (c) "[Hl Hdeepown]".
  wp_apply (wp_GetUID with "[$Hl]").
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
    l @! (go.PointerType v1.ObjectMeta) @! "GetResourceVersion" #()
  {{{ RET #m.(v1.ObjectMeta.ResourceVersion');
      l ↦{dq} m
  }}}.
Proof. wp_start as "H". wp_auto. iApply "HΦ". iFrame. Qed.

Lemma wp_GetResourceVersion_deepown l m dq :
  {{{ is_pkg_init v1 ∗
      ObjectMetaV.deepown_l l m dq
  }}}
    l @! (go.PointerType v1.ObjectMeta) @! "GetResourceVersion" #()
  {{{ RET #m.(ObjectMetaV.ResourceVersion');
      ObjectMetaV.deepown_l l m dq
  }}}.
Proof.
  iIntros (Φ) "(#Hinit & Hdeepown_l) HΦ".
  iDestruct "Hdeepown_l" as (c) "[Hl Hdeepown]".
  wp_apply (wp_GetResourceVersion with "[$Hl]").
  iIntros "Hl".
  iNamed "Hdeepown".
  rewrite Hdeepown_resourceversion.
  iApply "HΦ".
  iExists c.
  iFrame.
  iPureIntro.
  done.
Qed.

Lemma wp_GetGeneration l m dq :
  {{{ is_pkg_init v1 ∗
      l ↦{dq} m
  }}}
    l @! (go.PointerType v1.ObjectMeta) @! "GetGeneration" #()
  {{{ RET #m.(v1.ObjectMeta.Generation');
      l ↦{dq} m
  }}}.
Proof. wp_start as "H". wp_auto. iApply "HΦ". iFrame. Qed.

Lemma wp_SetGeneration l m generation :
  {{{ is_pkg_init v1 ∗
      l ↦ m
  }}}
    l @! (go.PointerType v1.ObjectMeta) @! "SetGeneration" #generation
  {{{ RET #();
      l ↦ m <| v1.ObjectMeta.Generation' := generation |>
  }}}.
Proof. wp_start as "H". wp_auto. iApply "HΦ". iFrame. Qed.

Lemma wp_GetNamespace l m dq :
  {{{ is_pkg_init v1 ∗
      l ↦{dq} m
  }}}
    l @! (go.PointerType v1.ObjectMeta) @! "GetNamespace" #()
  {{{ RET #m.(v1.ObjectMeta.Namespace');
      l ↦{dq} m
  }}}.
Proof. wp_start as "H". wp_auto. iApply "HΦ". iFrame. Qed.

Lemma wp_GetNamespace_deepown l m dq:
  {{{ is_pkg_init v1 ∗
      ObjectMetaV.deepown_l l m dq
  }}}
    l @! (go.PointerType v1.ObjectMeta) @! "GetNamespace" #()
  {{{ RET #m.(ObjectMetaV.Namespace');
      ObjectMetaV.deepown_l l m dq
  }}}.
Proof.
  iIntros (Φ) "(#Hinit & Hdeepown_l) HΦ".
  iDestruct "Hdeepown_l" as (c) "[Hl Hdeepown]".
  wp_apply (wp_GetNamespace with "[$Hl]").
  iIntros "Hl".
  iNamed "Hdeepown".
  rewrite Hdeepown_namespace.
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
    l @! (go.PointerType v1.ObjectMeta) @! "SetNamespace" #namespace
  {{{ RET #();
      l ↦ m <| v1.ObjectMeta.Namespace' := namespace |>
  }}}.
Proof. wp_start as "H". wp_auto. iApply "HΦ". iFrame. Qed.

Lemma wp_SetNamespace_deepown l m namespace :
  {{{ is_pkg_init v1 ∗
      ObjectMetaV.deepown_l l m 1
  }}}
    l @! (go.PointerType v1.ObjectMeta) @! "SetNamespace" #namespace
  {{{ RET #();
      ObjectMetaV.deepown_l l (m <| ObjectMetaV.Namespace' := namespace |>) 1
  }}}.
Proof.
  iIntros (Φ) "(#Hinit & Hdeepown_l) HΦ".
  iDestruct "Hdeepown_l" as (c) "[Hl Hdeepown]".
  wp_apply (wp_SetNamespace with "[$Hl]").
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
    l @! (go.PointerType v1.ObjectMeta) @! "SetCreationTimestamp" #creation_timestamp
  {{{ RET #();
      l ↦ m <| v1.ObjectMeta.CreationTimestamp' := creation_timestamp |>
  }}}.
Proof. wp_start as "H". wp_auto. iApply "HΦ". iFrame. Qed.

Lemma wp_SetCreationTimestamp_deepown l m creation_timestamp pure_creation_timestamp :
  {{{ is_pkg_init v1 ∗
      ObjectMetaV.deepown_l l m 1 ∗
      TimeV.deepown creation_timestamp pure_creation_timestamp
  }}}
    l @! (go.PointerType v1.ObjectMeta) @! "SetCreationTimestamp" #creation_timestamp
  {{{ RET #();
      ObjectMetaV.deepown_l l (m <| ObjectMetaV.CreationTimestamp' := pure_creation_timestamp |>) 1
  }}}.
Proof.
  iIntros (Φ) "(#Hinit & Hdeepown_l & Hdeepown_time) HΦ".
  iDestruct "Hdeepown_l" as (c) "[Hl Hdeepown]".
  wp_apply (wp_SetCreationTimestamp with "[$Hl]").
  iIntros "Hl".
  iNamed "Hdeepown".
  iApply "HΦ".
  iExists (c <| v1.ObjectMeta.CreationTimestamp' := creation_timestamp |>).
  iFrame.
  iPureIntro.
  done.
Qed.

Lemma wp_GetDeletionTimestamp l m dq :
  {{{ is_pkg_init v1 ∗
      l ↦{dq} m
  }}}
    l @! (go.PointerType v1.ObjectMeta) @! "GetDeletionTimestamp" #()
  {{{ RET #m.(v1.ObjectMeta.DeletionTimestamp');
      l ↦{dq} m
  }}}.
Proof. wp_start as "H". iNamed "H". wp_auto. iApply "HΦ". iFrame. Qed.

Lemma wp_SetDeletionTimestamp l m deletion_timestamp :
  {{{ is_pkg_init v1 ∗
      l ↦ m
  }}}
    l @! (go.PointerType v1.ObjectMeta) @! "SetDeletionTimestamp" #deletion_timestamp
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
    l @! (go.PointerType v1.ObjectMeta) @! "SetDeletionTimestamp" #deletion_timestamp
  {{{ RET #();
      ObjectMetaV.deepown_l l (m <| ObjectMetaV.DeletionTimestamp' := pure_deletion_timestamp |>) 1
  }}}.
Proof.
  iIntros (Φ) "(#Hinit & Hdeepown_l & %Hdeletiontimestamp_none & Hdeletiontimestamp_some) HΦ".
  iDestruct "Hdeepown_l" as (c) "[Hl Hdeepown]".
  wp_apply (wp_SetDeletionTimestamp with "[$Hl]").
  iIntros "Hl".
  iNamed "Hdeepown".
  iApply "HΦ".
  iExists (c <| v1.ObjectMeta.DeletionTimestamp' := deletion_timestamp |>).
  iFrame.
  iPureIntro.
  done.
Qed.

Lemma wp_GetDeletionGracePeriodSeconds l m dq :
  {{{ is_pkg_init v1 ∗
      l ↦{dq} m
  }}}
    l @! (go.PointerType v1.ObjectMeta) @! "GetDeletionGracePeriodSeconds" #()
  {{{ RET #m.(v1.ObjectMeta.DeletionGracePeriodSeconds');
      l ↦{dq} m
  }}}.
Proof. wp_start as "H". wp_auto. iApply "HΦ". iFrame. Qed.

Lemma wp_SetDeletionGracePeriodSeconds l m dgps :
  {{{ is_pkg_init v1 ∗
      l ↦ m
  }}}
    l @! (go.PointerType v1.ObjectMeta) @! "SetDeletionGracePeriodSeconds" #dgps
  {{{ RET #();
      l ↦ m <| v1.ObjectMeta.DeletionGracePeriodSeconds' := dgps |>
  }}}.
Proof. wp_start as "H". wp_auto. iApply "HΦ". iFrame. Qed.

Lemma wp_SetDeletionGracePeriodSeconds_deepown l m dgps pure_dgps :
  {{{ is_pkg_init v1 ∗
      ObjectMetaV.deepown_l l m 1 ∗
      ⌜ dgps = null ↔ pure_dgps = None ⌝ ∗
      (match pure_dgps with
       | Some vd => ∃ cd, dgps ↦ cd ∗ ⌜ cd = vd ⌝
       | None => True
       end)
  }}}
    l @! (go.PointerType v1.ObjectMeta) @! "SetDeletionGracePeriodSeconds" #dgps
  {{{ RET #();
      ObjectMetaV.deepown_l l (m <| ObjectMetaV.DeletionGracePeriodSeconds' := pure_dgps |>) 1
  }}}.
Proof.
  iIntros (Φ) "(#Hinit & Hdeepown_l & %Hdgps_none & Hdgps_some) HΦ".
  iDestruct "Hdeepown_l" as (c) "[Hl Hdeepown]".
  wp_apply (wp_SetDeletionGracePeriodSeconds with "[$Hl]").
  iIntros "Hl".
  iNamed "Hdeepown".
  iApply "HΦ".
  iExists (c <| v1.ObjectMeta.DeletionGracePeriodSeconds' := dgps |>).
  iFrame.
  iPureIntro.
  done.
Qed.

Lemma wp_SetSelfLink l m self_link :
  {{{ is_pkg_init v1 ∗
      l ↦ m
  }}}
    l @! (go.PointerType v1.ObjectMeta) @! "SetSelfLink" #self_link
  {{{ RET #();
      l ↦ m <| v1.ObjectMeta.SelfLink' := self_link |>
  }}}.
Proof. wp_start as "H". wp_auto. iApply "HΦ". iFrame. Qed.

Lemma wp_SetSelfLink_deepown l m self_link :
  {{{ is_pkg_init v1 ∗
      ObjectMetaV.deepown_l l m 1
  }}}
    l @! (go.PointerType v1.ObjectMeta) @! "SetSelfLink" #self_link
  {{{ RET #();
      ObjectMetaV.deepown_l l (m <| ObjectMetaV.SelfLink' := self_link |>) 1
  }}}.
Proof.
  iIntros (Φ) "(#Hinit & Hdeepown_l) HΦ".
  iDestruct "Hdeepown_l" as (c) "[Hl Hdeepown]".
  wp_apply (wp_SetSelfLink with "[$Hl]").
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
    l @! (go.PointerType v1.ObjectMeta) @! "SetResourceVersion" #resource_version
  {{{ RET #();
      l ↦ m <| v1.ObjectMeta.ResourceVersion' := resource_version |>
  }}}.
Proof. wp_start as "H". wp_auto. iApply "HΦ". iFrame. Qed.

Lemma wp_SetResourceVersion_deepown l m resource_version :
  {{{ is_pkg_init v1 ∗
      ObjectMetaV.deepown_l l m 1
  }}}
    l @! (go.PointerType v1.ObjectMeta) @! "SetResourceVersion" #resource_version
  {{{ RET #();
      ObjectMetaV.deepown_l l (m <| ObjectMetaV.ResourceVersion' := resource_version |>) 1
  }}}.
Proof.
  iIntros (Φ) "(#Hinit & Hdeepown_l) HΦ".
  iDestruct "Hdeepown_l" as (c) "[Hl Hdeepown]".
  wp_apply (wp_SetResourceVersion with "[$Hl]").
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
    l @! (go.PointerType v1.ObjectMeta) @! "GetFinalizers" #()
  {{{ RET #m.(v1.ObjectMeta.Finalizers');
      l ↦{dq} m
  }}}.
Proof. wp_start as "H". wp_auto. iApply "HΦ". iFrame. Qed.

Lemma wp_GetFinalizers_deepown l m dq :
  {{{ is_pkg_init v1 ∗
      ObjectMetaV.deepown_l l m dq
  }}}
    l @! (go.PointerType v1.ObjectMeta) @! "GetFinalizers" #()
  {{{ sl, RET #sl;
      ⌜ sl = slice.nil ↔ m.(ObjectMetaV.Finalizers') = None ⌝ ∗
      match m.(ObjectMetaV.Finalizers') with
      | Some vfs => ∃ cfs, sl ↦*{dq} cfs ∗ ⌜ cfs = vfs ⌝ ∗ (sl ↦*{dq} cfs -∗ ObjectMetaV.deepown_l l m dq)
      | None => ObjectMetaV.deepown_l l m dq
      end
  }}}.
Proof.
  iIntros (Φ) "(#Hinit & Hdeepown_l) HΦ".
  iDestruct "Hdeepown_l" as (c) "[Hl Hdeepown]".
  wp_apply (wp_GetFinalizers with "[$Hl]").
  iIntros "Hl".
  iNamed "Hdeepown".
  iApply "HΦ".
  iSplit. 1: done.
  destruct m.(ObjectMetaV.Finalizers') as [|] eqn:Heq.
  - iDestruct "Hdeepown_finalizers_some" as (cfs) "[Hcfs_ptr <-]".
    iExists cfs. iFrame. iSplit. 1: done.
    iIntros "Hdeepown_finalizers_some".
    iFrame. iFrame "%".
    iSplit.
    + iPureIntro. split.
      * intros H. apply (proj1 Hdeepown_finalizers_none) in H. done.
      * intros H. rewrite Heq in H. done.
    + rewrite Heq. iFrame. done.
  - iFrame. iFrame "%".
    iSplit.
    + iPureIntro. split.
      * intros H. apply (proj1 Hdeepown_finalizers_none) in H. done.
      * intros H. apply (proj2 Hdeepown_finalizers_none). done.
    + rewrite Heq. iFrame.
Qed.

Lemma wp_SetFinalizers l m fs :
  {{{ is_pkg_init v1 ∗
      l ↦ m
  }}}
    l @! (go.PointerType v1.ObjectMeta) @! "SetFinalizers" #fs
  {{{ RET #();
      l ↦ m <| v1.ObjectMeta.Finalizers' := fs |>
  }}}.
Proof. wp_start as "H". wp_auto. iApply "HΦ". iFrame. Qed.

Lemma wp_SetFinalizers_deepown l m fs pure_fs :
  {{{ is_pkg_init v1 ∗
      ObjectMetaV.deepown_l l m 1 ∗
      ⌜ fs = slice.nil ↔ pure_fs = None ⌝ ∗
      (match pure_fs with
       | Some vfs => ∃ cfs, fs ↦* cfs ∗ ⌜ cfs = vfs ⌝
       | None => True
       end)
  }}}
    l @! (go.PointerType v1.ObjectMeta) @! "SetFinalizers" #fs
  {{{ RET #();
      ObjectMetaV.deepown_l l (m <| ObjectMetaV.Finalizers' := pure_fs |>) 1
  }}}.
Proof.
  iIntros (Φ) "(#Hinit & Hdeepown_l & %Hfs_none & Hfs_some) HΦ".
  iDestruct "Hdeepown_l" as (c) "[Hl Hdeepown]".
  wp_apply (wp_SetFinalizers with "[$Hl]").
  iIntros "Hl".
  iNamed "Hdeepown".
  iApply "HΦ".
  iExists (c <| v1.ObjectMeta.Finalizers' := fs |>).
  iFrame.
  iPureIntro.
  done.
Qed.

Lemma wp_SetUID l m uid :
  {{{ is_pkg_init v1 ∗
      l ↦ m
  }}}
    l @! (go.PointerType v1.ObjectMeta) @! "SetUID" #uid
  {{{ RET #();
      l ↦ m <| v1.ObjectMeta.UID' := uid |>
  }}}.
Proof. wp_start as "H". wp_auto. iApply "HΦ". iFrame. Qed.

Lemma wp_SetUID_deepown l m uid :
  {{{ is_pkg_init v1 ∗
      ObjectMetaV.deepown_l l m 1
  }}}
    l @! (go.PointerType v1.ObjectMeta) @! "SetUID" #uid
  {{{ RET #();
      ObjectMetaV.deepown_l l (m <| ObjectMetaV.UID' := uid |>) 1
  }}}.
Proof.
  iIntros (Φ) "(#Hinit & Hdeepown_l) HΦ".
  iDestruct "Hdeepown_l" as (c) "[Hl Hdeepown]".
  wp_apply (wp_SetUID with "[$Hl]").
  iIntros "Hl".
  iNamed "Hdeepown".
  iApply "HΦ".
  iExists (c <| v1.ObjectMeta.UID' := uid |>).
  iFrame.
  iPureIntro.
  done.
Qed.

Lemma wp_DeleteOptions__DeepCopy l options :
  {{{ is_pkg_init v1 ∗
      DeleteOptionsV.deepown_l l options 1
  }}}
    l @! (go.PointerType v1.DeleteOptions) @! "DeepCopy" #()
  {{{ l', RET #l';
      DeleteOptionsV.deepown_l l' options 1 ∗
      DeleteOptionsV.deepown_l l options 1
  }}}.
Proof. Admitted.

Lemma wp_NewControllerRef_ReplicaSet owner gvk rs_l m dq:
  {{{ is_pkg_init v1 ∗
      ⌜ owner = interface.mk_ok (go.PointerType v1.ReplicaSet) (# rs_l) ⌝ ∗
      ObjectMetaV.deepown_l (ReplicaSetV.objectmeta_ptr rs_l) m dq
  }}}
    @! v1.NewControllerRef #owner #gvk
  {{{ l controller_ref, RET #l;
      OwnerReferenceV.deepown_l l controller_ref 1 ∗
      ⌜ OwnerReferenceV.refers_to_controller controller_ref gvk.(schema.GroupVersionKind.Kind')
        m.(ObjectMetaV.Name')
        m.(ObjectMetaV.UID') ⌝ ∗
      ObjectMetaV.deepown_l (ReplicaSetV.objectmeta_ptr rs_l) m dq
  }}}.
Proof. Admitted.

Definition namespace_matches ns_query ns: Prop :=
  ns_query = v1.NamespaceAll ∨ ns_query = ns.

End proof.
