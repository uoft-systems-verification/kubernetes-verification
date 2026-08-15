From New.proof.k8s_io.apimachinery.pkg.apis.meta Require Export v1_init.
From New.proof Require Import prelude empty_ffi.
From New.proof.kubernetes_types Require Import prelude.
From New.proof.k8s_io.apimachinery.pkg Require Import labels.

Section proof.
Context `{hG: !heapGS Σ} `{!ffi_semantics _ _}.
Context `{!ffi_semantics _ _}.
Context {sem : go.Semantics} {package_sem : v1.Assumptions}.
Local Set Default Proof Using "All".

Lemma wp_Now :
  {{{ is_pkg_init v1 }}}
    @! v1.Now #()
  {{{ c v, RET #c;
    TimeV.deepown c v 1
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

(** Borrow the labels map from an owned ObjectMeta. The wand returns the map
    ownership to the enclosing metadata object after the caller has inspected
    it. *)
Lemma wp_GetLabels_deepown meta_l meta dq :
  {{{ is_pkg_init v1 ∗
      ObjectMetaV.deepown_l meta_l meta dq
  }}}
    meta_l @! (go.PointerType v1.ObjectMeta) @! "GetLabels" #()
  {{{ labels_l, RET #labels_l;
      labels_set_rep labels_l meta.(ObjectMetaV.Labels') dq ∗
      (labels_set_rep labels_l meta.(ObjectMetaV.Labels') dq -∗
        ObjectMetaV.deepown_l meta_l meta dq)
  }}}.
Proof.
  wp_start as "Hmeta".
  iDestruct "Hmeta" as (meta_c) "[Hmeta_l Hmeta]".
  iDestruct (struct_fields_split (V:=v1.ObjectMeta.t) with "Hmeta_l") as
    "[Hmeta_fields %Hmeta_nonnull]".
  iNamedPrefix "Hmeta_fields" "Hfield_".
  iNamed "Hmeta".
  wp_auto.
  iApply "HΦ".
  destruct meta.(ObjectMetaV.Labels') as [label_map|] eqn:Hlabels.
  - iDestruct "Hdeepown_labels_some" as (label_map_c)
      "[Hlabel_map %Hlabel_map]". subst label_map_c.
    iAssert (labels_set_rep meta_c.(v1.ObjectMeta.Labels')
      (Some label_map) dq) with "[Hlabel_map]" as "Hlabels_rep".
    { rewrite /labels_set_rep. iFrame.
      iPureIntro. exact Hdeepown_labels_none. }
    iFrame "Hlabels_rep".
    iIntros "Hlabels_rep_back".
    iEval (rewrite /labels_set_rep) in "Hlabels_rep_back".
    iDestruct "Hlabels_rep_back" as "[_ Hlabel_map]".
    iCombineNamed "Hfield_*" as "Hmeta_fields".
    iAssert (typed_pointsto_def meta_l meta_c dq) with
      "[Hmeta_fields]" as "Hmeta_l".
    { iNamed "Hmeta_fields". simpl. rewrite /named. iFrame. }
    iDestruct (struct_fields_combine (V:=v1.ObjectMeta.t) meta_l meta_c dq
      Hmeta_nonnull with "Hmeta_l") as "Hmeta_l".
    iExists meta_c. iFrame "Hmeta_l".
    rewrite /ObjectMetaV.deepown /named Hlabels. iFrame. iFrame "%".
    done.
  - iAssert (labels_set_rep meta_c.(v1.ObjectMeta.Labels') None dq)
      as "Hlabels_rep".
    { rewrite /labels_set_rep. iSplit; last done.
      iPureIntro. split; [intros _; done|].
      intros _. apply Hdeepown_labels_none. done. }
    iFrame "Hlabels_rep".
    iIntros "_".
    iCombineNamed "Hfield_*" as "Hmeta_fields".
    iAssert (typed_pointsto_def meta_l meta_c dq) with
      "[Hmeta_fields]" as "Hmeta_l".
    { iNamed "Hmeta_fields". simpl. rewrite /named. iFrame. }
    iDestruct (struct_fields_combine (V:=v1.ObjectMeta.t) meta_l meta_c dq
      Hmeta_nonnull with "Hmeta_l") as "Hmeta_l".
    iExists meta_c. iFrame "Hmeta_l".
    rewrite /ObjectMetaV.deepown /named Hlabels. iFrame. iFrame "%".
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
      TimeV.deepown creation_timestamp pure_creation_timestamp 1
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
       | Some vd => ∃ cd, deletion_timestamp ↦ cd ∗ TimeV.deepown cd vd 1
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

(* LabelSelector.DeepCopy is generated by Kubernetes' deepcopy generator and is
   not translated.  This is its ownership-preserving contract: the source is read
   at any fraction, and the copy is freshly allocated hence fully owned. *)
Lemma wp_LabelSelector__DeepCopy l selector dq :
  {{{ is_pkg_init v1 ∗
      LabelSelectorV.deepown_l l selector dq
  }}}
    l @! (go.PointerType v1.LabelSelector) @! "DeepCopy" #()
  {{{ l', RET #l';
      LabelSelectorV.deepown_l l' selector 1 ∗
      LabelSelectorV.deepown_l l selector dq
  }}}.
Proof. Admitted.

Lemma wp_GetOwnerReferences_deepown l m dq :
  {{{ is_pkg_init v1 ∗
      ObjectMetaV.deepown_l l m dq
  }}}
    l @! (go.PointerType v1.ObjectMeta) @! "GetOwnerReferences" #()
  {{{ sl, RET #sl;
      ⌜ sl = slice.nil ↔ m.(ObjectMetaV.OwnerReferences') = None ⌝ ∗
      match m.(ObjectMetaV.OwnerReferences') with
      | Some refs => ∃ cs,
          sl ↦*{dq} cs ∗
          ([∗ list] c;ref ∈ cs;refs, OwnerReferenceV.deepown c ref dq) ∗
          (∀ cs', sl ↦*{dq} cs' ∗
           ([∗ list] c;ref ∈ cs';refs, OwnerReferenceV.deepown c ref dq) -∗
           ObjectMetaV.deepown_l l m dq)
      | None => ObjectMetaV.deepown_l l m dq
      end
  }}}.
Proof.
  iIntros (Φ) "(#Hinit & Hmeta) HΦ".
  iDestruct "Hmeta" as (c) "[Hl Hmeta]".
  wp_method_call. rewrite /v1.ObjectMeta__GetOwnerReferencesⁱᵐᵖˡ. wp_call.
  iNamed "Hmeta". wp_auto.
  iApply "HΦ". iSplit; first done.
  destruct m.(ObjectMetaV.OwnerReferences') as [refs|] eqn:Hrefs.
  - iDestruct "Hdeepown_ownerreferences_some" as (cs) "[Hsl Hrefs]".
    iExists cs. iFrame. iIntros (cs') "[Hsl Hrefs]".
    iExists c. iFrame. iFrame "%". iSplit.
    + iPureIntro. rewrite Hrefs. exact Hdeepown_ownerreferences_none.
    + rewrite Hrefs. iExists cs'. iFrame.
  - iExists c. iFrame. iFrame "%". iSplit.
    + iPureIntro. rewrite Hrefs. exact Hdeepown_ownerreferences_none.
    + rewrite Hrefs. iFrame.
Qed.

Definition is_controller_reference_of (m : ObjectMetaV.t)
    (ref : OwnerReferenceV.t) : Prop :=
  ∃ refs,
    m.(ObjectMetaV.OwnerReferences') = Some refs ∧
    ref ∈ refs ∧
    ref.(OwnerReferenceV.Controller') = Some true.

Definition owner_references_borrow (m : ObjectMetaV.t) (dq : dfrac)
    (sl : slice.t)
    (Restore : iProp Σ) : iProp Σ :=
  ⌜ sl = slice.nil ↔ m.(ObjectMetaV.OwnerReferences') = None ⌝ ∗
  match m.(ObjectMetaV.OwnerReferences') with
  | Some refs => ∃ cs,
      sl ↦*{dq} cs ∗
      ([∗ list] c;ref ∈ cs;refs, OwnerReferenceV.deepown c ref dq) ∗
      (∀ cs',
        sl ↦*{dq} cs' ∗
        ([∗ list] c;ref ∈ cs';refs, OwnerReferenceV.deepown c ref dq) -∗
        Restore)
  | None => Restore
  end.

Definition get_owner_references_capability (owner : interface.t)
    (m : ObjectMetaV.t) (dq : dfrac)
    (Own : iProp Σ) : iProp Σ :=
  {{{ "Hinit" ∷ is_pkg_init v1 ∗
      "Hown" ∷ Own
  }}}
    (MethodResolve v1.Object "GetOwnerReferences" #owner) #()
  {{{ sl, RET #sl; owner_references_borrow m dq sl Own }}}.

Lemma get_owner_references_capability_ObjectMeta meta_l m dq :
  ⊢ get_owner_references_capability
    (interface.mk_ok (go.PointerType v1.ObjectMeta) #meta_l) m dq
    (ObjectMetaV.deepown_l meta_l m dq).
Proof.
  unfold get_owner_references_capability.
  wp_start as "H".
  iNamed "H".
  wp_auto.
  wp_apply (wp_GetOwnerReferences_deepown with "[$Hinit $Hown]").
  iIntros (sl) "Hrefs".
  iApply "HΦ". iExact "Hrefs".
Qed.

Local Lemma wp_GetControllerOfNoCopy_general owner m dq (Own : iProp Σ) :
  {{{ "Hinit" ∷ is_pkg_init v1 ∗
      "Hget" ∷ get_owner_references_capability owner m dq Own ∗
      "Hmeta" ∷ Own
  }}}
    @! v1.GetControllerOfNoCopy #owner
  {{{ controller_ref_l, RET #controller_ref_l;
      (⌜ controller_ref_l = null ⌝ ∗
       Own) ∨
      (∃ controller_ref controller_c,
        ⌜ controller_ref_l ≠ null ∧ is_controller_reference_of m controller_ref ⌝ ∗
        controller_ref_l ↦{dq} controller_c ∗
        OwnerReferenceV.deepown controller_c controller_ref dq ∗
        (controller_ref_l ↦{dq} controller_c ∗
         OwnerReferenceV.deepown controller_c controller_ref dq -∗ Own))
  }}}.
Proof.
  wp_start as "H". iNamed "H".
  rewrite exception_do_unseal /exception_do_def.
  wp_alloc controllee_ptr as "Hcontrollee".
  wp_pures.
  wp_alloc refs_ptr as "Hrefs_ptr".
  wp_pures.
  wp_load.
  wp_apply ("Hget" with "[$Hinit $Hmeta]").
  iIntros (refs_sl) "(%Hrefs_nil & Hrefs)". wp_auto.
  destruct m.(ObjectMetaV.OwnerReferences') as [refs|] eqn:Hrefs_some.
  2: {
    assert (refs_sl = slice.nil) as ->.
    { apply Hrefs_nil. done. }
    iPoseProof (own_slice_nil (V:=v1.OwnerReference.t) dq) as "Hrefs_sl".
    wp_alloc loop_i_ptr as "Hloop_i". wp_auto.
    set I0 := (∃ (loop_i : w64),
      "Hloop_i" ∷ loop_i_ptr ↦ loop_i ∗
      "%Hloop_i_bound" ∷ ⌜ 0 ≤ sint.Z loop_i ⌝)%I.
    iAssert I0 with "[Hloop_i]" as "Hloop".
    { iExists (W64 0). iFrame. iPureIntro. word. }
    wp_for "Hloop". wp_if_destruct; first word.
    clear I0. wp_auto.
    rewrite return_val_unseal /return_val_def. wp_auto.
    iApply "HΦ". iLeft. iFrame. done. }
  iDestruct "Hrefs" as (cs) "(Hrefs_sl & Hrefs & Hmeta_restore)".
  iDestruct (own_slice_len with "Hrefs_sl") as %(Hrefs_len1 & Hrefs_len2).
  iDestruct (big_sepL2_length with "Hrefs") as %Hrefs_len.
  wp_alloc loop_i_ptr as "Hloop_i". wp_auto.
  set I := (∃ (loop_i source_i : w64),
    "Hloop_i" ∷ loop_i_ptr ↦ loop_i ∗
    "Hi" ∷ i_ptr ↦ source_i ∗
    "Hrefs_sl" ∷ refs_sl ↦*{dq} cs ∗
    "Hrefs" ∷ ([∗ list] c;ref ∈ cs;refs, OwnerReferenceV.deepown c ref dq) ∗
    "%Hi_bound" ∷ ⌜ 0 ≤ sint.Z loop_i ≤ sint.Z (slice.len refs_sl) ⌝)%I.
  iAssert I with "[Hloop_i i Hrefs_sl Hrefs]" as "Hloop".
  { iExists (W64 0), (W64 0). iFrame. iPureIntro. word. }
  wp_for "Hloop". wp_if_destruct.
  - list_elem cs (sint.Z loop_i) as this_c.
    destruct (decide (0 ≤ sint.Z loop_i < sint.Z (slice.len refs_sl)))
      as [_|Hbounds]; last word.
    wp_apply (wp_load_slice_index with "[$Hrefs_sl]"); [word| |].
    { iPureIntro. exact Hthis_c_lookup. }
    iIntros "Hrefs_sl". wp_auto.
    assert (∃ this_ref, refs !! sint.nat loop_i = Some this_ref) as
      [this_ref Hthis_ref_lookup].
    { apply lookup_lt_is_Some_2. rewrite -Hrefs_len Hrefs_len1. word. }
    iDestruct (big_sepL2_lookup_acc with "Hrefs") as "[Hthis Hrefs_close]";
      [exact Hthis_c_lookup|exact Hthis_ref_lookup|].
    iDestruct (own_slice_elem_acc (sint.Z loop_i) with "Hrefs_sl")
      as "[Hcell Hrefs_sl_close]"; [word|exact Hthis_c_lookup|].
    iDestruct (typed_pointsto_not_null with "Hcell") as %Hthis_c_nonnull.
    iNamedPrefix "Hthis" "Hthis_".
    destruct this_ref.(OwnerReferenceV.Controller') as [controller|]
      eqn:Hcontroller.
    + iDestruct "Hthis_Hdeepown_controller_some" as
        (controller_c) "[Hcontroller %Hcontroller_c]".
      subst controller_c.
      assert (this_c.(v1.OwnerReference.Controller') ≠ null) as Hcontroller_nonnull.
      { intros Hnull. apply Hthis_Hdeepown_controller_none in Hnull.
        done. }
      destruct controller.
      * destruct (decide
          (0 ≤ sint.Z loop_i < sint.Z (slice.len refs_sl)))
        as [_|Hbounds']; last word.
        wp_auto.
        rewrite -> bool_decide_false by exact Hcontroller_nonnull.
        wp_auto.
        destruct (decide
          (0 ≤ sint.Z loop_i < sint.Z (slice.len refs_sl)))
          as [_|Hbounds'']; last word.
        wp_auto.
        iCombineNamed "Hthis_*" as "Hthis".
        destruct (decide
          (0 ≤ sint.Z loop_i < sint.Z (slice.len refs_sl)))
          as [_|Hbounds''']; last word.
        wp_auto.
        iApply wp_for_post_return.
        rewrite return_val_unseal /return_val_def. wp_auto.
        rewrite exception_seq_unseal /exception.exception_seq_def. wp_auto.
        iApply ("HΦ" $! (slice_index_ref v1.OwnerReference.t
          (sint.Z loop_i) refs_sl)). iRight.
        iExists this_ref, this_c. iSplitR.
        { iPureIntro. split; first exact Hthis_c_nonnull.
          unfold is_controller_reference_of. eexists. split; first done.
          split; [eapply list_elem_of_lookup_2; exact Hthis_ref_lookup|done]. }
        iFrame "Hcell".
        iAssert (OwnerReferenceV.deepown this_c this_ref dq)
          with "[Hthis Hcontroller]" as "Hthis".
        { unfold OwnerReferenceV.deepown. iFrame "% Hthis".
          iSplit.
          - iPureIntro. rewrite Hcontroller.
            exact Hthis_Hdeepown_controller_none.
          - rewrite Hcontroller. iExists true. iFrame. done. }
        iFrame "Hthis".
        iIntros "[Hcell Hthis]".
        iDestruct ("Hrefs_sl_close" with "Hcell") as "Hrefs_sl".
        iDestruct ("Hrefs_close" with "Hthis") as "Hrefs".
        iEval (rewrite (list_insert_id _ _ _ Hthis_c_lookup)) in "Hrefs_sl".
        iApply ("Hmeta_restore" $! cs). iFrame.
      * destruct (decide
          (0 ≤ sint.Z loop_i < sint.Z (slice.len refs_sl)))
        as [_|Hbounds']; last word.
        wp_auto.
        rewrite -> bool_decide_false by exact Hcontroller_nonnull.
        wp_auto.
        destruct (decide
          (0 ≤ sint.Z loop_i < sint.Z (slice.len refs_sl)))
          as [_|Hbounds'']; last word.
        wp_auto.
        iCombineNamed "Hthis_*" as "Hthis_rest".
        iAssert (OwnerReferenceV.deepown this_c this_ref dq)
          with "[Hthis_rest Hcontroller]" as "Hthis".
        { unfold OwnerReferenceV.deepown. iFrame "% Hthis_rest".
          iSplit.
          - iPureIntro. rewrite Hcontroller.
            exact Hthis_Hdeepown_controller_none.
          - rewrite Hcontroller. iExists false. iFrame. done. }
        iDestruct ("Hrefs_sl_close" with "Hcell") as "Hrefs_sl".
        iDestruct ("Hrefs_close" with "Hthis") as "Hrefs".
        iEval (rewrite (list_insert_id _ _ _ Hthis_c_lookup)) in "Hrefs_sl".
        iApply wp_for_post_do. wp_auto.
        iFrame "HΦ Hmeta_restore Hrefs_ptr".
        iExists (word.add loop_i (W64 1)), loop_i. iFrame. iPureIntro. word.
    + assert (this_c.(v1.OwnerReference.Controller') = null) as Hcontroller_null.
      { apply Hthis_Hdeepown_controller_none. done. }
      destruct (decide
        (0 ≤ sint.Z loop_i < sint.Z (slice.len refs_sl)))
        as [_|Hbounds']; last word.
      wp_auto.
      rewrite -> bool_decide_true by exact Hcontroller_null.
      wp_auto.
      iAssert (OwnerReferenceV.deepown this_c this_ref dq)
        with "[Hthis_Hdeepown_blockownerdeleton_some]" as "Hthis".
      { unfold OwnerReferenceV.deepown.
        iFrame "% Hthis_Hdeepown_blockownerdeleton_some".
        iSplit.
        - iPureIntro. rewrite Hcontroller.
          exact Hthis_Hdeepown_controller_none.
        - rewrite Hcontroller. done. }
      iDestruct ("Hrefs_sl_close" with "Hcell") as "Hrefs_sl".
      iDestruct ("Hrefs_close" with "Hthis") as "Hrefs".
      iEval (rewrite (list_insert_id _ _ _ Hthis_c_lookup)) in "Hrefs_sl".
      iApply wp_for_post_do. wp_auto.
      iFrame "HΦ Hmeta_restore Hrefs_ptr".
      iExists (word.add loop_i (W64 1)), loop_i. iFrame. iPureIntro. word.
  - clear I.
    rewrite return_val_unseal /return_val_def. wp_auto.
    iApply "HΦ". iLeft. iSplit; first done.
    iApply ("Hmeta_restore" $! cs). iFrame.
Qed.

Lemma wp_GetControllerOf_general owner m dq (Own : iProp Σ) :
  {{{ "Hinit" ∷ is_pkg_init v1 ∗
      "Hget" ∷ get_owner_references_capability owner m dq Own ∗
      "Hmeta" ∷ Own
  }}}
    @! v1.GetControllerOf #owner
  {{{ controller_ref_l, RET #controller_ref_l;
      Own ∗
      (⌜ controller_ref_l = null ⌝ ∨
       ∃ controller_ref,
         ⌜ controller_ref_l ≠ null ∧ is_controller_reference_of m controller_ref ⌝ ∗
         OwnerReferenceV.deepown_l controller_ref_l controller_ref 1)
  }}}.
Proof.
  wp_start as "H". iNamed "H".
  wp_auto.
  wp_bind (@! v1.GetControllerOfNoCopy #owner)%E.
  wp_apply (wp_GetControllerOfNoCopy_general owner m dq Own with
    "[$Hinit $Hget $Hmeta]").
  iIntros (controller_ref_l) "Hresult".
  iDestruct "Hresult" as "[(%Hnull & Hmeta)|Hresult]".
  - subst controller_ref_l. wp_auto. iApply "HΦ". iFrame "Hmeta".
    iLeft. done.
  - iDestruct "Hresult" as (controller_ref controller_c)
      "(%Hcontroller & Href_l & Href & Hrestore)".
    destruct Hcontroller as [Hcontroller_l_nonnull Hcontroller].
    wp_auto.
    rewrite -> bool_decide_false by exact Hcontroller_l_nonnull.
    wp_auto.
    unfold is_controller_reference_of in Hcontroller.
    destruct Hcontroller as (refs & Hrefs_some & Hcontroller_mem & Hcontroller).
    iNamedPrefix "Href" "Href_".
    iEval (rewrite Hcontroller) in "Href_Hdeepown_controller_some".
    iDestruct "Href_Hdeepown_controller_some" as
      (controller_b) "[Hcontroller_b %Hcontroller_b]".
    subst controller_b.
    wp_auto.
    wp_bind (#(functions ptr.To [go.bool]) #true)%E.
    wp_func_call. wp_call. wp_auto.
    destruct controller_ref.(OwnerReferenceV.BlockOwnerDeletion') as [block|]
      eqn:Hblock.
    + iDestruct "Href_Hdeepown_blockownerdeleton_some" as
        (block_c) "[Hblock_c %Hblock_c]". subst block_c.
      iDestruct (typed_pointsto_not_null with "Hblock_c") as %Hblock_nonnull.
      rewrite -> bool_decide_false by exact Hblock_nonnull.
      wp_auto.
      wp_bind (#(functions ptr.To [go.bool]) #block)%E.
      wp_func_call. wp_call.
      wp_alloc block_ptr as "Hblock_new". wp_auto.
      iAssert (OwnerReferenceV.deepown controller_c controller_ref dq)
        with "[Hcontroller_b Hblock_c]" as "Href".
      { unfold OwnerReferenceV.deepown, named. iFrame "%".
        rewrite Hcontroller. iSplitL "Hcontroller_b".
        - iExists true. iFrame. done.
        - iSplitL "".
          + iPureIntro. rewrite Hblock.
            exact Href_Hdeepown_blockownerdeleton_none.
          + rewrite Hblock. iExists block. iFrame. done. }
      iDestruct ("Hrestore" with "[$Href_l $Href]") as "Hmeta".
      iDestruct (typed_pointsto_not_null with "v") as %Hv_nonnull.
      iDestruct (typed_pointsto_not_null with "Hblock_new") as %Hblock_new_nonnull.
      iDestruct (typed_pointsto_not_null with "cp") as %Hcp_nonnull.
      iApply "HΦ". iFrame "Hmeta". iRight.
      iExists controller_ref. iSplitR.
      { iPureIntro. split; first exact Hcp_nonnull. unfold is_controller_reference_of.
        eexists. done. }
      iExists (controller_c <| v1.OwnerReference.Controller' := v_ptr |> <|
        v1.OwnerReference.BlockOwnerDeletion' := block_ptr |>).
      iFrame "cp". unfold OwnerReferenceV.deepown, named. simpl.
      iFrame "%". rewrite Hcontroller Hblock.
      iSplitL "".
      * iPureIntro. split; intros; done.
      * iSplitL "v".
        { iExists true. iFrame. done. }
        iSplitL "".
        { iPureIntro. split; intros; done. }
        iExists block. iFrame. done.
    + assert (controller_c.(v1.OwnerReference.BlockOwnerDeletion') = null)
        as Hblock_null.
      { apply Href_Hdeepown_blockownerdeleton_none. done. }
      rewrite -> bool_decide_true by exact Hblock_null.
      wp_auto.
      iAssert (OwnerReferenceV.deepown controller_c controller_ref dq)
        with "[Hcontroller_b]" as "Href".
      { unfold OwnerReferenceV.deepown, named. iFrame "%".
        rewrite Hcontroller Hblock. iSplitL "Hcontroller_b".
        - iExists true. iFrame. done.
        - iSplitL "".
          + iPureIntro. exact Href_Hdeepown_blockownerdeleton_none.
          + done. }
      iDestruct ("Hrestore" with "[$Href_l $Href]") as "Hmeta".
      iDestruct (typed_pointsto_not_null with "v") as %Hv_nonnull.
      iDestruct (typed_pointsto_not_null with "cp") as %Hcp_nonnull.
      iApply "HΦ". iFrame "Hmeta". iRight.
      iExists controller_ref. iSplitR.
      { iPureIntro. split; first exact Hcp_nonnull. unfold is_controller_reference_of.
        eexists. done. }
      iExists (controller_c <| v1.OwnerReference.Controller' := v_ptr |>).
      iFrame "cp". unfold OwnerReferenceV.deepown, named. simpl.
      iFrame "%". rewrite Hcontroller Hblock.
      iSplitL "".
      * iPureIntro. split; intros; done.
      * iSplitL "v".
        { iExists true. iFrame. done. }
        iSplitL ""; done.
Qed.

Lemma wp_GetControllerOf owner meta_l m dq :
  {{{ "Hinit" ∷ is_pkg_init v1 ∗
      "%Howner" ∷ ⌜ owner = interface.mk_ok (go.PointerType v1.ObjectMeta) #meta_l ⌝ ∗
      "Hmeta" ∷ ObjectMetaV.deepown_l meta_l m dq
  }}}
    @! v1.GetControllerOf #owner
  {{{ controller_ref_l, RET #controller_ref_l;
      ObjectMetaV.deepown_l meta_l m dq ∗
      (⌜ controller_ref_l = null ⌝ ∨
       ∃ controller_ref,
         ⌜ controller_ref_l ≠ null ∧ is_controller_reference_of m controller_ref ⌝ ∗
         OwnerReferenceV.deepown_l controller_ref_l controller_ref 1)
  }}}.
Proof.
  iIntros (Φ) "H HΦ". iNamed "H". subst owner.
  iPoseProof (get_owner_references_capability_ObjectMeta meta_l m dq) as "Hget".
  iApply (wp_GetControllerOf_general with "[$Hinit $Hget $Hmeta]").
  iExact "HΦ".
Qed.

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
      ⌜ OwnerReferenceV.valid controller_ref ⌝ ∗
      ObjectMetaV.deepown_l (ReplicaSetV.objectmeta_ptr rs_l) m dq
  }}}.
Proof. Admitted.

Lemma wp_NewControllerRef_StatefulSet owner gvk set_l m dq :
  {{{ is_pkg_init v1 ∗
      ⌜ owner = interface.mk_ok (go.PointerType v1.StatefulSet) (#set_l) ⌝ ∗
      ⌜ gvk.(schema.GroupVersionKind.Group') = "apps"%go ∧
        gvk.(schema.GroupVersionKind.Version') = "v1"%go ∧
        gvk.(schema.GroupVersionKind.Kind') = "StatefulSet"%go ⌝ ∗
      ⌜ ObjectMetaV.valid StatefulSetV.kind m ⌝ ∗
      ObjectMetaV.deepown_l (StatefulSetV.objectmeta_ptr set_l) m dq
  }}}
    @! v1.NewControllerRef #owner #gvk
  {{{ l controller_ref, RET #l;
      OwnerReferenceV.deepown_l l controller_ref 1 ∗
      ⌜ OwnerReferenceV.refers_to_controller controller_ref
          gvk.(schema.GroupVersionKind.Kind')
          m.(ObjectMetaV.Name') m.(ObjectMetaV.UID') ⌝ ∗
      ⌜ OwnerReferenceV.valid controller_ref ⌝ ∗
      ObjectMetaV.deepown_l (StatefulSetV.objectmeta_ptr set_l) m dq
  }}}.
Proof. Admitted.

Definition namespace_matches ns_query ns: Prop :=
  ns_query = v1.NamespaceAll ∨ ns_query = ns.

End proof.
