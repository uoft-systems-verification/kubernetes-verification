From New.proof Require Import prelude empty_ffi.
From New.proof.kubernetes_types Require Export prelude.
From New.proof.k8s_io.api.core Require Export v1.
From New.proof.k8s_io.api.apps Require Export v1.
From New.proof.k8s_io.apimachinery.pkg.api Require Export meta_init.
From New.proof.k8s_io.apimachinery.pkg Require Import labels.

Section proof.
Context `{hG: !heapGS Σ} `{!ffi_semantics _ _}.
Context {sem : go.Semantics}
  {package_sem : code.k8s_io.apimachinery.pkg.api.meta.meta.Assumptions}
  {meta_v1_sem : code.k8s_io.apimachinery.pkg.apis.meta.v1.v1.Assumptions}
  {core_v1_sem : code.k8s_io.api.core.v1.v1.Assumptions}
  {apps_v1_sem : code.k8s_io.api.apps.v1.v1.Assumptions}.
Local Set Default Proof Using "All".

Lemma wp_Accessor i l o:
  {{{ is_pkg_init code.k8s_io.apimachinery.pkg.api.meta.pkg_id.meta ∗
      "%Hi" ∷ ⌜ KObjectV.valid_interface i l o ⌝
  }}}
    @! code.k8s_io.apimachinery.pkg.api.meta.meta.Accessor #(interface.ok i)
  {{{ RET (#(interface.ok i), #interface.nil);
    True
  }}}.
Proof.
  wp_start as "H". iNamed "H".
  destruct o; simpl in Hi; destruct Hi as [-> Hcontains]; wp_auto;
    rewrite Hcontains; wp_auto.
  all: iApply "HΦ"; done.
Qed.

(** The borrowed-labels rule after method promotion through a supported
    Kubernetes object interface. *)
Lemma wp_GetLabels_deepown_kobject i l o meta dq :
  {{{ is_pkg_init code.k8s_io.apimachinery.pkg.apis.meta.v1.pkg_id.v1 ∗
      "%Hi" ∷ ⌜ KObjectV.valid_interface i l o ⌝ ∗
      "Hmeta" ∷ ObjectMetaV.deepown_l (KObjectV.objectmeta_ptr l o) meta dq
  }}}
    #(methods i.(interface.ty) "GetLabels" i.(interface.v)) #()
  {{{ labels_l, RET #labels_l;
      labels_set_rep labels_l meta.(ObjectMetaV.Labels') dq ∗
      (labels_set_rep labels_l meta.(ObjectMetaV.Labels') dq -∗
        ObjectMetaV.deepown_l (KObjectV.objectmeta_ptr l o) meta dq)
  }}}.
Proof.
  wp_start as "H". iNamed "H".
  destruct o; simpl in Hi; destruct Hi as [-> _]; wp_method_call;
    wp_pures; wp_apply (wp_GetLabels_deepown with "[$Hmeta]");
    iIntros (labels_l) "Hlabels"; iApply "HΦ"; iFrame.
Qed.

Lemma wp_GetName_deepown_kobject i l o m dq:
  {{{ is_pkg_init code.k8s_io.apimachinery.pkg.apis.meta.v1.pkg_id.v1 ∗
      "%Hi" ∷ ⌜ KObjectV.valid_interface i l o ⌝ ∗
      "Hmeta" ∷ ObjectMetaV.deepown_l (KObjectV.objectmeta_ptr l o) m dq
  }}}
    #(methods i.(interface.ty) "GetName" i.(interface.v)) #()
  {{{ RET #m.(ObjectMetaV.Name');
      ObjectMetaV.deepown_l (KObjectV.objectmeta_ptr l o) m dq
  }}}.
Proof.
  wp_start as "H". iNamed "H".
  destruct o; simpl in Hi; destruct Hi as [-> _]; wp_method_call;
    wp_pures; wp_apply (wp_GetName_deepown with "[$Hmeta]");
    iIntros "Hmeta"; iApply "HΦ"; iFrame.
Qed.

Lemma wp_GetGenerateName_deepown_kobject i l o m dq:
  {{{ is_pkg_init code.k8s_io.apimachinery.pkg.apis.meta.v1.pkg_id.v1 ∗
      "%Hi" ∷ ⌜ KObjectV.valid_interface i l o ⌝ ∗
      "Hmeta" ∷ ObjectMetaV.deepown_l (KObjectV.objectmeta_ptr l o) m dq
  }}}
    #(methods i.(interface.ty) "GetGenerateName" i.(interface.v)) #()
  {{{ RET #m.(ObjectMetaV.GenerateName');
      ObjectMetaV.deepown_l (KObjectV.objectmeta_ptr l o) m dq
  }}}.
Proof.
  wp_start as "H". iNamed "H".
  destruct o; simpl in Hi; destruct Hi as [-> _]; wp_method_call;
    wp_pures; wp_apply (wp_GetGenerateName_deepown with "[$Hmeta]");
    iIntros "Hmeta"; iApply "HΦ"; iFrame.
Qed.

Lemma wp_GetUID_deepown_kobject i l o m dq:
  {{{ is_pkg_init code.k8s_io.apimachinery.pkg.apis.meta.v1.pkg_id.v1 ∗
      "%Hi" ∷ ⌜ KObjectV.valid_interface i l o ⌝ ∗
      "Hmeta" ∷ ObjectMetaV.deepown_l (KObjectV.objectmeta_ptr l o) m dq
  }}}
    #(methods i.(interface.ty) "GetUID" i.(interface.v)) #()
  {{{ RET #m.(ObjectMetaV.UID');
      ObjectMetaV.deepown_l (KObjectV.objectmeta_ptr l o) m dq
  }}}.
Proof.
  wp_start as "H". iNamed "H".
  destruct o; simpl in Hi; destruct Hi as [-> _]; wp_method_call;
    wp_pures; wp_apply (wp_GetUID_deepown with "[$Hmeta]");
    iIntros "Hmeta"; iApply "HΦ"; iFrame.
Qed.

Lemma wp_GetResourceVersion_deepown_kobject i l o m dq:
  {{{ is_pkg_init code.k8s_io.apimachinery.pkg.apis.meta.v1.pkg_id.v1 ∗
      "%Hi" ∷ ⌜ KObjectV.valid_interface i l o ⌝ ∗
      "Hmeta" ∷ ObjectMetaV.deepown_l (KObjectV.objectmeta_ptr l o) m dq
  }}}
    #(methods i.(interface.ty) "GetResourceVersion" i.(interface.v)) #()
  {{{ RET #m.(ObjectMetaV.ResourceVersion');
      ObjectMetaV.deepown_l (KObjectV.objectmeta_ptr l o) m dq
  }}}.
Proof.
  wp_start as "H". iNamed "H".
  destruct o; simpl in Hi; destruct Hi as [-> _]; wp_method_call;
    wp_pures; wp_apply (wp_GetResourceVersion_deepown with "[$Hmeta]");
    iIntros "Hmeta"; iApply "HΦ"; iFrame.
Qed.

Lemma wp_SetName_deepown_kobject i l o m name:
  {{{ is_pkg_init code.k8s_io.apimachinery.pkg.apis.meta.v1.pkg_id.v1 ∗
      "%Hi" ∷ ⌜ KObjectV.valid_interface i l o ⌝ ∗
      "Hmeta" ∷ ObjectMetaV.deepown_l (KObjectV.objectmeta_ptr l o) m 1
  }}}
    #(methods i.(interface.ty) "SetName" i.(interface.v)) #name
  {{{ RET #();
      ObjectMetaV.deepown_l (KObjectV.objectmeta_ptr l o) (m <| ObjectMetaV.Name' := name |>) 1
  }}}.
Proof.
  wp_start as "H". iNamed "H".
  destruct o; simpl in Hi; destruct Hi as [-> _]; wp_method_call;
    wp_pures; wp_apply (wp_SetName_deepown with "[$Hmeta]");
    iIntros "Hmeta"; iApply "HΦ"; iFrame.
Qed.

Lemma wp_SetCreationTimestamp_deepown_kobject
    i l o m creation_timestamp pure_creation_timestamp:
  {{{ is_pkg_init code.k8s_io.apimachinery.pkg.apis.meta.v1.pkg_id.v1 ∗
      "%Hi" ∷ ⌜ KObjectV.valid_interface i l o ⌝ ∗
      "Hmeta" ∷ ObjectMetaV.deepown_l (KObjectV.objectmeta_ptr l o) m 1 ∗
      "Htime" ∷ TimeV.deepown creation_timestamp pure_creation_timestamp 1
  }}}
    #(methods i.(interface.ty) "SetCreationTimestamp" i.(interface.v))
      #creation_timestamp
  {{{ RET #();
      ObjectMetaV.deepown_l (KObjectV.objectmeta_ptr l o) (m <| ObjectMetaV.CreationTimestamp' := pure_creation_timestamp |>) 1
  }}}.
Proof.
  wp_start as "H". iNamed "H".
  destruct o; simpl in Hi; destruct Hi as [-> _]; wp_method_call;
    wp_pures;
    wp_apply (wp_SetCreationTimestamp_deepown with "[$Hmeta $Htime]");
    iIntros "Hmeta"; iApply "HΦ"; iFrame.
Qed.

Lemma wp_SetUID_deepown_kobject i l o m uid:
  {{{ is_pkg_init code.k8s_io.apimachinery.pkg.apis.meta.v1.pkg_id.v1 ∗
      "%Hi" ∷ ⌜ KObjectV.valid_interface i l o ⌝ ∗
      "Hmeta" ∷ ObjectMetaV.deepown_l (KObjectV.objectmeta_ptr l o) m 1
  }}}
    #(methods i.(interface.ty) "SetUID" i.(interface.v)) #uid
  {{{ RET #();
      ObjectMetaV.deepown_l (KObjectV.objectmeta_ptr l o) (m <| ObjectMetaV.UID' := uid |>) 1
  }}}.
Proof.
  wp_start as "H". iNamed "H".
  destruct o; simpl in Hi; destruct Hi as [-> _]; wp_method_call;
    wp_pures; wp_apply (wp_SetUID_deepown with "[$Hmeta]");
    iIntros "Hmeta"; iApply "HΦ"; iFrame.
Qed.

Lemma wp_SetResourceVersion_deepown_kobject i l o m resource_version:
  {{{ is_pkg_init code.k8s_io.apimachinery.pkg.apis.meta.v1.pkg_id.v1 ∗
      "%Hi" ∷ ⌜ KObjectV.valid_interface i l o ⌝ ∗
      "Hmeta" ∷ ObjectMetaV.deepown_l (KObjectV.objectmeta_ptr l o) m 1
  }}}
    #(methods i.(interface.ty) "SetResourceVersion" i.(interface.v))
      #resource_version
  {{{ RET #();
      ObjectMetaV.deepown_l (KObjectV.objectmeta_ptr l o) (m <| ObjectMetaV.ResourceVersion' := resource_version |>) 1
  }}}.
Proof.
  wp_start as "H". iNamed "H".
  destruct o; simpl in Hi; destruct Hi as [-> _]; wp_method_call;
    wp_pures; wp_apply (wp_SetResourceVersion_deepown with "[$Hmeta]");
    iIntros "Hmeta"; iApply "HΦ"; iFrame.
Qed.

Lemma wp_GetFinalizers_kobject i l o metadata_c dq:
  {{{ is_pkg_init code.k8s_io.apimachinery.pkg.apis.meta.v1.pkg_id.v1 ∗
      "%Hi" ∷ ⌜ KObjectV.valid_interface i l o ⌝ ∗
      "Hmeta" ∷ (KObjectV.objectmeta_ptr l o) ↦{dq} metadata_c
  }}}
    #(methods i.(interface.ty) "GetFinalizers" i.(interface.v)) #()
  {{{ RET #metadata_c.(code.k8s_io.apimachinery.pkg.apis.meta.v1.v1.ObjectMeta.Finalizers');
      (KObjectV.objectmeta_ptr l o) ↦{dq} metadata_c
  }}}.
Proof.
  wp_start as "H". iNamed "H".
  destruct o; simpl in Hi; destruct Hi as [-> _]; wp_method_call;
    wp_pures; wp_apply (wp_GetFinalizers with "[$Hmeta]");
    iIntros "Hmeta"; iApply "HΦ"; iFrame.
Qed.

Lemma wp_GetFinalizers_deepown_kobject i l o m dq:
  {{{ is_pkg_init code.k8s_io.apimachinery.pkg.apis.meta.v1.pkg_id.v1 ∗
      "%Hi" ∷ ⌜ KObjectV.valid_interface i l o ⌝ ∗
      "Hmeta" ∷ ObjectMetaV.deepown_l (KObjectV.objectmeta_ptr l o) m dq
  }}}
    #(methods i.(interface.ty) "GetFinalizers" i.(interface.v)) #()
  {{{ sl, RET #sl;
      ⌜ sl = slice.nil ↔ m.(ObjectMetaV.Finalizers') = None ⌝ ∗
      match m.(ObjectMetaV.Finalizers') with
      | Some vfs => ∃ cfs, sl ↦*{dq} cfs ∗ ⌜ cfs = vfs ⌝ ∗
          (sl ↦*{dq} cfs -∗ ObjectMetaV.deepown_l (KObjectV.objectmeta_ptr l o) m dq)
      | None => ObjectMetaV.deepown_l (KObjectV.objectmeta_ptr l o) m dq
      end
  }}}.
Proof.
  wp_start as "H". iNamed "H".
  destruct o; simpl in Hi; destruct Hi as [-> _]; wp_method_call;
    wp_pures; wp_apply (wp_GetFinalizers_deepown with "[$Hmeta]");
    iIntros (sl) "Hfinalizers"; iApply "HΦ"; iFrame.
Qed.

Lemma wp_GetOwnerReferences_deepown_kobject i l o m dq :
  {{{ is_pkg_init code.k8s_io.apimachinery.pkg.apis.meta.v1.pkg_id.v1 ∗
      "%Hi" ∷ ⌜ KObjectV.valid_interface i l o ⌝ ∗
      "Hmeta" ∷ ObjectMetaV.deepown_l (KObjectV.objectmeta_ptr l o) m dq
  }}}
    #(methods i.(interface.ty) "GetOwnerReferences" i.(interface.v)) #()
  {{{ sl, RET #sl;
      owner_references_borrow m dq sl (ObjectMetaV.deepown_l (KObjectV.objectmeta_ptr l o) m dq)
  }}}.
Proof.
  wp_start as "H". iNamed "H".
  destruct o; simpl in Hi; destruct Hi as [-> _]; wp_method_call;
    wp_pures;
    wp_apply (wp_GetOwnerReferences_deepown with "[$Hmeta]");
    iIntros (sl) "Hrefs"; iApply "HΦ"; iExact "Hrefs".
Qed.

Lemma get_owner_references_capability_kobject i l o dq :
  KObjectV.valid_interface i l o →
  ⊢ get_owner_references_capability
    (interface.ok i) (KObjectV.objectmeta o) dq
    (KObjectV.deepown_l l o dq).
Proof.
  intros Hi. unfold get_owner_references_capability.
  wp_start as "H". iNamed "H".
  iPoseProof (KObjectV.deepown_l_split with "Hown") as
    "(%Hl_nonnull & Htypemeta & Hmeta & Hspec & Hstatus)".
  wp_pures.
  iAssert (is_pkg_init code.k8s_io.apimachinery.pkg.apis.meta.v1.pkg_id.v1 ∗
           ⌜KObjectV.valid_interface i l o⌝ ∗
           ObjectMetaV.deepown_l (KObjectV.objectmeta_ptr l o) (KObjectV.objectmeta o) dq)%I
    with "[$Hmeta]" as "Hpre".
  { iFrame "#". done. }
  wp_apply (wp_GetOwnerReferences_deepown_kobject i l o with "Hpre").
  iIntros (sl) "Hrefs".
  iApply "HΦ".
  iEval (rewrite /owner_references_borrow) in "Hrefs".
  iEval (rewrite /owner_references_borrow).
  iDestruct "Hrefs" as "(%Hnil & Hrefs)".
  iSplit; first done.
  destruct (KObjectV.objectmeta o).(ObjectMetaV.OwnerReferences') as
    [refs|] eqn:Hrefs_some.
  - iDestruct "Hrefs" as (cs) "(Hsl & Hrefs & Hmeta_restore)".
    iExists cs. iFrame "Hsl Hrefs".
    iIntros (cs') "[Hsl Hrefs]".
    iDestruct ("Hmeta_restore" with "[$Hsl $Hrefs]") as "Hmeta".
    iApply (KObjectV.deepown_l_restore _ _ _ Hl_nonnull). iFrame.
  - iApply (KObjectV.deepown_l_restore _ _ _ Hl_nonnull). iFrame.
Qed.

Lemma wp_GetControllerOf_kobject_exact owner i l o dq :
  {{{ is_pkg_init code.k8s_io.apimachinery.pkg.apis.meta.v1.pkg_id.v1 ∗
      "%Howner" ∷ ⌜ owner = interface.ok i ⌝ ∗
      "%Hi" ∷ ⌜ KObjectV.valid_interface i l o ⌝ ∗
      "Hobj" ∷ KObjectV.deepown_l l o dq
  }}}
    @! code.k8s_io.apimachinery.pkg.apis.meta.v1.v1.GetControllerOf #owner
  {{{ controller_ref_l, RET #controller_ref_l;
      KObjectV.deepown_l l o dq ∗
      (⌜ controller_ref_l = null ∧ meta_parent_ref (KObjectV.objectmeta o) = None ⌝ ∨
       ∃ controller_ref,
         ⌜ controller_ref_l ≠ null ∧ is_controller_reference_of (KObjectV.objectmeta o) controller_ref ⌝ ∗
         OwnerReferenceV.deepown_l controller_ref_l controller_ref 1)
  }}}.
Proof.
  iIntros (Φ) "(#? & H) HΦ". iNamed "H". subst owner.
  iPoseProof (get_owner_references_capability_kobject i l o dq Hi) as
    "Hget".
  iAssert (is_pkg_init code.k8s_io.apimachinery.pkg.apis.meta.v1.pkg_id.v1 ∗
           get_owner_references_capability (interface.ok i) (KObjectV.objectmeta o) dq
             (KObjectV.deepown_l l o dq) ∗
           KObjectV.deepown_l l o dq)%I with "[$Hget $Hobj]" as "Hpre".
  { iFrame "#". }
  iApply (wp_GetControllerOf_general_exact with "Hpre").
  iExact "HΦ".
Qed.

Lemma wp_SetFinalizers_kobject i l o metadata_c finalizers:
  {{{ is_pkg_init code.k8s_io.apimachinery.pkg.apis.meta.v1.pkg_id.v1 ∗
      "%Hi" ∷ ⌜ KObjectV.valid_interface i l o ⌝ ∗
      "Hmeta" ∷ (KObjectV.objectmeta_ptr l o) ↦ metadata_c
  }}}
    #(methods i.(interface.ty) "SetFinalizers" i.(interface.v)) #finalizers
  {{{ RET #();
      (KObjectV.objectmeta_ptr l o) ↦
        (metadata_c <| code.k8s_io.apimachinery.pkg.apis.meta.v1.v1.ObjectMeta.Finalizers' := finalizers |>)
  }}}.
Proof.
  wp_start as "H". iNamed "H".
  destruct o; simpl in Hi; destruct Hi as [-> _]; wp_method_call;
    wp_pures; wp_apply (wp_SetFinalizers with "[$Hmeta]");
    iIntros "Hmeta"; iApply "HΦ"; iFrame.
Qed.

Lemma wp_GetDeletionGracePeriodSeconds_kobject i l o metadata_c dq:
  {{{ is_pkg_init code.k8s_io.apimachinery.pkg.apis.meta.v1.pkg_id.v1 ∗
      "%Hi" ∷ ⌜ KObjectV.valid_interface i l o ⌝ ∗
      "Hmeta" ∷ (KObjectV.objectmeta_ptr l o) ↦{dq} metadata_c
  }}}
    #(methods i.(interface.ty) "GetDeletionGracePeriodSeconds" i.(interface.v)) #()
  {{{ RET #metadata_c.(code.k8s_io.apimachinery.pkg.apis.meta.v1.v1.ObjectMeta.DeletionGracePeriodSeconds');
      (KObjectV.objectmeta_ptr l o) ↦{dq} metadata_c
  }}}.
Proof.
  wp_start as "H". iNamed "H".
  destruct o; simpl in Hi; destruct Hi as [-> _]; wp_method_call;
    wp_pures; wp_apply (wp_GetDeletionGracePeriodSeconds with "[$Hmeta]");
    iIntros "Hmeta"; iApply "HΦ"; iFrame.
Qed.

Lemma wp_SetDeletionGracePeriodSeconds_kobject i l o metadata_c dgps:
  {{{ is_pkg_init code.k8s_io.apimachinery.pkg.apis.meta.v1.pkg_id.v1 ∗
      "%Hi" ∷ ⌜ KObjectV.valid_interface i l o ⌝ ∗
      "Hmeta" ∷ (KObjectV.objectmeta_ptr l o) ↦ metadata_c
  }}}
    #(methods i.(interface.ty) "SetDeletionGracePeriodSeconds" i.(interface.v)) #dgps
  {{{ RET #();
      (KObjectV.objectmeta_ptr l o) ↦
        (metadata_c <| code.k8s_io.apimachinery.pkg.apis.meta.v1.v1.ObjectMeta.DeletionGracePeriodSeconds' := dgps |>)
  }}}.
Proof.
  wp_start as "H". iNamed "H".
  destruct o; simpl in Hi; destruct Hi as [-> _]; wp_method_call;
    wp_pures; wp_apply (wp_SetDeletionGracePeriodSeconds with "[$Hmeta]");
    iIntros "Hmeta"; iApply "HΦ"; iFrame.
Qed.

Lemma wp_GetDeletionTimestamp_kobject i l o metadata_c dq:
  {{{ is_pkg_init code.k8s_io.apimachinery.pkg.apis.meta.v1.pkg_id.v1 ∗
      "%Hi" ∷ ⌜ KObjectV.valid_interface i l o ⌝ ∗
      "Hmeta" ∷ (KObjectV.objectmeta_ptr l o) ↦{dq} metadata_c
  }}}
    #(methods i.(interface.ty) "GetDeletionTimestamp" i.(interface.v)) #()
  {{{ RET #metadata_c.(code.k8s_io.apimachinery.pkg.apis.meta.v1.v1.ObjectMeta.DeletionTimestamp');
      (KObjectV.objectmeta_ptr l o) ↦{dq} metadata_c
  }}}.
Proof.
  wp_start as "H". iNamed "H".
  destruct o; simpl in Hi; destruct Hi as [-> _]; wp_method_call;
    wp_pures; wp_apply (wp_GetDeletionTimestamp with "[$Hmeta]");
    iIntros "Hmeta"; iApply "HΦ"; iFrame.
Qed.

Lemma wp_SetDeletionTimestamp_kobject i l o metadata_c deletion_timestamp:
  {{{ is_pkg_init code.k8s_io.apimachinery.pkg.apis.meta.v1.pkg_id.v1 ∗
      "%Hi" ∷ ⌜ KObjectV.valid_interface i l o ⌝ ∗
      "Hmeta" ∷ (KObjectV.objectmeta_ptr l o) ↦ metadata_c
  }}}
    #(methods i.(interface.ty) "SetDeletionTimestamp" i.(interface.v)) #deletion_timestamp
  {{{ RET #();
      (KObjectV.objectmeta_ptr l o) ↦
        (metadata_c <| code.k8s_io.apimachinery.pkg.apis.meta.v1.v1.ObjectMeta.DeletionTimestamp' := deletion_timestamp |>)
  }}}.
Proof.
  wp_start as "H". iNamed "H".
  destruct o; simpl in Hi; destruct Hi as [-> _]; wp_method_call;
    wp_pures; wp_apply (wp_SetDeletionTimestamp with "[$Hmeta]");
    iIntros "Hmeta"; iApply "HΦ"; iFrame.
Qed.

Lemma wp_GetGeneration_kobject i l o metadata_c dq:
  {{{ is_pkg_init code.k8s_io.apimachinery.pkg.apis.meta.v1.pkg_id.v1 ∗
      "%Hi" ∷ ⌜ KObjectV.valid_interface i l o ⌝ ∗
      "Hmeta" ∷ (KObjectV.objectmeta_ptr l o) ↦{dq} metadata_c
  }}}
    #(methods i.(interface.ty) "GetGeneration" i.(interface.v)) #()
  {{{ RET #metadata_c.(code.k8s_io.apimachinery.pkg.apis.meta.v1.v1.ObjectMeta.Generation');
      (KObjectV.objectmeta_ptr l o) ↦{dq} metadata_c
  }}}.
Proof.
  wp_start as "H". iNamed "H".
  destruct o; simpl in Hi; destruct Hi as [-> _]; wp_method_call;
    wp_pures; wp_apply (wp_GetGeneration with "[$Hmeta]");
    iIntros "Hmeta"; iApply "HΦ"; iFrame.
Qed.

Lemma wp_SetGeneration_kobject i l o metadata_c generation:
  {{{ is_pkg_init code.k8s_io.apimachinery.pkg.apis.meta.v1.pkg_id.v1 ∗
      "%Hi" ∷ ⌜ KObjectV.valid_interface i l o ⌝ ∗
      "Hmeta" ∷ (KObjectV.objectmeta_ptr l o) ↦ metadata_c
  }}}
    #(methods i.(interface.ty) "SetGeneration" i.(interface.v)) #generation
  {{{ RET #();
      (KObjectV.objectmeta_ptr l o) ↦
        (metadata_c <| code.k8s_io.apimachinery.pkg.apis.meta.v1.v1.ObjectMeta.Generation' := generation |>)
  }}}.
Proof.
  wp_start as "H". iNamed "H".
  destruct o; simpl in Hi; destruct Hi as [-> _]; wp_method_call;
    wp_pures; wp_apply (wp_SetGeneration with "[$Hmeta]");
    iIntros "Hmeta"; iApply "HΦ"; iFrame.
Qed.

End proof.
