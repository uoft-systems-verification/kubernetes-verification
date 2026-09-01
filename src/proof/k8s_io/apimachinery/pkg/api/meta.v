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
  {{{ "Hinit" ∷ is_pkg_init code.k8s_io.apimachinery.pkg.api.meta.pkg_id.meta ∗
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
  {{{ "Hinit" ∷ is_pkg_init code.k8s_io.apimachinery.pkg.apis.meta.v1.pkg_id.v1 ∗
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
    wp_pures; wp_apply (wp_GetLabels_deepown with "[$Hinit $Hmeta]");
    iIntros (labels_l) "Hlabels"; iApply "HΦ"; iFrame.
Qed.

Lemma wp_GetName_deepown_kobject i l o m dq:
  {{{ "Hinit" ∷ is_pkg_init code.k8s_io.apimachinery.pkg.apis.meta.v1.pkg_id.v1 ∗
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
    wp_pures; wp_apply (wp_GetName_deepown with "[$Hinit $Hmeta]");
    iIntros "Hmeta"; iApply "HΦ"; iFrame.
Qed.

Lemma wp_GetGenerateName_deepown_kobject i l o m dq:
  {{{ "Hinit" ∷ is_pkg_init code.k8s_io.apimachinery.pkg.apis.meta.v1.pkg_id.v1 ∗
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
    wp_pures; wp_apply (wp_GetGenerateName_deepown with "[$Hinit $Hmeta]");
    iIntros "Hmeta"; iApply "HΦ"; iFrame.
Qed.

Lemma wp_GetUID_deepown_kobject i l o m dq:
  {{{ "Hinit" ∷ is_pkg_init code.k8s_io.apimachinery.pkg.apis.meta.v1.pkg_id.v1 ∗
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
    wp_pures; wp_apply (wp_GetUID_deepown with "[$Hinit $Hmeta]");
    iIntros "Hmeta"; iApply "HΦ"; iFrame.
Qed.

Lemma wp_GetResourceVersion_deepown_kobject i l o m dq:
  {{{ "Hinit" ∷ is_pkg_init code.k8s_io.apimachinery.pkg.apis.meta.v1.pkg_id.v1 ∗
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
    wp_pures; wp_apply (wp_GetResourceVersion_deepown with "[$Hinit $Hmeta]");
    iIntros "Hmeta"; iApply "HΦ"; iFrame.
Qed.

Lemma wp_SetName_deepown_kobject i l o m name:
  {{{ "Hinit" ∷ is_pkg_init code.k8s_io.apimachinery.pkg.apis.meta.v1.pkg_id.v1 ∗
      "%Hi" ∷ ⌜ KObjectV.valid_interface i l o ⌝ ∗
      "Hmeta" ∷ ObjectMetaV.deepown_l (KObjectV.objectmeta_ptr l o) m 1
  }}}
    #(methods i.(interface.ty) "SetName" i.(interface.v)) #name
  {{{ RET #();
      ObjectMetaV.deepown_l (KObjectV.objectmeta_ptr l o)
        (m <| ObjectMetaV.Name' := name |>) 1
  }}}.
Proof.
  wp_start as "H". iNamed "H".
  destruct o; simpl in Hi; destruct Hi as [-> _]; wp_method_call;
    wp_pures; wp_apply (wp_SetName_deepown with "[$Hinit $Hmeta]");
    iIntros "Hmeta"; iApply "HΦ"; iFrame.
Qed.

Lemma wp_SetCreationTimestamp_deepown_kobject
    i l o m creation_timestamp pure_creation_timestamp:
  {{{ "Hinit" ∷ is_pkg_init code.k8s_io.apimachinery.pkg.apis.meta.v1.pkg_id.v1 ∗
      "%Hi" ∷ ⌜ KObjectV.valid_interface i l o ⌝ ∗
      "Hmeta" ∷ ObjectMetaV.deepown_l (KObjectV.objectmeta_ptr l o) m 1 ∗
      "Htime" ∷ TimeV.deepown creation_timestamp pure_creation_timestamp 1
  }}}
    #(methods i.(interface.ty) "SetCreationTimestamp" i.(interface.v))
      #creation_timestamp
  {{{ RET #();
      ObjectMetaV.deepown_l (KObjectV.objectmeta_ptr l o)
        (m <| ObjectMetaV.CreationTimestamp' := pure_creation_timestamp |>) 1
  }}}.
Proof.
  wp_start as "H". iNamed "H".
  destruct o; simpl in Hi; destruct Hi as [-> _]; wp_method_call;
    wp_pures;
    wp_apply (wp_SetCreationTimestamp_deepown with "[$Hinit $Hmeta $Htime]");
    iIntros "Hmeta"; iApply "HΦ"; iFrame.
Qed.

Lemma wp_SetUID_deepown_kobject i l o m uid:
  {{{ "Hinit" ∷ is_pkg_init code.k8s_io.apimachinery.pkg.apis.meta.v1.pkg_id.v1 ∗
      "%Hi" ∷ ⌜ KObjectV.valid_interface i l o ⌝ ∗
      "Hmeta" ∷ ObjectMetaV.deepown_l (KObjectV.objectmeta_ptr l o) m 1
  }}}
    #(methods i.(interface.ty) "SetUID" i.(interface.v)) #uid
  {{{ RET #();
      ObjectMetaV.deepown_l (KObjectV.objectmeta_ptr l o)
        (m <| ObjectMetaV.UID' := uid |>) 1
  }}}.
Proof.
  wp_start as "H". iNamed "H".
  destruct o; simpl in Hi; destruct Hi as [-> _]; wp_method_call;
    wp_pures; wp_apply (wp_SetUID_deepown with "[$Hinit $Hmeta]");
    iIntros "Hmeta"; iApply "HΦ"; iFrame.
Qed.

Lemma wp_SetResourceVersion_deepown_kobject i l o m resource_version:
  {{{ "Hinit" ∷ is_pkg_init code.k8s_io.apimachinery.pkg.apis.meta.v1.pkg_id.v1 ∗
      "%Hi" ∷ ⌜ KObjectV.valid_interface i l o ⌝ ∗
      "Hmeta" ∷ ObjectMetaV.deepown_l (KObjectV.objectmeta_ptr l o) m 1
  }}}
    #(methods i.(interface.ty) "SetResourceVersion" i.(interface.v))
      #resource_version
  {{{ RET #();
      ObjectMetaV.deepown_l (KObjectV.objectmeta_ptr l o)
        (m <| ObjectMetaV.ResourceVersion' := resource_version |>) 1
  }}}.
Proof.
  wp_start as "H". iNamed "H".
  destruct o; simpl in Hi; destruct Hi as [-> _]; wp_method_call;
    wp_pures; wp_apply (wp_SetResourceVersion_deepown with "[$Hinit $Hmeta]");
    iIntros "Hmeta"; iApply "HΦ"; iFrame.
Qed.

Lemma wp_GetFinalizers_kobject i l o metadata_c dq:
  {{{ "Hinit" ∷ is_pkg_init code.k8s_io.apimachinery.pkg.apis.meta.v1.pkg_id.v1 ∗
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
    wp_pures; wp_apply (wp_GetFinalizers with "[$Hinit $Hmeta]");
    iIntros "Hmeta"; iApply "HΦ"; iFrame.
Qed.

Lemma wp_GetFinalizers_deepown_kobject i l o m dq:
  {{{ "Hinit" ∷ is_pkg_init code.k8s_io.apimachinery.pkg.apis.meta.v1.pkg_id.v1 ∗
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
    wp_pures; wp_apply (wp_GetFinalizers_deepown with "[$Hinit $Hmeta]");
    iIntros (sl) "Hfinalizers"; iApply "HΦ"; iFrame.
Qed.

Lemma wp_SetFinalizers_kobject i l o metadata_c finalizers:
  {{{ "Hinit" ∷ is_pkg_init code.k8s_io.apimachinery.pkg.apis.meta.v1.pkg_id.v1 ∗
      "%Hi" ∷ ⌜ KObjectV.valid_interface i l o ⌝ ∗
      "Hmeta" ∷ (KObjectV.objectmeta_ptr l o) ↦ metadata_c
  }}}
    #(methods i.(interface.ty) "SetFinalizers" i.(interface.v)) #finalizers
  {{{ RET #();
      (KObjectV.objectmeta_ptr l o) ↦
        (metadata_c <|
          code.k8s_io.apimachinery.pkg.apis.meta.v1.v1.ObjectMeta.Finalizers' := finalizers |>)
  }}}.
Proof.
  wp_start as "H". iNamed "H".
  destruct o; simpl in Hi; destruct Hi as [-> _]; wp_method_call;
    wp_pures; wp_apply (wp_SetFinalizers with "[$Hinit $Hmeta]");
    iIntros "Hmeta"; iApply "HΦ"; iFrame.
Qed.

Lemma wp_GetDeletionGracePeriodSeconds_kobject i l o metadata_c dq:
  {{{ "Hinit" ∷ is_pkg_init code.k8s_io.apimachinery.pkg.apis.meta.v1.pkg_id.v1 ∗
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
    wp_pures; wp_apply (wp_GetDeletionGracePeriodSeconds with "[$Hinit $Hmeta]");
    iIntros "Hmeta"; iApply "HΦ"; iFrame.
Qed.

Lemma wp_SetDeletionGracePeriodSeconds_kobject i l o metadata_c dgps:
  {{{ "Hinit" ∷ is_pkg_init code.k8s_io.apimachinery.pkg.apis.meta.v1.pkg_id.v1 ∗
      "%Hi" ∷ ⌜ KObjectV.valid_interface i l o ⌝ ∗
      "Hmeta" ∷ (KObjectV.objectmeta_ptr l o) ↦ metadata_c
  }}}
    #(methods i.(interface.ty) "SetDeletionGracePeriodSeconds" i.(interface.v)) #dgps
  {{{ RET #();
      (KObjectV.objectmeta_ptr l o) ↦
        (metadata_c <|
          code.k8s_io.apimachinery.pkg.apis.meta.v1.v1.ObjectMeta.DeletionGracePeriodSeconds' := dgps |>)
  }}}.
Proof.
  wp_start as "H". iNamed "H".
  destruct o; simpl in Hi; destruct Hi as [-> _]; wp_method_call;
    wp_pures; wp_apply (wp_SetDeletionGracePeriodSeconds with "[$Hinit $Hmeta]");
    iIntros "Hmeta"; iApply "HΦ"; iFrame.
Qed.

Lemma wp_GetDeletionTimestamp_kobject i l o metadata_c dq:
  {{{ "Hinit" ∷ is_pkg_init code.k8s_io.apimachinery.pkg.apis.meta.v1.pkg_id.v1 ∗
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
    wp_pures; wp_apply (wp_GetDeletionTimestamp with "[$Hinit $Hmeta]");
    iIntros "Hmeta"; iApply "HΦ"; iFrame.
Qed.

Lemma wp_SetDeletionTimestamp_kobject i l o metadata_c deletion_timestamp:
  {{{ "Hinit" ∷ is_pkg_init code.k8s_io.apimachinery.pkg.apis.meta.v1.pkg_id.v1 ∗
      "%Hi" ∷ ⌜ KObjectV.valid_interface i l o ⌝ ∗
      "Hmeta" ∷ (KObjectV.objectmeta_ptr l o) ↦ metadata_c
  }}}
    #(methods i.(interface.ty) "SetDeletionTimestamp" i.(interface.v)) #deletion_timestamp
  {{{ RET #();
      (KObjectV.objectmeta_ptr l o) ↦
        (metadata_c <|
          code.k8s_io.apimachinery.pkg.apis.meta.v1.v1.ObjectMeta.DeletionTimestamp' := deletion_timestamp |>)
  }}}.
Proof.
  wp_start as "H". iNamed "H".
  destruct o; simpl in Hi; destruct Hi as [-> _]; wp_method_call;
    wp_pures; wp_apply (wp_SetDeletionTimestamp with "[$Hinit $Hmeta]");
    iIntros "Hmeta"; iApply "HΦ"; iFrame.
Qed.

Lemma wp_GetGeneration_kobject i l o metadata_c dq:
  {{{ "Hinit" ∷ is_pkg_init code.k8s_io.apimachinery.pkg.apis.meta.v1.pkg_id.v1 ∗
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
    wp_pures; wp_apply (wp_GetGeneration with "[$Hinit $Hmeta]");
    iIntros "Hmeta"; iApply "HΦ"; iFrame.
Qed.

Lemma wp_SetGeneration_kobject i l o metadata_c generation:
  {{{ "Hinit" ∷ is_pkg_init code.k8s_io.apimachinery.pkg.apis.meta.v1.pkg_id.v1 ∗
      "%Hi" ∷ ⌜ KObjectV.valid_interface i l o ⌝ ∗
      "Hmeta" ∷ (KObjectV.objectmeta_ptr l o) ↦ metadata_c
  }}}
    #(methods i.(interface.ty) "SetGeneration" i.(interface.v)) #generation
  {{{ RET #();
      (KObjectV.objectmeta_ptr l o) ↦
        (metadata_c <|
          code.k8s_io.apimachinery.pkg.apis.meta.v1.v1.ObjectMeta.Generation' := generation |>)
  }}}.
Proof.
  wp_start as "H". iNamed "H".
  destruct o; simpl in Hi; destruct Hi as [-> _]; wp_method_call;
    wp_pures; wp_apply (wp_SetGeneration with "[$Hinit $Hmeta]");
    iIntros "Hmeta"; iApply "HΦ"; iFrame.
Qed.

End proof.
