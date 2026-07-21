From New.proof Require Import prelude empty_ffi.
From New.proof.map Require Import for_range.
From New.proof.kubernetes_types Require Export prelude.
From New.proof.k8s_io.kubernetes.pkg Require Export controller_init.
From New.proof.k8s_io.apimachinery.pkg.api Require Import meta.
From New.proof.k8s_io.apimachinery.pkg.apis.meta Require Import v1.

Section proof.
Context `{hG: !heapGS Σ} `{!ffi_semantics _ _}.
Context {sem : go.Semantics}
  {package_sem : controller.Assumptions}
  {apps_v1_sem : code.k8s_io.api.apps.v1.v1.Assumptions}
  {controller_core_v1_sem : core_v1.Assumptions}
  {controller_meta_v1_sem : meta_v1.Assumptions}.
Collection W := sem + package_sem.
Local Set Default Proof Using "All".

#[local] Existing Instance controller_core_v1_sem.
#[local] Existing Instance controller_meta_v1_sem.

Definition pod_from_template (template : PodTemplateSpecV.t) (pod : PodV.t) : Prop :=
  pod.(PodV.Spec') = template.(PodTemplateSpecV.Spec') ∧
  pod.(PodV.ObjectMeta').(ObjectMetaV.Labels') =
    Some (default ∅ template.(PodTemplateSpecV.ObjectMeta').(ObjectMetaV.Labels')) ∧
  pod.(PodV.ObjectMeta').(ObjectMetaV.Annotations') =
    Some (default ∅ template.(PodTemplateSpecV.ObjectMeta').(ObjectMetaV.Annotations')) ∧
  pod.(PodV.ObjectMeta').(ObjectMetaV.Finalizers') =
    Some (default [] template.(PodTemplateSpecV.ObjectMeta').(ObjectMetaV.Finalizers')).

Definition generated_pod_meta (template : PodTemplateSpecV.t)
    (parent_name : go_string) (owners : option (list OwnerReferenceV.t)) :
    ObjectMetaV.t :=
  ObjectMetaV.mk ""%go (parent_name ++ "-"%go) ""%go ""%go ""%go ""%go
    (W64 0) TimeV.zero None None
    (Some (default ∅ template.(PodTemplateSpecV.ObjectMeta').(ObjectMetaV.Labels')))
    (Some (default ∅
      template.(PodTemplateSpecV.ObjectMeta').(ObjectMetaV.Annotations')))
    owners
    (Some (default []
      template.(PodTemplateSpecV.ObjectMeta').(ObjectMetaV.Finalizers')))
    None.

Definition generated_pod (template : PodTemplateSpecV.t)
    (parent_name : go_string) (owners : option (list OwnerReferenceV.t)) :
    PodV.t :=
  PodV.mk (zero_val v1.TypeMeta.t)
    (generated_pod_meta template parent_name owners)
    template.(PodTemplateSpecV.Spec') PodStatusV.zero.

Lemma wp_getPodsLabelSet template_l template dq :
  {{{ "Hinit" ∷ is_pkg_init controller ∗
      "Htemplate" ∷ PodTemplateSpecV.deepown_l template_l template dq
  }}}
  @! controller.getPodsLabelSet #template_l
  {{{ labels_l, RET #labels_l;
      PodTemplateSpecV.deepown_l template_l template dq ∗
      labels_l ↦$ default ∅
        template.(PodTemplateSpecV.ObjectMeta').(ObjectMetaV.Labels')
  }}}.
Proof. Admitted.
(*
  wp_start as "H". iNamed "H".
  iDestruct "Htemplate" as (template_c) "[Htemplate_l Htemplate]".
  iNamedPrefix "Htemplate" "Htemplate_".
  iNamedPrefix "Htemplate_Hdeepown_objectmeta" "Hmeta_".
  wp_auto.
  rewrite exception_do_unseal /exception_do_def.
  wp_bind (#(functions go.make1 [go.MapType go.string go.string]) #())%E.
  wp_apply (wp_map_make1 (K:=go_string) (V:=go_string) go.string go.string).
  iIntros (labels_l) "Hlabels".
  Timeout 10 wp_pures.
  Timeout 10 wp_store.
  Timeout 10 wp_pures.
  Timeout 10 wp_load.
  Timeout 10 wp_pures.
  Timeout 10 iDestruct (access_strict
      (A:=(template_l.[v1.PodTemplateSpec.t, "ObjectMeta"] ↦{dq}
        template_c.(v1.PodTemplateSpec.ObjectMeta')))
      (A':=(template_l.[v1.PodTemplateSpec.t, "ObjectMeta"] ↦{dq}
        template_c.(v1.PodTemplateSpec.ObjectMeta')))
      with "Htemplate_l") as "[Hobjectmeta Hclose_template]".
  Timeout 10 iDestruct (access_strict
      (A:=(template_l.[v1.PodTemplateSpec.t, "ObjectMeta"].[v1.ObjectMeta.t, "Labels"]
        ↦{dq} template_c.(v1.PodTemplateSpec.ObjectMeta').(v1.ObjectMeta.Labels')))
      (A':=(template_l.[v1.PodTemplateSpec.t, "ObjectMeta"].[v1.ObjectMeta.t, "Labels"]
        ↦{dq} template_c.(v1.PodTemplateSpec.ObjectMeta').(v1.ObjectMeta.Labels')))
      with "Hobjectmeta") as "[Hlabels_field Hclose_objectmeta]".
  Timeout 10 wp_apply (wp_load with "Hlabels_field").
  iIntros "Hlabels_field".
  iPoseProof ("Hclose_objectmeta" with "Hlabels_field") as "Hobjectmeta".
  iPoseProof ("Hclose_template" with "Hobjectmeta") as "Htemplate_l".
  Timeout 10 wp_pures.
  Timeout 10 wp_alloc v_ptr as "v".
  Timeout 10 wp_pures.
  Timeout 10 wp_alloc k_ptr as "k".
  Timeout 10 wp_pures.
  destruct template.(PodTemplateSpecV.ObjectMeta').(ObjectMetaV.Labels')
    as [labels|] eqn:Hlabels_opt.
  - iDestruct "Hmeta_Hdeepown_labels_some" as (labels_c)
      "[Hlabels_src %Hlabels_c]".
    subst labels_c.
    wp_apply (wp_map_for_range_return_func (key_type:=go.string)
      (λ (keys : list go_string) i,
        ∃ (last_value last_key : go_string),
          "v" ∷ v_ptr ↦ last_value ∗
          "k" ∷ k_ptr ↦ last_key ∗
          "desiredLabels" ∷ desiredLabels_ptr ↦ labels_l ∗
          "Hlabels" ∷ labels_l ↦$ map_prefix keys i labels)%I
      with "Hlabels_src").
    { done. }
    iIntros (keys) "%Hkeys".
    iSplitL "v k desiredLabels Hlabels".
    { iExists ""%go, ""%go. iFrame.
      rewrite map_prefix_empty. iFrame. }
    iSplitL "".
    { iModIntro. iIntros (i key value) "%Hiter Hloop".
      destruct Hkeys as [Hkeys_dom [Hkeys_len Hkeys_nodup]].
      destruct Hiter as [Hi_bounds [Hkey_lookup Hvalue_lookup]].
      destruct Hi_bounds as [Hi_nonneg Hi_upper].
      iDestruct "Hloop" as (last_value last_key)
        "(v & k & desiredLabels & Hlabels)".
      wp_pures.
      simpl subst'.
      Timeout 10 wp_auto.
      wp_apply (wp_map_insert (K:=go_string) (V:=go_string)
        go.string labels_l (map_prefix keys i labels) key value
        with "Hlabels") as "Hlabels".
      iRight. iSplit; [done|].
      iExists value, key. iFrame.
      rewrite -map_prefix_insert; done. }
    iIntros "Hlabels_src Hloop".
    iDestruct "Hloop" as (last_value last_key)
      "(v & k & desiredLabels & Hlabels)".
    destruct Hkeys as [Hkeys_dom [Hkeys_len Hkeys_nodup]].
    rewrite (map_prefix_all keys labels Hkeys_dom Hkeys_len).
    Timeout 10 wp_auto.
    rewrite return_val_unseal /return_val_def. Timeout 10 wp_auto.
    iAssert ((match template.(PodTemplateSpecV.ObjectMeta').(ObjectMetaV.Labels') with
      | Some labels' => ∃ labels_c,
          template_c.(v1.PodTemplateSpec.ObjectMeta').(v1.ObjectMeta.Labels') ↦${dq} labels_c ∗
          ⌜labels_c = labels'⌝
      | None => True
      end)%I) with "[Hlabels_src]" as "Hmeta_Hdeepown_labels_some".
    { rewrite Hlabels_opt. iExists labels.
      iSplitL "Hlabels_src"; [iExact "Hlabels_src"|done]. }
    iCombineNamed "Hmeta_*" as "Hobjectmeta".
    iAssert (ObjectMetaV.deepown
        template_c.(v1.PodTemplateSpec.ObjectMeta')
        template.(PodTemplateSpecV.ObjectMeta') dq)
      with "[Hobjectmeta]" as "Hobjectmeta".
    { rewrite /ObjectMetaV.deepown Hlabels_opt /=. iNamed "Hobjectmeta".
      iFrame "Hmeta_Hdeepown_creationtimestamp
        Hmeta_Hdeepown_deletiontimestamp_some
        Hmeta_Hdeepown_deletiongraceperiodseconds_some
        Hmeta_Hdeepown_labels_some Hmeta_Hdeepown_annotations_some
        Hmeta_Hdeepown_ownerreferences_some Hmeta_Hdeepown_finalizers_some
        Hmeta_Hdeepown_managedfields_some".
      iPureIntro. Timeout 10 naive_solver. }
    iApply ("HΦ" $! labels_l). iFrame "Hlabels".
    iExists template_c. iFrame "Htemplate_l".
    rewrite /PodTemplateSpecV.deepown. iFrame.
  - assert (template_c.(v1.PodTemplateSpec.ObjectMeta').(v1.ObjectMeta.Labels') =
        map.nil) as Hlabels_nil.
    { apply Hmeta_Hdeepown_labels_none. done. }
    rewrite Hlabels_nil.
    Timeout 10 wp_pures.
    Timeout 10 wp_apply (wp_map_for_range_nil go.string go.string).
    Timeout 10 wp_pures.
    rewrite return_val_unseal /return_val_def.
    Timeout 10 wp_pures.
    iCombineNamed "Hmeta_*" as "Hobjectmeta".
    iAssert (ObjectMetaV.deepown
        template_c.(v1.PodTemplateSpec.ObjectMeta')
        template.(PodTemplateSpecV.ObjectMeta') dq)
      with "[Hobjectmeta]" as "Hobjectmeta".
    { rewrite /ObjectMetaV.deepown Hlabels_opt /=. iNamed "Hobjectmeta".
      iFrame "Hmeta_Hdeepown_creationtimestamp
        Hmeta_Hdeepown_deletiontimestamp_some
        Hmeta_Hdeepown_deletiongraceperiodseconds_some
        Hmeta_Hdeepown_annotations_some
        Hmeta_Hdeepown_ownerreferences_some Hmeta_Hdeepown_finalizers_some
        Hmeta_Hdeepown_managedfields_some".
      iPureIntro. Timeout 10 naive_solver. }
    iApply ("HΦ" $! labels_l).
    iFrame "Hlabels".
    iExists template_c. iFrame "Htemplate_l".
    rewrite /PodTemplateSpecV.deepown. iFrame.
Qed.
*)

Lemma wp_getPodsFinalizers template_l template dq :
  {{{ is_pkg_init controller ∗
      PodTemplateSpecV.deepown_l template_l template dq
  }}}
  @! controller.getPodsFinalizers #template_l
  {{{ finalizers_sl, RET #finalizers_sl;
      PodTemplateSpecV.deepown_l template_l template dq ∗
      finalizers_sl ↦* default []
        template.(PodTemplateSpecV.ObjectMeta').(ObjectMetaV.Finalizers') ∗
      ⌜ finalizers_sl ≠ slice.nil ⌝
  }}}.
Proof. Admitted.

Lemma wp_getPodsAnnotationSet template_l template dq :
  {{{ is_pkg_init controller ∗
      PodTemplateSpecV.deepown_l template_l template dq
  }}}
  @! controller.getPodsAnnotationSet #template_l
  {{{ annotations_l, RET #annotations_l;
      PodTemplateSpecV.deepown_l template_l template dq ∗
      annotations_l ↦$ default ∅
        template.(PodTemplateSpecV.ObjectMeta').(ObjectMetaV.Annotations')
  }}}.
Proof. Admitted.

Lemma wp_getPodsPrefix controller_name :
  {{{ is_pkg_init controller ∗
      ⌜ valid_dns1123_subdomain controller_name ⌝
  }}}
  @! controller.getPodsPrefix #controller_name
  {{{ RET #(controller_name ++ "-"%go);
      ⌜ valid_generate_name PodV.kind (controller_name ++ "-"%go) ⌝
  }}}.
Proof. Admitted.

(* PodSpec.DeepCopy is generated by Kubernetes' deepcopy generator and is not
   translated in this package.  This is its ownership-preserving contract. *)
Lemma wp_PodSpec__DeepCopy spec_l spec dq :
  {{{ is_pkg_init controller ∗
      PodSpecV.deepown_l spec_l spec dq
  }}}
  spec_l @! (go.PointerType v1.PodSpec) @! "DeepCopy" #()
  {{{ spec_copy_l, RET #spec_copy_l;
      PodSpecV.deepown_l spec_copy_l spec 1 ∗
      PodSpecV.deepown_l spec_l spec dq
  }}}.
Proof. Admitted.

Lemma wp_PodControllerIndexKey namespace ownerReference owner_reference dq:
  {{{ is_pkg_init controller ∗
      ownerReference ↦{dq} owner_reference
  }}}
  @! controller.PodControllerIndexKey #namespace #ownerReference
  {{{ index_key, RET #index_key;
      ⌜ index_key = namespace ++ "/"%go ++ 
        owner_reference.(v1.OwnerReference.Kind') ++ "/"%go ++ 
        owner_reference.(v1.OwnerReference.Name') ++ "/"%go ++
        owner_reference.(v1.OwnerReference.UID')⌝
  }}}.
Proof.
Admitted.

Lemma wp_GetPodFromTemplate template_l obj controller_ref_l template_dq
    parent_dq template parent_l parent controller_ref :
  {{{ "Hinit" ∷ is_pkg_init controller ∗
      "Htemplate" ∷ PodTemplateSpecV.deepown_l template_l template template_dq ∗
      "Hparent_meta" ∷ ObjectMetaV.deepown_l
        (KObjectV.objectmeta_ptr parent_l parent)
        (KObjectV.objectmeta parent) parent_dq ∗
      "Hcontroller_ref" ∷
        (match controller_ref with
        | Some ref => OwnerReferenceV.deepown_l controller_ref_l ref 1
        | None => ⌜ controller_ref_l = null ⌝
        end) ∗
      "%Hparent_interface" ∷
        ⌜ KObjectV.valid_interface obj parent_l parent ⌝ ∗
      "%Hparent_name_valid" ∷
        ⌜ valid_dns1123_subdomain
            (KObjectV.objectmeta parent).(ObjectMetaV.Name') ⌝ ∗
      "%Hcontroller_ref_is_parent" ∷
        ⌜ match controller_ref with
          | Some ref =>
              OwnerReferenceV.refers_to_controller ref
                (KObjectV.kind parent)
                (KObjectV.objectmeta parent).(ObjectMetaV.Name')
                (KObjectV.objectmeta parent).(ObjectMetaV.UID')
          | None => True
          end ⌝
  }}}
  @! controller.GetPodFromTemplate #template_l #(interface.ok obj) #controller_ref_l
  {{{ pod_l pod, RET (#pod_l, #interface.nil);
      "Hpod" ∷ PodV.deepown_l pod_l pod 1 ∗
      "%Howner_references" ∷
        ⌜ match controller_ref with
          | Some _ =>
              obj_parent_ref_is (KObjectV.Pod pod) (KObjectV.kind parent)
                (KObjectV.objectmeta parent).(ObjectMetaV.Name')
                (KObjectV.objectmeta parent).(ObjectMetaV.UID')
          | None =>
              pod.(PodV.ObjectMeta').(ObjectMetaV.OwnerReferences') = None
          end ⌝ ∗
      "%Hgenerate_name" ∷
        ⌜ pod.(PodV.ObjectMeta').(ObjectMetaV.GenerateName') =
            (KObjectV.objectmeta parent).(ObjectMetaV.Name') ++ "-"%go ⌝ ∗
      "%Hgenerate_name_valid" ∷
        ⌜ valid_generate_name PodV.kind
            pod.(PodV.ObjectMeta').(ObjectMetaV.GenerateName') ⌝ ∗
      "%Hdeletion_timestamp" ∷
        ⌜ pod.(PodV.ObjectMeta').(ObjectMetaV.DeletionTimestamp') = None ⌝ ∗
      "%Hfrom_template" ∷ ⌜ pod_from_template template pod ⌝ ∗
      "Htemplate" ∷
        PodTemplateSpecV.deepown_l template_l template template_dq ∗
      "Hparent_meta" ∷ ObjectMetaV.deepown_l
        (KObjectV.objectmeta_ptr parent_l parent)
        (KObjectV.objectmeta parent) parent_dq
  }}}.
Proof.
  wp_start as "H". iNamed "H".
  iDestruct "Hinit" as "#Hinit".
  wp_alloc controllerRef_ptr as "controllerRef".
  wp_pures.
  wp_alloc parentObject_ptr as "parentObject".
  wp_pures.
  wp_alloc template_ptr as "template_ptr".
  wp_auto.
  wp_apply (wp_getPodsLabelSet with "[$Hinit $Htemplate]").
  iIntros (labels_l) "[Htemplate Hlabels]".
  wp_auto.
  wp_apply (wp_getPodsFinalizers with "[$Hinit $Htemplate]").
  iIntros (finalizers_sl) "(Htemplate & Hfinalizers & %Hfinalizers_not_nil)".
  wp_auto.
  wp_apply (wp_getPodsAnnotationSet with "[$Hinit $Htemplate]").
  iIntros (annotations_l) "[Htemplate Hannotations]".
  wp_auto.
  wp_apply wp_Accessor. 1: iPureIntro; done.
  wp_auto.
  wp_apply (wp_GetName_deepown with "[$Hparent_meta]").
  iIntros "Hparent_meta".
  wp_auto.
  wp_apply (wp_getPodsPrefix with "[]").
  { iFrame "#". done. }
  iIntros "%Hprefix_valid".
  wp_auto.
  wp_alloc pod_l as "Hpod_l".
  destruct controller_ref as [ref|].
  - simpl in Hcontroller_ref_is_parent.
    iDestruct "Hcontroller_ref" as (ref_c) "[Href_l Href]".
    iDestruct (typed_pointsto_not_null with "Href_l") as "%Href_not_null".
    iDestruct (struct_fields_split (V:=v1.Pod.t) with "Hpod_l") as
      "[Hpod_fields %Hpod_l_not_null]".
    iNamedPrefix "Hpod_fields" "Hpod_".
    iDestruct (struct_fields_split (V:=v1.ObjectMeta.t)
      with "Hpod_ObjectMeta") as "[Hmeta_fields %Hmeta_l_not_null]".
    iNamedPrefix "Hmeta_fields" "Hmeta_".
    wp_auto.
    rewrite -> bool_decide_false by exact Href_not_null.
    wp_pures.
    wp_auto.
    wp_apply (wp_slice_literal
      (V:=v1.OwnerReference.t) (t:=v1.OwnerReference)).
    iSplitR; first done.
    iIntros (ref_sl_ptr) "[Href_sl Href_sl_cap]".
    set ref_sl : slice.t := {| slice.ptr := ref_sl_ptr;
      slice.len := W64 1; slice.cap := W64 1 |}.
    iAssert (ref_sl ↦* [ref_c])%I with "[Href_sl]" as "Href_sl".
    { iExactEq "Href_sl". f_equal. }
    subst ref_sl.
    iPoseProof (own_slice_nil (V:=v1.OwnerReference.t) (DfracOwn 1))
      as "Howners".
    iPoseProof (own_slice_cap_nil (V:=v1.OwnerReference.t)) as "Howners_cap".
    wp_auto.
    wp_apply (wp_slice_append
      (st:=go.SliceType v1.OwnerReference)
      (t:=v1.OwnerReference) (V:=v1.OwnerReference.t)
      slice.nil ([] : list v1.OwnerReference.t)
      {| slice.ptr := ref_sl_ptr; slice.len := W64 1;
        slice.cap := W64 1 |} [ref_c] (DfracOwn 1) with
      "[$Howners $Howners_cap $Href_sl]").
    iIntros (owners_sl)
      "(Howners_result & Howners_cap_result & Href_sl_back)".
    wp_auto.
    iPoseProof (PodTemplateSpecV.deepown_l_split with "Htemplate") as
      "(%Htemplate_l_not_null & Htemplate_meta & Htemplate_spec)".
    wp_apply (wp_PodSpec__DeepCopy with "[$Hinit $Htemplate_spec]").
    iIntros (spec_copy_l) "[Hspec_copy Htemplate_spec]".
    iDestruct "Hspec_copy" as (spec_c) "[Hspec_copy_l Hspec_copy]".
    wp_auto.
    iPoseProof (PodTemplateSpecV.deepown_l_restore _ _ _
      Htemplate_l_not_null with "[$Htemplate_meta $Htemplate_spec]") as
      "Htemplate".
    iDestruct (own_map_not_nil with "Hlabels") as "%Hlabels_not_nil".
    iDestruct (own_map_not_nil with "Hannotations") as
      "%Hannotations_not_nil".
    iDestruct (own_slice_len with "Howners_result") as "%Howners_len".
    assert (owners_sl ≠ slice.nil) as Howners_not_nil.
    { intros ->. simpl in Howners_len. word. }
    iAssert (∃ labels_c,
        labels_l ↦$ labels_c ∗
        ⌜ labels_c = default ∅
          template.(PodTemplateSpecV.ObjectMeta').(ObjectMetaV.Labels') ⌝)%I
      with "[Hlabels]" as "Hlabels_some".
    { iExists _. iFrame. done. }
    iAssert (∃ annotations_c,
        annotations_l ↦$ annotations_c ∗
        ⌜ annotations_c = default ∅
          template.(PodTemplateSpecV.ObjectMeta').(ObjectMetaV.Annotations') ⌝)%I
      with "[Hannotations]" as "Hannotations_some".
    { iExists _. iFrame. done. }
    iAssert (∃ owners_c, owners_sl ↦* owners_c ∗
        [∗ list] owner_c;owner ∈ owners_c;[ref],
          OwnerReferenceV.deepown owner_c owner 1)%I
      with "[Howners_result Href]" as "Howners_some".
    { iExists [ref_c]. simpl. iFrame. }
    iAssert (∃ finalizers_c, finalizers_sl ↦* finalizers_c ∗
        ⌜ finalizers_c = default []
          template.(PodTemplateSpecV.ObjectMeta').(ObjectMetaV.Finalizers') ⌝)%I
      with "[Hfinalizers]" as "Hfinalizers_some".
    { iExists _. iFrame. done. }
    set pod_meta_c : v1.ObjectMeta.t :=
      v1.ObjectMeta.mk ""%go
        ((KObjectV.objectmeta parent).(ObjectMetaV.Name') ++ "-"%go)
        ""%go ""%go ""%go ""%go (W64 0) (zero_val v1.Time.t)
        null null labels_l annotations_l owners_sl finalizers_sl slice.nil.
    iCombineNamed "Hmeta_*" as "Hmeta_fields".
    iAssert (typed_pointsto_def (PodV.objectmeta_ptr pod_l)
        pod_meta_c (DfracOwn 1))%I with "[Hmeta_fields]" as "Hmeta_fields".
    { rewrite /PodV.objectmeta_ptr /pod_meta_c /=.
      iNamed "Hmeta_fields". iFrame. }
    iDestruct (struct_fields_combine (V:=v1.ObjectMeta.t)
      (PodV.objectmeta_ptr pod_l) pod_meta_c (DfracOwn 1)
      Hmeta_l_not_null with "Hmeta_fields") as "Hmeta_l".
    iPoseProof (TimeV.deepown_zero (Σ:=Σ) (DfracOwn 1)) as "Htime".
    iAssert (ObjectMetaV.deepown pod_meta_c
        (generated_pod_meta template
          (KObjectV.objectmeta parent).(ObjectMetaV.Name') (Some [ref])) 1)%I
      with "[Htime Hlabels_some Hannotations_some Howners_some Hfinalizers_some]"
      as "Hmeta".
    { rewrite /ObjectMetaV.deepown /generated_pod_meta /pod_meta_c /=.
      iFrame "Htime Hlabels_some Hannotations_some Howners_some Hfinalizers_some".
      iPureIntro. Timeout 10 naive_solver. }
    iAssert (ObjectMetaV.deepown_l (PodV.objectmeta_ptr pod_l)
        (generated_pod_meta template
          (KObjectV.objectmeta parent).(ObjectMetaV.Name') (Some [ref])) 1)%I
      with "[Hmeta_l Hmeta]" as "Hpod_meta".
    { iExists pod_meta_c. iFrame. }
    iAssert (PodSpecV.deepown_l (PodV.spec_ptr pod_l)
        template.(PodTemplateSpecV.Spec') 1)%I
      with "[Hpod_Spec Hspec_copy]" as "Hpod_spec".
    { iExists spec_c. iFrame. }
    iPoseProof (PodStatusV.deepown_zero (Σ:=Σ) (DfracOwn 1)) as
      "Hstatus".
    iAssert (PodStatusV.deepown_l (PodV.status_ptr pod_l)
        PodStatusV.zero 1)%I with "[Hpod_Status Hstatus]" as "Hpod_status".
    { iExists (zero_val v1.PodStatus.t). iFrame. done. }
    iPoseProof (PodV.deepown_l_restore pod_l
      (generated_pod template
        (KObjectV.objectmeta parent).(ObjectMetaV.Name') (Some [ref])) 1
      Hpod_l_not_null with
      "[$Hpod_TypeMeta $Hpod_meta $Hpod_spec $Hpod_status]") as "Hpod".
    iApply ("HΦ" $! pod_l
      (generated_pod template
        (KObjectV.objectmeta parent).(ObjectMetaV.Name') (Some [ref]))).
    iFrame "Hpod Htemplate Hparent_meta".
    iPureIntro.
    destruct Hcontroller_ref_is_parent as
      (Hkind & Hname & Huid & Hblock & Hcontroller).
    split_and!; try done.
    + rewrite /obj_parent_ref_is /meta_parent_ref_is /meta_parent_ref
        /generated_pod /generated_pod_meta /= Hcontroller /=.
      rewrite Hkind Hname Huid. done.
  - iDestruct "Hcontroller_ref" as "%Hcontroller_ref_l".
    subst controller_ref_l.
    wp_auto.
    iDestruct (struct_fields_split (V:=v1.Pod.t) with "Hpod_l") as
      "[Hpod_fields %Hpod_l_not_null]".
    iNamedPrefix "Hpod_fields" "Hpod_".
    iDestruct (struct_fields_split (V:=v1.ObjectMeta.t)
      with "Hpod_ObjectMeta") as "[Hmeta_fields %Hmeta_l_not_null]".
    iNamedPrefix "Hmeta_fields" "Hmeta_".
    iPoseProof (PodTemplateSpecV.deepown_l_split with "Htemplate") as
      "(%Htemplate_l_not_null & Htemplate_meta & Htemplate_spec)".
    wp_apply (wp_PodSpec__DeepCopy with "[$Hinit $Htemplate_spec]").
    iIntros (spec_copy_l) "[Hspec_copy Htemplate_spec]".
    iDestruct "Hspec_copy" as (spec_c) "[Hspec_copy_l Hspec_copy]".
    wp_auto.
    iPoseProof (PodTemplateSpecV.deepown_l_restore _ _ _
      Htemplate_l_not_null with "[$Htemplate_meta $Htemplate_spec]") as
      "Htemplate".
    iDestruct (own_map_not_nil with "Hlabels") as "%Hlabels_not_nil".
    iDestruct (own_map_not_nil with "Hannotations") as
      "%Hannotations_not_nil".
    iAssert (∃ labels_c,
        labels_l ↦$ labels_c ∗
        ⌜ labels_c = default ∅
          template.(PodTemplateSpecV.ObjectMeta').(ObjectMetaV.Labels') ⌝)%I
      with "[Hlabels]" as "Hlabels_some".
    { iExists _. iFrame. done. }
    iAssert (∃ annotations_c,
        annotations_l ↦$ annotations_c ∗
        ⌜ annotations_c = default ∅
          template.(PodTemplateSpecV.ObjectMeta').(ObjectMetaV.Annotations') ⌝)%I
      with "[Hannotations]" as "Hannotations_some".
    { iExists _. iFrame. done. }
    iAssert (∃ finalizers_c, finalizers_sl ↦* finalizers_c ∗
        ⌜ finalizers_c = default []
          template.(PodTemplateSpecV.ObjectMeta').(ObjectMetaV.Finalizers') ⌝)%I
      with "[Hfinalizers]" as "Hfinalizers_some".
    { iExists _. iFrame. done. }
    set pod_meta_c : v1.ObjectMeta.t :=
      v1.ObjectMeta.mk ""%go
        ((KObjectV.objectmeta parent).(ObjectMetaV.Name') ++ "-"%go)
        ""%go ""%go ""%go ""%go (W64 0) (zero_val v1.Time.t)
        null null labels_l annotations_l slice.nil finalizers_sl slice.nil.
    iCombineNamed "Hmeta_*" as "Hmeta_fields".
    iAssert (typed_pointsto_def (PodV.objectmeta_ptr pod_l)
        pod_meta_c (DfracOwn 1))%I with "[Hmeta_fields]" as "Hmeta_fields".
    { rewrite /PodV.objectmeta_ptr /pod_meta_c /=.
      iNamed "Hmeta_fields". iFrame. }
    iDestruct (struct_fields_combine (V:=v1.ObjectMeta.t)
      (PodV.objectmeta_ptr pod_l) pod_meta_c (DfracOwn 1)
      Hmeta_l_not_null with "Hmeta_fields") as "Hmeta_l".
    iPoseProof (TimeV.deepown_zero (Σ:=Σ) (DfracOwn 1)) as "Htime".
    iAssert (ObjectMetaV.deepown pod_meta_c
        (generated_pod_meta template
          (KObjectV.objectmeta parent).(ObjectMetaV.Name') None) 1)%I
      with "[Htime Hlabels_some Hannotations_some Hfinalizers_some]"
      as "Hmeta".
    { rewrite /ObjectMetaV.deepown /generated_pod_meta /pod_meta_c /=.
      iFrame "Htime Hlabels_some Hannotations_some Hfinalizers_some".
      iPureIntro. Timeout 10 naive_solver. }
    iAssert (ObjectMetaV.deepown_l (PodV.objectmeta_ptr pod_l)
        (generated_pod_meta template
          (KObjectV.objectmeta parent).(ObjectMetaV.Name') None) 1)%I
      with "[Hmeta_l Hmeta]" as "Hpod_meta".
    { iExists pod_meta_c. iFrame. }
    iAssert (PodSpecV.deepown_l (PodV.spec_ptr pod_l)
        template.(PodTemplateSpecV.Spec') 1)%I
      with "[Hpod_Spec Hspec_copy]" as "Hpod_spec".
    { iExists spec_c. iFrame. }
    iPoseProof (PodStatusV.deepown_zero (Σ:=Σ) (DfracOwn 1)) as
      "Hstatus".
    iAssert (PodStatusV.deepown_l (PodV.status_ptr pod_l)
        PodStatusV.zero 1)%I with "[Hpod_Status Hstatus]" as "Hpod_status".
    { iExists (zero_val v1.PodStatus.t). iFrame. done. }
    iPoseProof (PodV.deepown_l_restore pod_l
      (generated_pod template
        (KObjectV.objectmeta parent).(ObjectMetaV.Name') None) 1
      Hpod_l_not_null with
      "[$Hpod_TypeMeta $Hpod_meta $Hpod_spec $Hpod_status]") as "Hpod".
    iApply ("HΦ" $! pod_l
      (generated_pod template
        (KObjectV.objectmeta parent).(ObjectMetaV.Name') None)).
    iFrame "Hpod Htemplate Hparent_meta".
    iPureIntro.
    split_and!; try done.
Qed.

Lemma wp_GetPodFromTemplate_ReplicaSet template_l obj controller_ref_l
  dq (template_c : v1.core_v1.PodTemplateSpec.t) template rs_l meta controller_ref:
  {{{ is_pkg_init controller ∗
      template_l ↦{dq} template_c ∗
      PodTemplateSpecV.deepown template_c template dq ∗
      ObjectMetaV.deepown_l (ReplicaSetV.objectmeta_ptr rs_l) meta dq ∗
      OwnerReferenceV.deepown_l controller_ref_l controller_ref 1 ∗
      ⌜ PodTemplateSpecV.valid template ⌝ ∗
      ⌜ obj = interface.mk_ok (go.PointerType v1.ReplicaSet) (# rs_l) ⌝ ∗
      ⌜ ObjectMetaV.valid ReplicaSetV.kind meta ⌝ ∗
      ⌜ length meta.(ObjectMetaV.Name') < 58 ⌝ ∗
      ⌜ OwnerReferenceV.refers_to_controller controller_ref "ReplicaSet"%go
        meta.(ObjectMetaV.Name') meta.(ObjectMetaV.UID') ⌝
  }}}
  @! controller.GetPodFromTemplate #template_l #obj #controller_ref_l
  {{{ pod_l pod, RET (#pod_l, #interface.nil);
      PodV.deepown_l pod_l pod 1 ∗
      ⌜ obj_parent_ref_is (KObjectV.Pod pod) "ReplicaSet"%go meta.(ObjectMetaV.Name') meta.(ObjectMetaV.UID') ⌝ ∗
      ⌜ KObjectV.valid_nameless_create "Pod"%go meta.(ObjectMetaV.Namespace') (KObjectV.Pod pod) ⌝ ∗
      template_l ↦{dq} template_c ∗
      PodTemplateSpecV.deepown template_c template dq ∗
      ObjectMetaV.deepown_l (ReplicaSetV.objectmeta_ptr rs_l) meta dq
  }}}.
Proof. Admitted.

Lemma wp_GetPodFromTemplate_StatefulSet template_l obj controller_ref_l
    dq (template_c : v1.core_v1.PodTemplateSpec.t) template set_l meta
    controller_ref :
  {{{ is_pkg_init controller ∗
      template_l ↦{dq} template_c ∗
      PodTemplateSpecV.deepown template_c template dq ∗
      ObjectMetaV.deepown_l (StatefulSetV.objectmeta_ptr set_l) meta dq ∗
      OwnerReferenceV.deepown_l controller_ref_l controller_ref 1 ∗
      ⌜ PodTemplateSpecV.valid template ⌝ ∗
      ⌜ obj = interface.mk_ok (go.PointerType v1.StatefulSet) (#set_l) ⌝ ∗
      ⌜ ObjectMetaV.valid StatefulSetV.kind meta ⌝ ∗
      ⌜ length meta.(ObjectMetaV.Name') < 58 ⌝ ∗
      ⌜ OwnerReferenceV.valid controller_ref ⌝ ∗
      ⌜ OwnerReferenceV.refers_to_controller controller_ref "StatefulSet"%go
          meta.(ObjectMetaV.Name') meta.(ObjectMetaV.UID') ⌝
  }}}
    @! controller.GetPodFromTemplate #template_l #obj #controller_ref_l
  {{{ pod_l pod, RET (#pod_l, #interface.nil);
      PodV.deepown_l pod_l pod 1 ∗
      ⌜ obj_parent_ref_is (KObjectV.Pod pod) "StatefulSet"%go
          meta.(ObjectMetaV.Name') meta.(ObjectMetaV.UID') ⌝ ∗
      ⌜ KObjectV.valid_nameless_create "Pod"%go meta.(ObjectMetaV.Namespace')
          (KObjectV.Pod pod) ⌝ ∗
      ⌜ pod.(PodV.ObjectMeta').(ObjectMetaV.DeletionTimestamp') = None ⌝ ∗
      ⌜ pod_from_template template pod ⌝ ∗
      template_l ↦{dq} template_c ∗
      PodTemplateSpecV.deepown template_c template dq ∗
      ObjectMetaV.deepown_l (StatefulSetV.objectmeta_ptr set_l) meta dq
  }}}.
Proof. Admitted.

End proof.
