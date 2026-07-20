From New.proof Require Import prelude empty_ffi.
From New.proof.map Require Import for_range.
From New.proof.kubernetes_types Require Export prelude.
From New.proof.k8s_io.kubernetes.pkg Require Export controller_init.

Section proof.
Context `{hG: !heapGS Σ} `{!ffi_semantics _ _}.
Context {sem : go.Semantics}
  {package_sem : controller.Assumptions}
  {meta_v1_sem : code.k8s_io.apimachinery.pkg.apis.meta.v1.v1.Assumptions}
  {core_v1_sem : code.k8s_io.api.core.v1.v1.Assumptions}
  {apps_v1_sem : code.k8s_io.api.apps.v1.v1.Assumptions}.
Local Set Default Proof Using "All".

Parameter pod_from_template : PodTemplateSpecV.t → PodV.t → Prop.

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
  Timeout 10 wp_auto.
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
        template.(PodTemplateSpecV.ObjectMeta').(ObjectMetaV.Finalizers')
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
