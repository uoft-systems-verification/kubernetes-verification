From New.proof Require Import prelude empty_ffi.
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
