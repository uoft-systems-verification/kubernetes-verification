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
      ⌜ index_key = namespace ++ "/"%go ++ 
        owner_reference.(v1.OwnerReference.Kind') ++ "/"%go ++ 
        owner_reference.(v1.OwnerReference.Name') ++ "/"%go ++
        owner_reference.(v1.OwnerReference.UID')⌝
  }}}.
Proof.
Admitted.

Definition is_pod_active (pod: v1.Pod.t): Prop :=
  "Succeeded"%go ≠ pod.(v1.Pod.Status').(v1.PodStatus.Phase') ∧
  "Failed"%go ≠ pod.(v1.Pod.Status').(v1.PodStatus.Phase') ∧
	pod.(v1.Pod.ObjectMeta').(v1.ObjectMeta.DeletionTimestamp') = null.

Lemma wp_IsPodActive p pod dq:
  {{{ is_pkg_init controller ∗
      p↦{dq}pod
  }}}
  @! controller.IsPodActive #p
  {{{ RET #(bool_decide (is_pod_active pod));
      p↦{dq}pod
  }}}.
Proof.
  wp_start as "Hp".
  wp_alloc p' as "Hp'".
  unfold v1.PodSucceeded, v1.PodFailed. wp_auto.
  iDestruct (struct_fields_split with "Hp") as "Hp". iNamed "Hp". wp_auto.
  destruct (bool_decide ("Succeeded"%go = pod.(v1.Pod.Status').(v1.PodStatus.Phase'))) eqn:HPhase1. all: rewrite HPhase1; wp_auto.
  - assert (bool_decide (is_pod_active pod) = false) as ->.
    { apply bool_decide_eq_false_2. unfold is_pod_active.
      apply bool_decide_eq_true in HPhase1. naive_solver. }
    shelve.
  - destruct (bool_decide ("Failed"%go = pod.(v1.Pod.Status').(v1.PodStatus.Phase'))) eqn:HPhase2. all: rewrite HPhase2; wp_auto.
    + assert (bool_decide (is_pod_active pod) = false) as ->.
      { apply bool_decide_eq_false_2. unfold is_pod_active.
        apply bool_decide_eq_true in HPhase2. naive_solver. }
      shelve.
    + destruct (bool_decide (pod.(v1.Pod.ObjectMeta').(v1.ObjectMeta.DeletionTimestamp') = null)) eqn:Hdt.
      * assert (bool_decide (is_pod_active pod) = true) as ->.
        { apply bool_decide_eq_true. unfold is_pod_active.
          apply bool_decide_eq_false in HPhase1.
          apply bool_decide_eq_false in HPhase2.
          apply bool_decide_eq_true in Hdt. naive_solver. }
        shelve.
      * assert (bool_decide (is_pod_active pod) = false) as ->.
        { apply bool_decide_eq_false_2. unfold is_pod_active.
          apply bool_decide_eq_false in Hdt. naive_solver. }
        shelve.
    Unshelve.
    all: iApply "HΦ";
        iDestruct (struct_fields_combine (v:=pod) with "[$HTypeMeta $HObjectMeta $HSpec $HStatus]") as "Hp";
        iFrame.
Qed.

Lemma wp_GetPodFromTemplate template_l obj controller_ref_l
  dq template pure_template rs_l meta pure_meta controller_ref pure_controller_ref:
  {{{ is_pkg_init controller ∗
      template_l ↦{dq} template ∗
      PurePodTemplateSpec.deepown template pure_template dq ∗
      ⌜ PurePodTemplateSpec.well_formed pure_template ⌝ ∗
      ⌜ obj = interface.mk (ptrT.id v1.ReplicaSet.id) (# rs_l) ⌝ ∗
      rs_l ↦s[v1.ReplicaSet :: "ObjectMeta"]{dq} meta ∗
      PureObjectMeta.deepown meta pure_meta dq ∗
      ⌜ PureObjectMeta.well_formed pure_meta ⌝ ∗
      ⌜ length pure_meta.(PureObjectMeta.Name') < 58 ⌝ ∗
      PureOwnerReference.deepown_l controller_ref_l controller_ref pure_controller_ref 1
  }}}
  @! controller.GetPodFromTemplate #template_l #obj #controller_ref_l
  {{{ pod_l pod pure_pod, RET (#pod_l, #interface.nil);
      PurePod.deepown_l pod_l pod pure_pod 1 ∗
      ⌜ obj_has_controller_parent_of (PureKObject.Pod pure_pod) "ReplicaSet"%go pure_meta.(PureObjectMeta.Name') pure_meta.(PureObjectMeta.UID') ⌝ ∗
      ⌜ PurePod.well_formed_for_nameless_create pure_pod ⌝ ∗
      template_l ↦{dq} template ∗
      PurePodTemplateSpec.deepown template pure_template dq ∗
      rs_l ↦s[v1.ReplicaSet :: "ObjectMeta"]{dq} meta ∗
      PureObjectMeta.deepown meta pure_meta dq
  }}}.
Proof. Admitted.

Definition is_pure_pod_active (pure_pod: PurePod.t): Prop :=
  "Succeeded"%go ≠ pure_pod.(PurePod.Status').(PurePodStatus.Phase') ∧
  "Failed"%go ≠ pure_pod.(PurePod.Status').(PurePodStatus.Phase') ∧
	pure_pod.(PurePod.ObjectMeta').(PureObjectMeta.DeletionTimestamp') = None.

Lemma deepown_preserves_activeness pod pure_pod dq:
  PurePod.deepown pod pure_pod dq -∗
    ⌜ is_pod_active pod ↔ is_pure_pod_active pure_pod ⌝.
Proof.
  iIntros "H". iNamed "H". iNamed "Hdeepown_objectmeta". iNamed "Hdeepown_podstatus".
  iPureIntro. unfold is_pod_active. unfold is_pure_pod_active. split.
  all: rewrite Hdeepown_deletiontimestamp_none; rewrite Hdeepown_phase; done.
Qed.

End proof.
