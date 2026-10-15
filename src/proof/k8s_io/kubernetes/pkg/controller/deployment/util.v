From New.proof Require Import prelude empty_ffi.
From New.proof.kubernetes_types Require Export prelude.
From New.proof.k8s_io.api.core Require Import v1.
From New.proof.k8s_io.kubernetes.pkg.controller.deployment Require Export util_init.

(* EqualIgnoreHash compares two pod templates after deleting the
   pod-template-hash label from each copy's labels. *)
Definition drop_hash_label (t : PodTemplateSpecV.t) : PodTemplateSpecV.t :=
  t <| PodTemplateSpecV.ObjectMeta' :=
    t.(PodTemplateSpecV.ObjectMeta') <| ObjectMetaV.Labels' :=
      delete "pod-template-hash"%go <$>
        t.(PodTemplateSpecV.ObjectMeta').(ObjectMetaV.Labels') |> |>.

(* Perennial models [delete] on a nil map as stuck, while Go makes it a no-op,
   so EqualIgnoreHash is specified only for templates with non-nil labels. *)
Definition template_has_labels (t : PodTemplateSpecV.t) : Prop :=
  is_Some t.(PodTemplateSpecV.ObjectMeta').(ObjectMetaV.Labels').

(* TRUSTED: the comparison equality.Semantic.DeepEqual performs on two pod
   templates. It is reflection-based, so goose cannot translate it, and it
   compares every PodSpec field while PodSpecV models only a few, so its result
   is not determined by the model values. It is therefore left abstract, like
   storage_object_normalize in kubernetes_model/common.v.

   TODO: model every PodSpec field in PodSpecV. Then define equality between
   PodTemplateSpecV values (as Semantic.DeepEqual compares them, including
   treating nil and empty slices and maps as equal), and remove this Parameter
   and the two Axioms below. wp_Semantic_DeepEqual_PodTemplateSpec would then
   be stated with that equality; it stays trusted, since DeepEqual is
   reflection-based. *)
Parameter template_semantic_eq : PodTemplateSpecV.t → PodTemplateSpecV.t → Prop.
Axiom template_semantic_eq_dec : ∀ t1 t2, Decision (template_semantic_eq t1 t2).
#[global] Existing Instance template_semantic_eq_dec.
Axiom template_semantic_eq_sym : ∀ t1 t2,
  template_semantic_eq t1 t2 → template_semantic_eq t2 t1.

Definition template_matches (t1 t2 : PodTemplateSpecV.t) : Prop :=
  template_semantic_eq (drop_hash_label t1) (drop_hash_label t2).

#[global] Instance template_matches_dec t1 t2 : Decision (template_matches t1 t2).
Proof. unfold template_matches. apply _. Defined.

Lemma template_matches_sym t1 t2 : template_matches t1 t2 → template_matches t2 t1.
Proof. apply template_semantic_eq_sym. Qed.

Section proof.
Context `{hG: !heapGS Σ} `{!ffi_semantics _ _}.
Context {sem : go.Semantics}
  {package_sem : util.Assumptions}
  {util_core_v1_sem : code.k8s_io.api.core.v1.v1.Assumptions}
  {util_meta_v1_sem : code.k8s_io.apimachinery.pkg.apis.meta.v1.v1.Assumptions}.
Collection W := sem + package_sem.
Local Set Default Proof Using "All".

(* Take the core and meta assumptions as separate variables, as controller.v
   does, so callers' instances are used for the template points-to and
   ownership instead of the ones reached through [util.Assumptions]. *)
#[local] Existing Instance util_core_v1_sem.
#[local] Existing Instance util_meta_v1_sem.

(* TRUSTED: equality.Semantic.DeepEqual on two pod templates is
   reflection-based and not translated by goose. Its contract is
   [template_semantic_eq] on the templates' model values. It only reads its
   arguments. *)
Lemma wp_Semantic_DeepEqual_PodTemplateSpec t1_l t2_l c1 c2 tv1 tv2 dq1 dq2 :
  {{{ is_pkg_init code.k8s_io.apimachinery.pkg.api.equality.pkg_id.equality ∗
      t1_l ↦{dq1} c1 ∗ PodTemplateSpecV.deepown c1 tv1 dq1 ∗
      t2_l ↦{dq2} c2 ∗ PodTemplateSpecV.deepown c2 tv2 dq2
  }}}
    (global_addr equality.Semantic) @! (go.PointerType conversion.Equalities) @! "DeepEqual"
      #(interface.mk_ok (go.PointerType core_v1.PodTemplateSpec) #t1_l)
      #(interface.mk_ok (go.PointerType core_v1.PodTemplateSpec) #t2_l)
  {{{ RET #(bool_decide (template_semantic_eq tv1 tv2));
      t1_l ↦{dq1} c1 ∗ PodTemplateSpecV.deepown c1 tv1 dq1 ∗
      t2_l ↦{dq2} c2 ∗ PodTemplateSpecV.deepown c2 tv2 dq2
  }}}.
Proof. Admitted.

Lemma wp_EqualIgnoreHash t1_l t2_l c1 c2 tv1 tv2 dq1 dq2 :
  {{{ is_pkg_init util ∗
      "Ht1_l" ∷ t1_l ↦{dq1} c1 ∗
      "Ht1" ∷ PodTemplateSpecV.deepown c1 tv1 dq1 ∗
      "Ht2_l" ∷ t2_l ↦{dq2} c2 ∗
      "Ht2" ∷ PodTemplateSpecV.deepown c2 tv2 dq2 ∗
      "%Hlabels1" ∷ ⌜ template_has_labels tv1 ⌝ ∗
      "%Hlabels2" ∷ ⌜ template_has_labels tv2 ⌝
  }}}
    @! util.EqualIgnoreHash #t1_l #t2_l
  {{{ RET #(bool_decide (template_matches tv1 tv2));
      t1_l ↦{dq1} c1 ∗
      PodTemplateSpecV.deepown c1 tv1 dq1 ∗
      t2_l ↦{dq2} c2 ∗
      PodTemplateSpecV.deepown c2 tv2 dq2
  }}}.
Proof.
  wp_start as "H". iNamed "H".
  iAssert (is_pkg_init code.k8s_io.api.core.v1.pkg_id.v1) as "#Hcore". { iPkgInit. }
  wp_auto.
  wp_apply (wp_PodTemplateSpec__DeepCopy with "[$Hcore $Ht1_l $Ht1]").
  iIntros (copy1_l) "(Hcopy1 & Ht1_l & Ht1)". wp_auto.
  wp_apply (wp_PodTemplateSpec__DeepCopy with "[$Hcore $Ht2_l $Ht2]").
  iIntros (copy2_l) "(Hcopy2 & Ht2_l & Ht2)".
  (* Open both copies down to their ObjectMeta field, which the deletes read. *)
  iDestruct "Hcopy1" as (cc1) "[Hcc1_l Hcc1]".
  iDestruct (struct_fields_split (V:=v1.PodTemplateSpec.t) with "Hcc1_l") as "[Hcc1_l %Hcc1_nn]".
  iNamedPrefix "Hcc1_l" "Hcc1f_".
  iDestruct "Hcopy2" as (cc2) "[Hcc2_l Hcc2]".
  iDestruct (struct_fields_split (V:=v1.PodTemplateSpec.t) with "Hcc2_l") as "[Hcc2_l %Hcc2_nn]".
  iNamedPrefix "Hcc2_l" "Hcc2f_".
  iDestruct (struct_fields_split (V:=v1.ObjectMeta.t) with "Hcc1f_ObjectMeta")
    as "[Hom1 %Hom1_nn]".
  iNamedPrefix "Hom1" "Hom1_".
  iDestruct (struct_fields_split (V:=v1.ObjectMeta.t) with "Hcc2f_ObjectMeta")
    as "[Hom2 %Hom2_nn]".
  iNamedPrefix "Hom2" "Hom2_".
  (* The copies' labels maps are non-nil, so delete applies to them. *)
  destruct Hlabels1 as [lm1 Hlm1]. destruct Hlabels2 as [lm2 Hlm2].
  iDestruct "Hcc1" as "[Hm1 Hs1]".
  iEval (rewrite /named) in "Hm1". iNamedPrefix "Hm1" "Hm1_".
  iDestruct "Hcc2" as "[Hm2 Hs2]".
  iEval (rewrite /named) in "Hm2". iNamedPrefix "Hm2" "Hm2_".
  iEval (rewrite Hlm1) in "Hm1_Hdeepown_labels_some".
  iDestruct "Hm1_Hdeepown_labels_some" as (cl1) "[Hlab1 ->]".
  iEval (rewrite Hlm2) in "Hm2_Hdeepown_labels_some".
  iDestruct "Hm2_Hdeepown_labels_some" as (cl2) "[Hlab2 ->]".
  wp_auto.
  wp_apply (wp_map_delete with "Hlab1"). iIntros "Hlab1".
  wp_auto.
  wp_apply (wp_map_delete with "Hlab2"). iIntros "Hlab2".
  wp_auto.
  (* Reassemble each copy, now modelled by the template with the hash label
     dropped. *)
  iCombineNamed "Hom1_*" as "Hom1".
  iAssert (typed_pointsto_def (copy1_l.[v1.PodTemplateSpec.t, "ObjectMeta"])
      (v1.PodTemplateSpec.ObjectMeta' cc1) (DfracOwn 1)) with "[Hom1]" as "Hom1".
  { iNamed "Hom1". destruct cc1 as [om1 sp1]. destruct om1. simpl. iFrame. }
  iDestruct (struct_fields_combine _ _ _ Hom1_nn with "Hom1") as "Hcc1f_ObjectMeta".
  iCombineNamed "Hcc1f_*" as "Hcc1f".
  iAssert (typed_pointsto_def copy1_l cc1 (DfracOwn 1)) with "[Hcc1f]" as "Hcc1f".
  { iNamed "Hcc1f". destruct cc1. simpl. iFrame. }
  iDestruct (struct_fields_combine _ _ _ Hcc1_nn with "Hcc1f") as "Hcopy1_l".
  iCombineNamed "Hom2_*" as "Hom2".
  iAssert (typed_pointsto_def (copy2_l.[v1.PodTemplateSpec.t, "ObjectMeta"])
      (v1.PodTemplateSpec.ObjectMeta' cc2) (DfracOwn 1)) with "[Hom2]" as "Hom2".
  { iNamed "Hom2". destruct cc2 as [om2 sp2]. destruct om2. simpl. iFrame. }
  iDestruct (struct_fields_combine _ _ _ Hom2_nn with "Hom2") as "Hcc2f_ObjectMeta".
  iCombineNamed "Hcc2f_*" as "Hcc2f".
  iAssert (typed_pointsto_def copy2_l cc2 (DfracOwn 1)) with "[Hcc2f]" as "Hcc2f".
  { iNamed "Hcc2f". destruct cc2. simpl. iFrame. }
  iDestruct (struct_fields_combine _ _ _ Hcc2_nn with "Hcc2f") as "Hcopy2_l".
  iCombineNamed "Hm1_*" as "Hm1".
  iAssert (PodTemplateSpecV.deepown cc1 (drop_hash_label tv1) (DfracOwn 1))
    with "[Hm1 Hlab1 Hs1]" as "Hcopy1".
  { iNamed "Hm1".
    rewrite /PodTemplateSpecV.deepown /ObjectMetaV.deepown /drop_hash_label /= Hlm1 /=.
    iFrame "∗%". iPureIntro. split; [|done]. split; [|discriminate].
    intros Hnull. apply Hm1_Hdeepown_labels_none in Hnull. rewrite Hlm1 in Hnull. discriminate. }
  iCombineNamed "Hm2_*" as "Hm2".
  iAssert (PodTemplateSpecV.deepown cc2 (drop_hash_label tv2) (DfracOwn 1))
    with "[Hm2 Hlab2 Hs2]" as "Hcopy2".
  { iNamed "Hm2".
    rewrite /PodTemplateSpecV.deepown /ObjectMetaV.deepown /drop_hash_label /= Hlm2 /=.
    iFrame "∗%". iPureIntro. split; [|done]. split; [|discriminate].
    intros Hnull. apply Hm2_Hdeepown_labels_none in Hnull. rewrite Hlm2 in Hnull. discriminate. }
  iAssert (is_pkg_init code.k8s_io.apimachinery.pkg.api.equality.pkg_id.equality)
    as "#Heq". { iPkgInit. }
  wp_apply (wp_Semantic_DeepEqual_PodTemplateSpec with "[$Heq $Hcopy1_l $Hcopy1 $Hcopy2_l $Hcopy2]").
  iIntros "_". wp_auto.
  iApply "HΦ". iFrame.
Qed.

End proof.
