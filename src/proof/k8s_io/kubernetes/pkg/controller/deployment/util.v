From New.proof Require Import prelude empty_ffi.
From New.proof.kubernetes_types Require Export prelude.
From New.proof.k8s_io.kubernetes.pkg.controller.deployment Require Export util_init.

(* TODO: un-axiomatize. Once PodTemplateSpecV carries enough structure to state
   template equality, template_matches should become a Definition (equality of
   the templates after deleting the pod-template-hash label from each
   ObjectMeta), the two axioms below should become proved lemmas, and
   wp_EqualIgnoreHash below should be discharged rather than
   Admitted.

   EqualIgnoreHash compares pod templates ignoring the pod-template-hash label.
   PodTemplateSpecV is axiomatized, so the comparison relation and the spec
   below are trusted, mirroring controller.v's pod_from_template. *)
Parameter template_matches : PodTemplateSpecV.t → PodTemplateSpecV.t → Prop.
Axiom template_matches_dec : ∀ t1 t2, Decision (template_matches t1 t2).
#[global] Existing Instance template_matches_dec.
Axiom template_matches_sym : ∀ t1 t2, template_matches t1 t2 → template_matches t2 t1.

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

Lemma wp_EqualIgnoreHash t1_l t2_l c1 c2 tv1 tv2 dq1 dq2 :
  {{{ is_pkg_init util ∗
      "Ht1_l" ∷ t1_l ↦{dq1} c1 ∗
      "Ht1" ∷ PodTemplateSpecV.deepown c1 tv1 dq1 ∗
      "Ht2_l" ∷ t2_l ↦{dq2} c2 ∗
      "Ht2" ∷ PodTemplateSpecV.deepown c2 tv2 dq2
  }}}
    @! util.EqualIgnoreHash #t1_l #t2_l
  {{{ RET #(bool_decide (template_matches tv1 tv2));
      t1_l ↦{dq1} c1 ∗
      PodTemplateSpecV.deepown c1 tv1 dq1 ∗
      t2_l ↦{dq2} c2 ∗
      PodTemplateSpecV.deepown c2 tv2 dq2
  }}}.
Proof.
Admitted.

End proof.
