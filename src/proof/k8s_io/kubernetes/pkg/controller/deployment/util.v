From New.proof Require Import prelude empty_ffi.
From New.object_specs Require Export prelude.
From New.proof.k8s_io.api.core Require Import v1.
From New.proof Require Import sort.
From New.proof.k8s_io.kubernetes.pkg Require Import controller.
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

(* TRUSTED: the imported reflection-based equality.Semantic.DeepEqual
   operates on the complete template views. Its semantic equality treats nil
   and empty slices/maps alike and uses custom equality for Quantity and Time;
   it is therefore distinct from record equality on representation views.
   TODO: define that recursive semantic equality explicitly and prove its
   symmetry, keeping only the reflection call itself as a library contract. *)
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

Local Transparent ObjectMetaV.deepown ObjectMetaView.ObjectMetaV.deepown.

Section proof.
Context `{hG: !heapGS Σ} `{!ffi_semantics _ _}.
Context {sem : go.Semantics}
  {package_sem : util.Assumptions}
  {util_core_v1_sem : code.k8s_io.api.core.v1.v1.Assumptions}
  {util_meta_v1_sem : code.k8s_io.apimachinery.pkg.apis.meta.v1.v1.Assumptions}
  {util_apps_v1_sem : code.k8s_io.api.apps.v1.v1.Assumptions}.
Collection W := sem + package_sem.
Local Set Default Proof Using "All".

(* Take the core and meta assumptions as separate variables, as controller.v
   does, so callers' instances are used for the template points-to and
   ownership instead of the ones reached through [util.Assumptions]. *)
#[local] Existing Instance util_core_v1_sem.
#[local] Existing Instance util_meta_v1_sem.
#[local] Existing Instance util_apps_v1_sem.

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

(* FindNewReplicaSet sorts [rsList] in place, oldest first with ties broken by
   name, and returns the first entry whose template matches the deployment's.
   The caller gets the slice back in its sorted order. *)
Lemma wp_FindNewReplicaSet d_l (d : DeploymentV.t) sl ptrs (rss : list ReplicaSetV.t) dq1 dq3 :
  {{{ is_pkg_init util ∗
      "Hd" ∷ DeploymentV.deepown_l d_l d dq1 ∗
      "Hsl" ∷ sl ↦* ptrs ∗
      "Hrss" ∷ ([∗ list] ptr;rs ∈ ptrs;rss, ReplicaSetV.deepown_l ptr rs dq3) ∗
      "%Hlabels" ∷ ⌜ template_has_labels d.(DeploymentV.Spec').(DeploymentSpecV.Template') ∧
        Forall (λ rs, template_has_labels rs.(ReplicaSetV.Spec').(ReplicaSetSpecV.Template')) rss ⌝ ∗
      "%Htimes" ∷ ⌜ creation_times_comparable rss ⌝
  }}}
    @! util.FindNewReplicaSet #d_l #sl
  {{{ (rs_l : loc) ptrs' rss', RET #rs_l;
      ⌜ zip ptrs rss ≡ₚ zip ptrs' rss' ∧ sorted_by rs_created_before rss' ⌝ ∗
      (match list_find (λ rs, template_matches rs.(ReplicaSetV.Spec').(ReplicaSetSpecV.Template')
          d.(DeploymentV.Spec').(DeploymentSpecV.Template')) rss' with
       | Some (i, _) => ⌜ ptrs' !! i = Some rs_l ⌝
       | None => ⌜ rs_l = null ⌝
       end) ∗
      DeploymentV.deepown_l d_l d dq1 ∗
      sl ↦* ptrs' ∗
      ([∗ list] ptr;rs ∈ ptrs';rss', ReplicaSetV.deepown_l ptr rs dq3)
  }}}.
Proof.
  wp_start as "H". iNamed "H". wp_auto_keep.
  iDestruct (big_sepL2_length with "Hrss") as %Hlen0.
  (* Sort the (pointer, ReplicaSet) entries together. *)
  set entries := zip ptrs rss.
  assert (entries.*1 = ptrs) as Hfst by (apply fst_zip; lia).
  assert (entries.*2 = rss) as Hsnd by (apply snd_zip; lia).
  iAssert (rs_by_creation_contents dq3 sl entries) with "[Hsl Hrss]" as "Hcontents".
  { rewrite /rs_by_creation_contents Hfst. iFrame "Hsl".
    rewrite big_sepL2_alt. iDestruct "Hrss" as "[_ $]". }
  iAssert (is_pkg_init sort) as "#Hsort". { iPkgInit. }
  wp_bind ((let: "$a0" := Convert controller.ReplicaSetsByCreationTimestamp sort.Interface #sl in
    (FuncResolve sort.Sort [] #()) "$a0")%E).
  iApply (wp_Sort_sorted controller.ReplicaSetsByCreationTimestamp
    (rs_by_creation_contents dq3) rs_entry_created_before sl entries
    with "[$Hsort $Hcontents]").
  { iPureIntro. apply rs_created_before_strict_weak_order. rewrite Hsnd. exact Htimes. }
  iNext. iIntros (sorted) "[Hcontents [%Hperm %Hsorted]]".
  iDestruct "Hcontents" as "[Hsl Hrss]".
  set ptrs' := sorted.*1. set rss' := sorted.*2.
  assert (zip ptrs' rss' = sorted) as Hzip by apply zip_fst_snd.
  iAssert ([∗ list] ptr;rs ∈ ptrs';rss', ReplicaSetV.deepown_l ptr rs dq3)%I
    with "[Hrss]" as "Hrss".
  { rewrite big_sepL2_alt Hzip. iFrame. iPureIntro. rewrite /ptrs' /rss' !length_fmap. done. }
  assert (zip ptrs rss ≡ₚ zip ptrs' rss' ∧ sorted_by rs_created_before rss') as Hsort_post.
  { split; [rewrite Hzip; exact Hperm|].
    intros i j x y Hij Hx Hy.
    rewrite /rss' list_lookup_fmap in Hx. rewrite /rss' list_lookup_fmap in Hy.
    destruct (sorted !! i) as [ex|] eqn:Hex; [|done].
    destruct (sorted !! j) as [ey|] eqn:Hey; [|done].
    simplify_eq/=. exact (Hsorted i j ex ey Hij Hex Hey). }
  assert (Forall (λ rs, template_has_labels rs.(ReplicaSetV.Spec').(ReplicaSetSpecV.Template')) rss')
    as Hlabels'.
  { rewrite /rss' -Hzip. apply Forall_forall. intros r Hr.
    apply (Forall_forall _ rss) ; [exact (proj2 Hlabels)|].
    rewrite -Hsnd. apply list_elem_of_fmap in Hr as [e [-> He]].
    apply list_elem_of_fmap_2. rewrite Hperm. rewrite Hzip in He. exact He. }
  clear Hperm Hsorted Hzip Hfst Hsnd Htimes.
  clear entries. clearbody ptrs' rss'. clear ptrs rss Hlen0.
  rename ptrs' into ptrs. rename rss' into rss.
  destruct Hlabels as [Hd_labels _]. pose proof (conj Hd_labels Hlabels') as Hlabels.
  clear Hd_labels Hlabels'.
  wp_auto_keep.
  iDestruct (own_slice_len with "Hsl") as %(Hsl_len1 & Hsl_len2).
  iDestruct (own_slice_wf with "Hsl") as %Hsl_cap.
  iDestruct (big_sepL2_length with "Hrss") as %Hptrs_rss_len.
  set P := (λ rs : ReplicaSetV.t, template_matches rs.(ReplicaSetV.Spec').(ReplicaSetSpecV.Template')
    d.(DeploymentV.Spec').(DeploymentSpecV.Template')).
  (* The range loop's own index shares the name "i" with the Go loop variable,
     so wp_auto_keep does not allocate it. *)
  wp_alloc i_ptr0 as "i0". wp_auto_keep.
  (* The loop has scanned rss[0..i) without finding a matching template. *)
  set I := (∃ (i : w64) (i_value : w64),
    "Hi_ptr" ∷ i_ptr0 ↦ i ∗
    "Hdeployment_ptr" ∷ deployment_ptr ↦ d_l ∗
    "Hd" ∷ DeploymentV.deepown_l d_l d dq1 ∗
    "Hi_value_ptr" ∷ i_ptr ↦ i_value ∗
    "Hrss" ∷ ([∗ list] ptr;rs ∈ ptrs;rss, ReplicaSetV.deepown_l ptr rs dq3) ∗
    "%Hi" ∷ ⌜ 0 ≤ sint.Z i ≤ sint.Z (slice.len sl) ⌝ ∗
    "%Hnot_found" ∷ ⌜ ∀ j r, (j < sint.nat i)%nat → rss !! j = Some r → ¬ P r ⌝
  )%I.
  iAssert I with "[i0 i deployment Hd Hrss]" as "Hloop_inv".
  { iExists (W64 0), (W64 0). iFrame.
    iPureIntro. split; [word|]. intros j r Hj. exfalso. word. }
  wp_for "Hloop_inv". wp_if_destruct.
  - list_elem ptrs (sint.Z i) as this_ptr.
    destruct (decide (0 ≤ sint.Z i < sint.Z (slice.len sl))) as [_|Hbounds]; last word.
    wp_apply (wp_load_slice_index with "[$Hsl]"); [word| |].
    { iPureIntro. exact Hthis_ptr_lookup. }
    iIntros "Hsl". wp_auto_keep.
    (* The body reads rsList[i] itself rather than the range value. *)
    destruct (decide (0 ≤ sint.Z i < sint.Z (slice.len sl))) as [_|Hbounds]; last word.
    wp_apply (wp_load_slice_index with "[$Hsl]"); [word| |].
    { iPureIntro. exact Hthis_ptr_lookup. }
    iIntros "Hsl". wp_auto_keep.
    assert (∃ this_rs, rss !! sint.nat i = Some this_rs) as [this_rs Hthis_rs_lookup].
    { apply lookup_lt_is_Some_2. rewrite -Hptrs_rss_len Hsl_len1. word. }
    iDestruct (big_sepL2_lookup_acc with "Hrss") as "[Hthis Hrss_restore]";
      [exact Hthis_ptr_lookup|exact Hthis_rs_lookup|].
    (* EqualIgnoreHash takes &rs.Spec.Template and &d.Spec.Template, so both
       specs have to be split all the way down to their Template fields. *)
    iPoseProof (ReplicaSetV.deepown_l_split with "Hthis") as
      "(%Hthis_not_null & Hthis_typemeta & Hthis_objectmeta_l & Hthis_spec_l & Hthis_status_l)".
    iDestruct "Hthis_spec_l" as (rs_spec_c) "[Hthis_spec_field Hthis_spec]".
    iDestruct (struct_fields_split (V:=v1.ReplicaSetSpec.t) with "Hthis_spec_field") as
      "[Hrs_spec_fields %Hrs_spec_not_null]".
    iNamedPrefix "Hrs_spec_fields" "Hrsf_".
    iPoseProof (DeploymentV.deepown_l_split with "Hd") as
      "(%Hd_not_null & Hd_typemeta & Hd_objectmeta_l & Hd_spec_l & Hd_status_l)".
    iDestruct "Hd_spec_l" as (d_spec_c) "[Hd_spec_field Hd_spec]".
    iDestruct (struct_fields_split (V:=v1.DeploymentSpec.t) with "Hd_spec_field") as
      "[Hd_spec_fields %Hd_spec_not_null]".
    iNamedPrefix "Hd_spec_fields" "Hdf_".
    iNamedPrefix "Hthis_spec" "Hrs_".
    iNamedPrefix "Hd_spec" "Hd_".
    assert (template_has_labels this_rs.(ReplicaSetV.Spec').(ReplicaSetSpecV.Template')) as Hthis_labels.
    { exact (Forall_lookup_1 _ _ _ _ (proj2 Hlabels) Hthis_rs_lookup). }
    wp_apply (wp_EqualIgnoreHash with
      "[$Hrsf_Template $Hrs_Hdeepown_template $Hdf_Template $Hd_Hdeepown_template]").
    { iPureIntro. split; [exact Hthis_labels|exact (proj1 Hlabels)]. }
    iIntros "(Hrsf_Template & Hrs_Hdeepown_template & Hdf_Template & Hd_Hdeepown_template)".
    (* Put both objects back together before branching. *)
    iCombineNamed "Hrsf_*" as "Hrs_spec_fields".
    iAssert (typed_pointsto_def (ReplicaSetV.spec_ptr this_ptr) rs_spec_c dq3)
      with "[Hrs_spec_fields]" as "Hrs_spec_fields".
    { iNamed "Hrs_spec_fields". destruct rs_spec_c. simpl. iFrame. }
    iDestruct (struct_fields_combine _ _ _ Hrs_spec_not_null with "Hrs_spec_fields")
      as "Hthis_spec_field".
    iCombineNamed "Hdf_*" as "Hd_spec_fields".
    iAssert (typed_pointsto_def (DeploymentV.spec_ptr d_l) d_spec_c dq1)
      with "[Hd_spec_fields]" as "Hd_spec_fields".
    { iNamed "Hd_spec_fields". destruct d_spec_c. simpl. iFrame. }
    iDestruct (struct_fields_combine _ _ _ Hd_spec_not_null with "Hd_spec_fields")
      as "Hd_spec_field".
    iCombineNamed "Hrs_Hdeepown_*" as "Hthis_spec_parts".
    iAssert (ReplicaSetSpecV.deepown rs_spec_c (ReplicaSetV.Spec' this_rs) dq3)
      with "[Hthis_spec_parts]" as "Hthis_spec".
    { iNamed "Hthis_spec_parts". iFrame. done. }
    iCombineNamed "Hd_Hdeepown_*" as "Hd_spec_parts".
    iAssert (DeploymentSpecV.deepown d_spec_c (DeploymentV.Spec' d) dq1)
      with "[Hd_spec_parts]" as "Hd_spec".
    { iNamed "Hd_spec_parts". iFrame. done. }
    iPoseProof (ReplicaSetV.deepown_l_restore _ _ _ Hthis_not_null
      with "[$Hthis_typemeta $Hthis_objectmeta_l $Hthis_status_l Hthis_spec_field Hthis_spec]")
      as "Hthis".
    { iExists rs_spec_c. iFrame. }
    iPoseProof (DeploymentV.deepown_l_restore _ _ _ Hd_not_null
      with "[$Hd_typemeta $Hd_objectmeta_l $Hd_status_l Hd_spec_field Hd_spec]") as "Hd".
    { iExists d_spec_c. iFrame. }
    iSpecialize ("Hrss_restore" with "Hthis").
    iRename "Hrss_restore" into "Hrss".
    wp_if_destruct.
    + (* This template matches, and Hnot_found rules out every earlier one, so
         this index is the one list_find picks. *)
      destruct (decide (0 ≤ sint.Z i < sint.Z (slice.len sl))) as [_|Hbounds]; last word.
      wp_apply (wp_load_slice_index with "[$Hsl]"); [word| |].
      { iPureIntro. exact Hthis_ptr_lookup. }
      iIntros "Hsl".
      wp_auto_keep. iApply wp_for_post_return. wp_auto_keep.
      assert (list_find P rss = Some (sint.nat i, this_rs)) as Hfind.
      { apply list_find_Some. split_and!.
        - exact Hthis_rs_lookup.
        - assumption.
        - intros j r Hlookup Hj HP.
          eapply (Hnot_found j r); [lia|exact Hlookup|exact HP]. }
      iApply ("HΦ" $! this_ptr ptrs rss). rewrite -/P Hfind. iFrame. done.
    + iApply wp_for_post_do. wp_auto_keep.
      iFrame "Hsl HΦ rsList".
      iExists (word.add i (W64 1)), _.
      iFrame.
      iPureIntro. split; [word|].
      intros j r Hj Hlookup HP.
      destruct (decide (j < sint.nat i)%nat) as [Hj_old|Hj_not_old].
      * eapply (Hnot_found j r); done.
      * assert (j = sint.nat i) as -> by word.
        rewrite Hthis_rs_lookup in Hlookup.
        injection Hlookup as <-.
        contradiction.
  - (* The loop ran off the end, so no template matched. *)
    assert (sint.nat i = length rss) as Hi_len.
    { rewrite -Hptrs_rss_len Hsl_len1. word. }
    assert (list_find P rss = None) as Hfind.
    { apply list_find_None. apply Forall_forall.
      intros r Hr HP.
      rewrite -list_elem_of_In in Hr.
      apply list_elem_of_lookup_1 in Hr as [j Hlookup].
      eapply (Hnot_found j r); [|exact Hlookup|exact HP].
      rewrite Hi_len. apply lookup_lt_Some in Hlookup. lia. }
    iApply ("HΦ" $! null ptrs rss). rewrite -/P Hfind. iFrame. done.
Qed.

End proof.
