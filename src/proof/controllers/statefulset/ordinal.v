From New.proof.controllers Require Export common.
From New.proof.controllers.statefulset Require Import pod_predicates.
From New.proof.controllers.statefulset Require Export statefulset_init.
From New.proof.k8s_io.api.apps Require Export v1.

Section proof.
Context `{hG: !heapGS Σ} `{!ffi_semantics _ _}.
Context {sem : go.Semantics}
  {package_sem : code.controllers.statefulset.statefulset.Assumptions}.
Collection W := sem + package_sem.
#[local] Instance base_common_sem : common.Assumptions | 100 :=
  code.controllers.statefulset.statefulset.import_common_Assumption.
#[local] Instance controller_sem : controller.Assumptions :=
  code.controllers.statefulset.statefulset.import_controller_Assumption.
#[local] Instance runtime_sem : code.k8s_io.apimachinery.pkg.runtime.runtime.Assumptions :=
  controller.import_runtime_Assumption.
#[local] Instance runtime_object_underlying_eq :
    runtime.Object ≤u runtime.Objectⁱᵐᵖˡ.
Proof using package_sem. apply _. Qed.
#[local] Instance meta_object_underlying_eq :
    meta_v1.Object ≤u meta_v1.Objectⁱᵐᵖˡ.
Proof using package_sem. apply _. Qed.
#[local] Instance base_apimodel_sem : apimodel.Assumptions | 100 :=
  common.import_apimodel_Assumption.
#[local] Instance object_meta_v1_sem :
    code.k8s_io.apimachinery.pkg.apis.meta.v1.v1.Assumptions :=
  apimodel.import_apis_meta_v1_Assumption.
#[local] Instance object_apps_v1_sem :
    code.k8s_io.api.apps.v1.v1.Assumptions :=
  apimodel.import_api_apps_v1_Assumption.
#[local] Instance object_core_v1_sem :
    code.k8s_io.api.core.v1.v1.Assumptions :=
  code.k8s_io.api.apps.v1.v1.import_core_v1_Assumption.
#[local] Instance apimodel_sem : apimodel.Assumptions | 0.
Proof using package_sem.
  constructor; try exact object_core_v1_sem; try apply _.
Defined.
#[local] Instance common_sem : common.Assumptions | 0.
Proof using package_sem.
  constructor; try exact apimodel_sem; try apply _.
Defined.
Context `{!kubernetesModelG Σ}.
Local Set Default Proof Using "All".

Definition find_pod_by_ordinal
    (set_name : go_string) (ordinal : nat) (pods : list PodV.t) :
    option (nat * PodV.t) :=
  list_find (λ pod,
    pod.(PodV.ObjectMeta').(ObjectMetaV.Name') =
      desired_pod_name set_name ordinal) pods.

Lemma pod_ordinal_suffix_last_dash pod_name parent suffix :
  pod_name = parent ++ [byte_dash] ++ suffix →
  byte_dash ∉ suffix →
  pod_ordinal_suffix pod_name = Some suffix.
Proof.
  intros -> Hsuffix.
  unfold pod_ordinal_suffix.
  rewrite !reverse_app /=.
  assert (list_find (λ b, b = byte_dash)
      (reverse suffix ++ byte_dash :: reverse parent) =
      Some (length suffix, byte_dash)) as Hfind.
  { apply list_find_Some. split_and!.
    - erewrite lookup_app_r.
      2: { rewrite length_reverse. lia. }
      rewrite length_reverse Nat.sub_diag. done.
    - done.
    - intros j b Hlookup Hj Heq. subst b. apply Hsuffix.
      assert ((j < length (reverse suffix))%nat) as Hj'.
      { rewrite length_reverse. exact Hj. }
      rewrite (lookup_app_l _ _ _ Hj') in Hlookup.
      apply list_elem_of_lookup_2 in Hlookup.
      by apply (proj1 (elem_of_reverse _ _)) in Hlookup. }
  rewrite reverse_singleton -List.app_assoc.
  rewrite Hfind /=.
  replace (length suffix) with (length (reverse suffix)) by
    exact (length_reverse suffix).
  rewrite take_app_length reverse_involutive. done.
Qed.

Lemma pod_ordinal_suffix_no_dash pod_name :
  byte_dash ∉ pod_name →
  pod_ordinal_suffix pod_name = None.
Proof.
  intros Hno_dash. unfold pod_ordinal_suffix.
  assert (list_find (λ b, b = byte_dash) (reverse pod_name) = None)
    as Hfind.
  { apply list_find_None. apply Forall_forall.
    intros b Hb Heq. apply Hno_dash. subst b.
    rewrite -list_elem_of_In in Hb.
    apply (proj1 (elem_of_reverse _ _)). exact Hb. }
  rewrite Hfind. done.
Qed.

Lemma wp_replicasOf set_l (set : StatefulSetV.t) dq :
  {{{ StatefulSetV.deepown_l set_l set dq ∗
      ⌜ StatefulSetSpecV.valid set.(StatefulSetV.Spec') ⌝ }}}
    @! statefulset.replicasOf #set_l
  {{{ (replicas : w64), RET #replicas;
      ⌜ sint.Z replicas = Z.of_nat (statefulset_replicas set) ⌝ ∗
      StatefulSetV.deepown_l set_l set dq
  }}}.
Proof.
  wp_start as "(Hset & %Hvalid)".
  iPoseProof (StatefulSetV.deepown_l_split with "Hset") as
    "(%Hset_l_not_null & Htypemeta & Hobjectmeta & Hspec_l & Hstatus_l)".
  iDestruct "Hspec_l" as (spec_c) "[Hspec_field Hspec]".
  iNamed "Hspec".
  pose proof (StatefulSetSpecV.valid_replicas _ Hvalid) as
    (replicas32 & Hreplicas_eq & Hreplicas_nonnegative).
  rewrite Hreplicas_eq.
  iDestruct "Hdeepown_replicas_some" as (replicas32_c)
    "[Hreplicas %Hreplicas32_c_eq]".
  subst replicas32_c.
  assert (spec_c.(v1.StatefulSetSpec.Replicas') ≠ null) as Hreplicas_ptr_not_null.
  { intros Hreplicas_ptr_null.
    apply Hdeepown_replicas_none in Hreplicas_ptr_null.
    congruence. }
  wp_auto.
  wp_if_destruct.
  { exfalso. done. }
  wp_pures.
  iApply ("HΦ" $! (W64 (sint.Z replicas32))).
  iSplitR.
  { iPureIntro.
    replace (sint.Z (W64 (sint.Z replicas32))) with (sint.Z replicas32) by word.
    unfold statefulset_replicas.
    rewrite Hreplicas_eq.
    replace (Z.of_nat (sint.nat replicas32)) with (sint.Z replicas32) by word.
    done. }
  iApply (StatefulSetV.deepown_l_restore _ _ _ Hset_l_not_null).
  iFrame "Htypemeta Hobjectmeta Hstatus_l".
  unfold StatefulSetSpecV.deepown_l, StatefulSetV.spec_ptr.
  iExists spec_c.
  iFrame "Hspec_field".
  unfold StatefulSetSpecV.deepown.
  iSplit; first done.
  iSplitL "Hreplicas".
  {
  rewrite Hreplicas_eq.
  iExists replicas32.
  iFrame.
  done.
  }
  iFrame.
  done.
Qed.

Lemma wp_endOrdinalOf set_l (set : StatefulSetV.t) dq :
  {{{ StatefulSetV.deepown_l set_l set dq ∗
      ⌜ StatefulSetSpecV.valid set.(StatefulSetV.Spec') ⌝ }}}
    @! statefulset.endOrdinalOf #set_l
  {{{ (end_ordinal : w64), RET #end_ordinal;
      ⌜ sint.Z end_ordinal = Z.of_nat (statefulset_replicas set) - 1 ⌝ ∗
      StatefulSetV.deepown_l set_l set dq
  }}}.
Proof.
  wp_start as "(Hset & %Hvalid)".
  wp_auto.
  wp_apply (wp_replicasOf with "[$Hset //]").
  iIntros (replicas) "[%Hreplicas Hset]".
  wp_pures.
  iApply "HΦ".
  iFrame.
  iPureIntro.
  assert (sint.Z (word.sub replicas (W64 1)) = sint.Z replicas - 1) as -> by word.
  rewrite Hreplicas.
  done.
Qed.

Lemma wp_podName (set_name : go_string) (ordinal : w64) :
  {{{ ⌜ 0 <= sint.Z ordinal ⌝ }}}
    @! statefulset.podName #set_name #ordinal
  {{{ RET #(set_name ++ "-"%go ++ decimal_string (sint.nat ordinal)); True }}}.
Proof.
  wp_start as "%Hordinal_nonnegative".
  wp_auto.
  wp_apply (wp_strconv_Itoa with "[]").
  { iSplit; first by iEval (rewrite is_pkg_init_unfold /=).
    iPureIntro. exact Hordinal_nonnegative. }
  wp_pures.
  iEval (rewrite List.app_assoc) in "HΦ".
  iApply "HΦ".
  done.
Qed.

Lemma wp_claimName
    (set_name claim_template_name : go_string) (ordinal : w64) :
  {{{ ⌜ 0 <= sint.Z ordinal ⌝ }}}
    @! statefulset.claimName #set_name #claim_template_name #ordinal
  {{{ RET #(claim_template_name ++ "-"%go ++ set_name ++ "-"%go ++
        decimal_string (sint.nat ordinal)); True }}}.
Proof.
  wp_start as "%Hordinal_nonnegative".
  wp_auto.
  wp_apply (wp_strconv_Itoa with "[]").
  { iSplit; first by iEval (rewrite is_pkg_init_unfold /=).
    iPureIntro. exact Hordinal_nonnegative. }
  wp_pures.
  iEval (rewrite !List.app_assoc) in "HΦ".
  iApply "HΦ".
  done.
Qed.

Lemma wp_parentNameAndOrdinal (pod_name : go_string) :
  {{{ ⌜ Z.of_nat (length pod_name) <= go_int_max ⌝ }}}
    @! statefulset.parentNameAndOrdinal #pod_name
  {{{ (parent : go_string) (ordinal : w64), RET (#parent, #ordinal);
      ⌜ ∀ set_name,
        (parent = set_name ∧
          0 <= sint.Z ordinal ∧
          pod_name = desired_pod_name set_name (sint.nat ordinal)) ↔
        pod_has_int32_member_name set_name pod_name ⌝
  }}}.
Proof.
  wp_start as "%Hpod_name_len".
  wp_auto.
  wp_apply (wp_strings_LastIndex_singleton pod_name byte_dash with "[]").
  { iSplit; first by iEval (rewrite is_pkg_init_unfold /=).
    iPureIntro. exact Hpod_name_len. }
  iIntros (idx) "%Hidx".
  wp_auto.
  destruct Hidx as [(parent & suffix & Hname_decomp & Hsuffix_no_dash & Hidx_Z)|
                    (Hno_dash & Hidx_Z)].
  - assert (Hprefix_next_bound : Z.of_nat (S (length parent)) <= go_int_max).
    { rewrite Hname_decomp app_length /= in Hpod_name_len. lia. }
    unfold go_int_max in Hprefix_next_bound.
    assert (Hidx_next_Z : sint.Z (word.add idx (W64 1)) =
        Z.of_nat (S (length parent))) by word.
    assert (Hidx_nat : sint.nat idx = length parent) by word.
    assert (Hidx_next_nonneg : 0 <= sint.Z (word.add idx (W64 1))).
    { rewrite Hidx_next_Z. lia. }
    assert (Hidx_next : sint.nat (word.add idx (W64 1)) = S (length parent)) by word.
    wp_if_destruct.
    { exfalso. rewrite Hidx_Z in l. change (sint.Z (W64 0)) with 0 in l. lia. }
    wp_pures.
    wp_pures.
    wp_bind (Slice go.string
      ((#(parent ++ [byte_dash] ++ suffix), #(word.add idx (W64 1)))%V,
       #(functions go.len [go.string]) (#(parent ++ [byte_dash] ++ suffix))))%E.
    iApply (wp_wand _ _ _
      (λ v, ⌜ v = #(drop (sint.nat (word.add idx (W64 1)))
        (parent ++ [byte_dash] ++ suffix)) ⌝)%I with "[]").
    { iApply (wp_string_slice_to_end
        (parent ++ [byte_dash] ++ suffix) (word.add idx (W64 1))).
      - iPureIntro.
        split; [exact Hidx_next_nonneg|].
        rewrite Hidx_next app_length /=.
        lia.
      - iIntros "_".
        iPureIntro.
        done. }
    iIntros (suffix_val) "->".
    assert (drop (sint.nat (word.add idx (W64 1)))
      (parent ++ [byte_dash] ++ suffix) = suffix) as Hdrop_suffix.
    { rewrite Hidx_next.
      clear Hpod_name_len Hsuffix_no_dash Hidx_Z Hprefix_next_bound
        Hidx_next_Z Hidx_nat Hidx_next_nonneg Hidx_next.
      induction parent as [|b parent IH]; simpl; [done|exact IH]. }
    rewrite Hdrop_suffix.
    wp_pures.
    wp_apply (wp_strconv_ParseInt_decimal_int32 with "[]").
    { by iEval (rewrite is_pkg_init_unfold /=). }
    iIntros (ordinal err) "%Hparse".
    wp_auto.
    destruct (parse_decimal_string suffix) as [expected_ordinal|] eqn:Hparse_suffix.
    + destruct (decide (expected_ordinal <= go_int32_max_nat)%nat) as
        [Hexpected_ordinal_bound|Hexpected_ordinal_overflow].
      * destruct Hparse as (Herr_nil & Hordinal_nat & Hordinal_Z & Hordinal_bounds).
        rewrite Herr_nil.
        wp_auto.
        wp_bind (Slice go.string
          (#(parent ++ [byte_dash] ++ suffix), #(W64 0), #idx)%V)%E.
        iApply (wp_wand _ _ _
          (λ v, ⌜ v = #(subslice (sint.nat (W64 0)) (sint.nat idx)
            (parent ++ [byte_dash] ++ suffix)) ⌝)%I with "[]").
        { iApply (wp_string_slice
            (parent ++ [byte_dash] ++ suffix) (W64 0) idx).
          - iPureIntro.
            split.
            + split; [word|].
              rewrite Hidx_Z.
              lia.
            + rewrite Hidx_nat app_length /=.
              lia.
          - iIntros "_".
            iPureIntro.
            done. }
        iIntros (parent_val) "->".
        wp_auto.
        rewrite /subslice /= Hidx_nat.
        rewrite drop_0.
        rewrite take_app_length.
        assert (Hpost : ∀ set_name,
          (parent = set_name ∧ 0 <= sint.Z ordinal ∧
            (parent ++ [byte_dash] ++ suffix) =
              desired_pod_name set_name (sint.nat ordinal)) ↔
          pod_has_int32_member_name set_name (parent ++ [byte_dash] ++ suffix)).
        { intros set_name. split.
          - intros (Hparent_eq & _ & Hname).
            subst set_name.
            unfold pod_has_int32_member_name.
            exists expected_ordinal.
            split; [done|].
            by rewrite -Hordinal_nat.
          - intros Hex.
            unfold pod_has_int32_member_name in Hex.
            destruct Hex as (ordinal' & Hordinal'_bound & Hcanonical).
            pose proof (desired_pod_name_last_dash_decomp
              (parent ++ [byte_dash] ++ suffix) parent suffix set_name ordinal'
              eq_refl Hsuffix_no_dash Hcanonical) as [-> Hsuffix].
            rewrite Hsuffix parse_decimal_string_decimal_string in Hparse_suffix.
            simplify_eq/=.
            repeat split; try done; try lia. }
        iApply ("HΦ" $! parent ordinal).
        iPureIntro.
        exact Hpost.
      * destruct err as [err_i|].
        2: { exfalso. apply Hparse. reflexivity. }
        wp_pures.
        iApply ("HΦ" $! ""%go (W64 (-1))).
        iPureIntro.
        intros set_name. split.
        -- intros (_ & Hnonnegative & _). word.
        -- intros (ordinal' & Hordinal'_bound & Hname).
           pose proof (desired_pod_name_last_dash_decomp
             (parent ++ [byte_dash] ++ suffix) parent suffix set_name ordinal'
             eq_refl Hsuffix_no_dash Hname) as [_ Hsuffix].
           rewrite Hsuffix parse_decimal_string_decimal_string in Hparse_suffix.
           simplify_eq/=.
    + destruct err as [err_i|].
      2: { exfalso. apply Hparse. reflexivity. }
      wp_pures.
      iApply ("HΦ" $! ""%go (W64 (-1))).
      iPureIntro.
      intros set_name. split.
      * intros (_ & Hnonnegative & _). word.
      * intros (ordinal' & Hordinal'_bound & Hname).
        pose proof (desired_pod_name_last_dash_decomp
          (parent ++ [byte_dash] ++ suffix) parent suffix set_name ordinal'
          eq_refl Hsuffix_no_dash Hname) as [_ Hsuffix].
        rewrite Hsuffix parse_decimal_string_decimal_string in Hparse_suffix.
        done.
  - 
    wp_if_destruct.
    2: { exfalso. word. }
    wp_pures.
    iApply ("HΦ" $! ""%go (W64 (-1))).
    iPureIntro.
    intros set_name. split.
    + intros (_ & Hnonnegative & _). word.
    + intros (ordinal' & Hordinal'_bound & Hname).
      exfalso.
      apply Hno_dash.
      rewrite Hname.
      apply desired_pod_name_has_dash.
Qed.

Lemma wp_findPodByOrdinal set_l pods_sl
    (set : StatefulSetV.t) (ptrs : list loc) (pods : list PodV.t)
    (ordinal : w64) dq_set dq_pods :
  {{{ "Hset" ∷ StatefulSetV.deepown_l set_l set dq_set ∗
      "Hpods_sl" ∷ pods_sl ↦* ptrs ∗
      "Hpods" ∷ ([∗ list] ptr;pod ∈ ptrs;pods,
        PodV.deepown_l ptr pod dq_pods) ∗
      "%Hordinal" ∷ ⌜ 0 ≤ sint.Z ordinal ∧
        (sint.nat ordinal ≤ go_int32_max_nat)%nat ⌝ ∗
      "%Hpod_name_len" ∷ ⌜ ∀ pod, pod ∈ pods →
        Z.of_nat (length pod.(PodV.ObjectMeta').(ObjectMetaV.Name')) ≤
          go_int_max ⌝ ∗
      "%Hpods_members" ∷ ⌜ Forall (λ pod,
        pod_has_int32_member_name
          set.(StatefulSetV.ObjectMeta').(ObjectMetaV.Name')
          pod.(PodV.ObjectMeta').(ObjectMetaV.Name')) pods ⌝
  }}}
    @! statefulset.findPodByOrdinal #set_l #pods_sl #ordinal
  {{{ pod_l, RET #pod_l;
      StatefulSetV.deepown_l set_l set dq_set ∗
      pods_sl ↦* ptrs ∗
      ([∗ list] ptr;pod ∈ ptrs;pods,
        PodV.deepown_l ptr pod dq_pods) ∗
      ⌜ match find_pod_by_ordinal
          set.(StatefulSetV.ObjectMeta').(ObjectMetaV.Name')
          (sint.nat ordinal) pods with
        | Some (idx, _) => ptrs !! idx = Some pod_l
        | None => pod_l = null
        end ⌝
  }}}.
Proof.
  wp_start as "H". iNamed "H".
  wp_auto.
  iDestruct (own_slice_len with "Hpods_sl") as %(Hpods_sl_len1 & Hpods_sl_len2).
  iDestruct (own_slice_wf with "Hpods_sl") as %Hpods_sl_cap.
  iDestruct (big_sepL2_length with "Hpods") as %Hptrs_pods_len.
  set set_name := set.(StatefulSetV.ObjectMeta').(ObjectMetaV.Name').
  set P := (λ pod,
    pod.(PodV.ObjectMeta').(ObjectMetaV.Name') =
      desired_pod_name set_name (sint.nat ordinal)).
  set I := (∃ (i : w64) (pod_ptr_value : loc),
    "Hi_ptr" ∷ i_ptr ↦ i ∗
    "Hset_ptr" ∷ set_ptr ↦ set_l ∗
    "Hset" ∷ StatefulSetV.deepown_l set_l set dq_set ∗
    "Hpod_ptr" ∷ pod_ptr ↦ pod_ptr_value ∗
    "Hpods" ∷ ([∗ list] ptr;pod ∈ ptrs;pods,
      PodV.deepown_l ptr pod dq_pods) ∗
    "%Hi" ∷ ⌜ 0 ≤ sint.Z i ≤ sint.Z (slice.len pods_sl) ⌝ ∗
    "%Hnot_found" ∷ ⌜ ∀ j pod,
      (j < sint.nat i)%nat → pods !! j = Some pod → ¬ P pod ⌝
  )%I.
  iAssert I with "[i set Hset pod Hpods]" as "Hloop_inv".
  { iExists (W64 0), null. iFrame.
    iPureIntro. split; [word|]. intros j pod Hj. exfalso. word. }
  wp_for "Hloop_inv". wp_if_destruct.
  - list_elem ptrs (sint.Z i) as this_ptr.
    destruct (decide (0 ≤ sint.Z i < sint.Z (slice.len pods_sl)))
      as [_|Hbounds]; last word.
    wp_apply (wp_load_slice_index with "[$Hpods_sl]"); [word| |].
    { iPureIntro. exact Hthis_ptr_lookup. }
    iIntros "Hpods_sl". wp_auto.
    assert (∃ this_pod, pods !! sint.nat i = Some this_pod) as
      [this_pod Hthis_pod_lookup].
    { apply lookup_lt_is_Some_2.
      rewrite -Hptrs_pods_len Hpods_sl_len1. word. }
    iDestruct (big_sepL2_lookup_acc with "Hpods") as
      "[Hthis Hpods_restore]";
      [exact Hthis_ptr_lookup|exact Hthis_pod_lookup|].
    iPoseProof (PodV.deepown_l_split with "Hthis") as
      "(%Hthis_not_null & Hthis_typemeta & Hthis_objectmeta_l & Hthis_spec_l & Hthis_status_l)".
    iDestruct "Hthis_objectmeta_l" as
      (this_meta_c) "[Hthis_objectmeta_field Hthis_objectmeta]".
    iNamedPrefix "Hthis_objectmeta" "Hthis_meta_".
    iPoseProof (StatefulSetV.deepown_l_split with "Hset") as
      "(%Hset_l_not_null & Hset_typemeta & Hset_objectmeta_l & Hset_spec_l & Hset_status_l)".
    iDestruct "Hset_objectmeta_l" as
      (set_meta_c) "[Hset_objectmeta_field Hset_objectmeta]".
    iNamedPrefix "Hset_objectmeta" "Hset_meta_".
    wp_auto.
    rewrite Hthis_meta_Hdeepown_name.
    wp_apply (wp_parentNameAndOrdinal with "[]").
    { iPureIntro. apply Hpod_name_len.
      by apply list_elem_of_lookup_2 in Hthis_pod_lookup. }
    iIntros (parent pod_ordinal) "%Hparent".
    assert (pod_has_int32_member_name set_name
      this_pod.(PodV.ObjectMeta').(ObjectMetaV.Name')) as Hthis_member.
    { unfold set_name. rewrite Forall_forall in Hpods_members.
      apply Hpods_members.
      rewrite -list_elem_of_In.
      eapply list_elem_of_lookup_2. exact Hthis_pod_lookup. }
    destruct (proj2 (Hparent set_name) Hthis_member) as
      (Hparent_eq & Hpod_ordinal_nonnegative & Hthis_name).
    subst parent.
    unfold set_name in *.
    wp_auto.
    rewrite Hset_meta_Hdeepown_name.
    iCombineNamed "Hset_meta_*" as "Hset_objectmeta".
    iAssert (ObjectMetaV.deepown set_meta_c
        set.(StatefulSetV.ObjectMeta') dq_set)
      with "[Hset_objectmeta]" as "Hset_objectmeta".
    { iNamed "Hset_objectmeta". iFrame. done. }
    iAssert (ObjectMetaV.deepown_l (StatefulSetV.objectmeta_ptr set_l)
        set.(StatefulSetV.ObjectMeta') dq_set)
      with "[Hset_objectmeta_field Hset_objectmeta]" as "Hset_objectmeta_l".
    { iExists set_meta_c. iFrame. }
    iPoseProof (StatefulSetV.deepown_l_restore _ _ _ Hset_l_not_null
      with "[$Hset_typemeta $Hset_objectmeta_l $Hset_spec_l $Hset_status_l]") as "Hset".
    iCombineNamed "Hthis_meta_*" as "Hthis_objectmeta".
    iAssert (ObjectMetaV.deepown this_meta_c
        this_pod.(PodV.ObjectMeta') dq_pods)
      with "[Hthis_objectmeta]" as "Hthis_objectmeta".
    { iNamed "Hthis_objectmeta". iFrame. done. }
    iAssert (ObjectMetaV.deepown_l (PodV.objectmeta_ptr this_ptr)
        this_pod.(PodV.ObjectMeta') dq_pods)
      with "[Hthis_objectmeta_field Hthis_objectmeta]" as "Hthis_objectmeta_l".
    { iExists this_meta_c. iFrame. }
    iPoseProof (PodV.deepown_l_restore _ _ _ Hthis_not_null
      with "[$Hthis_typemeta $Hthis_objectmeta_l $Hthis_spec_l $Hthis_status_l]") as "Hthis".
    iSpecialize ("Hpods_restore" with "Hthis").
    iRename "Hpods_restore" into "Hpods".
    replace (bool_decide
      (set.(StatefulSetV.ObjectMeta').(ObjectMetaV.Name') =
       set.(StatefulSetV.ObjectMeta').(ObjectMetaV.Name'))) with true by
      (symmetry; apply bool_decide_eq_true_2; done).
    destruct (decide (pod_ordinal = ordinal)) as [->|Hordinal_ne].
    + wp_auto.
      replace (bool_decide (ordinal = ordinal)) with true by
        (symmetry; apply bool_decide_eq_true_2; done).
      wp_auto.
      iApply wp_for_post_return.
      wp_pures.
      iApply ("HΦ" $! this_ptr). iFrame.
      iPureIntro.
      unfold find_pod_by_ordinal.
      assert (list_find P pods = Some (sint.nat i, this_pod)) as Hfind.
      { apply list_find_Some. split_and!.
        * exact Hthis_pod_lookup.
        * unfold P in *. rewrite -Hthis_name. done.
        * intros j pod Hlookup Hj HP.
          eapply (Hnot_found j pod); [lia|exact Hlookup|exact HP]. }
      rewrite Hfind. exact Hthis_ptr_lookup.
    + wp_auto.
      replace (bool_decide (pod_ordinal = ordinal)) with false by
        (symmetry; apply bool_decide_eq_false_2; done).
      wp_auto.
      iApply wp_for_post_do. wp_auto.
      iFrame "ordinal Hpods_sl HΦ".
      iExists (word.add i (W64 1)), this_ptr.
      iFrame.
      iPureIntro. split; [word|].
      intros j pod Hj Hlookup HP.
      destruct (decide (j < sint.nat i)%nat) as [Hj_old|Hj_not_old].
      * eapply (Hnot_found j pod); done.
      * assert (j = sint.nat i) as -> by word.
        rewrite Hthis_pod_lookup in Hlookup. simplify_eq/=.
        unfold P in HP.
        apply Hordinal_ne.
        apply word.signed_inj.
        replace (sint.Z ordinal) with (Z.of_nat (sint.nat ordinal)) by word.
        replace (sint.Z pod_ordinal) with (Z.of_nat (sint.nat pod_ordinal)) by word.
        apply f_equal.
        apply (desired_pod_name_inj set_name).
        rewrite -Hthis_name. exact HP.
  - assert (sint.nat i = length pods) as Hi_len.
    { rewrite -Hptrs_pods_len Hpods_sl_len1. word. }
    iApply ("HΦ" $! null). iFrame.
    iPureIntro.
    unfold find_pod_by_ordinal.
    change (match list_find P pods with
      | Some (idx, _) => ptrs !! idx = Some null
      | None => null = null
      end).
    assert (list_find P pods = None) as Hfind.
    { apply list_find_None. apply Forall_forall.
      intros pod Hpod HP.
      rewrite -list_elem_of_In in Hpod.
      apply list_elem_of_lookup_1 in Hpod as [j Hlookup].
      eapply (Hnot_found j pod); [|exact Hlookup|exact HP].
      rewrite Hi_len. apply lookup_lt_Some in Hlookup. lia. }
    rewrite Hfind. done.
Qed.

Lemma wp_parentNameAndOrdinal_parse (pod_name : go_string) :
  {{{ ⌜ Z.of_nat (length pod_name) <= go_int_max ⌝ }}}
    @! statefulset.parentNameAndOrdinal #pod_name
  {{{ (parent : go_string) (ordinal : w64), RET (#parent, #ordinal);
      ⌜ match parse_pod_ordinal pod_name with
        | Some expected_ordinal =>
            if decide (expected_ordinal <= go_int32_max_nat)%nat
            then sint.Z ordinal = Z.of_nat expected_ordinal
            else sint.Z ordinal < 0
        | None => sint.Z ordinal < 0
        end ⌝
  }}}.
Proof.
  wp_start as "%Hpod_name_len".
  wp_auto.
  wp_apply (wp_strings_LastIndex_singleton pod_name byte_dash with "[]").
  { iSplit; first by iEval (rewrite is_pkg_init_unfold /=).
    iPureIntro. exact Hpod_name_len. }
  iIntros (idx) "%Hidx".
  wp_auto.
  destruct Hidx as
    [(parent & suffix & Hname_decomp & Hsuffix_no_dash & Hidx_Z)|
     (Hno_dash & Hidx_Z)].
  - assert (Hpod_ordinal_suffix :
      pod_ordinal_suffix pod_name = Some suffix).
    { by apply (pod_ordinal_suffix_last_dash pod_name parent suffix). }
    assert (Hprefix_next_bound : Z.of_nat (S (length parent)) <= go_int_max).
    { rewrite Hname_decomp app_length /= in Hpod_name_len. lia. }
    unfold go_int_max in Hprefix_next_bound.
    assert (Hidx_next_Z : sint.Z (word.add idx (W64 1)) =
        Z.of_nat (S (length parent))) by word.
    assert (Hidx_nat : sint.nat idx = length parent) by word.
    assert (Hidx_next_nonneg : 0 <= sint.Z (word.add idx (W64 1))).
    { rewrite Hidx_next_Z. lia. }
    assert (Hidx_next : sint.nat (word.add idx (W64 1)) =
        S (length parent)) by word.
    wp_if_destruct.
    { exfalso. rewrite Hidx_Z in l.
      change (sint.Z (W64 0)) with 0 in l. lia. }
    wp_pures.
    wp_pures.
    wp_bind (Slice go.string
      ((#(parent ++ [byte_dash] ++ suffix), #(word.add idx (W64 1)))%V,
       #(functions go.len [go.string])
         (#(parent ++ [byte_dash] ++ suffix))))%E.
    iApply (wp_wand _ _ _
      (λ v, ⌜ v = #(drop (sint.nat (word.add idx (W64 1)))
        (parent ++ [byte_dash] ++ suffix)) ⌝)%I with "[]").
    { iApply (wp_string_slice_to_end
        (parent ++ [byte_dash] ++ suffix) (word.add idx (W64 1))).
      - iPureIntro. split; [exact Hidx_next_nonneg|].
        rewrite Hidx_next app_length /=. lia.
      - iIntros "_". iPureIntro. done. }
    iIntros (suffix_val) "->".
    assert (drop (sint.nat (word.add idx (W64 1)))
      (parent ++ [byte_dash] ++ suffix) = suffix) as Hdrop_suffix.
    { rewrite Hidx_next.
      clear Hpod_name_len Hsuffix_no_dash Hidx_Z Hprefix_next_bound
        Hidx_next_Z Hidx_nat Hidx_next_nonneg Hidx_next
        Hpod_ordinal_suffix.
      induction parent as [|b parent IH]; simpl; [done|exact IH]. }
    rewrite Hdrop_suffix.
    wp_pures.
    wp_apply (wp_strconv_ParseInt_decimal_int32 with "[]").
    { by iEval (rewrite is_pkg_init_unfold /=). }
    iIntros (ordinal err) "%Hparse".
    wp_auto.
    destruct (parse_decimal_string suffix) as [expected_ordinal|]
      eqn:Hparse_suffix.
    + destruct (decide (expected_ordinal <= go_int32_max_nat)%nat) as
        [Hexpected_ordinal_bound|Hexpected_ordinal_overflow].
      * destruct Hparse as
          (Herr_nil & Hordinal_nat & Hordinal_Z & Hordinal_bounds).
        rewrite Herr_nil.
        wp_auto.
        wp_bind (Slice go.string
          (#(parent ++ [byte_dash] ++ suffix), #(W64 0), #idx)%V)%E.
        iApply (wp_wand _ _ _
          (λ v, ⌜ v = #(subslice (sint.nat (W64 0)) (sint.nat idx)
            (parent ++ [byte_dash] ++ suffix)) ⌝)%I with "[]").
        { iApply (wp_string_slice
            (parent ++ [byte_dash] ++ suffix) (W64 0) idx).
          - iPureIntro. split.
            + split; [word|]. rewrite Hidx_Z. lia.
            + rewrite Hidx_nat app_length /=. lia.
          - iIntros "_". iPureIntro. done. }
        iIntros (parent_val) "->".
        wp_auto.
        rewrite /subslice /= Hidx_nat drop_0 take_app_length.
        iApply "HΦ". iPureIntro.
        unfold parse_pod_ordinal.
        rewrite Hpod_ordinal_suffix /=.
        rewrite Hparse_suffix.
        case_decide; [exact Hordinal_Z|done].
      * destruct err as [err_i|].
        2: { exfalso. apply Hparse. reflexivity. }
        wp_pures. iApply "HΦ". iPureIntro.
        unfold parse_pod_ordinal.
        rewrite Hpod_ordinal_suffix /=.
        rewrite Hparse_suffix.
        case_decide; [done|word].
    + destruct err as [err_i|].
      2: { exfalso. apply Hparse. reflexivity. }
      wp_pures. iApply "HΦ". iPureIntro.
      unfold parse_pod_ordinal.
      rewrite Hpod_ordinal_suffix /= Hparse_suffix. word.
  - wp_if_destruct.
    2: { exfalso. word. }
    wp_pures. iApply "HΦ". iPureIntro.
    unfold parse_pod_ordinal.
    rewrite (pod_ordinal_suffix_no_dash pod_name Hno_dash). simpl. word.
Qed.

Lemma wp_ordinalOf_parse (pod_name : go_string) :
  {{{ ⌜ Z.of_nat (length pod_name) <= go_int_max ⌝ }}}
    @! statefulset.ordinalOf #pod_name
  {{{ (ordinal : w64), RET #ordinal;
      ⌜ match parse_pod_ordinal pod_name with
        | Some expected_ordinal =>
            if decide (expected_ordinal <= go_int32_max_nat)%nat
            then sint.Z ordinal = Z.of_nat expected_ordinal
            else sint.Z ordinal < 0
        | None => sint.Z ordinal < 0
        end ⌝
  }}}.
Proof.
  wp_start as "%Hpod_name_len". wp_auto.
  wp_apply (wp_parentNameAndOrdinal_parse pod_name with "[]").
  { iPureIntro. exact Hpod_name_len. }
  iIntros (parent ordinal) "%Hordinal". wp_auto.
  iApply "HΦ". done.
Qed.

Lemma wp_ordinalOf pod_name ordinal set_name :
  {{{ ⌜ Z.of_nat (length pod_name) <= go_int_max ⌝ ∗
      ⌜ (ordinal <= go_int32_max_nat)%nat ∧
        pod_name = desired_pod_name set_name ordinal ⌝
  }}}
    @! statefulset.ordinalOf #pod_name
  {{{ (ordinal_ret : w64), RET #ordinal_ret;
      ⌜ sint.Z ordinal_ret = Z.of_nat ordinal ⌝
  }}}.
Proof.
  wp_start as "(%Hname_len & %Hpre)".
  destruct Hpre as (Hordinal_bound & Hname).
  wp_auto.
  wp_apply (wp_parentNameAndOrdinal with "[]").
  { iPureIntro. exact Hname_len. }
  iIntros (parent ordinal_ret) "%Hparent".
  wp_auto.
  iApply "HΦ".
  iPureIntro.
  unfold pod_has_int32_member_name.
  pose proof (proj2 (Hparent set_name)
    (ex_intro _ ordinal (conj Hordinal_bound Hname))) as
    (_ & Hordinal_ret_nonnegative & Hname_ret).
  assert (sint.nat ordinal_ret = ordinal) as Hordinal_ret.
  { apply (desired_pod_name_inj set_name).
    rewrite -Hname_ret. exact Hname. }
  replace (sint.Z ordinal_ret) with (Z.of_nat (sint.nat ordinal_ret)) by word.
  by rewrite Hordinal_ret.
Qed.

Lemma wp_isMemberOf (set_name name : go_string) :
  {{{ ⌜ Z.of_nat (length name) <= go_int_max ⌝ }}}
    @! statefulset.isMemberOf #set_name #name
  {{{ (ret : bool), RET #ret;
      ⌜ ret = true ↔ pod_has_int32_member_name set_name name ⌝
  }}}.
Proof.
  wp_start as "%Hname_len".
  wp_auto.
  wp_apply (wp_parentNameAndOrdinal with "[]").
  { iPureIntro. exact Hname_len. }
  iIntros (parent ordinal) "%Hparent".
  wp_auto.
  destruct (decide (parent = set_name)) as [Hparent_eq|Hparent_ne].
  - subst parent.
    replace (bool_decide (set_name = set_name)) with true by
      (symmetry; apply bool_decide_true; done).
    wp_pures.
    wp_load.
    destruct (decide (0 <= sint.Z ordinal)) as
      [Hordinal_nonnegative|Hordinal_negative].
    + wp_auto.
      replace (bool_decide (sint.Z (W64 0) ≤ sint.Z ordinal)) with true by
        (symmetry; apply bool_decide_true; word).
      wp_pures.
      wp_load.
      wp_load.
      wp_pures.
      wp_load.
      wp_pures.
      wp_bind (@! statefulset.podName #set_name #ordinal)%E.
      wp_apply (wp_podName set_name ordinal with "[]").
      { iPureIntro. exact Hordinal_nonnegative. }
      iApply ("HΦ" $! (bool_decide
        (name = desired_pod_name set_name (sint.nat ordinal)))).
      iPureIntro.
      unfold pod_has_int32_member_name.
      split.
      * intros Hret.
        apply bool_decide_eq_true in Hret.
        apply (proj1 (Hparent set_name)).
        repeat split; done.
      * intros Hex.
        destruct (proj2 (Hparent set_name) Hex) as (_ & _ & Hname_eq).
        apply bool_decide_eq_true_2.
        done.
    + wp_auto.
      replace (bool_decide (sint.Z (W64 0) ≤ sint.Z ordinal)) with false by
        (symmetry; apply bool_decide_false; word).
      wp_pures.
      iApply "HΦ".
      iPureIntro.
      unfold pod_has_int32_member_name.
      split; [done|].
      intros Hex.
      destruct (proj2 (Hparent set_name) Hex) as (_ & Hordinal_nonnegative & _).
      lia.
  - replace (bool_decide (parent = set_name)) with false by
      (symmetry; apply bool_decide_false; done).
    wp_auto.
    iApply "HΦ".
    iPureIntro.
    unfold pod_has_int32_member_name.
    split; [done|].
    intros Hex.
    destruct (proj2 (Hparent set_name) Hex) as (Hparent_eq & _ & _).
    contradiction.
Qed.

Lemma wp_podInOrdinalRange set_l (set : StatefulSetV.t) pod_name ordinal set_name dq :
  {{{ "Hset" ∷ StatefulSetV.deepown_l set_l set dq ∗
      "%Hspec_valid" ∷ ⌜ StatefulSetSpecV.valid set.(StatefulSetV.Spec') ⌝ ∗
      "%Hname_len" ∷ ⌜ Z.of_nat (length pod_name) <= go_int_max ⌝ ∗
      "%Hpod_name" ∷ ⌜ (ordinal <= go_int32_max_nat)%nat ∧
        pod_name = desired_pod_name set_name ordinal ⌝
  }}}
    @! statefulset.podInOrdinalRange #set_l #pod_name
  {{{ (ret : bool), RET #ret;
      ⌜ ret = true ↔ (ordinal < statefulset_replicas set)%nat ⌝ ∗
      StatefulSetV.deepown_l set_l set dq
  }}}.
Proof.
  wp_start as "H". iNamed "H".
  wp_auto.
  wp_apply (wp_ordinalOf pod_name ordinal set_name with "[]").
  { iPureIntro. split; done. }
  iIntros (ordinal_ret) "%Hordinal_ret".
  wp_auto.
  replace (bool_decide (sint.Z (W64 0) ≤ sint.Z ordinal_ret)) with true.
  2:{ symmetry. apply bool_decide_true.
      rewrite Hordinal_ret. change (sint.Z (W64 0)) with 0. lia. }
  wp_pures.
  wp_load.
  wp_pures.
  wp_load.
  wp_pures.
  wp_apply (wp_endOrdinalOf with "[$Hset //]").
  iIntros (end_ordinal) "[%Hend_ordinal Hset]".
  wp_pures.
  iApply "HΦ".
  iFrame.
  iPureIntro.
  split.
  - intros Hret.
    apply bool_decide_eq_true in Hret.
    rewrite Hordinal_ret Hend_ordinal in Hret.
    lia.
  - intros Hlt.
    apply bool_decide_eq_true_2.
    rewrite Hordinal_ret Hend_ordinal.
    lia.
Qed.

End proof.
