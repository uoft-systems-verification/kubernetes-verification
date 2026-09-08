From New.proof Require Import prelude empty_ffi.
From New.proof Require Export sort.
From New.proof.map Require Import for_range.
From New.proof.kubernetes_types Require Export prelude.
From New.proof.k8s_io.api.core Require Export v1.
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

(** An abstract sortable element keeps a pod, its pointer, and its rank
    together, matching the coupled swaps performed by [ActivePodsWithRanks]. *)
Record active_pod_with_rank := {
  active_pod_ptr : loc;
  active_pod_value : PodV.t;
  active_pod_rank : w64;
}.

Fixpoint active_pods_with_ranks_entries
    (ptrs : list loc) (pods : list PodV.t) (ranks : list w64) : list active_pod_with_rank :=
  match ptrs, pods, ranks with
  | ptr :: ptrs, pod :: pods, rank :: ranks =>
      {| active_pod_ptr := ptr; active_pod_value := pod; active_pod_rank := rank |} ::
        active_pods_with_ranks_entries ptrs pods ranks
  | _, _, _ => []
  end.

Lemma active_pods_with_ranks_entries_ptrs ptrs pods ranks :
  length ptrs = length pods → length ptrs = length ranks →
  active_pod_ptr <$> active_pods_with_ranks_entries ptrs pods ranks = ptrs.
Proof.
  revert pods ranks. induction ptrs as [|ptr ptrs IH]; intros [|pod pods] [|rank ranks];
    simpl; intros; try congruence.
  f_equal. apply IH; lia.
Qed.

Lemma active_pods_with_ranks_entries_pods ptrs pods ranks :
  length ptrs = length pods → length ptrs = length ranks →
  active_pod_value <$> active_pods_with_ranks_entries ptrs pods ranks = pods.
Proof.
  revert pods ranks. induction ptrs as [|ptr ptrs IH]; intros [|pod pods] [|rank ranks];
    simpl; intros; try congruence.
  f_equal. apply IH; lia.
Qed.

Lemma active_pods_with_ranks_entries_ranks ptrs pods ranks :
  length ptrs = length pods → length ptrs = length ranks →
  active_pod_rank <$> active_pods_with_ranks_entries ptrs pods ranks = ranks.
Proof.
  revert pods ranks. induction ptrs as [|ptr ptrs IH]; intros [|pod pods] [|rank ranks];
    simpl; intros; try congruence.
  f_equal. apply IH; lia.
Qed.

Definition active_pods_with_ranks_contents dq
    (ranked : controller.ActivePodsWithRanks.t) (entries : list active_pod_with_rank) : iProp Σ :=
  ranked.(controller.ActivePodsWithRanks.Pods') ↦* (active_pod_ptr <$> entries) ∗
  ranked.(controller.ActivePodsWithRanks.Rank') ↦* (active_pod_rank <$> entries) ∗
  ([∗ list] ptr;pod ∈ (active_pod_ptr <$> entries);(active_pod_value <$> entries),
    PodV.deepown_l ptr pod dq).

(** The model API omits these Kubernetes method bodies, so their method-level
    contracts are the controller-specific trusted boundary. *)
Lemma wp_active_pods_with_ranks_len dq ranked entries :
  {{{ active_pods_with_ranks_contents dq ranked entries }}}
    ranked @! controller.ActivePodsWithRanks @! "Len" #()
  {{{ (n : w64), RET #n; active_pods_with_ranks_contents dq ranked entries ∗
      ⌜ sint.nat n = length entries ∧ 0 ≤ sint.Z n ⌝
  }}}.
Proof. Admitted.

Lemma wp_active_pods_with_ranks_less dq ranked entries (i j : w64) :
  0 ≤ sint.Z i < length entries → 0 ≤ sint.Z j < length entries →
  {{{ active_pods_with_ranks_contents dq ranked entries }}}
    ranked @! controller.ActivePodsWithRanks @! "Less" #i #j
  {{{ (b : bool), RET #b; active_pods_with_ranks_contents dq ranked entries }}}.
Proof. Admitted.

Lemma wp_active_pods_with_ranks_swap dq ranked entries (i j : w64) :
  0 ≤ sint.Z i < length entries → 0 ≤ sint.Z j < length entries →
  {{{ active_pods_with_ranks_contents dq ranked entries }}}
    ranked @! controller.ActivePodsWithRanks @! "Swap" #i #j
  {{{ RET #(); active_pods_with_ranks_contents dq ranked
      (list_swap entries (sint.nat i) (sint.nat j))
  }}}.
Proof. Admitted.

#[global] Instance active_pods_with_ranks_sort_interface dq :
  SortInterfaceSpec controller.ActivePodsWithRanks
    (active_pods_with_ranks_contents dq).
Proof.
  constructor.
  - apply wp_active_pods_with_ranks_len.
  - apply wp_active_pods_with_ranks_less.
  - apply wp_active_pods_with_ranks_swap.
Qed.

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

Lemma generated_pod_parent_ref template parent_name ref kind uid :
  OwnerReferenceV.refers_to_controller ref kind parent_name uid →
  obj_parent_ref_is (KObjectV.Pod (generated_pod template parent_name (Some [ref])))
    kind parent_name uid.
Proof.
  intros (Hkind & Hname & Huid & _ & Hcontroller).
  rewrite /obj_parent_ref_is /meta_parent_ref_is /meta_parent_ref
    /generated_pod /generated_pod_meta /=.
  rewrite Hcontroller /= Hkind Hname Huid. done.
Qed.

Lemma generated_pod_valid_create template parent_name ref namespace :
  PodTemplateSpecV.valid template →
  valid_dns1123_subdomain parent_name →
  length parent_name < 58 →
  valid_finalizers template.(PodTemplateSpecV.ObjectMeta').(ObjectMetaV.Finalizers') →
  OwnerReferenceV.valid ref →
  namespace ≠ ""%go →
  valid_namespace namespace →
  KObjectV.valid_create "Pod"%go namespace
    (KObjectV.Pod (generated_pod template parent_name (Some [ref]))).
Proof.
  intros (Hlabels & Hannotations & Hspec) Hname Hlen Hfinalizers Href
    Hnamespace_nonempty Hnamespace_valid.
  rewrite /KObjectV.valid_create /= /PodV.valid_create
    /generated_pod /generated_pod_meta /=.
  split_and!.
  - done.
  - exact Hnamespace_nonempty.
  - exact Hnamespace_valid.
  - apply zero_typemeta_valid_create.
  - rewrite /ObjectMetaV.valid_create /=.
    split_and!.
    + apply valid_generate_name_of_valid_prefix.
      exists parent_name. split_and!; [done| |].
      * intros ->. inversion Hname as [Hsyntax _]. inversion Hsyntax.
      * unfold valid_name, PodV.kind. right. split; [left; done|exact Hname].
    + rewrite length_app /=. lia.
    + left. done.
    + destruct template.(PodTemplateSpecV.ObjectMeta').(ObjectMetaV.Labels') as [labels|];
        simpl in *; [exact Hlabels|apply map_Forall_empty].
    + destruct template.(PodTemplateSpecV.ObjectMeta').(ObjectMetaV.Annotations') as [annotations|];
        simpl in *; [destruct Hannotations as [Hannotations _]; exact Hannotations|apply map_Forall_empty].
    + destruct template.(PodTemplateSpecV.ObjectMeta').(ObjectMetaV.Annotations') as [annotations|];
        simpl in *; [destruct Hannotations as [_ Hannotations]; exact Hannotations|done].
    + intros i1 i2 or1 or2 H1 H2 _ _.
      pose proof (lookup_lt_Some _ _ _ H1) as Hi1.
      pose proof (lookup_lt_Some _ _ _ H2) as Hi2. simpl in Hi1, Hi2. lia.
    + intros owner Howner. rewrite list_elem_of_singleton in Howner. subst owner. exact Href.
    + destruct template.(PodTemplateSpecV.ObjectMeta').(ObjectMetaV.Finalizers') as [finalizers|];
        simpl in *; [exact Hfinalizers|constructor].
    + apply valid_managed_fields_none.
  - exact Hspec.
Qed.

(** Trusted because [PodStatusV] deliberately keeps the status fields opaque,
    while the imported Kubernetes implementation reads [status.phase]. *)
Lemma wp_IsPodActive (pod_l : loc) (pod : PodV.t) (dq : dfrac) :
  {{{ is_pkg_init controller ∗
      "Hpod" ∷ PodV.deepown_l pod_l pod dq
  }}}
    @! controller.IsPodActive #pod_l
  {{{ (active : bool), RET #active; PodV.deepown_l pod_l pod dq }}}.
Proof. Admitted.

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
Proof.
  wp_start as "H". iNamed "H".
  iDestruct "Htemplate" as (template_c) "[Htemplate_l Htemplate]".
  iNamedPrefix "Htemplate" "Htemplate_".
  iNamedPrefix "Htemplate_Hdeepown_objectmeta" "Hmeta_".
  iDestruct (struct_fields_split with "Htemplate_l") as
    "[Htemplate_fields %Htemplate_nonnull]".
  iNamedPrefix "Htemplate_fields" "Htemplate_field_".
  iDestruct (struct_fields_split with "Htemplate_field_ObjectMeta") as
    "[Hmeta_fields %Hmeta_nonnull]".
  iNamedPrefix "Hmeta_fields" "Hmeta_field_".
  wp_auto.
  rewrite go.make1_underlying.
  rewrite (go.is_underlying (t := labels.Set')
    (tunder := labels.Set'ⁱᵐᵖˡ)).
  wp_apply wp_map_make1 as (labels_l) "Hlabels".
  wp_pures.
  iCombineNamed "Hmeta_field_*" as "Hmeta_fields".
  iAssert (typed_pointsto_def
      (template_l.[v1.PodTemplateSpec.t, "ObjectMeta"])
      template_c.(v1.PodTemplateSpec.ObjectMeta') dq)
    with "[Hmeta_fields]" as "Hobjectmeta".
  { iNamed "Hmeta_fields". simpl. rewrite /named. iFrame. }
  iDestruct (struct_fields_combine (V:=v1.ObjectMeta.t)
      (template_l.[v1.PodTemplateSpec.t, "ObjectMeta"])
      template_c.(v1.PodTemplateSpec.ObjectMeta') dq Hmeta_nonnull
      with "Hobjectmeta") as "Hobjectmeta".
  iCombineNamed "Htemplate_field_*" as "Htemplate_fields".
  iAssert (typed_pointsto_def template_l template_c dq)
    with "[Htemplate_fields Hobjectmeta]" as "Htemplate_l".
  { iNamed "Htemplate_fields". simpl. rewrite /named. iFrame. }
  iDestruct (struct_fields_combine (V:=v1.PodTemplateSpec.t)
      template_l template_c dq Htemplate_nonnull with "Htemplate_l")
    as "Htemplate_l".
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
      wp_auto.
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
    wp_auto.
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
      iFrame. iFrame "%". }
    iApply ("HΦ" $! labels_l). iFrame "Hlabels".
    iExists template_c. iFrame "Htemplate_l".
    rewrite /PodTemplateSpecV.deepown. iFrame.
  - assert (template_c.(v1.PodTemplateSpec.ObjectMeta').(v1.ObjectMeta.Labels') =
        map.nil) as Hlabels_nil.
    { apply Hmeta_Hdeepown_labels_none. done. }
    rewrite Hlabels_nil.
    wp_apply (wp_map_for_range_nil go.string go.string).
    wp_pures.
    iCombineNamed "Hmeta_*" as "Hobjectmeta".
    iAssert (ObjectMetaV.deepown
        template_c.(v1.PodTemplateSpec.ObjectMeta')
        template.(PodTemplateSpecV.ObjectMeta') dq)
      with "[Hobjectmeta]" as "Hobjectmeta".
    { rewrite /ObjectMetaV.deepown Hlabels_opt /=. iNamed "Hobjectmeta".
      iFrame. iFrame "%". }
    iApply ("HΦ" $! labels_l).
    iFrame "Hlabels".
    iExists template_c. iFrame "Htemplate_l".
    rewrite /PodTemplateSpecV.deepown. iFrame.
Qed.

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
Proof.
  wp_start as "Htemplate".
  iDestruct "Htemplate" as (template_c) "[Htemplate_l Htemplate]".
  iNamedPrefix "Htemplate" "Htemplate_".
  iNamedPrefix "Htemplate_Hdeepown_objectmeta" "Hmeta_".
  iDestruct (struct_fields_split with "Htemplate_l") as
    "[Htemplate_fields %Htemplate_nonnull]".
  iNamedPrefix "Htemplate_fields" "Htemplate_field_".
  iDestruct (struct_fields_split with "Htemplate_field_ObjectMeta") as
    "[Hmeta_fields %Hmeta_nonnull]".
  iNamedPrefix "Hmeta_fields" "Hmeta_field_".
  iAssert (∃ finalizers,
      template_c.(v1.PodTemplateSpec.ObjectMeta').(v1.ObjectMeta.Finalizers')
        ↦*{dq} finalizers ∗
      ⌜finalizers = default []
        template.(PodTemplateSpecV.ObjectMeta').(ObjectMetaV.Finalizers')⌝)%I
    with "[Hmeta_Hdeepown_finalizers_some]" as
      (finalizers) "[Hfinalizers_src %Hfinalizers]".
  { destruct template.(PodTemplateSpecV.ObjectMeta').(ObjectMetaV.Finalizers')
      as [finalizers|] eqn:Hfinalizers_opt; simpl.
    - iDestruct "Hmeta_Hdeepown_finalizers_some" as (finalizers_c)
        "[Hfinalizers_src %Hfinalizers_c]".
      subst finalizers_c. iExists finalizers. iSplitL; first iFrame. done.
    - assert (template_c.(v1.PodTemplateSpec.ObjectMeta').(v1.ObjectMeta.Finalizers') =
          slice.nil) as Hfinalizers_nil.
      { apply Hmeta_Hdeepown_finalizers_none. done. }
      rewrite Hfinalizers_nil. iExists []. iSplit; last done.
      iApply own_slice_nil. }
  subst finalizers.
  iDestruct (own_slice_len with "Hfinalizers_src") as
    %[Hfinalizers_len Hfinalizers_len_nonnegative].
  assert (Hmake3 : ∀ stk E (len cap : u64),
    0 ≤ sint.Z len ≤ sint.Z cap →
    {{{ True }}}
      #(functions go.make3 [go.SliceType go.string]) #len #cap @ stk; E
    {{{ sl, RET #sl;
        sl ↦* (replicate (sint.nat len) (zero_val go_string)) ∗
        own_slice_cap go_string sl (DfracOwn 1) ∗
        ⌜sl ≠ slice.nil⌝
    }}}).
  { intros stk E len cap Hbounds. wp_start.
    wp_if_destruct; first (exfalso; word).
    wp_if_destruct; first (exfalso; word).
    case_bool_decide; wp_auto.
    - subst cap. assert (len = W64 0) by word. subst len.
      wp_apply wp_ArbitraryInt. iIntros (x) "_".
      wp_auto. iApply "HΦ".
      iDestruct (own_slice_empty with "[]") as "$"; simpl.
      { word. }
      { word. }
      { by iApply array_empty. }
      iDestruct own_slice_cap_empty as "$"; simpl.
      { word. }
      { word. }
      iPureIntro. intros Hnil.
      apply (f_equal slice.ptr) in Hnil.
      apply (f_equal addr_id) in Hnil.
      rewrite /loc_add addr_id_of_plus /addr_id /null /= in Hnil. lia.
    - iApply "HΦ".
      rewrite own_slice_unseal /own_slice_def /=.
      iDestruct (array_split len with "p") as "[Hsl Hcap]"; first word.
      simpl. rewrite take_replicate.
      iSplitL "Hsl".
      { iRight. iSplitL; last word.
        replace (_ `min` _)%nat with (sint.nat len) by word. iFrame. }
      rewrite own_slice_cap_unseal /own_slice_cap_def /=.
      iSplitL "Hcap".
      { iRight. iSplitR; first word. iFrame. }
      iPureIntro. intros Hnil.
      apply (f_equal slice.cap) in Hnil. simpl in Hnil. word. }
  assert (Hmake2 : ∀ stk E (len : u64),
    {{{ ⌜0 ≤ sint.Z len⌝ }}}
      #(functions go.make2 [go.SliceType go.string]) #len @ stk; E
    {{{ sl, RET #sl;
        sl ↦* (replicate (sint.nat len) (zero_val go_string)) ∗
        own_slice_cap go_string sl (DfracOwn 1) ∗
        ⌜sl ≠ slice.nil⌝
    }}}).
  { intros stk E len. wp_start as "%Hlen".
    wp_apply Hmake3; first word.
    iIntros (sl) "Hsl". iApply "HΦ". iFrame. }
  wp_auto.
  wp_apply Hmake2; first word.
  iIntros (finalizers_sl)
    "(Hfinalizers & Hfinalizers_cap & %Hfinalizers_non_nil)".
  iEval (rewrite -Hfinalizers_len) in "Hfinalizers".
  wp_auto.
  wp_apply (wp_slice_copy with "[$Hfinalizers $Hfinalizers_src]") as (n)
    "(%Hcopied & Hfinalizers & Hfinalizers_src)".
  iAssert (finalizers_sl ↦* default []
      template.(PodTemplateSpecV.ObjectMeta').(ObjectMetaV.Finalizers'))
    with "[Hfinalizers]" as "Hfinalizers".
  { iEval (rewrite length_replicate) in "Hfinalizers".
    iEval (rewrite take_ge; last done) in "Hfinalizers".
    assert (length (replicate
        (length (default [] (ObjectMetaV.Finalizers'
          (PodTemplateSpecV.ObjectMeta' template)))) (zero_val go_string)) ≤
      length (default [] (ObjectMetaV.Finalizers'
        (PodTemplateSpecV.ObjectMeta' template))))%nat as Hdrop.
    { rewrite length_replicate. done. }
    iEval (rewrite (drop_ge _ _ Hdrop)) in "Hfinalizers".
    iEval (rewrite app_nil_r) in "Hfinalizers".
    iExact "Hfinalizers". }
  wp_pures.
  iCombineNamed "Hmeta_field_*" as "Hmeta_fields".
  iAssert (typed_pointsto_def
      (template_l.[v1.PodTemplateSpec.t, "ObjectMeta"])
      template_c.(v1.PodTemplateSpec.ObjectMeta') dq)
    with "[Hmeta_fields]" as "Hobjectmeta_l".
  { iNamed "Hmeta_fields". simpl. rewrite /named. iFrame. }
  iDestruct (struct_fields_combine (V:=v1.ObjectMeta.t)
      (template_l.[v1.PodTemplateSpec.t, "ObjectMeta"])
      template_c.(v1.PodTemplateSpec.ObjectMeta') dq Hmeta_nonnull
      with "Hobjectmeta_l") as "Hobjectmeta_l".
  iCombineNamed "Htemplate_field_*" as "Htemplate_fields".
  iAssert (typed_pointsto_def template_l template_c dq)
    with "[Htemplate_fields Hobjectmeta_l]" as "Htemplate_l".
  { iNamed "Htemplate_fields". simpl. rewrite /named. iFrame. }
  iDestruct (struct_fields_combine (V:=v1.PodTemplateSpec.t)
      template_l template_c dq Htemplate_nonnull with "Htemplate_l")
    as "Htemplate_l".
  iAssert ((match template.(PodTemplateSpecV.ObjectMeta').(ObjectMetaV.Finalizers') with
    | Some finalizers' => ∃ finalizers_c,
        template_c.(v1.PodTemplateSpec.ObjectMeta').(v1.ObjectMeta.Finalizers')
          ↦*{dq} finalizers_c ∗ ⌜finalizers_c = finalizers'⌝
    | None => True
    end)%I) with "[Hfinalizers_src]" as "Hmeta_Hdeepown_finalizers_some".
  { destruct template.(PodTemplateSpecV.ObjectMeta').(ObjectMetaV.Finalizers')
      as [finalizers|] eqn:Hfinalizers_opt; simpl.
    - iExists finalizers. iSplitL; first iFrame. done.
    - iClear "Hfinalizers_src". done. }
  iCombineNamed "Hmeta_*" as "Hobjectmeta".
  iAssert (ObjectMetaV.deepown
      template_c.(v1.PodTemplateSpec.ObjectMeta')
      template.(PodTemplateSpecV.ObjectMeta') dq)
    with "[Hobjectmeta]" as "Hobjectmeta".
  { rewrite /ObjectMetaV.deepown.
    iNamed "Hobjectmeta". iFrame. iFrame "%". }
  iApply ("HΦ" $! finalizers_sl).
  iFrame "Hfinalizers".
  iSplitL "Htemplate_l Hobjectmeta Htemplate_Hdeepown_spec".
  { iExists template_c. iFrame "Htemplate_l".
    rewrite /PodTemplateSpecV.deepown. iFrame. }
  done.
Qed.

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
Proof.
  wp_start as "Htemplate".
  iDestruct "Htemplate" as (template_c) "[Htemplate_l Htemplate]".
  iNamedPrefix "Htemplate" "Htemplate_".
  iNamedPrefix "Htemplate_Hdeepown_objectmeta" "Hmeta_".
  iDestruct (struct_fields_split with "Htemplate_l") as
    "[Htemplate_fields %Htemplate_nonnull]".
  iNamedPrefix "Htemplate_fields" "Htemplate_field_".
  iDestruct (struct_fields_split with "Htemplate_field_ObjectMeta") as
    "[Hmeta_fields %Hmeta_nonnull]".
  iNamedPrefix "Hmeta_fields" "Hmeta_field_".
  wp_auto.
  rewrite go.make1_underlying.
  rewrite (go.is_underlying (t := labels.Set')
    (tunder := labels.Set'ⁱᵐᵖˡ)).
  wp_apply wp_map_make1 as (annotations_l) "Hannotations".
  wp_pures.
  iCombineNamed "Hmeta_field_*" as "Hmeta_fields".
  iAssert (typed_pointsto_def
      (template_l.[v1.PodTemplateSpec.t, "ObjectMeta"])
      template_c.(v1.PodTemplateSpec.ObjectMeta') dq)
    with "[Hmeta_fields]" as "Hobjectmeta".
  { iNamed "Hmeta_fields". simpl. rewrite /named. iFrame. }
  iDestruct (struct_fields_combine (V:=v1.ObjectMeta.t)
      (template_l.[v1.PodTemplateSpec.t, "ObjectMeta"])
      template_c.(v1.PodTemplateSpec.ObjectMeta') dq Hmeta_nonnull
      with "Hobjectmeta") as "Hobjectmeta".
  iCombineNamed "Htemplate_field_*" as "Htemplate_fields".
  iAssert (typed_pointsto_def template_l template_c dq)
    with "[Htemplate_fields Hobjectmeta]" as "Htemplate_l".
  { iNamed "Htemplate_fields". simpl. rewrite /named. iFrame. }
  iDestruct (struct_fields_combine (V:=v1.PodTemplateSpec.t)
      template_l template_c dq Htemplate_nonnull with "Htemplate_l")
    as "Htemplate_l".
  destruct template.(PodTemplateSpecV.ObjectMeta').(ObjectMetaV.Annotations')
    as [annotations|] eqn:Hannotations_opt.
  - iDestruct "Hmeta_Hdeepown_annotations_some" as (annotations_c)
      "[Hannotations_src %Hannotations_c]".
    subst annotations_c.
    wp_apply (wp_map_for_range_return_func (key_type:=go.string)
      (λ (keys : list go_string) i,
        ∃ (last_value last_key : go_string),
          "v" ∷ v_ptr ↦ last_value ∗
          "k" ∷ k_ptr ↦ last_key ∗
          "desiredAnnotations" ∷ desiredAnnotations_ptr ↦ annotations_l ∗
          "Hannotations" ∷ annotations_l ↦$ map_prefix keys i annotations)%I
      with "Hannotations_src").
    { done. }
    iIntros (keys) "%Hkeys".
    iSplitL "v k desiredAnnotations Hannotations".
    { iExists ""%go, ""%go. iFrame.
      rewrite map_prefix_empty. iFrame. }
    iSplitL "".
    { iModIntro. iIntros (i key value) "%Hiter Hloop".
      destruct Hkeys as [Hkeys_dom [Hkeys_len Hkeys_nodup]].
      destruct Hiter as [Hi_bounds [Hkey_lookup Hvalue_lookup]].
      destruct Hi_bounds as [Hi_nonneg Hi_upper].
      iDestruct "Hloop" as (last_value last_key)
        "(v & k & desiredAnnotations & Hannotations)".
      wp_pures. simpl subst'. wp_auto.
      wp_apply (wp_map_insert (K:=go_string) (V:=go_string)
        go.string annotations_l (map_prefix keys i annotations) key value
        with "Hannotations") as "Hannotations".
      iRight. iSplit; [done|].
      iExists value, key. iFrame.
      rewrite -map_prefix_insert; done. }
    iIntros "Hannotations_src Hloop".
    iDestruct "Hloop" as (last_value last_key)
      "(v & k & desiredAnnotations & Hannotations)".
    destruct Hkeys as [Hkeys_dom [Hkeys_len Hkeys_nodup]].
    rewrite (map_prefix_all keys annotations Hkeys_dom Hkeys_len).
    wp_auto.
    iAssert ((match template.(PodTemplateSpecV.ObjectMeta').(ObjectMetaV.Annotations') with
      | Some annotations' => ∃ annotations_c,
          template_c.(v1.PodTemplateSpec.ObjectMeta').(v1.ObjectMeta.Annotations')
            ↦${dq} annotations_c ∗ ⌜annotations_c = annotations'⌝
      | None => True
      end)%I) with "[Hannotations_src]" as
        "Hmeta_Hdeepown_annotations_some".
    { rewrite Hannotations_opt. iExists annotations.
      iSplitL "Hannotations_src"; [iExact "Hannotations_src"|done]. }
    iCombineNamed "Hmeta_*" as "Hobjectmeta".
    iAssert (ObjectMetaV.deepown
        template_c.(v1.PodTemplateSpec.ObjectMeta')
        template.(PodTemplateSpecV.ObjectMeta') dq)
      with "[Hobjectmeta]" as "Hobjectmeta".
    { rewrite /ObjectMetaV.deepown Hannotations_opt /=.
      iNamed "Hobjectmeta". iFrame. iFrame "%". }
    iApply ("HΦ" $! annotations_l). iFrame "Hannotations".
    iExists template_c. iFrame "Htemplate_l".
    rewrite /PodTemplateSpecV.deepown. iFrame.
  - assert (template_c.(v1.PodTemplateSpec.ObjectMeta').(v1.ObjectMeta.Annotations') =
        map.nil) as Hannotations_nil.
    { apply Hmeta_Hdeepown_annotations_none. done. }
    rewrite Hannotations_nil.
    wp_apply (wp_map_for_range_nil go.string go.string).
    wp_pures.
    iCombineNamed "Hmeta_*" as "Hobjectmeta".
    iAssert (ObjectMetaV.deepown
        template_c.(v1.PodTemplateSpec.ObjectMeta')
        template.(PodTemplateSpecV.ObjectMeta') dq)
      with "[Hobjectmeta]" as "Hobjectmeta".
    { rewrite /ObjectMetaV.deepown Hannotations_opt /=.
      iNamed "Hobjectmeta". iFrame. iFrame "%". }
    iApply ("HΦ" $! annotations_l). iFrame "Hannotations".
    iExists template_c. iFrame "Htemplate_l".
    rewrite /PodTemplateSpecV.deepown. iFrame.
Qed.

Lemma wp_getPodsPrefix controller_name :
  {{{ is_pkg_init controller ∗
      ⌜ valid_dns1123_subdomain controller_name ⌝
  }}}
    @! controller.getPodsPrefix #controller_name
  {{{ RET #(controller_name ++ "-"%go); True }}}.
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
  wp_start as "HownerReference".
  iDestruct (typed_pointsto_not_null with "HownerReference") as %HownerReference_nonnull.
  wp_auto.
  rewrite -> bool_decide_false by exact HownerReference_nonnull.
  wp_auto.
  iApply "HΦ". iPureIntro. rewrite !app_assoc. done.
Qed.

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
            (KObjectV.objectmeta parent).(ObjectMetaV.Name') ⌝
  }}}
    @! controller.GetPodFromTemplate #template_l #(interface.ok obj) #controller_ref_l
  {{{ pod_l, RET (#pod_l, #interface.nil);
      "Hpod" ∷ PodV.deepown_l pod_l
        (generated_pod template
          (KObjectV.objectmeta parent).(ObjectMetaV.Name')
          (match controller_ref with
          | Some ref => Some [ref]
          | None => None
          end)) 1 ∗
      "Htemplate" ∷
        PodTemplateSpecV.deepown_l template_l template template_dq ∗
      "Hparent_meta" ∷ ObjectMetaV.deepown_l
        (KObjectV.objectmeta_ptr parent_l parent)
        (KObjectV.objectmeta parent) parent_dq
  }}}.
Proof.
  wp_start as "H". iNamed "H".
  iDestruct "Hinit" as "#Hinit".
  iAssert (is_pkg_init code.k8s_io.api.core.v1.pkg_id.v1)
    as "#Hcore_v1".
  { iPkgInit. }
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
  wp_apply (wp_GetName_deepown_kobject obj parent_l parent with "[$Hparent_meta]"). 1: done.
  iIntros "Hparent_meta".
  wp_auto.
  wp_apply (wp_getPodsPrefix with "[]").
  { iFrame "#". done. }
  wp_alloc pod_l as "Hpod_l".
  destruct controller_ref as [ref|].
  - iDestruct "Hcontroller_ref" as (ref_c) "[Href_l Href]".
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
    iDestruct "Htemplate_spec" as
      (template_spec_phy) "[Htemplate_spec_ptr Htemplate_spec]".
    wp_apply (wp_PodSpec__DeepCopy
      with "[$Hcore_v1 $Htemplate_spec_ptr $Htemplate_spec]").
    iIntros (spec_copy_l)
      "(Hspec_copy & Htemplate_spec_ptr & Htemplate_spec)".
    iDestruct "Hspec_copy" as (spec_c) "[Hspec_copy_l Hspec_copy]".
    wp_auto.
    iAssert (PodSpecV.deepown_l
        (PodTemplateSpecV.spec_ptr template_l)
        template.(PodTemplateSpecV.Spec') template_dq)
      with "[Htemplate_spec_ptr Htemplate_spec]" as "Htemplate_spec".
    { iExists template_spec_phy. iFrame. }
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
    iApply ("HΦ" $! pod_l).
    iFrame "Hpod Htemplate Hparent_meta".
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
    iDestruct "Htemplate_spec" as
      (template_spec_phy) "[Htemplate_spec_ptr Htemplate_spec]".
    wp_apply (wp_PodSpec__DeepCopy
      with "[$Hcore_v1 $Htemplate_spec_ptr $Htemplate_spec]").
    iIntros (spec_copy_l)
      "(Hspec_copy & Htemplate_spec_ptr & Htemplate_spec)".
    iDestruct "Hspec_copy" as (spec_c) "[Hspec_copy_l Hspec_copy]".
    wp_auto.
    iAssert (PodSpecV.deepown_l
        (PodTemplateSpecV.spec_ptr template_l)
        template.(PodTemplateSpecV.Spec') template_dq)
      with "[Htemplate_spec_ptr Htemplate_spec]" as "Htemplate_spec".
    { iExists template_spec_phy. iFrame. }
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
    iApply ("HΦ" $! pod_l).
    iFrame "Hpod Htemplate Hparent_meta".
Qed.

End proof.
