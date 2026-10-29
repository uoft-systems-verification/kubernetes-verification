From New.proof.controllers Require Import client_tactics.
From New.proof Require Import wp_keep.
From New.proof.controllers.statefulset Require Export pod_predicates.
From New.proof.controllers.statefulset Require Export ordinal.
From New.proof.k8s_io.api.core Require Export v1.
From New.proof.kubernetes_model.tx Require Export update_release.

From New.proof.controllers.statefulset Require Export release_pod.

Local Transparent ObjectMetaV.deepown ObjectMetaView.ObjectMetaV.deepown.

(* Collect transient allocations from imports before checking large program proofs. *)
Optimize Heap.

Section proof.
Context `{hG: !heapGS Σ} `{!ffi_semantics _ _}.
Context {sem : go.Semantics}
  {package_sem : code.controllers.statefulset.statefulset.Assumptions}.
Context {model_sem : apimodel.Assumptions}.
Context {client_ctx : code.context.context.Context.t} {kube_client : loc}.
Collection W := sem + package_sem + model_sem.
#[local] Instance base_common_sem : common.Assumptions | 100 :=
  code.controllers.statefulset.statefulset.import_common_Assumption.
#[local] Instance controller_sem : controller.Assumptions :=
  code.controllers.statefulset.statefulset.import_controller_Assumption.
#[local] Instance runtime_sem :
    code.k8s_io.apimachinery.pkg.runtime.runtime.Assumptions :=
  controller.import_runtime_Assumption.
#[local] Instance runtime_object_underlying_eq :
    runtime.Object ≤u runtime.Objectⁱᵐᵖˡ.
Proof using package_sem model_sem. apply _. Qed.
#[local] Instance meta_object_underlying_eq :
    meta_v1.Object ≤u meta_v1.Objectⁱᵐᵖˡ.
Proof using package_sem model_sem. apply _. Qed.
#[local] Instance base_apimodel_sem : apimodel.Assumptions | 100 :=
  model_sem.
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
Proof using package_sem model_sem.
  constructor; try exact object_core_v1_sem; try apply _.
Defined.
#[local] Instance common_sem : common.Assumptions | 0.
Proof using package_sem model_sem.
  constructor; try exact apimodel_sem; try apply _.
Defined.
Context `{!kubernetesModelG Σ}.
Context `{!KObjectV.ObjectInterfaceAssumptions}.
Local Set Default Proof Using "All - client_ctx - kube_client".

Definition pods_with_bad_names
    (set : StatefulSetV.t) (pods : list PodV.t) : list PodV.t :=
  filter
    (λ pod,
      ¬ pod_has_int32_member_name
        set.(StatefulSetV.ObjectMeta').(ObjectMetaV.Name')
        pod.(PodV.ObjectMeta').(ObjectMetaV.Name'))
    pods.

Lemma bad_pod_key_not_in_prefix
    (Bad : PodV.t → Prop) `{∀ pod, Decision (Bad pod)}
    pods pod i :
  NoDup (PodV.key <$> filter Bad pods) →
  pods !! i = Some pod →
  Bad pod →
  PodV.key pod ∉ PodV.key <$> filter Bad (take i pods).
Proof.
  intros Hnodup Hlookup Hbad Hin.
  rewrite -(take_drop_middle pods i pod Hlookup) in Hnodup.
  rewrite list.filter_app
    (filter_cons_True Bad pod (drop (S i) pods) Hbad)
    fmap_app /= in Hnodup.
  apply list.NoDup_app in Hnodup as (_ & Hdisjoint & _).
  apply (Hdisjoint (PodV.key pod) Hin).
  by left.
Qed.

(* [releasePodsWithBadNames] leaves the input Go objects unchanged because
   [releasePod] updates a deep copy. The update consumes the ghost fragments
   for each released Pod. *)
Lemma wp_releasePodsWithBadNames γ model_l set_l pods_sl
    (set : StatefulSetV.t) (ptrs : list loc)
    (pods bad_name_pods : list PodV.t)
    (children : gset KKey.t) dq_set dq_pods pod_orphans :
  {{{ "#Hpkg" ∷
        is_pkg_init code.controllers.statefulset.pkg_id.statefulset ∗
      "#Hisk" ∷ is_kubernetes γ model_l ∗
      "#Hglobal_l" ∷
        (global_addr apimodel.ModelState) ↦□ model_l ∗
      "#Hmodel_init" ∷ is_pkg_init apimodel ∗
      "Hset" ∷ StatefulSetV.deepown_l set_l set dq_set ∗
      "Hpods_sl" ∷ pods_sl ↦* ptrs ∗
      "Hpods" ∷
        ([∗ list] ptr;pod ∈ ptrs;pods,
          PodV.deepown_l ptr pod dq_pods) ∗
      "%Hbad_name_pods" ∷
        ⌜ bad_name_pods = pods_with_bad_names set pods ⌝ ∗
      "Hown_meta" ∷
        ([∗ list] pod ∈ bad_name_pods,
          own_meta_frag γ
            (PodV.key pod)
            pod.(PodV.ObjectMeta').(ObjectMetaV.UID') 1
            pod.(PodV.ObjectMeta')) ∗
      "Hown_spec" ∷
        ([∗ list] pod ∈ bad_name_pods,
          own_spec_frag γ
            (PodV.key pod)
            pod.(PodV.ObjectMeta').(ObjectMetaV.UID') 1
            (ObjectSpecV.PodSpec pod.(PodV.Spec'))) ∗
      "Hown_children" ∷ own_children_frag γ
        (StatefulSetV.key set)
        set.(StatefulSetV.ObjectMeta').(ObjectMetaV.UID') 1
        children ∗
      "%Hname_lengths" ∷
        ⌜ Forall
          (λ pod,
            Z.of_nat
              (length
                pod.(PodV.ObjectMeta').(ObjectMetaV.Name')) ≤
            go_int_max)
          pods ⌝ ∗
      "%Hreleaseable" ∷
        ⌜ Forall
          (λ pod,
            PodV.valid pod ∧
            meta_parent_ref pod.(PodV.ObjectMeta') =
              Some
                (StatefulSetV.key set,
                 set.(StatefulSetV.ObjectMeta').(
                   ObjectMetaV.UID')) ∧
            PodV.key pod ∈ children)
          bad_name_pods ⌝ ∗
      "Hown_pod_orphans" ∷ own_orphans_frag γ
        (PodV.kind, set.(StatefulSetV.ObjectMeta').(ObjectMetaV.Namespace'))
        (DfracOwn 1) pod_orphans
  }}}
    @! statefulset.releasePodsWithBadNames #client_ctx #kube_client #set_l #pods_sl
  {{{ (released_pods : list PodV.t), RET #interface.nil;
      "Hset" ∷ StatefulSetV.deepown_l set_l set dq_set ∗
      "Hpods_sl" ∷ pods_sl ↦* ptrs ∗
      "Hpods" ∷
        ([∗ list] ptr;pod ∈ ptrs;pods,
          PodV.deepown_l ptr pod dq_pods) ∗
      "Hown_children" ∷ own_children_frag γ
        (StatefulSetV.key set)
        set.(StatefulSetV.ObjectMeta').(ObjectMetaV.UID') 1
        (children ∖
          list_to_set (PodV.key <$> bad_name_pods)) ∗
      "Hown_pod_orphans" ∷ own_orphans_frag γ
        (PodV.kind, set.(StatefulSetV.ObjectMeta').(ObjectMetaV.Namespace'))
        (DfracOwn 1) (pod_orphans ∪ list_to_set (PodV.key <$> bad_name_pods)) ∗
      "%Hreleased_keys" ∷ ⌜ PodV.key <$> released_pods = PodV.key <$> bad_name_pods ⌝ ∗
      "%Hreleased_updated" ∷ ⌜ Forall2 (λ pod pod', PodV.updated pod.(PodV.Spec') (release_pod_input set pod) pod')
        bad_name_pods released_pods ⌝ ∗
      "Hreleased_frags" ∷ ([∗ list] pod ∈ released_pods,
        own_meta_frag γ (PodV.key pod) pod.(PodV.ObjectMeta').(ObjectMetaV.UID') 1
          pod.(PodV.ObjectMeta') ∗
        own_spec_frag γ (PodV.key pod) pod.(PodV.ObjectMeta').(ObjectMetaV.UID') 1
          (ObjectSpecV.PodSpec pod.(PodV.Spec')))
  }}}.
Proof.
  wp_start as "H". iNamed "H".
  subst bad_name_pods.
  set Bad := (λ pod : PodV.t,
    ¬ pod_has_int32_member_name
      set.(StatefulSetV.ObjectMeta').(ObjectMetaV.Name')
      pod.(PodV.ObjectMeta').(ObjectMetaV.Name')).
  iEval (fold Bad) in "Hown_meta".
  iEval (fold Bad) in "Hown_spec".
  unfold pods_with_bad_names in Hreleaseable.
  fold Bad in Hreleaseable.
  iPoseProof (kview.own_meta_list_no_dup
    PodV.key PodV.ObjectMeta' (filter Bad pods)
    with "Hown_meta") as "%Hbad_name_pods_nodup".
  wp_auto_keep.
  iPersist "ctx". iPersist "kubeClient".
  iDestruct (own_slice_len with "Hpods_sl") as
    %(Hpods_sl_len1 & Hpods_sl_len2).
  iDestruct (own_slice_wf with "Hpods_sl") as
    %Hpods_sl_cap.
  iDestruct (big_sepL2_length with "Hpods") as %Hpods_len.
  set I := (∃ (i : w64) (pod_ptr_value : loc) (released_pods : list PodV.t),
    "Hi_ptr" ∷ i_ptr ↦ i ∗
    "Hset_ptr" ∷ set_ptr ↦ set_l ∗
    "Hset" ∷ StatefulSetV.deepown_l set_l set dq_set ∗
    "Hpod_ptr" ∷ pod_ptr ↦ pod_ptr_value ∗
    "Hpods_sl" ∷ pods_sl ↦* ptrs ∗
    "Hpods" ∷
      ([∗ list] ptr;pod ∈ ptrs;pods,
        PodV.deepown_l ptr pod dq_pods) ∗
    "Hown_meta_todo" ∷
      ([∗ list] pod ∈ filter Bad (drop (sint.nat i) pods),
        own_meta_frag γ
          (PodV.key pod)
          pod.(PodV.ObjectMeta').(ObjectMetaV.UID') 1
          pod.(PodV.ObjectMeta')) ∗
    "Hown_spec_todo" ∷
      ([∗ list] pod ∈ filter Bad (drop (sint.nat i) pods),
        own_spec_frag γ
          (PodV.key pod)
          pod.(PodV.ObjectMeta').(ObjectMetaV.UID') 1
          (ObjectSpecV.PodSpec pod.(PodV.Spec'))) ∗
    "Hown_children" ∷ own_children_frag γ
      (StatefulSetV.key set)
      set.(StatefulSetV.ObjectMeta').(ObjectMetaV.UID') 1
      (children ∖ list_to_set
        (PodV.key <$> filter Bad (take (sint.nat i) pods))) ∗
    "Hown_pod_orphans" ∷ own_orphans_frag γ
      (PodV.kind, set.(StatefulSetV.ObjectMeta').(ObjectMetaV.Namespace'))
      (DfracOwn 1)
      (pod_orphans ∪ list_to_set
        (PodV.key <$> filter Bad (take (sint.nat i) pods))) ∗
    "%Hreleased_keys" ∷ ⌜ PodV.key <$> released_pods =
      PodV.key <$> filter Bad (take (sint.nat i) pods) ⌝ ∗
    "%Hreleased_updated" ∷ ⌜ Forall2 (λ pod pod', PodV.updated pod.(PodV.Spec') (release_pod_input set pod) pod')
      (filter Bad (take (sint.nat i) pods)) released_pods ⌝ ∗
    "Hreleased_frags" ∷ ([∗ list] pod ∈ released_pods,
      own_meta_frag γ (PodV.key pod) pod.(PodV.ObjectMeta').(ObjectMetaV.UID') 1
        pod.(PodV.ObjectMeta') ∗
      own_spec_frag γ (PodV.key pod) pod.(PodV.ObjectMeta').(ObjectMetaV.UID') 1
        (ObjectSpecV.PodSpec pod.(PodV.Spec'))) ∗
    "%Hi" ∷
      ⌜ 0 ≤ sint.Z i ≤ sint.Z (slice.len pods_sl) ⌝
  )%I.
  iAssert I with
    "[i set Hset pod Hpods_sl Hpods Hown_meta Hown_spec
      Hown_children Hown_pod_orphans]" as "Hloop_inv".
  {
    iExists (W64 0), (zero_val loc), [].
    rewrite !take_0 !drop_0 !filter_nil
      fmap_nil list_to_set_nil difference_empty_L union_empty_r_L big_sepL_nil.
    iFrame.
    iPureIntro. split_and!; [done|constructor|done|word..].
  }
  wp_for "Hloop_inv".
  wp_if_destruct.
  - list_elem ptrs (sint.Z i) as this_ptr.
    destruct (decide
      (0 ≤ sint.Z i < sint.Z (slice.len pods_sl)))
      as [_|Hbounds]; last word.
    wp_apply (wp_load_slice_index with
      "[$Hpods_sl]"); [word| |].
    {
      iPureIntro.
      exact Hthis_ptr_lookup.
    }
    iIntros "Hpods_sl".
    wp_auto_keep.
    assert (∃ this_pod,
        pods !! sint.nat i = Some this_pod)
      as [this_pod Hthis_pod_lookup].
    {
      apply lookup_lt_is_Some_2.
      rewrite -Hpods_len Hpods_sl_len1.
      word.
    }
    iDestruct (big_sepL2_lookup_acc with "Hpods")
      as "[Hthis Hpods_restore]".
    { exact Hthis_ptr_lookup. }
    { exact Hthis_pod_lookup. }
    iPoseProof (PodV.deepown_l_split with "Hthis") as
      "(%Hthis_not_null & Hthis_typemeta &
        Hthis_objectmeta_l & Hthis_spec_l & Hthis_status_l)".
    iDestruct "Hthis_objectmeta_l" as
      (this_meta_c)
      "[Hthis_objectmeta_field Hthis_objectmeta]".
    iNamedPrefix "Hthis_objectmeta" "Hthis_meta_".
    iPoseProof (StatefulSetV.deepown_l_split with "Hset") as
      "(%Hset_l_not_null & Hset_typemeta &
        Hset_objectmeta_l & Hset_spec_l & Hset_status_l)".
    iDestruct "Hset_objectmeta_l" as
      (set_meta_c)
      "[Hset_objectmeta_field Hset_objectmeta]".
    iNamedPrefix "Hset_objectmeta" "Hset_meta_".
    wp_auto_keep.
    rewrite Hset_meta_Hdeepown_name Hthis_meta_Hdeepown_name.
    wp_apply (wp_isMemberOf with "[]").
    {
      iPureIntro.
      rewrite Forall_forall in Hname_lengths.
      apply Hname_lengths.
      rewrite -list_elem_of_In.
      apply list_elem_of_lookup_2 in Hthis_pod_lookup.
      exact Hthis_pod_lookup.
    }
    iIntros (member) "%Hmember".
    iCombineNamed "Hset_meta_*" as "Hset_objectmeta".
    iAssert (ObjectMetaV.deepown set_meta_c
        set.(StatefulSetV.ObjectMeta') dq_set)
      with "[Hset_objectmeta]" as "Hset_objectmeta".
    { iNamed "Hset_objectmeta". iFrame. done. }
    iAssert (ObjectMetaV.deepown_l
        (StatefulSetV.objectmeta_ptr set_l)
        set.(StatefulSetV.ObjectMeta') dq_set)
      with "[Hset_objectmeta_field Hset_objectmeta]"
      as "Hset_objectmeta_l".
    { iExists set_meta_c. iFrame. }
    iPoseProof (StatefulSetV.deepown_l_restore _ _ _
      Hset_l_not_null
      with "[$Hset_typemeta $Hset_objectmeta_l
        $Hset_spec_l $Hset_status_l]") as "Hset".
    iCombineNamed "Hthis_meta_*" as "Hthis_objectmeta".
    iAssert (ObjectMetaV.deepown this_meta_c
        this_pod.(PodV.ObjectMeta') dq_pods)
      with "[Hthis_objectmeta]" as "Hthis_objectmeta".
    { iNamed "Hthis_objectmeta". iFrame. done. }
    iAssert (ObjectMetaV.deepown_l
        (PodV.objectmeta_ptr this_ptr)
        this_pod.(PodV.ObjectMeta') dq_pods)
      with "[Hthis_objectmeta_field Hthis_objectmeta]"
      as "Hthis_objectmeta_l".
    { iExists this_meta_c. iFrame. }
    iAssert (PodV.deepown_l this_ptr this_pod dq_pods)
      with
        "[Hthis_typemeta Hthis_objectmeta_l
          Hthis_spec_l Hthis_status_l]"
      as "Hthis".
    {
      iApply (PodV.deepown_l_restore
        this_ptr this_pod dq_pods Hthis_not_null).
      iFrame.
    }
    wp_if_destruct.
    + assert (¬ Bad this_pod) as Hthis_good.
      {
        unfold Bad.
        intros Hthis_bad.
        apply Hthis_bad.
        apply (proj1 Hmember).
        done.
      }
      assert (Htake_next :
          take (S (sint.nat i)) pods =
            take (sint.nat i) pods ++ [this_pod]).
      { by apply take_S_r. }
      assert (Hdrop_current :
          drop (sint.nat i) pods =
            this_pod :: drop (S (sint.nat i)) pods).
      { by apply drop_S. }
      assert (Hnext :
          sint.nat (word.add i (W64 1)) =
            S (sint.nat i)) by word.
      assert (Hfilter_take :
          filter Bad
              (take (sint.nat (word.add i (W64 1))) pods) =
            filter Bad (take (sint.nat i) pods)).
      {
        rewrite Hnext Htake_next list.filter_app.
        assert (filter Bad [this_pod] = []) as ->.
        { by apply filter_singleton_False. }
        by rewrite app_nil_r.
      }
      assert (Hfilter_drop :
          filter Bad (drop (sint.nat i) pods) =
            filter Bad
              (drop (sint.nat (word.add i (W64 1))) pods)).
      {
        rewrite Hnext Hdrop_current.
        by rewrite (filter_cons_False Bad this_pod
          (drop (S (sint.nat i)) pods) Hthis_good).
      }
      iPoseProof ("Hpods_restore" with "Hthis") as "Hpods".
      iApply wp_for_post_continue.
      wp_auto_keep.
      iFrame "HΦ".
      iExists (word.add i (W64 1)), this_ptr, released_pods.
      rewrite Hfilter_take -Hfilter_drop.
      iFrame "∗ %".
      iPureIntro. word.
    + assert (Bad this_pod) as Hthis_bad.
      {
        unfold Bad.
        intros Hthis_good.
        pose proof (proj2 Hmember Hthis_good) as Hfalse.
        done.
      }
      assert (Htake_next :
          take (S (sint.nat i)) pods =
            take (sint.nat i) pods ++ [this_pod]).
      { by apply take_S_r. }
      assert (Hdrop_current :
          drop (sint.nat i) pods =
            this_pod :: drop (S (sint.nat i)) pods).
      { by apply drop_S. }
      iEval (rewrite Hdrop_current
        (filter_cons_True Bad this_pod
          (drop (S (sint.nat i)) pods) Hthis_bad))
        in "Hown_meta_todo".
      iDestruct "Hown_meta_todo" as
        "[Hown_meta_this Hown_meta_todo]".
      iEval (rewrite Hdrop_current
        (filter_cons_True Bad this_pod
          (drop (S (sint.nat i)) pods) Hthis_bad))
        in "Hown_spec_todo".
      iDestruct "Hown_spec_todo" as
        "[Hown_spec_this Hown_spec_todo]".
      assert (Hthis_in_bad_name_pods :
          this_pod ∈ filter Bad pods).
      {
        apply list_elem_of_filter.
        split; first exact Hthis_bad.
        by apply list_elem_of_lookup_2 in Hthis_pod_lookup.
      }
      rewrite Forall_forall in Hreleaseable.
      assert (Hthis_in_bad_name_pods_In :
          In this_pod (filter Bad pods)).
      {
        rewrite -list_elem_of_In.
        exact Hthis_in_bad_name_pods.
      }
      pose proof (Hreleaseable this_pod
        Hthis_in_bad_name_pods_In) as
        (Hthis_valid & Hthis_parent & Hthis_key_in).
      assert (Hthis_key_not_removed :
          PodV.key this_pod ∉
            PodV.key <$> filter Bad (take (sint.nat i) pods)).
      {
        eapply bad_pod_key_not_in_prefix;
          [exact Hbad_name_pods_nodup
          |exact Hthis_pod_lookup
          |exact Hthis_bad].
      }
      assert (Hthis_key_in_current :
          PodV.key this_pod ∈
            children ∖ list_to_set
              (PodV.key <$>
                filter Bad (take (sint.nat i) pods))).
      {
        apply elem_of_difference.
        split; first exact Hthis_key_in.
        rewrite elem_of_list_to_set.
        exact Hthis_key_not_removed.
      }
      wp_apply (wp_releasePod_combined γ model_l
        set_l this_ptr set this_pod
        (children ∖ list_to_set
          (PodV.key <$> filter Bad
            (take (sint.nat i) pods)))
        dq_set dq_pods false 0%nat
        with
          "[$Hpkg $Hisk $Hglobal_l $Hset $Hthis
            $Hown_meta_this $Hown_spec_this
            $Hown_children $Hown_pod_orphans]").
      {
        iFrame "%".
      }
      iIntros (err) "(%Herr & Hrelease_Hset & Hrelease_Hpod & [Hrelease_Hown_children Hreleased_this] &
        Hown_pod_orphans)".
      specialize (Herr eq_refl). subst err.
      iDestruct "Hreleased_this" as (released_pod)
        "(%Hreleased_pod_key & %Hreleased_pod_updated & Hreleased_pod_meta & Hreleased_pod_spec)".
      wp_auto_keep.
      assert (Hnext :
          sint.nat (word.add i (W64 1)) =
            S (sint.nat i)) by word.
      assert (Hfilter_take :
          filter Bad
              (take (sint.nat (word.add i (W64 1))) pods) =
            filter Bad (take (sint.nat i) pods) ++ [this_pod]).
      {
        rewrite Hnext Htake_next list.filter_app.
        assert (filter Bad [this_pod] = [this_pod]) as ->.
        { by apply filter_singleton_True. }
        done.
      }
      assert (Hfilter_drop :
          filter Bad
              (drop (sint.nat (word.add i (W64 1))) pods) =
            filter Bad (drop (S (sint.nat i)) pods)).
      { by rewrite Hnext. }
      assert (Hchildren_next :
          (children ∖ list_to_set
              (PodV.key <$> filter Bad
                (take (sint.nat i) pods))) ∖
              {[PodV.key this_pod]} =
            children ∖ list_to_set
              (PodV.key <$> filter Bad
                (take (sint.nat
                  (word.add i (W64 1))) pods))).
      {
        by rewrite Hfilter_take fmap_app /= list_to_set_app_L
          list_to_set_singleton_L difference_difference_l_L.
      }
      iEval (rewrite Hchildren_next)
        in "Hrelease_Hown_children".
      assert (Horphans_next :
          (pod_orphans ∪ list_to_set
              (PodV.key <$> filter Bad
                (take (sint.nat i) pods))) ∪
              {[PodV.key this_pod]} =
            pod_orphans ∪ list_to_set
              (PodV.key <$> filter Bad
                (take (sint.nat
                  (word.add i (W64 1))) pods))).
      {
        rewrite Hfilter_take fmap_app /= list_to_set_app_L
          list_to_set_singleton_L.
        by rewrite assoc_L.
      }
      iEval (rewrite Horphans_next) in "Hown_pod_orphans".
      assert (Hreleased_keys' : PodV.key <$> released_pods ++ [released_pod] =
          PodV.key <$> filter Bad (take (sint.nat (word.add i (W64 1))) pods)).
      { rewrite Hfilter_take !fmap_app Hreleased_keys /= Hreleased_pod_key. done. }
      assert (Hreleased_updated' : Forall2 (λ pod pod', PodV.updated pod.(PodV.Spec') (release_pod_input set pod) pod')
          (filter Bad (take (sint.nat (word.add i (W64 1))) pods)) (released_pods ++ [released_pod])).
      { rewrite Hfilter_take. apply Forall2_app; [done|]. apply Forall2_cons; [done|constructor]. }
      iPoseProof ("Hpods_restore" with
        "Hrelease_Hpod") as "Hpods".
      iApply wp_for_post_do.
      wp_auto_keep.
      iFrame "HΦ".
      iExists (word.add i (W64 1)), this_ptr, (released_pods ++ [released_pod]).
      rewrite Hfilter_drop. iEval (rewrite big_sepL_snoc).
      iFrame "∗ %".
      iPureIntro. word.
  - assert (Hindex_end :
        sint.nat i = length pods).
    {
      rewrite -Hpods_len Hpods_sl_len1.
      word.
    }
    assert (Htake_all :
        take (sint.nat i) pods = pods).
    {
      rewrite Hindex_end.
      apply take_ge. lia.
    }
    assert (Hdrop_all :
        drop (sint.nat i) pods = []).
    {
      rewrite Hindex_end.
      apply drop_ge. lia.
    }
    iEval (rewrite Htake_all) in "Hown_children Hown_pod_orphans".
    iEval (rewrite Hdrop_all filter_nil !big_sepL_nil)
      in "Hown_meta_todo Hown_spec_todo".
    rewrite Htake_all in Hreleased_keys Hreleased_updated.
    iApply ("HΦ" $! released_pods).
    unfold pods_with_bad_names, Bad. unfold Bad in Hreleased_keys, Hreleased_updated.
    iFrame "∗ %".
Qed.

(** The preservation rule consumes strong ownership only for bad living Pods.
    Terminating Pods use persistent deletion observations instead.  Both the
    successful update and the swallowed NotFound outcome let the loop finish. *)
Lemma wp_releasePodsWithBadNames_combined γ model_l set_l pods_sl
    (set : StatefulSetV.t) (ptrs : list loc) (pods : list PodV.t)
    (children : gset KKey.t) dq_set dq_pods
    (terminating_bound : nat) pod_orphans :
  let Bad := (λ pod : PodV.t,
    ¬ pod_has_int32_member_name
      set.(StatefulSetV.ObjectMeta').(ObjectMetaV.Name')
      pod.(PodV.ObjectMeta').(ObjectMetaV.Name')) in
  let BadLiving := (λ pod : PodV.t, Bad pod ∧ is_pod_alive pod) in
  {{{ "#Hpkg" ∷ is_pkg_init code.controllers.statefulset.pkg_id.statefulset ∗
      "#Hisk" ∷ is_kubernetes γ model_l ∗
      "#Hglobal_l" ∷ (global_addr apimodel.ModelState) ↦□ model_l ∗
      "#Hmodel_init" ∷ is_pkg_init apimodel ∗
      "Hset" ∷ StatefulSetV.deepown_l set_l set dq_set ∗
      "Hpods_sl" ∷ pods_sl ↦* ptrs ∗
      "Hpods" ∷ ([∗ list] ptr;pod ∈ ptrs;pods, PodV.deepown_l ptr pod dq_pods) ∗
      "Hown_meta" ∷ ([∗ list] pod ∈ filter BadLiving pods,
        own_meta_frag γ (PodV.key pod) pod.(PodV.ObjectMeta').(ObjectMetaV.UID') 1
          pod.(PodV.ObjectMeta')) ∗
      "Hown_spec" ∷ ([∗ list] pod ∈ filter BadLiving pods,
        own_spec_frag γ (PodV.key pod) pod.(PodV.ObjectMeta').(ObjectMetaV.UID') 1
          (ObjectSpecV.PodSpec pod.(PodV.Spec'))) ∗
      "Hown_occupied" ∷ ([∗ list] pod ∈ filter BadLiving pods,
        own_occupied_reserved_frag γ 1 (PodV.key pod) pod.(PodV.ObjectMeta').(ObjectMetaV.UID')) ∗
      "#Hown_deletion_observed_frag" ∷ ([∗ list] pod ∈ terminating_pods pods,
        own_deletion_observed_frag γ (PodV.key pod) pod.(PodV.ObjectMeta').(ObjectMetaV.UID')) ∗
      "Hown_children" ∷ own_children_frag γ (StatefulSetV.key set)
        set.(StatefulSetV.ObjectMeta').(ObjectMetaV.UID') 1 children ∗
      "Hown_terminating_children_frag" ∷ own_terminating_children_frag γ (StatefulSetV.key set)
        set.(StatefulSetV.ObjectMeta').(ObjectMetaV.UID') terminating_bound ∗
      "%Hchildren" ∷ ⌜ children = list_to_set (PodV.key <$> filter is_pod_alive pods) ⌝ ∗
      "%Hname_lengths" ∷ ⌜ Forall (λ pod,
        Z.of_nat (length pod.(PodV.ObjectMeta').(ObjectMetaV.Name')) ≤ go_int_max) pods ⌝ ∗
      "%Hreleaseable" ∷ ⌜ Forall (λ pod,
        PodV.valid pod ∧ meta_parent_ref pod.(PodV.ObjectMeta') = Some
          (StatefulSetV.key set, set.(StatefulSetV.ObjectMeta').(ObjectMetaV.UID'))) pods ⌝ ∗
      "%Hnodup" ∷ ⌜ NoDup (PodV.key <$> pods) ⌝ ∗
      "Hown_pod_orphans" ∷ own_orphans_frag γ
        (PodV.kind, set.(StatefulSetV.ObjectMeta').(ObjectMetaV.Namespace'))
        (DfracOwn 1) pod_orphans
  }}}
    @! statefulset.releasePodsWithBadNames #client_ctx #kube_client #set_l #pods_sl
  {{{ (n : nat) (released_pods : list PodV.t) (err : interface.t), RET #err;
      "%Hn" ∷ ⌜ n ≤ length pods ⌝ ∗
      "%Hdone" ∷ ⌜ err = interface.nil → n = length pods ⌝ ∗
      "Hset" ∷ StatefulSetV.deepown_l set_l set dq_set ∗
      "Hpods_sl" ∷ pods_sl ↦* ptrs ∗
      "Hpods" ∷ ([∗ list] ptr;pod ∈ ptrs;pods, PodV.deepown_l ptr pod dq_pods) ∗
      "Hown_meta" ∷ ([∗ list] pod ∈ filter BadLiving (drop n pods),
        own_meta_frag γ (PodV.key pod) pod.(PodV.ObjectMeta').(ObjectMetaV.UID') 1 pod.(PodV.ObjectMeta')) ∗
      "Hown_spec" ∷ ([∗ list] pod ∈ filter BadLiving (drop n pods),
        own_spec_frag γ (PodV.key pod) pod.(PodV.ObjectMeta').(ObjectMetaV.UID') 1
          (ObjectSpecV.PodSpec pod.(PodV.Spec'))) ∗
      "Hown_occupied" ∷ ([∗ list] pod ∈ filter BadLiving (drop n pods),
        own_occupied_reserved_frag γ 1 (PodV.key pod) pod.(PodV.ObjectMeta').(ObjectMetaV.UID')) ∗
      "Hown_children" ∷ own_children_frag γ (StatefulSetV.key set)
        set.(StatefulSetV.ObjectMeta').(ObjectMetaV.UID') 1
          (children ∖ list_to_set (PodV.key <$> filter BadLiving (take n pods))) ∗
      "Hown_terminating_children_frag" ∷ own_terminating_children_frag γ (StatefulSetV.key set)
        set.(StatefulSetV.ObjectMeta').(ObjectMetaV.UID') terminating_bound ∗
      "Hown_pod_orphans" ∷ own_orphans_frag γ
        (PodV.kind, set.(StatefulSetV.ObjectMeta').(ObjectMetaV.Namespace'))
        (DfracOwn 1) (pod_orphans ∪ list_to_set (PodV.key <$> filter BadLiving (take n pods))) ∗
      "%Hreleased_keys" ∷ ⌜ PodV.key <$> released_pods = PodV.key <$> filter BadLiving (take n pods) ⌝ ∗
      "%Hreleased_updated" ∷ ⌜ Forall2 (λ pod pod', PodV.updated pod.(PodV.Spec') (release_pod_input set pod) pod')
        (filter BadLiving (take n pods)) released_pods ⌝ ∗
      "Hreleased_frags" ∷ ([∗ list] pod ∈ released_pods,
        own_meta_frag γ (PodV.key pod) pod.(PodV.ObjectMeta').(ObjectMetaV.UID') 1
          pod.(PodV.ObjectMeta') ∗
        own_spec_frag γ (PodV.key pod) pod.(PodV.ObjectMeta').(ObjectMetaV.UID') 1
          (ObjectSpecV.PodSpec pod.(PodV.Spec')))
  }}}.
Proof.
  simpl. wp_start as "H". iNamed "H".
  set Bad := (λ pod : PodV.t,
    ¬ pod_has_int32_member_name
      set.(StatefulSetV.ObjectMeta').(ObjectMetaV.Name')
      pod.(PodV.ObjectMeta').(ObjectMetaV.Name')).
  set BadLiving := (λ pod : PodV.t, Bad pod ∧ is_pod_alive pod).
  wp_auto_keep.
  iPersist "ctx". iPersist "kubeClient".
  iDestruct (own_slice_len with "Hpods_sl") as %(Hpods_sl_len1 & Hpods_sl_len2).
  iDestruct (own_slice_wf with "Hpods_sl") as %Hpods_sl_cap.
  iDestruct (big_sepL2_length with "Hpods") as %Hpods_len.
  set I := (∃ (i : w64) (pod_ptr_value : loc) (released_pods : list PodV.t),
    "Hi_ptr" ∷ i_ptr ↦ i ∗
    "Hset_ptr" ∷ set_ptr ↦ set_l ∗
    "Hset" ∷ StatefulSetV.deepown_l set_l set dq_set ∗
    "Hpod_ptr" ∷ pod_ptr ↦ pod_ptr_value ∗
    "Hpods_sl" ∷ pods_sl ↦* ptrs ∗
    "Hpods" ∷ ([∗ list] ptr;pod ∈ ptrs;pods, PodV.deepown_l ptr pod dq_pods) ∗
    "Hown_meta_todo" ∷ ([∗ list] pod ∈ filter BadLiving (drop (sint.nat i) pods),
      own_meta_frag γ (PodV.key pod) pod.(PodV.ObjectMeta').(ObjectMetaV.UID') 1
        pod.(PodV.ObjectMeta')) ∗
    "Hown_spec_todo" ∷ ([∗ list] pod ∈ filter BadLiving (drop (sint.nat i) pods),
      own_spec_frag γ (PodV.key pod) pod.(PodV.ObjectMeta').(ObjectMetaV.UID') 1
        (ObjectSpecV.PodSpec pod.(PodV.Spec'))) ∗
    "Hown_occupied_todo" ∷ ([∗ list] pod ∈ filter BadLiving (drop (sint.nat i) pods),
      own_occupied_reserved_frag γ 1 (PodV.key pod) pod.(PodV.ObjectMeta').(ObjectMetaV.UID')) ∗
    "Hown_children" ∷ own_children_frag γ (StatefulSetV.key set)
      set.(StatefulSetV.ObjectMeta').(ObjectMetaV.UID') 1
        (children ∖ list_to_set (PodV.key <$> filter BadLiving (take (sint.nat i) pods))) ∗
    "Hown_terminating_children_frag" ∷ own_terminating_children_frag γ (StatefulSetV.key set)
      set.(StatefulSetV.ObjectMeta').(ObjectMetaV.UID') terminating_bound ∗
    "Hown_pod_orphans" ∷ own_orphans_frag γ
      (PodV.kind, set.(StatefulSetV.ObjectMeta').(ObjectMetaV.Namespace'))
      (DfracOwn 1) (pod_orphans ∪ list_to_set (PodV.key <$> filter BadLiving (take (sint.nat i) pods))) ∗
    "%Hreleased_keys" ∷ ⌜ PodV.key <$> released_pods =
      PodV.key <$> filter BadLiving (take (sint.nat i) pods) ⌝ ∗
    "%Hreleased_updated" ∷ ⌜ Forall2 (λ pod pod', PodV.updated pod.(PodV.Spec') (release_pod_input set pod) pod')
      (filter BadLiving (take (sint.nat i) pods)) released_pods ⌝ ∗
    "Hreleased_frags" ∷ ([∗ list] pod ∈ released_pods,
      own_meta_frag γ (PodV.key pod) pod.(PodV.ObjectMeta').(ObjectMetaV.UID') 1
        pod.(PodV.ObjectMeta') ∗
      own_spec_frag γ (PodV.key pod) pod.(PodV.ObjectMeta').(ObjectMetaV.UID') 1
        (ObjectSpecV.PodSpec pod.(PodV.Spec'))) ∗
    "%Hi" ∷ ⌜ 0 ≤ sint.Z i ≤ sint.Z (slice.len pods_sl) ⌝)%I.
  iAssert I with "[i set Hset pod Hpods_sl Hpods Hown_meta Hown_spec Hown_occupied
      Hown_children Hown_terminating_children_frag Hown_pod_orphans]" as "Hloop_inv".
  { iExists (W64 0), (zero_val loc), [].
    rewrite !take_0 !drop_0 !filter_nil fmap_nil list_to_set_nil difference_empty_L union_empty_r_L
      big_sepL_nil.
    iFrame. iPureIntro. split_and!; [done|constructor|done|word..]. }
  wp_for "Hloop_inv". wp_if_destruct.
  - list_elem ptrs (sint.Z i) as this_ptr.
    destruct (decide (0 ≤ sint.Z i < sint.Z (slice.len pods_sl))) as [_|Hbounds]; last word.
    wp_apply (wp_load_slice_index with "[$Hpods_sl]"); [word| |].
    { iPureIntro. exact Hthis_ptr_lookup. }
    iIntros "Hpods_sl". wp_auto_keep.
    assert (∃ this_pod, pods !! sint.nat i = Some this_pod) as [this_pod Hthis_pod_lookup].
    { apply lookup_lt_is_Some_2. rewrite -Hpods_len Hpods_sl_len1. word. }
    iDestruct (big_sepL2_lookup_acc with "Hpods") as "[Hthis Hpods_restore]";
      [exact Hthis_ptr_lookup|exact Hthis_pod_lookup|].
    iPoseProof (PodV.deepown_l_split with "Hthis") as
      "(%Hthis_not_null & Hthis_typemeta & Hthis_objectmeta_l & Hthis_spec_l & Hthis_status_l)".
    iDestruct "Hthis_objectmeta_l" as (this_meta_c) "[Hthis_objectmeta_field Hthis_objectmeta]".
    iNamedPrefix "Hthis_objectmeta" "Hthis_meta_".
    iPoseProof (StatefulSetV.deepown_l_split with "Hset") as
      "(%Hset_l_not_null & Hset_typemeta & Hset_objectmeta_l & Hset_spec_l & Hset_status_l)".
    iDestruct "Hset_objectmeta_l" as (set_meta_c) "[Hset_objectmeta_field Hset_objectmeta]".
    iNamedPrefix "Hset_objectmeta" "Hset_meta_".
    wp_auto_keep. rewrite Hset_meta_Hdeepown_name Hthis_meta_Hdeepown_name.
    wp_apply (wp_isMemberOf with "[]").
    { iPureIntro. rewrite Forall_forall in Hname_lengths. apply Hname_lengths.
      rewrite -list_elem_of_In. by apply list_elem_of_lookup_2 in Hthis_pod_lookup. }
    iIntros (member) "%Hmember".
    iCombineNamed "Hset_meta_*" as "Hset_objectmeta".
    iAssert (ObjectMetaV.deepown set_meta_c set.(StatefulSetV.ObjectMeta') dq_set)
      with "[Hset_objectmeta]" as "Hset_objectmeta".
    { iNamed "Hset_objectmeta". iFrame. done. }
    iAssert (ObjectMetaV.deepown_l (StatefulSetV.objectmeta_ptr set_l)
        set.(StatefulSetV.ObjectMeta') dq_set)
      with "[Hset_objectmeta_field Hset_objectmeta]" as "Hset_objectmeta_l".
    { iExists set_meta_c. iFrame. }
    iPoseProof (StatefulSetV.deepown_l_restore _ _ _ Hset_l_not_null
      with "[$Hset_typemeta $Hset_objectmeta_l $Hset_spec_l $Hset_status_l]") as "Hset".
    iCombineNamed "Hthis_meta_*" as "Hthis_objectmeta".
    iAssert (ObjectMetaV.deepown this_meta_c this_pod.(PodV.ObjectMeta') dq_pods)
      with "[Hthis_objectmeta]" as "Hthis_objectmeta".
    { iNamed "Hthis_objectmeta". iFrame. done. }
    iAssert (ObjectMetaV.deepown_l (PodV.objectmeta_ptr this_ptr)
        this_pod.(PodV.ObjectMeta') dq_pods)
      with "[Hthis_objectmeta_field Hthis_objectmeta]" as "Hthis_objectmeta_l".
    { iExists this_meta_c. iFrame. }
    iAssert (PodV.deepown_l this_ptr this_pod dq_pods)
      with "[Hthis_typemeta Hthis_objectmeta_l Hthis_spec_l Hthis_status_l]" as "Hthis".
    { iApply (PodV.deepown_l_restore this_ptr this_pod dq_pods Hthis_not_null). iFrame. }
    assert (Htake_next : take (S (sint.nat i)) pods = take (sint.nat i) pods ++ [this_pod]) by
      (by apply take_S_r).
    assert (Hdrop_current : drop (sint.nat i) pods = this_pod :: drop (S (sint.nat i)) pods) by
      (by apply drop_S).
    assert (Hnext : sint.nat (word.add i (W64 1)) = S (sint.nat i)) by word.
    wp_if_destruct.
    + assert (Hthis_good : ¬ Bad this_pod).
      { unfold Bad. intros Hbad. apply Hbad. by apply (proj1 Hmember). }
      assert (Hthis_not_bad_living : ¬ BadLiving this_pod) by (unfold BadLiving; tauto).
      assert (Hfilter_take : filter BadLiving (take (sint.nat (word.add i (W64 1))) pods) =
          filter BadLiving (take (sint.nat i) pods)).
      { rewrite Hnext Htake_next list.filter_app.
        assert (filter BadLiving [this_pod] = []) as ->.
        { by apply filter_singleton_False. }
        by rewrite app_nil_r. }
      assert (Hfilter_drop : filter BadLiving (drop (sint.nat i) pods) =
          filter BadLiving (drop (sint.nat (word.add i (W64 1))) pods)).
      { rewrite Hnext Hdrop_current.
        by rewrite (filter_cons_False BadLiving this_pod _ Hthis_not_bad_living). }
      iPoseProof ("Hpods_restore" with "Hthis") as "Hpods".
      iApply wp_for_post_continue. wp_auto_keep. iFrame "HΦ".
      iExists (word.add i (W64 1)), this_ptr, released_pods. rewrite Hfilter_take -Hfilter_drop.
      iFrame "∗ %". iPureIntro. word.
    + assert (Hthis_bad : Bad this_pod).
      { unfold Bad. intros Hgood. discriminate (proj2 Hmember Hgood). }
      rewrite Forall_forall in Hreleaseable.
      pose proof (Hreleaseable this_pod ltac:(rewrite -list_elem_of_In;
        exact (list_elem_of_lookup_2 _ _ _ Hthis_pod_lookup))) as
        (Hthis_valid & Hthis_parent).
      destruct (decide (is_pod_alive this_pod)) as [Hthis_living|Hthis_terminating].
      * assert (Hthis_bad_living : BadLiving this_pod) by (split; done).
        iEval (rewrite Hdrop_current
          (filter_cons_True BadLiving this_pod _ Hthis_bad_living))
          in "Hown_meta_todo Hown_spec_todo Hown_occupied_todo".
        iDestruct "Hown_meta_todo" as "[Hown_meta_this Hown_meta_todo]".
        iDestruct "Hown_spec_todo" as "[Hown_spec_this Hown_spec_todo]".
        iDestruct "Hown_occupied_todo" as "[Hown_occupied_this Hown_occupied_todo]".
        assert (Hthis_key_in : PodV.key this_pod ∈
            list_to_set (C:=gset KKey.t) (PodV.key <$> filter is_pod_alive pods)).
        { rewrite elem_of_list_to_set. apply list_elem_of_fmap_2.
          apply list_elem_of_filter. split; first exact Hthis_living.
          by apply list_elem_of_lookup_2 in Hthis_pod_lookup. }
        assert (Hbad_living_nodup : NoDup (PodV.key <$> filter BadLiving pods)).
        { by apply NoDup_fmap_filter. }
        assert (Hthis_key_not_removed : PodV.key this_pod ∉
            PodV.key <$> filter BadLiving (take (sint.nat i) pods)).
        { eapply bad_pod_key_not_in_prefix; done. }
        assert (Hthis_key_in_current : PodV.key this_pod ∈
            list_to_set (C:=gset KKey.t) (PodV.key <$> filter is_pod_alive pods) ∖
              list_to_set (PodV.key <$> filter BadLiving (take (sint.nat i) pods))).
        { apply elem_of_difference. split; first exact Hthis_key_in.
          rewrite elem_of_list_to_set. exact Hthis_key_not_removed. }
        wp_apply (wp_releasePod_combined γ model_l set_l this_ptr set this_pod
          (list_to_set (C:=gset KKey.t) (PodV.key <$> filter is_pod_alive pods) ∖
            list_to_set (PodV.key <$> filter BadLiving (take (sint.nat i) pods)))
          dq_set dq_pods false terminating_bound with
          "[$Hpkg $Hisk $Hglobal_l $Hset $Hthis $Hown_meta_this $Hown_spec_this $Hown_children
            $Hown_pod_orphans]").
        { iFrame "%". }
        iIntros (err) "(%Herr & Hset & Hthis & [Hown_children Hreleased_this] & Hown_pod_orphans)".
        specialize (Herr eq_refl). subst err. wp_auto_keep.
        iDestruct "Hreleased_this" as (released_pod)
          "(%Hreleased_pod_key & %Hreleased_pod_updated & Hreleased_pod_meta & Hreleased_pod_spec)".
        assert (Hfilter_take : filter BadLiving (take (sint.nat (word.add i (W64 1))) pods) =
            filter BadLiving (take (sint.nat i) pods) ++ [this_pod]).
        { rewrite Hnext Htake_next list.filter_app.
          assert (filter BadLiving [this_pod] = [this_pod]) as ->.
          { by apply filter_singleton_True. }
          done. }
        assert (Hchildren_next :
            (list_to_set (C:=gset KKey.t) (PodV.key <$> filter is_pod_alive pods) ∖
              list_to_set (PodV.key <$> filter BadLiving (take (sint.nat i) pods))) ∖
              {[PodV.key this_pod]} =
            list_to_set (C:=gset KKey.t) (PodV.key <$> filter is_pod_alive pods) ∖
              list_to_set (PodV.key <$> filter BadLiving
                (take (sint.nat (word.add i (W64 1))) pods))).
        { rewrite Hfilter_take fmap_app /= list_to_set_app_L
            list_to_set_singleton_L difference_difference_l_L. done. }
        iEval (rewrite Hchildren_next) in "Hown_children".
        assert (Horphans_next :
            (pod_orphans ∪ list_to_set (PodV.key <$> filter BadLiving (take (sint.nat i) pods))) ∪
              {[PodV.key this_pod]} =
            pod_orphans ∪ list_to_set (PodV.key <$> filter BadLiving
              (take (sint.nat (word.add i (W64 1))) pods))).
        { rewrite Hfilter_take fmap_app /= list_to_set_app_L list_to_set_singleton_L.
          by rewrite assoc_L. }
        iEval (rewrite Horphans_next) in "Hown_pod_orphans".
        assert (Hreleased_keys' : PodV.key <$> released_pods ++ [released_pod] =
            PodV.key <$> filter BadLiving (take (S (sint.nat i)) pods)).
        { rewrite -Hnext Hfilter_take !fmap_app Hreleased_keys /= Hreleased_pod_key. done. }
        assert (Hreleased_updated' : Forall2 (λ pod pod', PodV.updated pod.(PodV.Spec') (release_pod_input set pod) pod')
            (filter BadLiving (take (S (sint.nat i)) pods)) (released_pods ++ [released_pod])).
        { rewrite -Hnext Hfilter_take. apply Forall2_app; [done|]. apply Forall2_cons; [done|constructor]. }
        iPoseProof ("Hpods_restore" with "Hthis") as "Hpods".
        iApply wp_for_post_do. wp_auto_keep. iFrame "HΦ".
        iExists (word.add i (W64 1)), this_ptr, (released_pods ++ [released_pod]). rewrite Hnext.
        iEval (rewrite big_sepL_snoc). iFrame "∗ %". iPureIntro. word.
      * assert (Hthis_not_bad_living : ¬ BadLiving this_pod) by (unfold BadLiving; tauto).
        assert (Hthis_observed : this_pod ∈ terminating_pods pods).
        { unfold terminating_pods, pod_is_terminating, pod_is_living.
          apply list_elem_of_filter. split; first exact Hthis_terminating.
          by apply list_elem_of_lookup_2 in Hthis_pod_lookup. }
        iDestruct (big_sepL_elem_of_acc _ _ _ Hthis_observed with "Hown_deletion_observed_frag") as
          "[#Hthis_observed _]".
        wp_apply (wp_releasePod_combined γ model_l set_l this_ptr set this_pod ∅
          dq_set dq_pods true terminating_bound with
          "[$Hpkg $Hisk $Hglobal_l $Hset $Hthis $Hthis_observed $Hown_terminating_children_frag
            $Hown_pod_orphans]").
        { iFrame "%". }
        iIntros (err) "(_ & Hset & Hthis & Hown_terminating_children_frag & Hown_pod_orphans)".
        assert (Hfilter_take : filter BadLiving (take (sint.nat (word.add i (W64 1))) pods) =
            filter BadLiving (take (sint.nat i) pods)).
        { rewrite Hnext Htake_next list.filter_app.
          assert (filter BadLiving [this_pod] = []) as ->.
          { by apply filter_singleton_False. }
          by rewrite app_nil_r. }
        assert (Hfilter_drop : filter BadLiving (drop (sint.nat i) pods) =
            filter BadLiving (drop (sint.nat (word.add i (W64 1))) pods)).
        { rewrite Hnext Hdrop_current.
          by rewrite (filter_cons_False BadLiving this_pod _ Hthis_not_bad_living). }
        iPoseProof ("Hpods_restore" with "Hthis") as "Hpods".
        destruct err as [err_ok|].
        { wp_auto_keep. iApply wp_for_post_return. wp_auto_keep.
          iApply ("HΦ" $! (sint.nat i) released_pods (interface.ok err_ok)).
          iFrame "∗ %". iPureIntro. split; first word. intros Hnil. inversion Hnil. }
        wp_auto_keep. iApply wp_for_post_do. wp_auto_keep. iFrame "HΦ".
        iExists (word.add i (W64 1)), this_ptr, released_pods.
        rewrite Hfilter_take -Hfilter_drop. iFrame "∗ %". iPureIntro. word.
  - assert (Hindex_end : sint.nat i = length pods).
    { rewrite -Hpods_len Hpods_sl_len1. word. }
    assert (Htake_all : take (sint.nat i) pods = pods).
    { rewrite Hindex_end. apply take_ge. lia. }
    assert (Hdrop_all : drop (sint.nat i) pods = []).
    { rewrite Hindex_end. apply drop_ge. lia. }
    iEval (rewrite Htake_all) in "Hown_children Hown_pod_orphans".
    iEval (rewrite Hdrop_all filter_nil !big_sepL_nil)
      in "Hown_meta_todo Hown_spec_todo Hown_occupied_todo".
    rewrite Htake_all in Hreleased_keys Hreleased_updated.
    iApply ("HΦ" $! (length pods) released_pods interface.nil).
    rewrite -Hindex_end Htake_all Hdrop_all /=. iFrame "∗ %". iPureIntro. split; done.
Qed.

End proof.
