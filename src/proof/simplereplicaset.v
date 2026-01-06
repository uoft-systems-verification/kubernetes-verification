From New.proof Require Import prelude empty_ffi.
From New.proof Require Export get index create delete util.
From New.proof.kubernetes_model Require Export simplereplicaset_init.
From New.proof.k8s_io.kubernetes.pkg Require Export controller.
From New.proof.k8s_io.apimachinery.pkg.runtime Require Export schema.
From New.proof.k8s_io.apimachinery.pkg.api Require Export errors.

Section proof.
Context `{!mapG Σ KKey.t PureKObject.t}.
Context `{!mapG Σ KKey.t (gset KKey.t)}.
Context `{!auth_setG Σ KKey.t}.
Context `{hG: !heapGS Σ} {go_ctx: GoContext}.

Lemma wp_manageReplicas γ l (gv: schema.GroupVersion.t) pod_l_sl rs_l
  (ptrs: list loc) active_pods active_pure_pods rs pure_rs rs_key pure_pod_map active_pure_pod_map grand_child_keys dq1 dq2 (n: w32):
  {{{ is_pkg_init simplereplicaset ∗
      "#Hisk" ∷ is_kubernetes γ l ∗
      "#Hglobal_l" ∷ (global_addr simplereplicaset.state) ↦□ l ∗
      "#Hglobal_gv" ∷ (global_addr v1.SchemeGroupVersion) ↦□ gv ∗
      "Hpod_l_sl" ∷ pod_l_sl ↦* ptrs ∗
      "Hptrs" ∷ ([∗ list] ptr;pod ∈ ptrs;active_pods, ptr ↦{dq1} pod) ∗
      "Hdeepown_pods" ∷ ([∗ list] pod;pure_pod ∈ active_pods;active_pure_pods, PurePod.deepown pod pure_pod dq1) ∗
      "Hrs_l" ∷ rs_l ↦{dq2} rs ∗
      "Hdeepown_rs" ∷ PureReplicaSet.deepown rs pure_rs dq2 ∗
      "%Hpure_rs_well_formed" ∷ ⌜ PureReplicaSet.well_formed pure_rs ⌝ ∗
      "%Hpure_rs_name_short" ∷ ⌜ length pure_rs.(PureReplicaSet.ObjectMeta').(PureObjectMeta.Name') < 58 ⌝ ∗
      "%Hrs_key_namespace_eq" ∷ ⌜ pure_rs.(PureReplicaSet.ObjectMeta').(PureObjectMeta.Namespace') = rs_key.(KKey.Namespace') ⌝ ∗
      "%Hrs_key_name_eq" ∷ ⌜ pure_rs.(PureReplicaSet.ObjectMeta').(PureObjectMeta.Name') = rs_key.(KKey.Name') ⌝ ∗
      "%Hrs_key_kind_eq" ∷ ⌜ rs_key.(KKey.Kind') = "ReplicaSet"%go ⌝ ∗
      "Hghostown_rs" ∷ rs_key [[ γ.(γ_state) ]]↦ (PureKObject.ReplicaSet pure_rs) ∗
      "Hghostown_pods" ∷ ([∗ map] key ↦ pod ∈ pure_pod_map, key [[ γ.(γ_state) ]]↦ PureKObject.Pod pod) ∗
      "Hghostown_children" ∷ rs_key [[ γ.(γ_children) ]]↦ dom pure_pod_map ∗
      "Hghostown_grandchildren" ∷ ([∗ map] key ↦ s ∈ grand_child_keys, key [[ γ.(γ_children) ]]↦ s) ∗
      "%Hdom_eq" ∷ ⌜ dom pure_pod_map = dom grand_child_keys ⌝ ∗
      "%Hpods_keys_eq" ∷ ⌜ ∀ key pod, pure_pod_map !! key = Some pod → key = PurePod.key pod ⌝ ∗
      "%Hpods_ns_eq" ∷ ⌜ ∀ key, key ∈ dom pure_pod_map → key.(KKey.Namespace') = rs_key.(KKey.Namespace') ⌝ ∗
      "%Hactive_map_eq" ∷ ⌜ active_pure_pod_map = filter (λ kv, controller.is_pure_pod_active (snd kv)) pure_pod_map ⌝ ∗
      "%Hlen_size_eq" ∷ ⌜ length active_pure_pods = size active_pure_pod_map ⌝ ∗
      "%Hin" ∷ ⌜ ∀ pure_pod, pure_pod ∈ active_pure_pods → active_pure_pod_map !! (PurePod.key pure_pod) = Some pure_pod ⌝ ∗
      "%Hno_dup" ∷ ⌜ ∀ i j p1 p2, i ≠ j → active_pure_pods !! i = Some p1 → active_pure_pods !! j = Some p2 → (PurePod.key p1) ≠ (PurePod.key p2) ⌝ ∗
      "%Hreplicas_eq" ∷ ⌜ pure_rs.(PureReplicaSet.Spec').(PureReplicaSetSpec.Replicas') = Some n ⌝
  }}}
  @! simplereplicaset.manageReplicas #pod_l_sl #rs_l
  {{{ pure_pod_map' grand_child_keys', RET #interface.nil;
      rs_key [[ γ.(γ_state) ]]↦ (PureKObject.ReplicaSet pure_rs) ∗
      ([∗ map] key ↦ pod ∈ pure_pod_map', key [[ γ.(γ_state) ]]↦ PureKObject.Pod pod) ∗
      rs_key [[ γ.(γ_children) ]]↦ dom pure_pod_map' ∗
      ([∗ map] key ↦ s ∈ grand_child_keys', key [[ γ.(γ_children) ]]↦ s) ∗
      ⌜ dom pure_pod_map' = dom grand_child_keys' ⌝ ∗
      ⌜ size (filter (λ kv, controller.is_pure_pod_active (snd kv)) pure_pod_map') = sint.nat n ⌝
  }}}.
Proof.
  wp_start as "H". iNamed "H".
  iDestruct (own_slice_len with "Hpod_l_sl") as %(Hpod_l_sl_len1 & Hpod_l_sl_len2).
  iDestruct (own_slice_wf with "Hpod_l_sl") as %Hpod_l_sl_cap.
  iDestruct (big_sepL2_length with "Hptrs") as %Hlen1.
  iDestruct (big_sepL2_length with "Hdeepown_pods") as %Hlen2.
  assert (size active_pure_pod_map = sint.nat (slice.len_f pod_l_sl)) as Hslice_len by congruence.
  iDestruct (struct_fields_split with "Hrs_l") as "Hrs_l". iNamed "Hrs_l". wp_auto.
  iNamedPrefix "Hdeepown_rs" "Hrs_". iNamedPrefix "Hrs_Hdeepown_spec" "Hrs_".
  iAssert ((rs.(v1.ReplicaSet.Spec').(v1.ReplicaSetSpec.Replicas')↦{dq2}n)%I) with "[Hrs_Hdeepown_replicas_some]" as "Hreplicas".
  { rewrite Hreplicas_eq. iDestruct "Hrs_Hdeepown_replicas_some" as "(%replicas & Hreplicas & ->)". done. }
  wp_auto.
  destruct Hpure_rs_well_formed as (Hpure_rs_meta_well_formed & Hpure_rs_spec_well_formed & _).
  destruct Hpure_rs_spec_well_formed as (Hpure_rs_spec_replicas_well_formed & Hpure_rs_spec_template_well_formed).
  assert (0 ≤ sint.Z n) as Hn.
  { destruct Hpure_rs_spec_replicas_well_formed as (i & Hi_eq & Hi). rewrite Hi_eq in Hreplicas_eq. congruence. }
  assert ((sint.Z (word.sub (slice.len_f pod_l_sl) (W64 (sint.Z n)))) = (sint.Z (slice.len_f pod_l_sl)) - (sint.Z n)) as ->.
  { word. }
  assert ((sint.Z (W64 0)) = 0) as -> by word.
  wp_if_destruct.
  - set I := (∃ (i: w64) (pure_pod_map': gmap KKey.t PurePod.t) (grand_child_keys': gmap KKey.t (gset KKey.t)),
      "Hi_ptr" ∷ i_ptr ↦ i ∗
      "Hghostown_pods" ∷ ([∗ map] key ↦ pod ∈ pure_pod_map', key [[ γ.(γ_state) ]]↦ PureKObject.Pod pod) ∗
      "Hghostown_children" ∷ rs_key [[ γ.(γ_children) ]]↦ dom pure_pod_map' ∗
      "Hghostown_grandchildren" ∷ ([∗ map] key ↦ s ∈ grand_child_keys', key [[ γ.(γ_children) ]]↦ s) ∗
      "%Hdom_eq'" ∷ ⌜ dom pure_pod_map' = dom grand_child_keys' ⌝ ∗
      "%Hpod_number'" ∷ ⌜ size (filter (λ kv, controller.is_pure_pod_active (snd kv)) pure_pod_map') = Z.to_nat ((sint.Z (slice.len_f pod_l_sl)) + sint.Z i) ⌝ ∗
      "%Hi" :: ⌜0 ≤ sint.Z i ≤ sint.Z (word.mul (word.sub (slice.len_f pod_l_sl) (W64 (sint.Z n))) (W64 (-1)))⌝
    )%I.
    iAssert (I) with "[i Hghostown_pods Hghostown_children Hghostown_grandchildren]" as "Hloop_inv". {
    iExists (W64 0), pure_pod_map, grand_child_keys.
    iFrame. iPureIntro. split_and!; [done|word|word|word]. }
    wp_for "Hloop_inv". wp_if_destruct.
    + wp_apply wp_globals_get. wp_apply schema.wp_GroupVersion__WithKind.
      { (* TODO: why so cumbersome? *) iAssert (is_pkg_init code.k8s_io.api.apps.v1.v1) as "H". all: iPkgInit. }
      iIntros (gvk) "%Hgvk". wp_auto.
      wp_apply (v1.wp_NewControllerRef_replicaset with "[$HObjectMeta $Hrs_Hdeepown_objectmeta]"); [done|].
      iIntros (controller_ref_l controller_ref pure_controller_ref) "(Hdeepown_controller_ref & %Hcontroller_ref_well_formed & HObjectMeta & Hrs_Hdeepown_objectmeta)". wp_auto.
      iDestruct (struct_fields_split with "HSpec") as "HSpec". iNamed "HSpec".
      wp_apply (controller.wp_GetPodFromTemplate with "[$HTemplate $Hrs_Hdeepown_template $HObjectMeta $Hrs_Hdeepown_objectmeta $Hdeepown_controller_ref]"); [done|].
      iIntros (this_pod_l this_pod this_pure_pod) "(Hdeepown_l_this_pod & %Hobj_has_controller_parent_of & %Hthis_pod_well_formed 
        & HTemplate & Hrs_Hdeepown_template & HObjectMeta & Hrs_Hdeepown_objectmeta)". wp_auto.
      rewrite bool_decide_true //. wp_auto.
      wp_apply wp_globals_get.
      iAssert(⌜ rs.(v1.ReplicaSet.ObjectMeta').(v1.ObjectMeta.Namespace') = pure_rs.(PureReplicaSet.ObjectMeta').(PureObjectMeta.Namespace') ⌝%I) as "->".
      { iNamed "Hrs_Hdeepown_objectmeta". done. }
      wp_apply (wp_State__PodCreate_without_name with "[$Hdeepown_l_this_pod $Hghostown_rs $Hghostown_children]").
      { iFrame "#". iPureIntro. unfold PureObjectMeta.well_formed in Hpure_rs_meta_well_formed.
        rewrite Hrs_key_kind_eq. rewrite <-Hrs_key_name_eq. split_and!. all: intuition. }
      iIntros (created_pod_ptr created_pod created_pure_pod new_name new_key) "H".
      iNamedPrefix "H" "Hfrom_create_". wp_auto.
      rewrite bool_decide_true //. wp_auto.
      iApply wp_for_post_do. wp_auto.
      assert (is_pure_pod_active created_pure_pod) as Hactive.
      { (* TODO: find the right spec to prove this assert *) admit. }
      iAssert (I) with "[Hi_ptr Hghostown_pods Hghostown_grandchildren Hfrom_create_Hown_created_pure_pod
        Hfrom_create_Hown_child_keys Hfrom_create_Hown_grandchild_keys]" as "loop_inv".
      { unfold I. iExists (word.add i (W64 1)), (<[new_key := created_pure_pod]> pure_pod_map'), (<[new_key := ∅]> grand_child_keys').
        iFrame.
        assert (pure_pod_map' !! new_key = None) as Hnot_in1.
        { apply not_elem_of_dom. done. }
        assert (grand_child_keys' !! new_key = None) as Hnot_in2.
        { apply not_elem_of_dom. rewrite <-Hdom_eq'. done. }
        iDestruct (big_sepM_insert _ pure_pod_map' new_key created_pure_pod Hnot_in1 with "[$Hghostown_pods $Hfrom_create_Hown_created_pure_pod]") as "Hghostown_pods".
        iDestruct (big_sepM_insert _ grand_child_keys' new_key ∅ Hnot_in2 with "[$Hghostown_grandchildren $Hfrom_create_Hown_grandchild_keys]") as "Hghostown_grandchildren".
        assert (dom pure_pod_map' ∪ {[new_key]} = dom (<[new_key:=created_pure_pod]> pure_pod_map')) as ->.
        { rewrite dom_insert_L. rewrite union_comm_L. done. }
        iFrame.
        iPureIntro. split.
        - rewrite !dom_insert_L. rewrite Hdom_eq'. done.
        - rewrite map_filter_insert. simpl. destruct (decide (is_pure_pod_active created_pure_pod)); [|done].
          rewrite map_size_insert. rewrite Hpod_number'.
          assert (filter (λ kv : KKey.t * PurePod.t, is_pure_pod_active kv.2) pure_pod_map' !! new_key = None) as ->.
          { rewrite map_lookup_filter. rewrite Hnot_in1. done. }
          word.
      }
      iFrame.
      iApply (struct_fields_combine (V:=v1.ReplicaSetSpec.t)). iFrame.
    + iApply "HΦ". iFrame. iPureIntro. split. all: try done.
      rewrite Hpod_number'. word.
  - wp_if_destruct.
    2: { iApply "HΦ". iFrame. iPureIntro. split.
      * rewrite Hdom_eq. done.
      * word. }
    wp_bind.
    wp_apply wp_slice_slice_pure; [iPureIntro;word|].
    iDestruct (own_slice_f 0 (word.sub (slice.len_f pod_l_sl) (W64 (sint.Z n))) with "Hpod_l_sl")
      as "(Hbefore_slice & Hslice & Hafter_slice )"; [word|].
    iDestruct (own_slice_len with "Hslice") as %(Hslice_len1 & Hslice_len2).
    set I := (∃ (i: w64) (pod: loc) (pure_pod_map' active_pure_pod_map': gmap KKey.t PurePod.t) (grand_child_keys': gmap KKey.t (gset KKey.t)),
      "Hi_ptr" ∷ i_ptr ↦ i ∗
      "Hpod_ptr" ∷ pod_ptr ↦ pod ∗
      "Hghostown_pods" ∷ ([∗ map] key ↦ pod ∈ pure_pod_map', key [[ γ.(γ_state) ]]↦ PureKObject.Pod pod) ∗
      "Hghostown_children" ∷ rs_key [[ γ.(γ_children) ]]↦ dom pure_pod_map' ∗
      "Hghostown_grandchildren" ∷ ([∗ map] key ↦ s ∈ grand_child_keys', key [[ γ.(γ_children) ]]↦ s) ∗
      "%Hdom_eq'" ∷ ⌜ dom pure_pod_map' = dom grand_child_keys' ⌝ ∗
      "%Hactive_map_eq'" ∷ ⌜ active_pure_pod_map' = filter (λ kv, controller.is_pure_pod_active (snd kv)) pure_pod_map' ⌝ ∗
      "%Hpod_number'" ∷ ⌜ size active_pure_pod_map' = Z.to_nat ((sint.Z (slice.len_f pod_l_sl)) - sint.Z i) ⌝ ∗
      "%Hin'" ∷ ⌜ ∀ pure_pod, pure_pod ∈ (drop (sint.nat i) active_pure_pods) →
                                active_pure_pod_map' !! (PurePod.key pure_pod) = Some pure_pod ⌝ ∗
      "%Hmap_sub" ∷ ⌜ ∀ pure_pod, pure_pod ∈ (drop (sint.nat i) active_pure_pods) →
                                    pure_pod_map' !! (PurePod.key pure_pod) = Some pure_pod →
                                      pure_pod_map !! (PurePod.key pure_pod) = Some pure_pod ⌝ ∗
      "%Hi" :: ⌜0 ≤ sint.Z i ≤ sint.Z (slice.len_f (slice.slice_f pod_l_sl ptrT (W64 0) (word.sub (slice.len_f pod_l_sl) (W64 (sint.Z n)))))⌝
    )%I.
    iAssert (I) with "[i pod Hghostown_pods Hghostown_children Hghostown_grandchildren]" as "Hloop_inv". {
    iExists (W64 0), (default_val loc), pure_pod_map, (filter (λ kv : KKey.t * PurePod.t, is_pure_pod_active kv.2) pure_pod_map), grand_child_keys.
    iFrame. iPureIntro. split_and!. all: try done. word. }
    wp_for "Hloop_inv". wp_if_destruct.
    + wp_pure; [rewrite /slice.slice_f /=;word|].
      set sliced_ptrs := (subslice (sint.nat (W64 0)) (sint.nat (word.sub (slice.len_f pod_l_sl) (W64 (sint.Z n)))) ptrs).
      list_elem sliced_ptrs (sint.Z i) as this_ptr.
      { rewrite Hslice_len1 /slice.slice_f /=. word. }
      wp_apply (wp_load_slice_elem with "[$Hslice]"); [word|eauto|].
      iIntros "Hslice". wp_auto.
      assert (ptrs !! sint.nat i = Some this_ptr) as Hlookup_ptrs.
      { eapply lookup_take_Some in Hthis_ptr_lookup. intuition. }
      assert (∃ active_pod, active_pods !! sint.nat i = Some active_pod) as [active_pod Hlookup_active_pods].
      { apply lookup_lt_is_Some_2. rewrite <-Hlen1. word. }
      iDestruct (big_sepL2_lookup_acc with "Hptrs") as "[Hthis_ptr Hother_ptrs]".
      { apply Hlookup_ptrs. }
      { apply Hlookup_active_pods. }
      iDestruct (struct_fields_split with "Hthis_ptr") as "Hthis_ptr". iNamedPrefix "Hthis_ptr" "Hpod_". wp_auto.
      wp_apply wp_globals_get.
      assert (∃ active_pure_pod, active_pure_pods !! sint.nat i = Some active_pure_pod) as [active_pure_pod Hlookup_active_pure_pods].
      { apply lookup_lt_is_Some_2. rewrite <-Hlen2. word. }
      iDestruct (big_sepL2_lookup_acc with "Hdeepown_pods") as "[Hdeepown_this_pod Hdeepown_other_pods]".
      { apply Hlookup_active_pods. }
      { apply Hlookup_active_pure_pods. }
      assert (active_pure_pod ∈ drop (sint.nat i) active_pure_pods) as Hin_drop.
      { apply (list_elem_of_lookup_2 _ 0). rewrite lookup_drop. rewrite Nat.add_0_r. done. }
      set k := PurePod.key active_pure_pod.
      assert (filter (λ kv : KKey.t * PurePod.t, is_pure_pod_active kv.2) pure_pod_map' !! k = Some active_pure_pod)
      as Hin_filtered_pure_pod_map'.
      { apply Hin'. done. }
      assert (pure_pod_map' !! k = Some active_pure_pod) as Hin_pure_pod_map'.
      { apply map_lookup_filter_Some in Hin_filtered_pure_pod_map'. intuition. }
      assert (pure_pod_map !! k = Some active_pure_pod) as Hin_pure_pod_map.
      { apply Hmap_sub; [done|done]. }
      iDestruct (big_sepM_delete _ pure_pod_map' k _ Hin_pure_pod_map' with "Hghostown_pods") as "[Hghostown_this_pod Hghostown_other_pods]".
      assert (∃ s, grand_child_keys' !! k = Some s) as [s Hin_grand_child_keys'].
      { assert (k ∈ dom grand_child_keys') as Hin_dom.
        { rewrite -Hdom_eq'. apply elem_of_dom. eauto. }
        apply elem_of_dom in Hin_dom. done. }
      iDestruct (big_sepM_delete _ grand_child_keys' k _ Hin_grand_child_keys' with "Hghostown_grandchildren")
      as "[Hghostown_this_grandchildren Hghostown_other_grandchildren]".
      iAssert(⌜ k = mk_pod_key (v1.ObjectMeta.Namespace' (v1.ReplicaSet.ObjectMeta' rs)) (v1.ObjectMeta.Name' (v1.Pod.ObjectMeta' active_pod)) ⌝%I) as "%Hk_eq".
      { iNamedPrefix "Hdeepown_this_pod" "Hpod_". iNamedPrefix "Hpod_Hdeepown_objectmeta" "Hpod_". rewrite Hpod_Hdeepown_name.
        iNamedPrefix "Hrs_Hdeepown_objectmeta" "Hrs_".
        iPureIntro.
        rewrite Hrs_Hdeepown_namespace. rewrite Hrs_key_namespace_eq.
        assert(KKey.Namespace' rs_key = PureObjectMeta.Namespace' (PurePod.ObjectMeta' active_pure_pod)) as ->.
        { symmetry. rewrite -(Hpods_ns_eq k).
          - apply elem_of_dom. done.
          - done. }
        done.
      }
      wp_apply (wp_State__PodDelete _ _ _ _ k active_pure_pod with "[$Hghostown_this_pod $Hghostown_children $Hghostown_this_grandchildren]").
      { iFrame "#". iPureIntro. split; [done|]. apply elem_of_dom. done. }
      iIntros (updated_pure_pod) "H". iNamed "H". wp_auto.
      rewrite bool_decide_true //. wp_auto.
      iApply wp_for_post_do. wp_auto.
      iAssert (I) with "[Hi_ptr Hpod_ptr Hghostown_other_pods Hghostown_other_grandchildren Hpod_updated_or_deleted]" as "loop_inv".
      { iDestruct "Hpod_updated_or_deleted" as "[Hpod_updated | Hown_child_keys]".
        - iNamed "Hpod_updated".
          iExists (word.add i (W64 1)), this_ptr, (<[k := updated_pure_pod]> pure_pod_map'), (filter (λ kv : KKey.t * PurePod.t, is_pure_pod_active kv.2) (<[k := updated_pure_pod]> pure_pod_map')), grand_child_keys'.
          iFrame.
          iDestruct (big_sepM_insert _ (delete k pure_pod_map') k updated_pure_pod with "[$Hghostown_other_pods $Hown_pod]") as "Hghostown_pods".
          { apply lookup_delete_eq. }
          iDestruct (big_sepM_insert _ (delete k grand_child_keys') k s with "[$Hghostown_other_grandchildren $Hown_grandchild_keys]") as "Hghostown_grand_children".
          { apply lookup_delete_eq. }
          assert (<[k:=updated_pure_pod]> (delete k pure_pod_map') = <[k:=updated_pure_pod]> pure_pod_map') as ->.
          { apply insert_delete_eq. }
          assert (<[k:=s]> (delete k grand_child_keys') = grand_child_keys') as ->.
          { rewrite insert_delete_id; done. }
          assert (dom (<[k:=updated_pure_pod]> pure_pod_map') = dom pure_pod_map') as ->.
          { rewrite dom_insert_lookup_L; done. }
          iFrame. iPureIntro.
          assert (is_pure_pod_active active_pure_pod) as Hactive.
          { apply map_lookup_filter_Some in Hin_filtered_pure_pod_map' as [_ Hactive]. done. }
          assert (¬ is_pure_pod_active updated_pure_pod) as Hinactive.
          { unfold is_pure_pod_active. simpl. intro H. destruct H as (_ & _ & H). done. }
          assert(filter (λ kv : KKey.t * PurePod.t, is_pure_pod_active kv.2) pure_pod_map !! k = Some active_pure_pod)
          as Hin_filtered_pure_pod_map.
          { apply map_lookup_filter_Some in Hin_filtered_pure_pod_map' as [Hlookup_k Hactive'].
            apply map_lookup_filter_Some. split; [eapply Hmap_sub; eauto | done]. }
          split_and!. all: try done.
          + rewrite map_filter_insert. simpl.
            destruct (decide (is_pure_pod_active updated_pure_pod)); [done|].
            rewrite map_filter_delete.
            rewrite map_size_delete_Some.
            * done.
            * rewrite Hpod_number'. word.
          + intros pure_pod Hin_drop_next.
            apply list_elem_of_lookup_1 in Hin_drop_next as [j Hlookup_j].
            rewrite lookup_drop in Hlookup_j.
            assert (pure_pod ∈ drop (sint.nat i) active_pure_pods) as Hin_drop_i.
            { replace (sint.nat (word.add i (W64 1))) with (S (sint.nat i)) in Hlookup_j by word.
              apply (list_elem_of_lookup_2 _ (S j)).
              rewrite lookup_drop.
              replace (S j + sint.nat i) with (j + S (sint.nat i)) by lia.
              assert ((S (sint.nat i) + j)%nat = (sint.nat i + S j)%nat) as <- by lia.
              done. }
            apply Hin' in Hin_drop_i as Hlookup_k0.
            assert (sint.nat i ≠ (sint.nat (word.add i (W64 1)) + j)%nat) as Hi_neq.
            { word. }
            assert (k ≠ PurePod.key pure_pod) as Hk_neq.
            { apply (Hno_dup (sint.nat i) (sint.nat (word.add i (W64 1)) + j)%nat); [done|done|done]. }
            rewrite map_filter_insert. simpl.
            destruct (decide (is_pure_pod_active updated_pure_pod)); [done|].
            rewrite map_filter_delete. rewrite lookup_delete_ne; done.
          + intros pure_pod Hin_drop_next Hin_inserted_map'.
            apply list_elem_of_lookup_1 in Hin_drop_next as [j Hlookup_j].
            rewrite lookup_drop in Hlookup_j.
            assert (pure_pod ∈ drop (sint.nat i) active_pure_pods) as Hin_drop_i.
            { replace (sint.nat (word.add i (W64 1))) with (S (sint.nat i)) in Hlookup_j by word.
              apply (list_elem_of_lookup_2 _ (S j)).
              rewrite lookup_drop.
              replace (S j + sint.nat i) with (j + S (sint.nat i)) by lia.
              assert ((S (sint.nat i) + j)%nat = (sint.nat i + S j)%nat) as <- by lia.
              done. }
            apply (Hmap_sub _ Hin_drop_i).
            assert (sint.nat i ≠ (sint.nat (word.add i (W64 1)) + j)%nat) as Hi_neq.
            { word. }
            assert (k ≠ PurePod.key pure_pod) as Hk_neq.
            { apply (Hno_dup (sint.nat i) (sint.nat (word.add i (W64 1)) + j)%nat); [done|done|done]. }
            rewrite lookup_insert_ne in Hin_inserted_map'; done.
          + word.
          + rewrite /slice.slice_f /=. word.
        - iExists (word.add i (W64 1)), this_ptr, (delete k pure_pod_map'), (filter (λ kv : KKey.t * PurePod.t, is_pure_pod_active kv.2) (delete k pure_pod_map')), (delete k grand_child_keys').
          assert (dom pure_pod_map' ∖ {[k]} = dom (delete k pure_pod_map')) as ->.
          { rewrite dom_delete_L. done. }
          iFrame. iPureIntro. split_and!. all: try done.
          + rewrite !dom_delete_L. rewrite Hdom_eq'. done.
          + rewrite map_filter_delete.
            rewrite map_size_delete_Some.
            * done.
            * rewrite Hpod_number'. word.
          + intros pure_pod Hin_drop_next.
            apply list_elem_of_lookup_1 in Hin_drop_next as [j Hlookup_j].
            rewrite lookup_drop in Hlookup_j.
            assert (pure_pod ∈ drop (sint.nat i) active_pure_pods) as Hin_drop_i.
            { replace (sint.nat (word.add i (W64 1))) with (S (sint.nat i)) in Hlookup_j by word.
              apply (list_elem_of_lookup_2 _ (S j)).
              rewrite lookup_drop.
              replace (S j + sint.nat i) with (j + S (sint.nat i)) by lia.
              assert ((S (sint.nat i) + j)%nat = (sint.nat i + S j)%nat) as <- by lia.
              done. }
            apply Hin' in Hin_drop_i as Hlookup_k0.
            assert (sint.nat i ≠ (sint.nat (word.add i (W64 1)) + j)%nat) as Hi_neq.
            { word. }
            assert (k ≠ PurePod.key pure_pod) as Hk_neq.
            { apply (Hno_dup (sint.nat i) (sint.nat (word.add i (W64 1)) + j)%nat); [done|done|done]. }
            rewrite map_filter_delete. rewrite lookup_delete_ne; done.
          + intros pure_pod Hin_drop_next Hin_inserted_map'.
            apply list_elem_of_lookup_1 in Hin_drop_next as [j Hlookup_j].
            rewrite lookup_drop in Hlookup_j.
            assert (pure_pod ∈ drop (sint.nat i) active_pure_pods) as Hin_drop_i.
            { replace (sint.nat (word.add i (W64 1))) with (S (sint.nat i)) in Hlookup_j by word.
              apply (list_elem_of_lookup_2 _ (S j)).
              rewrite lookup_drop.
              replace (S j + sint.nat i) with (j + S (sint.nat i)) by lia.
              assert ((S (sint.nat i) + j)%nat = (sint.nat i + S j)%nat) as <- by lia.
              done. }
            apply (Hmap_sub _ Hin_drop_i).
            assert (sint.nat i ≠ (sint.nat (word.add i (W64 1)) + j)%nat) as Hi_neq.
            { word. }
            assert (k ≠ PurePod.key pure_pod) as Hk_neq.
            { apply (Hno_dup (sint.nat i) (sint.nat (word.add i (W64 1)) + j)%nat); [done|done|done]. }
            rewrite lookup_delete_ne in Hin_inserted_map'; done.
          + word.
          + rewrite /slice.slice_f /=. word.
      }
      iFrame.
      iCombineNamed "Hpod_*" as "H".
      iAssert ((this_ptr ↦{dq1} active_pod)%I) with "[H]" as "Hthis_ptr".
      { iNamed "H". iApply (struct_fields_combine (V:=v1.Pod.t)). iFrame. }
      iSplitL "Hthis_ptr Hother_ptrs".
      * iApply "Hother_ptrs". done.
      * iApply "Hdeepown_other_pods". done.
    + iApply "HΦ". iFrame. iPureIntro. split. all: try done.
      rewrite Hpod_number'. rewrite /slice.slice_f /= in Hi. word.
Admitted.

Lemma wp_FilterActivePods l ptrs pods pure_pods dq:
  {{{ is_pkg_init simplereplicaset ∗
      "Hl" ∷ l ↦* ptrs ∗
      "Hptrs" ∷ ([∗ list] ptr;pod ∈ ptrs;pods, ptr ↦{dq} pod) ∗
      "Hpods" ∷ ([∗ list] pod;pure_pod ∈ pods;pure_pods, PurePod.deepown pod pure_pod dq)
  }}}
  @! simplereplicaset.FilterActivePods #l
  {{{ l' ptrs' pods' pure_pods', RET #l';
      l' ↦* ptrs' ∗
      ([∗ list] ptr;pod ∈ ptrs';pods', ptr ↦{dq} pod) ∗
      ([∗ list] pod;pure_pod ∈ pods';pure_pods', PurePod.deepown pod pure_pod dq) ∗
      ⌜ pods' = filter (λ v, controller.is_pod_active v) pods ⌝ ∗
      ⌜ pure_pods' = filter (λ v, controller.is_pure_pod_active v) pure_pods ⌝
  }}}.
Proof.
  wp_start as "H". iNamed "H". wp_auto.
  iPoseProof own_slice_nil as "Hslice_nil".
  iPoseProof own_slice_cap_nil as "Hown_slice_nil_cap".
  iDestruct (own_slice_len with "Hl") as %(Hl_len1 & Hl_len2).
  iDestruct (own_slice_wf with "Hl") as %Hl_cap.
  iDestruct (big_sepL2_length with "Hptrs") as %Hlen.
  iDestruct (big_sepL2_length with "Hpods") as %Hlen'.
  iAssert ((∃ (i: w64) (p: loc) (result: slice.t) (ptrs': list loc) pods' pure_pods',
      "Hi_ptr" ∷ i_ptr ↦ i ∗
      "Hp_ptr" ∷ p_ptr ↦ p ∗
      "Hresult_ptr" :: result_ptr ↦ result ∗
      "Hresult" ∷ result ↦* ptrs' ∗
      "Hptrs_before_i" ∷ ([∗ list] ptr;pod ∈ ptrs';pods', ptr ↦{dq} pod) ∗
      "Hptrs_after_i" ∷ ([∗ list] ptr;pod ∈ (drop (sint.nat i) ptrs);(drop (sint.nat i) pods), ptr ↦{dq} pod) ∗
      "Hpods_before_i" ∷ ([∗ list] pod;pure_pod ∈ pods';pure_pods', PurePod.deepown pod pure_pod dq) ∗
      "Hpods_after_i" ∷ ([∗ list] pod;pure_pod ∈ (drop (sint.nat i) pods);(drop (sint.nat i) pure_pods), PurePod.deepown pod pure_pod dq) ∗
      "Hown_result_cap" :: own_slice_cap loc result (DfracOwn 1) ∗
      "%Hi" :: ⌜0 ≤ sint.Z i ≤ sint.Z (slice.len_f l)⌝ ∗
      "%Hpods'_eq" ∷ ⌜ pods' = filter (λ v, controller.is_pod_active v) (take (sint.nat i) pods) ⌝ ∗
      "%Hpure_pods'_eq" ∷ ⌜ pure_pods' = filter (λ v, controller.is_pure_pod_active v) (take (sint.nat i) pure_pods) ⌝
  )%I) with "[i result p Hptrs Hpods]" as "Hloop_inv". {
    iExists (W64 0), (default_val loc), slice.nil, [], [], [].
    iFrame. iFrame "#".
    rewrite !take_0 !filter_nil !big_sepL2_nil. done. }
  wp_for "Hloop_inv".
  wp_if_destruct.
  - wp_pure; first word.
    list_elem ptrs (sint.Z i) as this_ptr.
    wp_apply (wp_load_slice_elem with "[$Hl]"); [word|eauto| ]. iIntros "Hl". wp_auto.
    assert (∃ this_pod, pods !! sint.nat i = Some this_pod) as [this_pod Hthis_pod_lookup].
    { apply lookup_lt_is_Some_2. rewrite -Hlen Hl_len1. word. }
    assert (∃ this_pure_pod, pure_pods !! sint.nat i = Some this_pure_pod) as [this_pure_pod Hthis_pure_pod_lookup].
    { apply lookup_lt_is_Some_2. rewrite -Hlen' -Hlen Hl_len1. word. }
    iPoseProof (big_sepL2_destruct_cons _ _ _ this_ptr this_pod with "Hptrs_after_i") as "[Hthis Hother]".
    { split. all: rewrite lookup_drop Nat.add_0_r; done. }
    iPoseProof (big_sepL2_destruct_cons _ _ _ this_pod this_pure_pod with "Hpods_after_i") as "[Hthis_pod Hother_pods]".
    { split. all: rewrite lookup_drop Nat.add_0_r; done. }
    iDestruct (controller.deepown_preserves_activeness with "Hthis_pod") as %Hactive.
    wp_apply (controller.wp_IsPodActive with "[$Hthis]").
    iIntros "Hthis".
    destruct (bool_decide (is_pod_active this_pod)) eqn:Hpod_active_decide. all: wp_auto.
    + assert (is_pod_active this_pod) as Hpod_active.
      { rewrite bool_decide_eq_true in Hpod_active_decide. done. }
      assert (is_pure_pod_active this_pure_pod) as Hpure_active.
      { apply Hactive. done. }
      wp_apply wp_slice_literal. iIntros (sl) "Hsl". wp_auto.
      wp_apply (wp_slice_append with "[$Hresult $Hown_result_cap $Hsl]"). iIntros (result') "(Hresult & Hown_result_cap & Hsl)". wp_auto.
      iApply wp_for_post_do. wp_auto.
      iFrame "Hl HΦ pods".
      iExists (word.add i (W64 1)), this_ptr, result', (ptrs' ++ [this_ptr]),
        ((filter (λ v, controller.is_pod_active v) (take (sint.nat (word.add i (W64 1))) pods))),
        ((filter (λ v, controller.is_pure_pod_active v) (take (sint.nat (word.add i (W64 1))) pure_pods))).
      assert (filter (λ v, is_pod_active v) (take (sint.nat i) pods) ++ [this_pod] =
              filter (λ v, is_pod_active v) (take (sint.nat (word.add i (W64 1))) pods)) as <-.
      { assert (sint.nat (word.add i (W64 1)) = S (sint.nat i)) as -> by word.
        rewrite (take_S_r _ _ this_pod); [done|].
        rewrite list.filter_app filter_singleton_True; [done|done|done]. }
      assert (filter (λ v, is_pure_pod_active v) (take (sint.nat i) pure_pods) ++ [this_pure_pod] =
              filter (λ v, is_pure_pod_active v) (take (sint.nat (word.add i (W64 1))) pure_pods)) as <-.
      { assert (sint.nat (word.add i (W64 1)) = S (sint.nat i)) as -> by word.
        rewrite (take_S_r _ _ this_pure_pod); [done|].
        rewrite list.filter_app filter_singleton_True; [done|done|done]. }
      assert (sint.nat (word.add i (W64 1)) = S (sint.nat i)) as -> by word. rewrite !drop_drop Nat.add_1_r.
      iFrame.
      iSplitR; [done|]. iSplitR; [done|]. iPureIntro. split; [word|done].
    + assert (¬ is_pod_active this_pod) as Hpod_active.
      { rewrite bool_decide_eq_false in Hpod_active_decide. done. }
      assert (¬ is_pure_pod_active this_pure_pod) as Hpure_active.
      { intros H. apply Hactive in H. done. }
      iApply wp_for_post_do. wp_auto. iFrame "Hl HΦ pods".
      iExists (word.add i (W64 1)), this_ptr, result, ptrs',
        ((filter (λ v, controller.is_pod_active v) (take (sint.nat (word.add i (W64 1))) pods))),
        ((filter (λ v, controller.is_pure_pod_active v) (take (sint.nat (word.add i (W64 1))) pure_pods))).
      assert (filter (λ v, is_pod_active v) (take (sint.nat i) pods) =
              filter (λ v, is_pod_active v) (take (sint.nat (word.add i (W64 1))) pods)) as <-.
      { assert (sint.nat (word.add i (W64 1)) = S (sint.nat i)) as -> by word.
        rewrite (take_S_r _ _ this_pod); [done|].
        rewrite list.filter_app filter_singleton_False; [done|done|rewrite app_nil_r; done]. }
      assert (filter (λ v, is_pure_pod_active v) (take (sint.nat i) pure_pods) =
              filter (λ v, is_pure_pod_active v) (take (sint.nat (word.add i (W64 1))) pure_pods)) as <-.
      { assert (sint.nat (word.add i (W64 1)) = S (sint.nat i)) as -> by word.
        rewrite (take_S_r _ _ this_pure_pod); [done|].
        rewrite list.filter_app filter_singleton_False; [done|done|rewrite app_nil_r; done]. }
      assert (sint.nat (word.add i (W64 1)) = S (sint.nat i)) as -> by word. rewrite !drop_drop Nat.add_1_r.
      iFrame. iPureIntro. split; [word|done].
  - iApply "HΦ". iFrame "Hresult Hptrs_before_i Hpods_before_i".
    iPureIntro. split.
    + assert (sint.nat i = length pods) as -> by word. rewrite take_ge; [lia|]. done.
    + assert (sint.nat i = length pure_pods) as -> by word. rewrite take_ge; [lia|]. done.
Qed.

Lemma wp_FilterPodsByOwner γ l owner owner_kind metadata pure_metadata dq
  parent_key owned_parent owned_pod_map owned_child_keys:
  {{{ is_pkg_init simplereplicaset ∗
      "#Hisk" ∷ is_kubernetes γ l ∗
      "#Hglobal" ∷ (global_addr simplereplicaset.state)↦□l ∗
      "Howner" ∷ owner ↦{dq} metadata ∗
      "Hdeepown_meta" ∷ PureObjectMeta.deepown metadata pure_metadata dq ∗
      "%Howner_kind_eq" ∷ ⌜ owner_kind = parent_key.(KKey.Kind') ⌝ ∗
      "%Hnamespace_eq" ∷ ⌜ pure_metadata.(PureObjectMeta.Namespace') = parent_key.(KKey.Namespace') ⌝ ∗
      "%Hname_eq" ∷ ⌜ pure_metadata.(PureObjectMeta.Name') = parent_key.(KKey.Name') ⌝ ∗
      "%Howner_kind_nonempty" ∷ ⌜ owner_kind ≠ ""%go ⌝ ∗
      "Hown_parent" ∷ parent_key [[ γ.(γ_state) ]]↦ owned_parent ∗
      "Hown_pods" ∷ ([∗ map] key ↦ pod ∈ owned_pod_map, key [[ γ.(γ_state) ]]↦ PureKObject.Pod pod) ∗
      "Hown_child_keys" ∷ parent_key [[ γ.(γ_children) ]]↦ owned_child_keys ∗
      "%Howned_child_keys_equal_dom_owned_pods" ∷ ⌜ owned_child_keys = dom owned_pod_map ⌝ ∗
      "%Hindexed_value" ∷ ⌜ pure_metadata = (PureKObject.metadata owned_parent) ⌝ ∗
      "%Hmeta_wellformed" ∷ ⌜ PureObjectMeta.well_formed pure_metadata ⌝
  }}}
  @! simplereplicaset.FilterPodsByOwner #owner #owner_kind
  {{{ (ptr_slice: slice.t) (ptrs: list loc) (pods: list v1.Pod.t) (pure_pods: list PurePod.t) dq', RET (#ptr_slice, #interface.nil);
      ptr_slice ↦* ptrs ∗
      ([∗ list] ptr;pod ∈ ptrs;pods, ptr ↦{dq'} pod) ∗
      ([∗ list] pod;pure_pod ∈ pods;pure_pods, PurePod.deepown pod pure_pod dq') ∗
      ⌜ ∀ pure_pod, pure_pod ∈ pure_pods → PurePod.well_formed pure_pod ⌝ ∗
      ⌜ length pure_pods = size owned_pod_map ⌝ ∗
      ⌜ ∀ p, p ∈ pure_pods → owned_pod_map !! (PurePod.key p) = Some p ⌝ ∗
      ⌜ ∀ k p, owned_pod_map !! k = Some p → p ∈ pure_pods ⌝ ∗
      ⌜ ∀ key p, owned_pod_map !! key = Some p → key = PurePod.key p ⌝ ∗
      ⌜ ∀ key, key ∈ dom owned_pod_map → key.(KKey.Namespace') = parent_key.(KKey.Namespace') ⌝ ∗
      ⌜ ∀ i j p1 p2, i ≠ j → pure_pods !! i = Some p1 → pure_pods !! j = Some p2 → (PurePod.key p1) ≠ (PurePod.key p2) ⌝ ∗
      owner ↦{dq} metadata ∗
      PureObjectMeta.deepown metadata pure_metadata dq ∗
      parent_key [[ γ.(γ_state) ]]↦ owned_parent ∗
      ([∗ map] key ↦ pod ∈ owned_pod_map, key [[ γ.(γ_state) ]]↦ PureKObject.Pod pod) ∗
      parent_key [[ γ.(γ_children) ]]↦ owned_child_keys
  }}}.
Proof.
  wp_start as "H". iNamed "H". subst. wp_auto.
  wp_alloc owner_reference as "Howner_reference". wp_auto.
  wp_apply (controller.wp_PodControllerIndexKey with "[$Howner_reference]").
  iIntros (index_key) "%Hindex_key_eq". wp_auto.
  wp_apply wp_globals_get.
  iNamedPrefix "Hdeepown_meta" "Htemp_".
  wp_apply (wp_State__ByIndex_pod with "[$Hown_parent $Hown_pods $Hown_child_keys]").
  { iFrame "#". iPureIntro. unfold controller.PodControllerIndex. rewrite <-Hnamespace_eq. rewrite <-Hname_eq.
    rewrite Hindex_key_eq. rewrite Htemp_Hdeepown_namespace. rewrite Htemp_Hdeepown_name. rewrite Htemp_Hdeepown_uid. done. }
  iCombineNamed "Htemp_*" as "H".
  iAssert (PureObjectMeta.deepown metadata (PureKObject.metadata owned_parent) dq) with "[H]" as "Hdeepown_meta".
  { iNamed "H". iFrame. done. }
  iIntros (objs_l ptrs pods pure_pods dq') "H".
  set objs := map (λ ptr : loc, interface.mk (ptrT.id v1.Pod.id) (# ptr)) ptrs.
  iNamed "H". wp_auto. rewrite bool_decide_true //. wp_auto.
  iPoseProof own_slice_nil as "Hslice_nil".
  iPoseProof own_slice_cap_nil as "Hown_slice_nil_cap".
  iDestruct (own_slice_len with "Hobjs_l") as %(Hobjs_l_len1 & Hobjs_l_len2).
  iDestruct (own_slice_wf with "Hobjs_l") as %Hobjs_l_cap.
  iDestruct (big_sepL2_length with "Hptrs_pods") as %Hlen.
  iAssert ((∃ (i: w64) (result: slice.t) (v: interface.t),
      "Hi_ptr" ∷ i_ptr ↦ i ∗
      "Hresult_ptr" ∷ result_ptr ↦ result ∗
      "Hresult" ∷ result ↦* take (sint.nat i) ptrs ∗
      "Hobj" ∷ obj_ptr ↦ v ∗
      "Hown_result_cap" ∷ own_slice_cap loc result (DfracOwn 1) ∗
      "%Hi" ∷ ⌜0 ≤ sint.Z i ≤ sint.Z (slice.len_f objs_l)⌝
  )%I) with "[i result obj]" as "Hloop_inv". {
    iExists (W64 0), slice.nil, (default_val interface.t).
    iFrame. iFrame "#". iPureIntro. word. }
  wp_for "Hloop_inv".
  wp_if_destruct.
  - wp_pure; first word.
    list_elem objs (sint.Z i) as this_obj.
    wp_apply (wp_load_slice_elem with "[$Hobjs_l]"); [word|eauto| ].
    iIntros "Hobjs_l". wp_auto.
    assert (∃ this_ptr, ptrs !! sint.nat i = Some this_ptr) as [this_ptr Hthis_ptr].
    { apply lookup_lt_is_Some_2.
      assert (length objs = length ptrs) as Hlen_eq.
      { subst objs. apply map_length. }
      rewrite -Hlen_eq Hobjs_l_len1.
      word. }
    assert (this_obj = interface.mk (ptrT.id v1.Pod.id) (# this_ptr)) as ->.
    { subst objs.
      rewrite list_lookup_fmap in Hthis_obj_lookup.
      rewrite Hthis_ptr in Hthis_obj_lookup.
      simpl in Hthis_obj_lookup.
      congruence. }
    unshelve wp_apply wp_interface_checked_type_assert; try tc_solve.
    { iPureIntro. intros ptr_id. exists this_ptr. done. }
    iIntros (y ok) "%if_ok".
    assert (ok = true) as ->.
    { destruct ok; [done|]. intuition. }
    inversion if_ok. apply (inj to_val) in H0. subst y.
    wp_auto.
    wp_apply wp_slice_literal. iIntros (sl) "Hsl". wp_auto.
    wp_apply (wp_slice_append with "[$Hresult $Hown_result_cap $Hsl]").
    iIntros (result') "(Hresult & Hown_result_cap & Hsl)". wp_auto.
    iApply wp_for_post_do. wp_auto.
    iFrame "Howner HΦ err pods ownerKind owner key Hdeepown_meta Hobjs_l Hptrs_pods Hpods_purepods Hown_pod_list Hown_child_keys Hown_parent".
    iExists (word.add i (W64 1)), result', (interface.mk (ptrT.id v1.Pod.id) (# this_ptr)).
    iFrame.
    iSplitL;[|iPureIntro;word].
    assert (sint.nat (word.add i (W64 1)) = S (sint.nat i)) as -> by word.
    assert (take (S (sint.nat i)) ptrs = take (sint.nat i) ptrs ++ [this_ptr]) as ->.
    { apply take_S_r. done. }
    iFrame.
  - iApply "HΦ". iFrame.
    assert (take (sint.nat i) ptrs = ptrs) as ->.
    { assert (sint.nat i = length objs) as -> by word.
      assert (length objs = length ptrs) as ->.
      { subst objs. apply map_length. }
      apply take_ge. lia. }
    iFrame. iPureIntro. done.
Qed.

Lemma wp_syncReplicaSet γ l (gv: schema.GroupVersion.t) namespace name
  rs_key pure_rs pure_pod_map grand_child_key_map (n: w32):
  {{{ is_pkg_init simplereplicaset ∗
      "#Hisk" ∷ is_kubernetes γ l ∗
      "#Hglobal_l" ∷ (global_addr simplereplicaset.state)↦□l ∗
      "#Hglobal_gv" ∷ (global_addr v1.SchemeGroupVersion) ↦□ gv ∗
      "%rs_key_eq" ∷ ⌜ rs_key = mk_replicaset_key namespace name ⌝ ∗
      "Hghostown_rs" ∷ rs_key [[ γ.(γ_state) ]]↦ PureKObject.ReplicaSet pure_rs ∗
      "Hghostown_pods" ∷ ([∗ map] key ↦ v ∈ pure_pod_map, key [[ γ.(γ_state) ]]↦ PureKObject.Pod v) ∗
      "Hghostown_children" ∷ rs_key [[ γ.(γ_children) ]]↦ dom pure_pod_map ∗
      "Hghostown_grandchildren" ∷ ([∗ map] key ↦ s ∈ grand_child_key_map, key [[ γ.(γ_children) ]]↦ s) ∗
      "%Hpure_rs_name_short" ∷ ⌜ length pure_rs.(PureReplicaSet.ObjectMeta').(PureObjectMeta.Name') < 58 ⌝ ∗
      "%Hdom_eq" ∷ ⌜ dom pure_pod_map = dom grand_child_key_map ⌝ ∗
      "%Hts_non" ∷ ⌜ pure_rs.(PureReplicaSet.ObjectMeta').(PureObjectMeta.DeletionTimestamp') = None ⌝ ∗
      "%Hreplicas_eq" ∷ ⌜ pure_rs.(PureReplicaSet.Spec').(PureReplicaSetSpec.Replicas') = Some n ⌝
  }}}
  @! simplereplicaset.syncReplicaSet #namespace #name
  {{{ (pure_pod_map': gmap KKey.t PurePod.t) grand_child_key_map', RET #interface.nil;
      rs_key [[ γ.(γ_state) ]]↦ PureKObject.ReplicaSet pure_rs ∗
      ([∗ map] key ↦ v ∈ pure_pod_map', key [[ γ.(γ_state) ]]↦ PureKObject.Pod v) ∗
      rs_key [[ γ.(γ_children) ]]↦ dom pure_pod_map' ∗
      ([∗ map] key ↦ s ∈ grand_child_key_map', key [[ γ.(γ_children) ]]↦ s) ∗
      ⌜ dom pure_pod_map' = dom grand_child_key_map' ⌝ ∗
      ⌜ size (filter (λ kv, controller.is_pure_pod_active (snd kv)) pure_pod_map') = sint.nat n ⌝
  }}}.
Proof.
  wp_start as "H". iNamed "H". wp_auto. subst rs_key. wp_apply wp_globals_get.
  wp_apply (wp_State__ReplicaSetGet with "[$Hghostown_rs]"); [iFrame "#"; done|].
  iIntros (ptr rs dq) "(Hdeepown_l_rs & %Hwell_formed_rs & %Hnamespace_eq & %Hname_eq & Hghostown_rs)". wp_auto.
  wp_apply errors.wp_IsNotFound_nil; [done|]. rewrite bool_decide_true //. wp_auto.
  iDestruct "Hdeepown_l_rs" as "[Hptr Hdeepown_rs]". iNamed "Hdeepown_rs".
  iDestruct (struct_fields_split with "Hptr") as "Hptr". iNamed "Hptr".
  wp_apply (wp_FilterPodsByOwner with "[$Hghostown_rs $Hghostown_pods $Hghostown_children $HObjectMeta $Hdeepown_objectmeta]").
  { iFrame "#". iPureIntro. split_and!. all: try done. destruct Hwell_formed_rs as (H & _). done. }
  iIntros (ptr_slice ptrs pods pure_pods dq') "(Hptr_slice & Hptrs & Hpods & %Hwell_formed_pods & %Hlen_size_eq &
    %Hlist_in_map & %Hmap_in_list & %Hkey_eq & %Hns_eq & %Hno_dup & HObjectMeta & Hdeepown_objectmeta & Hghostown_rs &
    Hghostown_pods & Hghostown_children)". wp_auto.
  rewrite bool_decide_true //. wp_auto.
  wp_apply (wp_FilterActivePods with "[$Hptr_slice $Hptrs $Hpods]").
  iIntros (acitve_ptr_slice active_ptrs active_pods active_pure_pods) "(Hptr_slice & Hactive_ptrs & Hactive_pods &
    %Hactive_pods_eq & %Hactive_pure_pods_eq)". wp_auto.
  iAssert(⌜ rs.(v1.ReplicaSet.ObjectMeta').(v1.ObjectMeta.DeletionTimestamp') = null ⌝%I) as "->".
  { iNamed "Hdeepown_objectmeta". iPureIntro. apply Hdeepown_deletiontimestamp_none. done. }
  rewrite bool_decide_true //. wp_auto.
  iAssert ((ptr ↦{dq} rs)%I) with "[HTypeMeta HObjectMeta HSpec HStatus]" as "Hptr".
  { iApply (struct_fields_combine (V:=v1.ReplicaSet.t)). iFrame. }
  iAssert (PureReplicaSet.deepown rs pure_rs dq %I) with "[Hdeepown_objectmeta Hdeepown_spec Hdeepown_status]"
    as "Hdeepown_rs".
  { iFrame. iPureIntro. done. }
  iAssert (⌜ length active_pure_pods = sint.nat (slice.len_f acitve_ptr_slice) ⌝%I) as "%Hlen_acitve_ptr_slice".
  { iDestruct (own_slice_len with "Hptr_slice") as %(Hl_len1 & Hl_len2).
    iDestruct (big_sepL2_length with "Hactive_ptrs") as %Hlen3.
    iDestruct (big_sepL2_length with "Hactive_pods") as %Hlen4.
    iPureIntro. congruence. }
  wp_apply (wp_manageReplicas with "[$Hptr_slice $Hactive_ptrs $Hactive_pods $Hptr $Hdeepown_rs $Hghostown_rs
    $Hghostown_pods $Hghostown_children $Hghostown_grandchildren]").
  { iFrame "#". iPureIntro. split_and!. all: try done.
    - rewrite Hactive_pure_pods_eq.
      pose proof (filter_list_map_size_eq PurePod.key (λ v, is_pure_pod_active v) pure_pods pure_pod_map).
      apply H. all: try done.
    - intros pure_pod Hpure_pod_in.
      rewrite Hactive_pure_pods_eq in Hpure_pod_in.
      apply list_elem_of_filter in Hpure_pod_in as [Hactive Hpure_pod_in_pure_pods].
      apply Hlist_in_map in Hpure_pod_in_pure_pods as Hk_lookup.
      apply map_lookup_filter_Some_2; [done|]. done.
    - rewrite Hactive_pure_pods_eq.
      apply (filter_preserves_key_uniqueness PurePod.key (λ v, is_pure_pod_active v)).
      done. }
  iIntros (pure_pod_map' grand_child_key_map') "(Hghostown_rs & Hghostown_pods & Hghostown_children &
    Hghostown_grandchildren & %Hdom_eq' & %Hdesired)". wp_auto.
  iApply "HΦ". iFrame. done.
Qed.

End proof.
