From New.proof Require Import prelude empty_ffi.
From New.proof.kubernetes_model Require Export get index create delete.
From New.proof Require Export util.
From New.proof.controllers Require Export common.
From New.proof.controllers Require Export replicaset_init.
From New.proof.k8s_io.kubernetes.pkg Require Export controller.
From New.proof.k8s_io.apimachinery.pkg.runtime Require Export schema.
From New.proof.k8s_io.apimachinery.pkg.api Require Export errors.

Section proof.
Context `{hG: !heapGS Σ} {go_ctx: GoContext}.
Context `{!kviewG Σ}.
Context `{!cviewG Σ}.
Context `{!tombstoneG Σ}.

Definition current_state_matches rs pods : Prop :=
  match rs.(ReplicaSetV.Spec').(ReplicaSetSpecV.Replicas') with
  | Some replicas => length (filter is_pod_alive pods) = sint.nat replicas
  | None => False
  end.

Lemma list_to_set_app_singleton_kkey (x : KKey.t) (l1 l2 l3 : list KKey.t) :
  list_to_set (C:=gset KKey.t) (l1 ++ ((l2 ++ [x]) ++ l3)) =
  list_to_set (C:=gset KKey.t) ((x :: l1) ++ l2 ++ l3).
Proof.
  apply set_eq. intros k.
  rewrite !elem_of_list_to_set.
  rewrite !elem_of_app !list_elem_of_singleton !elem_of_cons.
  split.
  - intros [Hl1 | [[Hl2 | Hx] | Hl3]].
    + left. right. exact Hl1.
    + right. left. exact Hl2.
    + subst k. left. left. done.
    + right. right. exact Hl3.
  - intros [[Hx | Hl1] | [Hl2 | Hl3]].
    + subst k. right. left. right. done.
    + left. exact Hl1.
    + right. left. left. exact Hl2.
    + right. right. exact Hl3.
Qed.

Lemma list_to_set_cons_difference_kkey (x : KKey.t) (l : list KKey.t) :
  x ∉ l →
  list_to_set (C:=gset KKey.t) l =
  list_to_set (C:=gset KKey.t) (x :: l) ∖ {[x]}.
Proof.
  intros Hnotin.
  apply set_eq. intros k.
  rewrite elem_of_difference !elem_of_list_to_set elem_of_singleton elem_of_cons.
  split.
  - intros Hk. split.
    + right. exact Hk.
    + intros ->. exact (Hnotin Hk).
  - intros [[-> | Hk] Hneq].
    + exfalso. apply Hneq. done.
    + exact Hk.
Qed.

Lemma pod_key_not_in_delete_remainder
    active_pods inactive_pods inactive_pods' this_pod i :
  NoDup (PodV.key <$> (active_pods ++ inactive_pods)) →
  active_pods !! i = Some this_pod →
  (∀ key, key ∈ PodV.key <$> inactive_pods' → key ∈ PodV.key <$> take i active_pods) →
  PodV.key this_pod ∉
    PodV.key <$> (drop (S i) active_pods ++ inactive_pods' ++ inactive_pods).
Proof.
  intros Hnodup Hlookup Hincluded Hcontra.
  rewrite !fmap_app !elem_of_app in Hcontra.
  assert ((active_pods ++ inactive_pods) !! i = Some this_pod) as Hlookup_this.
  { apply lookup_app_l_Some. exact Hlookup. }
  assert ((PodV.key <$> (active_pods ++ inactive_pods)) !! i = Some (PodV.key this_pod))
    as Hlookup_key_this.
  { rewrite list_lookup_fmap Hlookup_this. done. }
  destruct Hcontra as [Hdrop | [Hinactive' | Hinactive]].
  - apply list_elem_of_lookup_1 in Hdrop as (j & Hlookup_drop_key).
    rewrite list_lookup_fmap in Hlookup_drop_key.
    destruct (drop (S i) active_pods !! j) as [pod_j|] eqn:Hlookup_drop; simpl in Hlookup_drop_key; [|done].
    assert ((active_pods ++ inactive_pods) !! (S i + j)%nat = Some pod_j) as Hlookup_j.
    { apply lookup_app_l_Some. rewrite lookup_drop in Hlookup_drop. exact Hlookup_drop. }
    assert ((PodV.key <$> (active_pods ++ inactive_pods)) !! (S i + j)%nat = Some (PodV.key this_pod))
      as Hlookup_key_j.
    { rewrite list_lookup_fmap Hlookup_j. exact Hlookup_drop_key. }
    pose proof (NoDup_lookup _ _ _ _ Hnodup Hlookup_key_this Hlookup_key_j) as Heq.
    lia.
  - pose proof (Hincluded _ Hinactive') as Hkey_take.
    apply list_elem_of_lookup_1 in Hkey_take as (j & Hlookup_take_key).
    rewrite list_lookup_fmap in Hlookup_take_key.
    destruct (take i active_pods !! j) as [pod_j|] eqn:Hlookup_take; simpl in Hlookup_take_key; [|done].
    apply lookup_take_Some in Hlookup_take as (Hlookup_active_j & Hj_lt).
    assert ((active_pods ++ inactive_pods) !! j = Some pod_j) as Hlookup_j.
    { apply lookup_app_l_Some. exact Hlookup_active_j. }
    assert ((PodV.key <$> (active_pods ++ inactive_pods)) !! j = Some (PodV.key this_pod))
      as Hlookup_key_j.
    { rewrite list_lookup_fmap Hlookup_j. exact Hlookup_take_key. }
    pose proof (NoDup_lookup _ _ _ _ Hnodup Hlookup_key_this Hlookup_key_j) as Heq.
    lia.
  - apply list_elem_of_lookup_1 in Hinactive as (j & Hlookup_inactive_key).
    rewrite list_lookup_fmap in Hlookup_inactive_key.
    destruct (inactive_pods !! j) as [pod_j|] eqn:Hlookup_inactive; simpl in Hlookup_inactive_key; [|done].
    assert ((active_pods ++ inactive_pods) !! (length active_pods + j)%nat = Some pod_j) as Hlookup_j.
    { rewrite lookup_app.
      assert (active_pods !! (length active_pods + j)%nat = None) as Hactive_none.
      { apply lookup_ge_None_2. apply Nat.le_add_r. }
      rewrite Hactive_none.
      replace (length active_pods + j - length active_pods)%nat with j by lia.
      exact Hlookup_inactive. }
    assert ((PodV.key <$> (active_pods ++ inactive_pods)) !! (length active_pods + j)%nat =
        Some (PodV.key this_pod)) as Hlookup_key_j.
    { rewrite list_lookup_fmap Hlookup_j. exact Hlookup_inactive_key. }
    pose proof (NoDup_lookup _ _ _ _ Hnodup Hlookup_key_this Hlookup_key_j) as Heq.
    apply lookup_lt_Some in Hlookup.
    lia.
Qed.

Lemma list_to_set_pod_key_filter_partition pods :
  list_to_set (C:=gset KKey.t)
    (PodV.key <$> (filter is_pod_alive pods ++ filter (λ pod, not (is_pod_alive pod)) pods)) =
  list_to_set (C:=gset KKey.t) (PodV.key <$> pods).
Proof.
  apply set_eq. intros key.
  rewrite fmap_app !elem_of_list_to_set elem_of_app !list_elem_of_fmap.
  split.
  - intros [(pod & -> & Hin)|(pod & -> & Hin)].
    + apply list_elem_of_filter in Hin as [_ Hin].
      exists pod. split; done.
    + apply list_elem_of_filter in Hin as [_ Hin].
      exists pod. split; done.
  - intros (pod & -> & Hin).
    destruct (decide (is_pod_alive pod)) as [Halive|Hnot_alive].
    + left. exists pod. split; [done|apply list_elem_of_filter; split; done].
    + right. exists pod. split; [done|apply list_elem_of_filter; split; done].
Qed.

Lemma pod_key_filter_partition_perm pods :
  PodV.key <$> (filter is_pod_alive pods ++ filter (λ pod, not (is_pod_alive pod)) pods) ≡ₚ
  PodV.key <$> pods.
Proof.
  apply Permutation_map.
  apply filter_partition_perm.
Qed.

Lemma pod_key_meta_perm pods1 pods2 :
  PodV.ObjectMeta' <$> pods1 ≡ₚ PodV.ObjectMeta' <$> pods2 →
  PodV.key <$> pods1 ≡ₚ PodV.key <$> pods2.
Proof.
  intros Hperm.
  unfold PodV.key.
  rewrite (list_fmap_compose PodV.ObjectMeta' PodV.meta_key pods1).
  rewrite (list_fmap_compose PodV.ObjectMeta' PodV.meta_key pods2).
  apply Permutation_map. exact Hperm.
Qed.

Lemma wp_manageReplicas γ l (gv: schema.GroupVersion.t) sl rs_l ptrs active_pods inactive_pods rs n dq1 dq2 :
  {{{ is_pkg_init code.controllers.replicaset.replicaset ∗
      "#Hisk" ∷ is_kubernetes γ l ∗
      "#Hglobal_l" ∷ (global_addr common.State) ↦□ l ∗
      "#Hglobal_gv" ∷ (global_addr v1.SchemeGroupVersion) ↦□ gv ∗
      "Hsl" ∷ sl ↦* ptrs ∗
      "Hdeepown_l_active_pods" ∷ ([∗ list] ptr;pod ∈ ptrs;active_pods, PodV.deepown_l ptr pod dq1) ∗
      "Hdeepown_l_rs" ∷ ReplicaSetV.deepown_l rs_l rs dq2 ∗
      "Hown_active_pod_meta_frags" ∷ ([∗ list] pod ∈ active_pods,
        own_meta_frag γ (PodV.key pod) pod.(PodV.ObjectMeta').(ObjectMetaV.UID') 1 pod.(PodV.ObjectMeta')) ∗
      "Hown_children_frag" ∷ own_children_frag γ (ReplicaSetV.key rs)
        rs.(ReplicaSetV.ObjectMeta').(ObjectMetaV.UID') 1 (list_to_set (PodV.key <$> (active_pods ++ inactive_pods))) ∗
      "%Hrs_meta_valid" ∷ ⌜ ObjectMetaV.valid rs.(ReplicaSetV.ObjectMeta') ⌝ ∗
      "%Hrs_spec_valid" ∷ ⌜ ReplicaSetSpecV.valid rs.(ReplicaSetV.Spec') ⌝ ∗
      "%Hactive_pods" ∷ ⌜ ∀ pod, pod ∈ active_pods → is_pod_alive pod ⌝ ∗
      "%Hrs_name_short" ∷ ⌜ length rs.(ReplicaSetV.ObjectMeta').(ObjectMetaV.Name') < 58 ⌝ ∗
      "%Hreplicas_eq" ∷ ⌜ rs.(ReplicaSetV.Spec').(ReplicaSetSpecV.Replicas') = Some n ⌝ ∗
      "%Hnodup" ∷ ⌜ NoDup (PodV.key <$> (active_pods ++ inactive_pods)) ⌝
  }}}
    @! replicaset.manageReplicas #sl #rs_l
  {{{ pods', RET #interface.nil;
      ⌜ length (filter is_pod_alive pods') = sint.nat n ⌝ ∗
      sl ↦* ptrs ∗
      ([∗ list] ptr;pod ∈ ptrs;active_pods, PodV.deepown_l ptr pod dq1) ∗
      ReplicaSetV.deepown_l rs_l rs dq2 ∗
      ([∗ list] pod ∈ pods',
        own_meta_frag γ (PodV.key pod) pod.(PodV.ObjectMeta').(ObjectMetaV.UID') 1 pod.(PodV.ObjectMeta')) ∗
      own_children_frag γ (ReplicaSetV.key rs)
        rs.(ReplicaSetV.ObjectMeta').(ObjectMetaV.UID') 1 (list_to_set (PodV.key <$> (pods' ++ inactive_pods)))
  }}}.
Proof.
  wp_start as "H". iNamed "H". wp_auto.
  iPoseProof (ReplicaSetV.deepown_l_split with "Hdeepown_l_rs") as
    "(Hdeepown_t_l_rs & Hdeepown_m_l_rs & Hdeepown_s_l_rs & Hdeepown_st_l_rs)".
  iDestruct "Hdeepown_s_l_rs" as "(%rs_spec_c & Hrs_spec_l & Hdeepown_rs_spec)".
  iNamedPrefix "Hdeepown_rs_spec" "Hrs_".
  iAssert ((rs_spec_c.(v1.ReplicaSetSpec.Replicas') ↦{dq2} n)%I) with "[Hrs_Hdeepown_replicas_some]"
    as "Hrs_Hdeepown_replicas".
  { rewrite Hreplicas_eq. iDestruct "Hrs_Hdeepown_replicas_some" as "(%replicas & Hreplicas & ->)". done. }
  wp_auto.
  iDestruct (own_slice_len with "Hsl") as %(Hsl_len1 & Hsl_len2).
  iDestruct (own_slice_wf with "Hsl") as %Hsl_cap.
  iDestruct (big_sepL2_length with "Hdeepown_l_active_pods") as %Hlen.
  assert (0 ≤ sint.Z n) as Hn.
  { pose proof (ReplicaSetSpecV.valid_replicas _ Hrs_spec_valid) as (i & Hi_eq & Hi).
    rewrite Hi_eq in Hreplicas_eq. congruence. }
  assert ((sint.Z (word.sub (slice.len_f sl) (W64 (sint.Z n)))) = (sint.Z (slice.len_f sl)) - (sint.Z n)) as -> by word.
  assert ((sint.Z (W64 0)) = 0) as -> by word.
  wp_if_destruct.
  - set I := (∃ (i: w64) (active_pods': list PodV.t),
      "Hi_ptr" ∷ i_ptr ↦ i ∗
      "Hown_pod_meta_frags" ∷ ([∗ list] pod ∈ active_pods',
        own_meta_frag γ (PodV.key pod) pod.(PodV.ObjectMeta').(ObjectMetaV.UID') 1 pod.(PodV.ObjectMeta')) ∗
      "Hown_children_frag" ∷ own_children_frag γ (ReplicaSetV.key rs) rs.(ReplicaSetV.ObjectMeta').(ObjectMetaV.UID') 1
        (list_to_set (PodV.key <$> (active_pods' ++ inactive_pods))) ∗
      "%Hlen_active_pods'" ∷ ⌜ length active_pods' = Z.to_nat ((sint.Z (slice.len_f sl)) + sint.Z i) ⌝ ∗
      "%Hall_active" ∷ ⌜ ∀ pod, pod ∈ active_pods' → is_pod_alive pod ⌝ ∗
      "%Hi" ∷ ⌜ 0 ≤ sint.Z i ≤ sint.Z (word.mul (word.sub (slice.len_f sl) (W64 (sint.Z n))) (W64 (-1))) ⌝
    )%I.
    iAssert (I) with "[i Hown_active_pod_meta_frags Hown_children_frag]" as "Hloop_inv".
    { iExists (W64 0), active_pods. iFrame. iPureIntro. split_and!. all: try word. done. }
    wp_for "Hloop_inv". wp_if_destruct.
    + wp_apply wp_globals_get. wp_apply schema.wp_GroupVersion__WithKind.
      { (* TODO: why? *) iAssert (is_pkg_init code.k8s_io.api.apps.v1.v1) as "H". all: iPkgInit. }
      iIntros (gvk) "%Hgvk". wp_auto.
      destruct Hgvk as (Hgvk_g & Hgvk_v & Hgvk_k).
      wp_apply (v1.wp_NewControllerRef_ReplicaSet with "[$Hdeepown_m_l_rs]"); [done|].
      iIntros (controller_ref_l controller_ref) "(Hdeepown_l_controller_ref & %Hcontroller_ref_valid &
        Hdeepown_m_l_rs)". wp_auto. rewrite Hgvk_k in Hcontroller_ref_valid.
      iDestruct (struct_fields_split with "Hrs_spec_l") as "H". iNamedPrefix "H" "Hrs_".
      wp_apply (controller.wp_GetPodFromTemplate_ReplicaSet with "[$Hrs_HTemplate $Hrs_Hdeepown_template
        $Hdeepown_m_l_rs $Hdeepown_l_controller_ref]").
      { pose proof (ReplicaSetSpecV.valid_template _ Hrs_spec_valid) as Hrs_valid_template.
        iPureIntro. split_and!. all: try done. }
      iIntros (pod_l pod) "(Hdeepown_l_pod & %Hpr & %Hvalid & Hrs_HTemplate & Hrs_Hdeepown_template & Hdeepown_m_l_rs)".
      wp_auto. rewrite bool_decide_true //. wp_auto.
      wp_apply (v1.wp_GetNamespace_deepown with "[$Hdeepown_m_l_rs]") as "Hdeepown_m_l_rs".
      wp_apply wp_globals_get.
      wp_apply (wp_State__PodCreate_nameless with "[$Hdeepown_l_pod $Hown_children_frag]").
      { iFrame "#". iSplit.
        - iAssert (is_pkg_init code.controllers.common.common) as "H". all: iPkgInit.
        - iPureIntro. split_and!. all: try done.
          + apply ObjectMetaV.valid_namespace_nonempty_of_valid. exact Hrs_meta_valid.
          + apply ObjectMetaV.valid_namespace_of_valid. exact Hrs_meta_valid.
      }
      iIntros (pod_l' pod' key uid) "H". iNamedPrefix "H" "Hcreate_". subst key. subst uid. wp_auto.
      rewrite bool_decide_true //. wp_auto.
      iApply wp_for_post_do. wp_auto.
      iAssert (I) with "[Hi_ptr Hown_pod_meta_frags Hcreate_Hown_meta Hcreate_Hown_children]" as "loop_inv".
      { iExists (word.add i (W64 1)), (active_pods' ++ [pod']). iFrame "Hi_ptr".
        iSplitL "Hown_pod_meta_frags Hcreate_Hown_meta".
        - rewrite big_sepL_app. simpl. iFrame.
        - iSplitL "Hcreate_Hown_children".
            + assert (list_to_set (PodV.key <$> (active_pods' ++ inactive_pods)) ∪ {[PodV.key pod']} =
                list_to_set (PodV.key <$> ((active_pods' ++ [pod']) ++ inactive_pods)))
                as ->.
              { rewrite !fmap_app. simpl. Timeout 5 set_solver. }
              done.
            + iSplit.
              { iPureIntro. rewrite length_app /= Hlen_active_pods'.
                word. }
              iSplit.
              { iPureIntro. intros pod0 Hpod0.
                apply elem_of_app in Hpod0 as [Hpod0|Hpod0].
                - apply Hall_active. done.
                - rewrite list_elem_of_singleton in Hpod0. subst pod0.
                  unfold is_pod_alive.
                  unfold ObjectMetaV.nameless_created in Hcreate_Hmeta_created.
	                  Timeout 5 naive_solver. }
              { iPureIntro. word. }
      }
      iFrame. iApply (struct_fields_combine (V:=v1.ReplicaSetSpec.t)). iFrame.
    + iApply "HΦ". iFrame.
      iSplitR.
      { iPureIntro.
        rewrite (filter_all is_pod_alive active_pods' Hall_active) Hlen_active_pods'. word. }
      iApply ReplicaSetV.deepown_l_restore. iFrame.
      iSplitR. 1: done. iSplitL. 2: done.
      rewrite Hreplicas_eq. iExists n. iSplitL. all: done.
  - wp_if_destruct.
    2 : { iApply "HΦ". iFrame.
      iSplit.
      { iPureIntro.
        rewrite (filter_all is_pod_alive active_pods Hactive_pods).
        rewrite -Hlen Hsl_len1. word. }
      iApply ReplicaSetV.deepown_l_restore. iFrame.
      iSplitR. 1: done. iSplitL. 2: done.
      rewrite Hreplicas_eq. iExists n. iSplitL. all: done. }
    wp_apply wp_slice_slice_pure; [iPureIntro;word|].
    iDestruct (own_slice_f 0 (word.sub (slice.len_f sl) (W64 (sint.Z n))) with "Hsl")
      as "(Hbefore_slice & Hslice & Hafter_slice )"; [word|].
    iDestruct (own_slice_len with "Hslice") as %(Hslice_len1 & Hslice_len2).
    set I := (∃ (i: w64) (pod_l: loc) (inactive_pods': list PodV.t),
      "Hi_ptr" ∷ i_ptr ↦ i ∗
      "Hpod_ptr" ∷ pod_ptr ↦ pod_l ∗
      "Hown_active_pod_meta_frags" ∷ ([∗ list] pod ∈ drop (sint.nat i) active_pods,
        own_meta_frag γ (PodV.key pod) pod.(PodV.ObjectMeta').(ObjectMetaV.UID') 1 pod.(PodV.ObjectMeta')) ∗
      "Hown_inactive_pod_meta_frags" ∷ ([∗ list] pod ∈ inactive_pods',
        own_meta_frag γ (PodV.key pod) pod.(PodV.ObjectMeta').(ObjectMetaV.UID') 1 pod.(PodV.ObjectMeta')) ∗
      "Hown_children_frag" ∷ own_children_frag γ (ReplicaSetV.key rs) rs.(ReplicaSetV.ObjectMeta').(ObjectMetaV.UID') 1
        (list_to_set (PodV.key <$> ((drop (sint.nat i) active_pods) ++ inactive_pods' ++ inactive_pods))) ∗
      "%Hinactive" ∷ ⌜ ∀ pod, pod ∈ inactive_pods' → ¬ is_pod_alive pod ⌝ ∗
      "%Hincluded" ∷ ⌜ ∀ key, key ∈ PodV.key <$> inactive_pods' → key ∈ PodV.key <$> take (sint.nat i) active_pods ⌝ ∗
      "%Hi" ∷ ⌜ 0 ≤ sint.Z i ≤ sint.Z (slice.len_f (slice.slice_f sl ptrT (W64 0) (word.sub (slice.len_f sl) (W64 (sint.Z n))))) ⌝
    )%I.
    iAssert (I) with "[i pod Hown_active_pod_meta_frags Hown_children_frag]" as "Hloop_inv".
    { iExists (W64 0), (default_val loc), [].
      rewrite drop_0 big_sepL_nil.
      iFrame.
      iPureIntro. split.
      - intros pod0 Hpod0. inversion Hpod0.
      - split.
        + intros key Hkey. inversion Hkey.
        + word.
	    }
	    wp_for "Hloop_inv". wp_if_destruct.
	    + wp_pure; [rewrite /slice.slice_f /=;word|].
	      set sliced_ptrs := (subslice (sint.nat (W64 0)) (sint.nat (word.sub (slice.len_f sl) (W64 (sint.Z n)))) ptrs).
	      list_elem sliced_ptrs (sint.Z i) as this_ptr.
      { rewrite Hslice_len1 /slice.slice_f /=. word. }
      wp_apply (wp_load_slice_elem with "[$Hslice]"); [word|eauto|].
      iIntros "Hslice". wp_auto.
      assert (ptrs !! sint.nat i = Some this_ptr) as Hlookup_ptrs.
      { eapply lookup_take_Some in Hthis_ptr_lookup. intuition. }
      assert (∃ this_pod, active_pods !! sint.nat i = Some this_pod) as [this_pod Hlookup_active_pods].
      { apply lookup_lt_is_Some_2. rewrite <-Hlen. word. }
      iDestruct (big_sepL2_lookup_acc with "Hdeepown_l_active_pods") as "[Hdeepown_l_this Hdeepown_l_others]".
      { apply Hlookup_ptrs. }
      { apply Hlookup_active_pods. }
      iPoseProof (PodV.deepown_l_split with "Hdeepown_l_this") as
        "(Hdeepown_t_l_pod & Hdeepown_m_l_pod & Hdeepown_s_l_pod & Hdeepown_st_l_pod)".
      wp_apply (v1.wp_GetUID_deepown with "[$Hdeepown_m_l_pod]"). iIntros "Hdeepown_m_l_pod". wp_auto.
      wp_apply (v1.wp_GetNamespace_deepown with "[$Hdeepown_m_l_pod]"). iIntros "Hdeepown_m_l_pod". wp_auto.
      wp_apply (v1.wp_GetName_deepown with "[$Hdeepown_m_l_pod]"). iIntros "Hdeepown_m_l_pod". wp_auto.
      wp_apply (common.wp_NewDeleteOptionsWithUID). iIntros (do_c) "(Hdeepown_do & %Hvalid_do)". wp_auto.
      wp_apply wp_globals_get.
      assert (drop (sint.nat i) active_pods = this_pod :: drop (S (sint.nat i)) active_pods)
        as Hdrop_active_pods.
      { apply drop_S. exact Hlookup_active_pods. }
      iEval (rewrite Hdrop_active_pods) in "Hown_active_pod_meta_frags".
      iDestruct "Hown_active_pod_meta_frags" as
        "[Hown_pod_meta_frag_this Hown_active_pod_meta_frags_tail]".
      wp_apply (wp_State__PodDelete_matching_pre with "[$Hdeepown_do $Hown_pod_meta_frag_this $Hown_children_frag]").
      { iFrame "#". iSplit.
        - iAssert (is_pkg_init code.controllers.common.common) as "H". all: iPkgInit.
        - iPureIntro. split_and!. all: try done.
          rewrite elem_of_list_to_set.
          apply list_elem_of_fmap_2.
          rewrite elem_of_app. left.
          rewrite Hdrop_active_pods. left. }
      iIntros (kmeta') "H". wp_auto.
      rewrite bool_decide_true //. wp_auto.
      iApply wp_for_post_do. wp_auto.
      iDestruct "H" as "[H | H]".
      * iNamedPrefix "H" "Hdelete_".
        iAssert (I) with "[Hi_ptr Hpod_ptr Hdelete_Hown_meta_frag Hdelete_Hown_children_frag
          Hown_active_pod_meta_frags_tail Hown_inactive_pod_meta_frags]" as "loop_inv".
	        { iExists (word.add i (W64 1)), this_ptr, (inactive_pods' ++ [this_pod <|PodV.ObjectMeta':=kmeta'|>]).
	          iPoseProof (kview.own_meta_valid with "Hdelete_Hown_meta_frag") as "%Hmeta_valid".
	          destruct Hmeta_valid as (Hname_eq & Hnamespace_eq & Huid_eq & _).
	          assert (PodV.key (this_pod <| PodV.ObjectMeta' := kmeta' |>) = PodV.key this_pod) as Hkey_eq.
	          { rewrite /PodV.key /PodV.meta_key /=.
	            rewrite -Hnamespace_eq -Hname_eq.
	            done. }
	          assert (sint.nat (word.add i (W64 1)) = S (sint.nat i)) as Hsucc by word.
            rewrite Hsucc.
	          iFrame "Hi_ptr Hpod_ptr".
            iSplitL "Hown_active_pod_meta_frags_tail".
            { iFrame. }
            iSplitL "Hown_inactive_pod_meta_frags Hdelete_Hown_meta_frag".
            { rewrite big_sepL_app big_sepL_singleton Hkey_eq -Huid_eq. iFrame. }
	          iSplitL "Hdelete_Hown_children_frag".
	          { assert (list_to_set (C:=gset KKey.t) (PodV.key <$>
                  (drop (S (sint.nat i)) active_pods ++
                    ((inactive_pods' ++ [this_pod <| PodV.ObjectMeta' := kmeta' |>]) ++ inactive_pods))) =
	              list_to_set (C:=gset KKey.t) (PodV.key <$>
                  (drop (sint.nat i) active_pods ++ inactive_pods' ++ inactive_pods))) as Hchildren_eq.
	            { rewrite Hdrop_active_pods !fmap_app /= Hkey_eq.
	              apply list_to_set_app_singleton_kkey. }
	            rewrite Hchildren_eq. iFrame. }
		        iPureIntro. split.
            - intros pod0 Hpod0.
              apply elem_of_app in Hpod0 as [Hpod0|Hpod0].
              + apply Hinactive. done.
              + rewrite list_elem_of_singleton in Hpod0. subst pod0.
                unfold is_pod_alive. simpl. exact Hdelete_Hdeletion_timestamp.
            - split.
              + intros key Hkey.
                rewrite fmap_app in Hkey.
                apply elem_of_app in Hkey as [Hkey|Hkey].
                * rewrite (take_S_r active_pods (sint.nat i) this_pod Hlookup_active_pods).
                  rewrite fmap_app. apply elem_of_app. left.
                  apply Hincluded. done.
                * simpl in Hkey. rewrite list_elem_of_singleton in Hkey. subst key.
                  rewrite Hkey_eq.
                  rewrite (take_S_r active_pods (sint.nat i) this_pod Hlookup_active_pods).
                  rewrite fmap_app. apply elem_of_app. right.
                  simpl. left.
              + rewrite /slice.slice_f /=. word.
	        }
	        iFrame. iApply "Hdeepown_l_others".
	        iApply PodV.deepown_l_restore. iFrame.
	      * iNamedPrefix "H" "Hdelete_".
	        iAssert (I) with "[Hi_ptr Hpod_ptr Hdelete_Hown_children_frag
	          Hown_active_pod_meta_frags_tail Hown_inactive_pod_meta_frags]" as "loop_inv".
	        { iExists (word.add i (W64 1)), this_ptr, inactive_pods'.
	          assert (sint.nat (word.add i (W64 1)) = S (sint.nat i)) as Hsucc by word.
	          rewrite Hsucc.
	          iFrame "Hi_ptr Hpod_ptr Hown_active_pod_meta_frags_tail Hown_inactive_pod_meta_frags".
	          iSplitL "Hdelete_Hown_children_frag".
	          { assert (list_to_set (C:=gset KKey.t) (PodV.key <$>
                  (drop (S (sint.nat i)) active_pods ++ inactive_pods' ++ inactive_pods)) =
	              list_to_set (C:=gset KKey.t) (PodV.key <$>
                  (drop (sint.nat i) active_pods ++ inactive_pods' ++ inactive_pods)) ∖
                    {[PodV.key this_pod]}) as Hchildren_eq.
		            { rewrite Hdrop_active_pods !fmap_app /=.
		              apply list_to_set_cons_difference_kkey.
		              rewrite -!fmap_app.
		              apply (pod_key_not_in_delete_remainder active_pods inactive_pods inactive_pods'
		                this_pod (sint.nat i)); done. }
	            rewrite Hchildren_eq. iFrame. }
	          iPureIntro. split.
	          - exact Hinactive.
	          - split.
	            + intros key Hkey.
	              rewrite (take_S_r active_pods (sint.nat i) this_pod Hlookup_active_pods).
	              rewrite fmap_app. apply elem_of_app. left.
		              apply Hincluded. done.
		            + rewrite /slice.slice_f /=. word. }
	        iFrame. iApply "Hdeepown_l_others".
	        iApply PodV.deepown_l_restore. iFrame.
	      + iPoseProof (own_slice_f (W64 0) (word.sub (slice.len_f sl) (W64 (sint.Z n))) sl
	          with "[$Hbefore_slice $Hslice $Hafter_slice]") as "Hsl".
	        { word. }
	        iAssert (([∗ list] pod ∈ drop (sint.nat i) active_pods ++ inactive_pods',
	          own_meta_frag γ (PodV.key pod) pod.(PodV.ObjectMeta').(ObjectMetaV.UID') 1
	            pod.(PodV.ObjectMeta')))%I
	          with "[Hown_active_pod_meta_frags Hown_inactive_pod_meta_frags]" as "Hown_pod_meta_frags_ret".
	        { rewrite big_sepL_app. iFrame. }
	        iAssert (own_children_frag γ (ReplicaSetV.key rs)
	          rs.(ReplicaSetV.ObjectMeta').(ObjectMetaV.UID') 1
	          (list_to_set (PodV.key <$> ((drop (sint.nat i) active_pods ++ inactive_pods') ++ inactive_pods))))%I
	          with "[Hown_children_frag]" as "Hown_children_frag_ret".
	        { rewrite app_assoc. iFrame. }
	        iApply "HΦ".
	        iFrame "Hsl Hdeepown_l_active_pods Hown_pod_meta_frags_ret Hown_children_frag_ret".
	        iSplitR.
	        { iPureIntro.
	          rewrite list.filter_app.
	          assert (filter is_pod_alive (drop (sint.nat i) active_pods) =
	              drop (sint.nat i) active_pods) as Hfilter_active.
	          { apply filter_all. intros pod Hpod.
	            apply Hactive_pods.
	            apply list_elem_of_lookup_1 in Hpod as (j & Hlookup_pod).
	            apply (list_elem_of_lookup_2 active_pods (sint.nat i + j)%nat).
	            rewrite lookup_drop in Hlookup_pod. exact Hlookup_pod. }
	          rewrite Hfilter_active.
	          assert (filter is_pod_alive inactive_pods' = []) as Hfilter_inactive.
	          { apply filter_none. exact Hinactive. }
	          rewrite Hfilter_inactive app_nil_r.
	          assert (sint.Z i = sint.Z (word.sub (slice.len_f sl) (W64 (sint.Z n)))) as Hi_Z.
	          { rewrite /slice.slice_f /= in Hi. word. }
	          assert (sint.nat i = sint.nat (word.sub (slice.len_f sl) (W64 (sint.Z n)))) as Hi_eq by word.
          rewrite length_drop -Hlen Hsl_len1 Hi_eq.
          word. }
		        iApply ReplicaSetV.deepown_l_restore. iFrame.
		      iSplitR. 1: done. iSplitL. 2: done.
		      rewrite Hreplicas_eq. iExists n. iSplitL. all: done.
Qed.

Lemma wp_syncReplicaSet γ l (gv: schema.GroupVersion.t) namespace name rs pods :
  {{{ is_pkg_init code.controllers.replicaset.replicaset ∗
      "#Hisk" ∷ is_kubernetes γ l ∗
      "#Hglobal_l" ∷ (global_addr common.State) ↦□ l ∗
      "#Hglobal_gv" ∷ (global_addr v1.SchemeGroupVersion) ↦□ gv ∗
      "Hown_rs_meta_frag" ∷ own_meta_frag γ (ReplicaSetV.key rs) rs.(ReplicaSetV.ObjectMeta').(ObjectMetaV.UID') 1
        rs.(ReplicaSetV.ObjectMeta') ∗
      "Hown_rs_spec_frag" ∷ own_spec_frag γ (ReplicaSetV.key rs) rs.(ReplicaSetV.ObjectMeta').(ObjectMetaV.UID') 1
        (ObjectSpecV.ReplicaSetSpec rs.(ReplicaSetV.Spec')) ∗
      "Hown_pod_meta_frags" ∷ ([∗ list] k ↦ pod ∈ pods,
        own_meta_frag γ (PodV.key pod) pod.(PodV.ObjectMeta').(ObjectMetaV.UID') 1 pod.(PodV.ObjectMeta')) ∗
      "Hown_children_frag" ∷ own_children_frag γ (ReplicaSetV.key rs) rs.(ReplicaSetV.ObjectMeta').(ObjectMetaV.UID') 1
        (list_to_set (PodV.key <$> pods)) ∗
      "%Hnamespace_eq" ∷ ⌜ namespace = rs.(ReplicaSetV.ObjectMeta').(ObjectMetaV.Namespace') ⌝ ∗
      "%Hname_eq" ∷ ⌜ name = rs.(ReplicaSetV.ObjectMeta').(ObjectMetaV.Name') ⌝ ∗
      "%Hdeletion_timestamp_eq" ∷ ⌜ rs.(ReplicaSetV.ObjectMeta').(ObjectMetaV.DeletionTimestamp') = None ⌝ ∗
      "%Hrs_name_short" ∷ ⌜ length rs.(ReplicaSetV.ObjectMeta').(ObjectMetaV.Name') < 58 ⌝ ∗
      "%Hrs_spec_valid" ∷ ⌜ ReplicaSetSpecV.valid rs.(ReplicaSetV.Spec') ⌝
  }}}
    @! replicaset.syncReplicaSet #namespace #name
  {{{ (pods' : list PodV.t), RET #interface.nil;
      ⌜ current_state_matches rs pods' ⌝ ∗
      own_meta_frag γ (ReplicaSetV.key rs) rs.(ReplicaSetV.ObjectMeta').(ObjectMetaV.UID') 1
        rs.(ReplicaSetV.ObjectMeta') ∗
      own_spec_frag γ (ReplicaSetV.key rs) rs.(ReplicaSetV.ObjectMeta').(ObjectMetaV.UID') 1
        (ObjectSpecV.ReplicaSetSpec rs.(ReplicaSetV.Spec')) ∗
      ([∗ list] pod ∈ pods',
        own_meta_frag γ (PodV.key pod) pod.(PodV.ObjectMeta').(ObjectMetaV.UID') 1 pod.(PodV.ObjectMeta')) ∗
      own_children_frag γ (ReplicaSetV.key rs) rs.(ReplicaSetV.ObjectMeta').(ObjectMetaV.UID') 1
        (list_to_set (PodV.key <$> pods'))
  }}}.
Proof.
  wp_start as "H". iNamed "H". wp_auto.
  wp_apply wp_globals_get.
  iAssert (is_pkg_init code.controllers.common.common) as "#Hcommon_init".
  { iPkgInit. }
  iAssert (is_pkg_init apimodel) as "#Hapimodel".
  { iPkgInit. }
  wp_apply (wp_State__ReplicaSetGet with "[$Hown_rs_meta_frag $Hown_rs_spec_frag]").
  { iFrame "#".
    iPureIntro.
    rewrite /ReplicaSetV.key /ReplicaSetV.meta_key Hnamespace_eq Hname_eq.
    done. }
  iIntros (rs_l rs_get) "Hget". iNamedPrefix "Hget" "Hget_".
  iRename "Hget_Hdeepown_l" into "Hdeepown_l_rs".
  iRename "Hget_Hown_meta_frag" into "Hown_rs_meta_frag".
  iRename "Hget_Hown_spec_frag" into "Hown_rs_spec_frag".
  wp_auto.
  wp_apply (wp_IsNotFound_nil with "[]").
  { done. }
  wp_pures.
  rewrite bool_decide_true //.
  wp_auto.

  iPoseProof (ReplicaSetV.deepown_l_split with "Hdeepown_l_rs") as
    "(Hdeepown_t_l_rs & Hdeepown_m_l_rs & Hdeepown_s_l_rs & Hdeepown_st_l_rs)".
  iPoseProof (kview.own_meta_valid with "Hown_rs_meta_frag") as "%Hrs_meta_frag_valid".
  destruct Hrs_meta_frag_valid as (_ & _ & _ & Hrs_meta_valid).
  assert (ObjectMetaV.valid rs_get.(ReplicaSetV.ObjectMeta')) as Hrs_get_meta_valid.
  { rewrite <-Hget_Hmeta_eq. exact Hrs_meta_valid. }
  destruct Hget_Hvalid' as [Hrs_typemeta_valid _].
  destruct Hrs_typemeta_valid as [_ Hrs_kind_valid].
  pose proof (valid_kind_slash_free _ Hrs_kind_valid) as Hrs_kind_slash_free.
  pose proof (ObjectMetaV.valid_namespace_of_valid _ Hrs_get_meta_valid) as Hrs_namespace_valid.
  pose proof (ObjectMetaV.valid_name_of_valid _ Hrs_get_meta_valid) as Hrs_name_valid.
  pose proof (ObjectMetaV.valid_uid_of_valid _ Hrs_get_meta_valid) as Hrs_uid_valid.
  pose proof (valid_namespace_slash_free _ Hrs_namespace_valid) as Hrs_namespace_slash_free.
  pose proof (valid_name_slash_free _ Hrs_name_valid) as Hrs_name_slash_free.
  pose proof (valid_uid_slash_free _ Hrs_uid_valid) as Hrs_uid_slash_free.
  iPoseProof (kview.own_meta_list_no_dup PodV.key PodV.ObjectMeta' with "Hown_pod_meta_frags") as "%Hpods_nodup".
  assert (list_to_set (C:=gset KKey.t) (PodV.key <$> pods) =
      filter (λ key, key.(KKey.Kind') = "Pod"%go)
        (list_to_set (C:=gset KKey.t) (PodV.key <$> pods))) as Hdom_eq.
  { apply set_eq. intros key.
    rewrite elem_of_filter.
    split.
    - intros Hkey_in. split; [|done].
      apply elem_of_list_to_set in Hkey_in.
      apply list_elem_of_fmap_1 in Hkey_in as (pod & Hkey_eq & _).
      subst key.
      rewrite /PodV.key /PodV.meta_key /PodV.kind //.
    - intros [_ Hkey_in]. done. }
  iEval (rewrite Hget_Hkey_eq Hget_Hmeta_eq) in "Hown_children_frag".
  wp_apply (common.wp_FilterPodsByOwner with
    "[$Hdeepown_m_l_rs $Hown_pod_meta_frags $Hown_children_frag]").
  { iFrame "#".
    iPureIntro. split_and!; try done. }
  iIntros (all_sl all_ptrs all_pods dq) "(Hall_sl & Hall_deepown_pods & %Hall_meta_perm & %Hall_valid & %Hall_nodup &
    Hdeepown_m_l_rs & Hall_meta_frags & Hown_children_frag)".
  wp_auto.
  rewrite bool_decide_true //.
  wp_auto.
  wp_apply (common.wp_FilterActivePods with "[$Hall_sl $Hall_deepown_pods]").
  iIntros (active_sl active_ptrs) "(Hactive_sl & Hactive_deepown_pods)".
  wp_auto.

  iDestruct (big_sepL_filter_partition is_pod_alive
    (λ pod, own_meta_frag γ (PodV.key pod) pod.(PodV.ObjectMeta').(ObjectMetaV.UID') 1
      pod.(PodV.ObjectMeta')) all_pods with "Hall_meta_frags")
    as "[Hactive_meta_frags Hinactive_meta_frags]".
  assert (PodV.key <$> all_pods ≡ₚ PodV.key <$> pods) as Hall_key_perm.
  { apply pod_key_meta_perm. exact Hall_meta_perm. }
  assert (list_to_set (C:=gset KKey.t)
      (PodV.key <$> (filter is_pod_alive all_pods ++ filter (λ pod, not (is_pod_alive pod)) all_pods)) =
    list_to_set (C:=gset KKey.t) (PodV.key <$> pods)) as Hchildren_keys_eq.
  { rewrite list_to_set_pod_key_filter_partition.
    rewrite Hall_key_perm. done. }
  iAssert (own_children_frag γ (ReplicaSetV.key rs_get)
      rs_get.(ReplicaSetV.ObjectMeta').(ObjectMetaV.UID') 1
      (list_to_set (C:=gset KKey.t)
        (PodV.key <$> (filter is_pod_alive all_pods ++ filter (λ pod, not (is_pod_alive pod)) all_pods))))%I
    with "[Hown_children_frag]" as "Hown_children_frag".
  { rewrite Hchildren_keys_eq.
    iExact "Hown_children_frag". }
  iDestruct "Hdeepown_m_l_rs" as (rs_meta_c) "[Hrs_meta_l Hdeepown_m_rs]".
  iNamedPrefix "Hdeepown_m_rs" "Hrs_meta_".
  assert (rs_meta_c.(v1.ObjectMeta.DeletionTimestamp') = null) as Hrs_deletion_timestamp_null.
  { apply Hrs_meta_Hdeepown_deletiontimestamp_none.
    rewrite <-Hget_Hmeta_eq. exact Hdeletion_timestamp_eq. }
  assert (rs_get.(ReplicaSetV.ObjectMeta').(ObjectMetaV.DeletionTimestamp') = None)
    as Hdeletion_timestamp_eq_get.
  { rewrite <-Hget_Hmeta_eq. exact Hdeletion_timestamp_eq. }
  wp_auto.
  rewrite Hrs_deletion_timestamp_null.
  wp_auto.
  iEval (rewrite Hdeletion_timestamp_eq_get) in "Hrs_meta_Hdeepown_deletiontimestamp_some".
  iAssert (ObjectMetaV.deepown rs_meta_c rs_get.(ReplicaSetV.ObjectMeta') 1)
    with "[Hrs_meta_Hdeepown_creationtimestamp
      Hrs_meta_Hdeepown_deletiongraceperiodseconds_some
      Hrs_meta_Hdeepown_labels_some Hrs_meta_Hdeepown_annotations_some
      Hrs_meta_Hdeepown_ownerreferences_some Hrs_meta_Hdeepown_finalizers_some
      Hrs_meta_Hdeepown_managedfields_some]" as "Hdeepown_m_rs".
  { rewrite /ObjectMetaV.deepown Hdeletion_timestamp_eq_get.
    iFrame "%". iFrame. done. }
  iAssert (ObjectMetaV.deepown_l (ReplicaSetV.objectmeta_ptr rs_l) rs_get.(ReplicaSetV.ObjectMeta') 1)
    with "[Hrs_meta_l Hdeepown_m_rs]" as "Hdeepown_m_l_rs".
  { iExists rs_meta_c. iFrame. }
  iPoseProof (ReplicaSetV.deepown_l_restore with
    "[$Hdeepown_t_l_rs $Hdeepown_m_l_rs $Hdeepown_s_l_rs $Hdeepown_st_l_rs]") as
    "Hdeepown_l_rs".

  pose proof (ReplicaSetSpecV.valid_replicas _ Hrs_spec_valid) as (n & Hreplicas_eq & _).
  assert (rs_get.(ReplicaSetV.Spec').(ReplicaSetSpecV.Replicas') = Some n) as Hreplicas_eq_get.
  { rewrite <-Hget_Hspec_eq. exact Hreplicas_eq. }
  assert (ReplicaSetSpecV.valid rs_get.(ReplicaSetV.Spec')) as Hrs_get_spec_valid.
  { rewrite <-Hget_Hspec_eq. exact Hrs_spec_valid. }
  assert (length rs_get.(ReplicaSetV.ObjectMeta').(ObjectMetaV.Name') < 58) as Hrs_get_name_short.
  { rewrite <-Hget_Hmeta_eq. exact Hrs_name_short. }
  assert (NoDup (PodV.key <$>
      (filter is_pod_alive all_pods ++ filter (λ pod, not (is_pod_alive pod)) all_pods))) as Hpartition_nodup.
  { rewrite pod_key_filter_partition_perm. exact Hall_nodup. }
  wp_apply (wp_manageReplicas γ l gv active_sl rs_l active_ptrs
    (filter is_pod_alive all_pods) (filter (λ pod, not (is_pod_alive pod)) all_pods)
    rs_get n dq 1 with
    "[$Hactive_sl $Hactive_deepown_pods $Hdeepown_l_rs $Hactive_meta_frags $Hown_children_frag]").
  { iFrame "#".
    iPureIntro. split_and!; try done.
    intros pod Hpod.
    apply list_elem_of_filter in Hpod as [Halive _].
    exact Halive. }
  iIntros (pods_managed) "(%Hmanaged_len & Hactive_sl & Hactive_deepown_pods & Hdeepown_l_rs &
    Hmanaged_meta_frags & Hown_children_frag)".
  wp_auto.
  iAssert (([∗ list] pod ∈ pods_managed ++ filter (λ pod, not (is_pod_alive pod)) all_pods,
      own_meta_frag γ (PodV.key pod) pod.(PodV.ObjectMeta').(ObjectMetaV.UID') 1
        pod.(PodV.ObjectMeta')))%I
    with "[Hmanaged_meta_frags Hinactive_meta_frags]" as "Hpod_meta_frags_post".
  { rewrite big_sepL_app. iFrame. }
  iEval (rewrite -Hget_Hkey_eq -Hget_Hmeta_eq) in "Hown_children_frag".
  iApply ("HΦ" $! (pods_managed ++ filter (λ pod, not (is_pod_alive pod)) all_pods)).
  iFrame "Hown_rs_meta_frag Hown_rs_spec_frag Hpod_meta_frags_post Hown_children_frag".
  iPureIntro.
  unfold current_state_matches.
  rewrite Hreplicas_eq.
  simpl.
  rewrite list.filter_app.
  assert (filter is_pod_alive (filter (λ pod, not (is_pod_alive pod)) all_pods) = []) as Hfilter_inactive.
  { apply filter_none. intros pod Hpod.
    apply list_elem_of_filter in Hpod as [Hnot_alive _].
    exact Hnot_alive. }
  rewrite Hfilter_inactive app_nil_r.
  exact Hmanaged_len.
Qed.

End proof.
