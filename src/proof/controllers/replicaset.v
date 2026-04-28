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
Context `{!mono_gsetG types.UID.t Σ}.

Definition current_state_matches rs pods : Prop :=
  match rs.(ReplicaSetV.Spec').(ReplicaSetSpecV.Replicas') with
  | Some replicas => length (filter is_pod_alive pods) = sint.nat replicas
  | None => False
  end.

Lemma lookup_filter_ge {A} (P : A → Prop) `{∀ x, Decision (P x)}
    (l : list A) (n : nat) x :
  filter P l !! n = Some x →
  ∃ k : nat, n ≤ k ∧ l !! k = Some x.
Proof.
  revert n.
  induction l as [|y l IH]; intros n Hlookup.
  - destruct n; inversion Hlookup.
  - rewrite filter_cons in Hlookup.
    destruct (decide (P y)) as [Hy|Hy].
    + destruct n as [|n].
      * simpl in Hlookup. inversion Hlookup; subst.
        exists O. split; done.
      * simpl in Hlookup.
        destruct (IH n Hlookup) as (k & Hle & Hk).
        exists (S k). split; [lia|done].
    + destruct (IH n Hlookup) as (k & Hle & Hk).
      exists (S k). split; [lia|done].
Qed.

Lemma lookup_filter_elem_of_drop {A} (P : A → Prop) `{∀ x, Decision (P x)}
    (l : list A) (n : nat) x :
  filter P l !! n = Some x →
  x ∈ drop n l.
Proof.
  intros Hlookup.
  destruct (lookup_filter_ge P l n x Hlookup) as (k & Hle & Hk).
  apply (list_elem_of_lookup_2 (drop n l) (k - n) x).
  rewrite lookup_drop.
  replace (n + (k - n))%nat with k by lia.
  done.
Qed.

Lemma take_drop_middle_slices {A} (l : list A) i x :
  l !! i = Some x →
  take i l = take i (take i l ++ x :: drop (S i) l) ∧
  drop (S i) (take i l ++ x :: drop (S i) l) = drop (S i) l.
Proof.
  intros Hlookup.
  pose proof (lookup_lt_Some _ _ _ Hlookup) as Hlt.
  split.
  - assert ((i <= length (take i l))%nat) as Hlen_take by (rewrite length_take_le; lia).
    rewrite (take_app_le (take i l) (x :: drop (S i) l) i Hlen_take).
    rewrite take_take Nat.min_id. done.
  - replace (S i) with (length (take i l) + 1)%nat by (rewrite length_take_le; lia).
    rewrite drop_app_add. done.
Qed.

Lemma big_sepL_split_lookup {A} (Φ : A → iProp Σ) (l : list A) i x :
  l !! i = Some x →
  ([∗ list] y ∈ l, Φ y) -∗
  ([∗ list] y ∈ take i l, Φ y) ∗ Φ x ∗ ([∗ list] y ∈ drop (S i) l, Φ y).
Proof.
  iIntros (Hlookup) "H".
  destruct (take_drop_middle_slices l i x Hlookup) as [Htake Hdrop].
  rewrite -(take_drop_middle l i x Hlookup) big_sepL_app /=.
  iDestruct "H" as "(Hbefore & Hx & Hafter)".
  iEval (rewrite Htake) in "Hbefore".
  iEval (rewrite -Hdrop) in "Hafter".
  iFrame.
Qed.

Lemma wp_manageReplicas γ l (gv: schema.GroupVersion.t) sl rs_l ptrs pods rs n dq1 dq2 :
  {{{ is_pkg_init code.controllers.replicaset.replicaset ∗
      "#Hisk" ∷ is_kubernetes γ l ∗
      "#Hglobal_l" ∷ (global_addr common.State) ↦□ l ∗
      "#Hglobal_gv" ∷ (global_addr v1.SchemeGroupVersion) ↦□ gv ∗
      "Hsl" ∷ sl ↦* ptrs ∗
      "Hdeepown_l_pods" ∷ ([∗ list] ptr;pod ∈ ptrs;filter is_pod_alive pods, PodV.deepown_l ptr pod dq1) ∗
      "Hdeepown_l_rs" ∷ ReplicaSetV.deepown_l rs_l rs dq2 ∗
      "Hown_pod_meta_frags" ∷ ([∗ list] pod ∈ pods,
        own_meta_frag γ (PodV.key pod) pod.(PodV.ObjectMeta').(ObjectMetaV.UID') 1 pod.(PodV.ObjectMeta')) ∗
      "Hown_children_frag" ∷ own_children_frag γ (ReplicaSetV.key rs)
        rs.(ReplicaSetV.ObjectMeta').(ObjectMetaV.UID') 1 (list_to_set (PodV.key <$> pods)) ∗
      "%Hrs_valid" ∷ ⌜ ReplicaSetV.valid rs ⌝ ∗
      "%Hrs_name_short" ∷ ⌜ length rs.(ReplicaSetV.ObjectMeta').(ObjectMetaV.Name') < 58 ⌝ ∗
      "%Hreplicas_eq" ∷ ⌜ rs.(ReplicaSetV.Spec').(ReplicaSetSpecV.Replicas') = Some n ⌝
  }}}
    @! replicaset.manageReplicas #sl #rs_l
  {{{ pods', RET #interface.nil;
      ⌜ length (filter is_pod_alive pods') = sint.nat n ⌝ ∗
      sl ↦* ptrs ∗
      ([∗ list] ptr;pod ∈ ptrs;filter is_pod_alive pods, PodV.deepown_l ptr pod dq1) ∗
      ReplicaSetV.deepown_l rs_l rs dq2 ∗
      ([∗ list] pod ∈ pods',
        own_meta_frag γ (PodV.key pod) pod.(PodV.ObjectMeta').(ObjectMetaV.UID') 1 pod.(PodV.ObjectMeta')) ∗
      own_children_frag γ (ReplicaSetV.key rs)
        rs.(ReplicaSetV.ObjectMeta').(ObjectMetaV.UID') 1 (list_to_set (PodV.key <$> pods'))
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
  iDestruct (big_sepL2_length with "Hdeepown_l_pods") as %Hlen.
  assert (0 ≤ sint.Z n) as Hn.
  { destruct Hrs_valid as (_ & Hrs_spec_valid & _).
    pose proof (ReplicaSetSpecV.valid_replicas _ Hrs_spec_valid) as (i & Hi_eq & Hi).
    rewrite Hi_eq in Hreplicas_eq. congruence. }
  assert ((sint.Z (word.sub (slice.len_f sl) (W64 (sint.Z n)))) = (sint.Z (slice.len_f sl)) - (sint.Z n)) as -> by word.
  assert ((sint.Z (W64 0)) = 0) as -> by word.
  wp_if_destruct.
  - set I := (∃ (i: w64) (pods': list PodV.t),
      "Hi_ptr" ∷ i_ptr ↦ i ∗
      "Hown_pod_meta_frags" ∷ ([∗ list] pod ∈ pods',
        own_meta_frag γ (PodV.key pod) pod.(PodV.ObjectMeta').(ObjectMetaV.UID') 1 pod.(PodV.ObjectMeta')) ∗
      "Hown_children_frag" ∷ own_children_frag γ (ReplicaSetV.key rs)
        rs.(ReplicaSetV.ObjectMeta').(ObjectMetaV.UID') 1 (list_to_set (PodV.key <$> pods')) ∗
      "%Hpod_number'" ∷ ⌜ length (filter is_pod_alive pods') = Z.to_nat ((sint.Z (slice.len_f sl)) + sint.Z i) ⌝ ∗
      "%Hi" ∷ ⌜ 0 ≤ sint.Z i ≤ sint.Z (word.mul (word.sub (slice.len_f sl) (W64 (sint.Z n))) (W64 (-1))) ⌝
    )%I.
    iAssert (I) with "[i Hown_pod_meta_frags Hown_children_frag]" as "Hloop_inv".
    { iExists (W64 0), pods. iFrame. iPureIntro. split_and!; word. }
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
      { destruct Hrs_valid as (Hrs_meta_valid & Hrs_spec_valid & _).
        pose proof (ReplicaSetSpecV.valid_template _ Hrs_spec_valid) as Hrs_valid_template.
        iPureIntro. split_and!. all: try done. }
      iIntros (pod_l pod) "(Hdeepown_l_pod & %Hpr & %Hvalid & Hrs_HTemplate & Hrs_Hdeepown_template & Hdeepown_m_l_rs)".
      wp_auto. rewrite bool_decide_true //. wp_auto.
      wp_apply (v1.wp_GetNamespace_deepown with "[$Hdeepown_m_l_rs]") as "Hdeepown_m_l_rs".
      wp_apply wp_globals_get.
      wp_apply (wp_State__PodCreate_nameless with "[$Hdeepown_l_pod $Hown_children_frag]").
      { iFrame "#". iSplit.
        - iAssert (is_pkg_init code.controllers.common.common) as "H". all: iPkgInit.
        - iPureIntro. split_and!. all: try done.
          + destruct Hrs_valid as (Hrs_meta_valid & _).
            unfold ObjectMetaV.valid in Hrs_meta_valid. naive_solver.
          + destruct Hrs_valid as (Hrs_meta_valid & _).
            unfold ObjectMetaV.valid in Hrs_meta_valid. naive_solver.
      }
      iIntros (pod_l' pod' key uid) "H". iNamedPrefix "H" "Hcreate_". subst key. subst uid. wp_auto.
      rewrite bool_decide_true //. wp_auto.
      iApply wp_for_post_do. wp_auto.
      iAssert (I) with "[Hi_ptr Hown_pod_meta_frags Hcreate_Hown_meta Hcreate_Hown_children]" as "loop_inv".
      { iExists (word.add i (W64 1)), (pods' ++ [pod']). iFrame "Hi_ptr".
        iSplitL "Hown_pod_meta_frags Hcreate_Hown_meta".
        - rewrite big_sepL_app. simpl. iFrame.
        - iSplitL "Hcreate_Hown_children".
            + assert (list_to_set (PodV.key <$> pods') ∪ {[PodV.key pod']} = list_to_set (PodV.key <$> pods' ++ [pod']))
                as ->.
              { rewrite fmap_app. set_solver. }
              done.
            + iPureIntro.
              split_and!.
              * assert (length (filter is_pod_alive (pods' ++ [pod'])) =
                  S (length (filter is_pod_alive pods'))) as Hfilter_len.
                { assert (is_pod_alive pod') as Hpod_alive.
                  { unfold is_pod_alive.
                    unfold ObjectMetaV.nameless_created in Hcreate_Hmeta_created.
                    naive_solver.
                  }
                  clear -Hpod_alive.
                  induction pods' as [|pod0 pods'' IH]; simpl.
                  - rewrite filter_cons.
                    rewrite decide_True; done.
                  - rewrite !filter_cons.
                    destruct (decide (is_pod_alive pod0)); simpl.
                    + f_equal. exact IH.
                    + exact IH.
                }
                rewrite Hfilter_len Hpod_number'.
                word.
              * word.
              * word.
      }
      iFrame. iApply (struct_fields_combine (V:=v1.ReplicaSetSpec.t)). iFrame.
    + iApply "HΦ". iFrame. iSplitR. 1: iPureIntro; word.
      iApply ReplicaSetV.deepown_l_restore. iFrame.
      iSplitR. 1: done. iSplitL. 2: done.
      rewrite Hreplicas_eq. iExists n. iSplitL. all: done.
  - wp_if_destruct.
    2 : { iApply "HΦ". iFrame.
      iSplit. 1: iPureIntro; word.
      iApply ReplicaSetV.deepown_l_restore. iFrame.
      iSplitR. 1: done. iSplitL. 2: done.
      rewrite Hreplicas_eq. iExists n. iSplitL. all: done. }
    wp_apply wp_slice_slice_pure; [iPureIntro;word|].
    iDestruct (own_slice_f 0 (word.sub (slice.len_f sl) (W64 (sint.Z n))) with "Hsl")
      as "(Hbefore_slice & Hslice & Hafter_slice )"; [word|].
    iDestruct (own_slice_len with "Hslice") as %(Hslice_len1 & Hslice_len2).
    set I := (∃ (i: w64) (pod_l: loc) (pods': list PodV.t),
      "Hi_ptr" ∷ i_ptr ↦ i ∗
      "Hpod_ptr" ∷ pod_ptr ↦ pod_l ∗
      "Hown_pod_meta_frags" ∷ ([∗ list] pod ∈ pods',
        own_meta_frag γ (PodV.key pod) pod.(PodV.ObjectMeta').(ObjectMetaV.UID') 1 pod.(PodV.ObjectMeta')) ∗
      "Hown_children_frag" ∷ own_children_frag γ (ReplicaSetV.key rs)
        rs.(ReplicaSetV.ObjectMeta').(ObjectMetaV.UID') 1 (list_to_set (PodV.key <$> pods')) ∗
      "%Hincluded" ∷ ⌜ ∀ pod, pod ∈ drop (sint.nat i) pods → pod ∈ pods' ⌝ ∗
      "%Hlength" ∷ ⌜ length (filter is_pod_alive pods') = Z.to_nat ((sint.Z (slice.len_f sl)) - sint.Z i) ⌝ ∗
      "%Hi" ∷ ⌜ 0 ≤ sint.Z i ≤ sint.Z (slice.len_f (slice.slice_f sl ptrT (W64 0) (word.sub (slice.len_f sl) (W64 (sint.Z n))))) ⌝
    )%I.
    iAssert (I) with "[i pod Hown_pod_meta_frags Hown_children_frag]" as "Hloop_inv".
    { iExists (W64 0), (default_val loc), pods. iFrame. iPureIntro. split_and!.
      - rewrite drop_0. done.
      - word.
      - word.
      - word.
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
      assert (∃ this_pod, (filter is_pod_alive pods) !! sint.nat i = Some this_pod) as [this_pod Hlookup_active_pods].
      { apply lookup_lt_is_Some_2. rewrite <-Hlen. word. }
      iDestruct (big_sepL2_lookup_acc with "Hdeepown_l_pods") as "[Hdeepown_l_this Hdeepown_l_others]".
      { apply Hlookup_ptrs. }
      { apply Hlookup_active_pods. }
      iPoseProof (PodV.deepown_l_split with "Hdeepown_l_this") as
        "(Hdeepown_t_l_pod & Hdeepown_m_l_pod & Hdeepown_s_l_pod & Hdeepown_st_l_pod)".
      wp_apply (v1.wp_GetUID_deepown with "[$Hdeepown_m_l_pod]"). iIntros "Hdeepown_m_l_pod". wp_auto.
      wp_apply (v1.wp_GetNamespace_deepown with "[$Hdeepown_m_l_pod]"). iIntros "Hdeepown_m_l_pod". wp_auto.
      wp_apply (v1.wp_GetName_deepown with "[$Hdeepown_m_l_pod]"). iIntros "Hdeepown_m_l_pod". wp_auto.
      wp_apply (common.wp_NewDeleteOptionsWithUID). iIntros (do_c) "(Hdeepown_do & %Hvalid_do)". wp_auto.
      wp_apply wp_globals_get.
      assert (∃ j, pods' !! j = Some this_pod) as [j Hlookup_pods'].
      { apply list_elem_of_lookup_1, Hincluded.
        eapply lookup_filter_elem_of_drop.
        exact Hlookup_active_pods. }
      iPoseProof (big_sepL_split_lookup _ _ _ _ Hlookup_pods' with "Hown_pod_meta_frags") as
        "(Hown_pod_meta_frags_before & Hown_pod_meta_frag_this & Hown_pod_meta_frags_after)".
      wp_apply (wp_State__PodDelete_matching_pre with "[$Hdeepown_do $Hown_pod_meta_frag_this $Hown_children_frag]").
      { iFrame "#". iSplit.
        - iAssert (is_pkg_init code.controllers.common.common) as "H". all: iPkgInit.
        - iPureIntro. split_and!. all: try done.
          rewrite elem_of_list_to_set.
          apply list_elem_of_fmap_2.
          eapply list_elem_of_lookup_2.
          exact Hlookup_pods'. }
      iIntros (kmeta') "H". wp_auto.
      rewrite bool_decide_true //. wp_auto.
      iApply wp_for_post_do. wp_auto.
      iDestruct "H" as "[H | H]".
      * iNamedPrefix "H" "Hdelete_".
        iAssert (I) with "[Hi_ptr Hpod_ptr Hown_pod_meta_frags_before Hown_pod_meta_frags_after Hdelete_Hown_meta_frag
          Hdelete_Hown_children_frag]" as "loop_inv".
	        { iExists (word.add i (W64 1)), this_ptr,
	            (take j pods' ++ [this_pod <|PodV.ObjectMeta':=kmeta'|>] ++ drop (S j) pods').
	          iPoseProof (kview.own_meta_valid with "Hdelete_Hown_meta_frag") as "%Hmeta_valid".
	          destruct Hmeta_valid as (Hname_eq & Hnamespace_eq & Huid_eq & _).
	          assert (PodV.key (this_pod <| PodV.ObjectMeta' := kmeta' |>) = PodV.key this_pod) as Hkey_eq.
	          { rewrite /PodV.key /PodV.meta_key /=.
	            rewrite -Hnamespace_eq -Hname_eq.
	            done. }
	          iFrame. iSplitL "Hdelete_Hown_meta_frag".
	          { rewrite big_sepL_singleton Hkey_eq -Huid_eq. iFrame. }
	          iSplitL.
	          { assert (list_to_set (C:=gset KKey.t) (PodV.key <$>
	              (take j pods' ++ [this_pod <| PodV.ObjectMeta' := kmeta' |>] ++ drop (S j) pods')) =
	              list_to_set (C:=gset KKey.t) (PodV.key <$> pods')) as Hchildren_eq.
	            { replace (list_to_set (C:=gset KKey.t) (PodV.key <$> pods')) with
	                (list_to_set (C:=gset KKey.t)
	                  (PodV.key <$> (take j pods' ++ [this_pod] ++ drop (S j) pods'))).
	              2: { rewrite (take_drop_middle pods' j this_pod Hlookup_pods'). done. }
	              rewrite !fmap_app /= Hkey_eq.
	              done. }
	            rewrite Hchildren_eq. iFrame. }
		        iPureIntro. split_and!.
	          - admit.
	          - admit.
            - word.
            - rewrite /slice.slice_f /=. word.
	        }
        iFrame. iApply "Hdeepown_l_others".
        (* iApply PodV.deepown_l_restore. iFrame. *)

    Admitted.

Lemma wp_syncReplicaSet γ l (gv: schema.GroupVersion.t) namespace name rs pods :
  {{{ is_pkg_init code.controllers.replicaset.replicaset ∗
      "#Hisk" ∷ is_kubernetes γ l ∗
      "#Hglobal_l" ∷ (global_addr common.State) ↦□ l ∗
      "#Hglobal_gv" ∷ (global_addr v1.SchemeGroupVersion) ↦□ gv ∗
      "Hown_rs_meta_frag" ∷ own_meta_frag γ (ReplicaSetV.key rs) rs.(ReplicaSetV.ObjectMeta').(ObjectMetaV.UID') 1
        rs.(ReplicaSetV.ObjectMeta') ∗
      "Hown_pod_meta_frags" ∷ ([∗ list] k ↦ pod ∈ pods,
        own_meta_frag γ (PodV.key pod) pod.(PodV.ObjectMeta').(ObjectMetaV.UID') 1 pod.(PodV.ObjectMeta')) ∗
      "Hown_children_frag" ∷ own_children_frag γ (ReplicaSetV.key rs) rs.(ReplicaSetV.ObjectMeta').(ObjectMetaV.UID') 1
        (list_to_set (PodV.key <$> pods)) ∗
      "%Hnamespace_eq" ∷ ⌜ namespace = rs.(ReplicaSetV.ObjectMeta').(ObjectMetaV.Namespace') ⌝ ∗
      "%Hname_eq" ∷ ⌜ name = rs.(ReplicaSetV.ObjectMeta').(ObjectMetaV.Name') ⌝ ∗
      "%Hdeletion_timestamp_eq" ∷ ⌜ rs.(ReplicaSetV.ObjectMeta').(ObjectMetaV.DeletionTimestamp') = None ⌝ ∗
      "%Hrs_name_short" ∷ ⌜ length rs.(ReplicaSetV.ObjectMeta').(ObjectMetaV.Name') < 58 ⌝
  }}}
    @! replicaset.syncReplicaSet #namespace #name
  {{{ (pods' : list PodV.t), RET #interface.nil;
      ⌜ current_state_matches rs pods' ⌝ ∗
      own_meta_frag γ (ReplicaSetV.key rs) rs.(ReplicaSetV.ObjectMeta').(ObjectMetaV.UID') 1
        rs.(ReplicaSetV.ObjectMeta') ∗
      ([∗ list] pod ∈ pods',
        own_meta_frag γ (PodV.key pod) pod.(PodV.ObjectMeta').(ObjectMetaV.UID') 1 pod.(PodV.ObjectMeta')) ∗
      own_children_frag γ (ReplicaSetV.key rs) rs.(ReplicaSetV.ObjectMeta').(ObjectMetaV.UID') 1
        (list_to_set (PodV.key <$> pods'))
  }}}.
Proof. Admitted.

End proof.
