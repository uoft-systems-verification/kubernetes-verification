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

Lemma wp_manageReplicas γ l (gv: schema.GroupVersion.t) sl rs_l ptrs pods rs n dq1 dq2 :
  {{{ is_pkg_init code.controllers.replicaset.replicaset ∗
      "#Hisk" ∷ is_kubernetes γ l ∗
      "#Hglobal_l" ∷ (global_addr common.State) ↦□ l ∗
      "#Hglobal_gv" ∷ (global_addr v1.SchemeGroupVersion) ↦□ gv ∗
      "Hsl" ∷ sl ↦* ptrs ∗
      "Hdeepown_l_pods" ∷ ([∗ list] ptr;pod ∈ ptrs;pods, PodV.deepown_l ptr pod dq1) ∗
      "Hdeepown_l_rs" ∷ ReplicaSetV.deepown_l rs_l rs dq2 ∗
      "Hown_pod_meta_frags" ∷ ([∗ list] pod ∈ pods,
        own_meta_frag γ (PodV.key pod) pod.(PodV.ObjectMeta').(ObjectMetaV.UID') 1 pod.(PodV.ObjectMeta')) ∗
      "Hown_children_frag" ∷ own_children_frag γ (ReplicaSetV.key rs)
        rs.(ReplicaSetV.ObjectMeta').(ObjectMetaV.UID') 1 (list_to_set (PodV.key <$> pods)) ∗
      "%Hrs_valid" ∷ ⌜ ReplicaSetV.valid rs ⌝ ∗
      "%Hrs_name_short" ∷ ⌜ length rs.(ReplicaSetV.ObjectMeta').(ObjectMetaV.Name') < 58 ⌝ ∗
      "%Hpods_active" ∷ ⌜ Forall is_pod_alive pods ⌝ ∗
      "%Hreplicas_eq" ∷ ⌜ rs.(ReplicaSetV.Spec').(ReplicaSetSpecV.Replicas') = Some n ⌝
  }}}
    @! replicaset.manageReplicas #sl #rs_l
  {{{ pods', RET #interface.nil;
      ⌜ length pods' = sint.nat n ⌝ ∗
      ⌜ Forall is_pod_alive pods' ⌝ ∗
      sl ↦* ptrs ∗
      ([∗ list] ptr;pod ∈ ptrs;pods, PodV.deepown_l ptr pod dq1) ∗
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
      "%Hpods_active'" ∷ ⌜ Forall is_pod_alive pods' ⌝ ∗
      "%Hlength_eq'" ∷ ⌜ length pods' = Z.to_nat ((sint.Z (slice.len_f sl)) + sint.Z i) ⌝ ∗
      "%Hi" ∷ ⌜ 0 ≤ sint.Z i ≤ sint.Z (word.mul (word.sub (slice.len_f sl) (W64 (sint.Z n))) (W64 (-1))) ⌝
    )%I.
    iAssert (I) with "[i Hown_pod_meta_frags Hown_children_frag]" as "Hloop_inv".
    { iExists (W64 0), pods. iFrame. iPureIntro. split_and!; [done|word|word|word]. }
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
            * rewrite Forall_app. split; [done|].
              constructor; [|constructor].
              unfold is_pod_alive.
              unfold ObjectMetaV.nameless_created in Hcreate_Hmeta_created.
              naive_solver.
            * rewrite app_length /= Hlength_eq'.
              word.
            * word.
            * word.
      }
      iFrame. iApply (struct_fields_combine (V:=v1.ReplicaSetSpec.t)). iFrame.
    + iApply "HΦ". iFrame. iSplitR. 1: iPureIntro; word. iSplitR. 1: done.
      iApply ReplicaSetV.deepown_l_restore. iFrame.
      iSplitR. 1: done. iSplitL. 2: done.
      rewrite Hreplicas_eq. iExists n. iSplitL. all: done.
  - admit.
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
