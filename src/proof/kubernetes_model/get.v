From New.proof Require Import prelude empty_ffi.
From New.proof.kubernetes_model Require Export common_get.

Section proof.
Context `{hG: !heapGS Σ} `{!ffi_semantics _ _}.
Context {sem : go.Semantics} {package_sem : apimodel.Assumptions}.
Context `{!kubernetesModelG Σ}.
Local Set Default Proof Using "All".

Lemma wp_State__get_some_au γ l key :
  ∀ Φ,
  ( is_pkg_init apimodel ∗
    is_kubernetes γ l ∗
    |={⊤,∅}=> ∃ uid dq kmeta kspec_o kstatus_o,
      "Hown_meta_frag" ∷ own_meta_frag γ key uid dq kmeta ∗
      "Hown_spec_frag" ∷ match kspec_o with
      | Some kspec => own_spec_frag γ key uid dq kspec
      | None => True
      end ∗
      "Hown_status_frag" ∷ match kstatus_o with
      | Some kstatus => own_status_frag γ key uid dq kstatus
      | None => True
      end ∗
      "Hclose" ∷ (∀ i kobj,
        ⌜ KObjectV.valid kobj ⌝ ∗
        ⌜ KObjectV.extra_valid kobj ⌝ ∗
        ⌜ key = KObjectV.key kobj ⌝ ∗
        ⌜ ObjectMetaV.equiv_except_resource_version (KObjectV.objectmeta kobj) kmeta ⌝ ∗
        KObjectV.deepown_i i kobj 1 ∗
        own_meta_frag γ key uid dq kmeta ∗
        match kspec_o with
        | Some kspec => own_spec_frag γ key uid dq kspec ∗ ⌜ kspec = KObjectV.spec kobj ⌝
        | None => True
        end ∗
        match kstatus_o with
        | Some kstatus => own_status_frag γ key uid dq kstatus ∗ ⌜ kstatus = KObjectV.status kobj ⌝
        | None => True
        end
          ={∅,⊤}=∗ ▷ Φ (#(interface.ok i), #interface.nil)%V
      )
  ) -∗ WP l @! (go.PointerType apimodel.State) @! "get" #key {{ Φ }}.
Proof.
  iIntros (Φ) "(#Hpkg & #Hkinv & Hau)". iNamed "Hau". iNamed "Hkinv".
  wp_method_call. rewrite /apimodel.State__getⁱᵐᵖˡ. wp_call.
  wp_apply wp_with_defer as "%defer Hdefer".
  simpl subst. wp_auto.
  wp_apply wp_Mutex__Lock; [done|]. iIntros "[Hown_Mutex H]". iNamedPrefix "H" "Hinv_". wp_auto.
  wp_apply (wp_map_lookup2_KKey (go.InterfaceType []) with "[$Hinv_Hown_phys]").
  iIntros "Hinv_Hown_phys". wp_auto.
  iDestruct (big_sepM2_dom with "Hinv_Hphys_abs_rep") as %Hdom_eq.
  destruct (bool_decide (is_Some (phys_state !! key))) eqn:Hdecide.
  2: {
    apply bool_decide_eq_false in Hdecide.
    assert (phys_state !! key = None) as Hlookup_phys_none.
    { destruct (phys_state !! key) as [i|] eqn:Hlookup_phys; [|done].
      exfalso. apply Hdecide. done. }
    assert (abs_state !! key = None) as Hlookup_abs.
    { apply not_elem_of_dom. rewrite <- Hdom_eq.
      apply not_elem_of_dom. done. }
    iApply fupd_wp.
    iMod "Hau" as (uid dq kmeta kspec_o kstatus_o) "H". iNamed "H".
    iPoseProof (kview.own_meta_exists with "Hinv_Hown_abs Hown_meta_frag")
      as "(%obj & %Hlookup_abs' & %Huid_obj & %Hmeta_eq & %Huid_in)".
    assert (abs_state !! key ≠ None) as Hlookup_abs''.
    { intros Hnone. rewrite Hlookup_abs' in Hnone. done. }
    done.
  }
  assert (∃ i, phys_state !! key = Some i) as [i Hlookup_phys].
  { apply bool_decide_eq_true in Hdecide. done. }
  assert (∃ kobj, abs_state !! key = Some kobj) as [kobj Hlookup_abs].
  { apply elem_of_dom. rewrite <- Hdom_eq. apply elem_of_dom.
    eexists. done. }
  iDestruct (big_sepM2_lookup_acc _ _ _ _ _ _ Hlookup_phys Hlookup_abs with "Hinv_Hphys_abs_rep")
  as "(Hdeepown_i & Hother_rep)".
  destruct i as [i_ok|].
  2: { simpl. iDestruct "Hdeepown_i" as %[]. }
  rewrite Hlookup_phys. wp_auto.
  wp_apply (wp_deepCopy with "[$Hpkg $Hdeepown_i]").
  iIntros (i') "(Hdeepown_i' & Hdeepown_i)". wp_auto.
  iApply fupd_wp.
  iMod "Hau" as (uid dq kmeta kspec_o kstatus_o) "H". iNamed "H".
  iPoseProof (kview.own_auth_valid key kobj with "Hinv_Hown_abs") as "%Hin_auth".
  destruct (Hin_auth Hlookup_abs) as [Hkey_eq [Hwf _]].
  iPoseProof (kview.own_auth_extra_valid_forall with "Hinv_Hown_abs")
    as "%Habs_extra_valid".
  assert (KObjectV.extra_valid kobj) as Hextra_valid.
  { exact (Habs_extra_valid key kobj Hlookup_abs). }
  iPoseProof (kview.own_meta_valid with "Hown_meta_frag")
    as "(%Hname_eq & %Hns_eq & %Huid_eq & %Hmeta_wf & %Hmeta_living)".
  iPoseProof (kview.own_meta_exists2 with "Hinv_Hown_abs Hown_meta_frag")
    as "(%Huid_obj & %Hmeta_eq & %Huid_in)". 1: done.
  iPoseProof (kview.own_meta_living Hlookup_abs with
    "Hinv_Hown_abs Hown_meta_frag") as "%Hkobj_living".
  destruct kspec_o as [kspec|]; destruct kstatus_o as [kstatus|].
  1, 2: iPoseProof (kview.own_spec_exists with "Hinv_Hown_abs Hown_spec_frag") as "%Hspec_found";
        assert (kspec = KObjectV.spec kobj) as Hkspec_eq by
          (symmetry; eapply Hspec_found; [exact Hlookup_abs|exact Huid_obj|exact Hkobj_living]).
  1, 3: iPoseProof (kview.own_status_exists with "Hinv_Hown_abs Hown_status_frag") as "%Hstatus_found";
        assert (kstatus = KObjectV.status kobj) as Hkstatus_eq by
          (symmetry; eapply Hstatus_found; [exact Hlookup_abs|exact Huid_obj|exact Hkobj_living]).
  all: iMod ("Hclose" $! i' kobj with "[Hown_meta_frag Hown_spec_frag Hown_status_frag Hdeepown_i']") as "HΦ";
    [iFrame; iPureIntro; split_and!; done|].
  all: iModIntro.
  all: iAssert (([∗ map] i; obj ∈ phys_state; abs_state,
      match i with
      | interface.ok i_ok => KObjectV.deepown_i i_ok obj 1
      | interface.nil => False%I
      end)%I)
    with "[Hdeepown_i Hother_rep]" as "Hinv_Hphys_abs_rep";
    [iApply "Hother_rep"; iFrame|].
  all: iCombineNamed "Hinv_*" as "H".
  all: wp_apply (wp_Mutex__Unlock _ (kubernetes_inv γ l) with "[$Hown_Mutex H]");
    [iNamed "H"; iFrame; iFrame "#"; done|].
  all: iApply "HΦ".
Unshelve. all: try tc_solve.
Qed.

Lemma wp_State__get_some γ l key uid dq kmeta kspec_o kstatus_o :
  {{{ is_pkg_init apimodel ∗
      "#Hisk" ∷ is_kubernetes γ l ∗
      "Hown_meta_frag" ∷ own_meta_frag γ key uid dq kmeta ∗
      "Hown_spec_frag" ∷ match kspec_o with
      | Some kspec => own_spec_frag γ key uid dq kspec
      | None => True
      end ∗
      "Hown_status_frag" ∷ match kstatus_o with
      | Some kstatus => own_status_frag γ key uid dq kstatus
      | None => True
      end
  }}}
    l @! (go.PointerType apimodel.State) @! "get" #key
  {{{ i kobj, RET (#(interface.ok i), #interface.nil);
      "%Hvalid'" ∷ ⌜ KObjectV.valid kobj ⌝ ∗
      "%Hextra_valid" ∷ ⌜ KObjectV.extra_valid kobj ⌝ ∗
      "%Hkey_eq" ∷ ⌜ key = KObjectV.key kobj ⌝ ∗
      "%Hmeta_eq" ∷ ⌜ ObjectMetaV.equiv_except_resource_version (KObjectV.objectmeta kobj) kmeta ⌝ ∗
      "Hdeepown_i" ∷ KObjectV.deepown_i i kobj 1 ∗
      "Hown_meta_frag" ∷ own_meta_frag γ key uid dq kmeta ∗
      match kspec_o with
      | Some kspec =>
          "Hown_spec_frag" ∷ own_spec_frag γ key uid dq kspec ∗
          "%Hspec_eq" ∷ ⌜ kspec = KObjectV.spec kobj ⌝
      | None => True
      end ∗
      match kstatus_o with
      | Some kstatus =>
          "Hown_status_frag" ∷ own_status_frag γ key uid dq kstatus ∗
          "%Hstatus_eq" ∷ ⌜ kstatus = KObjectV.status kobj ⌝
      | None => True
      end
  }}}.
Proof.
  iIntros (Φ) "(#Hinit & H) HΦ". iNamed "H".
  iApply wp_State__get_some_au.
  iFrame "#". iFrame.
  iApply fupd_mask_intro; [ timeout 10 set_solver | iIntros "Hmask" ].
  iIntros (i kobj) "Hpost".
  iMod "Hmask" as "_".
  iModIntro. iNext.
  iApply ("HΦ" $! i kobj with "Hpost").
Qed.

Lemma wp_State__PodMutGet γ l key namespace name uid dq kmeta kspec kstatus :
  {{{ is_pkg_init apimodel ∗
      "#Hisk" ∷ is_kubernetes γ l ∗
      "%Hkey_def" ∷ ⌜ key = {|
        KKey.Kind' := "Pod"%go;
        KKey.Namespace' := namespace;
        KKey.Name' := name
      |} ⌝ ∗
      "Hown_meta_frag" ∷ own_meta_frag γ key uid dq kmeta ∗
      "Hown_spec_frag" ∷ own_spec_frag γ key uid dq (ObjectSpecV.PodSpec kspec) ∗
      "Hown_status_frag" ∷ own_status_frag γ key uid dq (ObjectStatusV.PodStatus kstatus)
  }}}
    l @! (go.PointerType apimodel.State) @! "PodMutGet" #namespace #name
  {{{ pod_l pod, RET (#pod_l, #interface.nil);
      "%Hvalid'" ∷ ⌜ KObjectV.valid (KObjectV.Pod pod) ⌝ ∗
      "%Hkey_eq" ∷ ⌜ key = PodV.key pod ⌝ ∗
      "%Hmeta_eq" ∷ ⌜ ObjectMetaV.equiv_except_resource_version pod.(PodV.ObjectMeta') kmeta ⌝ ∗
      "%Hspec_eq" ∷ ⌜ kspec = pod.(PodV.Spec') ⌝ ∗
      "%Hstatus_eq" ∷ ⌜ kstatus = pod.(PodV.Status') ⌝ ∗
      "Hdeepown_l" ∷ PodV.deepown_l pod_l pod 1 ∗
      "Hown_meta_frag" ∷ own_meta_frag γ key uid dq kmeta ∗
      "Hown_spec_frag" ∷ own_spec_frag γ key uid dq (ObjectSpecV.PodSpec kspec) ∗
      "Hown_status_frag" ∷ own_status_frag γ key uid dq (ObjectStatusV.PodStatus kstatus)
  }}}.
Proof.
  iIntros (Φ) "(#Hinit & H) HΦ". iNamed "H". subst key.
  wp_method_call. rewrite /apimodel.State__PodMutGetⁱᵐᵖˡ. wp_call. wp_auto.
  wp_apply (wp_State__get_some γ l
    {| KKey.Kind' := "Pod"%go; KKey.Namespace' := namespace; KKey.Name' := name |}
    uid dq kmeta (Some (ObjectSpecV.PodSpec kspec)) (Some (ObjectStatusV.PodStatus kstatus))
    with "[$Hinit $Hisk $Hown_meta_frag $Hown_spec_frag $Hown_status_frag]").
  iIntros (i kobj) "Hpost". iNamed "Hpost".
  iDestruct "Hpost" as "((Hown_spec_frag & %Hspec_eq) & Hown_status_frag & %Hstatus_eq)".
  destruct kobj as [pod|rs|pvc|sts|d]; try solve [simpl in Hspec_eq; done].
  simpl in Hvalid', Hkey_eq, Hmeta_eq, Hspec_eq, Hstatus_eq.
  assert (Hspec_eq' : kspec = pod.(PodV.Spec')) by congruence.
  assert (Hstatus_eq' : kstatus = pod.(PodV.Status')) by congruence.
  clear Hspec_eq Hstatus_eq.
  rename Hspec_eq' into Hspec_eq.
  rename Hstatus_eq' into Hstatus_eq.
  iDestruct "Hdeepown_i" as (pod_l) "[%Hi Hdeepown_l]".
  wp_auto.
  unfold KObjectV.valid_interface in Hi. destruct Hi as [Hi _]. rewrite Hi.
  change (go.PointerType api_core_v1.Pod) with (go.PointerType v1.Pod).
  cbn [interface.ty interface.v].
  replace (if decide (go.PointerType v1.Pod = go.PointerType v1.Pod)
           then #pod_l else #null)%V with (#pod_l)%V by
    (rewrite decide_True; done).
  replace (bool_decide (go.PointerType v1.Pod = go.PointerType v1.Pod)) with true by
    (symmetry; apply bool_decide_eq_true_2; done).
  wp_auto.
  iApply "HΦ". iFrame. iPureIntro. split_and!; done.
Qed.

Lemma wp_State__PodGet γ l key namespace name uid dq kmeta kspec kstatus :
  {{{ is_pkg_init apimodel ∗
      "#Hisk" ∷ is_kubernetes γ l ∗
      "%Hkey_def" ∷ ⌜ key = {|
        KKey.Kind' := "Pod"%go;
        KKey.Namespace' := namespace;
        KKey.Name' := name
      |} ⌝ ∗
      "Hown_meta_frag" ∷ own_meta_frag γ key uid dq kmeta ∗
      "Hown_spec_frag" ∷ own_spec_frag γ key uid dq (ObjectSpecV.PodSpec kspec) ∗
      "Hown_status_frag" ∷ own_status_frag γ key uid dq (ObjectStatusV.PodStatus kstatus)
  }}}
    l @! (go.PointerType apimodel.State) @! "PodGet" #namespace #name
  {{{ pod_l pod, RET (#pod_l, #interface.nil);
      "%Hvalid'" ∷ ⌜ KObjectV.valid (KObjectV.Pod pod) ⌝ ∗
      "%Hkey_eq" ∷ ⌜ key = PodV.key pod ⌝ ∗
      "%Hmeta_eq" ∷ ⌜ ObjectMetaV.equiv_except_resource_version pod.(PodV.ObjectMeta') kmeta ⌝ ∗
      "%Hspec_eq" ∷ ⌜ kspec = pod.(PodV.Spec') ⌝ ∗
      "%Hstatus_eq" ∷ ⌜ kstatus = pod.(PodV.Status') ⌝ ∗
      "Hdeepown_l" ∷ PodV.deepown_l pod_l pod 1 ∗
      "Hown_meta_frag" ∷ own_meta_frag γ key uid dq kmeta ∗
      "Hown_spec_frag" ∷ own_spec_frag γ key uid dq (ObjectSpecV.PodSpec kspec) ∗
      "Hown_status_frag" ∷ own_status_frag γ key uid dq (ObjectStatusV.PodStatus kstatus)
  }}}.
Proof.
  iIntros (Φ) "(#Hinit & H) HΦ". iNamed "H".
  wp_method_call. rewrite /apimodel.State__PodGetⁱᵐᵖˡ. wp_call. wp_auto.
  wp_apply (wp_State__PodMutGet γ l key namespace name uid dq kmeta kspec kstatus
    with "[$Hinit $Hisk $Hown_meta_frag $Hown_spec_frag $Hown_status_frag]").
  { iPureIntro. done. }
  iIntros (pod_l pod) "Hpost".
  wp_auto.
  iApply ("HΦ" with "Hpost").
Qed.

Lemma wp_State__ReplicaSetMutGet γ l key namespace name uid dq kmeta kspec :
  {{{ is_pkg_init apimodel ∗
      "#Hisk" ∷ is_kubernetes γ l ∗
      "%Hkey_def" ∷ ⌜ key = {|
        KKey.Kind' := "ReplicaSet"%go;
        KKey.Namespace' := namespace;
        KKey.Name' := name
      |} ⌝ ∗
      "Hown_meta_frag" ∷ own_meta_frag γ key uid dq kmeta ∗
      "Hown_spec_frag" ∷ own_spec_frag γ key uid dq (ObjectSpecV.ReplicaSetSpec kspec)
  }}}
    l @! (go.PointerType apimodel.State) @! "ReplicaSetMutGet" #namespace #name
  {{{ rs_l rs, RET (#rs_l, #interface.nil);
      "%Hvalid'" ∷ ⌜ KObjectV.valid (KObjectV.ReplicaSet rs) ⌝ ∗
      "%Hextra_valid" ∷ ⌜ ReplicaSetV.extra_valid rs ⌝ ∗
      "%Hkey_eq" ∷ ⌜ key = ReplicaSetV.key rs ⌝ ∗
      "%Hmeta_eq" ∷ ⌜ ObjectMetaV.equiv_except_resource_version rs.(ReplicaSetV.ObjectMeta') kmeta ⌝ ∗
      "%Hspec_eq" ∷ ⌜ kspec = rs.(ReplicaSetV.Spec') ⌝ ∗
      "Hdeepown_l" ∷ ReplicaSetV.deepown_l rs_l rs 1 ∗
      "Hown_meta_frag" ∷ own_meta_frag γ key uid dq kmeta ∗
      "Hown_spec_frag" ∷ own_spec_frag γ key uid dq (ObjectSpecV.ReplicaSetSpec kspec)
  }}}.
Proof.
  iIntros (Φ) "(#Hinit & H) HΦ". iNamed "H". subst key.
  wp_method_call. rewrite /apimodel.State__ReplicaSetMutGetⁱᵐᵖˡ. wp_call. wp_auto.
  wp_apply (wp_State__get_some γ l
    {| KKey.Kind' := "ReplicaSet"%go; KKey.Namespace' := namespace; KKey.Name' := name |}
    uid dq kmeta (Some (ObjectSpecV.ReplicaSetSpec kspec)) None
    with "[$Hinit $Hisk $Hown_meta_frag $Hown_spec_frag]").
  iIntros (i kobj) "Hpost". iNamed "Hpost".
  iDestruct "Hpost" as "((Hown_spec_frag & %Hspec_eq) & _)".
  destruct kobj as [pod|rs|pvc|sts|d]; try solve [simpl in Hspec_eq; done].
  simpl in Hvalid', Hkey_eq, Hmeta_eq, Hspec_eq.
  assert (Hspec_eq' : kspec = rs.(ReplicaSetV.Spec')) by congruence.
  clear Hspec_eq.
  rename Hspec_eq' into Hspec_eq.
  iDestruct "Hdeepown_i" as (rs_l) "[%Hi Hdeepown_l]".
  wp_auto.
  unfold KObjectV.valid_interface in Hi. destruct Hi as [Hi _]. rewrite Hi.
  change (go.PointerType api_apps_v1.ReplicaSet) with (go.PointerType v1.ReplicaSet).
  cbn [interface.ty interface.v].
  replace (if decide (go.PointerType v1.ReplicaSet = go.PointerType v1.ReplicaSet)
           then #rs_l else #null)%V with (#rs_l)%V by
    (rewrite decide_True; done).
  replace (bool_decide (go.PointerType v1.ReplicaSet = go.PointerType v1.ReplicaSet)) with true by
    (symmetry; apply bool_decide_eq_true_2; done).
  wp_auto.
  iApply "HΦ". iFrame. iPureIntro. split_and!; done.
Qed.

Lemma wp_State__ReplicaSetGet γ l key namespace name uid dq kmeta kspec :
  {{{ is_pkg_init apimodel ∗
      "#Hisk" ∷ is_kubernetes γ l ∗
      "%Hkey_def" ∷ ⌜ key = {|
        KKey.Kind' := "ReplicaSet"%go;
        KKey.Namespace' := namespace;
        KKey.Name' := name
      |} ⌝ ∗
      "Hown_meta_frag" ∷ own_meta_frag γ key uid dq kmeta ∗
      "Hown_spec_frag" ∷ own_spec_frag γ key uid dq (ObjectSpecV.ReplicaSetSpec kspec)
  }}}
    l @! (go.PointerType apimodel.State) @! "ReplicaSetGet" #namespace #name
  {{{ rs_l rs, RET (#rs_l, #interface.nil);
      "%Hvalid'" ∷ ⌜ KObjectV.valid (KObjectV.ReplicaSet rs) ⌝ ∗
      "%Hextra_valid" ∷ ⌜ ReplicaSetV.extra_valid rs ⌝ ∗
      "%Hkey_eq" ∷ ⌜ key = ReplicaSetV.key rs ⌝ ∗
      "%Hmeta_eq" ∷ ⌜ ObjectMetaV.equiv_except_resource_version rs.(ReplicaSetV.ObjectMeta') kmeta ⌝ ∗
      "%Hspec_eq" ∷ ⌜ kspec = rs.(ReplicaSetV.Spec') ⌝ ∗
      "Hdeepown_l" ∷ ReplicaSetV.deepown_l rs_l rs 1 ∗
      "Hown_meta_frag" ∷ own_meta_frag γ key uid dq kmeta ∗
      "Hown_spec_frag" ∷ own_spec_frag γ key uid dq (ObjectSpecV.ReplicaSetSpec kspec)
  }}}.
Proof.
  iIntros (Φ) "(#Hinit & H) HΦ". iNamed "H".
  wp_method_call. rewrite /apimodel.State__ReplicaSetGetⁱᵐᵖˡ. wp_call. wp_auto.
  wp_apply (wp_State__ReplicaSetMutGet γ l key namespace name uid dq kmeta kspec
    with "[$Hinit $Hisk $Hown_meta_frag $Hown_spec_frag]").
  { iPureIntro. done. }
  iIntros (rs_l rs) "Hpost".
  wp_auto.
  iApply ("HΦ" with "Hpost").
Qed.

Lemma wp_State__PersistentVolumeClaimMutGet γ l key namespace name uid dq kmeta :
  {{{ is_pkg_init apimodel ∗
      "#Hisk" ∷ is_kubernetes γ l ∗
      "%Hkey_def" ∷ ⌜ key = {|
        KKey.Kind' := "PersistentVolumeClaim"%go;
        KKey.Namespace' := namespace;
        KKey.Name' := name
      |} ⌝ ∗
      "Hown_meta_frag" ∷ own_meta_frag γ key uid dq kmeta
  }}}
    l @! (go.PointerType apimodel.State) @! "PersistentVolumeClaimMutGet" #namespace #name
  {{{ pvc_l pvc, RET (#pvc_l, #interface.nil);
      "%Hvalid'" ∷ ⌜ KObjectV.valid (KObjectV.PersistentVolumeClaim pvc) ⌝ ∗
      "%Hkey_eq" ∷ ⌜ key = PersistentVolumeClaimV.key pvc ⌝ ∗
      "%Hmeta_eq" ∷ ⌜ ObjectMetaV.equiv_except_resource_version pvc.(PersistentVolumeClaimV.ObjectMeta') kmeta ⌝ ∗
      "Hdeepown_l" ∷ PersistentVolumeClaimV.deepown_l pvc_l pvc 1 ∗
      "Hown_meta_frag" ∷ own_meta_frag γ key uid dq kmeta
  }}}.
Proof.
  iIntros (Φ) "(#Hinit & H) HΦ". iNamed "H". subst key.
  wp_method_call.
  rewrite /apimodel.State__PersistentVolumeClaimMutGetⁱᵐᵖˡ.
  wp_call. wp_auto.
  iAssert (is_pkg_init apimodel ∗
      is_kubernetes γ l ∗
      own_meta_frag γ
        {| KKey.Kind' := "PersistentVolumeClaim"%go;
           KKey.Namespace' := namespace;
           KKey.Name' := name |}
        uid dq kmeta ∗ True ∗ True)%I
    with "[$Hinit $Hisk $Hown_meta_frag]" as "Hget".
  { iFrame. done. }
  wp_apply (wp_State__get_some γ l
    {| KKey.Kind' := "PersistentVolumeClaim"%go;
       KKey.Namespace' := namespace;
       KKey.Name' := name |}
    uid dq kmeta
    (None : option ObjectSpecV.t) (None : option ObjectStatusV.t)
    with "Hget").
  iIntros (i kobj) "Hpost". iNamed "Hpost".
  iDestruct "Hpost" as "(_ & _)".
  destruct kobj as [pod|rs|pvc|sts|d];
    try solve [
      exfalso;
      apply (f_equal KKey.Kind') in Hkey_eq;
      simpl in Hkey_eq;
      discriminate
    ].
  simpl in Hvalid', Hkey_eq, Hmeta_eq.
  iDestruct "Hdeepown_i" as (pvc_l) "[%Hi Hdeepown_l]".
  wp_auto.
  unfold KObjectV.valid_interface in Hi. destruct Hi as [Hi _]. rewrite Hi.
  change (go.PointerType api_core_v1.PersistentVolumeClaim) with
    (go.PointerType v1.PersistentVolumeClaim).
  cbn [interface.ty interface.v].
  replace
    (if decide
      (go.PointerType v1.PersistentVolumeClaim =
       go.PointerType v1.PersistentVolumeClaim)
     then #pvc_l else #null)%V
    with (#pvc_l)%V by (rewrite decide_True; done).
  replace
    (bool_decide
      (go.PointerType v1.PersistentVolumeClaim =
       go.PointerType v1.PersistentVolumeClaim))
    with true by (symmetry; apply bool_decide_eq_true_2; done).
  wp_auto.
  iApply "HΦ". iFrame. iPureIntro. split_and!; done.
Qed.

Lemma wp_State__PersistentVolumeClaimGet γ l key namespace name uid dq kmeta :
  {{{ is_pkg_init apimodel ∗
      "#Hisk" ∷ is_kubernetes γ l ∗
      "%Hkey_def" ∷ ⌜ key = {|
        KKey.Kind' := "PersistentVolumeClaim"%go;
        KKey.Namespace' := namespace;
        KKey.Name' := name
      |} ⌝ ∗
      "Hown_meta_frag" ∷ own_meta_frag γ key uid dq kmeta
  }}}
    l @! (go.PointerType apimodel.State) @! "PersistentVolumeClaimGet" #namespace #name
  {{{ pvc_l pvc, RET (#pvc_l, #interface.nil);
      "%Hvalid'" ∷ ⌜ KObjectV.valid (KObjectV.PersistentVolumeClaim pvc) ⌝ ∗
      "%Hkey_eq" ∷ ⌜ key = PersistentVolumeClaimV.key pvc ⌝ ∗
      "%Hmeta_eq" ∷ ⌜ ObjectMetaV.equiv_except_resource_version pvc.(PersistentVolumeClaimV.ObjectMeta') kmeta ⌝ ∗
      "Hdeepown_l" ∷ PersistentVolumeClaimV.deepown_l pvc_l pvc 1 ∗
      "Hown_meta_frag" ∷ own_meta_frag γ key uid dq kmeta
  }}}.
Proof.
  iIntros (Φ) "(#Hinit & H) HΦ". iNamed "H".
  wp_method_call.
  rewrite /apimodel.State__PersistentVolumeClaimGetⁱᵐᵖˡ.
  wp_call. wp_auto.
  wp_apply (wp_State__PersistentVolumeClaimMutGet
    γ l key namespace name uid dq kmeta
    with "[$Hinit $Hisk $Hown_meta_frag]").
  { iPureIntro. done. }
  iIntros (pvc_l pvc) "Hpost".
  wp_auto.
  iApply ("HΦ" with "Hpost").
Qed.

Lemma wp_State__StatefulSetMutGet γ l key namespace name uid dq kmeta kspec :
  {{{ is_pkg_init apimodel ∗
      "#Hisk" ∷ is_kubernetes γ l ∗
      "%Hkey_def" ∷ ⌜ key = {|
        KKey.Kind' := "StatefulSet"%go;
        KKey.Namespace' := namespace;
        KKey.Name' := name
      |} ⌝ ∗
      "Hown_meta_frag" ∷ own_meta_frag γ key uid dq kmeta ∗
      "Hown_spec_frag" ∷ own_spec_frag γ key uid dq (ObjectSpecV.StatefulSetSpec kspec)
  }}}
    l @! (go.PointerType apimodel.State) @! "StatefulSetMutGet"
      #namespace #name
  {{{ sts_l sts, RET (#sts_l, #interface.nil);
      "%Hvalid'" ∷ ⌜ KObjectV.valid (KObjectV.StatefulSet sts) ⌝ ∗
      "%Hkey_eq" ∷ ⌜ key = StatefulSetV.key sts ⌝ ∗
      "%Hmeta_eq" ∷ ⌜ ObjectMetaV.equiv_except_resource_version sts.(StatefulSetV.ObjectMeta') kmeta ⌝ ∗
      "%Hspec_eq" ∷ ⌜ kspec = sts.(StatefulSetV.Spec') ⌝ ∗
      "Hdeepown_l" ∷ StatefulSetV.deepown_l sts_l sts 1 ∗
      "Hown_meta_frag" ∷ own_meta_frag γ key uid dq kmeta ∗
      "Hown_spec_frag" ∷ own_spec_frag γ key uid dq (ObjectSpecV.StatefulSetSpec kspec)
  }}}.
Proof.
  iIntros (Φ) "(#Hinit & H) HΦ". iNamed "H". subst key.
  wp_method_call.
  rewrite /apimodel.State__StatefulSetMutGetⁱᵐᵖˡ.
  wp_call. wp_auto.
  wp_apply (wp_State__get_some γ l
    {| KKey.Kind' := "StatefulSet"%go;
       KKey.Namespace' := namespace;
       KKey.Name' := name |}
    uid dq kmeta (Some (ObjectSpecV.StatefulSetSpec kspec)) None
    with "[$Hinit $Hisk $Hown_meta_frag $Hown_spec_frag]").
  iIntros (i kobj) "Hpost". iNamed "Hpost".
  iDestruct "Hpost" as "((Hown_spec_frag & %Hspec_eq) & _)".
  destruct kobj as [pod|rs|pvc|sts|d];
    try solve [simpl in Hspec_eq; done].
  simpl in Hvalid', Hkey_eq, Hmeta_eq, Hspec_eq.
  assert (Hspec_eq' : kspec = sts.(StatefulSetV.Spec')) by congruence.
  clear Hspec_eq. rename Hspec_eq' into Hspec_eq.
  iDestruct "Hdeepown_i" as (sts_l) "[%Hi Hdeepown_l]".
  wp_auto.
  unfold KObjectV.valid_interface in Hi. destruct Hi as [Hi _]. rewrite Hi.
  change (go.PointerType api_apps_v1.StatefulSet)
    with (go.PointerType v1.StatefulSet).
  cbn [interface.ty interface.v].
  replace (if decide
      (go.PointerType v1.StatefulSet = go.PointerType v1.StatefulSet)
    then #sts_l else #null)%V with (#sts_l)%V by
    (rewrite decide_True; done).
  replace (bool_decide
      (go.PointerType v1.StatefulSet = go.PointerType v1.StatefulSet))
    with true by (symmetry; apply bool_decide_eq_true_2; done).
  wp_auto.
  iApply "HΦ". iFrame. iPureIntro. split_and!; done.
Qed.

Lemma wp_State__StatefulSetGet γ l key namespace name uid dq kmeta kspec :
  {{{ is_pkg_init apimodel ∗
      "#Hisk" ∷ is_kubernetes γ l ∗
      "%Hkey_def" ∷ ⌜ key = {|
        KKey.Kind' := "StatefulSet"%go;
        KKey.Namespace' := namespace;
        KKey.Name' := name
      |} ⌝ ∗
      "Hown_meta_frag" ∷ own_meta_frag γ key uid dq kmeta ∗
      "Hown_spec_frag" ∷ own_spec_frag γ key uid dq (ObjectSpecV.StatefulSetSpec kspec)
  }}}
    l @! (go.PointerType apimodel.State) @! "StatefulSetGet"
      #namespace #name
  {{{ sts_l sts, RET (#sts_l, #interface.nil);
      "%Hvalid'" ∷ ⌜ KObjectV.valid (KObjectV.StatefulSet sts) ⌝ ∗
      "%Hkey_eq" ∷ ⌜ key = StatefulSetV.key sts ⌝ ∗
      "%Hmeta_eq" ∷ ⌜ ObjectMetaV.equiv_except_resource_version sts.(StatefulSetV.ObjectMeta') kmeta ⌝ ∗
      "%Hspec_eq" ∷ ⌜ kspec = sts.(StatefulSetV.Spec') ⌝ ∗
      "Hdeepown_l" ∷ StatefulSetV.deepown_l sts_l sts 1 ∗
      "Hown_meta_frag" ∷ own_meta_frag γ key uid dq kmeta ∗
      "Hown_spec_frag" ∷ own_spec_frag γ key uid dq (ObjectSpecV.StatefulSetSpec kspec)
  }}}.
Proof.
  iIntros (Φ) "(#Hinit & H) HΦ". iNamed "H".
  wp_method_call.
  rewrite /apimodel.State__StatefulSetGetⁱᵐᵖˡ.
  wp_call. wp_auto.
  wp_apply (wp_State__StatefulSetMutGet
    γ l key namespace name uid dq kmeta kspec
    with "[$Hinit $Hisk $Hown_meta_frag $Hown_spec_frag]").
  { iPureIntro. done. }
  iIntros (sts_l sts) "Hpost".
  wp_auto.
  iApply ("HΦ" with "Hpost").
Qed.

Lemma wp_State__DeploymentMutGet γ l key namespace name uid dq kmeta kspec :
  {{{ is_pkg_init apimodel ∗
      "#Hisk" ∷ is_kubernetes γ l ∗
      "%Hkey_def" ∷ ⌜ key = {|
        KKey.Kind' := "Deployment"%go;
        KKey.Namespace' := namespace;
        KKey.Name' := name
      |} ⌝ ∗
      "Hown_meta_frag" ∷ own_meta_frag γ key uid dq kmeta ∗
      "Hown_spec_frag" ∷ own_spec_frag γ key uid dq (ObjectSpecV.DeploymentSpec kspec)
  }}}
    l @! (go.PointerType apimodel.State) @! "DeploymentMutGet"
      #namespace #name
  {{{ d_l d, RET (#d_l, #interface.nil);
      "%Hvalid'" ∷ ⌜ KObjectV.valid (KObjectV.Deployment d) ⌝ ∗
      "%Hkey_eq" ∷ ⌜ key = DeploymentV.key d ⌝ ∗
      "%Hmeta_eq" ∷ ⌜ ObjectMetaV.equiv_except_resource_version d.(DeploymentV.ObjectMeta') kmeta ⌝ ∗
      "%Hspec_eq" ∷ ⌜ kspec = d.(DeploymentV.Spec') ⌝ ∗
      "Hdeepown_l" ∷ DeploymentV.deepown_l d_l d 1 ∗
      "Hown_meta_frag" ∷ own_meta_frag γ key uid dq kmeta ∗
      "Hown_spec_frag" ∷ own_spec_frag γ key uid dq (ObjectSpecV.DeploymentSpec kspec)
  }}}.
Proof.
  iIntros (Φ) "(#Hinit & H) HΦ". iNamed "H". subst key.
  wp_method_call.
  rewrite /apimodel.State__DeploymentMutGetⁱᵐᵖˡ.
  wp_call. wp_auto.
  wp_apply (wp_State__get_some γ l
    {| KKey.Kind' := "Deployment"%go;
       KKey.Namespace' := namespace;
       KKey.Name' := name |}
    uid dq kmeta (Some (ObjectSpecV.DeploymentSpec kspec)) None
    with "[$Hinit $Hisk $Hown_meta_frag $Hown_spec_frag]").
  iIntros (i kobj) "Hpost". iNamed "Hpost".
  iDestruct "Hpost" as "((Hown_spec_frag & %Hspec_eq) & _)".
  destruct kobj as [pod|rs|pvc|sts|d];
    try solve [simpl in Hspec_eq; done].
  simpl in Hvalid', Hkey_eq, Hmeta_eq, Hspec_eq.
  assert (Hspec_eq' : kspec = d.(DeploymentV.Spec')) by congruence.
  clear Hspec_eq. rename Hspec_eq' into Hspec_eq.
  iDestruct "Hdeepown_i" as (d_l) "[%Hi Hdeepown_l]".
  wp_auto.
  unfold KObjectV.valid_interface in Hi. rewrite Hi.
  change (go.PointerType api_apps_v1.Deployment)
    with (go.PointerType v1.Deployment).
  cbn [interface.ty interface.v].
  replace (if decide
      (go.PointerType v1.Deployment = go.PointerType v1.Deployment)
    then #d_l else #null)%V with (#d_l)%V by
    (rewrite decide_True; done).
  replace (bool_decide
      (go.PointerType v1.Deployment = go.PointerType v1.Deployment))
    with true by (symmetry; apply bool_decide_eq_true_2; done).
  wp_auto.
  iApply "HΦ". iFrame. iPureIntro. split_and!; done.
Qed.

Lemma wp_State__DeploymentGet γ l key namespace name uid dq kmeta kspec :
  {{{ is_pkg_init apimodel ∗
      "#Hisk" ∷ is_kubernetes γ l ∗
      "%Hkey_def" ∷ ⌜ key = {|
        KKey.Kind' := "Deployment"%go;
        KKey.Namespace' := namespace;
        KKey.Name' := name
      |} ⌝ ∗
      "Hown_meta_frag" ∷ own_meta_frag γ key uid dq kmeta ∗
      "Hown_spec_frag" ∷ own_spec_frag γ key uid dq (ObjectSpecV.DeploymentSpec kspec)
  }}}
    l @! (go.PointerType apimodel.State) @! "DeploymentGet"
      #namespace #name
  {{{ d_l d, RET (#d_l, #interface.nil);
      "%Hvalid'" ∷ ⌜ KObjectV.valid (KObjectV.Deployment d) ⌝ ∗
      "%Hkey_eq" ∷ ⌜ key = DeploymentV.key d ⌝ ∗
      "%Hmeta_eq" ∷ ⌜ ObjectMetaV.equiv_except_resource_version d.(DeploymentV.ObjectMeta') kmeta ⌝ ∗
      "%Hspec_eq" ∷ ⌜ kspec = d.(DeploymentV.Spec') ⌝ ∗
      "Hdeepown_l" ∷ DeploymentV.deepown_l d_l d 1 ∗
      "Hown_meta_frag" ∷ own_meta_frag γ key uid dq kmeta ∗
      "Hown_spec_frag" ∷ own_spec_frag γ key uid dq (ObjectSpecV.DeploymentSpec kspec)
  }}}.
Proof.
  iIntros (Φ) "(#Hinit & H) HΦ". iNamed "H".
  wp_method_call.
  rewrite /apimodel.State__DeploymentGetⁱᵐᵖˡ.
  wp_call. wp_auto.
  wp_apply (wp_State__DeploymentMutGet
    γ l key namespace name uid dq kmeta kspec
    with "[$Hinit $Hisk $Hown_meta_frag $Hown_spec_frag]").
  { iPureIntro. done. }
  iIntros (d_l d) "Hpost".
  wp_auto.
  iApply ("HΦ" with "Hpost").
Qed.

End proof.
