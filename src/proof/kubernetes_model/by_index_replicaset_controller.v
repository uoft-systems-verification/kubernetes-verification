From New.proof Require Import prelude empty_ffi.
From New.proof Require Import util.
From New.proof.k8s_io.kubernetes.pkg Require Import controller.
From New.proof.kubernetes_model Require Export inv common list new by_index_pod_controller.

Section proof.
Context `{hG: !heapGS Σ} `{!ffi_semantics _ _}.
Context {sem : go.Semantics} {package_sem : apimodel.Assumptions}.
Context `{!kubernetesModelG Σ}.
Local Set Default Proof Using "All".

(* ReplicaSet owner index: the ReplicaSet analogue of the Pod index in
   by_index_pod_controller.v.

   The Deployment controller fetches its children through State.ByIndex rather
   than by listing a namespace, because the listing specs
   (kubernetes_model/list_weak.v) are fragment-free: they hand back deep copies
   owned independently of the invariant, so nothing relates the returned
   objects to the parent's [own_children_frag]. The index is keyed by exactly
   that owner reference, so it can.

   Simpler than the Pod index in one respect: the Deployment controller never
   deletes ReplicaSets, so there is no [own_deletion_observed_frag] and no
   analogue of [terminating_pods]. *)

Definition replicaSetController_indexed_value (rs : ReplicaSetV.t) : go_string :=
  match meta_parent_ref rs.(ReplicaSetV.ObjectMeta') with
  | Some (parent_key, parent_uid) =>
    rs.(ReplicaSetV.ObjectMeta').(ObjectMetaV.Namespace') ++ "/"%go ++
    parent_key.(KKey.Kind') ++ "/"%go ++ parent_key.(KKey.Name') ++ "/"%go ++ parent_uid
  | None => rs.(ReplicaSetV.ObjectMeta').(ObjectMetaV.Namespace')
  end.

(* The ReplicaSet counterpart of [wp_index_of_podController]: the index key
   is upstream's [controller.PodControllerIndexKey] applied to the
   ReplicaSet's namespace and controller reference. *)
Lemma wp_index_of_replicaSetController i rs dq:
  {{{ is_pkg_init apimodel ∗
      "%Hvalid" ∷ ⌜ ReplicaSetV.valid rs ⌝ ∗
      "Hrs" ∷ KObjectV.deepown_i i (KObjectV.ReplicaSet rs) dq
  }}}
    @! apimodel.index_of #"replicaSetController"%go #(interface.ok i)
  {{{ sl, RET (#sl, #interface.nil);
      sl ↦* [replicaSetController_indexed_value rs] ∗
      KObjectV.deepown_i i (KObjectV.ReplicaSet rs) dq
  }}}.
Proof.
  wp_start as "H". iNamed "H".
  iAssert (is_pkg_init v1 ∗ is_pkg_init controller)%I as
    "(#Hmeta_init & #Hcontroller_init)".
  { iSplit; iPkgInit. }
  iDestruct "Hrs" as (rs_l) "[%Hi Hrs]".
  pose proof Hi as Hrs_interface.
  unfold KObjectV.valid_interface in Hi.
  destruct Hi as [Hi Hobject]. subst i.
  wp_auto.
  rewrite decide_True;
    [change (go.PointerType api_apps_v1.ReplicaSet) with
      (go.PointerType v1.ReplicaSet); reflexivity|].
  wp_auto.
  rewrite bool_decide_true;
    [change (go.PointerType api_apps_v1.ReplicaSet) with
      (go.PointerType v1.ReplicaSet); reflexivity|].
  wp_auto.
  iPoseProof (ReplicaSetV.deepown_l_split with "Hrs") as
    "(%Hrs_l_nonnull & Hrs_type & Hrs_meta_l & Hrs_spec & Hrs_status)".
  iDestruct "Hrs_meta_l" as (rs_meta_c) "[Hrs_meta_l Hrs_meta]".
  iDestruct (struct_fields_split (V:=v1.ObjectMeta.t) with
    "Hrs_meta_l") as "[Hrs_meta_fields %Hrs_meta_nonnull]".
  iNamedPrefix "Hrs_meta_fields" "Hrs_meta_field_".
  iNamedPrefix "Hrs_meta" "Hrs_meta_deepown_".
  wp_auto.
  rewrite Hrs_meta_deepown_Hdeepown_namespace.
  iCombineNamed "Hrs_meta_field_*" as "Hrs_meta_fields".
  iAssert (typed_pointsto_def (ReplicaSetV.objectmeta_ptr rs_l) rs_meta_c dq)
    with "[Hrs_meta_fields]" as "Hrs_meta_l".
  { iNamed "Hrs_meta_fields". simpl. rewrite /named.
    rewrite Hrs_meta_deepown_Hdeepown_namespace. iFrame. }
  iDestruct (struct_fields_combine (V:=v1.ObjectMeta.t)
    (ReplicaSetV.objectmeta_ptr rs_l) rs_meta_c dq Hrs_meta_nonnull with
    "Hrs_meta_l") as "Hrs_meta_l".
  iCombineNamed "Hrs_meta_deepown_*" as "Hrs_meta".
  iAssert (ObjectMetaV.deepown rs_meta_c rs.(ReplicaSetV.ObjectMeta') dq)
    with "[Hrs_meta]" as "Hrs_meta".
  { iNamed "Hrs_meta". rewrite /ObjectMetaV.deepown /named.
    iFrame. iFrame "%". }
  iAssert (ObjectMetaV.deepown_l (ReplicaSetV.objectmeta_ptr rs_l)
      rs.(ReplicaSetV.ObjectMeta') dq) with "[Hrs_meta_l Hrs_meta]" as
      "Hrs_meta_l".
  { iExists rs_meta_c. iFrame. }
  iPoseProof (ReplicaSetV.deepown_l_restore _ _ _ Hrs_l_nonnull with
    "[$Hrs_type $Hrs_meta_l $Hrs_spec $Hrs_status]") as "Hrs".
  wp_bind (@! v1.GetControllerOf
    #(interface.mk_ok (go.PointerType api_apps_v1.ReplicaSet) #rs_l))%E.
  wp_apply (wp_GetControllerOf_kobject_exact
    (interface.mk_ok (go.PointerType api_apps_v1.ReplicaSet) #rs_l)
    (interface.mk (go.PointerType api_apps_v1.ReplicaSet) #rs_l)
    rs_l (KObjectV.ReplicaSet rs) dq with
    "[$Hmeta_init $Hrs //]").
  iIntros (controller_ref_l) "(Hrs & Hcontroller_ref)".
  wp_pures.
  iDestruct "Hcontroller_ref" as "[%Hcontroller_ref|Hcontroller_ref]".
  - destruct Hcontroller_ref as [Hcontroller_ref_null Hparent_none].
    subst controller_ref_l.
    wp_apply (controller.wp_PodControllerIndexKey_nil with
      "[$Hcontroller_init]").
    wp_apply wp_slice_literal. iSplitR; first done.
    iIntros (sl_ptr) "[Hsl _]". wp_auto.
    iApply ("HΦ" $! (slice.mk sl_ptr (W64 1) (W64 1))).
    unfold replicaSetController_indexed_value. rewrite Hparent_none.
    iFrame "Hsl". iExists rs_l. iFrame. done.
  - iDestruct "Hcontroller_ref" as (controller_ref)
      "(%Hcontroller_ref & Hcontroller_ref)".
    destruct Hcontroller_ref as
      [Hcontroller_ref_nonnull Hcontroller_ref_of].
    iDestruct "Hcontroller_ref" as (controller_ref_c)
      "[Hcontroller_ref_l Hcontroller_ref]".
    iNamedPrefix "Hcontroller_ref" "Hcontroller_ref_deepown_".
    wp_apply (controller.wp_PodControllerIndexKey with
      "[$Hcontroller_init $Hcontroller_ref_l]").
    iIntros (index_key) "%Hindex_key". wp_auto.
    wp_apply wp_slice_literal. iSplitR; first done.
    iIntros (sl_ptr) "[Hsl _]". wp_auto.
    assert (meta_parent_ref rs.(ReplicaSetV.ObjectMeta') = Some ({|
      KKey.Kind' := controller_ref.(OwnerReferenceV.Kind');
      KKey.Namespace' := rs.(ReplicaSetV.ObjectMeta').(ObjectMetaV.Namespace');
      KKey.Name' := controller_ref.(OwnerReferenceV.Name')
    |}, controller_ref.(OwnerReferenceV.UID'))) as Hparent.
    { destruct Hcontroller_ref_of as
        (owner_references & Howner_references & Hcontroller_ref_in &
          Hcontroller_ref_controller).
      assert (valid_owner_references
        rs.(ReplicaSetV.ObjectMeta').(ObjectMetaV.OwnerReferences')) as
        Hvalid_owner_references.
      { unfold ReplicaSetV.valid, ObjectMetaV.valid in Hvalid. tauto. }
      rewrite Howner_references in Hvalid_owner_references.
      destruct Hvalid_owner_references as [Hcontroller_unique _].
      unfold meta_parent_ref. rewrite Howner_references.
      destruct (list_find
        (λ owner_reference : OwnerReferenceV.t,
          owner_reference.(OwnerReferenceV.Controller') = Some true)
        owner_references) as [[found_i found_ref]|] eqn:Hfind.
      - apply list_find_Some in Hfind as
          (Hfound_lookup & Hfound_controller & _).
        apply list_elem_of_lookup_1 in Hcontroller_ref_in as
          [controller_ref_i Hcontroller_ref_lookup].
        assert (controller_ref_i = found_i) as ->.
        { eapply Hcontroller_unique; eauto. }
        rewrite Hcontroller_ref_lookup in Hfound_lookup.
        injection Hfound_lookup as ->. reflexivity.
      - apply list_find_None in Hfind.
        rewrite Forall_forall in Hfind.
        exfalso. apply (Hfind controller_ref).
        + rewrite -list_elem_of_In. exact Hcontroller_ref_in.
        + exact Hcontroller_ref_controller. }
    iApply ("HΦ" $! (slice.mk sl_ptr (W64 1) (W64 1))).
    unfold replicaSetController_indexed_value. rewrite Hparent Hindex_key. simpl.
    rewrite Hcontroller_ref_deepown_Hdeepown_kind
      Hcontroller_ref_deepown_Hdeepown_name
      Hcontroller_ref_deepown_Hdeepown_uid.
    iFrame "Hsl". iExists rs_l. iFrame. done.
Qed.

End proof.
