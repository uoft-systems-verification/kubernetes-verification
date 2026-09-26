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

(* Filtering the store's ReplicaSets by this index value is the same as
   filtering them by controller reference. The ReplicaSet analogue of
   [matching_podController_indexed_value_implies_being_children_pods], and the
   step that lets the index be related back to [own_children_frag].

   The string reasoning is shared: [pod_controller_index_key_inj_right] and
   [pod_controller_index_key_inequality1] (string/prefix_suffix.v) are about
   the "ns/Kind/Name/UID" encoding, not about Pods. *)
Lemma matching_replicaSetController_indexed_value_implies_being_children
    rss parent_key parent_uid :
  slash_free parent_key.(KKey.Kind') →
  slash_free parent_key.(KKey.Namespace') →
  slash_free parent_key.(KKey.Name') →
  slash_free parent_uid →
  Forall ReplicaSetV.valid rss →
  filter (λ rs, replicaSetController_indexed_value rs =
    parent_key.(KKey.Namespace') ++ "/"%go ++ parent_key.(KKey.Kind') ++ "/"%go ++
    parent_key.(KKey.Name') ++ "/"%go ++ parent_uid) rss =
  filter (λ rs, obj_parent_ref (KObjectV.ReplicaSet rs) =
    Some (parent_key, parent_uid)) rss.
Proof.
  intros Hparent_kind_sf Hparent_ns_sf Hparent_name_sf Hparent_uid_sf Hrss_valid.
  induction Hrss_valid as [|rs rss Hrs_valid Hrss_valid IH]; simpl; [done|].
  rewrite !filter_cons.
  case_decide as Hindexed.
  - case_decide as Hparent.
    + simpl. f_equal. exact IH.
    + exfalso.
      apply Hparent.
      clear IH Hrss_valid Hparent.
      unfold replicaSetController_indexed_value, meta_parent_ref in Hindexed.
      unfold obj_parent_ref, meta_parent_ref.
      destruct Hrs_valid as (_ & _ & Hmeta_valid & _).
      assert (Hrs_ns_sf :
        slash_free rs.(ReplicaSetV.ObjectMeta').(ObjectMetaV.Namespace')).
      { eapply valid_namespace_slash_free.
        unfold ObjectMetaV.valid in Hmeta_valid. tauto. }
      destruct (ObjectMetaV.OwnerReferences' (ReplicaSetV.ObjectMeta' rs))
        as [orefs|] eqn:Horefs in Hindexed |- *.
      * destruct (list_find (λ oref : OwnerReferenceV.t,
          oref.(OwnerReferenceV.Controller') = Some true) orefs)
          as [[idx oref]|] eqn:Hfind in Hindexed |- *.
        -- pose proof (pod_controller_index_key_inj_right
             rs.(ReplicaSetV.ObjectMeta').(ObjectMetaV.Namespace')
             oref.(OwnerReferenceV.Kind')
             oref.(OwnerReferenceV.Name')
             oref.(OwnerReferenceV.UID')
             parent_key.(KKey.Namespace')
             parent_key.(KKey.Kind')
             parent_key.(KKey.Name')
             parent_uid
             Hrs_ns_sf
             Hparent_ns_sf
             Hparent_kind_sf
             Hparent_name_sf
             Hparent_uid_sf
             Hindexed) as (Hns_eq & Hkind_eq & Hname_eq & Huid_eq).
           unfold obj_parent_ref, meta_parent_ref.
           simpl.
           rewrite Horefs Hfind.
           destruct parent_key as [parent_kind parent_name parent_ns].
           simpl in *.
           subst.
           reflexivity.
        -- exfalso.
           eapply pod_controller_index_key_inequality1;
             [exact Hrs_ns_sf|exact Hparent_ns_sf|].
           exact Hindexed.
      * exfalso.
        eapply pod_controller_index_key_inequality1;
          [exact Hrs_ns_sf|exact Hparent_ns_sf|].
        exact Hindexed.
  - case_decide as Hparent.
    + exfalso.
      apply Hindexed.
      clear IH Hrss_valid Hindexed.
      unfold obj_parent_ref, meta_parent_ref in Hparent.
      unfold replicaSetController_indexed_value, meta_parent_ref.
      simpl.
      destruct (ObjectMetaV.OwnerReferences' (ReplicaSetV.ObjectMeta' rs))
        as [orefs|] eqn:Horefs.
      * destruct (list_find (λ oref : OwnerReferenceV.t,
          oref.(OwnerReferenceV.Controller') = Some true) orefs)
          as [[idx oref]|] eqn:Hfind.
        -- rewrite Horefs Hfind in Hparent |- *.
           inversion Hparent as [[Hkey_eq Huid_eq]]; clear Hparent.
           destruct parent_key as [parent_kind parent_name parent_ns].
           simpl in Hkey_eq, Huid_eq.
           inversion Hkey_eq; subst.
           reflexivity.
        -- rewrite Horefs Hfind in Hparent.
           discriminate.
      * rewrite Horefs in Hparent.
        discriminate.
    + simpl. exact IH.
Qed.

(* What survives a round trip through the store: everything except the
   resource version, which the API server rewrites. Mirrors
   [pod_storage_view], and for the same reason — it is the granularity at
   which the index can relate what it returns to what the caller framed.

   Metadata alone would not be enough here. [deployment_realized] constrains
   ReplicaSet *specs* (template and replica count), so a metadata-only
   permutation could not transfer it from the framed list to the returned
   one — which is exactly what the stability proof has to do. *)
Definition rs_storage_view (rs : ReplicaSetV.t) : ObjectMetaV.t * ObjectSpecV.t :=
  (ObjectMetaV.without_resource_version rs.(ReplicaSetV.ObjectMeta'),
   ObjectSpecV.ReplicaSetSpec rs.(ReplicaSetV.Spec')).

Definition rs_is_living (rs : ReplicaSetV.t) : Prop :=
  rs.(ReplicaSetV.ObjectMeta').(ObjectMetaV.DeletionTimestamp') = None.

(* Generic in the child-reference function, because it is instantiated twice:
   at [living_obj_parent_ref], which is what the children fragment records,
   and at [obj_parent_ref], which is what the index actually filters by. *)
Lemma filter_rs_child_ref_fmap
    (child_ref : KObjectV.t → option (KKey.t * types.UID.t))
    (rss : list ReplicaSetV.t) parent_key parent_uid :
  filter
      (λ obj : KObjectV.t, child_ref obj = Some (parent_key, parent_uid))
      (KObjectV.ReplicaSet <$> rss) =
    KObjectV.ReplicaSet <$>
      filter
        (λ rs, child_ref (KObjectV.ReplicaSet rs) =
          Some (parent_key, parent_uid)) rss.
Proof.
  induction rss as [|rs rss IH]; simpl; [done|].
  rewrite !filter_cons.
  destruct (decide (child_ref (KObjectV.ReplicaSet rs) =
    Some (parent_key, parent_uid))); simpl; by rewrite IH.
Qed.

(* The index's filter, cut down to the living objects, is the children
   fragment's filter. *)
Lemma filter_living_parent_rss (rss : list ReplicaSetV.t) parent_key parent_uid :
  filter rs_is_living
      (filter
        (λ rs, obj_parent_ref (KObjectV.ReplicaSet rs) =
          Some (parent_key, parent_uid)) rss) =
    filter
      (λ rs, living_obj_parent_ref (KObjectV.ReplicaSet rs) =
        Some (parent_key, parent_uid)) rss.
Proof.
  rewrite list_filter_filter.
  apply list_filter_iff. intros rs.
  rewrite cview.living_obj_parent_ref_eq_some.
  unfold rs_is_living. tauto.
Qed.

Lemma rs_storage_view_fmap (rss : list ReplicaSetV.t) :
  kobject_storage_view <$> (KObjectV.ReplicaSet <$> rss) =
    rs_storage_view <$> rss.
Proof.
  induction rss as [|rs rss IH]; simpl; [done|].
  f_equal. exact IH.
Qed.

(* Restricting to ReplicaSet-kinded keys commutes with restricting to a
   parent. [child_pod_state_dom_eq] with the kind changed. *)
Lemma child_rs_state_dom_eq
    (child_ref : KObjectV.t → option (KKey.t * types.UID.t))
    (abs_state : gmap KKey.t KObjectV.t) parent_key parent_uid :
  dom (filter (λ '(_, obj), child_ref obj = Some (parent_key, parent_uid))
    (filter (λ kv, KKey.Kind' kv.1 = ReplicaSetV.kind) abs_state)) =
  filter (λ key, KKey.Kind' key = ReplicaSetV.kind)
    (dom (filter (λ '(_, v), child_ref v = Some (parent_key, parent_uid))
      abs_state)).
Proof.
  apply set_eq; intros k.
  split.
  - intros Hk.
    apply elem_of_dom in Hk as [obj Hlookup].
    apply map_lookup_filter_Some in Hlookup as [Hlookup_rs_state Hparent].
    apply map_lookup_filter_Some in Hlookup_rs_state as [Hlookup_abs Hkind].
    apply elem_of_filter.
    split; [done|].
    apply elem_of_dom.
    exists obj. apply map_lookup_filter_Some. split; done.
  - intros Hk.
    apply elem_of_filter in Hk as [Hkind Hk_dom].
    apply elem_of_dom in Hk_dom as [obj Hlookup].
    apply map_lookup_filter_Some in Hlookup as [Hlookup_abs Hparent].
    apply elem_of_dom.
    exists obj.
    apply map_lookup_filter_Some. split; [|done].
    apply map_lookup_filter_Some. split; done.
Qed.

(* The caller's framed list, viewed through [rs_storage_view], is a
   permutation of the store's living children.
   [spec_pods_is_permutation_of_child_pod_state_for_storage_view] with
   [rs_storage_view] for [pod_storage_view]. *)
Lemma spec_rss_is_permutation_of_child_rs_state_for_storage_view
    (child_ref : KObjectV.t → option (KKey.t * types.UID.t))
    (spec_rss : list ReplicaSetV.t) (abs_state : gmap KKey.t KObjectV.t)
    parent_key parent_uid :
  NoDup (ReplicaSetV.key <$> spec_rss) →
  list_to_set (ReplicaSetV.key <$> spec_rss) =
    filter (λ key, KKey.Kind' key = ReplicaSetV.kind)
      (dom (filter
        (λ '(_, obj), child_ref obj = Some (parent_key, parent_uid))
        abs_state)) →
  Forall
    (λ rs, ∃ obj,
      abs_state !! ReplicaSetV.key rs = Some obj ∧
      (KObjectV.objectmeta obj).(ObjectMetaV.UID') =
        rs.(ReplicaSetV.ObjectMeta').(ObjectMetaV.UID') ∧
      ObjectMetaV.equiv_except_resource_version
        (KObjectV.objectmeta obj) rs.(ReplicaSetV.ObjectMeta') ∧
      KObjectV.spec obj = ObjectSpecV.ReplicaSetSpec rs.(ReplicaSetV.Spec'))
    spec_rss →
  rs_storage_view <$> spec_rss ≡ₚ
    kobject_storage_view <$>
      (map_to_list
        (filter
          (λ '(_, obj), child_ref obj = Some (parent_key, parent_uid))
          (filter (λ kv, KKey.Kind' kv.1 = ReplicaSetV.kind) abs_state))).*2.
Proof.
  intros Hnodup Hdom Hlookup.
  set child_rs_state := filter
    (λ '(_, obj), child_ref obj = Some (parent_key, parent_uid))
    (filter (λ kv, KKey.Kind' kv.1 = ReplicaSetV.kind) abs_state).
  assert (Hdom_child :
      list_to_set (ReplicaSetV.key <$> spec_rss) = dom child_rs_state).
  { rewrite /child_rs_state (child_rs_state_dom_eq child_ref).
    exact Hdom. }
  assert (Hentries_nodup :
      NoDup ((map (λ rs, (ReplicaSetV.key rs, rs_storage_view rs))
        spec_rss).*1)).
  { rewrite pair_fmap_keys. exact Hnodup. }
  assert (Hview_map_eq :
      (list_to_map
        (map (λ rs, (ReplicaSetV.key rs, rs_storage_view rs)) spec_rss)
        : gmap KKey.t (ObjectMetaV.t * ObjectSpecV.t)) =
      kobject_storage_view <$> child_rs_state).
  {
    apply map_eq. intros key.
    destruct ((list_to_map
      (map (λ rs, (ReplicaSetV.key rs, rs_storage_view rs)) spec_rss)
      : gmap KKey.t (ObjectMetaV.t * ObjectSpecV.t)) !! key)
      as [view|] eqn:Hview.
    - apply elem_of_list_to_map_2 in Hview as Hin.
      apply list_elem_of_fmap in Hin as (rs & Hpair & Hin).
      inversion Hpair; subst key view.
      rewrite Forall_forall in Hlookup.
      pose proof Hin as Hin_elem.
      rewrite list_elem_of_In in Hin.
      destruct (Hlookup rs Hin) as (obj & Hlookup_abs & Huid & Hmeta & Hspec).
      assert (ReplicaSetV.key rs ∈ dom child_rs_state) as Hkey_child.
      { rewrite -Hdom_child.
        apply elem_of_list_to_set.
        apply list_elem_of_fmap.
        exists rs. split; [done|exact Hin_elem]. }
      apply elem_of_dom in Hkey_child as [obj' Hlookup_child].
      rewrite lookup_fmap Hlookup_child /=.
      apply map_lookup_filter_Some in Hlookup_child as
        [Hlookup_rs_state Hparent].
      apply map_lookup_filter_Some in Hlookup_rs_state as
        [Hlookup_abs' Hkind].
      rewrite Hlookup_abs in Hlookup_abs'. injection Hlookup_abs' as <-.
      unfold rs_storage_view, kobject_storage_view.
      by rewrite Hmeta Hspec.
    - rewrite lookup_fmap.
      destruct (child_rs_state !! key) as [obj|]
        eqn:Hlookup_child; [|reflexivity].
      apply not_elem_of_dom in Hview.
      exfalso. apply Hview.
      rewrite dom_list_to_map_L pair_fmap_keys Hdom_child.
      apply elem_of_dom. exists obj. exact Hlookup_child.
  }
  pose proof (Permutation_sym
    (map_to_list_to_map
      (map (λ rs, (ReplicaSetV.key rs, rs_storage_view rs)) spec_rss)
      Hentries_nodup)) as Hperm_pairs.
  pose proof (Permutation_map snd Hperm_pairs) as Hperm_views.
  replace
    (map snd
      (map (λ rs : ReplicaSetV.t, (ReplicaSetV.key rs, rs_storage_view rs))
        spec_rss))
    with (rs_storage_view <$> spec_rss) in Hperm_views.
  2: {
    change
      (map snd
        (map (λ rs : ReplicaSetV.t, (ReplicaSetV.key rs, rs_storage_view rs))
          spec_rss))
      with
        ((map (λ rs : ReplicaSetV.t, (ReplicaSetV.key rs, rs_storage_view rs))
          spec_rss).*2).
    symmetry. apply pair_fmap_values.
  }
  change
    ((map_to_list
      (list_to_map
        (map (λ rs : ReplicaSetV.t, (ReplicaSetV.key rs, rs_storage_view rs))
          spec_rss)
        : gmap KKey.t (ObjectMetaV.t * ObjectSpecV.t))).*2)
    with
      (snd <$> map_to_list
        (list_to_map
          (map (λ rs : ReplicaSetV.t, (ReplicaSetV.key rs, rs_storage_view rs))
            spec_rss)
          : gmap KKey.t (ObjectMetaV.t * ObjectSpecV.t)))
    in Hperm_views.
  rewrite Hview_map_eq in Hperm_views.
  replace
    (map snd (map_to_list (kobject_storage_view <$> child_rs_state)))
    with (kobject_storage_view <$> (map_to_list child_rs_state).*2)
    in Hperm_views.
  2: symmetry; apply snd_fmap_map_to_list_fmap.
  exact Hperm_views.
Qed.

(* What the index returns, cut down to the living objects, is the caller's
   framed list up to storage view. Ported from
   [pods_is_permutation_of_spec_pods_for_storage_view]. *)
Lemma rss_is_permutation_of_spec_rss_for_storage_view
    (child_ref : KObjectV.t → option (KKey.t * types.UID.t))
    (rss spec_rss : list ReplicaSetV.t) (abs_state : gmap KKey.t KObjectV.t)
    parent_key parent_uid :
  KObjectV.ReplicaSet <$> rss ≡ₚ
    (map_to_list
      (filter (λ kv, KKey.Kind' kv.1 = ReplicaSetV.kind) abs_state)).*2 →
  NoDup (ReplicaSetV.key <$> spec_rss) →
  list_to_set (ReplicaSetV.key <$> spec_rss) =
    filter (λ key, KKey.Kind' key = ReplicaSetV.kind)
      (dom (filter
        (λ '(_, obj), child_ref obj = Some (parent_key, parent_uid))
        abs_state)) →
  Forall
    (λ rs, ∃ obj,
      abs_state !! ReplicaSetV.key rs = Some obj ∧
      (KObjectV.objectmeta obj).(ObjectMetaV.UID') =
        rs.(ReplicaSetV.ObjectMeta').(ObjectMetaV.UID') ∧
      ObjectMetaV.equiv_except_resource_version
        (KObjectV.objectmeta obj) rs.(ReplicaSetV.ObjectMeta') ∧
      KObjectV.spec obj = ObjectSpecV.ReplicaSetSpec rs.(ReplicaSetV.Spec'))
    spec_rss →
  rs_storage_view <$>
    filter
      (λ rs, child_ref (KObjectV.ReplicaSet rs) =
        Some (parent_key, parent_uid)) rss ≡ₚ
  rs_storage_view <$> spec_rss.
Proof.
  intros Hperm Hnodup Hdom Hlookup.
  transitivity
    (kobject_storage_view <$>
      (map_to_list
        (filter
          (λ '(_, obj), child_ref obj = Some (parent_key, parent_uid))
          (filter (λ kv, KKey.Kind' kv.1 = ReplicaSetV.kind) abs_state))).*2).
  - set rs_state := filter
      (λ kv, KKey.Kind' kv.1 = ReplicaSetV.kind) abs_state.
    set child_rs_state := filter
      (λ '(_, obj), child_ref obj = Some (parent_key, parent_uid))
      rs_state.
    assert (Hrs_perm :
      KObjectV.ReplicaSet <$>
        filter
          (λ rs, child_ref (KObjectV.ReplicaSet rs) =
            Some (parent_key, parent_uid)) rss ≡ₚ
      (map_to_list child_rs_state).*2).
    { pose proof (perm_filter
        (λ obj : KObjectV.t,
          child_ref obj = Some (parent_key, parent_uid))
        (KObjectV.ReplicaSet <$> rss) (map_to_list rs_state).*2 Hperm)
        as Hfiltered.
      rewrite filter_rs_child_ref_fmap in Hfiltered.
      eapply Permutation_trans; [exact Hfiltered|].
      apply filter_map_to_list_values_perm. }
    pose proof (Permutation_map kobject_storage_view Hrs_perm)
      as Hview_perm.
    transitivity
      (kobject_storage_view <$>
        (KObjectV.ReplicaSet <$>
          filter
            (λ rs, child_ref (KObjectV.ReplicaSet rs) =
              Some (parent_key, parent_uid)) rss)).
    + rewrite rs_storage_view_fmap. reflexivity.
    + exact Hview_perm.
  - apply Permutation_sym.
    exact (spec_rss_is_permutation_of_child_rs_state_for_storage_view
      child_ref spec_rss abs_state parent_key parent_uid Hnodup Hdom Hlookup).
Qed.

(* Living children plus terminating children are all the children. The
   ReplicaSet analogue of [living_terminating_child_pod_keys_partition]. This
   is what turns "[terminating_children.No], so no terminating children" into
   "the children fragment already lists every child the index can return". *)
Lemma living_terminating_child_rs_keys_partition
    (abs_state : gmap KKey.t KObjectV.t) parent_key parent_uid :
  filter (λ key, KKey.Kind' key = ReplicaSetV.kind)
      (dom (filter
        (λ '(_, obj), living_obj_parent_ref obj =
          Some (parent_key, parent_uid)) abs_state)) ∪
    filter (λ key, KKey.Kind' key = ReplicaSetV.kind)
      (dom (filter
        (λ '(_, obj), terminating_children.terminating_obj_parent_ref obj =
          Some (parent_key, parent_uid)) abs_state)) =
  filter (λ key, KKey.Kind' key = ReplicaSetV.kind)
    (dom (filter
      (λ '(_, obj), obj_parent_ref obj = Some (parent_key, parent_uid))
      abs_state)).
Proof.
  apply set_eq. intros key.
  rewrite elem_of_union !elem_of_filter.
  split.
  - intros [[Hkind Hliving]|[Hkind Hterminating]].
    + split; [exact Hkind|].
      apply elem_of_dom in Hliving as [obj Hlookup].
      apply map_lookup_filter_Some in Hlookup as [Hlookup Hparent].
      apply elem_of_dom. exists obj.
      apply map_lookup_filter_Some. split; [exact Hlookup|].
      apply cview.living_obj_parent_ref_eq_some in Hparent.
      destruct Hparent as [_ Hparent]. exact Hparent.
    + split; [exact Hkind|].
      apply elem_of_dom in Hterminating as [obj Hlookup].
      apply map_lookup_filter_Some in Hlookup as [Hlookup Hparent].
      apply elem_of_dom. exists obj.
      apply map_lookup_filter_Some. split; [exact Hlookup|].
      apply terminating_children.terminating_obj_parent_ref_eq_some in Hparent.
      destruct Hparent as [_ Hparent]. exact Hparent.
  - intros [Hkind Hparent].
    apply elem_of_dom in Hparent as [obj Hlookup].
    apply map_lookup_filter_Some in Hlookup as [Hlookup Hparent].
    destruct ((KObjectV.objectmeta obj).(ObjectMetaV.DeletionTimestamp'))
      as [deletion_timestamp|] eqn:Hdeletion_timestamp.
    + right. split; [exact Hkind|].
      apply elem_of_dom. exists obj.
      apply map_lookup_filter_Some. split; [exact Hlookup|].
      unfold terminating_children.terminating_obj_parent_ref.
      rewrite Hdeletion_timestamp. exact Hparent.
    + left. split; [exact Hkind|].
      apply elem_of_dom. exists obj.
      apply map_lookup_filter_Some. split; [exact Hlookup|].
      unfold cview.living_obj_parent_ref.
      rewrite Hdeletion_timestamp. exact Hparent.
Qed.

(* Distinct UIDs, read off the store invariant rather than the fragments.
   [own_meta_frag]s at different keys constrain independent entries, so a
   caller holding only fragments cannot derive this; the unique-UID clause of
   the store invariant in algebra/kview.v states it, and the index reads under
   the invariant. *)
Lemma rs_uid_nodup (rss : list ReplicaSetV.t)
    (abs_state : gmap KKey.t KObjectV.t) :
  KObjectV.ReplicaSet <$> rss ≡ₚ
    (map_to_list
      (filter (λ kv, KKey.Kind' kv.1 = ReplicaSetV.kind) abs_state)).*2 →
  NoDup (ReplicaSetV.key <$> rss) →
  (∀ k obj, abs_state !! k = Some obj →
    k = KObjectV.key obj ∧
    map_Forall (λ k' obj',
      (KObjectV.objectmeta obj).(ObjectMetaV.UID') =
        (KObjectV.objectmeta obj').(ObjectMetaV.UID') → k = k') abs_state) →
  NoDup ((λ rs, rs.(ReplicaSetV.ObjectMeta').(ObjectMetaV.UID')) <$> rss).
Proof.
  intros Hperm Hkey_nodup Hvalid.
  assert (Hin : ∀ rs, rs ∈ rss →
      abs_state !! ReplicaSetV.key rs = Some (KObjectV.ReplicaSet rs)).
  { intros rs Hrs.
    assert (KObjectV.ReplicaSet rs ∈
      (map_to_list
        (filter (λ kv, KKey.Kind' kv.1 = ReplicaSetV.kind) abs_state)).*2)
      as Hobj.
    { rewrite -Hperm. apply list_elem_of_fmap_2. exact Hrs. }
    apply list_elem_of_fmap in Hobj as ([k obj] & Hobj & Hentry).
    simpl in Hobj. subst obj.
    apply elem_of_map_to_list in Hentry.
    apply map_lookup_filter_Some in Hentry as [Hlookup _].
    destruct (Hvalid k (KObjectV.ReplicaSet rs) Hlookup) as [Hk _].
    simpl in Hk. subst k. exact Hlookup. }
  apply NoDup_alt. intros i j uid Hi Hj.
  rewrite list_lookup_fmap in Hi. rewrite list_lookup_fmap in Hj.
  destruct (rss !! i) as [rs1|] eqn:Hrs1; simpl in Hi; [|discriminate].
  destruct (rss !! j) as [rs2|] eqn:Hrs2; simpl in Hj; [|discriminate].
  injection Hi as Hi. injection Hj as Hj.
  assert (ReplicaSetV.key rs1 = ReplicaSetV.key rs2) as Hkey.
  { pose proof (Hin rs1 (list_elem_of_lookup_2 _ _ _ Hrs1)) as H1.
    pose proof (Hin rs2 (list_elem_of_lookup_2 _ _ _ Hrs2)) as H2.
    destruct (Hvalid _ _ H1) as [_ Huniq].
    apply (Huniq (ReplicaSetV.key rs2) (KObjectV.ReplicaSet rs2) H2).
    simpl. rewrite Hi Hj. reflexivity. }
  rewrite ->NoDup_alt in Hkey_nodup.
  apply (Hkey_nodup i j (ReplicaSetV.key rs1)); rewrite list_lookup_fmap.
  - rewrite Hrs1. reflexivity.
  - rewrite Hrs2 /=. by rewrite Hkey.
Qed.

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
(* The atomic-update form, and the Hoare triple built on it.

   Same layering as the Pod chain in by_index_pod_controller.v: the semantic
   work lives in the [_au] lemma, proved once against inv.v, and the triple
   below is a thin wrapper that [iApply]s it. The Pod file has several such
   wrappers; this file needs one.

   Simpler than the Pod version in two ways, both consequences of the
   Deployment controller never deleting ReplicaSets: no deletion observations,
   and no [include_specs] switch, because the only caller wants specs.

   The living/terminating distinction does not go away, because it is baked
   into the ghost state rather than introduced by the controller.
   [own_children_frag] records the keys of the *living* children, and
   [own_meta_frag] can only be held for an object with no deletion timestamp.
   The caller's framed list is therefore always the living children, while
   [index_of] filters by [obj_parent_ref], which is blind to deletion
   timestamps and so returns terminating children too. So the storage-view
   permutation is stated unconditionally only over [filter rs_is_living rss'],
   and over the whole list only when [has_terminating_children] is
   [terminating_children.No], as in the Pod atomic update.

   This file exists only because [filterReplicaSetsByOwner] fetches through an
   index instead of listing. If the model's listing specifications are given
   fragments and the controller goes back to the upstream listing shape, this
   file and the [ReplicaSetControllerIndex] constant both disappear. *)

Local Lemma wp_State__ByIndex_replicaSetController_au γ l indexed_value :
  ∀ Φ,
  ( is_pkg_init apimodel ∗
    is_kubernetes γ l ∗
    |={⊤,∅}=> ∃ rss rs_dqs has_terminating_children parent_key parent_uid
        children_keys children_dq,
      "Hown_meta_frags" ∷ ([∗ list] rs;rs_dq ∈ rss;rs_dqs,
        own_meta_frag γ (ReplicaSetV.key rs)
          rs.(ReplicaSetV.ObjectMeta').(ObjectMetaV.UID') rs_dq
          rs.(ReplicaSetV.ObjectMeta')) ∗
      "Hown_spec_frags" ∷ ([∗ list] rs;rs_dq ∈ rss;rs_dqs,
        own_spec_frag γ (ReplicaSetV.key rs)
          rs.(ReplicaSetV.ObjectMeta').(ObjectMetaV.UID') rs_dq
          (ObjectSpecV.ReplicaSetSpec rs.(ReplicaSetV.Spec'))) ∗
      "Hown_children_frag" ∷ own_children_frag γ parent_key parent_uid
        children_dq children_keys ∗
      "Hown_terminating_children_frag" ∷ own_terminating_children_frag γ
        parent_key parent_uid has_terminating_children ∗
      "%Hnodup" ∷ ⌜ NoDup (ReplicaSetV.key <$> rss) ⌝ ∗
      "%Hindexed_value_eq" ∷ ⌜ indexed_value = parent_key.(KKey.Namespace') ++ "/"%go ++
        parent_key.(KKey.Kind') ++ "/"%go ++ parent_key.(KKey.Name') ++ "/"%go ++ parent_uid ⌝ ∗
      "%Hdom_eq" ∷ ⌜ list_to_set (ReplicaSetV.key <$> rss) =
        filter (λ key, key.(KKey.Kind') = ReplicaSetV.kind) children_keys ⌝ ∗
      "%Hslash_free" ∷ ⌜ slash_free parent_key.(KKey.Kind') ∧
        slash_free parent_key.(KKey.Namespace') ∧
        slash_free parent_key.(KKey.Name') ∧
        slash_free parent_uid ⌝ ∗
      "Hclose" ∷ (∀ sl interfaces rss' dq',
        sl ↦* (interface.ok <$> interfaces) ∗
        ([∗ list] i;rs ∈ interfaces;rss',
          KObjectV.deepown_i i (KObjectV.ReplicaSet rs) dq') ∗
        (* In a good environment -- no child mid-deletion -- everything the
           index returned is the caller's list. *)
        ⌜ has_terminating_children = terminating_children.No →
            rs_storage_view <$> rss' ≡ₚ rs_storage_view <$> rss ⌝ ∗
        (* And unconditionally, the living half is, whatever the phase. Both
           [own_children_frag] and [own_meta_frag] are about living objects,
           while the index filters by [obj_parent_ref], which is blind to
           deletion timestamps. *)
        ⌜ rs_storage_view <$> filter rs_is_living rss' ≡ₚ
            rs_storage_view <$> rss ⌝ ∗
        ⌜ Forall ReplicaSetV.valid rss' ⌝ ∗
        ⌜ Forall (λ rs, obj_parent_ref (KObjectV.ReplicaSet rs) =
            Some (parent_key, parent_uid)) rss' ⌝ ∗
        ⌜ NoDup (ReplicaSetV.key <$> rss') ⌝ ∗
        ⌜ NoDup ((λ rs,
            rs.(ReplicaSetV.ObjectMeta').(ObjectMetaV.UID')) <$> rss') ⌝ ∗
        ([∗ list] rs;rs_dq ∈ rss;rs_dqs,
          own_meta_frag γ (ReplicaSetV.key rs)
            rs.(ReplicaSetV.ObjectMeta').(ObjectMetaV.UID') rs_dq
            rs.(ReplicaSetV.ObjectMeta')) ∗
        ([∗ list] rs;rs_dq ∈ rss;rs_dqs,
          own_spec_frag γ (ReplicaSetV.key rs)
            rs.(ReplicaSetV.ObjectMeta').(ObjectMetaV.UID') rs_dq
            (ObjectSpecV.ReplicaSetSpec rs.(ReplicaSetV.Spec'))) ∗
        own_children_frag γ parent_key parent_uid children_dq children_keys ∗
        own_terminating_children_frag γ parent_key parent_uid has_terminating_children
          ={∅,⊤}=∗ ▷ Φ (#sl, #interface.nil)%V
      )
  ) -∗ WP l @! (go.PointerType apimodel.State) @! "ByIndex"
        #ReplicaSetV.kind #"replicaSetController"%go #indexed_value {{ Φ }}.
Proof.
  iIntros (Φ) "(#? & #Hkinv & Hau)". iNamed "Hau". iNamed "Hkinv".
  wp_method_call. rewrite /apimodel.State__ByIndexⁱᵐᵖˡ. wp_call.
  wp_apply wp_with_defer as "%defer Hdefer". simpl subst. wp_auto.
  wp_apply wp_Mutex__Lock; [done|]. iIntros "[Hown_Mutex H]".
  iDestruct "H" as (phys_state_l phys_used_uid_l phys_used_rv_l phys_state
    phys_used_uid phys_used_rv abs_state used_uid used_reference) "H".
  iNamedPrefix "H" "Hinv_".
  subst used_uid. wp_auto.
  wp_apply (wp_State__objListLocked_ReplicaSet_NamespaceAll
    with "[$Hinv_Hstate_m_addr $Hinv_Hown_phys $Hinv_Hown_abs
      $Hinv_Hphys_abs_rep]").
  iIntros (sl interfaces all_rss)
    "(Hsl & Hdeepown_i_interfaces & %Hlist_result & %Hall_rss_valid &
      %Hall_rss_nodup & Hinv_Hstate_m_addr & Hinv_Hown_phys & Hinv_Hown_abs &
      Hinv_Hphys_abs_rep)". wp_auto.
  iPoseProof own_slice_nil as "Hslice_nil".
  iPoseProof own_slice_cap_nil as "Hown_slice_nil_cap".
  iDestruct (own_slice_len with "Hsl") as %(Hsl_len1 & Hsl_len2).
  iDestruct (own_slice_wf with "Hsl") as %Hsl_cap.
  iDestruct (big_sepL2_length with "Hdeepown_i_interfaces") as %Hlen_rss.
  set P := (λ rs, replicaSetController_indexed_value rs = indexed_value).
  set I := (∃ (i: w64) (val: interface.t) (sl': slice.t)
      (interfaces': list interface.t_ok) (rss' : list ReplicaSetV.t),
    "Hi_ptr" ∷ i_ptr ↦ i ∗
    "Hval_ptr" ∷ val_ptr ↦ val ∗
    "Hitems_ptr" ∷ items_ptr ↦ sl' ∗
    "Hsl'" ∷ sl' ↦* (interface.ok <$> interfaces') ∗
    "Hlist_pre" ∷ ([∗ list] i;rs ∈ interfaces';rss',
      KObjectV.deepown_i i (KObjectV.ReplicaSet rs) 1) ∗
    "Hlist_post" ∷ ([∗ list] i;rs ∈ (drop (sint.nat i) interfaces);
      (drop (sint.nat i) all_rss),
      KObjectV.deepown_i i (KObjectV.ReplicaSet rs) 1) ∗
    "Hcap_sl'" :: own_slice_cap interface.t sl' (DfracOwn 1) ∗
    "%Hfilter" ∷ ⌜ rss' = filter P (take (sint.nat i) all_rss) ⌝ ∗
    "%Hi" ∷ ⌜ 0 ≤ sint.Z i ≤ sint.Z sl.(slice.len) ⌝
  )%I.
  iAssert (I) with "[i val items Hdeepown_i_interfaces]" as "Hloop_inv".
  { iExists (W64 0), (zero_val interface.t), (zero_val slice.t), [], [].
    iFrame. iFrame "#". rewrite !big_sepL2_nil. done. }
  wp_for "Hloop_inv". wp_if_destruct.
  - assert (∃ this_interface, interfaces !! sint.nat i = Some this_interface)
      as [this_interface Hthis_interface_lookup].
    { apply lookup_lt_is_Some_2.
      rewrite <- (map_length interface.ok interfaces).
      rewrite Hsl_len1. word. }
    destruct (decide (0 ≤ sint.Z i < sint.Z (slice.len sl))) as [_|Hbounds];
      last lia.
    wp_apply (wp_load_slice_index with "[$Hsl]"); [word| | ].
    { rewrite list_lookup_fmap Hthis_interface_lookup. done. }
    iIntros "Hsl". wp_auto.
    assert (∃ this_rs, all_rss !! sint.nat i = Some this_rs)
      as [this_rs Hthis_rs_lookup].
    { apply lookup_lt_is_Some_2.
      rewrite -Hlen_rss.
      rewrite <- (map_length interface.ok interfaces).
      rewrite Hsl_len1. word. }
    iPoseProof (big_sepL2_head_tail _ _ _ this_interface this_rs
      with "Hlist_post") as "[Hthis_i_rs Hother_i_rs]".
    { split. all: rewrite lookup_drop Nat.add_0_r; done. }
    assert (ReplicaSetV.valid this_rs) as Hthis_rs_valid.
    { rewrite Forall_forall in Hall_rss_valid.
      apply Hall_rss_valid.
      rewrite -list_elem_of_In.
      eapply list_elem_of_lookup_2. exact Hthis_rs_lookup. }
    wp_apply (wp_index_of_replicaSetController with "[$Hthis_i_rs]");
      first by iFrame "#".
    iIntros (sl0) "(Hsl0 & Hthis_i_rs)". wp_auto.
    wp_alloc j_ptr as "Hj_ptr". wp_auto.
    iDestruct (own_slice_len with "Hsl0") as %(Hsl0_len1 & _).
    simpl in Hsl0_len1.
    set I0 := (∃ (j: w64) (v: go_string) (sl': slice.t),
      "Hj_ptr" ∷ j_ptr ↦ j ∗
      "Hv_ptr" ∷ v_ptr ↦ v ∗
      "Hitems_ptr" ∷ items_ptr ↦ sl' ∗
      "Hsl'" ∷ sl' ↦* (interface.ok <$> interfaces') ∗
      "Hcap_sl'" :: own_slice_cap interface.t sl' (DfracOwn 1) ∗
      "%Hneg_P" ∷ ⌜ sint.Z j = sint.Z sl0.(slice.len) → ¬ P this_rs ⌝ ∗
      "%Hj" ∷ ⌜ 0 ≤ sint.Z j ≤ sint.Z sl0.(slice.len) ⌝
    )%I.
    iAssert (I0) with "[Hj_ptr v Hitems_ptr Hsl' Hcap_sl']" as "Hloop_inv0".
    { iExists (W64 0), (zero_val go_string), sl'.
      iFrame. iPureIntro. simpl. word. }
    wp_for "Hloop_inv0". wp_if_destruct.
    + destruct (decide (0 ≤ sint.Z j < sint.Z (slice.len sl0)))
        as [_|Hbounds]; last lia.
      wp_apply (wp_load_slice_index with "[$Hsl0]"); [word| | ].
      { iPureIntro. assert (sint.nat j = 0%nat) as -> by word. done. }
      iIntros "Hsl0". wp_auto.
      destruct (bool_decide
        (replicaSetController_indexed_value this_rs = indexed_value))
        as [|] eqn:Heq; wp_auto.
      * wp_apply wp_slice_literal. iSplitR; first done.
        iIntros (sl1) "[Hsl1 _]". wp_auto.
        wp_apply (wp_slice_append with "[$Hsl' $Hcap_sl' $Hsl1]").
        iIntros (sl'') "(Hsl'' & Hcap_sl'' & Hsl1)". wp_auto.
        wp_for_post.
        wp_for_post.
        iAssert (I) with "[Hi_ptr Hval_ptr Hitems_ptr Hsl'' Hlist_pre
          Hthis_i_rs Hother_i_rs Hcap_sl'']" as "Hloop_inv".
        { iExists (word.add i (W64 1)), (interface.ok this_interface), sl'',
            (interfaces' ++ [this_interface]),
            ((filter P (take (sint.nat i) all_rss)) ++ [this_rs]).
          rewrite fmap_app /=.
          iFrame.
          rewrite !big_sepL2_nil.
          assert (sint.nat (word.add i (W64 1)) = S (sint.nat i)) as -> by word.
          rewrite !drop_drop Nat.add_1_r.
          iFrame. iPureIntro. split; [|word].
          rewrite (take_S_r _ _ this_rs Hthis_rs_lookup).
          rewrite list.filter_app. f_equal. unfold filter. simpl.
          destruct (decide (P this_rs)); [done|].
          exfalso. apply n. unfold P. apply bool_decide_eq_true in Heq. done.
        }
        iFrame.
      * wp_for_post.
        iAssert (I0) with "[Hj_ptr Hv_ptr Hitems_ptr Hsl' Hcap_sl']"
          as "Hloop_inv0".
        { iExists (word.add j (W64 1)),
            (replicaSetController_indexed_value this_rs), sl'0.
          iFrame. iPureIntro. split;[|word]. intros. unfold P.
          intros Hcontra. apply bool_decide_eq_false in Heq. done.
        }
        iFrame.
    + wp_for_post.
      iAssert (I) with "[Hi_ptr Hval_ptr Hitems_ptr Hsl' Hlist_pre
        Hthis_i_rs Hother_i_rs Hcap_sl']" as "Hloop_inv".
      { iExists (word.add i (W64 1)), (interface.ok this_interface), sl'0,
          interfaces', (filter P (take (sint.nat i) all_rss)).
        iFrame.
        assert (sint.nat (word.add i (W64 1)) = S (sint.nat i)) as -> by word.
        rewrite !drop_drop Nat.add_1_r.
        iFrame. iPureIntro. split; [|word].
        rewrite (take_S_r _ _ this_rs Hthis_rs_lookup).
        rewrite list.filter_app. unfold filter. simpl.
        assert (¬ P this_rs) as Hnot_P.
        { apply Hneg_P. word. }
        destruct (decide (P this_rs)); [done|].
        rewrite filter_nil app_nil_r. done.
      }
      iFrame.
  - iApply fupd_wp.
    iMod "Hau" as
      (rss rs_dqs has_terminating_children parent_key parent_uid children_keys
        children_dq) "H".
    iDestruct "H" as
      "(Hown_meta_frags & Hown_spec_frags & Hown_children_frag &
        Hown_terminating_children_frag &
        %Hnodup & %Hindexed_value_eq & %Hdom_eq & %Hslash_free & Hclose)".
    assert (sint.nat i = length all_rss) as ->.
    { rewrite -Hlen_rss.
      rewrite <- (map_length interface.ok interfaces).
      rewrite Hsl_len1. word. }
    rewrite take_ge. 1: done.
    iPoseProof (cview.own_auth_frag_valid
      with "Hinv_Hown_children Hown_children_frag")
      as "(%Hchildren_keys_eq & %Hin_used_reference)".
    iPoseProof (terminating_children.own_auth_frag_valid with
      "Hinv_Hown_terminating_children Hown_terminating_children_frag") as
      "%Hterminating_empty".
    iPoseProof (kview.own_auth_valid_forall with "Hinv_Hown_abs") as
      "%Habs_valid".
    iPoseProof (kview.own_meta_spec_list_exists_dqs_sep
      ReplicaSetV.key ReplicaSetV.ObjectMeta'
      (λ rs, ObjectSpecV.ReplicaSetSpec rs.(ReplicaSetV.Spec'))
      rss rs_dqs
      with "Hinv_Hown_abs Hown_meta_frags Hown_spec_frags")
      as "%Hlook_up_full".
    destruct Hslash_free as
      (Hkind_slash_free & Hns_slash_free & Hname_slash_free & Huid_slash_free).
    unfold P. subst indexed_value.
    rewrite (matching_replicaSetController_indexed_value_implies_being_children
      all_rss parent_key parent_uid). all: try done.
    set returned_rss := filter
      (λ rs, obj_parent_ref (KObjectV.ReplicaSet rs) =
        Some (parent_key, parent_uid)) all_rss.
    (* The living half of what the index returned is the caller's list. *)
    assert (Hstorage_perm :
      rs_storage_view <$> filter rs_is_living returned_rss ≡ₚ
        rs_storage_view <$> rss).
    { rewrite /returned_rss filter_living_parent_rss.
      apply (rss_is_permutation_of_spec_rss_for_storage_view
        living_obj_parent_ref all_rss rss abs_state parent_key parent_uid).
      - exact Hlist_result.
      - exact Hnodup.
      - rewrite Hchildren_keys_eq in Hdom_eq. exact Hdom_eq.
      - exact Hlook_up_full. }
    (* In a good environment the children fragment already lists every child
       the index can return, so the permutation covers the whole list. Mirrors
       [wp_State__ByIndex_podController_au]. *)
    assert (Hcombined_dom : has_terminating_children = terminating_children.No →
      list_to_set (ReplicaSetV.key <$> rss) =
        filter (λ key, KKey.Kind' key = ReplicaSetV.kind)
          (dom (filter
            (λ '(_, obj), obj_parent_ref obj = Some (parent_key, parent_uid))
            abs_state))).
    { intros ->. specialize (Hterminating_empty eq_refl).
      rewrite Hdom_eq Hchildren_keys_eq.
      unfold terminating_children.terminating_children in Hterminating_empty.
      assert (Hterminating_rs_keys_empty :
        filter (λ key, KKey.Kind' key = ReplicaSetV.kind)
          (dom (filter
            (λ '(_, obj),
              terminating_children.terminating_obj_parent_ref obj =
                Some (parent_key, parent_uid)) abs_state)) = ∅).
      { rewrite Hterminating_empty. apply set_eq. intros key.
        rewrite elem_of_filter !elem_of_empty. tauto. }
      pose proof (living_terminating_child_rs_keys_partition
        abs_state parent_key parent_uid) as Hpartition.
      transitivity
        (filter (λ key, KKey.Kind' key = ReplicaSetV.kind)
            (dom (filter
              (λ '(_, obj), living_obj_parent_ref obj =
                Some (parent_key, parent_uid)) abs_state)) ∪
          filter (λ key, KKey.Kind' key = ReplicaSetV.kind)
            (dom (filter
              (λ '(_, obj),
                terminating_children.terminating_obj_parent_ref obj =
                  Some (parent_key, parent_uid)) abs_state))).
      - apply set_eq. intros key. rewrite elem_of_union. split.
        + intros Hkey. left. exact Hkey.
        + intros [Hkey|Hkey]; first exact Hkey.
          exfalso. assert (key ∈ (∅ : gset KKey.t)) as Hempty.
          { rewrite -Hterminating_rs_keys_empty. exact Hkey. }
          rewrite elem_of_empty in Hempty. exact Hempty.
      - exact Hpartition. }
    assert (Hfull_perm : has_terminating_children = terminating_children.No →
      rs_storage_view <$> returned_rss ≡ₚ rs_storage_view <$> rss).
    { intros Hquiescent. rewrite /returned_rss.
      apply (rss_is_permutation_of_spec_rss_for_storage_view
        obj_parent_ref all_rss rss abs_state parent_key parent_uid).
      - exact Hlist_result.
      - exact Hnodup.
      - exact (Hcombined_dom Hquiescent).
      - exact Hlook_up_full. }
    (* Distinct UIDs come from the invariant, not from the fragments. *)
    assert (Hvalid_pair : ∀ k obj, abs_state !! k = Some obj →
      k = KObjectV.key obj ∧
      map_Forall (λ k' obj',
        (KObjectV.objectmeta obj).(ObjectMetaV.UID') =
          (KObjectV.objectmeta obj').(ObjectMetaV.UID') → k = k') abs_state).
    { intros k obj Hlookup.
      destruct (Habs_valid k obj Hlookup) as (Hk & _ & _ & _ & Huniq).
      split; [exact Hk|exact Huniq]. }
    pose proof (rs_uid_nodup all_rss abs_state
      Hlist_result Hall_rss_nodup Hvalid_pair) as Huid_nodup_all.
    iMod ("Hclose" $! sl' interfaces' returned_rss (DfracOwn 1)
      with "[Hown_meta_frags Hown_spec_frags Hown_children_frag
        Hown_terminating_children_frag Hsl' Hlist_pre]") as "HΦ".
    { iFrame "Hown_meta_frags Hown_spec_frags Hown_children_frag
        Hown_terminating_children_frag Hsl' Hlist_pre".
      iPureIntro. split_and!.
      - exact Hfull_perm.
      - exact Hstorage_perm.
      - apply Forall_filter. exact Hall_rss_valid.
      - apply Forall_forall. intros rs Hrs.
        rewrite -list_elem_of_In in Hrs.
        apply list_elem_of_filter in Hrs as [Hparent _]. exact Hparent.
      - eapply sublist_NoDup; [exact Hall_rss_nodup|].
        apply fmap_sublist, sublist_filter.
      - eapply sublist_NoDup; [exact Huid_nodup_all|].
        apply fmap_sublist, sublist_filter. }
    iModIntro.
    iCombineNamed "Hinv_*" as "H".
    wp_apply (wp_Mutex__Unlock _ (kubernetes_inv γ l) with "[$Hown_Mutex H]").
    { iNamed "H". iFrame. iFrame "#". iPureIntro. split_and!; done. }
    iApply "HΦ".
Qed.

(* The triple the Deployment controller uses. A thin wrapper over the atomic
   update, in the shape of [wp_State__ByIndex_podController]. *)
Lemma wp_State__ByIndex_replicaSetController γ l indexed_value rss rs_dqs
    parent_key parent_uid children_keys children_dq :
  {{{ is_pkg_init apimodel ∗
      "#Hisk" ∷ is_kubernetes γ l ∗
      "Hown_meta_frags" ∷ ([∗ list] rs;rs_dq ∈ rss;rs_dqs,
        own_meta_frag γ (ReplicaSetV.key rs)
          rs.(ReplicaSetV.ObjectMeta').(ObjectMetaV.UID') rs_dq
          rs.(ReplicaSetV.ObjectMeta')) ∗
      "Hown_spec_frags" ∷ ([∗ list] rs;rs_dq ∈ rss;rs_dqs,
        own_spec_frag γ (ReplicaSetV.key rs)
          rs.(ReplicaSetV.ObjectMeta').(ObjectMetaV.UID') rs_dq
          (ObjectSpecV.ReplicaSetSpec rs.(ReplicaSetV.Spec'))) ∗
      "Hown_children_frag" ∷ own_children_frag γ parent_key parent_uid
        children_dq children_keys ∗
      (* The good-environment premise: no child ReplicaSet is mid-deletion.
         Without it the index can return a terminating child the caller holds
         no fragment for, and [Hview_perm] below would be false. *)
      "Hown_terminating_children_frag" ∷ own_terminating_children_frag γ
        parent_key parent_uid terminating_children.No ∗
      "%Hnodup" ∷ ⌜ NoDup (ReplicaSetV.key <$> rss) ⌝ ∗
      "%Hindexed_value_eq" ∷ ⌜ indexed_value = parent_key.(KKey.Namespace') ++ "/"%go ++
        parent_key.(KKey.Kind') ++ "/"%go ++ parent_key.(KKey.Name') ++ "/"%go ++ parent_uid ⌝ ∗
      "%Hdom_eq" ∷ ⌜ list_to_set (ReplicaSetV.key <$> rss) =
        filter (λ key, key.(KKey.Kind') = ReplicaSetV.kind) children_keys ⌝ ∗
      "%Hslash_free" ∷ ⌜ slash_free parent_key.(KKey.Kind') ∧
        slash_free parent_key.(KKey.Namespace') ∧
        slash_free parent_key.(KKey.Name') ∧
        slash_free parent_uid ⌝
  }}}
    l @! (go.PointerType apimodel.State) @! "ByIndex"
      #ReplicaSetV.kind #"replicaSetController"%go #indexed_value
  {{{ sl interfaces rss' dq', RET (#sl, #interface.nil);
      "Hsl" ∷ sl ↦* (interface.ok <$> interfaces) ∗
      "Hrss" ∷ ([∗ list] i;rs ∈ interfaces;rss',
        KObjectV.deepown_i i (KObjectV.ReplicaSet rs) dq') ∗
      "%Hview_perm" ∷ ⌜ rs_storage_view <$> rss' ≡ₚ
        rs_storage_view <$> rss ⌝ ∗
      "%Hrss_valid" ∷ ⌜ Forall ReplicaSetV.valid rss' ⌝ ∗
      "%Hparent_refs" ∷ ⌜ Forall (λ rs,
        obj_parent_ref (KObjectV.ReplicaSet rs) = Some (parent_key, parent_uid)) rss' ⌝ ∗
      "%Hnodup'" ∷ ⌜ NoDup (ReplicaSetV.key <$> rss') ⌝ ∗
      (* The store's invariant gives every object a distinct UID (the
         unique-UID clause in algebra/kview.v). A caller holding only
         fragments cannot see that, so the index — which reads under the
         invariant — returns it.
         The Deployment controller needs it to tell its new ReplicaSet apart
         from the old ones by UID. *)
      "%Huid_nodup'" ∷ ⌜ NoDup ((λ rs,
          rs.(ReplicaSetV.ObjectMeta').(ObjectMetaV.UID')) <$> rss') ⌝ ∗
      "Hown_meta_frags" ∷ ([∗ list] rs;rs_dq ∈ rss;rs_dqs,
        own_meta_frag γ (ReplicaSetV.key rs)
          rs.(ReplicaSetV.ObjectMeta').(ObjectMetaV.UID') rs_dq
          rs.(ReplicaSetV.ObjectMeta')) ∗
      "Hown_spec_frags" ∷ ([∗ list] rs;rs_dq ∈ rss;rs_dqs,
        own_spec_frag γ (ReplicaSetV.key rs)
          rs.(ReplicaSetV.ObjectMeta').(ObjectMetaV.UID') rs_dq
          (ObjectSpecV.ReplicaSetSpec rs.(ReplicaSetV.Spec'))) ∗
      "Hown_children_frag" ∷ own_children_frag γ parent_key parent_uid
        children_dq children_keys ∗
      "Hown_terminating_children_frag" ∷ own_terminating_children_frag γ
        parent_key parent_uid terminating_children.No
  }}}.
Proof.
  iIntros (Φ) "(#Hinit & H) HΦ". iNamed "H".
  iApply wp_State__ByIndex_replicaSetController_au.
  iFrame "#".
  iApply fupd_mask_intro.
  { Timeout 10 set_solver. }
  iIntros "Hmask".
  iExists rss, rs_dqs, terminating_children.No, parent_key, parent_uid, children_keys,
    children_dq.
  simpl. iFrame "%". iFrame.
  iIntros (sl interfaces rss_ret dq') "Hpost".
  iDestruct "Hpost" as
    "(Hsl & Hrss & %Hfull_perm & %Hliving_perm & %Hrss_valid & %Hparent_refs &
      %Hnodup' & %Huid_nodup' & Hown_meta_frags & Hown_spec_frags &
      Hown_children_frag & Hown_terminating_children_frag)".
  specialize (Hfull_perm eq_refl).
  iMod "Hmask" as "_".
  iModIntro. iNext.
  iApply ("HΦ" $! sl interfaces rss_ret dq').
  iFrame "Hsl Hrss Hown_meta_frags Hown_spec_frags Hown_children_frag
    Hown_terminating_children_frag".
  iFrame "%".
Qed.

End proof.
