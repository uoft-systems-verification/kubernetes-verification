From New.proof Require Import prelude empty_ffi.
From New.proof Require Import util.
From New.proof.kubernetes_model Require Export inv common list new list_weak by_index_pod_controller.

Section proof.
Context `{hG: !heapGS Σ} `{!ffi_semantics _ _}.
Context {sem : go.Semantics} {package_sem : apimodel.Assumptions}.
Context `{!kubernetesModelG Σ}.
Local Set Default Proof Using "All".

(* Listing a namespace's ReplicaSets, related to the ghost state of one parent
   in that namespace. The Deployment controller finds its ReplicaSets the way
   upstream's [getReplicaSetsForDeployment] does: it lists the namespace and
   keeps the ones whose controller reference is the Deployment. The weak
   listing specs in list_weak.v return deep copies unrelated to the ghost
   state, so they cannot tie a listed ReplicaSet to the parent's
   [own_children_frag]; the specs here can.

   The children of a parent in the returned list are
   [rs_children parent_key parent_uid rss]. *)

Definition rs_children parent_key parent_uid (rss : list ReplicaSetV.t) :
    list ReplicaSetV.t :=
  filter (λ rs, obj_parent_ref (KObjectV.ReplicaSet rs) =
    Some (parent_key, parent_uid)) rss.

(* What survives a round trip through the store: everything except the
   resource version, which the API server rewrites. Mirrors
   [pod_storage_view], and for the same reason — it is the granularity at
   which a listing can relate what it returns to what the caller framed.

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
   and at [obj_parent_ref], which is what a listing's children are. *)
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

(* The parent-reference filter, cut down to the living objects, is the children
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

(* What the listing returns, cut down to the parent's children, is the
   caller's framed list up to storage view. [Q] is the listing's filter on
   store entries: it may be narrower than "every ReplicaSet" -- a namespace --
   as long as it keeps every ReplicaSet child of the parent. Ported from
   [pods_is_permutation_of_spec_pods_for_storage_view]. *)
Lemma rss_is_permutation_of_spec_rss_for_storage_view
    (Q : KKey.t * KObjectV.t → Prop) `{!∀ kv, Decision (Q kv)}
    (child_ref : KObjectV.t → option (KKey.t * types.UID.t))
    (rss spec_rss : list ReplicaSetV.t) (abs_state : gmap KKey.t KObjectV.t)
    parent_key parent_uid :
  KObjectV.ReplicaSet <$> rss ≡ₚ (map_to_list (filter Q abs_state)).*2 →
  (∀ kv, Q kv → KKey.Kind' kv.1 = ReplicaSetV.kind) →
  (∀ k obj, abs_state !! k = Some obj → KKey.Kind' k = ReplicaSetV.kind →
    child_ref obj = Some (parent_key, parent_uid) → Q (k, obj)) →
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
  intros Hperm HQ_kind HQ_child Hnodup Hdom Hlookup.
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
        (KObjectV.ReplicaSet <$> rss) (map_to_list (filter Q abs_state)).*2
        Hperm) as Hfiltered.
      rewrite filter_rs_child_ref_fmap in Hfiltered.
      eapply Permutation_trans; [exact Hfiltered|].
      eapply Permutation_trans; [apply filter_map_to_list_values_perm|].
      (* [Q] and "is a ReplicaSet" keep the same children of the parent. *)
      assert (Hchildren_eq :
        filter (λ '(_, obj), child_ref obj = Some (parent_key, parent_uid))
          (filter Q abs_state) = child_rs_state).
      { rewrite /child_rs_state /rs_state.
        apply map_filter_strong_ext_1. intros k obj.
        rewrite !map_lookup_filter_Some /=. split.
        - intros (Hchild & Hlookup_k & HQk).
          split_and!; [exact Hchild|exact Hlookup_k|exact (HQ_kind _ HQk)].
        - intros (Hchild & Hlookup_k & Hkind).
          split_and!; [exact Hchild|exact Hlookup_k|].
          exact (HQ_child k obj Hlookup_k Hkind Hchild). }
      rewrite Hchildren_eq. reflexivity. }
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
   "the children fragment already lists every child the listing can return". *)
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
   the store invariant in algebra/kview.v states it, and the listing reads under
   the invariant. *)
Lemma rs_uid_nodup (Q : KKey.t * KObjectV.t → Prop) `{!∀ kv, Decision (Q kv)}
    (rss : list ReplicaSetV.t) (abs_state : gmap KKey.t KObjectV.t) :
  KObjectV.ReplicaSet <$> rss ≡ₚ (map_to_list (filter Q abs_state)).*2 →
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
      (map_to_list (filter Q abs_state)).*2) as Hobj.
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

(* A child lives in its parent's namespace: [meta_parent_ref] builds the
   parent key from the child's own namespace. *)
Lemma obj_parent_ref_namespace obj parent_key parent_uid :
  obj_parent_ref obj = Some (parent_key, parent_uid) →
  parent_key.(KKey.Namespace') =
    (KObjectV.objectmeta obj).(ObjectMetaV.Namespace').
Proof.
  rewrite /obj_parent_ref /meta_parent_ref.
  destruct (ObjectMetaV.OwnerReferences' _) as [orefs|]; [|done].
  destruct (list_find _ orefs) as [[? oref]|]; [|done].
  by intros [= <- _].
Qed.

(* The objects [filterByLabelSelector] keeps. *)
Definition obj_labels_match (P : option (gmap go_string go_string) → Prop)
    `{!∀ ls, Decision (P ls)} (objs : list KObjectV.t) : list KObjectV.t :=
  filter (λ obj, P (KObjectV.objectmeta obj).(ObjectMetaV.Labels')) objs.

Lemma obj_labels_match_everything objs :
  obj_labels_match everything_matches objs = objs.
Proof.
  induction objs as [|obj objs IH]; [done|].
  rewrite /obj_labels_match filter_cons_True; first exact Logic.I.
  f_equal. exact IH.
Qed.

(* The strong counterpart of [wp_filterByLabelSelector_weak]: it says which
   objects survive, not only that they are valid. *)
Lemma wp_filterByLabelSelector sl interfaces objs
    (selector : labels.Selector.t) P `{!∀ ls, Decision (P ls)} :
  {{{ is_pkg_init apimodel ∗
      "#Hselector" ∷ is_selector selector P ∗
      "Hitems" ∷ sl ↦* (interface.ok <$> interfaces) ∗
      "Hobjects" ∷ ([∗ list] i;obj ∈ interfaces;objs,
        KObjectV.deepown_i i obj 1)
  }}}
    @! apimodel.filterByLabelSelector #sl #selector
  {{{ sl' interfaces', RET (#sl', #interface.nil);
      sl' ↦* (interface.ok <$> interfaces') ∗
      ([∗ list] i;obj ∈ interfaces';obj_labels_match P objs,
        KObjectV.deepown_i i obj 1)
  }}}.
Proof.
  wp_start as "H". iNamed "H".
  iAssert (is_pkg_init code.k8s_io.apimachinery.pkg.api.meta.pkg_id.meta)
    as "#Hmeta_init".
  { iPkgInit. }
  iAssert (is_pkg_init v1) as "#Hv1_init".
  { iPkgInit. }
  wp_auto.
  iDestruct (own_slice_len with "Hitems") as %[Hitems_len Hitems_nonneg].
  rewrite map_length in Hitems_len.
  iDestruct (big_sepL2_length with "Hobjects") as %Hobjects_len.
  iPoseProof (own_slice_nil (V:=interface.t)) as "Hfiltered".
  iPoseProof (own_slice_cap_nil (V:=interface.t)) as "Hfiltered_cap".
  set I := (∃ (i : w64) (val : interface.t) (filtered_sl : slice.t)
      (filtered_interfaces : list interface.t_ok),
    "Hi" ∷ i_ptr ↦ i ∗
    "Hval" ∷ val_ptr ↦ val ∗
    "Hfiltered_items" ∷ filtered_items_ptr ↦ filtered_sl ∗
    "Hfiltered" ∷ filtered_sl ↦* (interface.ok <$> filtered_interfaces) ∗
    "Hfiltered_cap" ∷ own_slice_cap interface.t filtered_sl (DfracOwn 1) ∗
    "Hremaining" ∷ ([∗ list] interface_i;obj ∈
      drop (sint.nat i) interfaces;drop (sint.nat i) objs,
      KObjectV.deepown_i interface_i obj 1) ∗
    "Hfiltered_objects" ∷ ([∗ list] interface_i;obj ∈
      filtered_interfaces;obj_labels_match P (take (sint.nat i) objs),
      KObjectV.deepown_i interface_i obj 1) ∗
    "%Hi_bounds" ∷ ⌜ 0 ≤ sint.Z i ≤ sint.Z (slice.len sl) ⌝)%I.
  iAssert I with
    "[i val filtered_items Hfiltered Hfiltered_cap Hobjects]"
    as "Hloop".
  { iExists (W64 0), (zero_val interface.t), slice.nil, [].
    rewrite !drop_0 take_0 /obj_labels_match filter_nil big_sepL2_nil.
    iFrame "i val filtered_items Hfiltered Hfiltered_cap Hobjects".
    iSplitR; [done|iPureIntro; word]. }
  iClear "Hfiltered Hfiltered_cap".
  wp_for "Hloop". wp_if_destruct.
  -
    assert (0 ≤ sint.Z i < sint.Z (slice.len sl)) as Hibounds by word.
    list_elem interfaces (sint.Z i) as this_interface.
    assert (∃ this_obj, objs !! sint.nat i = Some this_obj) as
      [this_obj Hthis_obj_lookup].
    { apply lookup_lt_is_Some_2. rewrite -Hobjects_len Hitems_len. word. }
    assert ((interface.ok <$> interfaces) !! sint.nat i =
      Some (interface.ok this_interface)) as Hthis_value_lookup.
    { rewrite list_lookup_fmap Hthis_interface_lookup. done. }
    rewrite decide_True.
    { exact Hibounds. }
    wp_apply (wp_load_slice_index (V:=interface.t)
      (t:=go.InterfaceType []) sl (sint.Z i)
      (interface.ok <$> interfaces) (DfracOwn 1)
      (interface.ok this_interface) with "[$Hitems]");
      [word|iPureIntro; exact Hthis_value_lookup|].
    iIntros "Hitems". wp_auto.
    assert (drop (sint.nat i) interfaces =
      this_interface :: drop (S (sint.nat i)) interfaces) as Hdrop_interfaces.
    { apply drop_S. exact Hthis_interface_lookup. }
    assert (drop (sint.nat i) objs =
      this_obj :: drop (S (sint.nat i)) objs) as Hdrop_objs.
    { apply drop_S. exact Hthis_obj_lookup. }
    iEval (rewrite Hdrop_interfaces Hdrop_objs) in "Hremaining".
    iDestruct "Hremaining" as "[Hthis Hremaining]".
    iDestruct "Hthis" as (this_l) "[%Hthis_interface Hthis]".
    wp_apply wp_Accessor; first (iPureIntro; exact Hthis_interface).
    iPoseProof (KObjectV.deepown_l_split with "Hthis") as
      "(%Hthis_l_nonnull & Hthis_type & Hthis_meta & Hthis_spec & Hthis_status)".
    wp_apply (wp_GetLabels_deepown_kobject this_interface this_l this_obj
      with "[$Hv1_init $Hthis_meta]"). 1: done.
    iIntros (labels_l) "[Hlabels Hrestore_meta]". wp_auto.
    wp_bind ((match selector with
      | interface.ok selector_i =>
          Val (#(methods selector_i.(interface.ty) "Matches"
            selector_i.(interface.v)))
      | interface.nil => Panic "nil interface"
      end)
      #(interface.ok (interface.mk labels.Set' #labels_l)))%E.
    iApply (wp_Selector__Matches_resolved selector P labels_l
      (KObjectV.objectmeta this_obj).(ObjectMetaV.Labels') 1
      with "[$Hselector $Hlabels]").
    iNext. iIntros (matches) "(#Hselector_again & Hlabels & %Hmatches)".
    iPoseProof ("Hrestore_meta" with "Hlabels") as "Hthis_meta".
    iPoseProof (KObjectV.deepown_l_restore _ _ _ Hthis_l_nonnull with
      "[$Hthis_type $Hthis_meta $Hthis_spec $Hthis_status]") as "Hthis".
    iAssert (KObjectV.deepown_i this_interface this_obj 1)
      with "[Hthis]" as "Hthis".
    { iExists this_l. iFrame "Hthis". iPureIntro. exact Hthis_interface. }
    destruct matches.
    + wp_auto.
      wp_apply wp_slice_literal. iSplitR; first done.
      iIntros (one_sl) "[Hone _]". wp_auto.
      wp_apply (wp_slice_append with
        "[$Hfiltered $Hfiltered_cap $Hone]").
      iIntros (filtered_sl') "(Hfiltered & Hfiltered_cap & Hone)".
      wp_auto. iApply wp_for_post_do. wp_auto.
      iFrame "HΦ Hitems selector".
      iExists (word.add i (W64 1)), (interface.ok this_interface),
        filtered_sl', (filtered_interfaces ++ [this_interface]).
      assert (sint.nat (word.add i (W64 1)) = S (sint.nat i)) as Hnext by word.
      rewrite Hnext fmap_app /=.
      symmetry in Hmatches. apply bool_decide_eq_true in Hmatches.
      rewrite (take_S_r _ _ this_obj Hthis_obj_lookup) /obj_labels_match
        list.filter_app (filter_singleton_True _ this_obj [] Hmatches).
      iAssert ([∗ list] interface_i;obj ∈ [this_interface];[this_obj],
        KObjectV.deepown_i interface_i obj 1)%I with "[Hthis]" as "Hthis".
      { rewrite big_sepL2_singleton. iFrame. }
      iDestruct (big_sepL2_app with "Hfiltered_objects Hthis")
        as "Hfiltered_objects".
      iFrame. iPureIntro. word.
    + wp_auto. iApply wp_for_post_do. wp_auto.
      iFrame "HΦ Hitems selector".
      iExists (word.add i (W64 1)), (interface.ok this_interface),
        filtered_sl, filtered_interfaces.
      assert (sint.nat (word.add i (W64 1)) = S (sint.nat i)) as -> by word.
      symmetry in Hmatches. apply bool_decide_eq_false in Hmatches.
      rewrite (take_S_r _ _ this_obj Hthis_obj_lookup) /obj_labels_match
        list.filter_app (filter_singleton_False _ this_obj [] Hmatches).
      rewrite app_nil_r.
      iFrame. iPureIntro. word.
  -
    assert (sint.nat i = length interfaces) as Hi_len.
    { rewrite Hitems_len. word. }
    assert (take (sint.nat i) objs = objs) as Htake by (apply take_ge; lia).
    iEval (rewrite Htake) in "Hfiltered_objects".
    iApply ("HΦ" $! filtered_sl filtered_interfaces).
    iFrame.
Qed.

(* The atomic-update form, and the Hoare triples built on it.

   Listing is logically atomic at [objList], which copies the namespace's
   ReplicaSets under the store lock; [ReplicaSetList]'s label filtering and
   type assertions run afterwards, on the copies.

   The listed ReplicaSets are every ReplicaSet in the namespace. Their
   restriction to the parent's children, cut down to the living ones, is the
   caller's framed list whatever [has_terminating_children] is: both
   [own_children_frag] and [own_meta_frag] are about living objects. Their
   whole restriction to the parent's children is the framed list only when no
   child is terminating. *)
Local Lemma wp_State__objList_ReplicaSet_au γ l namespace :
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
      "%Hns_eq" ∷ ⌜ namespace = parent_key.(KKey.Namespace') ⌝ ∗
      "%Hdom_eq" ∷ ⌜ list_to_set (ReplicaSetV.key <$> rss) =
        filter (λ key, key.(KKey.Kind') = ReplicaSetV.kind) children_keys ⌝ ∗
      "Hclose" ∷ (∀ sl interfaces all_rss,
        sl ↦* (interface.ok <$> interfaces) ∗
        ([∗ list] i;rs ∈ interfaces;all_rss,
          KObjectV.deepown_i i (KObjectV.ReplicaSet rs) 1) ∗
        ⌜ has_terminating_children = terminating_children.No →
            rs_storage_view <$> rs_children parent_key parent_uid all_rss ≡ₚ
              rs_storage_view <$> rss ⌝ ∗
        ⌜ rs_storage_view <$>
            filter rs_is_living (rs_children parent_key parent_uid all_rss) ≡ₚ
          rs_storage_view <$> rss ⌝ ∗
        ⌜ Forall ReplicaSetV.valid all_rss ⌝ ∗
        ⌜ Forall ReplicaSetV.extra_valid all_rss ⌝ ∗
        ⌜ NoDup (ReplicaSetV.key <$> all_rss) ⌝ ∗
        ⌜ NoDup ((λ rs,
            rs.(ReplicaSetV.ObjectMeta').(ObjectMetaV.UID')) <$> all_rss) ⌝ ∗
        ([∗ list] rs;rs_dq ∈ rss;rs_dqs,
          own_meta_frag γ (ReplicaSetV.key rs)
            rs.(ReplicaSetV.ObjectMeta').(ObjectMetaV.UID') rs_dq
            rs.(ReplicaSetV.ObjectMeta')) ∗
        ([∗ list] rs;rs_dq ∈ rss;rs_dqs,
          own_spec_frag γ (ReplicaSetV.key rs)
            rs.(ReplicaSetV.ObjectMeta').(ObjectMetaV.UID') rs_dq
            (ObjectSpecV.ReplicaSetSpec rs.(ReplicaSetV.Spec'))) ∗
        own_children_frag γ parent_key parent_uid children_dq children_keys ∗
        own_terminating_children_frag γ parent_key parent_uid
          has_terminating_children
          ={∅,⊤}=∗ ▷ Φ #sl)
  ) -∗ WP l @! (go.PointerType apimodel.State) @! "objList"
        #ReplicaSetV.kind #namespace {{ Φ }}.
Proof.
  iIntros (Φ) "(#Hpkg & #Hisk & Hau)".
  iDestruct "Hisk" as (mu_l) "[#Hmu #Hkinv]".
  iAssert (is_pkg_init sync) as "#Hsync".
  { iPkgInit. }
  wp_method_call. rewrite /apimodel.State__objListⁱᵐᵖˡ. wp_call.
  wp_apply wp_with_defer as "%defer Hdefer". simpl subst. wp_auto.
  wp_apply wp_Mutex__Lock.
  { iFrame "#". }
  iIntros "[Hown_Mutex H]".
  iDestruct "H" as (phys_state_l phys_used_uid_l phys_used_rv_l phys_state
    phys_used_uid phys_used_rv abs_state used_uid used_reference) "H".
  iNamedPrefix "H" "Hinv_". wp_auto.
  wp_apply (wp_State__objListLocked γ l ReplicaSetV.kind namespace
    phys_state_l phys_state abs_state used_uid with
    "[$Hpkg $Hinv_Hstate_m_addr $Hinv_Hown_phys $Hinv_Hown_abs
      $Hinv_Hphys_abs_rep]").
  iIntros (sl interfaces objs)
    "(Hsl & Hobjs & %Hperm & %Hvalid & %Hextra_valid & %Hobjs_nodup &
      Hinv_Hstate_m_addr &
      Hinv_Hown_phys & Hinv_Hown_abs & Hinv_Hphys_abs_rep)".
  iPoseProof (kview.own_auth_valid_forall with "Hinv_Hown_abs")
    as "%Habs_valid".
  assert (Forall (λ obj, KObjectV.kind obj = ReplicaSetV.kind) objs) as Hkind.
  { eapply Permutation_Forall; [symmetry; exact Hperm|].
    apply Forall_forall. intros obj Hobj.
    rewrite <-list_elem_of_In in Hobj.
    apply list_elem_of_fmap_1 in Hobj as [[key obj'] [Hobj_eq Hkey]].
    simpl in Hobj_eq. subst obj'.
    apply elem_of_map_to_list in Hkey.
    apply map_lookup_filter_Some in Hkey as [Hlookup [Hkey_kind _]].
    pose proof (Habs_valid key obj Hlookup) as Hobj_valid.
    destruct Hobj_valid as [Hkey_eq _].
    rewrite Hkey_eq in Hkey_kind.
    destruct obj; exact Hkey_kind. }
  destruct (kobject_list_to_replica_sets objs Hkind) as [all_rss ->].
  rewrite Forall_fmap in Hvalid.
  rewrite Forall_fmap in Hextra_valid.
  change (Forall ReplicaSetV.extra_valid all_rss) in Hextra_valid.
  iEval (rewrite big_sepL2_fmap_r) in "Hobjs".
  assert (NoDup (ReplicaSetV.key <$> all_rss)) as Hall_nodup.
  { rewrite -list_fmap_compose in Hobjs_nodup. exact Hobjs_nodup. }
  iApply fupd_wp.
  iMod "Hau" as
    (rss rs_dqs has_terminating_children parent_key parent_uid children_keys
      children_dq) "H".
  iDestruct "H" as
    "(Hown_meta_frags & Hown_spec_frags & Hown_children_frag &
      Hown_terminating_children_frag & %Hnodup & %Hns_eq & %Hdom_eq & Hclose)".
  iPoseProof (cview.own_auth_frag_valid
    with "Hinv_Hown_children Hown_children_frag")
    as "(%Hchildren_keys_eq & %Hin_used_reference)".
  iPoseProof (terminating_children.own_auth_frag_valid with
    "Hinv_Hown_terminating_children Hown_terminating_children_frag") as
    "%Hterminating_empty".
  iPoseProof (kview.own_meta_spec_list_exists_dqs_sep
    ReplicaSetV.key ReplicaSetV.ObjectMeta'
    (λ rs, ObjectSpecV.ReplicaSetSpec rs.(ReplicaSetV.Spec'))
    rss rs_dqs
    with "Hinv_Hown_abs Hown_meta_frags Hown_spec_frags")
    as "%Hlook_up_full".
  (* Every child of the parent lives in the listed namespace. *)
  assert (Hchild_ns : ∀ k obj, abs_state !! k = Some obj →
    obj_parent_ref obj = Some (parent_key, parent_uid) →
    namespace = k.(KKey.Namespace')).
  { intros k obj Hlookup Hparent.
    destruct (Habs_valid k obj Hlookup) as [Hk_eq _].
    rewrite Hns_eq (obj_parent_ref_namespace _ _ _ Hparent) Hk_eq.
    reflexivity. }
  (* The living children of the listing are the caller's list. *)
  assert (Hstorage_perm :
    rs_storage_view <$>
      filter rs_is_living (rs_children parent_key parent_uid all_rss) ≡ₚ
    rs_storage_view <$> rss).
  { rewrite /rs_children filter_living_parent_rss.
    eapply (rss_is_permutation_of_spec_rss_for_storage_view _
      living_obj_parent_ref all_rss rss abs_state parent_key parent_uid).
    - exact Hperm.
    - intros kv [Hkv _]. exact Hkv.
    - intros k obj Hlookup Hk Hchild. split; [exact Hk|].
      apply cview.living_obj_parent_ref_eq_some in Hchild as [_ Hparent].
      right. by rewrite (Hchild_ns k obj Hlookup Hparent).
    - exact Hnodup.
    - rewrite Hchildren_keys_eq in Hdom_eq. exact Hdom_eq.
    - exact Hlook_up_full. }
  (* In a good environment the children fragment already lists every child,
     so the permutation covers all of them. *)
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
    rs_storage_view <$> rs_children parent_key parent_uid all_rss ≡ₚ
      rs_storage_view <$> rss).
  { intros Hno_terminating. rewrite /rs_children.
    eapply (rss_is_permutation_of_spec_rss_for_storage_view _
      obj_parent_ref all_rss rss abs_state parent_key parent_uid).
    - exact Hperm.
    - intros kv [Hkv _]. exact Hkv.
    - intros k obj Hlookup Hk Hparent. split; [exact Hk|].
      right. by rewrite (Hchild_ns k obj Hlookup Hparent).
    - exact Hnodup.
    - exact (Hcombined_dom Hno_terminating).
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
  pose proof (rs_uid_nodup _ all_rss abs_state Hperm Hall_nodup Hvalid_pair)
    as Huid_nodup.
  iMod ("Hclose" $! sl interfaces all_rss
    with "[Hown_meta_frags Hown_spec_frags Hown_children_frag
      Hown_terminating_children_frag Hsl Hobjs]") as "HΦ".
  { iFrame "Hown_meta_frags Hown_spec_frags Hown_children_frag
      Hown_terminating_children_frag Hsl Hobjs".
    iPureIntro. split_and!; done. }
  iModIntro. wp_auto.
  iCombineNamed "Hinv_*" as "H".
  wp_apply (wp_Mutex__Unlock _ (kubernetes_inv γ l)
    with "[$Hown_Mutex H]").
  { iNamed "H". iFrame. iFrame "#". done. }
  iApply "HΦ".
Qed.

(* The Hoare triple for [objList], in a good environment: no child ReplicaSet
   is mid-deletion. Without that premise the listing can return a terminating
   child the caller holds no fragment for, and [Hview_perm] would be false. *)
Local Lemma wp_State__objList_ReplicaSet γ l namespace rss rs_dqs
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
      "Hown_terminating_children_frag" ∷ own_terminating_children_frag γ
        parent_key parent_uid terminating_children.No ∗
      "%Hnodup" ∷ ⌜ NoDup (ReplicaSetV.key <$> rss) ⌝ ∗
      "%Hns_eq" ∷ ⌜ namespace = parent_key.(KKey.Namespace') ⌝ ∗
      "%Hdom_eq" ∷ ⌜ list_to_set (ReplicaSetV.key <$> rss) =
        filter (λ key, key.(KKey.Kind') = ReplicaSetV.kind) children_keys ⌝
  }}}
    l @! (go.PointerType apimodel.State) @! "objList"
      #ReplicaSetV.kind #namespace
  {{{ sl interfaces all_rss, RET #sl;
      "Hsl" ∷ sl ↦* (interface.ok <$> interfaces) ∗
      "Hrss" ∷ ([∗ list] i;rs ∈ interfaces;all_rss,
        KObjectV.deepown_i i (KObjectV.ReplicaSet rs) 1) ∗
      "%Hview_perm" ∷ ⌜ rs_storage_view <$> rs_children parent_key parent_uid all_rss ≡ₚ
        rs_storage_view <$> rss ⌝ ∗
      "%Hrss_valid" ∷ ⌜ Forall ReplicaSetV.valid all_rss ⌝ ∗
      "%Hrss_extra_valid" ∷ ⌜ Forall ReplicaSetV.extra_valid all_rss ⌝ ∗
      "%Hnodup'" ∷ ⌜ NoDup (ReplicaSetV.key <$> all_rss) ⌝ ∗
      "%Huid_nodup'" ∷ ⌜ NoDup ((λ rs,
          rs.(ReplicaSetV.ObjectMeta').(ObjectMetaV.UID')) <$> all_rss) ⌝ ∗
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
  iApply wp_State__objList_ReplicaSet_au.
  iFrame "#".
  iApply fupd_mask_intro.
  { Timeout 10 set_solver. }
  iIntros "Hmask".
  iExists rss, rs_dqs, terminating_children.No, parent_key, parent_uid,
    children_keys, children_dq.
  iFrame "%". iFrame.
  iIntros (sl interfaces all_rss) "Hpost".
  iDestruct "Hpost" as
    "(Hsl & Hrss & %Hfull_perm & %Hliving_perm & %Hrss_valid &
      %Hrss_extra_valid & %Hnodup' & %Huid_nodup' & Hown_meta_frags &
      Hown_spec_frags & Hown_children_frag & Hown_terminating_children_frag)".
  specialize (Hfull_perm eq_refl).
  iMod "Hmask" as "_".
  iModIntro. iNext.
  iApply ("HΦ" $! sl interfaces all_rss).
  iFrame "Hsl Hrss Hown_meta_frags Hown_spec_frags Hown_children_frag
    Hown_terminating_children_frag".
  iFrame "%".
Qed.

Local Lemma wp_State__objListBySelector_ReplicaSet γ l namespace selector rss
    rs_dqs parent_key parent_uid children_keys children_dq :
  {{{ is_pkg_init apimodel ∗
      "#Hisk" ∷ is_kubernetes γ l ∗
      "#Hselector" ∷ is_selector selector everything_matches ∗
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
        parent_key parent_uid terminating_children.No ∗
      "%Hnodup" ∷ ⌜ NoDup (ReplicaSetV.key <$> rss) ⌝ ∗
      "%Hns_eq" ∷ ⌜ namespace = parent_key.(KKey.Namespace') ⌝ ∗
      "%Hdom_eq" ∷ ⌜ list_to_set (ReplicaSetV.key <$> rss) =
        filter (λ key, key.(KKey.Kind') = ReplicaSetV.kind) children_keys ⌝
  }}}
    l @! (go.PointerType apimodel.State) @! "objListBySelector"
      #ReplicaSetV.kind #namespace #selector
  {{{ sl interfaces all_rss, RET (#sl, #interface.nil);
      "Hsl" ∷ sl ↦* (interface.ok <$> interfaces) ∗
      "Hrss" ∷ ([∗ list] i;rs ∈ interfaces;all_rss,
        KObjectV.deepown_i i (KObjectV.ReplicaSet rs) 1) ∗
      "%Hview_perm" ∷ ⌜ rs_storage_view <$> rs_children parent_key parent_uid all_rss ≡ₚ
        rs_storage_view <$> rss ⌝ ∗
      "%Hrss_valid" ∷ ⌜ Forall ReplicaSetV.valid all_rss ⌝ ∗
      "%Hrss_extra_valid" ∷ ⌜ Forall ReplicaSetV.extra_valid all_rss ⌝ ∗
      "%Hnodup'" ∷ ⌜ NoDup (ReplicaSetV.key <$> all_rss) ⌝ ∗
      "%Huid_nodup'" ∷ ⌜ NoDup ((λ rs,
          rs.(ReplicaSetV.ObjectMeta').(ObjectMetaV.UID')) <$> all_rss) ⌝ ∗
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
  iIntros (Φ) "(#Hpkg & H) HΦ". iNamed "H".
  wp_method_call. rewrite /apimodel.State__objListBySelectorⁱᵐᵖˡ. wp_call.
  wp_auto.
  wp_apply (wp_State__objList_ReplicaSet with
    "[$Hpkg $Hisk $Hown_meta_frags $Hown_spec_frags $Hown_children_frag
      $Hown_terminating_children_frag]").
  { iPureIntro. split_and!; done. }
  iIntros (sl interfaces all_rss) "Hpost". iNamed "Hpost".
  wp_auto.
  iEval (rewrite -(big_sepL2_fmap_r KObjectV.ReplicaSet
    (λ _ i obj, KObjectV.deepown_i i obj 1))) in "Hrss".
  wp_bind (@! apimodel.filterByLabelSelector #sl #selector)%E.
  iApply (wp_filterByLabelSelector sl interfaces
    (KObjectV.ReplicaSet <$> all_rss) selector everything_matches
    with "[$Hpkg $Hselector $Hsl $Hrss]").
  iNext. iIntros (sl' interfaces') "[Hsl' Hrss']".
  rewrite obj_labels_match_everything.
  iEval (rewrite big_sepL2_fmap_r) in "Hrss'".
  wp_auto.
  iApply ("HΦ" $! sl' interfaces' all_rss).
  iFrame. iFrame "%".
Qed.

Local Lemma wp_State__ReplicaSetMutList_children γ l namespace selector rss
    rs_dqs parent_key parent_uid children_keys children_dq :
  {{{ is_pkg_init apimodel ∗
      "#Hisk" ∷ is_kubernetes γ l ∗
      "#Hselector" ∷ is_selector selector everything_matches ∗
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
        parent_key parent_uid terminating_children.No ∗
      "%Hnodup" ∷ ⌜ NoDup (ReplicaSetV.key <$> rss) ⌝ ∗
      "%Hns_eq" ∷ ⌜ namespace = parent_key.(KKey.Namespace') ⌝ ∗
      "%Hdom_eq" ∷ ⌜ list_to_set (ReplicaSetV.key <$> rss) =
        filter (λ key, key.(KKey.Kind') = ReplicaSetV.kind) children_keys ⌝
  }}}
    l @! (go.PointerType apimodel.State) @! "ReplicaSetMutList"
      #namespace #selector
  {{{ sl ptrs all_rss, RET (#sl, #interface.nil);
      "Hsl" ∷ sl ↦* ptrs ∗
      "Hrss" ∷ ([∗ list] ptr;rs ∈ ptrs;all_rss, ReplicaSetV.deepown_l ptr rs 1) ∗
      "%Hview_perm" ∷ ⌜ rs_storage_view <$> rs_children parent_key parent_uid all_rss ≡ₚ
        rs_storage_view <$> rss ⌝ ∗
      "%Hrss_valid" ∷ ⌜ Forall ReplicaSetV.valid all_rss ⌝ ∗
      "%Hrss_extra_valid" ∷ ⌜ Forall ReplicaSetV.extra_valid all_rss ⌝ ∗
      "%Hnodup'" ∷ ⌜ NoDup (ReplicaSetV.key <$> all_rss) ⌝ ∗
      "%Huid_nodup'" ∷ ⌜ NoDup ((λ rs,
          rs.(ReplicaSetV.ObjectMeta').(ObjectMetaV.UID')) <$> all_rss) ⌝ ∗
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
  iIntros (Φ) "(#Hpkg & H) HΦ". iNamed "H".
  wp_method_call. rewrite /apimodel.State__ReplicaSetMutListⁱᵐᵖˡ. wp_call.
  wp_auto.
  wp_apply (wp_State__objListBySelector_ReplicaSet with
    "[$Hpkg $Hisk $Hselector $Hown_meta_frags $Hown_spec_frags
      $Hown_children_frag $Hown_terminating_children_frag]").
  { iPureIntro. split_and!; done. }
  iIntros (objs_sl interfaces all_rss) "Hpost". iNamed "Hpost".
  iDestruct (replica_set_interfaces_to_ptrs with "Hrss") as
    (ptrs) "[%Hinterfaces Hrss]".
  subst interfaces.
  wp_auto.
  iDestruct (own_slice_len with "Hsl") as %(Hobjs_len1 & Hobjs_len2).
  rewrite !map_length in Hobjs_len1.
  iDestruct (own_slice_wf with "Hsl") as %Hobjs_cap.
  iDestruct (big_sepL2_length with "Hrss") as %Hptrs_len.
  wp_apply (wp_slice_make3 (V:=loc) (t:=go.PointerType v1.ReplicaSet)); first word.
  iIntros (rss_sl) "(Hrss_sl & Hrss_cap & %Hrss_cap_eq)".
  wp_auto.
  set I := (∃ (i : w64) (obj : interface.t) (rss_sl' : slice.t)
      (ptrs' : list loc),
    "Hi_ptr" ∷ i_ptr ↦ i ∗
    "Hobj_ptr" ∷ obj_ptr ↦ obj ∗
    "Hrss_ptr" ∷ rss_ptr ↦ rss_sl' ∗
    "Hrss_sl" ∷ rss_sl' ↦* ptrs' ∗
    "Hrss_cap" ∷ own_slice_cap loc rss_sl' (DfracOwn 1) ∗
    "%Hptrs'" ∷ ⌜ ptrs' = take (sint.nat i) ptrs ⌝ ∗
    "%Hi" ∷ ⌜ 0 ≤ sint.Z i ≤ sint.Z (slice.len objs_sl) ⌝)%I.
  iAssert I with "[i obj rss Hrss_sl Hrss_cap]" as "Hloop".
  { iExists (W64 0), (zero_val interface.t), rss_sl, [].
    iFrame. iPureIntro. split; [done|word]. }
  wp_for "Hloop". wp_if_destruct.
  1: {
    destruct (decide (0 ≤ sint.Z i < sint.Z (slice.len objs_sl))) as [_|Hbounds]; last word.
    assert (∃ this_ptr, ptrs !! sint.nat i = Some this_ptr) as
      [this_ptr Hthis_ptr_lookup].
    { apply lookup_lt_is_Some_2. rewrite Hobjs_len1. word. }
    assert ((interface.ok <$> ((λ ptr, interface.mk
        (go.PointerType v1.ReplicaSet) #ptr) <$> ptrs)) !! sint.nat i =
      Some (interface.ok (interface.mk
        (go.PointerType v1.ReplicaSet) #this_ptr))) as Hinterface_lookup.
    { rewrite !list_lookup_fmap Hthis_ptr_lookup. done. }
    wp_apply (wp_load_slice_index (V:=interface.t) (t:=go.InterfaceType [])
      objs_sl (sint.Z i)
      (interface.ok <$> ((λ ptr, interface.mk
        (go.PointerType v1.ReplicaSet) #ptr) <$> ptrs))
      (DfracOwn 1)
      (interface.ok (interface.mk
        (go.PointerType v1.ReplicaSet) #this_ptr)) with "[$Hsl]");
      [word|iPureIntro; exact Hinterface_lookup|].
    iIntros "Hsl". wp_auto.
    rewrite decide_True;
      [change (go.PointerType api_apps_v1.ReplicaSet)
        with (go.PointerType v1.ReplicaSet); reflexivity|].
    wp_auto.
    rewrite bool_decide_true;
      [change (go.PointerType api_apps_v1.ReplicaSet)
        with (go.PointerType v1.ReplicaSet); reflexivity|].
    wp_auto.
    wp_apply wp_slice_literal. iSplitR; first done.
    iIntros (sl_one) "[Hsl_one _]". wp_auto.
    wp_apply (wp_slice_append with "[$Hrss_sl $Hrss_cap $Hsl_one]").
    iIntros (rss_sl'') "(Hrss_sl & Hrss_cap & Hsl_one)". wp_auto.
    iApply wp_for_post_do. wp_auto.
    iFrame "Hsl HΦ Hrss Hown_meta_frags Hown_spec_frags Hown_children_frag
      Hown_terminating_children_frag".
    iExists (word.add i (W64 1)),
      (interface.ok (interface.mk (go.PointerType v1.ReplicaSet) #this_ptr)),
      rss_sl'', (take (sint.nat i) ptrs ++ [this_ptr]).
    iFrame.
    iPureIntro. split.
    + assert (sint.nat (word.add i (W64 1)) = S (sint.nat i)) as -> by word.
      rewrite (take_S_r _ _ this_ptr Hthis_ptr_lookup). done.
    + word. }
  clear I.
  assert (sint.nat i = length ptrs) as Hi_len.
  { rewrite Hobjs_len1. word. }
  assert (take (sint.nat i) ptrs = ptrs) as Htake by (apply take_ge; lia).
  iApply ("HΦ" $! rss_sl' ptrs all_rss).
  iEval (rewrite Htake) in "Hrss_sl".
  iFrame. iFrame "%".
Qed.

(* Listing a namespace's ReplicaSets with an all-matching selector, as the
   Deployment controller does. The returned list is every ReplicaSet in the
   namespace; its restriction to the parent's children is the caller's framed
   list, up to storage view. *)
Lemma wp_State__ReplicaSetList_children γ l namespace selector rss rs_dqs
    parent_key parent_uid children_keys children_dq :
  {{{ is_pkg_init apimodel ∗
      "#Hisk" ∷ is_kubernetes γ l ∗
      "#Hselector" ∷ is_selector selector everything_matches ∗
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
         Without it the listing can return a terminating child the caller
         holds no fragment for, and [Hview_perm] below would be false. *)
      "Hown_terminating_children_frag" ∷ own_terminating_children_frag γ
        parent_key parent_uid terminating_children.No ∗
      "%Hnodup" ∷ ⌜ NoDup (ReplicaSetV.key <$> rss) ⌝ ∗
      "%Hns_eq" ∷ ⌜ namespace = parent_key.(KKey.Namespace') ⌝ ∗
      "%Hdom_eq" ∷ ⌜ list_to_set (ReplicaSetV.key <$> rss) =
        filter (λ key, key.(KKey.Kind') = ReplicaSetV.kind) children_keys ⌝
  }}}
    l @! (go.PointerType apimodel.State) @! "ReplicaSetList"
      #namespace #selector
  {{{ sl ptrs all_rss, RET (#sl, #interface.nil);
      "Hsl" ∷ sl ↦* ptrs ∗
      "Hrss" ∷ ([∗ list] ptr;rs ∈ ptrs;all_rss, ReplicaSetV.deepown_l ptr rs 1) ∗
      "%Hview_perm" ∷ ⌜ rs_storage_view <$> rs_children parent_key parent_uid all_rss ≡ₚ
        rs_storage_view <$> rss ⌝ ∗
      "%Hrss_valid" ∷ ⌜ Forall ReplicaSetV.valid all_rss ⌝ ∗
      "%Hrss_extra_valid" ∷ ⌜ Forall ReplicaSetV.extra_valid all_rss ⌝ ∗
      "%Hnodup'" ∷ ⌜ NoDup (ReplicaSetV.key <$> all_rss) ⌝ ∗
      (* The store's invariant gives every object a distinct UID (the
         unique-UID clause in algebra/kview.v). A caller holding only
         fragments cannot see that, so the listing -- which reads under the
         invariant -- returns it. *)
      "%Huid_nodup'" ∷ ⌜ NoDup ((λ rs,
          rs.(ReplicaSetV.ObjectMeta').(ObjectMetaV.UID')) <$> all_rss) ⌝ ∗
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
  iIntros (Φ) "(#Hpkg & H) HΦ". iNamed "H".
  wp_method_call. rewrite /apimodel.State__ReplicaSetListⁱᵐᵖˡ. wp_call.
  wp_auto.
  wp_apply (wp_State__ReplicaSetMutList_children with
    "[$Hpkg $Hisk $Hselector $Hown_meta_frags $Hown_spec_frags
      $Hown_children_frag $Hown_terminating_children_frag]").
  { iPureIntro. split_and!; done. }
  iIntros (sl ptrs all_rss) "Hpost".
  wp_auto.
  iApply ("HΦ" with "Hpost").
Qed.

End proof.
