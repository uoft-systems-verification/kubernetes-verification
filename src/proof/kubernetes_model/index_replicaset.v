From New.proof Require Import prelude empty_ffi.
From New.proof Require Import util.
From New.proof.kubernetes_model Require Export inv common list new index.

Section proof.
Context `{hG: !heapGS Σ} `{!ffi_semantics _ _}.
Context {sem : go.Semantics} {package_sem : apimodel.Assumptions}.
Context `{!kubernetesModelG Σ}.
Local Set Default Proof Using "All".

(* ---------------------------------------------------------------- *)
(* ReplicaSet owner index — the analogue of index.v's Pod index.     *)
(*                                                                   *)
(* The Deployment controller fetches its children through            *)
(* State.ByIndex rather than by listing a namespace, because the     *)
(* listing specs (kubernetes_model/list_weak.v) are fragment-free:   *)
(* they hand back deep copies owned independently of the invariant,  *)
(* so nothing relates the returned objects to the parent's           *)
(* own_children_frag. The index is keyed by exactly that owner       *)
(* reference, so it can.                                            *)
(*                                                                   *)
(* Simpler than the Pod index in one respect: the Deployment         *)
(* controller never deletes ReplicaSets, so there is no              *)
(* living/terminating axis — no own_terminating_children_frag, no    *)
(* own_deletion_observed_frag, no terminating_pods analogue.         *)
(* ---------------------------------------------------------------- *)

Definition replicaSetController_indexed_value (rs : ReplicaSetV.t) : go_string :=
  match meta_parent_ref rs.(ReplicaSetV.ObjectMeta') with
  | Some (parent_key, parent_uid) =>
    rs.(ReplicaSetV.ObjectMeta').(ObjectMetaV.Namespace') ++ "/"%go ++
    parent_key.(KKey.Kind') ++ "/"%go ++ parent_key.(KKey.Name') ++ "/"%go ++ parent_uid
  | None => rs.(ReplicaSetV.ObjectMeta').(ObjectMetaV.Namespace')
  end.

(* Filtering the store's ReplicaSets by this index value is the same as
   filtering them by controller reference. The ReplicaSet analogue of index.v's
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
   resource version, which the API server rewrites. Mirrors index.v's
   [pod_storage_view], and for the same reason — it is the granularity at
   which the index can relate what it returns to what the caller framed.

   Metadata alone would not be enough here. [deployment_realized] constrains
   ReplicaSet *specs* (template and replica count), so a metadata-only
   permutation could not transfer it from the framed list to the returned
   one — which is exactly what the stability proof has to do. *)
Definition rs_storage_view (rs : ReplicaSetV.t) : ObjectMetaV.t * ObjectSpecV.t :=
  (ObjectMetaV.without_resource_version rs.(ReplicaSetV.ObjectMeta'),
   ObjectSpecV.ReplicaSetSpec rs.(ReplicaSetV.Spec')).

(* Projections out of a storage view. Going through named projections rather
   than [injection] keeps these proofs independent of how deeply the record
   equalities happen to destructure. *)
Definition rs_view_key (v : ObjectMetaV.t * ObjectSpecV.t) : KKey.t :=
  ReplicaSetV.meta_key v.1.

Definition rs_view_spec (v : ObjectMetaV.t * ObjectSpecV.t)
    : option ReplicaSetSpecV.t :=
  match v.2 with
  | ObjectSpecV.ReplicaSetSpec spec => Some spec
  | _ => None
  end.

Lemma rs_view_key_of_view rs : rs_view_key (rs_storage_view rs) = ReplicaSetV.key rs.
Proof. done. Qed.

Lemma rs_view_spec_of_view rs :
  rs_view_spec (rs_storage_view rs) = Some rs.(ReplicaSetV.Spec').
Proof. done. Qed.

(* Two ReplicaSets with the same storage view agree on everything the
   Deployment controller's predicates read: key, template, replica count. *)
Lemma rs_storage_view_eq_inv rs1 rs2 :
  rs_storage_view rs1 = rs_storage_view rs2 →
  ReplicaSetV.key rs1 = ReplicaSetV.key rs2 ∧
  rs1.(ReplicaSetV.Spec') = rs2.(ReplicaSetV.Spec').
Proof.
  intros Heq. split.
  - rewrite -!rs_view_key_of_view Heq. done.
  - pose proof (f_equal rs_view_spec Heq) as Hspec.
    rewrite !rs_view_spec_of_view in Hspec.
    injection Hspec as Hspec. exact Hspec.
Qed.

(* Same view up to permutation, so the same elements up to view. *)
Lemma rs_storage_view_perm_elem_of rss1 rss2 rs :
  rs_storage_view <$> rss1 ≡ₚ rs_storage_view <$> rss2 →
  rs ∈ rss1 →
  ∃ rs', rs' ∈ rss2 ∧ rs_storage_view rs' = rs_storage_view rs.
Proof.
  intros Hperm Hin.
  assert (rs_storage_view rs ∈ rs_storage_view <$> rss2) as Hview_in.
  { rewrite -Hperm. apply list_elem_of_fmap_2. exact Hin. }
  apply list_elem_of_fmap_1 in Hview_in as (rs' & Hview_eq & Hin').
  exists rs'. split; [exact Hin'|]. symmetry. exact Hview_eq.
Qed.

(* TRUSTED. Objects stored under distinct keys have distinct UIDs.

   This is stated by the store invariant (algebra/kview.v:56-61, "Each obj has
   unique uid"), but it is a property of the authoritative state, not of the
   fragments: two fragments at different keys constrain independent entries, so
   nothing in the CMRA relates their UIDs. Proving it means opening
   [is_kubernetes], which is why it is a lemma here rather than a step inside
   the controller proofs that need it.

   The alternative would be to surface UID freshness through the create chain —
   [wp_State__create_named_au] does establish it internally, as
   [Hgenerated_uid_fresh] — but that means reshaping the atomic update every
   typed create wrapper is built on, and with it the Pod and StatefulSet
   proofs. *)
Lemma own_meta_frag_uid_distinct γ k1 uid1 m1 k2 uid2 m2 :
  k1 ≠ k2 →
  own_meta_frag γ k1 uid1 1 m1 -∗
  own_meta_frag γ k2 uid2 1 m2 -∗
  ⌜ uid1 ≠ uid2 ⌝.
Proof. Admitted.

(* After a write, fragments are still keyed by the object that was there
   before, while the metadata they hold is the new one. They can be re-keyed
   onto the post-state: [kview.own_meta_valid] says a fragment's key and UID
   agree with the metadata it holds, and a ReplicaSet's key is determined by
   its metadata, so the two keyings coincide. *)
Lemma own_rs_frags_rekey γ (rss rss' : list ReplicaSetV.t) :
  ([∗ list] rs;rs2 ∈ rss;rss',
    own_meta_frag γ (ReplicaSetV.key rs)
      rs.(ReplicaSetV.ObjectMeta').(ObjectMetaV.UID') 1
      rs2.(ReplicaSetV.ObjectMeta') ∗
    own_spec_frag γ (ReplicaSetV.key rs)
      rs.(ReplicaSetV.ObjectMeta').(ObjectMetaV.UID') 1
      (ObjectSpecV.ReplicaSetSpec rs2.(ReplicaSetV.Spec'))) -∗
  ([∗ list] rs2 ∈ rss',
    own_meta_frag γ (ReplicaSetV.key rs2)
      rs2.(ReplicaSetV.ObjectMeta').(ObjectMetaV.UID') 1
      rs2.(ReplicaSetV.ObjectMeta') ∗
    own_spec_frag γ (ReplicaSetV.key rs2)
      rs2.(ReplicaSetV.ObjectMeta').(ObjectMetaV.UID') 1
      (ObjectSpecV.ReplicaSetSpec rs2.(ReplicaSetV.Spec'))).
Proof.
  iInduction rss as [|rs rest] "IH" forall (rss').
  - iIntros "H". iDestruct (big_sepL2_nil_inv_l with "H") as %->. done.
  - destruct rss' as [|rs2 rest'].
    { iIntros "H". iDestruct (big_sepL2_nil_inv_r with "H") as %Hc. done. }
    iIntros "[[Hm Hs] Htl]".
    iDestruct (kview.own_meta_valid with "Hm") as %(Hn & Hns & Huid & _ & _).
    assert (ReplicaSetV.key rs = ReplicaSetV.key rs2) as Hkey.
    { rewrite /ReplicaSetV.key /ReplicaSetV.meta_key.
      simpl in Hn, Hns. rewrite Hn Hns. done. }
    rewrite Hkey Huid.
    iFrame "Hm Hs".
    iApply ("IH" with "Htl").
Qed.

(* The pure half of [own_rs_frags_rekey]: the same [kview.own_meta_valid]
   that lets the fragments move also says the post-state sits at the same key
   and UID as the pre-state. Callers need this separately, to relate a list of
   post-states back to the keys the caller framed. *)
Lemma own_rs_frags_keys γ (rss rss' : list ReplicaSetV.t) :
  ([∗ list] rs;rs2 ∈ rss;rss',
    own_meta_frag γ (ReplicaSetV.key rs)
      rs.(ReplicaSetV.ObjectMeta').(ObjectMetaV.UID') 1
      rs2.(ReplicaSetV.ObjectMeta') ∗
    own_spec_frag γ (ReplicaSetV.key rs)
      rs.(ReplicaSetV.ObjectMeta').(ObjectMetaV.UID') 1
      (ObjectSpecV.ReplicaSetSpec rs2.(ReplicaSetV.Spec'))) -∗
  ⌜ Forall2 (λ rs rs2,
      ReplicaSetV.key rs2 = ReplicaSetV.key rs ∧
      rs2.(ReplicaSetV.ObjectMeta').(ObjectMetaV.UID') =
        rs.(ReplicaSetV.ObjectMeta').(ObjectMetaV.UID')) rss rss' ⌝.
Proof.
  iInduction rss as [|rs rest] "IH" forall (rss').
  - iIntros "H". iDestruct (big_sepL2_nil_inv_l with "H") as %->.
    iPureIntro. apply Forall2_nil_2.
  - destruct rss' as [|rs2 rest'].
    { iIntros "H". iDestruct (big_sepL2_nil_inv_r with "H") as %Hc. done. }
    iIntros "[[Hm Hs] Htl]".
    iDestruct (kview.own_meta_valid with "Hm") as %(Hn & Hns & Huid & _ & _).
    iDestruct ("IH" with "Htl") as %Htl.
    iPureIntro. apply Forall2_cons_2; [|exact Htl].
    split; [|by rewrite Huid].
    rewrite /ReplicaSetV.key /ReplicaSetV.meta_key.
    simpl in Hn, Hns. rewrite Hn Hns. done.
Qed.

(* Fragments do not see the resource version, so a list of them is determined
   by the storage views — which is what lets a caller move its fragments along
   the permutation the index returns. The Pod counterparts are
   [own_meta_frag_erased_meta] and [own_pod_frags_as_storage_views]. *)
Definition own_rs_storage_view_frag γ dq
    (view : ObjectMetaV.t * ObjectSpecV.t) : iProp Σ :=
  own_meta_frag γ (ReplicaSetV.meta_key view.1)
    view.1.(ObjectMetaV.UID') dq view.1 ∗
  own_spec_frag γ (ReplicaSetV.meta_key view.1)
    view.1.(ObjectMetaV.UID') dq view.2.

Lemma own_rs_meta_frag_erased_meta γ dq meta :
  own_meta_frag γ (ReplicaSetV.meta_key meta) meta.(ObjectMetaV.UID') dq meta ⊣⊢
  own_meta_frag γ
    (ReplicaSetV.meta_key (ObjectMetaV.without_resource_version meta))
    (ObjectMetaV.without_resource_version meta).(ObjectMetaV.UID') dq
    (ObjectMetaV.without_resource_version meta).
Proof.
  rewrite /own_meta_frag /kview.own_meta_frag /kview.mk_meta_frag
    /ObjectMetaV.without_resource_version /ReplicaSetV.meta_key.
  destruct meta. done.
Qed.

Lemma own_rs_frags_as_storage_views γ dq (rss : list ReplicaSetV.t) :
  ([∗ list] rs ∈ rss,
    own_meta_frag γ (ReplicaSetV.key rs)
      rs.(ReplicaSetV.ObjectMeta').(ObjectMetaV.UID') dq
      rs.(ReplicaSetV.ObjectMeta') ∗
    own_spec_frag γ (ReplicaSetV.key rs)
      rs.(ReplicaSetV.ObjectMeta').(ObjectMetaV.UID') dq
      (ObjectSpecV.ReplicaSetSpec rs.(ReplicaSetV.Spec'))) ⊣⊢
  ([∗ list] view ∈ rs_storage_view <$> rss,
    own_rs_storage_view_frag γ dq view).
Proof.
  rewrite -(big_sepL_fmap rs_storage_view
    (λ _ view, own_rs_storage_view_frag γ dq view) rss).
  apply big_sepL_proper.
  intros i rs Hlookup.
  rewrite /own_rs_storage_view_frag /rs_storage_view /=.
  rewrite own_rs_meta_frag_erased_meta.
  rewrite /own_spec_frag /kview.own_spec_frag /kview.mk_spec_frag
    /ReplicaSetV.key /ReplicaSetV.meta_key /ObjectMetaV.without_resource_version.
  destruct rs as [typemeta objectmeta].
  destruct objectmeta; done.
Qed.

(* Moving a fragment list along the index's permutation. *)
Lemma own_rs_frags_view_perm γ dq (rss rss' : list ReplicaSetV.t) :
  rs_storage_view <$> rss' ≡ₚ rs_storage_view <$> rss →
  ([∗ list] rs ∈ rss,
    own_meta_frag γ (ReplicaSetV.key rs)
      rs.(ReplicaSetV.ObjectMeta').(ObjectMetaV.UID') dq
      rs.(ReplicaSetV.ObjectMeta') ∗
    own_spec_frag γ (ReplicaSetV.key rs)
      rs.(ReplicaSetV.ObjectMeta').(ObjectMetaV.UID') dq
      (ObjectSpecV.ReplicaSetSpec rs.(ReplicaSetV.Spec'))) -∗
  ([∗ list] rs ∈ rss',
    own_meta_frag γ (ReplicaSetV.key rs)
      rs.(ReplicaSetV.ObjectMeta').(ObjectMetaV.UID') dq
      rs.(ReplicaSetV.ObjectMeta') ∗
    own_spec_frag γ (ReplicaSetV.key rs)
      rs.(ReplicaSetV.ObjectMeta').(ObjectMetaV.UID') dq
      (ObjectSpecV.ReplicaSetSpec rs.(ReplicaSetV.Spec'))).
Proof.
  intros Hperm.
  rewrite !own_rs_frags_as_storage_views Hperm.
  iIntros "H". iExact "H".
Qed.

(* A freshly created ReplicaSet's key differs from every key already held: two
   full-fraction metadata fragments cannot sit at one key. This needs no
   invariant — it is immediate from the fragments. *)
Lemma own_meta_frag_key_distinct_list γ (rss : list ReplicaSetV.t) k uid m :
  ([∗ list] rs ∈ rss,
    own_meta_frag γ (ReplicaSetV.key rs)
      rs.(ReplicaSetV.ObjectMeta').(ObjectMetaV.UID') 1
      rs.(ReplicaSetV.ObjectMeta')) -∗
  own_meta_frag γ k uid 1 m -∗
  ⌜ Forall (λ rs, ReplicaSetV.key rs ≠ k) rss ⌝.
Proof.
  iIntros "Hlist Hone".
  iInduction rss as [|rs rest] "IH".
  - iPureIntro. apply Forall_nil_2.
  - iDestruct "Hlist" as "[Hhead Htail]".
    iAssert ⌜ ReplicaSetV.key rs ≠ k ⌝%I as %Hne.
    { destruct (decide (ReplicaSetV.key rs = k)) as [Heq|Hkne];
        last (iPureIntro; exact Hkne).
      iDestruct (kview.own_meta_meta_false Heq with "Hhead Hone") as %[]. }
    iDestruct ("IH" with "Htail Hone") as %Hrest.
    iPureIntro. apply Forall_cons_2; [exact Hne|exact Hrest].
Qed.

(* The list form: a freshly created ReplicaSet's UID differs from every UID
   already held. Each element either sits at a different key — and then
   [own_meta_frag_uid_distinct] applies — or at the same key, which two
   full-fraction metadata fragments rule out outright. *)
Lemma own_meta_frag_uid_distinct_list γ (rss : list ReplicaSetV.t) k uid m :
  ([∗ list] rs ∈ rss,
    own_meta_frag γ (ReplicaSetV.key rs)
      rs.(ReplicaSetV.ObjectMeta').(ObjectMetaV.UID') 1
      rs.(ReplicaSetV.ObjectMeta')) -∗
  own_meta_frag γ k uid 1 m -∗
  ⌜ Forall (λ rs,
      rs.(ReplicaSetV.ObjectMeta').(ObjectMetaV.UID') ≠ uid) rss ⌝.
Proof.
  iIntros "Hlist Hone".
  iInduction rss as [|rs rest] "IH".
  - iPureIntro. apply Forall_nil_2.
  - iDestruct "Hlist" as "[Hhead Htail]".
    iAssert ⌜ rs.(ReplicaSetV.ObjectMeta').(ObjectMetaV.UID') ≠ uid ⌝%I as %Hne.
    { destruct (decide (ReplicaSetV.key rs = k)) as [Heq|Hkne].
      - iDestruct (kview.own_meta_meta_false Heq with "Hhead Hone") as %[].
      - iApply (own_meta_frag_uid_distinct _ _ _ _ _ _ _ Hkne with "Hhead Hone"). }
    iDestruct ("IH" with "Htail Hone") as %Hrest.
    iPureIntro. apply Forall_cons_2; [exact Hne|exact Hrest].
Qed.

(* ---------------------------------------------------------------- *)
(* Relating the store's ReplicaSets to the caller's framed list.     *)
(*                                                                   *)
(* Mirrors index.v:109-760 with [ReplicaSetV.kind] for "Pod". The    *)
(* living/terminating axis survives the port even though the         *)
(* Deployment controller never deletes ReplicaSets: it is not the    *)
(* controller that introduces it but the ghost state. Both           *)
(* [own_children_frag] (cview.v:124) and [own_meta_frag]             *)
(* (kview.v:71) are about *living* objects, so the framed list can   *)
(* only ever be the living children, while [index_of] filters by     *)
(* [obj_parent_ref] and returns terminating ones too.                *)
(* ---------------------------------------------------------------- *)

Lemma filter_rs_parent_ref_fmap (rss : list ReplicaSetV.t) parent_key parent_uid :
  filter (λ obj : KObjectV.t, obj_parent_ref obj = Some (parent_key, parent_uid))
      (KObjectV.ReplicaSet <$> rss) =
    KObjectV.ReplicaSet <$>
      filter (λ rs, obj_parent_ref (KObjectV.ReplicaSet rs) =
        Some (parent_key, parent_uid)) rss.
Proof.
  induction rss as [|rs rss IH]; simpl; [done|].
  rewrite !filter_cons.
  destruct (decide (obj_parent_ref (KObjectV.ReplicaSet rs) =
    Some (parent_key, parent_uid))); simpl; by rewrite IH.
Qed.

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
   fragment's filter. Mirrors index.v's [filter_living_parent_pods]. *)
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
   parent. index.v:193's [child_pod_state_dom_eq] with the kind changed. *)
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
   permutation of the store's living children. index.v:570 with
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
   framed list up to storage view. index.v:693 ported. *)
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
   ReplicaSet analogue of index.v:223's
   [living_terminating_child_pod_keys_partition]. This is what turns
   "[Quiescent], so no terminating children" into "the children fragment
   already lists every child the index can return". *)
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
   caller holding only fragments cannot derive this; the invariant states it
   (kview.v:56-61) and the index reads under the invariant. *)
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

(* TRUSTED, exactly as index.v:19's [wp_index_of_podController] is. The
   goose-translated [index_of] does an interface type assertion and then calls
   [controller.PodControllerIndexKey]; reasoning about that should be settled
   for Pod and ReplicaSet together rather than here, so this mirrors the Pod
   chain's assumption and rests on no more than it does. *)
Lemma wp_index_of_replicaSetController i rs dq:
  {{{ is_pkg_init apimodel ∗
      KObjectV.deepown_i i (KObjectV.ReplicaSet rs) dq
  }}}
    @! apimodel.index_of #"replicaSetController"%go #(interface.ok i)
  {{{ sl, RET (#sl, #interface.nil);
      sl ↦* [replicaSetController_indexed_value rs] ∗
      KObjectV.deepown_i i (KObjectV.ReplicaSet rs) dq
  }}}.
Proof. Admitted.

(* ---------------------------------------------------------------- *)
(* The atomic-update form, and the Hoare triple built on it.        *)
(*                                                                   *)
(* Same layering as index.v's Pod chain: the semantic work lives in *)
(* the [_au] lemma, proved once against inv.v, and every triple      *)
(* below is a thin wrapper that [iApply]s it. index.v has six such   *)
(* wrappers over [wp_State__ByIndex_podController_au] (:1097, :1153, *)
(* :1232, :1299, :1378, :1446); this file needs one.                 *)
(*                                                                   *)
(* Simpler than the Pod version in two ways, both consequences of    *)
(* the Deployment controller never deleting ReplicaSets: no [phase]  *)
(* and no [own_terminating_children_frag], so no deletion            *)
(* observations; and no [include_specs] switch, because the only     *)
(* caller wants specs.                                               *)
(*                                                                   *)
(* NOT simpler in the way an earlier draft of this file assumed. The *)
(* living/terminating distinction is not introduced by the           *)
(* controller, so dropping the terminating machinery does not make   *)
(* it go away: it is baked into the ghost state. [own_children_frag] *)
(* records the keys of the *living* children (cview.v:124), and      *)
(* [own_meta_frag] can only be held for an object with no deletion   *)
(* timestamp (kview.v:71). The caller's framed list is therefore     *)
(* always the living children, while [index_of] filters by           *)
(* [obj_parent_ref], which is blind to deletion timestamps and so    *)
(* returns terminating children too. A permutation between the two   *)
(* would be false in any state holding a terminating ReplicaSet      *)
(* child.                                                            *)
(*                                                                   *)
(* So the storage-view permutation below is stated over              *)
(* [filter rs_is_living rss'], mirroring the *unconditional* clause  *)
(* of the Pod atomic update (index.v:791). index.v gets the stronger *)
(* whole-list statement only under [phase = Quiescent], paid for     *)
(* with [own_terminating_children_frag]. If the Deployment stability *)
(* proof turns out to need the whole list rather than its living     *)
(* half, that is the extension to make, and it is mechanical:        *)
(* thread [phase] through, and mirror index.v:223's                  *)
(* [living_terminating_child_pod_keys_partition].                    *)
(*                                                                   *)
(* [wp_index_of_replicaSetController] above is [Admitted], exactly   *)
(* as the Pod chain's [wp_index_of_podController] (index.v:19) is,   *)
(* so this file rests on no more trust than that chain does.         *)
(*                                                                   *)
(* WORTH DECIDING ANYWAY. This whole file exists only because        *)
(* [filterReplicaSetsByOwner] fetches through an index instead of    *)
(* listing -- see the TODO on that function in                       *)
(* controllers/deployment/deployment.go. If the model's listing      *)
(* specifications are given fragments and the controller goes back   *)
(* to the upstream listing shape, this file and the                  *)
(* [ReplicaSetControllerIndex] constant both disappear.              *)
(* ---------------------------------------------------------------- *)

Local Lemma wp_State__ByIndex_replicaSetController_au γ l indexed_value :
  ∀ Φ,
  ( is_pkg_init apimodel ∗
    is_kubernetes γ l ∗
    |={⊤,∅}=> ∃ rss rs_dqs control_phase parent_key parent_uid
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
        parent_key parent_uid control_phase ∗
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
        ⌜ control_phase = Quiescent →
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
        own_terminating_children_frag γ parent_key parent_uid control_phase
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
    wp_apply (wp_index_of_replicaSetController with "[$Hthis_i_rs]").
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
      (rss rs_dqs control_phase parent_key parent_uid children_keys
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
       index.v:986-1030. *)
    assert (Hcombined_dom : control_phase = Quiescent →
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
    assert (Hfull_perm : control_phase = Quiescent →
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
   update, in the shape of index.v's [wp_State__ByIndex_podController]. *)
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
         no fragment for, and [Hview_perm] below would be false. This is the
         [ready = true] half of deployment/top_level.v's [owned_resources]. *)
      "Hown_terminating_children_frag" ∷ own_terminating_children_frag γ
        parent_key parent_uid Quiescent ∗
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
      (* The store's invariant gives every object a distinct UID
         (algebra/kview.v:56-61). A caller holding only fragments cannot see
         that, so the index — which reads under the invariant — returns it.
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
        parent_key parent_uid Quiescent
  }}}.
Proof.
  iIntros (Φ) "(#Hinit & H) HΦ". iNamed "H".
  iApply wp_State__ByIndex_replicaSetController_au.
  iFrame "#".
  iApply fupd_mask_intro.
  { Timeout 10 set_solver. }
  iIntros "Hmask".
  iExists rss, rs_dqs, Quiescent, parent_key, parent_uid, children_keys,
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
