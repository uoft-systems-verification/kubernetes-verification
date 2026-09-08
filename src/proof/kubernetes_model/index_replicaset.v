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
(* The atomic-update form, and the Hoare triple built on it.        *)
(*                                                                   *)
(* Same layering as index.v's Pod chain: the semantic work lives in *)
(* the [_au] lemma, proved once against inv.v, and every triple      *)
(* below is a thin wrapper that [iApply]s it. index.v has six such   *)
(* wrappers over [wp_State__ByIndex_podController_au] (:1097, :1153, *)
(* :1232, :1299, :1378, :1446); this file needs one.                 *)
(*                                                                   *)
(* Simpler than the Pod version in three ways, all consequences of   *)
(* the Deployment controller never deleting ReplicaSets: no          *)
(* living/terminating partition, so no [phase], no                   *)
(* [own_terminating_children_frag] and no deletion observations; and *)
(* no [include_specs] switch, because the only caller wants specs.   *)
(* ---------------------------------------------------------------- *)

(* TODO (separate PR): discharge this. It is the last real obligation for the
   Deployment controller's stability triple, and everything it needs is either
   already proved below/in list.v or has a direct Pod analogue to mirror.

   WHAT IT SAYS. [ByIndex] run under the store invariant returns exactly the
   objects whose controller reference is (parent_key, parent_uid) -- hence
   exactly the ReplicaSet-kinded keys recorded in [own_children_frag] -- and it
   returns them related to the caller's framed list by a permutation of
   [rs_storage_view], i.e. up to resource version. Metadata alone would not be
   enough: [deployment_realized] constrains ReplicaSet *specs*, so the caller
   has to move spec fragments across the permutation too.

   WHAT IS ALREADY DONE, and should just be used:
     - [wp_State__objListLocked_ReplicaSet_NamespaceAll] (list.v) -- the listing
       step, proved.
     - [matching_replicaSetController_indexed_value_implies_being_children]
       (above) -- filtering by index value = filtering by controller reference,
       proved. This is the step that connects the index to the children
       fragment.
     - [own_rs_frags_as_storage_views], [own_rs_frags_view_perm],
       [rs_storage_view_eq_inv] (above) -- the fragment-motion layer, proved.

   WHAT REMAINS, in dependency order:

     1. [child_rs_state_dom_eq] -- mirror index.v:193's
        [child_pod_state_dom_eq]. Roughly 30 lines. Simpler than the Pod
        version: there is no living/terminating partition to reconcile, so
        index.v:223's [living_terminating_child_pod_keys_partition] has no
        analogue and is not needed.

     2. [spec_rss_is_permutation_of_child_rs_state_for_storage_view] and
        [rss_is_permutation_of_spec_rss_for_storage_view] -- mirror index.v:570
        and index.v:693. Together ~200 lines, and the bulk of the work. These
        carry the storage-view permutation from the framed list to the list the
        API returned. Substitute [obj_parent_ref] for the Pod version's
        [living_obj_parent_ref] throughout: with no terminating axis the two
        coincide here.

     3. The body of this lemma -- mirror index.v:762's
        [wp_State__ByIndex_podController_au], ~150 lines with the pieces above
        in hand. Open the mutex, list with (list.v) above, run the filter loop
        (index.v:846-920 transfers almost verbatim -- it is generic in the
        object type), then at loop exit open the atomic update, rewrite with the
        matching lemma, and close with (2). Drop everything in the Pod proof
        that touches [phase], [own_terminating_children_frag],
        [terminating_pods] or [own_deletion_observed_frag]: the Deployment
        controller never deletes ReplicaSets, so none of it has an analogue.

     4. [wp_index_of_replicaSetController] -- the loop calls [index_of], and the
        Pod chain's corresponding [wp_index_of_podController] (index.v:19) is
        itself [Admitted]. Mirroring it leaves this file resting on exactly the
        trust the Pod chain already rests on. Proving it outright means
        reasoning about the goose-translated [index_of]'s interface type
        assertion and [controller.PodControllerIndexKey], and should be decided
        for Pod and ReplicaSet together rather than here.

   WORTH DECIDING FIRST. This whole file exists only because
   [filterReplicaSetsByOwner] fetches through an index instead of listing --
   see the TODO on that function in controllers/deployment/deployment.go. If
   the model's listing specifications are given fragments and the controller
   goes back to the upstream listing shape, this file and the
   [ReplicaSetControllerIndex] constant both disappear. Settle that before
   spending the ~400 lines above. *)
Local Lemma wp_State__ByIndex_replicaSetController_au γ l indexed_value :
  ∀ Φ,
  ( is_pkg_init apimodel ∗
    is_kubernetes γ l ∗
    |={⊤,∅}=> ∃ rss rs_dqs parent_key parent_uid children_keys children_dq,
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
        ⌜ rs_storage_view <$> rss' ≡ₚ rs_storage_view <$> rss ⌝ ∗
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
        own_children_frag γ parent_key parent_uid children_dq children_keys
          ={∅,⊤}=∗ ▷ Φ (#sl, #interface.nil)%V
      )
  ) -∗ WP l @! (go.PointerType apimodel.State) @! "ByIndex"
        #ReplicaSetV.kind #"replicaSetController"%go #indexed_value {{ Φ }}.
Proof.
Admitted.

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
      "%Hview_perm" ∷ ⌜ rs_storage_view <$> rss' ≡ₚ rs_storage_view <$> rss ⌝ ∗
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
        children_dq children_keys
  }}}.
Proof.
  iIntros (Φ) "(#Hinit & H) HΦ". iNamed "H".
  iApply wp_State__ByIndex_replicaSetController_au.
  iFrame "#".
  iApply fupd_mask_intro.
  { Timeout 10 set_solver. }
  iIntros "Hmask".
  iExists rss, rs_dqs, parent_key, parent_uid, children_keys, children_dq.
  simpl. iFrame "%". iFrame.
  iIntros (sl interfaces rss_ret dq') "Hpost".
  iDestruct "Hpost" as
    "(Hsl & Hrss & %Hview_perm & %Hrss_valid & %Hparent_refs & %Hnodup' &
      %Huid_nodup' & Hown_meta_frags & Hown_spec_frags & Hown_children_frag)".
  iMod "Hmask" as "_".
  iModIntro. iNext.
  iApply ("HΦ" $! sl interfaces rss_ret dq').
  iFrame "Hsl Hrss Hown_meta_frags Hown_spec_frags Hown_children_frag".
  iFrame "%".
Qed.

End proof.
