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
(* reference, so it can. See notes/deployment-spec-aug-26.md §3.2.   *)
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

(* TRUSTED — the single remaining obligation for H2.

   Discharging it means writing the ReplicaSet analogue of index.v's Pod
   chain: an [_au] version proved against inv.v showing that ByIndex over the
   invariant returns exactly the objects whose controller reference matches,
   and hence exactly the ReplicaSet-kinded keys in [own_children_frag]. That is
   the semantic core Q3 identified; the index packages it reusably rather than
   avoiding it.

   index.v is 1725 lines for the Pod case, ~1100 of them supporting lemmas
   below [wp_State__ByIndex_podController] at :1097. The ReplicaSet version
   should be materially leaner (no living/terminating partition), but it is a
   file, not a lemma. Note that even the Pod chain is not fully discharged —
   [wp_index_of_podController] (index.v:19) is itself Admitted.

   Shaped after [wp_State__ByIndex_podController_with_spec] (index.v:1153):
   metadata *and* spec fragments go in, both come back untouched, and the
   objects the API returned are related to the framed ones by a permutation
   of storage views. *)
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
Admitted.

End proof.
