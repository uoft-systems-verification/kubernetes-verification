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
