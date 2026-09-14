(* Ghost state and lemmas for the concurrent delete loop of manageReplicas
   (copied from upstream pkg/controller/replicaset): one goroutine per pod to
   delete, joined with a sync.WaitGroup, errors collected on a buffered
   channel and inspected with a non-blocking select.

   The proof shares the parent's children-set fragment among the goroutines
   through an Iris invariant, opened at the linearization point of the
   model's delete ([wp_State__delete_au]). Each goroutine holds a ghost-map
   marker for the key of its pod; the invariant maps the set of still-pending
   keys to the current children set, which is how a goroutine knows its pod is
   still owned when it deletes it. A pool of done tokens ties every [Done] to
   a preceding deletion, so [Wait] returning means every targeted pod is gone. *)
From New.proof Require Import prelude empty_ffi.
From New.proof.kubernetes_model Require Export delete.
From New.proof.controllers.replicaset Require Export top_level.
From New.proof Require Import sync.
From New.golang.theory Require Import chan.
From New.golang.theory.chan.au_spec Require Import chan_au_send.
From New.proof Require Import proof_prelude.

Section proof.
Context `{hG: !heapGS Σ} `{!ffi_semantics _ _}.
Context {sem : go.Semantics}
  {package_sem : code.controllers.replicaset.replicaset.Assumptions}.
Collection W := sem + package_sem.
#[local] Instance base_common_sem : common.Assumptions | 100 :=
  code.controllers.replicaset.replicaset.import_common_Assumption.
#[local] Instance controller_sem : controller.Assumptions :=
  code.controllers.replicaset.replicaset.import_controller_Assumption.
#[local] Instance runtime_sem :
    code.k8s_io.apimachinery.pkg.runtime.runtime.Assumptions :=
  controller.import_runtime_Assumption.
#[local] Instance runtime_object_underlying_eq :
    runtime.Object ≤u runtime.Objectⁱᵐᵖˡ.
Proof using package_sem. apply _. Qed.
#[local] Instance meta_object_underlying_eq :
    meta_v1.Object ≤u meta_v1.Objectⁱᵐᵖˡ.
Proof using package_sem. apply _. Qed.
#[local] Instance base_apimodel_sem : apimodel.Assumptions | 100 :=
  common.import_apimodel_Assumption.
#[local] Instance object_meta_v1_sem :
    code.k8s_io.apimachinery.pkg.apis.meta.v1.v1.Assumptions :=
  apimodel.import_apis_meta_v1_Assumption.
#[local] Instance object_apps_v1_sem :
    code.k8s_io.api.apps.v1.v1.Assumptions :=
  apimodel.import_api_apps_v1_Assumption.
#[local] Instance object_core_v1_sem :
    code.k8s_io.api.core.v1.v1.Assumptions :=
  code.k8s_io.api.apps.v1.v1.import_core_v1_Assumption.
#[local] Instance apimodel_sem : apimodel.Assumptions | 0.
Proof using package_sem.
  constructor; try exact object_core_v1_sem; try apply _.
Defined.
#[local] Instance common_sem : common.Assumptions | 0.
Proof using package_sem.
  constructor; try exact apimodel_sem; try apply _.
Defined.
#[local] Instance sync_sem : sync.Assumptions :=
  code.controllers.replicaset.replicaset.import_sync_Assumption.
Context `{!kubernetesModelG Σ}.
Context `{!KObjectV.ObjectInterfaceAssumptions}.
Local Set Default Proof Using "All".

Definition delete_batchN : namespace := nroot .@ "rs_delete_batch".
Definition delete_wgN : namespace := nroot .@ "rs_delete_wg".

(** Logically atomic pod deletion through the model's [PodDelete], derived from
    [wp_State__delete_au]. Restricted to delete options without a resource
    version precondition, which is what the controller uses. *)
Lemma wp_State__PodDelete_au γ l key namespace name options_c options uid kmeta
    parent_key parent_uid :
  ∀ Φ,
  ( is_pkg_init apimodel ∗
    "#Hisk" ∷ is_kubernetes γ l ∗
    "Hdeepown_options" ∷ DeleteOptionsV.deepown options_c options 1 ∗
    "%Hvalid_options" ∷ ⌜ DeleteOptionsV.valid options ⌝ ∗
    "%Hkey_def" ∷ ⌜ key = {|
      KKey.Kind' := "Pod"%go;
      KKey.Namespace' := namespace;
      KKey.Name' := name
    |} ⌝ ∗
    "%Hdelete_preconditions" ∷ ⌜ delete_preconditions_match options kmeta ⌝ ∗
    "%Hdelete_preconditions_rv_none" ∷ ⌜ delete_options_preconditions_resource_version_none options ⌝ ∗
    "Hown_meta_frag" ∷ own_meta_frag γ key uid 1 kmeta ∗
    "#Hown_unreserved_key_frag" ∷ own_unreserved_key_frag γ key ∗
    "Hau" ∷ (|={⊤,∅}=> ∃ children has_terminating_children,
      "%Hkey_in" ∷ ⌜ key ∈ children ⌝ ∗
      "Hown_children_frag" ∷ own_children_frag γ parent_key parent_uid 1 children ∗
      "Hown_terminating_children_frag" ∷
        own_terminating_children_frag γ parent_key parent_uid has_terminating_children ∗
      "Hclose" ∷ (
        own_children_frag γ parent_key parent_uid 1 (children ∖ {[key]}) ∗
        own_deletion_observed_frag γ key uid ∗
        own_terminating_children_frag γ parent_key parent_uid terminating_children.Maybe
        ={∅,⊤}=∗ ▷ Φ #interface.nil))
  ) -∗ WP l @! (go.PointerType apimodel.State) @! "PodDelete" #namespace #name #options_c {{ Φ }}.
Proof.
  iIntros (Φ) "(#Hinit & H)". iNamed "H". subst key.
  iPoseProof (kview.own_meta_valid with "Hown_meta_frag") as "%Hmeta_valid".
  destruct Hmeta_valid as (_ & _ & Huid_eq & _ & _).
  pose proof (delete_preconditions_match_uid_of_match options uid kmeta Huid_eq
    Hdelete_preconditions) as Hdelete_preconditions_uid.
  wp_method_call. rewrite /apimodel.State__PodDeleteⁱᵐᵖˡ. wp_call. wp_auto.
  wp_apply (wp_State__delete_au γ l
    {| KKey.Kind' := "Pod"%go; KKey.Namespace' := namespace; KKey.Name' := name |}
    options_c options).
  iFrame "#". iFrame "Hdeepown_options". iSplit; [done|].
  iMod "Hau" as (children has_terminating_children) "H". iNamed "H".
  iModIntro. iExists uid, kmeta, parent_key, parent_uid, children, has_terminating_children.
  iSplit; [done|]. iSplit; [done|].
  iFrame "Hown_meta_frag Hown_children_frag Hown_terminating_children_frag".
  iFrame "#".
  rewrite (decide_True _ _ Hdelete_preconditions_rv_none).
  iIntros "Hpost". iMod ("Hclose" with "Hpost") as "HΦ".
  iModIntro. iNext. wp_auto. iApply "HΦ".
Qed.

(** Invariant shared by the goroutines deleting one batch of [bs] pods.
    - [pending] is the set of keys not yet deleted; each goroutine holds the
      ghost-map marker of its own key while it is pending.
    - [γd] is a pool of [bs] done tokens; a goroutine takes one when it deletes
      its pod and returns it at [Done].
    - [rest] is the parent's children set once every targeted pod is gone. *)
Definition delete_batch_inv_body γ γwg γd (γm : gname) γdr (bs : w64) pk puid (rest : gset KKey.t) : iProp Σ :=
  ∃ (ctr : w32) (ndeleted ndone : nat) (drained : bool) (pending : gset KKey.t),
    "Hwg_ctr" ∷ own_WaitGroup γwg ctr ∗
    "Hpending_auth" ∷ ghost_map_auth γm 1 (gset_to_gmap () pending) ∗
    "Hdone_pool" ∷ own_toks γd (sint.nat bs - ndeleted + ndone) ∗
    "Hdrained_var" ∷ ghost_var γdr (1/2) drained ∗
    "%Hctr" ∷ ⌜ sint.Z ctr = sint.Z bs - Z.of_nat ndone ⌝ ∗
    "%Hpending_size" ∷ ⌜ (ndeleted + size pending)%nat = sint.nat bs ⌝ ∗
    "%Hcounts" ∷ ⌜ (ndone ≤ ndeleted)%nat ⌝ ∗
    "%Hpending_rest" ∷ ⌜ pending ## rest ⌝ ∗
    "%Hdrained" ∷ ⌜ drained = true → ndone = sint.nat bs ⌝ ∗
    "Hres" ∷ (⌜ drained = true ⌝ ∨ (⌜ drained = false ⌝ ∗
      own_children_frag γ pk puid 1 (rest ∪ pending) ∗
      ∃ has_terminating_children, own_terminating_children_frag γ pk puid has_terminating_children)).

(** One marker per targeted pod, keyed by the pod's key. *)
Lemma alloc_pending_markers (pods : list PodV.t) :
  NoDup (PodV.key <$> pods) →
  ⊢ |==> ∃ γm : gname,
    ghost_map_auth γm 1 (gset_to_gmap () (list_to_set (C:=gset KKey.t) (PodV.key <$> pods))) ∗
    [∗ list] pod ∈ pods, PodV.key pod ↪[γm] ().
Proof.
  intros Hnodup.
  iMod (ghost_map_alloc (gset_to_gmap () (list_to_set (C:=gset KKey.t) (PodV.key <$> pods))))
    as (γm) "[Hauth Helems]".
  iModIntro. iExists γm. iFrame "Hauth".
  rewrite big_sepM_gset_to_gmap.
  rewrite (big_sepS_list_to_set _ _ Hnodup).
  rewrite big_sepL_fmap. iFrame.
Qed.

Lemma pending_size_pos (pending : gset KKey.t) k :
  k ∈ pending → (1 ≤ size pending)%nat.
Proof.
  intros Hk.
  destruct (decide (size pending = 0%nat)) as [Hz|Hnz]; last lia.
  exfalso. apply size_empty_inv in Hz. Timeout 10 set_solver.
Qed.

Lemma pending_size_delete (pending : gset KKey.t) k :
  k ∈ pending → size (pending ∖ {[k]}) = (size pending - 1)%nat.
Proof.
  intros Hk.
  assert ({[k]} ⊆ pending) as Hsub. { Timeout 10 set_solver. }
  rewrite (size_difference _ _ Hsub) size_singleton. done.
Qed.

Lemma union_pending_delete (rest pending : gset KKey.t) k :
  k ∈ pending → pending ## rest →
  (rest ∪ pending) ∖ {[k]} = rest ∪ (pending ∖ {[k]}).
Proof. intros. Timeout 10 set_solver. Qed.

End proof.
