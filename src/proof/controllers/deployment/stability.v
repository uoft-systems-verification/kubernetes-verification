From New.proof Require Import prelude empty_ffi.
From New.proof.kubernetes_model Require Export get create_named update.
From New.proof Require Export util.
From New.proof Require Export wp_helpers.
From New.proof.kubernetes_types Require Export prelude.
From New.proof.controllers.deployment Require Export deployment_init.
From New.proof.k8s_io.api.apps Require Export v1.
From New.proof.k8s_io.kubernetes.pkg Require Export controller.
From New.proof.k8s_io.apimachinery.pkg.api Require Export errors.
From New.proof.controllers.deployment Require Export
  common replica_sets rollout sync_deployment.

Section proof.
Context `{hG: !heapGS Σ}.
Context {sem : go.Semantics}
  {package_sem : code.controllers.deployment.deployment.Assumptions}.
Collection W := sem + package_sem.
#[local] Instance controller_sem : controller.Assumptions :=
  code.controllers.deployment.deployment.import_controller_Assumption.
#[local] Instance base_apimodel_sem : apimodel.Assumptions | 100 :=
  code.controllers.deployment.deployment.import_apimodel_Assumption.
#[local] Instance object_meta_v1_sem :
    code.k8s_io.apimachinery.pkg.apis.meta.v1.v1.Assumptions :=
  apimodel.import_apis_meta_v1_Assumption.
#[local] Instance object_apps_v1_sem :
    code.k8s_io.api.apps.v1.v1.Assumptions :=
  apimodel.import_api_apps_v1_Assumption.
#[local] Instance object_core_v1_sem :
    code.k8s_io.api.core.v1.v1.Assumptions :=
  code.k8s_io.api.apps.v1.v1.import_core_v1_Assumption.
#[local] Instance intstr_sem : intstr.Assumptions :=
  code.k8s_io.api.apps.v1.v1.import_intstr_Assumption.
#[local] Instance apimodel_sem : apimodel.Assumptions | 0.
Proof using package_sem.
  constructor; try exact object_core_v1_sem; try apply _.
Defined.
Context `{!kubernetesModelG Σ}.
Local Set Default Proof Using "All".

(* ---------------------------------------------------------------- *)
(* H2 — stability.                                                    *)
(*                                                                   *)
(* The controller does not modify the cluster state when the state    *)
(* already realizes the deployment. Following the ReplicaSet          *)
(* controller (controllers/replicaset/top_level.v:161), absence of    *)
(* mutation is not argued from a trace: every fragment below is held  *)
(* at the *same* fraction [dq], and a write needs the full fraction.  *)
(* If the proof goes through at all, no write happened.               *)
(*                                                                   *)
(* The progress half (H1) lives in sync_deployment.v as               *)
(* [wp_syncDeployment], stated inline rather than through a           *)
(* [progress_spec] definition — this controller has no top_level.v.   *)
(* The fragment bundle is therefore defined here rather than shared.  *)
(* ---------------------------------------------------------------- *)

(* Everything the controller touches, at a uniform fraction.

   Compare [wp_syncDeployment]'s precondition, which holds the ReplicaSet
   fragments and the children fragment at 1 because it writes through them.
   Here they are all [dq] — that is the entire mechanism of this spec. *)
Definition stability_resources γ (d : DeploymentV.t)
    (rss : list ReplicaSetV.t) (children_keys : gset KKey.t)
    uid kmeta dq : iProp Σ :=
  "Hown_d_meta" ∷ own_meta_frag γ (DeploymentV.key d) uid dq kmeta ∗
  "Hown_d_spec" ∷ own_spec_frag γ (DeploymentV.key d) uid dq
    (ObjectSpecV.DeploymentSpec d.(DeploymentV.Spec')) ∗
  "Hreserved" ∷ own_available_reserved_frag γ dq (new_rs_key d) ∗
  "Hown_children" ∷ own_children_frag γ (DeploymentV.key d)
    uid dq children_keys ∗
  "Hown_frags" ∷ ([∗ list] rs ∈ rss,
    own_meta_frag γ (ReplicaSetV.key rs)
      rs.(ReplicaSetV.ObjectMeta').(ObjectMetaV.UID') dq
      rs.(ReplicaSetV.ObjectMeta') ∗
    own_spec_frag γ (ReplicaSetV.key rs)
      rs.(ReplicaSetV.ObjectMeta').(ObjectMetaV.UID') dq
      (ObjectSpecV.ReplicaSetSpec rs.(ReplicaSetV.Spec'))) ∗
  "%Hkeys_nodup" ∷ ⌜ NoDup (ReplicaSetV.key <$> rss) ⌝.

(* [deployment_realized] is this controller's [current_state_matches]. Unlike
   the ReplicaSet controller there is no [match_distance] to go with it: PR #7
   dropped surge pacing, so the controller converges in one sync and the
   distance would be two-valued. See notes/questions-08-20.md Q6. *)

Definition stability_spec γ model_l (namespace name : go_string)
    (d : DeploymentV.t) (rss : list ReplicaSetV.t)
    (children_keys : gset KKey.t) uid kmeta dq : iProp Σ :=
  {{{ is_pkg_init code.controllers.deployment.pkg_id.deployment ∗
      "#Hisk" ∷ is_kubernetes γ model_l ∗
      "#Hglobal_l" ∷ (global_addr apimodel.ModelState) ↦□ model_l ∗
      "Hresources" ∷ stability_resources γ d rss children_keys uid kmeta dq ∗
      "%Hkey_def" ∷ ⌜ DeploymentV.key d = {|
        KKey.Kind' := DeploymentV.kind;
        KKey.Namespace' := namespace;
        KKey.Name' := name
      |} ⌝ ∗
      "%Hd_valid" ∷ ⌜ DeploymentV.valid d ⌝ ∗
      "%Hnamespace_valid" ∷ ⌜ valid_namespace namespace ⌝ ∗
      "%Hnew_rs_name_valid" ∷ ⌜ valid_dns1123_subdomain (new_rs_name d) ⌝ ∗
      "%Hrss_valid" ∷ ⌜ Forall ReplicaSetV.valid rss ⌝ ∗
      "%Hdom_eq" ∷ ⌜ list_to_set (ReplicaSetV.key <$> rss) =
          filter (λ key, key.(KKey.Kind') = ReplicaSetV.kind) children_keys ⌝ ∗
      (* The no-collision assumption, as on the progress triple. Without it
         findNewReplicaSet may pick either of two matching ReplicaSets, and
         stability is false as stated — notes/questions-08-20.md Q2. *)
      "%Hunique_new" ∷ ⌜ unique_new_replica_set d rss ⌝ ∗
      "%Hmatch" ∷ ⌜ deployment_realized d rss ⌝
  }}}
    @! deployment.syncDeployment #namespace #name
  {{{ (err : interface.t), RET #err;
      stability_resources γ d rss children_keys uid kmeta dq
  }}}.

(* scaleReplicaSet is a no-op when the count already matches: deployment.go:104
   returns before [rsCopy := rs.DeepCopy()], so the ReplicaSetUpdateTx call is
   never reached and no fragment at 1 is needed. This is the fact that makes
   the whole stability chain provable at [dq]. *)
Lemma wp_scaleReplicaSet_stability rs_l (rs : ReplicaSetV.t)
    (new_scale : w32) dq :
  {{{ is_pkg_init code.controllers.deployment.pkg_id.deployment ∗
      "Hrs" ∷ ReplicaSetV.deepown_l rs_l rs dq ∗
      "%Hnoop" ∷ ⌜ rs_replicas rs = new_scale ⌝
  }}}
    @! deployment.scaleReplicaSet #rs_l #new_scale
  {{{ RET (#false, #rs_l, #interface.nil);
      ReplicaSetV.deepown_l rs_l rs dq
  }}}.
Proof.
  wp_start as "H". iNamed "H".
  wp_auto.
  wp_apply (wp_replicasOfRS rs_l (Some rs) dq with "[Hrs]").
  { iFrame "#". iExact "Hrs". }
  iIntros "Hrs".
  simpl.
  rewrite Hnoop.
  wp_auto.
  wp_if_destruct; [|exfalso; done].
  iApply "HΦ". iFrame.
Qed.

(* reconcileNewReplicaSet scales the new ReplicaSet to the deployment's count.
   Under [deployment_realized] it is already there, so this is scaleReplicaSet's
   no-op path and nothing is written. *)
Lemma wp_reconcileNewReplicaSet_stability new_rs_l (new_rs : ReplicaSetV.t)
    d_l (d : DeploymentV.t) dq_rs dq_d :
  {{{ is_pkg_init code.controllers.deployment.pkg_id.deployment ∗
      "Hnew_rs" ∷ ReplicaSetV.deepown_l new_rs_l new_rs dq_rs ∗
      "Hd" ∷ DeploymentV.deepown_l d_l d dq_d ∗
      "%Hnoop" ∷ ⌜ rs_replicas new_rs = deployment_replicas d ⌝
  }}}
    @! deployment.reconcileNewReplicaSet #new_rs_l #d_l
  {{{ RET (#false, #interface.nil);
      ReplicaSetV.deepown_l new_rs_l new_rs dq_rs ∗
      DeploymentV.deepown_l d_l d dq_d
  }}}.
Proof.
  wp_start as "H". iNamed "H".
  wp_auto.
  wp_apply (wp_replicasOf d_l d dq_d with "[$Hd]").
  iIntros "Hd".
  wp_auto.
  wp_apply (wp_scaleReplicaSet_stability new_rs_l new_rs
    (deployment_replicas d) dq_rs with "[$Hnew_rs]").
  { iPureIntro. exact Hnoop. }
  iIntros "Hnew_rs".
  wp_auto_lc 1.
  iApply "HΦ". iFrame.
Qed.

(* reconcileOldReplicaSets drains every old ReplicaSet to zero. Under
   [deployment_realized] they are already there, so every iteration takes
   scaleReplicaSet's no-op path and the loop writes nothing. [scaledDown] stays
   false throughout, which is why the return value is fixed. *)
Lemma wp_reconcileOldReplicaSets_stability sl ptrs (rss : list ReplicaSetV.t)
    dq_sl dq :
  {{{ is_pkg_init code.controllers.deployment.pkg_id.deployment ∗
      "Hsl" ∷ sl ↦*{dq_sl} ptrs ∗
      "Hrss" ∷ ([∗ list] ptr;rs ∈ ptrs;rss, ReplicaSetV.deepown_l ptr rs dq) ∗
      "%Hdrained" ∷ ⌜ Forall (λ rs, rs_replicas rs = W32 0) rss ⌝
  }}}
    @! deployment.reconcileOldReplicaSets #sl
  {{{ RET (#false, #interface.nil);
      sl ↦*{dq_sl} ptrs ∗
      ([∗ list] ptr;rs ∈ ptrs;rss, ReplicaSetV.deepown_l ptr rs dq)
  }}}.
Proof.
  wp_start as "H". iNamed "H". wp_auto.
  iDestruct (own_slice_len with "Hsl") as %(Hsl_len1 & Hsl_len2).
  iDestruct (big_sepL2_length with "Hrss") as %Hptrs_rss_len.
  (* Nothing changes across iterations: [scaledDown] stays false and both the
     slice and every deepown come back untouched. *)
  set I := (∃ (i : w64) (rs_ptr_value : loc),
    "Hi_ptr" ∷ i_ptr ↦ i ∗
    "HscaledDown_ptr" ∷ scaledDown_ptr ↦ false ∗
    "Hrs_ptr" ∷ rs_ptr ↦ rs_ptr_value ∗
    "Hsl" ∷ sl ↦*{dq_sl} ptrs ∗
    "Hrss" ∷ ([∗ list] ptr;rs ∈ ptrs;rss, ReplicaSetV.deepown_l ptr rs dq) ∗
    "%Hi" ∷ ⌜ 0 ≤ sint.Z i ≤ sint.Z (slice.len sl) ⌝
  )%I.
  iAssert I with "[i scaledDown rs Hsl Hrss]" as "Hloop_inv".
  { iExists (W64 0), null. iFrame. iPureIntro. word. }
  wp_for "Hloop_inv". wp_if_destruct.
  2:{ iApply "HΦ". iFrame. }
  list_elem ptrs (sint.Z i) as this_ptr.
  assert (∃ this_rs, rss !! sint.nat i = Some this_rs) as [this_rs Hthis_rs_lookup].
  { apply lookup_lt_is_Some_2. rewrite -Hptrs_rss_len Hsl_len1. word. }
  (* [slice.for_range] desugars to an index loop whose element load sits inside
     a [decide] on the bounds; resolve it before stepping. *)
  destruct (decide (0 ≤ sint.Z i < sint.Z (slice.len sl))) as [_|Hbounds]; last word.
  wp_apply (wp_load_slice_index with "[$Hsl]"); [word| |].
  { iPureIntro. exact Hthis_ptr_lookup. }
  iIntros "Hsl". wp_auto.
  assert (rs_replicas this_rs = W32 0) as Hthis_drained.
  { rewrite Forall_lookup in Hdrained. eapply Hdrained. exact Hthis_rs_lookup. }
  iDestruct (big_sepL2_lookup_acc with "Hrss") as "[Hthis Hrss_restore]";
    [exact Hthis_ptr_lookup|exact Hthis_rs_lookup|].
  wp_apply (wp_scaleReplicaSet_stability this_ptr this_rs (W32 0) dq with "[$Hthis]").
  { iPureIntro. exact Hthis_drained. }
  iIntros "Hthis".
  iDestruct ("Hrss_restore" with "Hthis") as "Hrss".
  wp_auto_lc 1.
  iApply wp_for_post_do. wp_auto.
  iFrame "HΦ".
  iExists (word.add i (W64 1)), this_ptr.
  iFrame.
  iPureIntro. word.
Qed.

(* getNewReplicaSet adopts rather than creates when a template match exists.
   [deployment_realized] guarantees one does, so findNewReplicaSet returns
   non-nil at deployment.go:121 and the ReplicaSetCreate path below it is dead —
   which is why no reserved fragment appears here. *)
Lemma wp_getNewReplicaSet_stability d_l (d : DeploymentV.t)
    sl ptrs (rss : list ReplicaSetV.t) dq_d dq_sl dq :
  {{{ is_pkg_init code.controllers.deployment.pkg_id.deployment ∗
      "Hd" ∷ DeploymentV.deepown_l d_l d dq_d ∗
      "Hsl" ∷ sl ↦*{dq_sl} ptrs ∗
      "Hrss" ∷ ([∗ list] ptr;rs ∈ ptrs;rss, ReplicaSetV.deepown_l ptr rs dq) ∗
      "%Hmatch" ∷ ⌜ deployment_realized d rss ⌝
  }}}
    @! deployment.getNewReplicaSet #d_l #sl
  {{{ (new_rs_l : loc) (i : nat) (new_rs : ReplicaSetV.t),
      RET (#new_rs_l, #interface.nil);
      "%Hfound" ∷ ⌜ find_new_replica_set d rss = Some (i, new_rs) ⌝ ∗
      "%Hptr" ∷ ⌜ ptrs !! i = Some new_rs_l ⌝ ∗
      "Hd" ∷ DeploymentV.deepown_l d_l d dq_d ∗
      "Hsl" ∷ sl ↦*{dq_sl} ptrs ∗
      "Hrss" ∷ ([∗ list] ptr;rs ∈ ptrs;rss, ReplicaSetV.deepown_l ptr rs dq)
  }}}.
Proof.
  wp_start as "H". iNamed "H".
  (* [deployment_realized] exhibits a template match, so [list_find] must
     succeed — this is what rules out the create path. *)
  destruct Hmatch as (mrs & Hmrs_in & Hmrs_matches & _ & _).
  assert (is_Some (find_new_replica_set d rss)) as [[i new_rs] Hfound].
  { unfold find_new_replica_set.
    eapply list_find_elem_of; [exact Hmrs_in|exact Hmrs_matches]. }
  wp_auto.
  wp_apply (wp_findNewReplicaSet d_l d sl ptrs rss dq_d dq_sl dq
    with "[$Hd $Hsl $Hrss]").
  (* The first conjunct is a match on [find_new_replica_set]; introduce it
     opaquely and rewrite before destructing. *)
  iIntros (rs_l) "[Hm (Hd & Hsl & Hrss)]".
  rewrite Hfound.
  iDestruct "Hm" as %Hlookup.
  wp_auto.
  assert (rss !! i = Some new_rs) as Hrss_lookup.
  { unfold find_new_replica_set in Hfound.
    apply list_find_Some in Hfound as (H1 & _ & _). exact H1. }
  (* The returned pointer is non-null because it owns a ReplicaSet, which is
     what makes the early return fire. *)
  iDestruct (big_sepL2_lookup_acc with "Hrss") as "[Hthis Hrss_restore]";
    [exact Hlookup|exact Hrss_lookup|].
  iPoseProof (ReplicaSetV.deepown_l_split with "Hthis") as
    "(%Hnn & Ht & Hm & Hs & Hst)".
  iPoseProof (ReplicaSetV.deepown_l_restore _ _ _ Hnn
    with "[$Ht $Hm $Hs $Hst]") as "Hthis".
  iDestruct ("Hrss_restore" with "Hthis") as "Hrss".
  rewrite (bool_decide_eq_false_2 _ Hnn). simpl.
  wp_auto.
  iApply ("HΦ" $! rs_l i new_rs). iFrame. done.
Qed.

(* findOldReplicaSets hands back the *filtered* pointer slice while the caller
   still holds deepowns for the whole list, so the bundle has to be split along
   the same filter and put back afterwards. [util.v]'s
   [big_sepL_filter_partition] splits but does not recombine; this is the
   accessor form, over [big_sepL2] and specialised to the [zip] shape
   [old_replica_set_pairs] uses. Belongs in util.v if a second caller appears. *)
Lemma big_sepL2_filter_acc (P : ReplicaSetV.t → Prop)
    `{∀ x, Decision (P x)} (Φ : loc → ReplicaSetV.t → iProp Σ) ptrs rss :
  ([∗ list] ptr;rs ∈ ptrs;rss, Φ ptr rs) -∗
  ([∗ list] ptr;rs ∈ (filter (λ pr, P pr.2) (zip ptrs rss)).*1;
                     (filter (λ pr, P pr.2) (zip ptrs rss)).*2, Φ ptr rs) ∗
  (([∗ list] ptr;rs ∈ (filter (λ pr, P pr.2) (zip ptrs rss)).*1;
                      (filter (λ pr, P pr.2) (zip ptrs rss)).*2, Φ ptr rs) -∗
   ([∗ list] ptr;rs ∈ ptrs;rss, Φ ptr rs)).
Proof.
  iIntros "H".
  iInduction ptrs as [|ptr ptrs] "IH" forall (rss).
  - iDestruct (big_sepL2_nil_inv_l with "H") as %->.
    simpl. iSplitR; [done|]. iIntros "_". done.
  - destruct rss as [|rs rss].
    { iDestruct (big_sepL2_nil_inv_r with "H") as %Hcontra. done. }
    simpl. iDestruct "H" as "[Hhd Htl]".
    iDestruct ("IH" with "Htl") as "[Hold Hrestore]".
    destruct (decide (P rs)) as [HP|HnP].
    + rewrite (filter_cons_True _ (ptr, rs) _ HP). simpl.
      iFrame "Hhd Hold". iIntros "[Hhd2 Hold2]". iFrame "Hhd2".
      iApply "Hrestore". iFrame.
    + rewrite (filter_cons_False _ (ptr, rs) _ HnP).
      iFrame "Hold". iIntros "Hold2". iFrame "Hhd".
      iApply "Hrestore". iFrame.
Qed.

(* ---------------------------------------------------------------- *)
(* Pure consequences of [deployment_realized].                       *)
(* ---------------------------------------------------------------- *)

(* findNewReplicaSet picks the *first* template match; uniqueness forces it to
   be the one [deployment_realized] exhibits, so it already sits at the
   deployment's replica count and reconcileNewReplicaSet is a no-op. *)
Lemma realized_found_at_count d rss i found_rs :
  deployment_realized d rss →
  unique_new_replica_set d rss →
  find_new_replica_set d rss = Some (i, found_rs) →
  rs_replicas found_rs = deployment_replicas d.
Proof.
  intros (mrs & Hmrs_in & Hmrs_matches & Hmrs_count & _) Huniq Hfound.
  unfold find_new_replica_set in Hfound.
  apply list_find_Some in Hfound as (Hi_lookup & Hi_matches & _).
  apply list_elem_of_lookup_1 in Hmrs_in as [j Hj_lookup].
  assert (i = j) as -> by (eapply Huniq; eassumption).
  rewrite Hj_lookup in Hi_lookup. injection Hi_lookup as <-.
  unfold rs_replicas. rewrite Hmrs_count. done.
Qed.

(* Every ReplicaSet findOldReplicaSets keeps is drained to zero.
   [deployment_realized] states this keyed by [ReplicaSetV.key] while
   [rs_is_old] tests UIDs, so NoDup on keys is what bridges the two. *)
Lemma realized_old_drained d rss i found_rs rs :
  deployment_realized d rss →
  unique_new_replica_set d rss →
  NoDup (ReplicaSetV.key <$> rss) →
  find_new_replica_set d rss = Some (i, found_rs) →
  rs ∈ rss →
  rs_is_old (Some found_rs) rs →
  rs_replicas rs = W32 0.
Proof.
  intros Hrealized Huniq Hnodup Hfound Hrs_in Hold.
  pose proof Hrealized as (mrs & Hmrs_in & Hmrs_matches & _ & Hforall).
  (* Identify [found_rs] with the realized ReplicaSet, exactly as above. *)
  pose proof Hfound as Hfound'.
  unfold find_new_replica_set in Hfound'.
  apply list_find_Some in Hfound' as (Hi_lookup & Hi_matches & _).
  apply list_elem_of_lookup_1 in Hmrs_in as [j Hj_lookup].
  assert (i = j) as -> by (eapply Huniq; eassumption).
  rewrite Hj_lookup in Hi_lookup. injection Hi_lookup as <-.
  (* [rs] is old, so its UID differs; NoDup on keys then forces its key to
     differ too, and the Forall leaves only the zero disjunct. *)
  rewrite Forall_lookup in Hforall.
  apply list_elem_of_lookup_1 in Hrs_in as [k Hk_lookup].
  destruct (Hforall k rs Hk_lookup) as [Hkey_eq|Hzero].
  - exfalso. apply Hold.
    assert (k = j) as ->.
    { eapply NoDup_lookup; [exact Hnodup| |].
      - rewrite list_lookup_fmap Hk_lookup /=. reflexivity.
      - rewrite list_lookup_fmap Hj_lookup /= Hkey_eq. reflexivity. }
    rewrite Hj_lookup in Hk_lookup. injection Hk_lookup as <-. done.
  - unfold rs_replicas. rewrite Hzero. done.
Qed.

(* rollout under fractional ownership. The deployment is already realized, so
   getNewReplicaSet adopts rather than creates — which is why the reserved
   fragment comes back [own_available_reserved_frag] unchanged rather than
   splitting on adopted/created the way [wp_rollout] does.

   TRUSTED — Admitted. Discharging it needs stability variants of
   [wp_getNewReplicaSet], [wp_reconcileNewReplicaSet] and
   [wp_reconcileOldReplicaSets], each of which is the corresponding lemma in
   rollout.v with 1 replaced by [dq] and the post-state equal to the
   pre-state. Those are no-ops for the same reason this is: with [dq] the
   scale path cannot be taken, because [scaleReplicaSet] writes. *)
Lemma wp_rollout_stability γ model_l d_l (d : DeploymentV.t)
    sl ptrs (rss : list ReplicaSetV.t) (children_keys : gset KKey.t)
    uid dq_d dq_sl dq_rss dq :
  {{{ "#Hpkg" ∷ is_pkg_init code.controllers.deployment.pkg_id.deployment ∗
      "#Hisk" ∷ is_kubernetes γ model_l ∗
      "#Hglobal_l" ∷ (global_addr apimodel.ModelState) ↦□ model_l ∗
      "Hd" ∷ DeploymentV.deepown_l d_l d dq_d ∗
      "Hsl" ∷ sl ↦*{dq_sl} ptrs ∗
      "Hrss" ∷ ([∗ list] ptr;rs ∈ ptrs;rss, ReplicaSetV.deepown_l ptr rs dq_rss) ∗
      "%Hd_valid" ∷ ⌜ DeploymentV.valid d ⌝ ∗
      "%Hrss_valid" ∷ ⌜ Forall ReplicaSetV.valid rss ⌝ ∗
      "%Hkeys_nodup" ∷ ⌜ NoDup (ReplicaSetV.key <$> rss) ⌝ ∗
      "%Hnamespace_valid" ∷ ⌜ valid_namespace
          d.(DeploymentV.ObjectMeta').(ObjectMetaV.Namespace') ⌝ ∗
      "%Hnew_rs_name_valid" ∷ ⌜ valid_dns1123_subdomain (new_rs_name d) ⌝ ∗
      "%Hunique_new" ∷ ⌜ unique_new_replica_set d rss ⌝ ∗
      "%Hmatch" ∷ ⌜ deployment_realized d rss ⌝ ∗
      "Hreserved" ∷ own_available_reserved_frag γ dq (new_rs_key d) ∗
      "Hown_children" ∷ own_children_frag γ (DeploymentV.key d)
        uid dq children_keys ∗
      "Hown_frags" ∷ ([∗ list] rs ∈ rss,
        own_meta_frag γ (ReplicaSetV.key rs)
          rs.(ReplicaSetV.ObjectMeta').(ObjectMetaV.UID') dq
          rs.(ReplicaSetV.ObjectMeta') ∗
        own_spec_frag γ (ReplicaSetV.key rs)
          rs.(ReplicaSetV.ObjectMeta').(ObjectMetaV.UID') dq
          (ObjectSpecV.ReplicaSetSpec rs.(ReplicaSetV.Spec')))
  }}}
    @! deployment.rollout #d_l #sl
  {{{ RET #interface.nil;
      "Hd" ∷ DeploymentV.deepown_l d_l d dq_d ∗
      "Hsl" ∷ sl ↦*{dq_sl} ptrs ∗
      "Hrss" ∷ ([∗ list] ptr;rs ∈ ptrs;rss, ReplicaSetV.deepown_l ptr rs dq_rss) ∗
      "Hreserved" ∷ own_available_reserved_frag γ dq (new_rs_key d) ∗
      "Hown_children" ∷ own_children_frag γ (DeploymentV.key d)
        uid dq children_keys ∗
      "Hown_frags" ∷ ([∗ list] rs ∈ rss,
        own_meta_frag γ (ReplicaSetV.key rs)
          rs.(ReplicaSetV.ObjectMeta').(ObjectMetaV.UID') dq
          rs.(ReplicaSetV.ObjectMeta') ∗
        own_spec_frag γ (ReplicaSetV.key rs)
          rs.(ReplicaSetV.ObjectMeta').(ObjectMetaV.UID') dq
          (ObjectSpecV.ReplicaSetSpec rs.(ReplicaSetV.Spec')))
  }}}.
Proof.
Admitted.

(* The deletion branch needs no hypothesis: if DeletionTimestamp is set the
   controller returns before rollout, and if it is not set the state is
   already realized. Both paths leave every fragment untouched, so the
   postcondition is the precondition either way and the spec does not have to
   split on it — unlike [wp_syncDeployment], whose two branches differ.

   TRUSTED — Admitted. Beyond [wp_rollout_stability] this needs a stability
   variant of [wp_filterReplicaSetsByOwner], which is itself trusted by
   decision pending notes/questions-08-20.md Q3. *)
Lemma wp_syncDeployment_stability γ model_l namespace name
    d rss children_keys uid kmeta dq :
  ⊢ stability_spec γ model_l namespace name d rss children_keys uid kmeta dq.
Proof.
Admitted.

End proof.
