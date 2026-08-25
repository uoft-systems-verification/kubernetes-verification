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
Context `{hG: !heapGS Σ} `{!ffi_semantics _ _}.
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
(* controller (controllers/replicaset/top_level.v:161), "performs no  *)
(* mutation" is not argued from a trace: every fragment below is held *)
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
