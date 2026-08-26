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
  common replica_sets rollout top_level.

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
(* Top-level specs: the controller's entry point and its listing.    *)
(* ---------------------------------------------------------------- *)

(* filterReplicaSetsByOwner lists the deployment's namespace and keeps the
   ReplicaSets whose controller reference points at the deployment.

   TRUSTED — Admitted, and unlike the other Admitted specs in this tree it is
   not merely waiting on a model wrapper. Discharging it needs all of:

     - a spec for the public [ReplicaSetList], which bottoms out in
       [objListBySelector] / [filterByLabelSelector]. Neither has a spec for
       any kind, Pod included; the only listing spec in the tree is for the
       internal [objListLocked].
     - a spec for [metav1.GetControllerOf], which is goose-translated but
       unspecced.
     - the semantic core: that listing a namespace and filtering by controller
       reference yields exactly the keys in [own_children_frag]. That is a
       statement about the model invariant, not something the children fragment
       gives directly.

   See notes/spec-remaining.md and open question 3 — whether to discharge this
   from inv.v or to add a ReplicaSet owner index and mirror the ReplicaSet
   controller. Until that is settled this is trusted base, on top of
   [template_matches] and [template_hash].

   The shape below follows [wp_State__ByIndex_podController], the proven
   analogue for "fetch my children": the caller supplies the objects it already
   holds fragments for, and gets back what the API returned, related to them by
   a permutation modulo resource version. Fragments are threaded through
   unchanged rather than conjured. *)
Lemma wp_filterReplicaSetsByOwner γ model_l d_l (d : DeploymentV.t)
    (rss : list ReplicaSetV.t) (children_keys : gset KKey.t)
    dq_d children_dq :
  {{{ "#Hpkg" ∷ is_pkg_init code.controllers.deployment.pkg_id.deployment ∗
      "#Hisk" ∷ is_kubernetes γ model_l ∗
      "#Hglobal_l" ∷ (global_addr apimodel.ModelState) ↦□ model_l ∗
      "Hd" ∷ DeploymentV.deepown_l d_l d dq_d ∗
      "%Hd_valid" ∷ ⌜ DeploymentV.valid d ⌝ ∗
      "%Hnodup" ∷ ⌜ NoDup (ReplicaSetV.key <$> rss) ⌝ ∗
      (* The caller's [rss] is exactly the ReplicaSet part of the children. *)
      "%Hdom_eq" ∷ ⌜ list_to_set (ReplicaSetV.key <$> rss) =
          filter (λ key, key.(KKey.Kind') = ReplicaSetV.kind) children_keys ⌝ ∗
      "Hown_children" ∷ own_children_frag γ (DeploymentV.key d)
        d.(DeploymentV.ObjectMeta').(ObjectMetaV.UID') children_dq children_keys ∗
      "Hown_frags" ∷ ([∗ list] rs ∈ rss,
        own_meta_frag γ (ReplicaSetV.key rs)
          rs.(ReplicaSetV.ObjectMeta').(ObjectMetaV.UID') 1
          rs.(ReplicaSetV.ObjectMeta') ∗
        own_spec_frag γ (ReplicaSetV.key rs)
          rs.(ReplicaSetV.ObjectMeta').(ObjectMetaV.UID') 1
          (ObjectSpecV.ReplicaSetSpec rs.(ReplicaSetV.Spec')))
  }}}
    @! deployment.filterReplicaSetsByOwner #d_l
  {{{ sl ptrs (rss' : list ReplicaSetV.t) dq', RET (#sl, #interface.nil);
      "Hd" ∷ DeploymentV.deepown_l d_l d dq_d ∗
      "Hsl" ∷ sl ↦* ptrs ∗
      "Hrss'" ∷ ([∗ list] ptr;rs ∈ ptrs;rss',
        ReplicaSetV.deepown_l ptr rs dq') ∗
      (* [rss'] is the same set of objects as [rss], up to resource version. *)
      "%Hmeta_perm" ∷ ⌜ ObjectMetaV.without_resource_version <$>
            (ReplicaSetV.ObjectMeta' <$> rss') ≡ₚ
          ObjectMetaV.without_resource_version <$>
            (ReplicaSetV.ObjectMeta' <$> rss) ⌝ ∗
      "%Hrss'_valid" ∷ ⌜ Forall ReplicaSetV.valid rss' ⌝ ∗
      "%Hnodup'" ∷ ⌜ NoDup (ReplicaSetV.key <$> rss') ⌝ ∗
      (* Every returned ReplicaSet is controlled by this deployment — the
         filter's whole purpose. *)
      "%Hparent_refs" ∷ ⌜ Forall (λ rs,
          obj_parent_ref (KObjectV.ReplicaSet rs) =
            Some (DeploymentV.key d,
                  d.(DeploymentV.ObjectMeta').(ObjectMetaV.UID'))) rss' ⌝ ∗
      "Hown_children" ∷ own_children_frag γ (DeploymentV.key d)
        d.(DeploymentV.ObjectMeta').(ObjectMetaV.UID') children_dq children_keys ∗
      "Hown_frags" ∷ ([∗ list] rs ∈ rss,
        own_meta_frag γ (ReplicaSetV.key rs)
          rs.(ReplicaSetV.ObjectMeta').(ObjectMetaV.UID') 1
          rs.(ReplicaSetV.ObjectMeta') ∗
        own_spec_frag γ (ReplicaSetV.key rs)
          rs.(ReplicaSetV.ObjectMeta').(ObjectMetaV.UID') 1
          (ObjectSpecV.ReplicaSetSpec rs.(ReplicaSetV.Spec')))
  }}}.
Proof.
Admitted.

(* syncDeployment is the controller's entry point: read the deployment, gather
   its ReplicaSets, and — unless the deployment is being deleted — roll out.

   The postcondition is [deployment_realized] rather than a progress measure:
   this controller has no surge pacing, so one sync reaches the desired state.
   [rss_post] is existential because the new ReplicaSet may have been created
   during the sync, in which case it is not among the [rss] the caller framed. *)
Lemma wp_syncDeployment γ model_l (namespace name : go_string)
    (d : DeploymentV.t) (rss : list ReplicaSetV.t)
    (children_keys : gset KKey.t) uid kmeta dq_d children_dq :
  ⊢ progress_spec γ model_l namespace name d rss children_keys uid kmeta
      dq_d children_dq.
Proof.
Admitted.

End proof.
