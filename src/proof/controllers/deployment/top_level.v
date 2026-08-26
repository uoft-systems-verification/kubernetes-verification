From New.proof Require Import prelude empty_ffi.
From New.proof.kubernetes_model Require Export get create_named update.
From New.proof Require Export util.
From New.proof Require Export wp_helpers.
From New.proof.kubernetes_types Require Export prelude.
From New.proof.controllers.deployment Require Export deployment_init.
From New.proof.k8s_io.api.apps Require Export v1.
From New.proof.k8s_io.kubernetes.pkg Require Export controller.
From New.proof.k8s_io.apimachinery.pkg.api Require Export errors.
From New.proof.controllers.deployment Require Export common.

Section specs.
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
(* Shared ownership bundle for the two top-level triples.            *)
(*                                                                   *)
(* The reduction in notes/hoare.md is (M) + (H1) + (H2) + (A1)-(A4). *)
(* H1 is [progress_spec] below, discharged by [wp_syncDeployment] in *)
(* sync_deployment.v; H2 is [stability_spec], discharged by          *)
(* [wp_syncDeployment_stability] in stability.v.                     *)
(*                                                                   *)
(* There is no preservation triple. Preservation is H1's third       *)
(* disjunct ([waiting_on_env]), and this controller never waits on   *)
(* the environment: #7 dropped surge pacing, so the new RS goes to   *)
(* replicasOf(d) and old RSs to 0 in the same sync. H1 collapses to  *)
(* its first disjunct -- see notes/deployment-spec.md 52-58 and Q6.  *)
(* ---------------------------------------------------------------- *)

(* Field names are prefixed because [replicaset/top_level.v] already exports
   [rs_dq] and [children_dq] as global record projections. *)
Record all_fractions := {
  dep_dq : dfrac;
  dep_rs_dq : dfrac;
  dep_children_dq : dfrac;
}.

(* The progress triple writes through the ReplicaSet fragments, so those are
   full. The children fraction stays a parameter rather than being pinned to 1:
   that is exactly how [wp_syncDeployment] was stated before this refactor, and
   changing it is a semantic decision, not a refactor -- see the note on the
   created branch in sync_deployment.v. *)
Definition mutating_fractions (dq children_dq : dfrac) : all_fractions :=
  {| dep_dq := dq; dep_rs_dq := 1; dep_children_dq := children_dq |}.

(* Stability holds everything at the *same* fraction. That is the entire
   mechanism of H2: a write needs the full fraction, so if the proof goes
   through at all, no write happened. *)
Definition stability_fractions (dq : dfrac) : all_fractions :=
  {| dep_dq := dq; dep_rs_dq := dq; dep_children_dq := dq |}.

(* Everything the controller owns going in. The reserved fragment travels with
   the children fragment (both are 1 under [mutating_fractions], both [dq]
   under [stability_fractions]), so it shares [dep_children_dq].

   This is the precondition bundle for both triples, and the *post*condition
   bundle for stability. The progress postcondition cannot use it: its branches
   differ in the children set and in whether the reserved key is available or
   occupied, so it spells those out. *)
Definition owned_resources γ (d : DeploymentV.t)
    (rss : list ReplicaSetV.t) (children_keys : gset KKey.t)
    uid kmeta (fractions : all_fractions) : iProp Σ :=
  "Hown_d_meta" ∷ own_meta_frag γ (DeploymentV.key d) uid
    fractions.(dep_dq) kmeta ∗
  "Hown_d_spec" ∷ own_spec_frag γ (DeploymentV.key d) uid fractions.(dep_dq)
    (ObjectSpecV.DeploymentSpec d.(DeploymentV.Spec')) ∗
  "Hreserved" ∷ own_available_reserved_frag γ fractions.(dep_children_dq)
    (new_rs_key d) ∗
  "Hown_children" ∷ own_children_frag γ (DeploymentV.key d) uid
    fractions.(dep_children_dq) children_keys ∗
  "Hown_frags" ∷ ([∗ list] rs ∈ rss,
    own_meta_frag γ (ReplicaSetV.key rs)
      rs.(ReplicaSetV.ObjectMeta').(ObjectMetaV.UID') fractions.(dep_rs_dq)
      rs.(ReplicaSetV.ObjectMeta') ∗
    own_spec_frag γ (ReplicaSetV.key rs)
      rs.(ReplicaSetV.ObjectMeta').(ObjectMetaV.UID') fractions.(dep_rs_dq)
      (ObjectSpecV.ReplicaSetSpec rs.(ReplicaSetV.Spec'))) ∗
  "%Hkeys_nodup" ∷ ⌜ NoDup (ReplicaSetV.key <$> rss) ⌝.

(* The hypotheses both triples carry. [unique_new_replica_set] is the
   no-collision assumption: findNewReplicaSet returns the *first* template
   match, so with two matches a sync could pick either and stability would be
   false as stated -- notes/questions-08-20.md Q2. *)
Definition input_requirement (d : DeploymentV.t) (rss : list ReplicaSetV.t)
    (children_keys : gset KKey.t) (namespace name : go_string) : Prop :=
  DeploymentV.key d = {|
    KKey.Kind' := DeploymentV.kind;
    KKey.Namespace' := namespace;
    KKey.Name' := name
  |} ∧
  DeploymentV.valid d ∧
  valid_namespace namespace ∧
  valid_dns1123_subdomain (new_rs_name d) ∧
  Forall ReplicaSetV.valid rss ∧
  list_to_set (ReplicaSetV.key <$> rss) =
    filter (λ key, key.(KKey.Kind') = ReplicaSetV.kind) children_keys ∧
  unique_new_replica_set d rss.

(* H1 -- progress. [deployment_realized] rather than a progress measure: with no
   surge pacing one sync reaches the desired state, so [match_distance] would be
   two-valued and the three-disjunct postcondition collapses to its first
   disjunct. [rss_post] is existential because the new ReplicaSet may have been
   created during the sync, in which case it is not among the framed [rss]. *)
Definition progress_spec γ model_l (namespace name : go_string)
    (d : DeploymentV.t) (rss : list ReplicaSetV.t)
    (children_keys : gset KKey.t) uid kmeta dq_d children_dq : iProp Σ :=
  {{{ is_pkg_init code.controllers.deployment.pkg_id.deployment ∗
      "#Hisk" ∷ is_kubernetes γ model_l ∗
      "#Hglobal_l" ∷ (global_addr apimodel.ModelState) ↦□ model_l ∗
      "Hresources" ∷ owned_resources γ d rss children_keys uid kmeta
        (mutating_fractions dq_d children_dq) ∗
      "%Hinput" ∷ ⌜ input_requirement d rss children_keys namespace name ⌝
  }}}
    @! deployment.syncDeployment #namespace #name
  {{{ (rss_post : list ReplicaSetV.t), RET #interface.nil;
      "Hown_d_meta" ∷ own_meta_frag γ (DeploymentV.key d) uid dq_d kmeta ∗
      "Hown_d_spec" ∷ own_spec_frag γ (DeploymentV.key d) uid dq_d
        (ObjectSpecV.DeploymentSpec d.(DeploymentV.Spec')) ∗
      "Hown_frags" ∷ ([∗ list] rs ∈ rss_post,
        own_meta_frag γ (ReplicaSetV.key rs)
          rs.(ReplicaSetV.ObjectMeta').(ObjectMetaV.UID') 1
          rs.(ReplicaSetV.ObjectMeta') ∗
        own_spec_frag γ (ReplicaSetV.key rs)
          rs.(ReplicaSetV.ObjectMeta').(ObjectMetaV.UID') 1
          (ObjectSpecV.ReplicaSetSpec rs.(ReplicaSetV.Spec'))) ∗
      ( (* Deleting: the controller returns early and touches nothing. *)
        ( "%Hdeleting" ∷ ⌜ is_Some
              kmeta.(ObjectMetaV.DeletionTimestamp') ∧ rss_post = rss ⌝ ∗
          "Hreserved" ∷ own_available_reserved_frag γ children_dq (new_rs_key d) ∗
          "Hown_children" ∷ own_children_frag γ (DeploymentV.key d)
            uid children_dq children_keys)
        ∨
        (* Live: one sync realizes the deployment. *)
        ( "%Hnot_deleting" ∷ ⌜ kmeta.(ObjectMetaV.DeletionTimestamp') = None ⌝ ∗
          "%Hrealized" ∷ ⌜ deployment_realized d rss_post ⌝ ∗
          "%Hunique_new'" ∷ ⌜ unique_new_replica_set d rss_post ⌝ ∗
          (* Either the new ReplicaSet was adopted from [rss], or it was created
             and [rss_post] has it on top. *)
          ( ( "%Hadopted" ∷ ⌜ rss_post = rss ⌝ ∗
              "Hreserved" ∷ own_available_reserved_frag γ children_dq
                (new_rs_key d) ∗
              "Hown_children" ∷ own_children_frag γ (DeploymentV.key d)
                uid children_dq children_keys)
            ∨
            ( "%Hcreated" ∷ ⌜ ∃ new_rs, rss_post = rss ++ [new_rs] ∧
                  ReplicaSetV.key new_rs = new_rs_key d ⌝ ∗
              "Hreserved" ∷ own_occupied_reserved_frag γ children_dq
                (new_rs_key d) d.(DeploymentV.ObjectMeta').(ObjectMetaV.UID') ∗
              "Hown_children" ∷ own_children_frag γ (DeploymentV.key d)
                uid children_dq ({[ new_rs_key d ]} ∪ children_keys)))))
  }}}.

(* H2 -- stability. Nothing moves, so the postcondition is the precondition.

   No hypothesis on the deletion timestamp: if it is set the controller returns
   before rollout, and if it is not the state is already realized. Both paths
   leave every fragment untouched, unlike [progress_spec] whose branches differ. *)
Definition stability_spec γ model_l (namespace name : go_string)
    (d : DeploymentV.t) (rss : list ReplicaSetV.t)
    (children_keys : gset KKey.t) uid kmeta dq : iProp Σ :=
  {{{ is_pkg_init code.controllers.deployment.pkg_id.deployment ∗
      "#Hisk" ∷ is_kubernetes γ model_l ∗
      "#Hglobal_l" ∷ (global_addr apimodel.ModelState) ↦□ model_l ∗
      "Hresources" ∷ owned_resources γ d rss children_keys uid kmeta
        (stability_fractions dq) ∗
      "%Hinput" ∷ ⌜ input_requirement d rss children_keys namespace name ⌝ ∗
      "%Hmatch" ∷ ⌜ deployment_realized d rss ⌝
  }}}
    @! deployment.syncDeployment #namespace #name
  {{{ (err : interface.t), RET #err;
      owned_resources γ d rss children_keys uid kmeta (stability_fractions dq)
  }}}.

End specs.
