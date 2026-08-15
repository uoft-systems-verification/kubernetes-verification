From New.proof Require Import prelude empty_ffi.
From New.proof Require Export util.
From New.proof Require Export wp_helpers.
From New.proof.kubernetes_types Require Export prelude.
From New.proof.controllers.deployment Require Export deployment_init.
From New.proof.k8s_io.api.apps Require Export v1.
From New.proof.k8s_io.kubernetes.pkg Require Export controller.
From New.proof.k8s_io.apimachinery.pkg.api Require Export errors.

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
Local Set Default Proof Using "All".
(* ---------------------------------------------------------------- *)
(* Gallina model of the pure deployment helpers                      *)
(* ---------------------------------------------------------------- *)

Definition deployment_replicas (d : DeploymentV.t) : w32 :=
  match d.(DeploymentV.Spec').(DeploymentSpecV.Replicas') with
  | Some replicas => replicas
  | None => W32 1
  end.

Definition rs_replicas (rs : ReplicaSetV.t) : w32 :=
  match rs.(ReplicaSetV.Spec').(ReplicaSetSpecV.Replicas') with
  | Some replicas => replicas
  | None => W32 0
  end.

Definition rs_opt_replicas (rs_o : option ReplicaSetV.t) : w32 :=
  match rs_o with
  | Some rs => rs_replicas rs
  | None => W32 0
  end.

(* ---------------------------------------------------------------- *)
(* Ownership helpers for nil-able arguments                          *)
(* ---------------------------------------------------------------- *)

(* Ownership of a possibly-nil *apps.ReplicaSet argument. *)
Definition rs_opt_own (l : loc) (rs_o : option ReplicaSetV.t) dq : iProp Σ :=
  match rs_o with
  | Some rs => ReplicaSetV.deepown_l l rs dq
  | None => ⌜ l = null ⌝
  end.

(* Ownership of a possibly-nil map[string]string argument.  ObjectMetaV models
   an absent label/annotation map as None, and Go ranges over a nil map without
   faulting, so cloneAndAddLabel must accept both. *)
Definition labels_opt_own (l : loc)
    (m_o : option (gmap go_string go_string)) dq : iProp Σ :=
  match m_o with
  | Some m => l ↦${dq} m
  | None => ⌜ l = null ⌝
  end.

Definition rs_uid (rs : ReplicaSetV.t) : types.UID.t :=
  rs.(ReplicaSetV.ObjectMeta').(ObjectMetaV.UID').

(* findOldReplicaSets keeps every ReplicaSet other than the new one (matched
   by UID). *)
Definition rs_is_old (new_rs_o : option ReplicaSetV.t) (rs : ReplicaSetV.t) : Prop :=
  match new_rs_o with
  | Some new_rs => rs_uid rs ≠ rs_uid new_rs
  | None => True
  end.

#[global] Instance rs_is_old_dec new_rs_o rs : Decision (rs_is_old new_rs_o rs).
Proof.
  unfold rs_is_old.
  destruct new_rs_o as [new_rs|].
  - destruct (decide (rs_uid rs = rs_uid new_rs)) as [Huid|Huid].
    + right. intros Hneq. exact (Hneq Huid).
    + left. exact Huid.
  - left. done.
Defined.

Definition old_replica_set_pairs (ptrs : list loc) (rss : list ReplicaSetV.t)
    (new_rs_o : option ReplicaSetV.t) : list (loc * ReplicaSetV.t) :=
  filter (λ pr, rs_is_old new_rs_o pr.2) (zip ptrs rss).

(* TODO: un-axiomatize. Once PodTemplateSpecV carries enough structure to state
   template equality, template_matches should become a Definition (equality of
   the templates after deleting the pod-template-hash label from each
   ObjectMeta), the two axioms below should become proved lemmas, and
   wp_equalIgnoreHash in replica_sets.v should be discharged rather than
   Admitted.

   equalIgnoreHash compares pod templates ignoring the pod-template-hash label.
   PodTemplateSpecV is axiomatized, so the comparison relation and the spec
   below are trusted, mirroring controller.v's pod_from_template. *)
Parameter template_matches : PodTemplateSpecV.t → PodTemplateSpecV.t → Prop.
Axiom template_matches_dec : ∀ t1 t2, Decision (template_matches t1 t2).
#[global] Existing Instance template_matches_dec.
Axiom template_matches_sym : ∀ t1 t2, template_matches t1 t2 → template_matches t2 t1.

Definition rs_template (rs : ReplicaSetV.t) : PodTemplateSpecV.t :=
  rs.(ReplicaSetV.Spec').(ReplicaSetSpecV.Template').

Definition deployment_template (d : DeploymentV.t) : PodTemplateSpecV.t :=
  d.(DeploymentV.Spec').(DeploymentSpecV.Template').

(* findNewReplicaSet returns the first ReplicaSet whose template matches the
   deployment's, or nil. *)
Definition find_new_replica_set (d : DeploymentV.t) (rss : list ReplicaSetV.t)
    : option (nat * ReplicaSetV.t) :=
  list_find (λ rs, template_matches (rs_template rs) (deployment_template d)) rss.

End proof.
