From New.proof Require Import prelude empty_ffi.
From New.proof Require Export util.
From New.proof Require Export wp_helpers.
From New.object_specs Require Export prelude.
From New.proof.controllers.deployment Require Export deployment_init.
From New.proof.k8s_io.api.apps Require Export v1.
From New.proof.k8s_io.kubernetes.pkg Require Export controller.
From New.proof.k8s_io.kubernetes.pkg.controller.deployment Require Export util.
From New.proof.k8s_io.kubernetes.pkg.util Require Export labels.
From New.proof.k8s_io.apimachinery.pkg.api Require Export errors.

Section proof.
Context `{hG: !heapGS Σ}.
Context {sem : go.Semantics}
  {package_sem : code.controllers.deployment.deployment.Assumptions}.
Context {model_sem : apimodel.Assumptions}.
Collection W := sem + package_sem + model_sem.
#[local] Instance controller_sem : controller.Assumptions :=
  code.controllers.deployment.deployment.import_controller_Assumption.
#[local] Instance base_apimodel_sem : apimodel.Assumptions | 100 :=
  model_sem.
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
Proof using package_sem model_sem.
  constructor; try exact object_core_v1_sem; try apply _.
Defined.
Local Set Default Proof Using "All".
Context `{!KObjectV.ObjectInterfaceAssumptions}.
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

Definition rs_template (rs : ReplicaSetV.t) : PodTemplateSpecV.t :=
  rs.(ReplicaSetV.Spec').(ReplicaSetSpecV.Template').

Definition deployment_template (d : DeploymentV.t) : PodTemplateSpecV.t :=
  d.(DeploymentV.Spec').(DeploymentSpecV.Template').

(* findNewReplicaSet returns the first ReplicaSet whose template matches the
   deployment's, or nil. *)
Definition find_new_replica_set (d : DeploymentV.t) (rss : list ReplicaSetV.t)
    : option (nat * ReplicaSetV.t) :=
  list_find (λ rs, template_matches (rs_template rs) (deployment_template d)) rss.

(* scaleReplicaSet rewrites only the replica count. *)
Definition rs_scaled_spec (rs : ReplicaSetV.t) (n : w32) : ReplicaSetSpecV.t :=
  ReplicaSetSpecV.mk
    (Some n)
    rs.(ReplicaSetV.Spec').(ReplicaSetSpecV.MinReadySeconds')
    rs.(ReplicaSetV.Spec').(ReplicaSetSpecV.Selector')
    rs.(ReplicaSetV.Spec').(ReplicaSetSpecV.Template').

(* The ReplicaSet [scaleReplicaSet] submits: the deep copy with nothing but the
   replica count overwritten. *)
Definition rs_scaled (rs : ReplicaSetV.t) (n : w32) : ReplicaSetV.t :=
  rs <| ReplicaSetV.Spec' := rs_scaled_spec rs n |>.

(* Rescaling preserves everything admission looks at. The replica count is the
   only field that changes, and a non-negative count is still admissible. *)
Lemma rs_scaled_spec_valid_create rs n :
  ReplicaSetSpecV.valid_create rs.(ReplicaSetV.Spec') →
  0 ≤ sint.Z n →
  ReplicaSetSpecV.valid_create (rs_scaled_spec rs n).
Proof.
  rewrite /ReplicaSetSpecV.valid_create /rs_scaled_spec /=.
  intros (_ & Hmin & Hsel & Htmpl) Hn. split_and!; done.
Qed.

Lemma rs_scaled_valid_create request_kind ns rs n :
  ReplicaSetV.valid rs →
  0 ≤ sint.Z n →
  request_kind = ReplicaSetV.kind →
  ns = rs.(ReplicaSetV.ObjectMeta').(ObjectMetaV.Namespace') →
  ReplicaSetV.valid_create request_kind ns (rs_scaled rs n).
Proof.
  rewrite /ReplicaSetV.valid /ReplicaSetV.valid_create /rs_scaled /=.
  intros (Htm & _ & Hmeta & Hspec & _) Hn Hkind Hns.
  pose proof Hmeta as (_ & _ & _ & Hns_nonempty & Hns_valid & _).
  split_and!.
  - exact Hkind.
  - rewrite Hns. exact Hns_nonempty.
  - rewrite Hns. exact Hns_valid.
  - eapply valid_typemeta_valid_create_typemeta. exact Htm.
  - (* A valid stored ObjectMeta is admissible on create, as for
       [PodV.valid_create_of_valid]. *)
    unfold ObjectMetaV.valid in Hmeta. unfold ObjectMetaV.valid_create.
    destruct Hmeta as (Hgenerate_name & Hname_nonempty & Hname & Hnamespace_nonempty &
      Hnamespace_valid & Huid & Hlabels & Hannotations & Howner_references & Hfinalizers &
      Hmanaged_fields & Hself_link).
    case_decide; first contradiction.
    split; [split; assumption|].
    split; [right; split; [assumption|symmetry; exact Hns]|].
    repeat split; assumption.
  - apply rs_scaled_spec_valid_create; [exact (proj1 Hspec)|exact Hn].
Qed.

End proof.
