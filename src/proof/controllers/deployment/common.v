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

(* cloneSelectorAndAddLabel returns a copy of [selector] whose MatchLabels are
   [selector]'s plus one binding.  A nil MatchLabels is first replaced by a fresh
   empty map, so the result's MatchLabels is always Some. *)
Definition selector_with_label (selector : LabelSelectorV.t)
    (key value : go_string) : LabelSelectorV.t :=
  LabelSelectorV.mk
    (Some (<[key := value]>
      (default ∅ selector.(LabelSelectorV.MatchLabels'))))
    selector.(LabelSelectorV.MatchExpressions').

Definition rs_uid (rs : ReplicaSetV.t) : types.UID.t :=
  rs.(ReplicaSetV.ObjectMeta').(ObjectMetaV.UID').

(* findOldReplicaSets keeps every ReplicaSet whose UID differs from the new
   one's. Keyed on the bare UID rather than the ReplicaSet it came from,
   matching the Go: the loop only ever needs a value to compare against, and
   taking the object would oblige a caller that already owns it through the
   list to own it a second time — which [deepown_l] cannot supply, since three
   of the predicates under it are opaque Axioms. See
   notes/deployment-spec-aug-26.md §3.1. *)
Definition rs_is_old (new_rs_uid : types.UID.t) (rs : ReplicaSetV.t) : Prop :=
  rs_uid rs ≠ new_rs_uid.

#[global] Instance rs_is_old_dec new_rs_uid rs : Decision (rs_is_old new_rs_uid rs).
Proof. unfold rs_is_old. apply _. Defined.

Definition old_replica_set_pairs (ptrs : list loc) (rss : list ReplicaSetV.t)
    (new_rs_uid : types.UID.t) : list (loc * ReplicaSetV.t) :=
  filter (λ pr, rs_is_old new_rs_uid pr.2) (zip ptrs rss).

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

(* ---------------------------------------------------------------- *)
(* Model of the state-touching helpers                               *)
(* ---------------------------------------------------------------- *)

Definition deployment_unique_label_key : go_string := "pod-template-hash"%go.

(* TODO: un-axiomatize alongside [template_matches]. controller.ComputeHash is
   goose-translated but has no WP spec, so the hash it returns is trusted here
   the same way template equality is. The only property the controller relies on
   is that matching templates hash equally, which is what makes the deterministic
   RS name stable across syncs — that is [template_hash_respects_matches]. *)
Parameter template_hash : PodTemplateSpecV.t → go_string.
Axiom template_hash_respects_matches : ∀ t1 t2,
  template_matches t1 t2 → template_hash t1 = template_hash t2.

(* scaleReplicaSet rewrites only the replica count. *)
Definition rs_scaled_spec (rs : ReplicaSetV.t) (n : w32) : ReplicaSetSpecV.t :=
  ReplicaSetSpecV.mk
    (Some n)
    rs.(ReplicaSetV.Spec').(ReplicaSetSpecV.MinReadySeconds')
    rs.(ReplicaSetV.Spec').(ReplicaSetSpecV.Selector')
    rs.(ReplicaSetV.Spec').(ReplicaSetSpecV.Template').

(* The labels getNewReplicaSet stamps onto the new ReplicaSet's template, and
   the selector it derives, both add the pod-template-hash binding. *)
Definition new_rs_labels (d : DeploymentV.t) : gmap go_string go_string :=
  <[deployment_unique_label_key := template_hash (deployment_template d)]>
    (default ∅
      (deployment_template d).(PodTemplateSpecV.ObjectMeta').(ObjectMetaV.Labels')).

Definition new_rs_selector (d : DeploymentV.t) : option LabelSelectorV.t :=
  (λ selector, selector_with_label selector
     deployment_unique_label_key (template_hash (deployment_template d)))
  <$> d.(DeploymentV.Spec').(DeploymentSpecV.Selector').

Definition new_rs_name (d : DeploymentV.t) : go_string :=
  d.(DeploymentV.ObjectMeta').(ObjectMetaV.Name') ++ "-"%go ++
    template_hash (deployment_template d).

Definition new_rs_key (d : DeploymentV.t) : KKey.t :=
  {|
    KKey.Kind' := ReplicaSetV.kind;
    KKey.Namespace' := d.(DeploymentV.ObjectMeta').(ObjectMetaV.Namespace');
    KKey.Name' := new_rs_name d
  |}.

(* The template stamped onto the new ReplicaSet: the deployment's, with the
   pod-template-hash label added. Note ComputeHash runs on the deep copy
   *before* the label is added, so the hash is of the deployment's template. *)
Definition new_rs_template (d : DeploymentV.t) : PodTemplateSpecV.t :=
  PodTemplateSpecV.mk
    ((deployment_template d).(PodTemplateSpecV.ObjectMeta')
       <| ObjectMetaV.Labels' := Some (new_rs_labels d) |>)
    (deployment_template d).(PodTemplateSpecV.Spec').

(* Characterizes the ReplicaSet getNewReplicaSet submits. Stated field-by-field
   because that is what the callers need: [rollout] only ever reads back the
   replica count and the template. *)
Definition is_new_replica_set (d : DeploymentV.t) (rs : ReplicaSetV.t) : Prop :=
  rs.(ReplicaSetV.ObjectMeta').(ObjectMetaV.Name') = new_rs_name d ∧
  rs.(ReplicaSetV.ObjectMeta').(ObjectMetaV.Namespace') =
    d.(DeploymentV.ObjectMeta').(ObjectMetaV.Namespace') ∧
  rs.(ReplicaSetV.ObjectMeta').(ObjectMetaV.Labels') = Some (new_rs_labels d) ∧
  obj_parent_ref_is (KObjectV.ReplicaSet rs) DeploymentV.kind
    d.(DeploymentV.ObjectMeta').(ObjectMetaV.Name')
    d.(DeploymentV.ObjectMeta').(ObjectMetaV.UID') ∧
  rs.(ReplicaSetV.Spec').(ReplicaSetSpecV.Replicas') =
    Some (deployment_replicas d) ∧
  rs.(ReplicaSetV.Spec').(ReplicaSetSpecV.MinReadySeconds') =
    d.(DeploymentV.Spec').(DeploymentSpecV.MinReadySeconds') ∧
  rs.(ReplicaSetV.Spec').(ReplicaSetSpecV.Selector') = new_rs_selector d ∧
  rs_template rs = new_rs_template d.

(* ---------------------------------------------------------------- *)
(* Top-level predicates                                              *)
(* ---------------------------------------------------------------- *)

(* At most one of [rss] matches the deployment's template.

   This is a precondition, not a theorem: [findNewReplicaSet] returns the
   *first* match, so with two matching ReplicaSets a sync could pick either and
   the choice would not be stable across syncs. See notes/deployment-spec.md
   §2b. Carried by [wp_rollout] and [wp_syncDeployment]. *)
Definition unique_new_replica_set (d : DeploymentV.t) (rss : list ReplicaSetV.t)
    : Prop :=
  ∀ i j rs_i rs_j,
    rss !! i = Some rs_i → rss !! j = Some rs_j →
    template_matches (rs_template rs_i) (deployment_template d) →
    template_matches (rs_template rs_j) (deployment_template d) →
    i = j.

(* The deployment's desired state is realized by [rss]: some ReplicaSet carries
   the deployment's template and sits at its replica count, and every other one
   is drained to zero.

   Deliberately scoped to template and replica count only. It does *not*
   constrain the pod-template-hash selector/label machinery — [is_new_replica_set]
   covers that for the objects this controller creates, but a ReplicaSet adopted
   from the API server need not satisfy it. This is exactly what [wp_rollout]'s
   postcondition delivers. *)
Definition deployment_realized (d : DeploymentV.t) (rss : list ReplicaSetV.t)
    : Prop :=
  ∃ new_rs,
    new_rs ∈ rss ∧
    template_matches (rs_template new_rs) (deployment_template d) ∧
    new_rs.(ReplicaSetV.Spec').(ReplicaSetSpecV.Replicas') =
      Some (deployment_replicas d) ∧
    Forall (λ rs,
      ReplicaSetV.key rs = ReplicaSetV.key new_rs ∨
      rs.(ReplicaSetV.Spec').(ReplicaSetSpecV.Replicas') = Some (W32 0)) rss.

End proof.
