From New.proof Require Import prelude empty_ffi.
From New.proof.kubernetes_model Require Export get create_named update.
From New.proof Require Export util.
From New.proof Require Export wp_helpers.
From New.proof.kubernetes_types Require Export prelude.
From New.proof.controllers.deployment Require Export deployment_init.
From New.proof.k8s_io.api.apps Require Export v1.
From New.proof.k8s_io.kubernetes.pkg Require Export controller.
From New.proof.k8s_io.apimachinery.pkg.api Require Export errors.
From New.proof.controllers.deployment Require Export common replica_sets.

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
(* Specs for the state-touching half of the controller.              *)
(*                                                                   *)
(* All five are stated and Admitted. Discharging them needs the      *)
(* ReplicaSet-typed model wrappers (ReplicaSetUpdate / Create), which *)
(* do not exist yet — see notes/spec-remaining.md §4.3. Stating them  *)
(* first is deliberate: the ownership footprints below are what fix   *)
(* the shape those wrappers have to take.                            *)
(*                                                                   *)
(* Convention, following the ReplicaSet and StatefulSet controllers:  *)
(* the preconditions are strong enough to rule out API failure, so    *)
(* every spec returns a nil error.                                    *)
(* ---------------------------------------------------------------- *)

(* scaleReplicaSet is a no-op when the count already matches; otherwise it
   submits a spec that differs only in the replica count. The source object is
   read-only — the code deep-copies before mutating — so [rs] comes back at the
   same fraction, and the freshly-owned result appears only in the scaled
   branch, where it is a distinct object returned by the API. *)
Lemma wp_scaleReplicaSet γ model_l rs_l (rs : ReplicaSetV.t)
    (new_scale : w32) dq :
  {{{ "#Hpkg" ∷ is_pkg_init code.controllers.deployment.pkg_id.deployment ∗
      "#Hisk" ∷ is_kubernetes γ model_l ∗
      "#Hglobal_l" ∷ (global_addr apimodel.ModelState) ↦□ model_l ∗
      "Hrs" ∷ ReplicaSetV.deepown_l rs_l rs dq ∗
      "%Hrs_valid" ∷ ⌜ ReplicaSetV.valid rs ⌝ ∗
      "%Hscale_nonneg" ∷ ⌜ 0 ≤ sint.Z new_scale ⌝ ∗
      "Hown_meta" ∷ own_meta_frag γ (ReplicaSetV.key rs)
        rs.(ReplicaSetV.ObjectMeta').(ObjectMetaV.UID') 1
        rs.(ReplicaSetV.ObjectMeta') ∗
      "Hown_spec" ∷ own_spec_frag γ (ReplicaSetV.key rs)
        rs.(ReplicaSetV.ObjectMeta').(ObjectMetaV.UID') 1
        (ObjectSpecV.ReplicaSetSpec rs.(ReplicaSetV.Spec'))
  }}}
    @! deployment.scaleReplicaSet #rs_l #new_scale
  {{{ (scaled : bool) (rs'_l : loc) (rs' : ReplicaSetV.t),
      RET (#scaled, #rs'_l, #interface.nil);
      "Hrs" ∷ ReplicaSetV.deepown_l rs_l rs dq ∗
      "%Hkey" ∷ ⌜ ReplicaSetV.key rs' = ReplicaSetV.key rs ⌝ ∗
      "%Huid" ∷ ⌜ rs'.(ReplicaSetV.ObjectMeta').(ObjectMetaV.UID') =
          rs.(ReplicaSetV.ObjectMeta').(ObjectMetaV.UID') ⌝ ∗
      "Hown_meta" ∷ own_meta_frag γ (ReplicaSetV.key rs)
        rs.(ReplicaSetV.ObjectMeta').(ObjectMetaV.UID') 1
        rs'.(ReplicaSetV.ObjectMeta') ∗
      "Hown_spec" ∷ own_spec_frag γ (ReplicaSetV.key rs)
        rs.(ReplicaSetV.ObjectMeta').(ObjectMetaV.UID') 1
        (ObjectSpecV.ReplicaSetSpec rs'.(ReplicaSetV.Spec')) ∗
      ( ("%Hnoop" ∷ ⌜ rs_replicas rs = new_scale ∧ scaled = false ∧
             rs' = rs ∧ rs'_l = rs_l ⌝)
        ∨
        ( "%Hscaled" ∷ ⌜ rs_replicas rs ≠ new_scale ∧ scaled = true ⌝ ∗
          "Hrs'" ∷ ReplicaSetV.deepown_l rs'_l rs' 1 ∗
          "%Hspec_updated" ∷ ⌜ ObjectSpecV.updated
              (ObjectSpecV.ReplicaSetSpec (rs_scaled_spec rs new_scale))
              (ObjectSpecV.ReplicaSetSpec rs'.(ReplicaSetV.Spec')) ⌝))
  }}}.
Proof.
Admitted.

(* getNewReplicaSet adopts the existing template-matching ReplicaSet if there is
   one, and otherwise creates it under the deterministic name [new_rs_name d].
   The reserved fragment is what licenses the named create; the children
   fragment is what the new key is added to.

   The IsAlreadyExists path in the Go code re-reads the object rather than
   failing. Under the no-collision assumption that object holds the same
   template, so it is folded into the "adopted" branch here rather than given a
   third outcome — see deployment.go's header and notes/deployment-spec.md §2b. *)
Lemma wp_getNewReplicaSet γ model_l d_l (d : DeploymentV.t)
    sl ptrs (rss : list ReplicaSetV.t) (children : gset KKey.t)
    dq_d dq_rss :
  {{{ "#Hpkg" ∷ is_pkg_init code.controllers.deployment.pkg_id.deployment ∗
      "#Hisk" ∷ is_kubernetes γ model_l ∗
      "#Hglobal_l" ∷ (global_addr apimodel.ModelState) ↦□ model_l ∗
      "Hd" ∷ DeploymentV.deepown_l d_l d dq_d ∗
      "Hsl" ∷ sl ↦*{dq_rss} ptrs ∗
      "Hrss" ∷ ([∗ list] ptr;rs ∈ ptrs;rss, ReplicaSetV.deepown_l ptr rs dq_rss) ∗
      "%Hd_valid" ∷ ⌜ DeploymentV.valid d ⌝ ∗
      "%Hnamespace_valid" ∷ ⌜ valid_namespace
          d.(DeploymentV.ObjectMeta').(ObjectMetaV.Namespace') ⌝ ∗
      "%Hnew_rs_name_valid" ∷ ⌜ valid_dns1123_subdomain (new_rs_name d) ⌝ ∗
      "Hreserved" ∷ own_available_reserved_frag γ 1 (new_rs_key d) ∗
      "Hown_children" ∷ own_children_frag γ (DeploymentV.key d)
        d.(DeploymentV.ObjectMeta').(ObjectMetaV.UID') 1 children
  }}}
    @! deployment.getNewReplicaSet #d_l #sl
  {{{ (new_rs_l : loc) (new_rs : ReplicaSetV.t),
      RET (#new_rs_l, #interface.nil);
      "Hd" ∷ DeploymentV.deepown_l d_l d dq_d ∗
      "Hsl" ∷ sl ↦*{dq_rss} ptrs ∗
      "Hrss" ∷ ([∗ list] ptr;rs ∈ ptrs;rss, ReplicaSetV.deepown_l ptr rs dq_rss) ∗
      "%Hnew_rs_matches" ∷ ⌜ template_matches (rs_template new_rs)
          (deployment_template d) ⌝ ∗
      ( (* Adopted: an existing ReplicaSet already matched, nothing was written. *)
        ( "%Hadopted" ∷ ⌜ ∃ i, find_new_replica_set d rss = Some (i, new_rs) ∧
              ptrs !! i = Some new_rs_l ⌝ ∗
          "Hreserved" ∷ own_available_reserved_frag γ 1 (new_rs_key d) ∗
          "Hown_children" ∷ own_children_frag γ (DeploymentV.key d)
            d.(DeploymentV.ObjectMeta').(ObjectMetaV.UID') 1 children)
        ∨
        (* Created: no ReplicaSet matched, so one was submitted and stored. *)
        ( "%Hcreated" ∷ ⌜ find_new_replica_set d rss = None ⌝ ∗
          "Hnew_rs" ∷ ReplicaSetV.deepown_l new_rs_l new_rs 1 ∗
          "%Hnew_rs_valid" ∷ ⌜ ReplicaSetV.valid new_rs ⌝ ∗
          "%Hnew_rs_key" ∷ ⌜ ReplicaSetV.key new_rs = new_rs_key d ⌝ ∗
          "%Hnew_rs_shape" ∷ ⌜ ∃ submitted,
              is_new_replica_set d submitted ∧
              ObjectSpecV.created
                (ObjectSpecV.ReplicaSetSpec submitted.(ReplicaSetV.Spec'))
                (ObjectSpecV.ReplicaSetSpec new_rs.(ReplicaSetV.Spec')) ⌝ ∗
          "Hown_meta" ∷ own_meta_frag γ (new_rs_key d)
            new_rs.(ReplicaSetV.ObjectMeta').(ObjectMetaV.UID') 1
            new_rs.(ReplicaSetV.ObjectMeta') ∗
          "Hown_spec" ∷ own_spec_frag γ (new_rs_key d)
            new_rs.(ReplicaSetV.ObjectMeta').(ObjectMetaV.UID') 1
            (ObjectSpecV.ReplicaSetSpec new_rs.(ReplicaSetV.Spec')) ∗
          "Hreserved" ∷ own_occupied_reserved_frag γ 1 (new_rs_key d)
            new_rs.(ReplicaSetV.ObjectMeta').(ObjectMetaV.UID') ∗
          "Hown_children" ∷ own_children_frag γ (DeploymentV.key d)
            d.(DeploymentV.ObjectMeta').(ObjectMetaV.UID') 1
            ({[ new_rs_key d ]} ∪ children)))
  }}}.
Proof.
Admitted.

(* reconcileNewReplicaSet scales the new ReplicaSet straight to the
   deployment's replica count — there is no surge pacing in this controller. *)
Lemma wp_reconcileNewReplicaSet γ model_l new_rs_l d_l
    (new_rs : ReplicaSetV.t) (d : DeploymentV.t) dq_rs dq_d :
  {{{ "#Hpkg" ∷ is_pkg_init code.controllers.deployment.pkg_id.deployment ∗
      "#Hisk" ∷ is_kubernetes γ model_l ∗
      "#Hglobal_l" ∷ (global_addr apimodel.ModelState) ↦□ model_l ∗
      "Hnew_rs" ∷ ReplicaSetV.deepown_l new_rs_l new_rs dq_rs ∗
      "Hd" ∷ DeploymentV.deepown_l d_l d dq_d ∗
      "%Hnew_rs_valid" ∷ ⌜ ReplicaSetV.valid new_rs ⌝ ∗
      "%Hd_valid" ∷ ⌜ DeploymentV.valid d ⌝ ∗
      "Hown_meta" ∷ own_meta_frag γ (ReplicaSetV.key new_rs)
        new_rs.(ReplicaSetV.ObjectMeta').(ObjectMetaV.UID') 1
        new_rs.(ReplicaSetV.ObjectMeta') ∗
      "Hown_spec" ∷ own_spec_frag γ (ReplicaSetV.key new_rs)
        new_rs.(ReplicaSetV.ObjectMeta').(ObjectMetaV.UID') 1
        (ObjectSpecV.ReplicaSetSpec new_rs.(ReplicaSetV.Spec'))
  }}}
    @! deployment.reconcileNewReplicaSet #new_rs_l #d_l
  {{{ (scaled : bool) (new_rs' : ReplicaSetV.t),
      RET (#scaled, #interface.nil);
      "Hnew_rs" ∷ ReplicaSetV.deepown_l new_rs_l new_rs dq_rs ∗
      "Hd" ∷ DeploymentV.deepown_l d_l d dq_d ∗
      "Hown_meta" ∷ own_meta_frag γ (ReplicaSetV.key new_rs)
        new_rs.(ReplicaSetV.ObjectMeta').(ObjectMetaV.UID') 1
        new_rs'.(ReplicaSetV.ObjectMeta') ∗
      "Hown_spec" ∷ own_spec_frag γ (ReplicaSetV.key new_rs)
        new_rs.(ReplicaSetV.ObjectMeta').(ObjectMetaV.UID') 1
        (ObjectSpecV.ReplicaSetSpec new_rs'.(ReplicaSetV.Spec')) ∗
      (* Whether or not a write happened, the stored replica count now matches
         the deployment's. This is the postcondition [rollout] actually needs. *)
      "%Hreplicas" ∷ ⌜ new_rs'.(ReplicaSetV.Spec').(ReplicaSetSpecV.Replicas') =
          Some (deployment_replicas d) ⌝ ∗
      "%Hscaled" ∷ ⌜ scaled = bool_decide (rs_replicas new_rs ≠ deployment_replicas d) ⌝
  }}}.
Proof.
Admitted.

(* reconcileOldReplicaSets drains every old ReplicaSet to zero in one pass. *)
Lemma wp_reconcileOldReplicaSets γ model_l sl ptrs
    (old_rss : list ReplicaSetV.t) dq_sl dq_rss :
  {{{ "#Hpkg" ∷ is_pkg_init code.controllers.deployment.pkg_id.deployment ∗
      "#Hisk" ∷ is_kubernetes γ model_l ∗
      "#Hglobal_l" ∷ (global_addr apimodel.ModelState) ↦□ model_l ∗
      "Hsl" ∷ sl ↦*{dq_sl} ptrs ∗
      "Hrss" ∷ ([∗ list] ptr;rs ∈ ptrs;old_rss,
        ReplicaSetV.deepown_l ptr rs dq_rss) ∗
      "%Hrss_valid" ∷ ⌜ Forall ReplicaSetV.valid old_rss ⌝ ∗
      "%Hkeys_nodup" ∷ ⌜ NoDup (ReplicaSetV.key <$> old_rss) ⌝ ∗
      "Hown_frags" ∷ ([∗ list] rs ∈ old_rss,
        own_meta_frag γ (ReplicaSetV.key rs)
          rs.(ReplicaSetV.ObjectMeta').(ObjectMetaV.UID') 1
          rs.(ReplicaSetV.ObjectMeta') ∗
        own_spec_frag γ (ReplicaSetV.key rs)
          rs.(ReplicaSetV.ObjectMeta').(ObjectMetaV.UID') 1
          (ObjectSpecV.ReplicaSetSpec rs.(ReplicaSetV.Spec')))
  }}}
    @! deployment.reconcileOldReplicaSets #sl
  {{{ (scaled_down : bool) (old_rss' : list ReplicaSetV.t),
      RET (#scaled_down, #interface.nil);
      "Hsl" ∷ sl ↦*{dq_sl} ptrs ∗
      "Hrss" ∷ ([∗ list] ptr;rs ∈ ptrs;old_rss,
        ReplicaSetV.deepown_l ptr rs dq_rss) ∗
      "%Hlen" ∷ ⌜ length old_rss' = length old_rss ⌝ ∗
      "Hown_frags" ∷ ([∗ list] rs;rs' ∈ old_rss;old_rss',
        own_meta_frag γ (ReplicaSetV.key rs)
          rs.(ReplicaSetV.ObjectMeta').(ObjectMetaV.UID') 1
          rs'.(ReplicaSetV.ObjectMeta') ∗
        own_spec_frag γ (ReplicaSetV.key rs)
          rs.(ReplicaSetV.ObjectMeta').(ObjectMetaV.UID') 1
          (ObjectSpecV.ReplicaSetSpec rs'.(ReplicaSetV.Spec'))) ∗
      (* Every old ReplicaSet is at zero once this returns. *)
      "%Hdrained" ∷ ⌜ Forall (λ rs',
          rs'.(ReplicaSetV.Spec').(ReplicaSetSpecV.Replicas') = Some (W32 0))
          old_rss' ⌝ ∗
      "%Hscaled_down" ∷ ⌜ scaled_down =
          bool_decide (Exists (λ rs, rs_replicas rs ≠ W32 0) old_rss) ⌝
  }}}.
Proof.
Admitted.

(* rollout performs one reconciliation step: ensure the new ReplicaSet exists
   and sits at the deployment's replica count, and drain every other one.
   Without pacing this reaches the desired state in a single sync, which is why
   the postcondition is an equality rather than a progress measure. *)
Lemma wp_rollout γ model_l d_l (d : DeploymentV.t)
    sl ptrs (rss : list ReplicaSetV.t) (children : gset KKey.t)
    dq_d dq_sl dq_rss :
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
      (* The no-collision assumption, made explicit. Without it findNewReplicaSet
         may pick either of two matching ReplicaSets and stability fails —
         see notes/deployment-spec.md §2b. *)
      "%Hunique_new" ∷ ⌜ unique_new_replica_set d rss ⌝ ∗
      "Hreserved" ∷ own_available_reserved_frag γ 1 (new_rs_key d) ∗
      "Hown_children" ∷ own_children_frag γ (DeploymentV.key d)
        d.(DeploymentV.ObjectMeta').(ObjectMetaV.UID') 1 children ∗
      "Hown_frags" ∷ ([∗ list] rs ∈ rss,
        own_meta_frag γ (ReplicaSetV.key rs)
          rs.(ReplicaSetV.ObjectMeta').(ObjectMetaV.UID') 1
          rs.(ReplicaSetV.ObjectMeta') ∗
        own_spec_frag γ (ReplicaSetV.key rs)
          rs.(ReplicaSetV.ObjectMeta').(ObjectMetaV.UID') 1
          (ObjectSpecV.ReplicaSetSpec rs.(ReplicaSetV.Spec')))
  }}}
    @! deployment.rollout #d_l #sl
  {{{ (new_rs : ReplicaSetV.t) (rss' : list ReplicaSetV.t), RET #interface.nil;
      "Hd" ∷ DeploymentV.deepown_l d_l d dq_d ∗
      "Hsl" ∷ sl ↦*{dq_sl} ptrs ∗
      "Hrss" ∷ ([∗ list] ptr;rs ∈ ptrs;rss, ReplicaSetV.deepown_l ptr rs dq_rss) ∗
      (* The new ReplicaSet matches the template and sits at the deployment's
         count. *)
      "%Hnew_rs_matches" ∷ ⌜ template_matches (rs_template new_rs)
          (deployment_template d) ⌝ ∗
      "%Hnew_rs_replicas" ∷
        ⌜ new_rs.(ReplicaSetV.Spec').(ReplicaSetSpecV.Replicas') =
            Some (deployment_replicas d) ⌝ ∗
      (* Every *other* owned ReplicaSet is at zero. Keyed rather than
         positional, because the new one may or may not be in [rss]. *)
      "%Hold_drained" ∷ ⌜ Forall (λ rs',
          ReplicaSetV.key rs' = ReplicaSetV.key new_rs ∨
          rs'.(ReplicaSetV.Spec').(ReplicaSetSpecV.Replicas') = Some (W32 0))
          rss' ⌝ ∗
      (* [rss'] is the post-state of exactly the ReplicaSets passed in, so
         these fragments cover [rss] and nothing else. *)
      "Hown_frags" ∷ ([∗ list] rs;rs' ∈ rss;rss',
        own_meta_frag γ (ReplicaSetV.key rs)
          rs.(ReplicaSetV.ObjectMeta').(ObjectMetaV.UID') 1
          rs'.(ReplicaSetV.ObjectMeta') ∗
        own_spec_frag γ (ReplicaSetV.key rs)
          rs.(ReplicaSetV.ObjectMeta').(ObjectMetaV.UID') 1
          (ObjectSpecV.ReplicaSetSpec rs'.(ReplicaSetV.Spec'))) ∗
      (* The new ReplicaSet's own fragments are handed back separately only
         when it was created; when it was adopted it is already one of [rss'],
         and claiming its fragments again would duplicate them. *)
      ( ( "%Hadopted" ∷ ⌜ ∃ i, rss' !! i = Some new_rs ⌝ ∗
          "Hreserved" ∷ own_available_reserved_frag γ 1 (new_rs_key d) ∗
          "Hown_children" ∷ own_children_frag γ (DeploymentV.key d)
            d.(DeploymentV.ObjectMeta').(ObjectMetaV.UID') 1 children)
        ∨
        ( "%Hcreated" ∷ ⌜ ReplicaSetV.key new_rs = new_rs_key d ∧
              new_rs_key d ∉ (ReplicaSetV.key <$> rss) ⌝ ∗
          "Hnew_rs_meta" ∷ own_meta_frag γ (new_rs_key d)
            new_rs.(ReplicaSetV.ObjectMeta').(ObjectMetaV.UID') 1
            new_rs.(ReplicaSetV.ObjectMeta') ∗
          "Hnew_rs_spec" ∷ own_spec_frag γ (new_rs_key d)
            new_rs.(ReplicaSetV.ObjectMeta').(ObjectMetaV.UID') 1
            (ObjectSpecV.ReplicaSetSpec new_rs.(ReplicaSetV.Spec')) ∗
          "Hreserved" ∷ own_occupied_reserved_frag γ 1 (new_rs_key d)
            new_rs.(ReplicaSetV.ObjectMeta').(ObjectMetaV.UID') ∗
          "Hown_children" ∷ own_children_frag γ (DeploymentV.key d)
            d.(DeploymentV.ObjectMeta').(ObjectMetaV.UID') 1
            ({[ new_rs_key d ]} ∪ children)))
  }}}.
Proof.
Admitted.

End proof.
