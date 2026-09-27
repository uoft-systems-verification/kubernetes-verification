From New.proof Require Import prelude empty_ffi.
From New.proof.controllers.replicaset Require Export replicaset_init.
From New.proof.kubernetes_types Require Export prelude.

Module podutil := code.k8s_io.kubernetes.pkg.api.v1.pod.pod.
Module featuregate := code.k8s_io.component_base.featuregate.featuregate.
Module utilfeature := code.k8s_io.apiserver.pkg.util.feature.feature.
Module goreflect := code.reflect.reflect.

Section proof.
Context `{hG: !heapGS Σ} `{!ffi_semantics _ _}.
Context {sem : go.Semantics}
  {package_sem : code.controllers.replicaset.replicaset.Assumptions}.
Collection W := sem + package_sem.
#[local] Instance base_common_sem : common.Assumptions | 100 :=
  code.controllers.replicaset.replicaset.import_common_Assumption.
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
Local Set Default Proof Using "All".

(* Trusted: availability also compares the ready condition's transition time
   with [now], and the time operations it uses (metav1.Time.IsZero,
   time.Time.Add and time.Time.Compare) are not modelled. This spec only
   assumes that the helper terminates, returns some boolean, and leaves the pod
   unchanged. Readiness alone is proven: see [wp_IsPodReady] in
   k8s_io/kubernetes/pkg/api/v1/pod.v. *)
Lemma wp_IsPodAvailable pod_l pod dq (min_ready_seconds : w32) (now : val) :
  {{{ is_pkg_init code.controllers.replicaset.pkg_id.replicaset ∗
      PodV.deepown_l pod_l pod dq
  }}}
    @! podutil.IsPodAvailable #pod_l #min_ready_seconds now
  {{{ (b : bool), RET #b; PodV.deepown_l pod_l pod dq }}}.
Proof. Admitted.

(* Trusted: the global feature gate is an interface value from an untranslated
   package. Querying it only returns some boolean. *)
Lemma wp_DefaultFeatureGate_Enabled (feature : val) :
  {{{ is_pkg_init code.controllers.replicaset.pkg_id.replicaset }}}
    (MethodResolve featuregate.FeatureGate "Enabled"%go
      (![featuregate.FeatureGate] #(global_addr utilfeature.DefaultFeatureGate)) feature)%E
  {{{ (b : bool), RET #b; True }}}.
Proof. Admitted.

(* Trusted: [reflect.DeepEqual] is untranslated; it only reads its arguments
   and returns some boolean. *)
Lemma wp_reflect_DeepEqual (a b : interface.t) :
  {{{ is_pkg_init code.controllers.replicaset.pkg_id.replicaset }}}
    @! goreflect.DeepEqual #a #b
  {{{ (r : bool), RET #r; True }}}.
Proof. Admitted.

End proof.
