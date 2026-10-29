From New.proof Require Export prelude empty_ffi.
From New.proof.kubernetes_model Require Export apimodel_init.
From New.proof.k8s_io.client_go Require Export kubernetes_init.
From New.proof.k8s_io.client_go.listers.apps Require Export v1_init.
From New.proof.k8s_io.client_go.listers.core Require Export v1_init.
From New.proof.k8s_io.client_go.tools Require Export cache_init.
From New.proof Require Export wp_keep.

Module controller_client.
Module cache := code.k8s_io.client_go.tools.cache.cache.
Module apps_listers := code.k8s_io.client_go.listers.apps.v1.v1.
Module core_listers := code.k8s_io.client_go.listers.core.v1.v1.

(* Root receivers of the trusted cache/lister representations. Their physical
   storage is abstract: the bridge queries the separately initialized model. *)
Definition indexer {ext : ffi_syntax} {go_gctx : GoGlobalContext} : interface.t :=
  interface.mk_ok (go.PointerType cache.cache) #null.
Definition replica_set_lister {ext : ffi_syntax} {go_gctx : GoGlobalContext} : interface.t :=
  interface.mk_ok (go.PointerType apps_listers.replicaSetLister) #null.
Definition stateful_set_lister {ext : ffi_syntax} {go_gctx : GoGlobalContext} : interface.t :=
  interface.mk_ok (go.PointerType apps_listers.statefulSetLister) #null.
Definition deployment_lister {ext : ffi_syntax} {go_gctx : GoGlobalContext} : interface.t :=
  interface.mk_ok (go.PointerType apps_listers.deploymentLister) #null.
Definition pod_lister {ext : ffi_syntax} {go_gctx : GoGlobalContext} : interface.t :=
  interface.mk_ok (go.PointerType core_listers.podLister) #null.
Definition claim_lister {ext : ffi_syntax} {go_gctx : GoGlobalContext} : interface.t :=
  interface.mk_ok (go.PointerType core_listers.persistentVolumeClaimLister) #null.

End controller_client.

Ltac wp_controller_cache :=
  try rewrite /controller_client.indexer;
  wp_pures_keep;
  wp_method_call;
  rewrite /trusted_code.k8s_io.client_go.tools.cache.cache.cache__ByIndexⁱᵐᵖˡ;
  wp_call; wp_pures_keep;
  rewrite /trusted_code.k8s_io.client_go.tools.cache.cache.modelByIndex;
  wp_call; wp_auto_keep.

Transparent code.k8s_io.client_go.gentype.gentype.Client.

Ltac controller_type_neq :=
  cbv delta [code.k8s_io.api.core.v1.v1.Pod
    code.k8s_io.api.core.v1.v1.PersistentVolumeClaim
    code.k8s_io.api.core.v1.v1.ServiceAccount
    code.k8s_io.api.core.v1.v1.Namespace
    code.k8s_io.api.apps.v1.v1.ReplicaSet
    code.k8s_io.api.apps.v1.v1.StatefulSet
    code.k8s_io.api.apps.v1.v1.Deployment
    code.k8s_io.api.rbac.v1.v1.ClusterRole];
  discriminate.

Ltac controller_type_decisions :=
  repeat first
    [ rewrite decide_True; [reflexivity|]
    | rewrite decide_False; [controller_type_neq|] ].

Section cache_bridge.
Context `{hG: !heapGS Σ} `{!ffi_semantics _ _}.
Context {sem : go.Semantics}
  {cache_sem : code.k8s_io.client_go.tools.cache.cache.Assumptions}
  {model_sem : apimodel.Assumptions}.
Collection W := sem + cache_sem + model_sem.
Local Set Default Proof Using "All".

Lemma wp_pod_indexer (model_l : loc) (indexed_value : go_string) Φ :
  (global_addr apimodel.ModelState) ↦□ model_l -∗
  WP model_l @! (go.PointerType apimodel.State) @! "ByIndex"
    #"Pod"%go #"podController"%go #indexed_value {{ Φ }} -∗
  WP (MethodResolve controller_client.cache.Indexer "ByIndex"%go
    #controller_client.indexer) #"podController"%go #indexed_value {{ Φ }}.
Proof.
  iIntros "#Hglobal Hcall".
  wp_controller_cache.
  iExact "Hcall".
Qed.

End cache_bridge.

Ltac wp_controller_auto :=
  try wp_auto_keep;
  controller_type_decisions;
  try wp_auto_keep.
