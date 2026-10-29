From New.golang Require Import defn.
Require Export New.code.k8s_io.api.rbac.v1.
Require Export New.code.k8s_io.client_go.listers.
Module api_rbac_v1 := code.k8s_io.api.rbac.v1.v1.
Module generic_listers := code.k8s_io.client_go.listers.listers.

Module v1.
Section code.
Context {ext : ffi_syntax} {go_gctx : GoGlobalContext}.

Definition clusterRoleResourceIndexerType : go.type :=
  generic_listers.ResourceIndexer (go.PointerType api_rbac_v1.ClusterRole).

(* ClusterRole is cluster-scoped. As for other listers, the trusted generic
   ResourceIndexer stores only its namespace, empty here. The store is assumed
   synchronized with the model, without informer lag. *)
Definition NewClusterRoleListerⁱᵐᵖˡ : val :=
  λ: "indexer", Convert clusterRoleResourceIndexerType go.any #""%go.

End code.
End v1.
