From New.golang Require Import defn.
Require Export New.code.k8s_io.api.rbac.v1.
Require Export New.code.k8s_io.client_go.gentype.
Module api_rbac_v1 := code.k8s_io.api.rbac.v1.v1.

Module v1.
Section code.
Context {ext : ffi_syntax} {go_gctx : GoGlobalContext}.

Definition clusterRoleClientType : go.type :=
  gentype.Client (go.PointerType api_rbac_v1.ClusterRole).

(* Cluster-scoped counterpart of the existing typed-client constructors.
   No namespace is needed; the generic ClusterRole Update shim ignores it. *)
Definition RbacV1Client__ClusterRolesⁱᵐᵖˡ : val :=
  λ: "c" <>,
    let: "client" := GoAlloc clusterRoleClientType
      (CompositeLiteral clusterRoleClientType (LiteralValue [])) in
    Convert (go.PointerType clusterRoleClientType) go.any "client".

End code.
End v1.
