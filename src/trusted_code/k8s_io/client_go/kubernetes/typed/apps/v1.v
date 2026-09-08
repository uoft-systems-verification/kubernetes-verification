From New.golang Require Import defn.
Require Export New.code.k8s_io.api.apps.v1.
Require Export New.code.k8s_io.client_go.gentype.
Module api_apps_v1 := code.k8s_io.api.apps.v1.v1.
Module gentype_api_apps_v1 := trusted_code.k8s_io.client_go.gentype.api_apps_v1.

Module v1.
Section code.
Context {ext : ffi_syntax} {go_gctx : GoGlobalContext}.

Definition appsV1ClientType : go.type :=
  go.Named "k8s.io/client-go/kubernetes/typed/apps/v1.AppsV1Client"%go [].

Definition replicaSetClientType : go.type :=
  gentype.Client (go.PointerType gentype_api_apps_v1.ReplicaSet).

(* Go-like equivalent of this trusted shim. This is intentionally not valid
   client-go source: [namespace] is private to package gentype, and the minimal
   generic client does not implement every method in [ReplicaSetInterface].

   func (c *AppsV1Client) ReplicaSets(namespace string) ReplicaSetInterface {
       return &gentype.Client[*appsv1.ReplicaSet]{namespace: namespace}
   }
*)
Definition AppsV1Client__ReplicaSetsⁱᵐᵖˡ : val :=
  λ: "c" "namespace",
    exception_do (let: "c" := (GoAlloc (go.PointerType appsV1ClientType) "c") in
    let: "namespace" := (GoAlloc go.string "namespace") in
    let: "replicaSetClient" := (GoAlloc replicaSetClientType
      (let: "$v0" := (![go.string] "namespace") in
       CompositeLiteral replicaSetClientType
         (LiteralValue [KeyedElement (Some (KeyField "namespace"%go))
           (ElementExpression go.string "$v0")]))) in
    return: (Convert (go.PointerType replicaSetClientType) go.any "replicaSetClient")).

End code.
End v1.
