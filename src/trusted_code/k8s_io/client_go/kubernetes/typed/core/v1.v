From New.golang Require Import defn.
Require Export New.code.k8s_io.api.core.v1.
Require Export New.code.k8s_io.client_go.gentype.
Module api_core_v1 := code.k8s_io.api.core.v1.v1.

Module v1.
Section code.
Context {ext : ffi_syntax} {go_gctx : GoGlobalContext}.

Definition coreV1ClientType : go.type :=
  go.Named "k8s.io/client-go/kubernetes/typed/core/v1.CoreV1Client"%go [].

Definition podClientType : go.type :=
  gentype.Client (go.PointerType api_core_v1.Pod).

(* Go-like equivalent of this trusted shim. This is intentionally not valid
   client-go source: [namespace] is private to package gentype, and the minimal
   generic client does not implement every method in [PodInterface].

   func (c *CoreV1Client) Pods(namespace string) PodInterface {
       return &gentype.Client[*corev1.Pod]{namespace: namespace}
   }
*)
Definition CoreV1Client__Podsⁱᵐᵖˡ : val :=
  λ: "c" "namespace",
    exception_do (let: "c" := (GoAlloc (go.PointerType coreV1ClientType) "c") in
    let: "namespace" := (GoAlloc go.string "namespace") in
    let: "podClient" := (GoAlloc podClientType
      (let: "$v0" := (![go.string] "namespace") in
       CompositeLiteral podClientType
         (LiteralValue [KeyedElement (Some (KeyField "namespace"%go))
           (ElementExpression go.string "$v0")]))) in
    return: (Convert (go.PointerType podClientType) go.any "podClient")).

End code.
End v1.
