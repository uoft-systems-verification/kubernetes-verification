From New.golang Require Import defn.
Require Export New.code.k8s_io.api.core.v1.
Require Export New.code.k8s_io.apimachinery.pkg.runtime.
Require Export New.code.k8s_io.client_go.applyconfigurations.core.v1.
Require Export New.code.k8s_io.client_go.gentype.
Require Export New.code.k8s_io.client_go.rest.
Module api_core_v1 := code.k8s_io.api.core.v1.v1.
Module applyconfigurations_core_v1 := code.k8s_io.client_go.applyconfigurations.core.v1.v1.

Module v1.
Section code.
Context {ext : ffi_syntax} {go_gctx : GoGlobalContext}.

Definition coreV1ClientType : go.type :=
  go.Named "k8s.io/client-go/kubernetes/typed/core/v1.CoreV1Client"%go [].

Definition podsType : go.type :=
  go.Named "k8s.io/client-go/kubernetes/typed/core/v1.pods"%go [].

Definition podClientType : go.type :=
  gentype.ClientWithListAndApply
    (go.PointerType api_core_v1.Pod)
    (go.PointerType api_core_v1.PodList)
    (go.PointerType applyconfigurations_core_v1.PodApplyConfiguration).

Definition emptyPod : val :=
  λ: <>,
    exception_do (return: (GoAlloc api_core_v1.Pod (CompositeLiteral api_core_v1.Pod (LiteralValue [])))).

Definition emptyPodList : val :=
  λ: <>,
    exception_do (return: (GoAlloc api_core_v1.PodList (CompositeLiteral api_core_v1.PodList (LiteralValue [])))).

Definition newPodsⁱᵐᵖˡ : val :=
  λ: "c" "namespace",
    exception_do (let: "c" := (GoAlloc (go.PointerType coreV1ClientType) "c") in
    let: "namespace" := (GoAlloc go.string "namespace") in
    let: "client" := (GoAlloc (go.PointerType podClientType) (let: "$a0" := #"pods"%go in
    let: "$a1" := (GoZeroVal rest.Interface #()) in
    let: "$a2" := (GoZeroVal runtime.ParameterCodec #()) in
    let: "$a3" := (![go.string] "namespace") in
    let: "$a4" := emptyPod in
    let: "$a5" := emptyPodList in
    let: "$a6" := (CompositeLiteral (go.SliceType (gentype.Option (go.PointerType api_core_v1.Pod))) (LiteralValue [])) in
    (FuncResolve gentype.NewClientWithListAndApply
      [go.PointerType api_core_v1.Pod; go.PointerType api_core_v1.PodList; go.PointerType applyconfigurations_core_v1.PodApplyConfiguration] #())
      "$a0" "$a1" "$a2" "$a3" "$a4" "$a5" "$a6")) in
    return: (GoAlloc podsType (let: "$v0" := (![go.PointerType podClientType] "client") in
      CompositeLiteral podsType (LiteralValue [KeyedElement None (ElementExpression (go.PointerType podClientType) "$v0")])))).

End code.
End v1.
