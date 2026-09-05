From New.golang Require Import defn.
Require Export New.code.context.
Require Export New.code.kubernetes_model.apimodel.
Require Export New.code.k8s_io.api.core.v1.
Require Export New.code.k8s_io.apimachinery.pkg.apis.meta.v1.
Module api_core_v1 := code.k8s_io.api.core.v1.v1.
Module meta_v1 := code.k8s_io.apimachinery.pkg.apis.meta.v1.v1.

Module gentype.
Section code.
Context {ext : ffi_syntax} {go_gctx : GoGlobalContext}.

Definition clientType (T : go.type) : go.type :=
  go.Named "k8s.io/client-go/gentype.Client"%go [T].

Definition Client__Createⁱᵐᵖˡ (T : go.type) : val :=
  λ: "c" "ctx" "obj" "opts",
    exception_do (let: "c" := (GoAlloc (go.PointerType (clientType T)) "c") in
    let: "obj" := (GoAlloc T "obj") in
    let: "namespace" := (GoAlloc go.string (![go.string] (StructFieldRef (clientType T) "namespace"%go (![go.PointerType (clientType T)] "c")))) in
    let: "typed" := (GoAlloc (go.PointerType api_core_v1.Pod)
      (TypeAssert (go.PointerType api_core_v1.Pod) (Convert T go.any (![T] "obj")))) in
    let: ("$ret0", "$ret1") := (let: "$a0" := (![go.string] "namespace") in
    let: "$a1" := (![go.PointerType api_core_v1.Pod] "typed") in
    (MethodResolve (go.PointerType apimodel.State) "PodCreate"%go
      (![go.PointerType apimodel.State] (GlobalVarAddr apimodel.ModelState #()))) "$a0" "$a1") in
    return: (TypeAssert T (Convert (go.PointerType api_core_v1.Pod) go.any "$ret0"), "$ret1")).

End code.
End gentype.
