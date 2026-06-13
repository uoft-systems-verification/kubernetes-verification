From New.golang Require Import defn.
Require Export New.code.context.
Require Export New.code.kubernetes_model.apimodel.wrapper.
Require Export New.code.k8s_io.apimachinery.pkg.apis.meta.v1.
Module meta_v1 := code.k8s_io.apimachinery.pkg.apis.meta.v1.v1.
Module model_wrapper := code.kubernetes_model.apimodel.wrapper.wrapper.

Module gentype.
Section code.
Context {ext : ffi_syntax} {go_gctx : GoGlobalContext}.

Definition clientType (T : go.type) : go.type :=
  go.Named "k8s.io/client-go/gentype.Client"%go [T].

Definition Client__Createⁱᵐᵖˡ (T : go.type) : val :=
  λ: "c" "ctx" "obj" "opts",
    exception_do (let: "c" := (GoAlloc (go.PointerType (clientType T)) "c") in
    let: "opts" := (GoAlloc meta_v1.CreateOptions "opts") in
    let: "obj" := (GoAlloc T "obj") in
    let: "ctx" := (GoAlloc context.Context "ctx") in
    let: "namespace" := (GoAlloc go.string (![go.string] (StructFieldRef (clientType T) "namespace"%go (![go.PointerType (clientType T)] "c")))) in
    let: "modelClient" := (GoAlloc (go.PointerType (model_wrapper.Client T)) (let: "$a0" := (![go.string] "namespace") in
    (FuncResolve model_wrapper.NewClient [T] #()) "$a0")) in
    let: ("$ret0", "$ret1") := (let: "$a0" := (![context.Context] "ctx") in
    let: "$a1" := (![T] "obj") in
    let: "$a2" := (![meta_v1.CreateOptions] "opts") in
    (MethodResolve (go.PointerType (model_wrapper.Client T)) "Create"%go (![go.PointerType (model_wrapper.Client T)] "modelClient")) "$a0" "$a1" "$a2") in
    return: ("$ret0", "$ret1")).

End code.
End gentype.
