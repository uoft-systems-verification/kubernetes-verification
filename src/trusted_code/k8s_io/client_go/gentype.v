From New.golang Require Import defn.
Require Import New.code.context.
Require Import New.code.kubernetes_model.apimodel.
Require Import New.code.k8s_io.api.core.v1.
Require Import New.code.k8s_io.apimachinery.pkg.apis.meta.v1.
Module api_core_v1 := code.k8s_io.api.core.v1.v1.
Module meta_v1 := code.k8s_io.apimachinery.pkg.apis.meta.v1.v1.

Module gentype.
Section code.
Context {ext : ffi_syntax} {go_gctx : GoGlobalContext}.

Definition clientType (T : go.type) : go.type :=
  go.Named "k8s.io/client-go/gentype.Client"%go [T].

(* Trusted Go equivalent:

   func (c *Client[T]) Create(ctx context.Context, obj T, opts metav1.CreateOptions) (T, error) {
       _ = ctx
       _ = opts
       type podPointer = *corev1.Pod
       typed := any(obj).(podPointer)
       created, err := apimodel.ModelState.PodCreate(c.namespace, typed)
       return any(created).(T), err
   }
*)
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

(* Trusted Go equivalent:

   func (c *Client[T]) Delete(ctx context.Context, name string, opts metav1.DeleteOptions) error {
       _ = ctx
       return apimodel.ModelState.PodDelete(c.namespace, name, opts)
   }
*)
Definition Client__Deleteⁱᵐᵖˡ (T : go.type) : val :=
  λ: "c" "ctx" "name" "opts",
    exception_do (let: "c" := (GoAlloc (go.PointerType (clientType T)) "c") in
    let: "opts" := (GoAlloc meta_v1.DeleteOptions "opts") in
    let: "name" := (GoAlloc go.string "name") in
    let: "namespace" := (GoAlloc go.string (![go.string] (StructFieldRef (clientType T) "namespace"%go (![go.PointerType (clientType T)] "c")))) in
    return: (let: "$a0" := (![go.string] "namespace") in
    let: "$a1" := (![go.string] "name") in
    let: "$a2" := (![meta_v1.DeleteOptions] "opts") in
    (MethodResolve (go.PointerType apimodel.State) "PodDelete"%go
      (![go.PointerType apimodel.State] (GlobalVarAddr apimodel.ModelState #()))) "$a0" "$a1" "$a2")).

End code.
End gentype.
