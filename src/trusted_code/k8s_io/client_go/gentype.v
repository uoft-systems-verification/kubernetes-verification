From New.golang Require Import defn.
Require Import New.code.context.
Require Import New.code.kubernetes_model.apimodel.
Require Import New.code.k8s_io.api.apps.v1.
Require Import New.code.k8s_io.api.core.v1.
Require Import New.code.k8s_io.apimachinery.pkg.apis.meta.v1.
Module api_apps_v1 := code.k8s_io.api.apps.v1.v1.
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
       switch typed := any(obj).(type) {
       case *corev1.Pod:
           created, err := apimodel.ModelState.PodCreate(c.namespace, typed)
           return any(created).(T), err
       case *appsv1.ReplicaSet:
           created, err := apimodel.ModelState.ReplicaSetCreate(c.namespace, typed)
           return any(created).(T), err
       case *corev1.PersistentVolumeClaim:
           created, err := apimodel.ModelState.PersistentVolumeClaimCreate(c.namespace, typed)
           return any(created).(T), err
       case *appsv1.StatefulSet:
           created, err := apimodel.ModelState.StatefulSetCreate(c.namespace, typed)
           return any(created).(T), err
       default:
           panic("unsupported Kubernetes object type")
       }
   }
*)
Definition clientCreate (T objectType : go.type) (method : go_string) : val :=
  λ: "c" "ctx" "obj" "opts",
    exception_do (let: "c" := (GoAlloc (go.PointerType (clientType T)) "c") in
    let: "obj" := (GoAlloc T "obj") in
    let: "namespace" := (GoAlloc go.string (![go.string] (StructFieldRef (clientType T) "namespace"%go (![go.PointerType (clientType T)] "c")))) in
    let: "typed" := (GoAlloc objectType (TypeAssert objectType (Convert T go.any (![T] "obj")))) in
    let: ("$ret0", "$ret1") := (let: "$a0" := (![go.string] "namespace") in
    let: "$a1" := (![objectType] "typed") in
    (MethodResolve (go.PointerType apimodel.State) method
      (![go.PointerType apimodel.State] (GlobalVarAddr apimodel.ModelState #()))) "$a0" "$a1") in
    return: (TypeAssert T (Convert objectType go.any "$ret0"), "$ret1")).

Definition Client__Createⁱᵐᵖˡ (T : go.type) : val :=
  if decide (T = go.PointerType api_core_v1.Pod) then
    clientCreate T (go.PointerType api_core_v1.Pod) "PodCreate"%go
  else if decide (T = go.PointerType api_apps_v1.ReplicaSet) then
    clientCreate T (go.PointerType api_apps_v1.ReplicaSet) "ReplicaSetCreate"%go
  else if decide (T = go.PointerType api_core_v1.PersistentVolumeClaim) then
    clientCreate T (go.PointerType api_core_v1.PersistentVolumeClaim) "PersistentVolumeClaimCreate"%go
  else if decide (T = go.PointerType api_apps_v1.StatefulSet) then
    clientCreate T (go.PointerType api_apps_v1.StatefulSet) "StatefulSetCreate"%go
  else
    (λ: "c" "ctx" "obj" "opts", Panic "unsupported Kubernetes object type")%V.

(* Trusted Go equivalent:

   func (c *Client[T]) Delete(ctx context.Context, name string, opts metav1.DeleteOptions) error {
       _ = ctx
       var zero T
       switch any(zero).(type) {
       case *corev1.Pod:
           return apimodel.ModelState.PodDelete(c.namespace, name, opts)
       case *appsv1.ReplicaSet:
           return apimodel.ModelState.ReplicaSetDelete(c.namespace, name, opts)
       case *corev1.PersistentVolumeClaim:
           return apimodel.ModelState.PersistentVolumeClaimDelete(c.namespace, name, opts)
       case *appsv1.StatefulSet:
           return apimodel.ModelState.StatefulSetDelete(c.namespace, name, opts)
       default:
           panic("unsupported Kubernetes object type")
       }
   }
*)
Definition clientDelete (T : go.type) (method : go_string) : val :=
  λ: "c" "ctx" "name" "opts",
    exception_do (let: "c" := (GoAlloc (go.PointerType (clientType T)) "c") in
    let: "opts" := (GoAlloc meta_v1.DeleteOptions "opts") in
    let: "name" := (GoAlloc go.string "name") in
    let: "namespace" := (GoAlloc go.string (![go.string] (StructFieldRef (clientType T) "namespace"%go (![go.PointerType (clientType T)] "c")))) in
    return: (let: "$a0" := (![go.string] "namespace") in
    let: "$a1" := (![go.string] "name") in
    let: "$a2" := (![meta_v1.DeleteOptions] "opts") in
    (MethodResolve (go.PointerType apimodel.State) method
      (![go.PointerType apimodel.State] (GlobalVarAddr apimodel.ModelState #()))) "$a0" "$a1" "$a2")).

Definition Client__Deleteⁱᵐᵖˡ (T : go.type) : val :=
  if decide (T = go.PointerType api_core_v1.Pod) then
    clientDelete T "PodDelete"%go
  else if decide (T = go.PointerType api_apps_v1.ReplicaSet) then
    clientDelete T "ReplicaSetDelete"%go
  else if decide (T = go.PointerType api_core_v1.PersistentVolumeClaim) then
    clientDelete T "PersistentVolumeClaimDelete"%go
  else if decide (T = go.PointerType api_apps_v1.StatefulSet) then
    clientDelete T "StatefulSetDelete"%go
  else
    (λ: "c" "ctx" "name" "opts", Panic "unsupported Kubernetes object type")%V.

End code.
End gentype.
