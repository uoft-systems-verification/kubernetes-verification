From New.golang Require Import defn.
Require Import New.code.kubernetes_model.apimodel.
Require Import New.code.k8s_io.api.apps.v1.
Require Import New.code.k8s_io.api.core.v1.
Module api_apps_v1 := code.k8s_io.api.apps.v1.v1.
Module api_core_v1 := code.k8s_io.api.core.v1.v1.

Module listers.
Section code.
Context {ext : ffi_syntax} {go_gctx : GoGlobalContext}.

(* Trusted Go equivalent:

   func (l ResourceIndexer[T]) Get(name string) (T, error) {
       var zero T
       switch any(zero).(type) {
       case *corev1.Pod:
           obj, err := apimodel.ModelState.PodGet(l.namespace, name)
           return any(obj).(T), err
       case *appsv1.ReplicaSet:
           obj, err := apimodel.ModelState.ReplicaSetGet(l.namespace, name)
           return any(obj).(T), err
       case *corev1.PersistentVolumeClaim:
           obj, err := apimodel.ModelState.PersistentVolumeClaimGet(l.namespace, name)
           return any(obj).(T), err
       case *appsv1.StatefulSet:
           obj, err := apimodel.ModelState.StatefulSetGet(l.namespace, name)
           return any(obj).(T), err
       default:
           panic("unsupported Kubernetes object type")
       }
   }
*)
Definition resourceIndexerGet (T : go.type) (method : go_string) : val :=
  λ: "namespace" "name",
    (* The trusted lister constructor represents its ResourceIndexer by the
       namespace string, which is the only receiver state used by this shim. *)
    let: "namespace" := (GoAlloc go.string "namespace") in
    let: "name" := (GoAlloc go.string "name") in
    let: ("$ret0", "$ret1") := (let: "$a0" := (![go.string] "namespace") in
    let: "$a1" := (![go.string] "name") in
    (MethodResolve (go.PointerType apimodel.State) method
      (![go.PointerType apimodel.State] (GlobalVarAddr apimodel.ModelState #()))) "$a0" "$a1") in
    (TypeAssert T (Convert T go.any "$ret0"), "$ret1").

Definition ResourceIndexer__Getⁱᵐᵖˡ (T : go.type) : val :=
  if decide (T = go.PointerType api_apps_v1.ReplicaSet) then
    resourceIndexerGet T "ReplicaSetGet"%go
  else if decide (T = go.PointerType api_core_v1.Pod) then
    resourceIndexerGet T "PodGet"%go
  else if decide (T = go.PointerType api_core_v1.PersistentVolumeClaim) then
    resourceIndexerGet T "PersistentVolumeClaimGet"%go
  else if decide (T = go.PointerType api_apps_v1.StatefulSet) then
    resourceIndexerGet T "StatefulSetGet"%go
  else
    (λ: "namespace" "name", Panic "unsupported Kubernetes object type")%V.

End code.
End listers.
