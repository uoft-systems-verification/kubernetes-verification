From New.golang Require Import defn.
Require Import New.code.kubernetes_model.apimodel.
Require Import New.code.k8s_io.api.apps.v1.
Require Import New.code.k8s_io.api.core.v1.
Require Import New.code.k8s_io.api.rbac.v1.
Module api_apps_v1 := code.k8s_io.api.apps.v1.v1.
Module api_core_v1 := code.k8s_io.api.core.v1.v1.
Module api_rbac_v1 := code.k8s_io.api.rbac.v1.v1.

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
       case *appsv1.Deployment:
           obj, err := apimodel.ModelState.DeploymentGet(l.namespace, name)
           return any(obj).(T), err
       case *corev1.ServiceAccount:
           obj, err := apimodel.ModelState.ServiceAccountGet(l.namespace, name)
           return any(obj).(T), err
       case *corev1.Namespace:
           obj, err := apimodel.ModelState.NamespaceGet(name)
           return any(obj).(T), err
       case *rbacv1.ClusterRole:
           obj, err := apimodel.ModelState.ClusterRoleGet(name)
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
  else if decide (T = go.PointerType api_apps_v1.Deployment) then
    resourceIndexerGet T "DeploymentGet"%go
  else if decide (T = go.PointerType api_core_v1.ServiceAccount) then
    resourceIndexerGet T "ServiceAccountGet"%go
  else if decide (T = go.PointerType api_core_v1.Namespace) then
    (λ: "namespace" "name",
      (MethodResolve (go.PointerType apimodel.State) "NamespaceGet"%go
        (![go.PointerType apimodel.State] (GlobalVarAddr apimodel.ModelState #()))) "name")%V
  else if decide (T = go.PointerType api_rbac_v1.ClusterRole) then
    (λ: "namespace" "name",
      (MethodResolve (go.PointerType apimodel.State) "ClusterRoleGet"%go
        (![go.PointerType apimodel.State] (GlobalVarAddr apimodel.ModelState #()))) "name")%V
  else
    (λ: "namespace" "name", Panic "unsupported Kubernetes object type")%V.

(* The namespace-only representation supports the Pod List used for ReplicaSet
   deletion ranking and ReplicaSet List used by Deployment reconciliation.
   As with Get, these shims assume synchronized caches without informer lag.
   Forward the namespace and selector without modification. *)
Definition ResourceIndexer__Listⁱᵐᵖˡ (T : go.type) : val :=
  if decide (T = go.PointerType api_core_v1.Pod) then
    (λ: "namespace" "selector",
      (MethodResolve (go.PointerType apimodel.State) "PodList"%go
        (![go.PointerType apimodel.State] (GlobalVarAddr apimodel.ModelState #())))
        "namespace" "selector")%V
  else if decide (T = go.PointerType api_apps_v1.ReplicaSet) then
    (λ: "namespace" "selector",
      (MethodResolve (go.PointerType apimodel.State) "ReplicaSetList"%go
        (![go.PointerType apimodel.State] (GlobalVarAddr apimodel.ModelState #())))
        "namespace" "selector")%V
  else if decide (T = go.PointerType api_rbac_v1.ClusterRole) then
    (λ: "namespace" "selector",
      (MethodResolve (go.PointerType apimodel.State) "ClusterRoleList"%go
        (![go.PointerType apimodel.State] (GlobalVarAddr apimodel.ModelState #()))) "selector")%V
  else
    (λ: "namespace" "selector", Panic "unsupported Kubernetes object type for list")%V.

End code.
End listers.
