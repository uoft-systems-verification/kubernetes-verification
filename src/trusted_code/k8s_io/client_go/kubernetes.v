From New.golang Require Import defn.
Require Export New.code.k8s_io.client_go.kubernetes.typed.apps.v1.
Require Export New.code.k8s_io.client_go.kubernetes.typed.core.v1.
Require Export New.code.k8s_io.client_go.kubernetes.typed.rbac.v1.
Module apps_v1 := code.k8s_io.client_go.kubernetes.typed.apps.v1.v1.
Module core_v1 := code.k8s_io.client_go.kubernetes.typed.core.v1.v1.

Module kubernetes.
Section code.
Context {ext : ffi_syntax} {go_gctx : GoGlobalContext}.

Definition clientsetType : go.type :=
  go.Named "k8s.io/client-go/kubernetes.Clientset"%go [].

Definition appsV1ClientType : go.type :=
  apps_v1.AppsV1Client.

Definition coreV1ClientType : go.type :=
  core_v1.CoreV1Client.

(* Trusted Go equivalent:

   func (c *Clientset) AppsV1() appsv1.AppsV1Interface {
       var client *appsv1.AppsV1Client
       return client
   }
*)
Definition Clientset__AppsV1ⁱᵐᵖˡ : val :=
  λ: "c" <>,
    exception_do (let: "c" := (GoAlloc (go.PointerType clientsetType) "c") in
    return: (#(interface.mk_ok (go.PointerType appsV1ClientType) (#null)))).

(* Trusted Go equivalent:

   func (c *Clientset) CoreV1() corev1.CoreV1Interface {
       var client *corev1.CoreV1Client
       return client
   }
*)
Definition Clientset__CoreV1ⁱᵐᵖˡ : val :=
  λ: "c" <>,
    exception_do (let: "c" := (GoAlloc (go.PointerType clientsetType) "c") in
    return: (#(interface.mk_ok (go.PointerType coreV1ClientType) (#null)))).

(* As for CoreV1 and AppsV1, the clientset receiver is abstract. *)
Definition Clientset__RbacV1ⁱᵐᵖˡ : val :=
  λ: "c" <>,
    #(interface.mk_ok
      (go.PointerType code.k8s_io.client_go.kubernetes.typed.rbac.v1.v1.RbacV1Client) #null).

End code.
End kubernetes.
