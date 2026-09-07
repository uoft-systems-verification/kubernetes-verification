From New.golang Require Import defn.
Require Export New.code.k8s_io.client_go.kubernetes.typed.core.v1.
Module core_v1 := code.k8s_io.client_go.kubernetes.typed.core.v1.v1.

Module kubernetes.
Section code.
Context {ext : ffi_syntax} {go_gctx : GoGlobalContext}.

Definition clientsetType : go.type :=
  go.Named "k8s.io/client-go/kubernetes.Clientset"%go [].

Definition coreV1ClientType : go.type :=
  core_v1.CoreV1Client.

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

End code.
End kubernetes.
