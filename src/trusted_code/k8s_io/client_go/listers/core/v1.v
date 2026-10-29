From New.golang Require Import defn.
Require Export New.code.k8s_io.api.core.v1.
Require Export New.code.k8s_io.client_go.listers.
Module api_core_v1 := code.k8s_io.api.core.v1.v1.
Module generic_listers := code.k8s_io.client_go.listers.listers.

Module v1.
Section code.
Context {ext : ffi_syntax} {go_gctx : GoGlobalContext}.

Definition persistentVolumeClaimResourceIndexerType : go.type :=
  generic_listers.ResourceIndexer (go.PointerType api_core_v1.PersistentVolumeClaim).

(* As for the apps listers, represent the namespaced ResourceIndexer by its
   namespace string. ResourceIndexer.Get redirects to the model's PVC Get.
   This assumes a cache synchronized with the model, without informer lag. *)
Definition persistentVolumeClaimLister__PersistentVolumeClaimsⁱᵐᵖˡ : val :=
  λ: "s" "namespace",
    Convert persistentVolumeClaimResourceIndexerType go.any "namespace".

Definition podResourceIndexerType : go.type :=
  generic_listers.ResourceIndexer (go.PointerType api_core_v1.Pod).

(* As for the apps listers, represent the namespaced ResourceIndexer by its
   namespace string. ResourceIndexer.Get redirects to the model's Pod Get.
   This assumes a cache synchronized with the model, without informer lag. *)
Definition podLister__Podsⁱᵐᵖˡ : val :=
  λ: "s" "namespace",
    Convert podResourceIndexerType go.any "namespace".

Definition serviceAccountResourceIndexerType : go.type :=
  generic_listers.ResourceIndexer (go.PointerType api_core_v1.ServiceAccount).

(* As for the apps listers, represent the namespaced ResourceIndexer by its
   namespace string. ResourceIndexer.Get redirects to the model's ServiceAccount Get.
   This assumes a cache synchronized with the model, without informer lag. *)
Definition serviceAccountLister__ServiceAccountsⁱᵐᵖˡ : val :=
  λ: "s" "namespace",
    Convert serviceAccountResourceIndexerType go.any "namespace".

Definition namespaceResourceIndexerType : go.type :=
  generic_listers.ResourceIndexer (go.PointerType api_core_v1.Namespace).

(* Cluster-scoped listers use an empty namespace in the trusted generic
   ResourceIndexer representation. They assume synchronized informer stores. *)
Definition NewNamespaceListerⁱᵐᵖˡ : val :=
  λ: "indexer", Convert namespaceResourceIndexerType go.any #""%go.

End code.
End v1.
