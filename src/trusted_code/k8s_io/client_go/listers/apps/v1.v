From New.golang Require Import defn.
Require Export New.code.k8s_io.api.apps.v1.
Require Export New.code.k8s_io.client_go.listers.
Module api_apps_v1 := code.k8s_io.api.apps.v1.v1.
Module generic_listers := code.k8s_io.client_go.listers.listers.

Module v1.
Section code.
Context {ext : ffi_syntax} {go_gctx : GoGlobalContext}.

Definition replicaSetResourceIndexerType : go.type :=
  generic_listers.ResourceIndexer (go.PointerType api_apps_v1.ReplicaSet).

(* Go-like equivalent of this trusted shim. The trusted representation stores
   only [namespace], the only ResourceIndexer state observed by the trusted Get.
   Consequently, this explanatory code is not valid client-go source.

   func (s *replicaSetLister) ReplicaSets(namespace string) ReplicaSetNamespaceLister {
       return trustedResourceIndexer[*appsv1.ReplicaSet]{namespace: namespace}
   }
*)
Definition replicaSetLister__ReplicaSetsⁱᵐᵖˡ : val :=
  λ: "s" "namespace",
    Convert replicaSetResourceIndexerType go.any "namespace".

Definition statefulSetResourceIndexerType : go.type :=
  generic_listers.ResourceIndexer (go.PointerType api_apps_v1.StatefulSet).

(* Go-like equivalent of this trusted shim. The trusted representation stores
   only [namespace], the only ResourceIndexer state observed by the trusted Get.
   Consequently, this explanatory code is not valid client-go source.

   func (s *statefulSetLister) StatefulSets(namespace string) StatefulSetNamespaceLister {
       return trustedResourceIndexer[*appsv1.StatefulSet]{namespace: namespace}
   }
*)
Definition statefulSetLister__StatefulSetsⁱᵐᵖˡ : val :=
  λ: "s" "namespace",
    Convert statefulSetResourceIndexerType go.any "namespace".

Definition deploymentResourceIndexerType : go.type :=
  generic_listers.ResourceIndexer (go.PointerType api_apps_v1.Deployment).

(* Go-like equivalent of this trusted shim. The trusted representation stores
   only [namespace], the only ResourceIndexer state observed by the trusted Get.
   Consequently, this explanatory code is not valid client-go source.

   func (s *deploymentLister) Deployments(namespace string) DeploymentNamespaceLister {
       return trustedResourceIndexer[*appsv1.Deployment]{namespace: namespace}
   }
*)
Definition deploymentLister__Deploymentsⁱᵐᵖˡ : val :=
  λ: "s" "namespace",
    Convert deploymentResourceIndexerType go.any "namespace".

End code.
End v1.
