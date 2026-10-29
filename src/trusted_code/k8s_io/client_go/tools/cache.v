From New.golang Require Import defn.
Require Import New.code.kubernetes_model.apimodel.

Module cache.
Section code.
Context {ext : ffi_syntax} {go_gctx : GoGlobalContext}.

(* Represent synchronized informer stores for the two controller indexes:
   PodControllerIndex ("podController") belongs to the Pod store, and
   controllerUID belongs to the ReplicaSet store. Only those matching
   receiver/index pairs are covered by this trusted contract. The receiver's
   storage is abstract, and informer lag is not modeled. Unsupported index
   names deliberately panic rather than being silently treated as Pod indexes.

   Go-like equivalent under those assumptions:
     func (c *cache) ByIndex(indexName, indexedValue string) ([]interface{}, error) {
         switch indexName {
         case "podController":
             return apimodel.ModelState.ByIndex("Pod", indexName, indexedValue)
         case "controllerUID":
             return apimodel.ModelState.ByIndex("ReplicaSet", indexName, indexedValue)
         default:
             panic("unsupported informer index")
         }
     }
*)
Definition modelByIndex (kind : go_string) : val :=
  λ: "indexName" "indexedValue",
    (MethodResolve (go.PointerType apimodel.State) "ByIndex"%go
      (![go.PointerType apimodel.State] (GlobalVarAddr apimodel.ModelState #())))
      #kind "indexName" "indexedValue".

Definition cache__ByIndexⁱᵐᵖˡ : val :=
  λ: "c" "indexName" "indexedValue",
    if: "indexName" =⟨go.string⟩ #"podController"%go then
      modelByIndex "Pod"%go "indexName" "indexedValue"
    else if: "indexName" =⟨go.string⟩ #"controllerUID"%go then
      modelByIndex "ReplicaSet"%go "indexName" "indexedValue"
    else Panic "unsupported informer index".

End code.
End cache.
