From New.proof.controllers Require Import client.

(* The trusted generic client receiver uses the same named type token. *)
#[global] Transparent code.k8s_io.client_go.gentype.gentype.Client.

(* Only unfold client implementations in the current WP expression. A model
   call must remain folded so its independently proved specification applies. *)
Ltac client_model_has_impl impl :=
  lazymatch goal with
  | |- environments.envs_entails _ (wp _ _ ?e _) =>
      lazymatch e with context[impl] => idtac end
  end.

Ltac wp_client_model_step :=
  try rewrite /controller_client.replica_set_lister /controller_client.stateful_set_lister
    /controller_client.deployment_lister /controller_client.pod_lister /controller_client.claim_lister;
  wp_pures_keep;
  wp_method_call;
  first [
    client_model_has_impl constr:(@trusted_code.k8s_io.client_go.kubernetes.kubernetes.Clientset__CoreV1ⁱᵐᵖˡ);
    rewrite /trusted_code.k8s_io.client_go.kubernetes.kubernetes.Clientset__CoreV1ⁱᵐᵖˡ; wp_call; try wp_auto_keep
  |
    client_model_has_impl constr:(@trusted_code.k8s_io.client_go.kubernetes.kubernetes.Clientset__AppsV1ⁱᵐᵖˡ);
    rewrite /trusted_code.k8s_io.client_go.kubernetes.kubernetes.Clientset__AppsV1ⁱᵐᵖˡ; wp_call; try wp_auto_keep
  |
    client_model_has_impl constr:(@trusted_code.k8s_io.client_go.kubernetes.kubernetes.Clientset__RbacV1ⁱᵐᵖˡ);
    rewrite /trusted_code.k8s_io.client_go.kubernetes.kubernetes.Clientset__RbacV1ⁱᵐᵖˡ; wp_call; try wp_auto_keep
  |
    client_model_has_impl constr:(@trusted_code.k8s_io.client_go.kubernetes.typed.core.v1.v1.CoreV1Client__Podsⁱᵐᵖˡ);
    rewrite /trusted_code.k8s_io.client_go.kubernetes.typed.core.v1.v1.CoreV1Client__Podsⁱᵐᵖˡ; wp_call; try wp_auto_keep
  |
    client_model_has_impl constr:(@trusted_code.k8s_io.client_go.kubernetes.typed.core.v1.v1.CoreV1Client__PersistentVolumeClaimsⁱᵐᵖˡ);
    rewrite /trusted_code.k8s_io.client_go.kubernetes.typed.core.v1.v1.CoreV1Client__PersistentVolumeClaimsⁱᵐᵖˡ; wp_call; try wp_auto_keep
  |
    client_model_has_impl constr:(@trusted_code.k8s_io.client_go.kubernetes.typed.core.v1.v1.CoreV1Client__ServiceAccountsⁱᵐᵖˡ);
    rewrite /trusted_code.k8s_io.client_go.kubernetes.typed.core.v1.v1.CoreV1Client__ServiceAccountsⁱᵐᵖˡ; wp_call; try wp_auto_keep
  |
    client_model_has_impl constr:(@trusted_code.k8s_io.client_go.kubernetes.typed.apps.v1.v1.AppsV1Client__ReplicaSetsⁱᵐᵖˡ);
    rewrite /trusted_code.k8s_io.client_go.kubernetes.typed.apps.v1.v1.AppsV1Client__ReplicaSetsⁱᵐᵖˡ; wp_call; try wp_auto_keep
  |
    client_model_has_impl constr:(@trusted_code.k8s_io.client_go.listers.apps.v1.v1.replicaSetLister__ReplicaSetsⁱᵐᵖˡ);
    rewrite /trusted_code.k8s_io.client_go.listers.apps.v1.v1.replicaSetLister__ReplicaSetsⁱᵐᵖˡ; wp_call; try wp_auto_keep
  |
    client_model_has_impl constr:(@trusted_code.k8s_io.client_go.listers.apps.v1.v1.statefulSetLister__StatefulSetsⁱᵐᵖˡ);
    rewrite /trusted_code.k8s_io.client_go.listers.apps.v1.v1.statefulSetLister__StatefulSetsⁱᵐᵖˡ; wp_call; try wp_auto_keep
  |
    client_model_has_impl constr:(@trusted_code.k8s_io.client_go.listers.apps.v1.v1.deploymentLister__Deploymentsⁱᵐᵖˡ);
    rewrite /trusted_code.k8s_io.client_go.listers.apps.v1.v1.deploymentLister__Deploymentsⁱᵐᵖˡ; wp_call; try wp_auto_keep
  |
    client_model_has_impl constr:(@trusted_code.k8s_io.client_go.listers.core.v1.v1.persistentVolumeClaimLister__PersistentVolumeClaimsⁱᵐᵖˡ);
    rewrite /trusted_code.k8s_io.client_go.listers.core.v1.v1.persistentVolumeClaimLister__PersistentVolumeClaimsⁱᵐᵖˡ; wp_call; try wp_auto_keep
  |
    client_model_has_impl constr:(@trusted_code.k8s_io.client_go.listers.core.v1.v1.podLister__Podsⁱᵐᵖˡ);
    rewrite /trusted_code.k8s_io.client_go.listers.core.v1.v1.podLister__Podsⁱᵐᵖˡ; wp_call; try wp_auto_keep
  |
    client_model_has_impl constr:(@trusted_code.k8s_io.client_go.listers.core.v1.v1.serviceAccountLister__ServiceAccountsⁱᵐᵖˡ);
    rewrite /trusted_code.k8s_io.client_go.listers.core.v1.v1.serviceAccountLister__ServiceAccountsⁱᵐᵖˡ; wp_call; try wp_auto_keep
  |
    client_model_has_impl constr:(@trusted_code.k8s_io.client_go.gentype.gentype.Client__Createⁱᵐᵖˡ);
    rewrite /trusted_code.k8s_io.client_go.gentype.gentype.Client__Createⁱᵐᵖˡ;
      controller_type_decisions;
      rewrite /trusted_code.k8s_io.client_go.gentype.gentype.clientCreate
        /trusted_code.k8s_io.client_go.gentype.gentype.clientType;
      wp_call; wp_controller_auto
  |
    client_model_has_impl constr:(@trusted_code.k8s_io.client_go.gentype.gentype.Client__Deleteⁱᵐᵖˡ);
    rewrite /trusted_code.k8s_io.client_go.gentype.gentype.Client__Deleteⁱᵐᵖˡ;
      controller_type_decisions;
      rewrite /trusted_code.k8s_io.client_go.gentype.gentype.clientDelete
        /trusted_code.k8s_io.client_go.gentype.gentype.clientType;
      wp_call; wp_controller_auto
  |
    client_model_has_impl constr:(@trusted_code.k8s_io.client_go.gentype.gentype.Client__Getⁱᵐᵖˡ);
    rewrite /trusted_code.k8s_io.client_go.gentype.gentype.Client__Getⁱᵐᵖˡ;
      controller_type_decisions;
      rewrite /trusted_code.k8s_io.client_go.gentype.gentype.clientGet
        /trusted_code.k8s_io.client_go.gentype.gentype.clientType;
      wp_call; wp_controller_auto
  |
    client_model_has_impl constr:(@trusted_code.k8s_io.client_go.gentype.gentype.Client__Updateⁱᵐᵖˡ);
    rewrite /trusted_code.k8s_io.client_go.gentype.gentype.Client__Updateⁱᵐᵖˡ;
      controller_type_decisions;
      rewrite /trusted_code.k8s_io.client_go.gentype.gentype.clientCreate
        /trusted_code.k8s_io.client_go.gentype.gentype.clientType;
      wp_call; wp_controller_auto
  |
    client_model_has_impl constr:(@trusted_code.k8s_io.client_go.gentype.gentype.Client__UpdateStatusⁱᵐᵖˡ);
    rewrite /trusted_code.k8s_io.client_go.gentype.gentype.Client__UpdateStatusⁱᵐᵖˡ;
      controller_type_decisions;
      rewrite /trusted_code.k8s_io.client_go.gentype.gentype.clientCreate
        /trusted_code.k8s_io.client_go.gentype.gentype.clientType;
      wp_call; wp_controller_auto
  |
    client_model_has_impl constr:(@trusted_code.k8s_io.client_go.listers.listers.ResourceIndexer__Getⁱᵐᵖˡ);
    rewrite /trusted_code.k8s_io.client_go.listers.listers.ResourceIndexer__Getⁱᵐᵖˡ;
      controller_type_decisions;
      rewrite /trusted_code.k8s_io.client_go.listers.listers.resourceIndexerGet;
      wp_call; try wp_auto_keep
  |
    client_model_has_impl constr:(@trusted_code.k8s_io.client_go.listers.listers.ResourceIndexer__Listⁱᵐᵖˡ);
    rewrite /trusted_code.k8s_io.client_go.listers.listers.ResourceIndexer__Listⁱᵐᵖˡ;
      controller_type_decisions; wp_call; try wp_auto_keep
  ].

Ltac wp_client_model := repeat wp_client_model_step.
