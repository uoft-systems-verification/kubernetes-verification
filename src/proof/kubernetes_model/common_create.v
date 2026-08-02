From New.proof Require Import prelude empty_ffi.
From New.proof.kubernetes_model Require Export common.
From New.proof.k8s_io.apiserver.pkg.registry Require Export rest.

(* Lightweight infrastructure shared by the independent Create variants. *)

Section proof.
Context `{hG: !heapGS Σ} `{!ffi_semantics _ _}.
Context {sem : go.Semantics} {package_sem : apimodel.Assumptions}.
Context `{!kubernetesModelG Σ}.
Local Set Default Proof Using "All".

Lemma tombed_uid_create_eq_used_uid_sub
    (used_uid tombed_uid current_uids : gset types.UID.t) uid :
  uid ∉ used_uid →
  tombed_uid = used_uid ∖ current_uids →
  tombed_uid = (used_uid ∪ {[uid]}) ∖ ({[uid]} ∪ current_uids).
Proof.
  intros Hfresh ->.
  Timeout 10 set_solver.
Qed.

End proof.
