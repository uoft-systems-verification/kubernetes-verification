From New.proof.k8s_io.apimachinery.pkg.util Require Export uuid_init.
From New.object_specs Require Import common.
From New.proof Require Import prelude empty_ffi.

Section proof.
Context `{hG: !heapGS Σ} `{!ffi_semantics _ _}.
Context {sem : go.Semantics} {package_sem : uuid.Assumptions}.
Local Set Default Proof Using "All".

(** Trusted Kubernetes library boundary for its UUID encoding. Freshness is
    deliberately left to the caller's collision check. *)
Lemma wp_NewUUID :
  {{{ is_pkg_init uuid }}}
    @! uuid.NewUUID #()
  {{{ (uid : types.UID.t), RET #uid; ⌜ valid_uid uid ⌝ }}}.
Proof. Admitted.

End proof.
