From New.proof Require Import prelude empty_ffi.
From New.proof.kubernetes_model Require Export common_update.

(* ResourceVersion plumbing shared by the transaction Update variants. *)

Lemma valid_simple_update_set_resource_version m_old m rv :
  ObjectMetaV.valid_simple_update m_old m →
  ObjectMetaV.valid_simple_update
    m_old (m <| ObjectMetaV.ResourceVersion' := rv |>).
Proof.
  rewrite /ObjectMetaV.valid_simple_update.
  destruct m_old, m; simpl; intuition congruence.
Qed.

Lemma objectmeta_updated_unset_resource_version_input m rv m' :
  ObjectMetaV.updated (m <| ObjectMetaV.ResourceVersion' := rv |>) m' →
  ObjectMetaV.updated m m'.
Proof.
  rewrite /ObjectMetaV.updated.
  destruct m, m'; simpl; intuition congruence.
Qed.
