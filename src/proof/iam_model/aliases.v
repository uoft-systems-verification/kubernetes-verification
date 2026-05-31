From New.proof Require Import prelude.
From New.code Require Export iam_model.
From iris.algebra Require Import gmap.

Definition identity_map : Type :=
  gmap iammodel.IdentityID.t (gmap iammodel.PolicyID.t unit).

Definition policy_map {ext : ffi_syntax} {go_gctx : GoGlobalContext} : Type :=
  gmap iammodel.PolicyID.t iammodel.IdentityPolicy.t.

Definition policy_id_set : Type :=
  gmap iammodel.PolicyID.t unit.
