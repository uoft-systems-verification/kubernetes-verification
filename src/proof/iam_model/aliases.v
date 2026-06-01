From New.proof Require Import prelude.
From New.code Require Export iam_model.
From iris.algebra Require Import gmap gset.

Definition identity_set : Type := gset iammodel.IdentityID.t.

Definition attachment : Type := (iammodel.IdentityID.t * iammodel.PolicyID.t)%type.

Definition attachment_set : Type := gset attachment.

Definition policy_map {ext : ffi_syntax} {go_gctx : GoGlobalContext} : Type :=
  gmap iammodel.PolicyID.t iammodel.IdentityPolicy.t.

Definition policy_id_set : Type := gset iammodel.PolicyID.t.
