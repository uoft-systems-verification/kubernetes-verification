From New.proof Require Export fmt io math reflect_init strings.
From New.proof.github_com.gogo.protobuf Require Export proto_init.
From New.proof.k8s_io.apimachinery.pkg.apis.meta Require Export v1_init.
From New.proof.k8s_io.apimachinery.pkg Require Export runtime_init.
From New.proof.k8s_io.apimachinery.pkg.runtime Require Export schema_init.
From New.proof.math Require Export bits.
Require Export New.generatedproof.k8s_io.api.rbac.v1.
From New.proof Require Import proof_prelude.


Section proof.
Context `{hG: heapGS Σ} `{!ffi_semantics _ _}.
Context {sem : go.Semantics} {package_sem : code.k8s_io.api.rbac.v1.v1.Assumptions}.
Collection W := sem + package_sem.

#[global] Instance : IsPkgInit (iProp Σ) code.k8s_io.api.rbac.v1.pkg_id.v1 := define_is_pkg_init True%I.
#[global] Instance : GetIsPkgInitWf (iProp Σ) code.k8s_io.api.rbac.v1.pkg_id.v1 := build_get_is_pkg_init_wf.

End proof.
