Require Export New.generatedproof.k8s_io.apimachinery.pkg.labels.
From New.proof Require Import proof_prelude.
From New.proof Require Export sort_init strconv_init.
From New.proof.k8s_io.klog Require Export klog_init.
From New.proof.k8s_io.apimachinery.pkg Require Export selection_init.
From New.proof.k8s_io.apimachinery.pkg.util Require Export validation_init.
From New.proof.k8s_io.apimachinery.pkg.util.validation Require Export field_init.


Section proof.
Context `{hG: heapGS Σ} `{!ffi_semantics _ _}.
Context {sem : go.Semantics} {package_sem : labels.Assumptions}.
Collection W := sem + package_sem.

Definition is_initialized : iProp Σ :=
  "#Heverything" ∷ (global_addr labels.sharedEverythingSelector) ↦□
    interface.ok (interface.mk labels.internalSelector #slice.nil) ∗
  "#Hnothing" ∷ (global_addr labels.sharedNothingSelector) ↦□
    interface.ok (interface.mk labels.nothingSelector #(labels.nothingSelector.mk)).

#[global] Instance : IsPkgInit (iProp Σ) labels :=
  define_is_pkg_init is_initialized.
#[global] Instance : GetIsPkgInitWf (iProp Σ) labels := build_get_is_pkg_init_wf.

End proof.
