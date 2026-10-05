From New.proof Require Import prelude empty_ffi.
From New.proof.k8s_io.component_base Require Export featuregate_init.
From New.proof.k8s_io.apiserver.pkg.util Require Export feature_init.

Module featuregate := code.k8s_io.component_base.featuregate.featuregate.
Module utilfeature := code.k8s_io.apiserver.pkg.util.feature.feature.

Section proof.
Context `{hG: !heapGS Σ} `{!ffi_semantics _ _}.
Context {sem : go.Semantics} {package_sem : utilfeature.Assumptions}.
Collection W := sem + package_sem.
Local Set Default Proof Using "All".

(* Trusted: the global feature gate is an interface value from an untranslated
   package. Querying it only returns some boolean. *)
Lemma wp_DefaultFeatureGate_Enabled (f : val) :
  {{{ is_pkg_init code.k8s_io.apiserver.pkg.util.feature.pkg_id.feature }}}
    (MethodResolve featuregate.FeatureGate "Enabled"%go
      (![featuregate.FeatureGate] #(global_addr utilfeature.DefaultFeatureGate)) f)%E
  {{{ (b : bool), RET #b; True }}}.
Proof. Admitted.

End proof.
