From verification Require Export prelude.
From New.proof Require Export std.
From New.proof Require Export context fmt.
Require Export New.generatedproof.k8s_io.kubernetes.pkg.controller.replicaset.
From Perennial Require Import base.

Section proof.
Context `{hG: heapGS Σ} `{!ffi_semantics _ _}.
Context `{!globalsGS Σ} {go_ctx: GoContext}.


#[global] Instance : IsPkgInit code.github_com.go_logr.logr.logr := define_is_pkg_init True%I.
#[global] Instance : GetIsPkgInitWf code.github_com.go_logr.logr.logr := build_get_is_pkg_init_wf.
#[global] Instance : IsPkgInit code.k8s_io.component_base.metrics.metrics := define_is_pkg_init True%I.
#[global] Instance : GetIsPkgInitWf code.k8s_io.component_base.metrics.metrics := build_get_is_pkg_init_wf.
#[global] Instance : IsPkgInit code.k8s_io.component_base.featuregate.featuregate := define_is_pkg_init True%I.
#[global] Instance : GetIsPkgInitWf code.k8s_io.component_base.featuregate.featuregate := build_get_is_pkg_init_wf.

#[global] Instance : IsPkgInit code.fmt.fmt := define_is_pkg_init True%I.
#[global] Instance : GetIsPkgInitWf code.fmt.fmt := build_get_is_pkg_init_wf.

#[global] Instance : IsPkgInit code.sort.sort := define_is_pkg_init True%I.
#[global] Instance : GetIsPkgInitWf code.sort.sort := build_get_is_pkg_init_wf.

#[global] Instance : IsPkgInit code.time.time := define_is_pkg_init True%I.
#[global] Instance : GetIsPkgInitWf code.time.time := build_get_is_pkg_init_wf.

#[global] Instance : IsPkgInit code.k8s_io.api.apps.v1.v1 := define_is_pkg_init True%I.
#[global] Instance : GetIsPkgInitWf code.k8s_io.api.apps.v1.v1 := build_get_is_pkg_init_wf.

#[global] Instance : IsPkgInit code.k8s_io.apimachinery.pkg.types.types := define_is_pkg_init True%I.
#[global] Instance : GetIsPkgInitWf code.k8s_io.apimachinery.pkg.types.types := build_get_is_pkg_init_wf.

#[global] Instance : IsPkgInit code.k8s_io.apimachinery.pkg.apis.meta.v1.v1 := define_is_pkg_init True%I.
#[global] Instance : GetIsPkgInitWf code.k8s_io.apimachinery.pkg.apis.meta.v1.v1 := build_get_is_pkg_init_wf.

#[global] Instance : IsPkgInit code.k8s_io.api.core.v1.v1 := define_is_pkg_init True%I.
#[global] Instance : GetIsPkgInitWf code.k8s_io.api.core.v1.v1 := build_get_is_pkg_init_wf.

#[global] Instance : IsPkgInit code.k8s_io.apimachinery.pkg.api.errors.errors := define_is_pkg_init True%I.
#[global] Instance : GetIsPkgInitWf code.k8s_io.apimachinery.pkg.api.errors.errors := build_get_is_pkg_init_wf.

#[global] Instance : IsPkgInit code.k8s_io.apimachinery.pkg.labels.labels := define_is_pkg_init True%I.
#[global] Instance : GetIsPkgInitWf code.k8s_io.apimachinery.pkg.labels.labels := build_get_is_pkg_init_wf.

#[global] Instance : IsPkgInit code.k8s_io.apimachinery.pkg.runtime.schema.schema := define_is_pkg_init True%I.
#[global] Instance : GetIsPkgInitWf code.k8s_io.apimachinery.pkg.runtime.schema.schema := build_get_is_pkg_init_wf.

#[global] Instance : IsPkgInit code.k8s_io.apimachinery.pkg.util.runtime.runtime := define_is_pkg_init True%I.
#[global] Instance : GetIsPkgInitWf code.k8s_io.apimachinery.pkg.util.runtime.runtime := build_get_is_pkg_init_wf.

#[global] Instance : IsPkgInit code.k8s_io.apiserver.pkg.util.feature.feature := define_is_pkg_init True%I.
#[global] Instance : GetIsPkgInitWf code.k8s_io.apiserver.pkg.util.feature.feature := build_get_is_pkg_init_wf.

#[global] Instance : IsPkgInit code.k8s_io.client_go.kubernetes.kubernetes := define_is_pkg_init True%I.
#[global] Instance : GetIsPkgInitWf code.k8s_io.client_go.kubernetes.kubernetes := build_get_is_pkg_init_wf.

#[global] Instance : IsPkgInit code.k8s_io.client_go.listers.apps.v1.v1 := define_is_pkg_init True%I.
#[global] Instance : GetIsPkgInitWf code.k8s_io.client_go.listers.apps.v1.v1 := build_get_is_pkg_init_wf.

#[global] Instance : IsPkgInit code.k8s_io.client_go.listers.core.v1.v1 := define_is_pkg_init True%I.
#[global] Instance : GetIsPkgInitWf code.k8s_io.client_go.listers.core.v1.v1 := build_get_is_pkg_init_wf.

#[global] Instance : IsPkgInit code.k8s_io.client_go.tools.cache.cache := define_is_pkg_init True%I.
#[global] Instance : GetIsPkgInitWf code.k8s_io.client_go.tools.cache.cache := build_get_is_pkg_init_wf.

#[global] Instance : IsPkgInit code.k8s_io.client_go.util.workqueue.workqueue := define_is_pkg_init True%I.
#[global] Instance : GetIsPkgInitWf code.k8s_io.client_go.util.workqueue.workqueue := build_get_is_pkg_init_wf.

#[global] Instance : IsPkgInit code.k8s_io.klog.v2.klog := define_is_pkg_init True%I.
#[global] Instance : GetIsPkgInitWf code.k8s_io.klog.v2.klog := build_get_is_pkg_init_wf.

#[global] Instance : IsPkgInit code.k8s_io.kubernetes.pkg.api.v1.pod.pod := define_is_pkg_init True%I.
#[global] Instance : GetIsPkgInitWf code.k8s_io.kubernetes.pkg.api.v1.pod.pod := build_get_is_pkg_init_wf.

#[global] Instance : IsPkgInit code.k8s_io.kubernetes.pkg.controller.controller := define_is_pkg_init True%I.
#[global] Instance : GetIsPkgInitWf code.k8s_io.kubernetes.pkg.controller.controller := build_get_is_pkg_init_wf.

#[global] Instance : IsPkgInit code.k8s_io.kubernetes.pkg.controller.replicaset.metrics.metrics := define_is_pkg_init True%I.
#[global] Instance : GetIsPkgInitWf code.k8s_io.kubernetes.pkg.controller.replicaset.metrics.metrics := build_get_is_pkg_init_wf.

#[global] Instance : IsPkgInit code.k8s_io.kubernetes.pkg.features.features := define_is_pkg_init True%I.
#[global] Instance : GetIsPkgInitWf code.k8s_io.kubernetes.pkg.features.features := build_get_is_pkg_init_wf.

#[global] Instance : IsPkgInit code.k8s_io.utils.clock.clock := define_is_pkg_init True%I.
#[global] Instance : GetIsPkgInitWf code.k8s_io.utils.clock.clock := build_get_is_pkg_init_wf.

#[global] Instance : IsPkgInit code.k8s_io.utils.ptr.ptr := define_is_pkg_init True%I.
#[global] Instance : GetIsPkgInitWf code.k8s_io.utils.ptr.ptr := build_get_is_pkg_init_wf.

#[global] Instance : IsPkgInit code.k8s_io.client_go.kubernetes.typed.apps.v1.v1 := define_is_pkg_init True%I.
#[global] Instance : GetIsPkgInitWf code.k8s_io.client_go.kubernetes.typed.apps.v1.v1 := build_get_is_pkg_init_wf.

#[global] Instance : IsPkgInit replicaset := define_is_pkg_init True%I.
#[global] Instance : GetIsPkgInitWf replicaset := build_get_is_pkg_init_wf.

End proof.
