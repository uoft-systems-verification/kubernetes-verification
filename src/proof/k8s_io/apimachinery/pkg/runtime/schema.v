From New.proof.k8s_io.apimachinery.pkg.runtime Require Export schema_init.
From New.proof Require Import prelude empty_ffi.
From New.proof.github_com.mit_pdos.perennial.goose.model Require Import strings.

Section proof.
Context `{hG: !heapGS Σ} `{!ffi_semantics _ _}.
Context {sem : go.Semantics} {package_sem : schema.Assumptions}.
Collection W := sem + package_sem.
Set Default Proof Using "W".

Lemma wp_GroupVersionKind__GroupVersion (gvk : schema.GroupVersionKind.t) :
  {{{ is_pkg_init schema }}}
    gvk @! schema.GroupVersionKind @! "GroupVersion" #()
  {{{ RET #{|
      schema.GroupVersion.Group' := gvk.(schema.GroupVersionKind.Group');
      schema.GroupVersion.Version' := gvk.(schema.GroupVersionKind.Version')
    |}; True
  }}}.
Proof. wp_start. wp_auto. wp_end. Qed.

Lemma wp_GroupVersion__String_apps_v1 (gv : schema.GroupVersion.t) :
  {{{ is_pkg_init schema ∗
      ⌜ gv.(schema.GroupVersion.Group') = "apps"%go ∧
        gv.(schema.GroupVersion.Version') = "v1"%go ⌝
  }}}
    gv @! schema.GroupVersion @! "String" #()
  {{{ RET #"apps/v1"%go; True }}}.
Proof.
  wp_start as "H". iDestruct "H" as %Hgv.
  destruct Hgv as [Hgroup Hversion].
  wp_auto. rewrite Hgroup.
  wp_apply wp_string_len as "%Hoverflow".
  rewrite Hgroup Hversion. iApply "HΦ". done.
Qed.

Lemma wp_GroupVersion__WithKind (gv: schema.GroupVersion.t) kind:
  {{{ is_pkg_init schema }}}
    gv @! schema.GroupVersion @! "WithKind" #kind
  {{{ gvk, RET #gvk;
      ⌜ gvk.(schema.GroupVersionKind.Group') = gv.(schema.GroupVersion.Group') ∧
        gvk.(schema.GroupVersionKind.Version') = gv.(schema.GroupVersion.Version') ∧
        gvk.(schema.GroupVersionKind.Kind') = kind ⌝
  }}}.
Proof. wp_start. wp_auto. wp_end. Qed.

End proof.
