(* Bug 03: block_scope. Go code: bugs/03_block_scope_repro.go.
   Each comment below gives the result of running the Go program (checked
   by go test) and the result of the goose translation, which the lemma
   proves (gen/code/example_com/goosebugs/bugs.v). *)
From New.proof Require Import proof_prelude.
From New.generatedproof Require Import example_com.goosebugs.bugs.

Section proof.
Context `{hG: heapGS Σ, !ffi_semantics _ _}.
Context {sem : go.Semantics} {package_sem : bugs.Assumptions}.
Collection W := sem + package_sem.
Set Default Proof Using "W".

#[global] Instance : IsPkgInit (iProp Σ) bugs := define_is_pkg_init True%I.
#[global] Instance : GetIsPkgInitWf (iProp Σ) bugs := build_get_is_pkg_init_wf.

(* Running the Go program: BlockScope(x) returns x
     (go test: Test03BlockScope in bugs/03_block_scope_repro_test.go
      runs BlockScope(10) and gets 10).
   Translated code, proved below: BlockScope(x) returns 42 for every x,
     because the block's x := 42 is still in scope at return x. *)
Lemma wp_BlockScope (x: w64) :
  {{{ is_pkg_init bugs }}} @! bugs.BlockScope #x {{{ RET #(W64 42); True }}}.
Proof. wp_start. wp_auto. wp_end. Qed.

(* Running the Go program: BlockScopeVar(x) returns x
     (go test: Test03BlockScope in bugs/03_block_scope_repro_test.go
      runs BlockScopeVar(10) and gets 10).
   Translated code, proved below: BlockScopeVar(x) returns 42 for every x,
     because the block's var x = 42 is still in scope at return x. *)
Lemma wp_BlockScopeVar (x: w64) :
  {{{ is_pkg_init bugs }}} @! bugs.BlockScopeVar #x {{{ RET #(W64 42); True }}}.
Proof. wp_start. wp_auto. wp_end. Qed.

(* Running the Go program: BlockScopeNested(x) returns x
     (go test: Test03BlockScope in bugs/03_block_scope_repro_test.go
      runs BlockScopeNested(10) and gets 10).
   Translated code, proved below: BlockScopeNested(x) returns 30 for every x,
     because the innermost block's x := 30 is still in scope. *)
Lemma wp_BlockScopeNested (x: w64) :
  {{{ is_pkg_init bugs }}} @! bugs.BlockScopeNested #x {{{ RET #(W64 30); True }}}.
Proof. wp_start. wp_auto. wp_end. Qed.

End proof.
