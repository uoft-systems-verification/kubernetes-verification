From New.proof Require Import prelude empty_ffi.
From New.proof.k8s_io.utils Require Export clock_init.

Section proof.
Context `{hG: !heapGS Σ} `{!ffi_semantics _ _}.
Context {sem : go.Semantics} {package_sem : clock.Assumptions}.
Collection W := sem + package_sem.
Local Set Default Proof Using "All".

(* The [RealClock{}] value passed as a [clock.PassiveClock]. *)
Definition real_clock : interface.t :=
  interface.mk_ok code.k8s_io.utils.clock.clock.RealClock #(code.k8s_io.utils.clock.clock.RealClock.mk).

(* [RealClock.Now] returns some time and leaves the caller's resources
   unchanged. It calls the untranslated [time.Now], so the proof relies on
   Perennial's axiom [wp_Now] (New.proof.time) for it. *)
Lemma wp_RealClock__Now :
  {{{ True }}}
    (MethodResolve code.k8s_io.utils.clock.clock.PassiveClock "Now" #real_clock) #()
  {{{ (now : time.Time.t), RET #now; True }}}.
Proof.
  iIntros (Φ) "_ HΦ". rewrite /real_clock.
  wp_pures. wp_method_call. rewrite /clock.RealClock__Nowⁱᵐᵖˡ. wp_pures.
  wp_apply wp_Now. iIntros (t) "_". wp_pures.
  iApply "HΦ". done.
Qed.

End proof.
