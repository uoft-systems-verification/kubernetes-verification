(* Adapted from Perennial for the complete time representation. *)
From New.proof Require Import proof_prelude.
From New.generatedproof Require Export time.
From New.golang.theory.chan.au_spec
  Require Import chan_au_base.
From New.golang.theory.chan.idioms Require Import bag.

Section wps.
Context `{hG: heapGS Σ, !ffi_semantics _ _}.
Context {sem : go.Semantics} {package_sem : time.Assumptions}.

#[global] Instance : IsPkgInit (iProp Σ) time := define_is_pkg_init True%I.
#[global] Instance : GetIsPkgInitWf (iProp Σ) time := build_get_is_pkg_init_wf.

Lemma wp_initialize' get_is_pkg_init :
  get_is_pkg_init_prop time get_is_pkg_init →
  {{{ own_initializing get_is_pkg_init }}}
    time.initialize' #()
  {{{ RET #(); own_initializing get_is_pkg_init ∗ is_pkg_init time }}}.
Proof.
  intros Hinit. wp_start as "Hown".
  wp_apply (wp_package_init with "[$Hown] HΦ").
  { destruct Hinit as (-> & ?); done. }
  iIntros "Hown". wp_auto.
Admitted.

Collection W := sem + package_sem.
Set Default Proof Using "W".

#[local]
Lemma wp_Time__sec (t : loc) (tv : time.Time.t) :
  {{{ t ↦ tv }}}
    t @! (go.PointerType time.Time) @! "sec" #()
  {{{ (x : w64), RET #x; t ↦ tv }}}.
Proof.
  wp_start. wp_auto. wp_if_destruct; by iApply "HΦ".
Qed.

#[local]
Lemma wp_Time__unixSec (t : loc) (tv : time.Time.t) :
  {{{ t ↦ tv }}}
    t @! (go.PointerType time.Time) @! "unixSec" #()
  {{{ (x : w64), RET #x; t ↦ tv }}}.
Proof.
  wp_start. wp_auto. wp_apply (wp_Time__sec with "[$]") as "% ?". by iApply "HΦ".
Qed.

#[local]
Lemma wp_Time__nsec (t : loc) (tv : time.Time.t) :
  {{{ t ↦ tv }}}
    t @! (go.PointerType time.Time) @! "nsec" #()
  {{{ (x : w32), RET #x; True }}}.
Proof.
  wp_start. wp_auto. by iApply "HΦ".
Qed.

Lemma wp_Time__UnixNano' (t : time.Time.t) :
  {{{ True }}}
    t @! time.Time @! "UnixNano" #()
  {{{ (x : w64), RET #x; True }}}.
Proof.
  wp_start. wp_auto. wp_apply (wp_Time__unixSec with "[$]") as "% ?".
  wp_apply (wp_Time__nsec with "[$]") as "% ?". by iApply "HΦ".
Qed.

Lemma wp_Time__UnixNano l (t : time.Time.t) :
  {{{ l ↦ t }}}
    l @! (go.PointerType time.Time) @! "UnixNano" #()
  {{{ (x : w64), RET #x; l ↦ t }}}.
Proof.
  wp_start. wp_auto. wp_apply wp_Time__UnixNano' as "% _".  wp_end.
Qed.

Axiom wp_Now :
  {{{ True }}}
    @! time.Now #()
  {{{ (t : time.Time.t), RET #t; True }}}.

Axiom wp_Until : ∀ (deadline : time.Time.t) ,
  {{{ True }}}
    @! time.Until #deadline
  {{{ (x : w64), RET #x; True }}}.

Axiom wp_Time__Add : ∀ (t : time.Time.t) (d : time.Duration.t),
  {{{ True }}}
    t @! time.Time @! "Add" #d
  {{{ (result : time.Time.t), RET #result;
      ⌜result.(time.Time.loc') = t.(time.Time.loc')⌝
  }}}.

Lemma wp_arbitraryTime :
  {{{ True }}}
    time.arbitraryTime #()
  {{{ (t: time.Time.t), RET #t; True }}}.
Proof.
  wp_start. wp_apply wp_ArbitraryInt as "%x _".
  change (go.Named "time.Time"%go []) with time.Time.
  wp_auto. by iApply "HΦ".
Qed.

Lemma wp_After (d : time.Duration.t) :
  {{{ True }}}
    @! time.After #d
  {{{ (ch: loc) γ, RET #ch; is_chan_bag γ ch (λ (t: time.Time.t), True)%I }}}.
Proof.
  wp_start. change (go.Named "time.Time"%go []) with time.Time.
  wp_apply chan.wp_make2; first word.
  iIntros (ch γ) "(His & Hcap & Hown)".
  simpl.
  iMod (start_bag (λ t, True)%I with "[$His] [$Hown]") as "#Hch".
  { done. }
  wp_auto.
  wp_apply wp_fork.
  {
    wp_apply wp_arbitraryTime.
    iIntros (t) "_".
    wp_apply (wp_bag_send with "[$Hch]"). done.
  }
  iApply "HΦ".
  iFrame "#".
Qed.

Lemma wp_Sleep (d : time.Duration.t) :
  {{{ True }}}
    @! time.Sleep #d
  {{{ RET #(); True }}}.
Proof. wp_start. by iApply "HΦ". Qed.

End wps.

From New.generatedviews Require Import runtime_time.
From New.proof Require Import empty_ffi.

Section complete_time.
Context `{hG : !heapGS Σ} `{!ffi_semantics _ _}.
Context {sem : go.Semantics} {package_sem : time.Assumptions}.
Local Set Default Proof Using "All".

(* The timestamp view projects the numeric fields and omits the shared timezone
   pointer. Constructing the view needs no heap ownership. *)
Lemma wp_Now_full :
  {{{ True }}}
    @! time.Now #()
  {{{ (t : time.Time.t) (view : TimeView.TimeV.t), RET #t;
      TimeView.TimeV.deepown t view 1
  }}}.
Proof.
  wp_start. wp_apply wp_Now as "%t _".
  iApply ("HΦ" $! t (TimeView.TimeV.of_go t)).
  rewrite /TimeView.TimeV.deepown. done.
Qed.
End complete_time.
