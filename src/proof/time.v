(* Adapted from Perennial for the complete time representation. *)
From New.proof Require Import proof_prelude.
From New.generatedproof Require Export time.
From New.golang.theory.chan.au_spec
  Require Import chan_au_base.
From New.golang.theory.chan.idioms Require Import bag.
From New.generatedviews Require Import runtime_time.

(** Gallina versions of [time.Time]'s [sec], [nsec], [Before], and [Equal], over
    the numeric fields of the timestamp view. Like Go, two times are compared by
    their monotonic readings ([ext]) only when both carry one, and by wall-clock
    seconds and nanoseconds otherwise. *)
Definition time_has_monotonic_bit : w64 := W64 9223372036854775808.

Definition time_both_monotonic (t u : TimeView.TimeV.t) : Prop :=
  word.and (word.and t.(TimeView.TimeV.wall') u.(TimeView.TimeV.wall'))
    time_has_monotonic_bit ≠ W64 0.

Definition time_sec (t : TimeView.TimeV.t) : w64 :=
  if decide (word.and t.(TimeView.TimeV.wall') time_has_monotonic_bit ≠ W64 0) then
    word.add (W64 59453308800)
      (word.sru (word.slu t.(TimeView.TimeV.wall') (W64 1)) (W64 31))
  else t.(TimeView.TimeV.ext').

Definition time_nsec (t : TimeView.TimeV.t) : w32 :=
  W32 (uint.Z (word.and t.(TimeView.TimeV.wall') (W64 1073741823))).

Definition time_before (t u : TimeView.TimeV.t) : Prop :=
  if decide (time_both_monotonic t u) then
    sint.Z t.(TimeView.TimeV.ext') < sint.Z u.(TimeView.TimeV.ext')
  else
    sint.Z (time_sec t) < sint.Z (time_sec u) ∨
    (time_sec t = time_sec u ∧ sint.Z (time_nsec t) < sint.Z (time_nsec u)).

Definition time_equal (t u : TimeView.TimeV.t) : Prop :=
  if decide (time_both_monotonic t u) then
    t.(TimeView.TimeV.ext') = u.(TimeView.TimeV.ext')
  else time_sec t = time_sec u ∧ time_nsec t = time_nsec u.

#[global] Instance time_before_dec t u : Decision (time_before t u).
Proof. rewrite /time_before. case_decide; apply _. Defined.

#[global] Instance time_equal_dec t u : Decision (time_equal t u).
Proof. rewrite /time_equal. case_decide; apply _. Defined.

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
Lemma wp_Time__sec (t : loc) (tv : time.Time.t) dq :
  {{{ t ↦{dq} tv }}}
    t @! (go.PointerType time.Time) @! "sec" #()
  {{{ RET #(time_sec (TimeView.TimeV.of_go tv)); t ↦{dq} tv }}}.
Proof.
  wp_start. wp_auto. rewrite /time_sec /time_has_monotonic_bit /=.
  wp_if_destruct; case_decide; try contradiction; by iApply "HΦ".
Qed.

#[local]
Lemma wp_Time__unixSec (t : loc) (tv : time.Time.t) :
  {{{ t ↦ tv }}}
    t @! (go.PointerType time.Time) @! "unixSec" #()
  {{{ (x : w64), RET #x; t ↦ tv }}}.
Proof.
  wp_start. wp_auto. wp_apply (wp_Time__sec with "[$]") as "?". by iApply "HΦ".
Qed.

#[local]
Lemma wp_Time__nsec (t : loc) (tv : time.Time.t) dq :
  {{{ t ↦{dq} tv }}}
    t @! (go.PointerType time.Time) @! "nsec" #()
  {{{ RET #(time_nsec (TimeView.TimeV.of_go tv)); t ↦{dq} tv }}}.
Proof.
  wp_start. wp_auto. by iApply "HΦ".
Qed.

Lemma wp_Time__UnixNano' (t : time.Time.t) :
  {{{ True }}}
    t @! time.Time @! "UnixNano" #()
  {{{ (x : w64), RET #x; True }}}.
Proof.
  wp_start. wp_auto. wp_apply (wp_Time__unixSec with "[$]") as "% ?".
  wp_apply (wp_Time__nsec with "[$]") as "?". by iApply "HΦ".
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

Lemma wp_Time__Before (t u : time.Time.t) :
  {{{ True }}}
    t @! time.Time @! "Before" #u
  {{{ RET #(bool_decide (time_before (TimeView.TimeV.of_go t) (TimeView.TimeV.of_go u))); True }}}.
Proof.
  wp_start. wp_auto. iSpecialize ("HΦ" with "[//]").
  wp_if_destruct.
  - wp_apply (wp_Time__sec with "[$t]") as "t".
    wp_apply (wp_Time__sec with "[$u]") as "u".
    assert (time_before (TimeView.TimeV.of_go t) (TimeView.TimeV.of_go u) ↔
      sint.Z (time_sec (TimeView.TimeV.of_go t)) < sint.Z (time_sec (TimeView.TimeV.of_go u)) ∨
      (time_sec (TimeView.TimeV.of_go t) = time_sec (TimeView.TimeV.of_go u) ∧
       sint.Z (time_nsec (TimeView.TimeV.of_go t)) < sint.Z (time_nsec (TimeView.TimeV.of_go u))))
      as Hbefore.
    { rewrite /time_before /time_both_monotonic /time_has_monotonic_bit decide_False //.
      intros Hne. apply Hne. exact e. }
    wp_if_destruct.
    + iExactEq "HΦ". do 2 f_equal. apply bool_decide_eq_true_2.
      apply Hbefore. left. done.
    + wp_if_destruct.
      * wp_apply (wp_Time__nsec with "[$t]") as "t".
        wp_apply (wp_Time__nsec with "[$u]") as "u".
        iExactEq "HΦ". do 2 f_equal. apply bool_decide_ext.
        rewrite Hbefore. split; [intros [?|[_ ?]]; [lia|done]|intros; right; done].
      * iExactEq "HΦ". do 2 f_equal. apply bool_decide_eq_false_2.
        rewrite Hbefore. intros [?|[? _]]; [lia|contradiction].
  - iExactEq "HΦ". do 2 f_equal. apply bool_decide_ext.
    rewrite /time_before /time_both_monotonic /time_has_monotonic_bit decide_True //.
Qed.

Lemma wp_Time__Equal (t u : time.Time.t) :
  {{{ True }}}
    t @! time.Time @! "Equal" #u
  {{{ RET #(bool_decide (time_equal (TimeView.TimeV.of_go t) (TimeView.TimeV.of_go u))); True }}}.
Proof.
  wp_start. wp_auto. iSpecialize ("HΦ" with "[//]").
  wp_if_destruct.
  - assert (time_equal (TimeView.TimeV.of_go t) (TimeView.TimeV.of_go u) ↔
      time_sec (TimeView.TimeV.of_go t) = time_sec (TimeView.TimeV.of_go u) ∧
      time_nsec (TimeView.TimeV.of_go t) = time_nsec (TimeView.TimeV.of_go u)) as Hequal.
    { rewrite /time_equal /time_both_monotonic /time_has_monotonic_bit decide_False //.
      intros Hne. apply Hne. exact e. }
    wp_apply (wp_Time__sec with "[$t]") as "t".
    wp_apply (wp_Time__sec with "[$u]") as "u".
    wp_if_destruct.
    + wp_apply (wp_Time__nsec with "[$t]") as "t".
      wp_apply (wp_Time__nsec with "[$u]") as "u".
      iExactEq "HΦ". do 2 f_equal. apply bool_decide_ext.
      rewrite Hequal. split; [intros [_ ?]; done|intros; split; done].
    + iExactEq "HΦ". do 2 f_equal. apply bool_decide_eq_false_2.
      rewrite Hequal. intros [? _]. contradiction.
  - iExactEq "HΦ". do 2 f_equal. apply bool_decide_ext.
    rewrite /time_equal /time_both_monotonic /time_has_monotonic_bit decide_True //.
Qed.

End wps.

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
