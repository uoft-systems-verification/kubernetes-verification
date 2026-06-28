From New.proof Require Import prelude empty_ffi.
From Stdlib Require Import Numbers.DecimalFacts Numbers.DecimalNat Numbers.DecimalString.

Section proof.

Local Open Scope nat_scope.

Definition byte_zero : w8 := W8 48.  (* ASCII '0' *)
Definition byte_one : w8 := W8 49.  (* ASCII '1' *)
Definition byte_two : w8 := W8 50.  (* ASCII '2' *)
Definition byte_three : w8 := W8 51.  (* ASCII '3' *)
Definition byte_four : w8 := W8 52.  (* ASCII '4' *)
Definition byte_five : w8 := W8 53.  (* ASCII '5' *)
Definition byte_six : w8 := W8 54.  (* ASCII '6' *)
Definition byte_seven : w8 := W8 55.  (* ASCII '7' *)
Definition byte_eight : w8 := W8 56.  (* ASCII '8' *)
Definition byte_nine : w8 := W8 57.  (* ASCII '9' *)

Definition decimal_digit_byte (digit : nat) : w8 :=
  match digit with
  | 0 => byte_zero
  | 1 => byte_one
  | 2 => byte_two
  | 3 => byte_three
  | 4 => byte_four
  | 5 => byte_five
  | 6 => byte_six
  | 7 => byte_seven
  | 8 => byte_eight
  (* Out-of-domain digits are unreachable in the lemmas that use this as a
     decimal digit; those lemmas require or derive [digit < 10]. *)
  | _ => byte_nine
  end.

Definition byte_decimal_digit (b : w8) : option nat :=
  if decide (b = byte_zero) then Some 0
  else if decide (b = byte_one) then Some 1
  else if decide (b = byte_two) then Some 2
  else if decide (b = byte_three) then Some 3
  else if decide (b = byte_four) then Some 4
  else if decide (b = byte_five) then Some 5
  else if decide (b = byte_six) then Some 6
  else if decide (b = byte_seven) then Some 7
  else if decide (b = byte_eight) then Some 8
  else if decide (b = byte_nine) then Some 9
  else None.

Definition decimal_uint_cons_digit (digit : nat) (rest : Decimal.uint) : Decimal.uint :=
  match digit with
  | 0 => Decimal.D0 rest
  | 1 => Decimal.D1 rest
  | 2 => Decimal.D2 rest
  | 3 => Decimal.D3 rest
  | 4 => Decimal.D4 rest
  | 5 => Decimal.D5 rest
  | 6 => Decimal.D6 rest
  | 7 => Decimal.D7 rest
  | 8 => Decimal.D8 rest
  (* Out-of-domain digits are unreachable in the lemmas that use this as a
     decimal digit; those lemmas require or derive [digit < 10]. *)
  | _ => Decimal.D9 rest
  end.

Fixpoint go_string_of_decimal_uint (d : Decimal.uint) : go_string :=
  match d with
  | Decimal.Nil => []
  | Decimal.D0 d => byte_zero :: go_string_of_decimal_uint d
  | Decimal.D1 d => byte_one :: go_string_of_decimal_uint d
  | Decimal.D2 d => byte_two :: go_string_of_decimal_uint d
  | Decimal.D3 d => byte_three :: go_string_of_decimal_uint d
  | Decimal.D4 d => byte_four :: go_string_of_decimal_uint d
  | Decimal.D5 d => byte_five :: go_string_of_decimal_uint d
  | Decimal.D6 d => byte_six :: go_string_of_decimal_uint d
  | Decimal.D7 d => byte_seven :: go_string_of_decimal_uint d
  | Decimal.D8 d => byte_eight :: go_string_of_decimal_uint d
  | Decimal.D9 d => byte_nine :: go_string_of_decimal_uint d
  end.

Definition decimal_string (n : nat) : go_string :=
  go_string_of_decimal_uint (Nat.to_uint n).

Fixpoint decimal_uint_of_go_string (s : go_string) : option Decimal.uint :=
  match s with
  | [] => Some Decimal.Nil
  | b :: s =>
      rest ← decimal_uint_of_go_string s;
      digit ← byte_decimal_digit b;
      Some (decimal_uint_cons_digit digit rest)
  end.

Definition parse_decimal_string (s : go_string) : option nat :=
  match s with
  | [] => None
  | _ =>
      d ← decimal_uint_of_go_string s;
      Some (Nat.of_uint d)
  end.

Definition parse_canonical_decimal_string (s : go_string) : option nat :=
  match parse_decimal_string s with
  | Some n => if decide (decimal_string n = s) then Some n else None
  | None => None
  end.

Ltac solve_decimal_byte :=
  unfold byte_decimal_digit, decimal_digit_byte, byte_zero, byte_one,
    byte_two, byte_three, byte_four, byte_five, byte_six, byte_seven,
    byte_eight, byte_nine;
  repeat (case_decide; simplify_eq/=; try done).

Lemma byte_decimal_digit_decimal_digit_byte digit :
  digit < 10 →
  byte_decimal_digit (decimal_digit_byte digit) = Some digit.
Proof.
  intros Hlt.
  destruct digit as [|[|[|[|[|[|[|[|[|[|digit]]]]]]]]]]; try lia;
    solve_decimal_byte.
Qed.

Lemma byte_decimal_digit_bound b digit :
  byte_decimal_digit b = Some digit →
  digit < 10.
Proof.
  unfold byte_decimal_digit.
  repeat case_decide; intros Hparse; simplify_eq/=; lia.
Qed.

Lemma decimal_digit_byte_byte_decimal_digit b digit :
  byte_decimal_digit b = Some digit →
  decimal_digit_byte digit = b.
Proof.
  unfold byte_decimal_digit.
  repeat case_decide; intros Hparse; simplify_eq/=; done.
Qed.

Lemma decimal_uint_cons_digit_go_string digit d :
  digit < 10 →
  go_string_of_decimal_uint (decimal_uint_cons_digit digit d) =
    decimal_digit_byte digit :: go_string_of_decimal_uint d.
Proof.
  intros Hlt.
  destruct digit as [|[|[|[|[|[|[|[|[|[|digit]]]]]]]]]]; try lia; done.
Qed.

Lemma decimal_uint_of_go_string_go_string_of_decimal_uint d :
  decimal_uint_of_go_string (go_string_of_decimal_uint d) = Some d.
Proof.
  induction d; simpl; try rewrite IHd;
    try (rewrite byte_decimal_digit_decimal_digit_byte; [|lia]); done.
Qed.

Lemma go_string_of_decimal_uint_decimal_uint_of_go_string s d :
  decimal_uint_of_go_string s = Some d →
  go_string_of_decimal_uint d = s.
Proof.
  revert d.
  induction s as [|b s IH]; intros d Hparse; simpl in Hparse.
  - by simplify_eq/=.
  - destruct (decimal_uint_of_go_string s) as [rest|] eqn:Hrest; [|done].
    destruct (byte_decimal_digit b) as [digit|] eqn:Hdigit; [|done].
    simplify_eq/=.
    assert (Hdigit_bound : digit < 10) by
      (eapply byte_decimal_digit_bound; exact Hdigit).
    rewrite (decimal_uint_cons_digit_go_string digit rest Hdigit_bound).
    rewrite (decimal_digit_byte_byte_decimal_digit _ _ Hdigit).
    by rewrite (IH _ eq_refl).
Qed.

Lemma decimal_uint_of_go_string_decimal_digit_byte digit d :
  digit < 10 →
  decimal_uint_of_go_string (decimal_digit_byte digit :: go_string_of_decimal_uint d) =
    Some (decimal_uint_cons_digit digit d).
Proof.
  intros Hlt. simpl.
  rewrite decimal_uint_of_go_string_go_string_of_decimal_uint.
  by rewrite byte_decimal_digit_decimal_digit_byte.
Qed.

Lemma go_string_of_decimal_uint_nil_inv d :
  go_string_of_decimal_uint d = [] →
  d = Decimal.Nil.
Proof.
  destruct d; done.
Qed.

Lemma decimal_digit_byte_nonzero digit :
  0 < digit →
  digit < 10 →
  decimal_digit_byte digit ≠ byte_zero.
Proof.
  intros Hgt Hlt.
  destruct digit as [|[|[|[|[|[|[|[|[|[|digit]]]]]]]]]]; try lia;
    unfold decimal_digit_byte, byte_zero, byte_one, byte_two, byte_three,
      byte_four, byte_five, byte_six, byte_seven, byte_eight, byte_nine;
    intros Heq; apply (f_equal uint.Z) in Heq; vm_compute in Heq; lia.
Qed.

Lemma parse_decimal_string_decimal_digit_byte_nonzero digit d :
  0 < digit →
  digit < 10 →
  parse_decimal_string (decimal_digit_byte digit :: go_string_of_decimal_uint d) =
    Some (Nat.of_uint (decimal_uint_cons_digit digit d)).
Proof.
  intros _ Hlt.
  unfold parse_decimal_string.
  destruct (go_string_of_decimal_uint d) as [|b s] eqn:Htail.
  - apply go_string_of_decimal_uint_nil_inv in Htail as ->.
    simpl.
    pose proof (byte_decimal_digit_decimal_digit_byte digit Hlt) as Hdigit.
    by rewrite Hdigit.
  - simpl.
    pose proof (decimal_uint_of_go_string_decimal_digit_byte digit d Hlt) as Hparse.
    rewrite Htail in Hparse. simpl in Hparse.
    by rewrite Hparse.
Qed.

Lemma decimal_uint_of_go_string_nonzero_unorm b s d :
  b ≠ byte_zero →
  decimal_uint_of_go_string (b :: s) = Some d →
  Decimal.unorm d = d.
Proof.
  intros Hnot_zero Hparse.
  simpl in Hparse.
  destruct (decimal_uint_of_go_string s) as [rest|] eqn:Hrest; [|done].
  destruct (byte_decimal_digit b) as [digit|] eqn:Hdigit; [|done].
  simplify_eq/=.
  pose proof (byte_decimal_digit_bound _ _ Hdigit) as Hdigit_bound.
  pose proof (decimal_digit_byte_byte_decimal_digit _ _ Hdigit) as Hbyte.
  destruct digit as [|[|[|[|[|[|[|[|[|[|digit]]]]]]]]]]; try lia; simpl; [|done..].
  exfalso. apply Hnot_zero. symmetry. exact Hbyte.
Qed.

Ltac rewrite_parse_decimal_string_nonzero :=
  match goal with
  | |- context [parse_decimal_string (decimal_digit_byte ?digit :: go_string_of_decimal_uint ?d)] =>
      let Hparse := fresh "Hparse" in
      assert (Hparse :
        parse_decimal_string (decimal_digit_byte digit :: go_string_of_decimal_uint d) =
        Some (Nat.of_uint (decimal_uint_cons_digit digit d))) by
        (apply parse_decimal_string_decimal_digit_byte_nonzero; lia);
      rewrite Hparse
  end.

Lemma decimal_D0_eq_unorm_nil d :
  Decimal.D0 d = Decimal.unorm d →
  d = Decimal.Nil.
Proof.
  intros Heq.
  destruct (Decimal.uint_eq_dec d Decimal.Nil) as [|Hnon_nil]; [done|].
  apply (f_equal Decimal.nb_digits) in Heq.
  simpl in Heq.
  pose proof (DecimalFacts.nb_digits_unorm d Hnon_nil).
  lia.
Qed.

Lemma nat_to_uint_not_nil n :
  Nat.to_uint n ≠ Decimal.Nil.
Proof.
  intros Hnil.
  pose proof (DecimalNat.Unsigned.of_to n) as Hof_to.
  rewrite Hnil in Hof_to.
  simpl in Hof_to.
  subst n.
  simpl in Hnil. done.
Qed.

Lemma nat_to_uint_D0_inv n d :
  Nat.to_uint n = Decimal.D0 d →
  d = Decimal.Nil.
Proof.
  intros Huint.
  pose proof (DecimalNat.Unsigned.of_to n) as Hof_to.
  rewrite Huint in Hof_to.
  simpl in Hof_to.
  pose proof (DecimalNat.Unsigned.to_of (Decimal.D0 d)) as Hto_of.
  simpl in Hto_of.
  rewrite Hof_to in Hto_of.
  rewrite Huint in Hto_of.
  by apply decimal_D0_eq_unorm_nil.
Qed.

Lemma parse_decimal_string_decimal_string n :
  parse_decimal_string (decimal_string n) = Some n.
Proof.
  unfold decimal_string.
  pose proof (DecimalNat.Unsigned.of_to n) as Hof_to.
  remember (Nat.to_uint n) as d eqn:Hd.
  destruct d as [|d|d|d|d|d|d|d|d|d|d].
  - exfalso. apply (nat_to_uint_not_nil n). by symmetry.
  - pose proof (eq_sym Hd) as Huint.
    apply nat_to_uint_D0_inv in Huint as ->.
    simpl. f_equal. symmetry. rewrite <-Hof_to. try rewrite <-Hd. done.
  - change (go_string_of_decimal_uint (Decimal.D1 d)) with
      (decimal_digit_byte 1 :: go_string_of_decimal_uint d).
    rewrite_parse_decimal_string_nonzero.
    by rewrite Hof_to.
  - change (go_string_of_decimal_uint (Decimal.D2 d)) with
      (decimal_digit_byte 2 :: go_string_of_decimal_uint d).
    rewrite_parse_decimal_string_nonzero.
    by rewrite Hof_to.
  - change (go_string_of_decimal_uint (Decimal.D3 d)) with
      (decimal_digit_byte 3 :: go_string_of_decimal_uint d).
    rewrite_parse_decimal_string_nonzero.
    by rewrite Hof_to.
  - change (go_string_of_decimal_uint (Decimal.D4 d)) with
      (decimal_digit_byte 4 :: go_string_of_decimal_uint d).
    rewrite_parse_decimal_string_nonzero.
    by rewrite Hof_to.
  - change (go_string_of_decimal_uint (Decimal.D5 d)) with
      (decimal_digit_byte 5 :: go_string_of_decimal_uint d).
    rewrite_parse_decimal_string_nonzero.
    by rewrite Hof_to.
  - change (go_string_of_decimal_uint (Decimal.D6 d)) with
      (decimal_digit_byte 6 :: go_string_of_decimal_uint d).
    rewrite_parse_decimal_string_nonzero.
    by rewrite Hof_to.
  - change (go_string_of_decimal_uint (Decimal.D7 d)) with
      (decimal_digit_byte 7 :: go_string_of_decimal_uint d).
    rewrite_parse_decimal_string_nonzero.
    by rewrite Hof_to.
  - change (go_string_of_decimal_uint (Decimal.D8 d)) with
      (decimal_digit_byte 8 :: go_string_of_decimal_uint d).
    rewrite_parse_decimal_string_nonzero.
    by rewrite Hof_to.
  - change (go_string_of_decimal_uint (Decimal.D9 d)) with
      (decimal_digit_byte 9 :: go_string_of_decimal_uint d).
    rewrite_parse_decimal_string_nonzero.
    by rewrite Hof_to.
Qed.

Lemma parse_canonical_decimal_string_sound s n :
  parse_canonical_decimal_string s = Some n →
  decimal_string n = s.
Proof.
  unfold parse_canonical_decimal_string.
  destruct (parse_decimal_string s) as [parsed|] eqn:Hparse; [|done].
  destruct (decide (decimal_string parsed = s)) as [Heq|]; [|done].
  intros Hn. simplify_eq/=. done.
Qed.

Lemma parse_canonical_decimal_string_decimal_string n :
  parse_canonical_decimal_string (decimal_string n) = Some n.
Proof.
  unfold parse_canonical_decimal_string.
  rewrite parse_decimal_string_decimal_string.
  destruct (decide (decimal_string n = decimal_string n)); [done|congruence].
Qed.

Lemma parse_canonical_decimal_string_complete s n :
  decimal_string n = s →
  parse_canonical_decimal_string s = Some n.
Proof.
  intros <-.
  apply parse_canonical_decimal_string_decimal_string.
Qed.

Lemma decimal_string_inj n1 n2 :
  decimal_string n1 = decimal_string n2 →
  n1 = n2.
Proof.
  intros Hstring.
  pose proof (parse_decimal_string_decimal_string n1) as Hparse1.
  pose proof (parse_decimal_string_decimal_string n2) as Hparse2.
  rewrite Hstring in Hparse1.
  by rewrite Hparse2 in Hparse1; simplify_eq/=.
Qed.

Lemma decimal_string_exists_decision s :
  Decision (∃ n, s = decimal_string n).
Proof.
  destruct (parse_canonical_decimal_string s) as [n|] eqn:Hparse.
  - left. exists n. symmetry. by apply parse_canonical_decimal_string_sound.
  - right. intros [n ->].
    rewrite parse_canonical_decimal_string_decimal_string in Hparse. done.
Defined.

Example parse_decimal_string_0 :
  parse_decimal_string "0"%go = Some 0.
Proof. done. Qed.

Example parse_decimal_string_1 :
  parse_decimal_string "1"%go = Some 1.
Proof. done. Qed.

Example parse_decimal_string_10 :
  parse_decimal_string "10"%go = Some 10.
Proof. done. Qed.

Example parse_decimal_string_empty :
  parse_decimal_string ""%go = None.
Proof. done. Qed.

Example parse_decimal_string_01 :
  parse_decimal_string "01"%go = Some 1.
Proof. done. Qed.

Example parse_decimal_string_00 :
  parse_decimal_string "00"%go = Some 0.
Proof. done. Qed.

Example parse_canonical_decimal_string_1 :
  parse_canonical_decimal_string "1"%go = Some 1.
Proof. done. Qed.

Example parse_canonical_decimal_string_01 :
  parse_canonical_decimal_string "01"%go = None.
Proof. done. Qed.

Example parse_decimal_string_non_digit_suffix :
  parse_decimal_string "1a"%go = None.
Proof. done. Qed.

End proof.
