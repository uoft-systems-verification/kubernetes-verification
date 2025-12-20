From proof Require Import prelude empty_ffi.

Section proof.

Definition byte_dash : w8 := W8 45.  (* ASCII '-' *)

Axiom reserved_name : go_string → Prop.

Definition no_dash (s: go_string) : Prop :=
  Forall (λ b, b ≠ byte_dash) s.

Definition reserved_derived_name (derived_name: go_string) : Prop :=
  ∃ prefix suffix,
    reserved_name prefix ∧
    no_dash suffix ∧
    derived_name = prefix ++ "-"%go ++ suffix.

Definition unreserved_generated_name (generated_name: go_string) : Prop :=
    ∃ prefix suffix,
      ¬ reserved_name prefix ∧
      no_dash suffix ∧
      length suffix = 5%nat ∧
      generated_name = prefix ++ "-"%go ++ suffix.

Lemma suffix_unique_length prefix1 suffix1 prefix2 suffix2 :
  no_dash suffix1 →
    no_dash suffix2 →
      prefix1 ++ "-"%go ++ suffix1 = prefix2 ++ "-"%go ++ suffix2 →
        length suffix1 = length suffix2.
Proof.
  intros Hno_dash1 Hno_dash2 Heq.
  unfold no_dash in *.
  destruct (decide (length suffix1 = length suffix2)) as [|Hneq]; [done|exfalso].
  apply app_eq_inv in Heq.
  destruct Heq as [(k & Hprefix_eq & Hsuffix_eq) | (k & Hprefix_eq & Hsuffix_eq)].
  - assert (k ≠ []) as Hk_nonempty.
    { intros Hcontra. rewrite Hcontra in Hsuffix_eq.
      apply (f_equal length) in Hsuffix_eq.
      simpl in Hsuffix_eq. lia. }
    destruct k as [|b k']; [done|].
    assert (b = byte_dash) as Hb_dash.
    { injection Hsuffix_eq as <- _. done. }
    injection Hsuffix_eq as _ ->.
    apply Forall_app in Hno_dash2 as [_ Hno_dash2_tail].
    apply Forall_cons_1 in Hno_dash2_tail.
    apply Hno_dash2_tail. reflexivity.
  - assert (k ≠ []) as Hk_nonempty.
    { intros Hcontra. rewrite Hcontra in Hsuffix_eq.
      apply (f_equal length) in Hsuffix_eq. 
      simpl in Hsuffix_eq. lia. }
    destruct k as [|b k']; [done|].
    assert (b = byte_dash) as Hb_dash.
    { injection Hsuffix_eq as <- _. done. }
    injection Hsuffix_eq as _ ->.
    apply Forall_app in Hno_dash1 as [_ Hno_dash1_tail].
    apply Forall_cons_1 in Hno_dash1_tail.
    apply Hno_dash1_tail. reflexivity.
Qed.

Lemma app_dash_inj prefix1 suffix1 prefix2 suffix2 :
  length suffix1 = length suffix2 →
    prefix1 ++ "-"%go ++ suffix1 = prefix2 ++ "-"%go ++ suffix2 →
      prefix1 = prefix2 ∧ suffix1 = suffix2.
Proof.
  intros Hlen Heq.
  assert (length ("-"%go ++ suffix1) = length ("-"%go ++ suffix2)) as Hlen'.
  { simpl. lia. }
  apply app_inj_2 in Heq; [|done].
  destruct Heq as [Hprefix_eq Hdash_suffix_eq].
  split; [done|].
  injection Hdash_suffix_eq as ->. done.
Qed.

Lemma no_conflict_between_derived_name_and_generated_name name1 name2 :
  reserved_derived_name name1 →
    unreserved_generated_name name2 →
      name1 ≠ name2.
Proof.
  intros Hname1 Hname2 Hcontra.
  destruct Hname1 as [prefix1 [suffix1 [Hreserved1 [Hno_dash1 ->]]]].
  destruct Hname2 as [prefix2 [suffix2 [Hnotreserved2 [Hno_dash2 [Hlen2 ->]]]]].
  assert (length suffix1 = length suffix2) as Hsuffix_len.
  { apply (suffix_unique_length _ _ _ _ Hno_dash1 Hno_dash2 Hcontra). }
  apply app_dash_inj in Hcontra; [|done].
  destruct Hcontra as [-> _].
  done.
Qed.

End proof.
