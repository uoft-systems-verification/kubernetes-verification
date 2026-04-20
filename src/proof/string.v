From New.proof Require Import prelude empty_ffi.

Section proof.

Lemma prefix_length_sep (sep : w8) prefix1 suffix1 prefix2 suffix2 :
  Forall (λ b, b ≠ sep) prefix1 →
    Forall (λ b, b ≠ sep) prefix2 →
      prefix1 ++ [sep] ++ suffix1 = prefix2 ++ [sep] ++ suffix2 →
        length prefix1 = length prefix2 ∧ length suffix1 = length suffix2.
Proof.
  intros Hno_sep1 Hno_sep2 Heq.
  destruct (decide (length prefix1 = length prefix2)) as [Hlen_eq|Hneq].
  - split; [done|].
    apply (f_equal length) in Heq.
    repeat rewrite app_length in Heq. simpl in Heq. lia.
  - exfalso.
    apply app_eq_inv in Heq.
    destruct Heq as [(k & Hprefix_eq & Hsuffix_eq) | (k & Hprefix_eq & Hsuffix_eq)].
    + assert (k ≠ []) as Hk_nonempty.
      { intros Hcontra. rewrite Hcontra in Hprefix_eq. rewrite app_nil_r in Hprefix_eq.
        apply (f_equal length) in Hprefix_eq. lia. }
      destruct k as [|b k']; [done|].
      simpl in Hsuffix_eq. injection Hsuffix_eq as Hb_eq _.
      subst b.
      rewrite Hprefix_eq in Hno_sep1.
      apply Forall_app in Hno_sep1 as [_ Hk_no_sep].
      apply Forall_cons_1 in Hk_no_sep.
      apply Hk_no_sep. reflexivity.
    + assert (k ≠ []) as Hk_nonempty.
      { intros Hcontra. rewrite Hcontra in Hprefix_eq. rewrite app_nil_r in Hprefix_eq.
        apply (f_equal length) in Hprefix_eq. lia. }
      destruct k as [|b k']; [done|].
      simpl in Hsuffix_eq. injection Hsuffix_eq as Hb_eq _.
      subst b.
      rewrite Hprefix_eq in Hno_sep2.
      apply Forall_app in Hno_sep2 as [_ Hk_no_sep].
      apply Forall_cons_1 in Hk_no_sep.
      apply Hk_no_sep. reflexivity.
Qed.

Lemma suffix_length_sep (sep : w8) prefix1 suffix1 prefix2 suffix2 :
  Forall (λ b, b ≠ sep) suffix1 →
    Forall (λ b, b ≠ sep) suffix2 →
      prefix1 ++ [sep] ++ suffix1 = prefix2 ++ [sep] ++ suffix2 →
        length prefix1 = length prefix2 ∧ length suffix1 = length suffix2.
Proof.
  intros Hno_sep1 Hno_sep2 Heq.
  destruct (decide (length suffix1 = length suffix2)) as [Hlen_eq|Hneq].
  - split; [|done].
    apply (f_equal length) in Heq.
    repeat rewrite app_length in Heq. simpl in Heq. lia.
  - exfalso.
    apply app_eq_inv in Heq.
    destruct Heq as [(k & Hprefix_eq & Hsuffix_eq) | (k & Hprefix_eq & Hsuffix_eq)].
    + assert (k ≠ []) as Hk_nonempty.
      { intros Hcontra. rewrite Hcontra in Hsuffix_eq.
        apply (f_equal length) in Hsuffix_eq.
        simpl in Hsuffix_eq. lia. }
      destruct k as [|b k']; [done|].
      assert (b = sep) as Hb_sep.
      { injection Hsuffix_eq as <- _. done. }
      injection Hsuffix_eq as _ ->.
      apply Forall_app in Hno_sep2 as [_ Hno_sep2_tail].
      apply Forall_cons_1 in Hno_sep2_tail.
      apply Hno_sep2_tail. reflexivity.
    + assert (k ≠ []) as Hk_nonempty.
      { intros Hcontra. rewrite Hcontra in Hsuffix_eq.
        apply (f_equal length) in Hsuffix_eq.
        simpl in Hsuffix_eq. lia. }
      destruct k as [|b k']; [done|].
      assert (b = sep) as Hb_sep.
      { injection Hsuffix_eq as <- _. done. }
      injection Hsuffix_eq as _ ->.
      apply Forall_app in Hno_sep1 as [_ Hno_sep1_tail].
      apply Forall_cons_1 in Hno_sep1_tail.
      apply Hno_sep1_tail. reflexivity.
Qed.

Lemma app_sep_suffix_inj (sep: w8) prefix1 suffix1 prefix2 suffix2 :
  Forall (λ b, b ≠ sep) suffix1 →
    Forall (λ b, b ≠ sep) suffix2 →
      prefix1 ++ [sep] ++ suffix1 = prefix2 ++ [sep] ++ suffix2 →
        prefix1 = prefix2 ∧ suffix1 = suffix2.
Proof.
  intros Hno_sep1 Hno_sep2 Heq.
  assert (length suffix1 = length suffix2) as Hlen_suffix.
  { apply (suffix_length_sep sep _ _ _ _ Hno_sep1 Hno_sep2 Heq). }
  assert (length ([sep] ++ suffix1) = length ([sep] ++ suffix2)) as Hlen'.
  { simpl. lia. }
  apply app_inj_2 in Heq; [|done].
  destruct Heq as [Hprefix_eq Hsep_suffix_eq].
  split; [done|].
  injection Hsep_suffix_eq as ->. done.
Qed.

Lemma app_prefix_sep_inj (sep: w8) prefix1 suffix1 prefix2 suffix2 :
  Forall (λ b, b ≠ sep) prefix1 →
    Forall (λ b, b ≠ sep) prefix2 →
      prefix1 ++ [sep] ++ suffix1 = prefix2 ++ [sep] ++ suffix2 →
        prefix1 = prefix2 ∧ suffix1 = suffix2.
Proof.
  intros Hno_sep1 Hno_sep2 Heq.
  assert (length prefix1 = length prefix2) as Hlen_prefix.
  { apply (prefix_length_sep sep _ _ _ _ Hno_sep1 Hno_sep2 Heq). }
  assert (length ([sep] ++ suffix1) = length ([sep] ++ suffix2)) as Hlen'.
  { apply (f_equal length) in Heq.
    repeat rewrite app_length in Heq.
    rewrite Hlen_prefix in Heq. simpl in Heq.
    repeat rewrite app_length. simpl. lia. }
  apply app_inj_2 in Heq; [|done].
  destruct Heq as [Hprefix_eq Hsep_suffix_eq].
  split; [done|].
  injection Hsep_suffix_eq as ->. done.
Qed.

Definition byte_dash : w8 := W8 45.  (* ASCII '-' *)
Definition byte_slash : w8 := W8 47.  (* ASCII '/' *)

Axiom reserved_name : go_string → Prop.

Definition dash_free (s: go_string) : Prop :=
  Forall (λ b, b ≠ byte_dash) s.

Definition slash_free (s: go_string) : Prop :=
  Forall (λ b, b ≠ byte_slash) s.

Definition w8_eq_dec (x y : w8) : {x = y} + {x ≠ y}.
Proof.
  destruct (decide (x = y)); [left|right]; done.
Defined.

Lemma slash_free_count_occ_zero s :
  slash_free s ↔ count_occ w8_eq_dec s byte_slash = 0%nat.
Proof.
  unfold slash_free.
  induction s as [|b s IH]; simpl.
  - split; done.
  - split.
    + intros Hsf.
      inversion Hsf as [|? ? Hneq Hsf']; subst.
      destruct (w8_eq_dec b byte_slash) as [->|Hneq'].
      * exfalso. apply Hneq. reflexivity.
      * apply IH in Hsf'. exact Hsf'.
    + intros Hcount.
      destruct (w8_eq_dec b byte_slash) as [->|Hneq']; simpl in Hcount.
      * discriminate.
      * constructor; [exact Hneq'|].
        apply IH. exact Hcount.
Qed.

Definition reserved_derived_name (derived_name: go_string) : Prop :=
  ∃ prefix suffix,
    reserved_name prefix ∧
    dash_free suffix ∧
    derived_name = prefix ++ "-"%go ++ suffix.

Definition unreserved_generated_name (generated_name: go_string) : Prop :=
    ∃ prefix suffix,
      ¬ reserved_name prefix ∧
      dash_free suffix ∧
      length suffix = 5%nat ∧
      generated_name = prefix ++ "-"%go ++ suffix.

Lemma derived_name_and_generated_name_neq name1 name2 :
  reserved_derived_name name1 →
    unreserved_generated_name name2 →
      name1 ≠ name2.
Proof.
  intros Hname1 Hname2 Hcontra.
  destruct Hname1 as (prefix1 & suffix1 & Hreserved1 & Hdash_free1 & ->).
  destruct Hname2 as (prefix2 & suffix2 & Hnotreserved2 & Hdash_free2 & Hlen2 & ->).
  assert ("-"%go = [byte_dash]) as Hdash_eq by done.
  rewrite Hdash_eq in Hcontra.
  apply app_sep_suffix_inj in Hcontra; [|done|done].
  destruct Hcontra as [-> _].
  done.
Qed.

Lemma pod_controller_index_key_inj namespace1 kind1 name1 uid1 namespace2 kind2 name2 uid2 :
  slash_free namespace1 ∧ slash_free kind1 ∧ slash_free name1 ∧ slash_free uid1 ∧
  slash_free namespace2 ∧ slash_free kind2 ∧ slash_free name2 ∧ slash_free uid2 →
    namespace1 ++ "/"%go ++ kind1 ++ "/"%go ++ name1 ++ "/"%go ++ uid1 =
    namespace2 ++ "/"%go ++ kind2 ++ "/"%go ++ name2 ++ "/"%go ++ uid2 →
      namespace1 = namespace2 ∧ kind1 = kind2 ∧ name1 = name2 ∧ uid1 = uid2.
Proof.
  intros (Hslash_free_ns1 & Hslash_free_k1 & Hslash_free_n1 & Hslash_free_u1 &
    Hslash_free_ns2 & Hslash_free_k2 & Hslash_free_n2 & Hslash_free_u2) Heq.
  assert ("/"%go = [byte_slash]) as Hslash_eq by done.
  rewrite !Hslash_eq in Heq.
  apply app_prefix_sep_inj in Heq; [|done|done].
  destruct Heq as [Hns_eq Heq].
  apply app_prefix_sep_inj in Heq; [|done|done].
  destruct Heq as [Hk_eq Heq].
  apply app_prefix_sep_inj in Heq; [|done|done].
  destruct Heq as [Hn_eq Hu_eq].
  done.
Qed.

Lemma pod_controller_index_key_inequality1 ns1 ns2 suffix :
  slash_free ns1 → slash_free ns2 →
  ns1 ≠ ns2 ++ "/"%go ++ suffix.
Proof.
  intros Hns1_slash_free Hns2_slash_free Heq.
  assert ("/"%go = [byte_slash]) as Hslash_eq by done.
  rewrite Hslash_eq in Heq.
  unfold slash_free in Hns1_slash_free.
  rewrite Heq in Hns1_slash_free.
  rewrite !Forall_app in Hns1_slash_free.
  destruct Hns1_slash_free as [_ [Hcontra _]].
  apply Forall_cons_1 in Hcontra.
  apply Hcontra. reflexivity.
Qed.

Lemma pod_controller_index_key_inequality2 ns1 ns2 suffix1 suffix2 :
  slash_free ns1 → slash_free ns2 → ns1 ≠ ns2 →
  ns1 ++ "/"%go ++ suffix1 ≠ ns2 ++ "/"%go ++ suffix2.
Proof.
  intros Hns1_slash_free Hns2_slash_free Hns_neq Hcontra.
  assert ("/"%go = [byte_slash]) as Hslash_eq by done.
  rewrite Hslash_eq in Hcontra.
  apply app_prefix_sep_inj in Hcontra; [|done|done].
  destruct Hcontra as [Hns_eq _].
  done.
Qed.

Lemma pod_controller_index_key_slash_count namespace kind name uid :
  count_occ w8_eq_dec (namespace ++ "/"%go ++ kind ++ "/"%go ++ name ++ "/"%go ++ uid) byte_slash =
    (count_occ w8_eq_dec namespace byte_slash +
     count_occ w8_eq_dec kind byte_slash +
     count_occ w8_eq_dec name byte_slash +
     count_occ w8_eq_dec uid byte_slash + 3)%nat.
Proof.
  assert ("/"%go = [byte_slash]) as Hslash_eq by done.
  rewrite Hslash_eq.
  repeat rewrite count_occ_app.
  repeat match goal with
  | |- context [count_occ w8_eq_dec [byte_slash] byte_slash] =>
      replace (count_occ w8_eq_dec [byte_slash] byte_slash) with 1%nat by
        (simpl; destruct (w8_eq_dec byte_slash byte_slash); [done|congruence])
  end.
  lia.
Qed.

Lemma pod_controller_index_key_inj_right namespace1 kind1 name1 uid1 namespace2 kind2 name2 uid2 :
  slash_free namespace1 →
  slash_free namespace2 →
  slash_free kind2 →
  slash_free name2 →
  slash_free uid2 →
  namespace1 ++ "/"%go ++ kind1 ++ "/"%go ++ name1 ++ "/"%go ++ uid1 =
  namespace2 ++ "/"%go ++ kind2 ++ "/"%go ++ name2 ++ "/"%go ++ uid2 →
  namespace1 = namespace2 ∧ kind1 = kind2 ∧ name1 = name2 ∧ uid1 = uid2.
Proof.
  intros Hns1_sf Hns2_sf Hkind2_sf Hname2_sf Huid2_sf Heq.
  pose proof (pod_controller_index_key_slash_count namespace1 kind1 name1 uid1) as Hcount1.
  pose proof (pod_controller_index_key_slash_count namespace2 kind2 name2 uid2) as Hcount2.
  pose proof (proj1 (slash_free_count_occ_zero namespace1) Hns1_sf) as Hns1_count.
  pose proof (proj1 (slash_free_count_occ_zero namespace2) Hns2_sf) as Hns2_count.
  pose proof (proj1 (slash_free_count_occ_zero kind2) Hkind2_sf) as Hkind2_count.
  pose proof (proj1 (slash_free_count_occ_zero name2) Hname2_sf) as Hname2_count.
  pose proof (proj1 (slash_free_count_occ_zero uid2) Huid2_sf) as Huid2_count.
  rewrite Heq in Hcount1.
  rewrite Hns2_count in Hcount2.
  rewrite Hkind2_count in Hcount2.
  rewrite Hname2_count in Hcount2.
  rewrite Huid2_count in Hcount2.
  rewrite Hns1_count in Hcount1.
  rewrite Hcount2 in Hcount1.
  assert (count_occ w8_eq_dec kind1 byte_slash = 0%nat ∧
          count_occ w8_eq_dec name1 byte_slash = 0%nat ∧
          count_occ w8_eq_dec uid1 byte_slash = 0%nat) as (Hkind1_count & Hname1_count & Huid1_count).
  { lia. }
  pose proof (proj2 (slash_free_count_occ_zero kind1) Hkind1_count) as Hkind1_sf.
  pose proof (proj2 (slash_free_count_occ_zero name1) Hname1_count) as Hname1_sf.
  pose proof (proj2 (slash_free_count_occ_zero uid1) Huid1_count) as Huid1_sf.
  eapply pod_controller_index_key_inj; [|exact Heq].
  repeat split; eauto.
Qed.


End proof.
