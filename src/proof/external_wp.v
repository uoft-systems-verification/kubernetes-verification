From New.proof Require Export prelude empty_ffi.
From New.code Require Export fmt.
From New.proof Require Export fmt strconv_init rand_init strings.
From New.proof.string Require Export decimal.

Section proof.
Context `{hG: !heapGS Σ}.
Context `{!ffi_semantics _ _}.
Context {sem : go.Semantics}.

Lemma wp_fmt_Sprintf (format: go_string) string_slice (string_list: list interface.t):
  {{{ is_pkg_init fmt ∗
      string_slice ↦* string_list
  }}}
    @! fmt.Sprintf #format #string_slice
  {{{ (v: go_string), RET #v;
      True
  }}}.
Proof.
Admitted.

Lemma wp_rand_Int63 :
  {{{ is_pkg_init rand }}}
    @! rand.Int63 #()
  {{{ (v: w64), RET #v; True }}}.
Proof.
Admitted.

Lemma wp_strconv_FormatInt (i: w64) (base: w64):
  {{{ is_pkg_init strconv }}}
    @! strconv.FormatInt #i #base
  {{{ (v: go_string), RET #v; True }}}.
Proof.
Admitted.

Lemma wp_strconv_Itoa (i: w64):
  {{{ is_pkg_init strconv ∗
      ⌜ 0 <= sint.Z i ⌝ }}}
    @! strconv.Itoa #i
  {{{ RET #(decimal_string (sint.nat i)); True }}}.
Proof.
Admitted.

Definition go_int32_max : Z := 2 ^ 31 - 1.
Definition go_int32_max_nat : nat := Z.to_nat go_int32_max.

Definition go_int_max : Z := 2 ^ 63 - 1.

Definition parse_int32_decimal_result (s : go_string) (i : w64) (err : error.t) : Prop :=
  match parse_decimal_string s with
  | Some n =>
      if decide (n <= go_int32_max_nat)%nat
      then err = interface.nil ∧
        sint.nat i = n ∧
        sint.Z i = Z.of_nat n ∧
        (0 <= sint.Z i <= go_int32_max)%Z
      else err ≠ interface.nil
  | None => err ≠ interface.nil
  end.

Lemma wp_strconv_ParseInt_decimal_int32 (s : go_string) :
  {{{ is_pkg_init strconv }}}
    @! strconv.ParseInt #s #(W64 10) #(W64 32)
  {{{ (i : w64) (err : error.t), RET (#i, #err);
      ⌜ parse_int32_decimal_result s i err ⌝ }}}.
Proof.
Admitted.

Lemma last_index_byte_found_facts (s : go_string) (sep : w8)
    (prefix suffix : go_string) idx :
  Z.of_nat (length s) <= go_int_max →
  s = prefix ++ [sep] ++ suffix →
  sint.Z idx = Z.of_nat (length prefix) →
  sint.nat idx = length prefix ∧
  0 <= sint.Z (word.add idx (W64 1)) ∧
  sint.nat (word.add idx (W64 1)) = S (length prefix).
Proof.
  intros Hlen Hdecomp Hidx.
  assert (Hprefix_next_bound : Z.of_nat (S (length prefix)) <= go_int_max).
  { rewrite Hdecomp app_length /= in Hlen. lia. }
  unfold go_int_max in Hprefix_next_bound.
  assert (Hidx_next : sint.Z (word.add idx (W64 1)) =
      Z.of_nat (S (length prefix))) by word.
  repeat split.
  - word.
  - rewrite Hidx_next. lia.
  - word.
Qed.

(* Spec for strings.LastIndex when the separator is a one-byte string. The
   successful branch exposes the split around the last occurrence: the suffix
   contains no [sep], so the returned index is the length of the prefix before
   that final separator. The failure branch states that [sep] is absent and the
   returned index is -1. *)
Lemma wp_strings_LastIndex_singleton (s : go_string) (sep : w8) :
  {{{ is_pkg_init strings ∗
      ⌜ Z.of_nat (length s) <= go_int_max ⌝ }}}
    @! strings.LastIndex #s #([sep] : go_string)
  {{{ (idx : w64), RET #idx;
      ⌜ (∃ prefix suffix,
          s = prefix ++ [sep] ++ suffix ∧
          sep ∉ suffix ∧
          sint.Z idx = Z.of_nat (length prefix)) ∨
        (sep ∉ s ∧ sint.Z idx = -1) ⌝ }}}.
Proof.
Admitted.

Lemma wp_string_slice (s : go_string) (low high : w64) :
  {{{ ⌜ 0 <= sint.Z low <= sint.Z high ∧
        sint.nat high <= length s ⌝ }}}
    Slice go.string (#s, #low, #high)%V
  {{{ RET #(subslice (sint.nat low) (sint.nat high) s); True }}}.
Proof.
Admitted.

Lemma wp_string_slice_to_end (s : go_string) (low : w64) :
  {{{ ⌜ 0 <= sint.Z low ∧ sint.nat low <= length s ⌝ }}}
    Slice go.string ((#s, #low)%V, #(functions go.len [go.string]) (#s))%E
  {{{ RET #(drop (sint.nat low) s); True }}}.
Proof.
Admitted.

End proof.
