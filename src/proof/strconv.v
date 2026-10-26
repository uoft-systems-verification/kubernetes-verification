From New.proof Require Export strconv_init.
From New.proof Require Import prelude empty_ffi.
From New.proof.string Require Export decimal.

(** Nonempty decimal input whose value fits in a uint64. *)
Definition uint64_decimal (s : go_string) : Prop :=
  ∃ n, parse_decimal_string s = Some n ∧ (Z.of_nat n < 2 ^ 64)%Z.

Lemma uint64_decimal_non_empty s : uint64_decimal s → s ≠ ""%go.
Proof.
  intros [n [Hparse _]] ->. discriminate Hparse.
Qed.

Section proof.
Context `{hG: !heapGS Σ} `{!ffi_semantics _ _}.
Context {sem : go.Semantics} {package_sem : strconv.Assumptions}.
Local Set Default Proof Using "All".

(** A returned error can format its message without borrowing the caller's heap. *)
Definition error_message_spec (err : interface.t) : iProp Σ :=
  match err with
  | interface.nil => True
  | interface.ok err_ok =>
      ({{{ True }}}
        #(methods err_ok.(interface.ty) "Error" err_ok.(interface.v)) #()
      {{{ (message : go_string), RET #message; True }}})%I
  end.

(** Trusted standard-library boundary for formatting a nonnegative int64 in
    base ten. The result describes the actual number, not just parseability. *)
Lemma wp_FormatInt_decimal (n : w64) :
  {{{ is_pkg_init strconv ∗ ⌜ 0 ≤ sint.Z n ⌝ }}}
    @! strconv.FormatInt #n #(W64 10)
  {{{ RET #(decimal_string (Z.to_nat (sint.Z n))); True }}}.
Proof. Admitted.

(** Trusted standard-library boundary for base-10 uint64 parsing. *)
Lemma wp_ParseUint_decimal (s : go_string) :
  {{{ is_pkg_init strconv }}}
    @! strconv.ParseUint #s #(W64 10) #(W64 64)
  {{{ (ret : w64) (err : interface.t), RET (#ret, #err);
      ⌜ uint64_decimal s → err = interface.nil ⌝ ∗
      error_message_spec err
  }}}.
Proof. Admitted.

End proof.
