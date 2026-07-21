From New.proof Require Export prelude empty_ffi.
(* Shared weakest-precondition helpers for external and generated Go code. *)
From New.code Require Export fmt.
From New.code.k8s_io.api.apps Require Export v1.
From New.code.k8s_io.apimachinery.pkg Require Export runtime.
From New.code.k8s_io.apimachinery.pkg.apis.meta Require Export v1.
From New.proof Require Export fmt strconv_init rand_init strings.
From New.proof.string Require Export decimal.

Section proof.
Context `{hG: !heapGS Σ} `{!ffi_semantics _ _}.
Context `{!ffi_semantics _ _}.
Context {sem : go.Semantics}.

Definition statefulset_pod_name_label : go_string :=
  "statefulset.kubernetes.io/pod-name"%go.

Definition pod_index_label : go_string :=
  "apps.kubernetes.io/pod-index"%go.

(* Shared pure Go interface-packaging rule for pointer values. *)
Lemma pure_wp_convert_pointer_to_interface t to elems
    `{!to ≤u go.InterfaceType elems} (l : loc) :
  PureWp True (Convert (go.PointerType t) to (#l))
    (#(interface.mk_ok (go.PointerType t) #l)).
Proof.
  apply pure_wp_go_step_det.
  apply (@go.convert_to_interface _ _ _ _ _ (#l) _
    (go.PointerType t) _ _ _ _).
Qed.
#[global] Existing Instance pure_wp_convert_pointer_to_interface.

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

(* Spec for strconv.ParseInt(s, 10, 32) on decimal strings. If [s] parses as a
   natural number within signed int32 range, ParseInt succeeds and returns that
   number as a Go int64 value. If [s] is not decimal or the parsed value exceeds
   the int32 bound requested by the bit-size argument, ParseInt returns a
   non-nil error; the numeric return value is intentionally left unspecified. *)
Lemma wp_strconv_ParseInt_decimal_int32 (s : go_string) :
  {{{ is_pkg_init strconv }}}
    @! strconv.ParseInt #s #(W64 10) #(W64 32)
  {{{ (i : w64) (err : error.t), RET (#i, #err);
      ⌜ match parse_decimal_string s with
        | Some n =>
            if decide (n <= go_int32_max_nat)%nat
            then err = interface.nil ∧
              sint.nat i = n ∧
              sint.Z i = Z.of_nat n ∧
              (0 <= sint.Z i <= go_int32_max)%Z
            else err ≠ interface.nil
        | None => err ≠ interface.nil
        end ⌝ }}}.
Proof.
Admitted.

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
