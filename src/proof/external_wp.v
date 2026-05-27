From New.proof Require Export prelude empty_ffi.
From New.code Require Export fmt.
From New.proof Require Export fmt strconv_init.

Section proof.
Context `{hG: !heapGS Σ}.
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

Lemma wp_strconv_FormatInt (i: w64) (base: w64):
  {{{ is_pkg_init strconv }}}
    @! strconv.FormatInt #i #base
  {{{ (v: go_string), RET #v; True }}}.
Proof.
Admitted.

End proof.
