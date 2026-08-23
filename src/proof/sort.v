From New.proof Require Export sort_init.

Section proof.
Context `{hG: heapGS Σ} `{!ffi_semantics _ _}.
Context {sem : go.Semantics} {package_sem : sort.Assumptions}.
Collection W := sem + package_sem.

(** Exchange the elements at [i] and [j]. Out-of-bounds indices leave the list
    unchanged; the [Swap] specification below requires both indices in bounds. *)
Definition list_swap {A} (xs : list A) (i j : nat) : list A :=
  match xs !! i, xs !! j with
  | Some xi, Some xj => <[j := xi]> (<[i := xj]> xs)
  | _, _ => xs
  end.

Lemma list_swap_fmap {A B} (f : A → B) xs i j :
  f <$> list_swap xs i j = list_swap (f <$> xs) i j.
Proof.
  rewrite /list_swap !list_lookup_fmap.
  destruct (xs !! i) as [xi|] eqn:Hi;
    destruct (xs !! j) as [xj|] eqn:Hj; simpl; try done.
  rewrite !list_fmap_insert. done.
Qed.

Lemma list_swap_permutation {A} (xs : list A) i j :
  xs ≡ₚ list_swap xs i j.
Proof.
  rewrite /list_swap.
  destruct (xs !! i) as [xi|] eqn:Hi;
    destruct (xs !! j) as [xj|] eqn:Hj; try done.
  symmetry. eapply Permutation_insert_swap; eauto.
Qed.

(** The part of Go's [sort.Interface] protocol needed to show that sorting is
    a permutation. [Less] may return either result, but must preserve the data. *)
Class SortInterfaceSpec {A D : Type} (T : go.type)
    `{!ZeroVal D} `{!TypedPointsto D} `{!IntoValTyped D T}
    (contents : D → list A → iProp Σ) : Prop := {
  wp_sort_len (data : D) (xs : list A) :
    {{{ contents data xs }}}
      data @! T @! "Len" #()
    {{{ (n : w64), RET #n;
        contents data xs ∗
        ⌜ sint.nat n = length xs ∧ 0 ≤ sint.Z n ⌝
    }}};
  wp_sort_less (data : D) (xs : list A) (i j : w64) :
    0 ≤ sint.Z i < length xs → 0 ≤ sint.Z j < length xs →
    {{{ contents data xs }}}
      data @! T @! "Less" #i #j
    {{{ (b : bool), RET #b; contents data xs }}};
  wp_sort_swap (data : D) (xs : list A) (i j : w64) :
    0 ≤ sint.Z i < length xs → 0 ≤ sint.Z j < length xs →
    {{{ contents data xs }}}
      data @! T @! "Swap" #i #j
    {{{ RET #(); contents data (list_swap xs (sint.nat i) (sint.nat j)) }}}
}.

(** Trusted standard-library boundary: [sort.Sort] is opaque in the generated
    semantics, so its correctness is assumed for every value satisfying the
    method-level protocol above. *)
Lemma wp_Sort {A D : Type} (T : go.type)
    `{!ZeroVal D} `{!TypedPointsto D} `{!IntoValTyped D T}
    (contents : D → list A → iProp Σ) `{!SortInterfaceSpec T contents}
    (data : D) (xs : list A) :
  {{{ is_pkg_init sort ∗
      contents data xs
  }}}
    (let: "$a0" := Convert T sort.Interface #data in
     (FuncResolve sort.Sort [] #()) "$a0")%E
  {{{ ys, RET #();
      contents data ys ∗
      ⌜ xs ≡ₚ ys ⌝
  }}}.
Proof. Admitted.

End proof.
