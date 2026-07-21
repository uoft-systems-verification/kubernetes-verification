From Coq Require Import Lists.List Sorting.Permutation.
From New.proof Require Import prelude empty_ffi.
Require Export New.generatedproof.benchmark.basic.

Set Default Proof Using "Type".

Section init.
Context `{hG: heapGS Σ} `{!ffi_semantics _ _}.
Context {sem : go.Semantics} {package_sem : code.benchmark.basic.basic.Assumptions}.
Collection W := sem + package_sem.

#[global] Instance : IsPkgInit (iProp Σ) code.benchmark.basic.pkg_id.basic := define_is_pkg_init True%I.
#[global] Instance : GetIsPkgInitWf (iProp Σ) code.benchmark.basic.pkg_id.basic := build_get_is_pkg_init_wf.

End init.

Section proof.
Context `{hG: !heapGS Σ} `{!ffi_semantics _ _}.
Context {sem : go.Semantics}.

Definition go_int_min : Z := -(2 ^ 63).
Definition go_int_max : Z := 2 ^ 63.

Definition go_int_safe (z : Z) : Prop :=
  go_int_min <= z < go_int_max.

Definition length_safe {A} (xs : list A) : Prop :=
  Z.of_nat (length xs) < go_int_max.

Fixpoint fact_nat (n : nat) : nat :=
  match n with
  | O => 1
  | S n' => n * fact_nat n'
  end.

Definition factorial_result (n : w64) : Z :=
  if decide (sint.Z n < 0)%Z then 0 else Z.of_nat (fact_nat (Z.to_nat (sint.Z n))).

Definition sum_Z (values : list w64) : Z :=
  fold_left Z.add (List.map sint.Z values) 0.

Definition sum_no_overflow (values : list w64) : Prop :=
  ∀ n, (n <= length values)%nat → go_int_safe (sum_Z (take n values)).

Definition positive_ints (values : list w64) : list w64 :=
  List.filter (λ value, bool_decide (0 < sint.Z value)%Z) values.

Definition count_string (key : go_string) (values : list go_string) : nat :=
  length (List.filter (λ value, bool_decide (value = key)) values).

Definition frequency_map_spec (values : list go_string) (counts : gmap go_string w64) : Prop :=
  (∀ key, key ∈ values →
    ∃ count, counts !! key = Some count ∧ sint.Z count = Z.of_nat (count_string key values)) ∧
  (∀ key count, counts !! key = Some count →
    sint.Z count = Z.of_nat (count_string key values)).

Definition lookup_int (counts : gmap go_string w64) (key : go_string) : w64 :=
  default (W64 0) (counts !! key).

Definition merge_counts_no_overflow (left right : gmap go_string w64) : Prop :=
  ∀ key, go_int_safe (sint.Z (lookup_int left key) + sint.Z (lookup_int right key)).

Definition merge_counts_spec
    (left right result : gmap go_string w64) : Prop :=
  dom result = dom left ∪ dom right ∧
  ∀ key, sint.Z (lookup_int result key) =
    sint.Z (lookup_int left key) + sint.Z (lookup_int right key).

Fixpoint unique_go_strings_go (seen values : list go_string) : list go_string :=
  match values with
  | [] => []
  | value :: values' =>
      if bool_decide (value ∈ seen) then
        unique_go_strings_go seen values'
      else
        value :: unique_go_strings_go (value :: seen) values'
  end.

Definition unique_go_strings (values : list go_string) : list go_string :=
  unique_go_strings_go [] values.

Fixpoint sorted_by_sint (values : list w64) : Prop :=
  match values with
  | [] => True
  | value :: values' =>
      Forall (λ other, sint.Z value <= sint.Z other)%Z values' ∧
      sorted_by_sint values'
  end.

Definition binary_search_result (values : list w64) (target index : w64) : Prop :=
  if decide (sint.Z index = -1)%Z then
    ∀ value, value ∈ values → value ≠ target
  else
    0 <= sint.Z index < Z.of_nat (length values) ∧
    values !! Z.to_nat (sint.Z index) = Some target.

Definition sort_result (before after : list w64) : Prop :=
  Permutation before after ∧ sorted_by_sint after.

Definition same_outside_range (low high : w64) (before after : list w64) : Prop :=
  length before = length after ∧
  ∀ i before_i after_i,
    before !! i = Some before_i →
    after !! i = Some after_i →
    (i < Z.to_nat (sint.Z low) ∨ Z.to_nat (sint.Z high) < i)%nat →
    after_i = before_i.

Definition range_sorted_by_sint (low high : w64) (values : list w64) : Prop :=
  ∀ i j value_i value_j,
    (Z.to_nat (sint.Z low) <= i)%nat →
    (i <= j)%nat →
    (j <= Z.to_nat (sint.Z high))%nat →
    values !! i = Some value_i →
    values !! j = Some value_j →
    sint.Z value_i <= sint.Z value_j.

Definition quick_sort_range_no_overflow (values : list w64) (low high : w64) : Prop :=
  length_safe values ∧
  go_int_safe (sint.Z low - 1) ∧
  go_int_safe (sint.Z high + 1) ∧
  if decide (sint.Z low < sint.Z high)%Z then
    0 <= sint.Z low ∧ sint.Z high < Z.of_nat (length values)
  else True.

Definition quick_sort_range_result
    (before after : list w64) (low high : w64) : Prop :=
  Permutation before after ∧
  same_outside_range low high before after ∧
  range_sorted_by_sint low high after.

Definition partition_no_overflow (values : list w64) (low high : w64) : Prop :=
  length_safe values ∧
  0 <= sint.Z low ∧
  sint.Z low <= sint.Z high ∧
  sint.Z high < Z.of_nat (length values) ∧
  go_int_safe (sint.Z high + 1).

Definition partition_result
    (before after : list w64) (low high pivot : w64) : Prop :=
  ∃ pivot_value,
    before !! Z.to_nat (sint.Z high) = Some pivot_value ∧
    after !! Z.to_nat (sint.Z pivot) = Some pivot_value ∧
    sint.Z low <= sint.Z pivot <= sint.Z high ∧
    Permutation before after ∧
    same_outside_range low high before after ∧
    (∀ i value,
      sint.Z low <= i < sint.Z pivot →
      after !! Z.to_nat i = Some value →
      sint.Z value < sint.Z pivot_value) ∧
    (∀ i value,
      sint.Z pivot < i <= sint.Z high →
      after !! Z.to_nat i = Some value →
      sint.Z pivot_value <= sint.Z value).

Lemma wp_add (a b : w64) :
  {{{ is_pkg_init basic ∗
      ⌜ go_int_safe (sint.Z a + sint.Z b) ⌝
  }}}
    @! basic.add #a #b
  {{{ (r : w64), RET #r;
      ⌜ (sint.Z r = sint.Z a + sint.Z b)%Z ⌝
  }}}.
Proof. Admitted.

Lemma wp_max (a b : w64) :
  {{{ is_pkg_init basic }}}
    @! basic.max #a #b
  {{{ (r : w64), RET #r;
      ⌜ ((sint.Z a > sint.Z b)%Z ∧ r = a) ∨
        ((sint.Z a <= sint.Z b)%Z ∧ r = b) ⌝
  }}}.
Proof. Admitted.

Lemma wp_factorial (n : w64) :
  {{{ is_pkg_init basic ∗
      ⌜ go_int_safe (sint.Z n + 1) ⌝ ∗
      ⌜ go_int_safe (factorial_result n) ⌝
  }}}
    @! basic.factorial #n
  {{{ (r : w64), RET #r;
      ⌜ (sint.Z r = factorial_result n)%Z ⌝
  }}}.
Proof. Admitted.

Lemma wp_sum (values : slice.t) (values_els : list w64) :
  {{{ is_pkg_init basic ∗
      values ↦* values_els ∗
      ⌜ length_safe values_els ⌝ ∗
      ⌜ sum_no_overflow values_els ⌝
  }}}
    @! basic.sum #values
  {{{ (r : w64), RET #r;
      values ↦* values_els ∗
      ⌜ (sint.Z r = sum_Z values_els)%Z ⌝
  }}}.
Proof. Admitted.

Lemma wp_reverseInts (values : slice.t) (values_els : list w64) :
  {{{ is_pkg_init basic ∗
      values ↦* values_els ∗
      ⌜ length_safe values_els ⌝
  }}}
    @! basic.reverseInts #values
  {{{ result, RET #result;
      values ↦* values_els ∗
      result ↦* rev values_els
  }}}.
Proof. Admitted.

Lemma wp_filterPositive (values : slice.t) (values_els : list w64) :
  {{{ is_pkg_init basic ∗
      values ↦* values_els ∗
      ⌜ length_safe values_els ⌝
  }}}
    @! basic.filterPositive #values
  {{{ result, RET #result;
      values ↦* values_els ∗
      result ↦* positive_ints values_els
  }}}.
Proof. Admitted.

Lemma wp_frequencies (values : slice.t) (values_els : list go_string) :
  {{{ is_pkg_init basic ∗
      values ↦* values_els ∗
      ⌜ length_safe values_els ⌝
  }}}
    @! basic.frequencies #values
  {{{ counts counts_els, RET #counts;
      values ↦* values_els ∗
      counts ↦$ counts_els ∗
      ⌜ frequency_map_spec values_els counts_els ⌝
  }}}.
Proof. Admitted.

Lemma wp_binarySearch (sorted : slice.t) (sorted_els : list w64) (target : w64) :
  {{{ is_pkg_init basic ∗
      sorted ↦* sorted_els ∗
      ⌜ length_safe sorted_els ⌝ ∗
      ⌜ sorted_by_sint sorted_els ⌝
  }}}
    @! basic.binarySearch #sorted #target
  {{{ (index : w64), RET #index;
      sorted ↦* sorted_els ∗
      ⌜ binary_search_result sorted_els target index ⌝
  }}}.
Proof. Admitted.

Lemma wp_mergeCounts
    (left right : loc) (left_els right_els : gmap go_string w64) :
  {{{ is_pkg_init basic ∗
      left ↦$ left_els ∗
      right ↦$ right_els ∗
      ⌜ merge_counts_no_overflow left_els right_els ⌝
  }}}
    @! basic.mergeCounts #left #right
  {{{ result result_els, RET #result;
      left ↦$ left_els ∗
      right ↦$ right_els ∗
      result ↦$ result_els ∗
      ⌜ merge_counts_spec left_els right_els result_els ⌝
  }}}.
Proof. Admitted.

Lemma wp_uniqueStrings (values : slice.t) (values_els : list go_string) :
  {{{ is_pkg_init basic ∗
      values ↦* values_els ∗
      ⌜ length_safe values_els ⌝
  }}}
    @! basic.uniqueStrings #values
  {{{ result, RET #result;
      values ↦* values_els ∗
      result ↦* unique_go_strings values_els
  }}}.
Proof. Admitted.

Lemma wp_selectionSort (values : slice.t) (values_els : list w64) :
  {{{ is_pkg_init basic ∗
      values ↦* values_els ∗
      ⌜ length_safe values_els ⌝
  }}}
    @! basic.selectionSort #values
  {{{ result result_els, RET #result;
      values ↦* values_els ∗
      result ↦* result_els ∗
      ⌜ sort_result values_els result_els ⌝
  }}}.
Proof. Admitted.

Lemma wp_insertionSort (values : slice.t) (values_els : list w64) :
  {{{ is_pkg_init basic ∗
      values ↦* values_els ∗
      ⌜ length_safe values_els ⌝
  }}}
    @! basic.insertionSort #values
  {{{ result result_els, RET #result;
      values ↦* values_els ∗
      result ↦* result_els ∗
      ⌜ sort_result values_els result_els ⌝
  }}}.
Proof. Admitted.

Lemma wp_quickSort (values : slice.t) (values_els : list w64) :
  {{{ is_pkg_init basic ∗
      values ↦* values_els ∗
      ⌜ length_safe values_els ⌝
  }}}
    @! basic.quickSort #values
  {{{ result result_els, RET #result;
      values ↦* values_els ∗
      result ↦* result_els ∗
      ⌜ sort_result values_els result_els ⌝
  }}}.
Proof. Admitted.

Lemma wp_quickSortRange (values : slice.t) (values_els : list w64) (low high : w64) :
  {{{ is_pkg_init basic ∗
      values ↦* values_els ∗
      ⌜ quick_sort_range_no_overflow values_els low high ⌝
  }}}
    @! basic.quickSortRange #values #low #high
  {{{ result_els, RET #();
      values ↦* result_els ∗
      ⌜ quick_sort_range_result values_els result_els low high ⌝
  }}}.
Proof. Admitted.

Lemma wp_partition (values : slice.t) (values_els : list w64) (low high : w64) :
  {{{ is_pkg_init basic ∗
      values ↦* values_els ∗
      ⌜ partition_no_overflow values_els low high ⌝
  }}}
    @! basic.partition #values #low #high
  {{{ (pivot : w64) result_els, RET #pivot;
      values ↦* result_els ∗
      ⌜ partition_result values_els result_els low high pivot ⌝
  }}}.
Proof. Admitted.

End proof.
