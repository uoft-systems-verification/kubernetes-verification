From New.proof Require Import prelude empty_ffi.
From New.proof.map Require Import for_range.
From New.proof.k8s_io.kubernetes.pkg.util Require Export labels_init.

Section proof.
Context `{hG: !heapGS Σ} `{!ffi_semantics _ _}.
Context {sem : go.Semantics} {package_sem : labels.Assumptions}.
Collection W := sem + package_sem.
Local Set Default Proof Using "All".

(* Ownership of a possibly-nil map[string]string argument.  ObjectMetaV models
   an absent label/annotation map as None, and Go ranges over a nil map without
   faulting, so CloneAndAddLabel must accept both. *)
Definition labels_opt_own (l : loc)
    (m_o : option (gmap go_string go_string)) dq : iProp Σ :=
  match m_o with
  | Some m => l ↦${dq} m
  | None => ⌜ l = null ⌝
  end.

(* CloneAndAddLabel returns a fresh map holding [existing] plus one binding.
   [existing] is only read, and a nil map ranges as empty, hence [default ∅].
   The result is fully owned: it is a map literal the callee just built. With an
   empty key it would return [existing] itself instead; the only caller passes
   the non-empty pod-template-hash key, so the spec rules that case out. *)
Lemma wp_CloneAndAddLabel existing_l (existing : option (gmap go_string go_string))
    (key value : go_string) dq :
  {{{ is_pkg_init labels ∗
      "Hexisting" ∷ labels_opt_own existing_l existing dq ∗
      "%Hkey" ∷ ⌜ key ≠ ""%go ⌝
  }}}
    @! labels.CloneAndAddLabel #existing_l #key #value
  {{{ (result_l : loc), RET #result_l;
      labels_opt_own existing_l existing dq ∗
      result_l ↦$ (<[key := value]> (default ∅ existing))
  }}}.
Proof.
  wp_start as "H". iNamed "H". wp_auto.
  rewrite bool_decide_eq_false_2 //. wp_auto.
  wp_apply wp_map_make1. iIntros (result_l) "Hresult".
  wp_auto.
  destruct existing as [m|].
  - (* The copy loop fills [result] with the map_prefix of the keys seen so far. *)
    wp_apply (wp_map_for_range_return_func (key_type:=go.string)
      (λ (keys : list go_string) i,
        ∃ (last_value last_key : go_string),
          "value" ∷ value_ptr ↦ last_value ∗
          "key" ∷ key_ptr ↦ last_key ∗
          "newLabels" ∷ newLabels_ptr ↦ result_l ∗
          "Hresult" ∷ result_l ↦$ map_prefix keys i m)%I
      with "Hexisting").
    { done. }
    iIntros (keys) "%Hkeys".
    iSplitL "value key newLabels Hresult".
    { iExists ""%go, ""%go. iFrame. rewrite map_prefix_empty. iFrame. }
    iSplitL "".
    { iModIntro. iIntros (i k0 v0) "%Hiter Hloop".
      destruct Hkeys as [Hkeys_dom [Hkeys_len Hkeys_nodup]].
      destruct Hiter as [Hi_bounds [Hkey_lookup Hvalue_lookup]].
      destruct Hi_bounds as [Hi_nonneg Hi_upper].
      iDestruct "Hloop" as (last_value last_key) "(value & key & newLabels & Hresult)".
      wp_pures. simpl subst'. wp_auto.
      wp_apply (wp_map_insert (K:=go_string) (V:=go_string)
        go.string result_l (map_prefix keys i m) k0 v0 with "Hresult") as "Hresult".
      iRight. iSplit; [done|].
      iExists v0, k0. iFrame.
      rewrite -map_prefix_insert; done. }
    iIntros "Hexisting Hloop".
    iDestruct "Hloop" as (last_value last_key) "(value & key & newLabels & Hresult)".
    destruct Hkeys as [Hkeys_dom [Hkeys_len Hkeys_nodup]].
    rewrite (map_prefix_all keys m Hkeys_dom Hkeys_len).
    wp_auto.
    wp_apply (wp_map_insert (K:=go_string) (V:=go_string)
      go.string result_l m key value with "Hresult") as "Hresult".
    iApply ("HΦ" $! result_l). iFrame.
  - (* A nil source map ranges zero times, leaving [result] empty. *)
    iDestruct "Hexisting" as %->.
    wp_apply (wp_map_for_range_nil go.string go.string).
    wp_apply (wp_map_insert (K:=go_string) (V:=go_string)
      go.string result_l ∅ key value with "Hresult") as "Hresult".
    iApply ("HΦ" $! result_l). iFrame. done.
Qed.

End proof.
