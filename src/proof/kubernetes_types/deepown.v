From New.proof Require Import prelude empty_ffi util.

(** Recursive ownership combinators for API views. Owned pointers, slices, and
    maps are represented by values, preserving nil versus allocated empty data. *)
Section deepown.
Context `{hG : !heapGS Σ} `{!ffi_semantics _ _}.
Context {sem : go.Semantics}.
Context {C V : Type} `{!ZeroVal C} `{!TypedPointsto (Σ:=Σ) C}.
Local Set Default Proof Using "All".

Definition deepown_ptr (P : C → V → dfrac → iProp Σ)
    (p : loc) (v : option V) dq : iProp Σ :=
  ⌜ p = null ↔ v = None ⌝ ∗
  match v with
  | None => True
  | Some v => ∃ c, p ↦{dq} c ∗ P c v dq
  end.

Lemma deepown_ptr_nil P dq : ⊢ deepown_ptr P null None dq.
Proof. rewrite /deepown_ptr. iSplit; [iPureIntro; tauto|done]. Qed.

Lemma deepown_ptr_persist P p v dq :
  (∀ c v, P c v dq ⊢ |==> P c v DfracDiscarded) →
  deepown_ptr P p v dq ⊢ |==> deepown_ptr P p v DfracDiscarded.
Proof.
  intros HP. rewrite /deepown_ptr. iIntros "[%Hnil Hv]".
  destruct v as [v|]; last by iFrame "%".
  iDestruct "Hv" as (c) "[Hp Hv]". iPersist "Hp".
  iMod (HP with "Hv") as "Hv". iModIntro. iFrame "%". iExists c. iFrame "# ∗".
Qed.

#[global] Instance deepown_ptr_persistent P p v
    `{!∀ c v, Persistent (P c v DfracDiscarded)} :
  Persistent (deepown_ptr P p v DfracDiscarded).
Proof. rewrite /deepown_ptr. destruct v; apply _. Qed.

Definition deepown_slice (P : C → V → dfrac → iProp Σ)
    (sl : slice.t) (vs : option (list V)) dq : iProp Σ :=
  ⌜ sl = slice.nil ↔ vs = None ⌝ ∗
  ∃ cs, sl ↦*{dq} cs ∗ own_slice_cap C sl dq ∗
    [∗ list] c;v ∈ cs;default [] vs, P c v dq.

Lemma deepown_slice_nil_iff P sl vs dq :
  deepown_slice P sl vs dq ⊢ ⌜ sl = slice.nil ↔ vs = None ⌝.
Proof. rewrite /deepown_slice. iIntros "[%Hnil _]". done. Qed.

(* Internal numeric buffers represent words, rather than API collections.
   big.Int.Set may copy an allocated empty buffer to nil. Own its complete
   backing storage while giving both empty representations the same value. *)
Definition deepown_slice_list (P : C → V → dfrac → iProp Σ)
    (sl : slice.t) (vs : list V) dq : iProp Σ :=
  ∃ cs, sl ↦*{dq} cs ∗ own_slice_cap C sl dq ∗ [∗ list] c;v ∈ cs;vs, P c v dq.

Lemma deepown_slice_cap_nil dq : ⊢ own_slice_cap C slice.nil dq.
Proof.
  rewrite own_slice_cap_unseal /own_slice_cap_def.
  iLeft. simpl. rewrite /slice_index_ref go.array_index_ref_0. done.
Qed.

Lemma deepown_slice_nil P dq : ⊢ deepown_slice P slice.nil None dq.
Proof.
  rewrite /deepown_slice. iSplit; first done.
  iExists []. rewrite big_sepL2_nil. iSplitL; first iApply own_slice_nil.
  iSplitL; [iApply deepown_slice_cap_nil|done].
Qed.

Lemma deepown_slice_list_nil P dq : ⊢ deepown_slice_list P slice.nil [] dq.
Proof.
  rewrite /deepown_slice_list. iExists []. rewrite big_sepL2_nil.
  iSplitL; first iApply own_slice_nil.
  iSplitL; [iApply deepown_slice_cap_nil|done].
Qed.

Lemma deepown_slice_list_persist P sl vs dq :
  (∀ c v, P c v dq ⊢ |==> P c v DfracDiscarded) →
  deepown_slice_list P sl vs dq ⊢ |==> deepown_slice_list P sl vs DfracDiscarded.
Proof.
  intros HP. rewrite /deepown_slice_list. iIntros "(%cs & Hsl & Hcap & Hvs)".
  iMod (own_slice_persist with "Hsl") as "Hsl". iPersist "Hcap".
  iMod (big_sepL2_persist P dq cs vs HP with "Hvs") as "Hvs".
  iModIntro. iExists cs. iFrame "# ∗".
Qed.

#[global] Instance deepown_slice_list_persistent P sl vs
    `{!∀ c v, Persistent (P c v DfracDiscarded)} :
  Persistent (deepown_slice_list P sl vs DfracDiscarded).
Proof. rewrite /deepown_slice_list. apply _. Qed.

Lemma deepown_slice_persist P sl vs dq :
  (∀ c v, P c v dq ⊢ |==> P c v DfracDiscarded) →
  deepown_slice P sl vs dq ⊢ |==> deepown_slice P sl vs DfracDiscarded.
Proof.
  intros HP. rewrite /deepown_slice. iIntros "(%Hnil & %cs & Hsl & Hcap & Hvs)".
  iMod (own_slice_persist with "Hsl") as "Hsl". iPersist "Hcap".
  iMod (big_sepL2_persist P dq cs (default [] vs) HP with "Hvs") as "Hvs".
  iModIntro. iFrame "%". iExists cs. iFrame "# ∗".
Qed.

#[global] Instance deepown_slice_persistent P sl vs
    `{!∀ c v, Persistent (P c v DfracDiscarded)} :
  Persistent (deepown_slice P sl vs DfracDiscarded).
Proof. rewrite /deepown_slice. apply _. Qed.

Definition deepown_map (P : C → V → dfrac → iProp Σ)
    (p : loc) (vs : option (gmap go_string V)) dq : iProp Σ :=
  ⌜ p = null ↔ vs = None ⌝ ∗
  match vs with
  | None => True
  | Some vs => ∃ cs, p ↦${dq} cs ∗ [∗ map] k↦c;v ∈ cs;vs, P c v dq
  end.

Lemma deepown_map_nil P dq : ⊢ deepown_map P null None dq.
Proof. rewrite /deepown_map. iSplit; [iPureIntro; tauto|done]. Qed.

Lemma deepown_map_persist P p vs dq :
  (∀ c v, P c v dq ⊢ |==> P c v DfracDiscarded) →
  deepown_map P p vs dq ⊢ |==> deepown_map P p vs DfracDiscarded.
Proof.
  intros HP. rewrite /deepown_map. iIntros "[%Hnil Hvs]".
  destruct vs as [vs|]; last by iFrame "%".
  iDestruct "Hvs" as (cs) "[Hm Hvs]".
  iMod (own_map_persist with "Hm") as "Hm".
  iAssert ([∗ map] k↦c;v ∈ cs;vs, |==> P c v DfracDiscarded)%I with "[Hvs]" as "Hvs".
  { iApply (big_sepM2_mono with "Hvs"). intros k c v _ _. apply HP. }
  iMod (big_sepM2_bupd with "Hvs") as "Hvs".
  iModIntro. iFrame "%". iExists cs. iFrame "# ∗".
Qed.

#[global] Instance deepown_map_persistent P p vs
    `{!∀ c v, Persistent (P c v DfracDiscarded)} :
  Persistent (deepown_map P p vs DfracDiscarded).
Proof. rewrite /deepown_map. destruct vs; apply _. Qed.

End deepown.
