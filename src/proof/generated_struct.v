From New.proof Require Import proof_prelude.
Require Import New.golang.theory.

(**
  Checked support for fast generated [IntoValTypedUnderlying] instances.

  The normal entry point is [scripts/optimize_generated_proofs.py]. For each
  selected generated struct, the optimizer reads the struct declaration and
  its [TypedPointsto] instance, then emits one [build_generated_struct_field]
  descriptor per field. It applies [generated_struct_into_val_typed] to those
  descriptors instead of running [solve_into_val_typed_struct] separately for
  every large struct.

  This file proves the allocation, load, and store programs once by induction
  over the descriptors. The generated instance only has to check each field's
  getter/setter step and the two record-reconstruction equalities. No proof is
  admitted.

  Run the optimizer directly with, for example:

    python3 scripts/optimize_generated_proofs.py \
      --optimize-into-val-typed PodSpec \
      src/generatedproof/k8s_io/api/core/v1.v

  [scripts/goose.sh] invokes the same rewrite after regeneration. The
  optimizer validates that descriptor order matches [TypedPointsto] and
  currently rejects structs containing embedded fields.
*)

Set Default Proof Using "Type".

Section generated_struct.
Context `{hG: heapGS Σ, !ffi_semantics _ _}.
Context {sem : go.Semantics}.

Record generated_struct_field (V : Type) (struct_ty : go.type) := {
  generated_field_name : go_string;
  generated_field_type : go.type;
  generated_field_value : Type;
  generated_field_zero : ZeroVal generated_field_value;
  generated_field_pointsto : TypedPointsto (Σ:=Σ) generated_field_value;
  generated_field_into_val :
    @IntoValTyped _ _ _ _ _ _ generated_field_value generated_field_type
      generated_field_zero generated_field_pointsto _;
  generated_field_get : V -> generated_field_value;
  generated_field_set : V -> generated_field_value -> V;
  generated_field_get_step v :
    ⟦StructFieldGet struct_ty generated_field_name, #v⟧ ⤳[under]
      #(generated_field_get v);
  generated_field_set_step v x :
    ⟦StructFieldSet struct_ty generated_field_name, (#v, #x)⟧ ⤳[under]
      #(generated_field_set v x);
}.

Arguments generated_field_name {_ _} _.
Arguments generated_field_type {_ _} _.
Arguments generated_field_value {_ _} _.
Arguments generated_field_zero {_ _} _.
Arguments generated_field_pointsto {_ _} _.
Arguments generated_field_into_val {_ _} _.
Arguments generated_field_get {_ _} _ _.
Arguments generated_field_set {_ _} _ _ _.
Arguments generated_field_get_step {_ _} _ _.
Arguments generated_field_set_step {_ _} _ _ _.

#[local] Existing Instance generated_field_zero.
#[local] Existing Instance generated_field_pointsto.
#[local] Existing Instance generated_field_into_val.
#[local] Existing Instance generated_field_get_step.
#[local] Existing Instance generated_field_set_step.

Definition build_generated_struct_field {V struct_ty A}
    (name : go_string) (ty : go.type)
    `{!ZeroVal A} `{!TypedPointsto A} `{!IntoValTyped A ty}
    (get : V -> A) (set : V -> A -> V)
    (get_step : forall v,
      ⟦StructFieldGet struct_ty name, #v⟧ ⤳[under] #(get v))
    (set_step : forall v x,
      ⟦StructFieldSet struct_ty name, (#v, #x)⟧ ⤳[under] #(set v x)) :
  generated_struct_field V struct_ty :=
  {|
    generated_field_name := name;
    generated_field_type := ty;
    generated_field_value := A;
    generated_field_zero := ZeroVal0;
    generated_field_pointsto := TypedPointsto0;
    generated_field_into_val := IntoValTyped0;
    generated_field_get := get;
    generated_field_set := set;
    generated_field_get_step := get_step;
    generated_field_set_step := set_step;
  |}.

#[local] Instance generated_field_get_pure {V struct_ty}
    (field : generated_struct_field V struct_ty) v :
  PureWp True
    (StructFieldGet struct_ty (generated_field_name field) #v)
    #(generated_field_get field v).
Proof.
  apply pure_wp_go_step_det.
  exact (go.tagged_steps under _ _ _ (generated_field_get_step field v)).
Qed.

#[local] Instance generated_field_set_pure {V struct_ty}
    (field : generated_struct_field V struct_ty) v x :
  PureWp True
    (StructFieldSet struct_ty (generated_field_name field) (#v, #x)%V)
    #(generated_field_set field v x).
Proof.
  apply pure_wp_go_step_det.
  exact (go.tagged_steps under _ _ _ (generated_field_set_step field v x)).
Qed.

#[local] Instance generated_field_ref_pure {V struct_ty}
    `{!ZeroVal V} `{!TypeRepr struct_ty V}
    (field : generated_struct_field V struct_ty) l :
  PureWp True
    (StructFieldRef struct_ty (generated_field_name field) #l)
    #(struct_field_ref V (generated_field_name field) l).
Proof.
  apply pure_wp_go_step_det.
  eapply (go.tagged_steps under).
  tc_solve.
Qed.

Definition generated_field_decl {V struct_ty}
    (field : generated_struct_field V struct_ty) : go.field_decl :=
  go.FieldDecl (generated_field_name field) (generated_field_type field).

Definition generated_field_own {V struct_ty}
    (field : generated_struct_field V struct_ty) l (v : V) dq : iProp Σ :=
  @typed_pointsto Σ
    (generated_field_value field)
    (generated_field_pointsto field)
    (struct_field_ref V (generated_field_name field) l)
    (generated_field_get field v) dq.

Fixpoint generated_fields_own {V struct_ty}
    (fields : list (generated_struct_field V struct_ty)) (l : loc) (v : V)
    (dq : dfrac) : iProp Σ :=
  match fields with
  | [] => True
  | field :: fields =>
      generated_field_own field l v dq ∗
      generated_fields_own fields l v dq
  end%I.

Fixpoint generated_fields_decl {V struct_ty}
    (fields : list (generated_struct_field V struct_ty)) : list go.field_decl :=
  match fields with
  | [] => []
  | field :: fields => generated_field_decl field :: generated_fields_decl fields
  end.

Fixpoint generated_fields_set {V struct_ty}
    (fields : list (generated_struct_field V struct_ty)) (dst src : V) : V :=
  match fields with
  | [] => dst
  | field :: fields =>
      generated_fields_set fields
        (generated_field_set field dst (generated_field_get field src)) src
  end.

Definition generated_field_alloc {V struct_ty}
    (field : generated_struct_field V struct_ty) (l : loc) (v : V)
    (rest : expr) : expr :=
  (let: "l_field" :=
     GoAlloc (generated_field_type field)
       (StructFieldGet struct_ty (generated_field_name field) #v) in
   (if: ("l_field" =⟨go.PointerType (generated_field_type field)⟩
            (StructFieldRef struct_ty (generated_field_name field) #l))
    then #() else AngelicExit #());;
   rest)%E.

Definition generated_fields_alloc {V struct_ty}
    (fields : list (generated_struct_field V struct_ty)) (l : loc) (v : V) : expr :=
  foldr (fun field rest => generated_field_alloc field l v rest) #() fields.

Definition generated_fields_load_acc {V struct_ty}
    (fields : list (generated_struct_field V struct_ty)) (l : loc) (acc : expr) : expr :=
  foldl (fun acc field =>
    StructFieldSet struct_ty (generated_field_name field)
      (acc, GoLoad (generated_field_type field)
        (StructFieldRef struct_ty (generated_field_name field) #l))%E)
    acc fields.

Definition generated_fields_load {V struct_ty}
    (fields : list (generated_struct_field V struct_ty)) (l : loc) (dst : V) : expr :=
  generated_fields_load_acc fields l #dst.

Definition generated_fields_store {V struct_ty}
    (fields : list (generated_struct_field V struct_ty)) (l : loc) (v : V) : expr :=
  foldl (fun acc field =>
    (acc;;
     GoStore (generated_field_type field)
       (StructFieldRef struct_ty (generated_field_name field) #l,
        StructFieldGet struct_ty (generated_field_name field) #v))%E)
    #() fields.

Definition generated_decls_alloc {V}
    (struct_ty : go.type) (decls : list go.field_decl) (l : loc) (v : V) : expr :=
  foldr (fun fd rest =>
    let '(field_name, field_type) :=
      match fd with
      | go.FieldDecl name ty => (name, ty)
      | go.EmbeddedField name ty => (name, ty)
      end in
    (let: "l_field" :=
       GoAlloc field_type (StructFieldGet struct_ty field_name #v) in
     (if: ("l_field" =⟨go.PointerType field_type⟩
              (StructFieldRef struct_ty field_name #l))
      then #() else AngelicExit #());;
     rest)%E) #() decls.

Definition generated_decls_alloc_var {V}
    (struct_ty : go.type) (decls : list go.field_decl) (v : V) : expr :=
  foldr (fun fd rest =>
    let '(field_name, field_type) :=
      match fd with
      | go.FieldDecl name ty => (name, ty)
      | go.EmbeddedField name ty => (name, ty)
      end in
    (let: "l_field" :=
       GoAlloc field_type (StructFieldGet struct_ty field_name #v) in
     (if: ("l_field" =⟨go.PointerType field_type⟩
              (StructFieldRef struct_ty field_name "l"))
      then #() else AngelicExit #());;
     rest)%E) #() decls.

Definition generated_decls_load_acc
    (struct_ty : go.type) (decls : list go.field_decl) (l : loc) (acc : expr) : expr :=
  foldl (fun acc fd =>
    let '(field_name, field_type) :=
      match fd with
      | go.FieldDecl name ty => (name, ty)
      | go.EmbeddedField name ty => (name, ty)
      end in
    StructFieldSet struct_ty field_name
      (acc, GoLoad field_type (StructFieldRef struct_ty field_name #l))%E)
    acc decls.

Definition generated_decls_load {V}
    (struct_ty : go.type) (decls : list go.field_decl) (l : loc) (dst : V) : expr :=
  generated_decls_load_acc struct_ty decls l #dst.

Definition generated_decl_store {V}
    (struct_ty : go.type) (l : loc) (v : V) (fd : go.field_decl) : expr :=
  let '(field_name, field_type) :=
    match fd with
    | go.FieldDecl name ty => pair name ty
    | go.EmbeddedField name ty => pair name ty
    end in
  (GoStore field_type
    (StructFieldRef struct_ty field_name #l,
     StructFieldGet struct_ty field_name #v))%E.

Definition generated_decls_store {V}
    (struct_ty : go.type) (decls : list go.field_decl) (l : loc) (v : V) : expr :=
  foldl (fun acc fd => (acc;; generated_decl_store struct_ty l v fd)%E)
    #() decls.

Lemma generated_decls_alloc_eq {V struct_ty}
    (fields : list (generated_struct_field V struct_ty)) l (v : V) :
  generated_decls_alloc struct_ty (generated_fields_decl fields) l v =
    generated_fields_alloc fields l v.
Proof.
  induction fields as [|field fields IH]; first done.
  change (generated_field_alloc field l v
            (generated_decls_alloc struct_ty (generated_fields_decl fields) l v) =
          generated_field_alloc field l v (generated_fields_alloc fields l v)).
  rewrite IH. done.
Qed.

Lemma generated_decls_alloc_var_subst {V}
    (struct_ty : go.type) (decls : list go.field_decl) l (v : V) :
  subst "l" #l (generated_decls_alloc_var struct_ty decls v) =
    generated_decls_alloc struct_ty decls l v.
Proof.
  induction decls as [|decl decls IH]; first done.
  destruct decl.
  all: rewrite /generated_decls_alloc_var /generated_decls_alloc /=.
  all: fold (generated_decls_alloc_var struct_ty decls v).
  all: fold (generated_decls_alloc struct_ty decls l v).
  all: rewrite IH.
  all: reflexivity.
Qed.

Lemma generated_decls_load_eq {V struct_ty}
    (fields : list (generated_struct_field V struct_ty)) l (dst : V) :
  generated_decls_load struct_ty (generated_fields_decl fields) l dst =
  generated_fields_load fields l dst.
Proof.
  rewrite /generated_decls_load /generated_fields_load
    /generated_decls_load_acc /generated_fields_load_acc.
  generalize (Val #dst) as acc.
  induction fields as [|field fields IH]; intros acc; first done.
  rewrite /= /generated_field_decl. apply IH.
Qed.

Lemma generated_decls_load_acc_eq {V struct_ty}
    (fields : list (generated_struct_field V struct_ty)) l (acc : expr) :
  generated_decls_load_acc struct_ty (generated_fields_decl fields) l acc =
    generated_fields_load_acc fields l acc.
Proof.
  rewrite /generated_decls_load_acc /generated_fields_load_acc.
  revert acc.
  induction fields as [|field fields IH]; intros acc; first done.
  rewrite /= /generated_field_decl. apply IH.
Qed.

Lemma generated_decls_store_eq {V struct_ty}
    (fields : list (generated_struct_field V struct_ty)) l (v : V) :
  generated_decls_store struct_ty (generated_fields_decl fields) l v =
  generated_fields_store fields l v.
Proof.
  rewrite /generated_decls_store /generated_fields_store.
  generalize (Val #()) as acc.
  induction fields as [|field fields IH]; intros acc; first done.
  rewrite /= /generated_field_decl. apply IH.
Qed.

Lemma generated_fields_alloc_subst {V struct_ty}
    (fields : list (generated_struct_field V struct_ty)) l (v : V) (x : val) :
  subst "l_field" x (generated_fields_alloc fields l v) =
    generated_fields_alloc fields l v.
Proof.
  induction fields as [|field fields IH]; first done.
  rewrite /generated_fields_alloc /= /generated_field_alloc /=.
  reflexivity.
Qed.

Lemma generated_fields_set_app {V struct_ty}
    (fields1 fields2 : list (generated_struct_field V struct_ty)) dst src :
  generated_fields_set (fields1 ++ fields2) dst src =
    generated_fields_set fields2 (generated_fields_set fields1 dst src) src.
Proof.
  revert dst.
  induction fields1 as [|field fields1 IH]; intros dst; first done.
  simpl. apply IH.
Qed.

Lemma generated_fields_own_app {V struct_ty}
    (fields1 fields2 : list (generated_struct_field V struct_ty)) l (v : V) dq :
  generated_fields_own (fields1 ++ fields2) l v dq ⊣⊢
    generated_fields_own fields1 l v dq ∗ generated_fields_own fields2 l v dq.
Proof.
  induction fields1 as [|field fields1 IH]; simpl.
  - iSplit.
    + iIntros "H". iSplit; first done. iExact "H".
    + iIntros "[_ H]". iExact "H".
  - rewrite IH. iSplit.
    + iIntros "[Hfield [Hfields Hrest]]". iFrame.
    + iIntros "[[Hfield Hfields] Hrest]". iFrame.
Qed.

Lemma wp_generated_fields_alloc {V struct_ty} `{!ZeroVal V} `{!TypeRepr struct_ty V}
    (fields : list (generated_struct_field V struct_ty)) l (v : V) s E :
  ⊢ WP generated_fields_alloc fields l v @ s; E
      {{ _, generated_fields_own fields l v 1 }}.
Proof.
  induction fields as [|field fields IH].
  { iStartProof. rewrite /generated_fields_alloc /=. iApply wp_value. done. }
  iStartProof.
  rewrite /generated_fields_alloc /= /generated_field_alloc.
  let field_zero := fresh "field_zero" in
  let field_pointsto := fresh "field_pointsto" in
  let field_into_val := fresh "field_into_val" in
  pose (field_zero := generated_field_zero field);
  pose (field_pointsto := generated_field_pointsto field);
  pose (field_into_val := generated_field_into_val field).
  wp_bind.
  wp_pure.
  wp_pure.
  wp_alloc field_l as "Hfield".
  destruct (decide
    (field_l = struct_field_ref V (generated_field_name field) l)) as [->|Hne].
  - wp_auto. wp_pures. rewrite bool_decide_true; last done. wp_pures.
    wp_apply (wp_wand with "[]").
    { fold (generated_fields_alloc (V:=V) (struct_ty:=struct_ty) fields l v).
      rewrite generated_fields_alloc_subst. iApply IH. }
    iIntros (ret) "Hfields". iFrame.
  - wp_auto. wp_pures. rewrite bool_decide_false; last done. wp_pures.
    wp_apply wp_AngelicExit.
Qed.

Lemma wp_generated_fields_load {V struct_ty} `{!ZeroVal V} `{!TypeRepr struct_ty V}
    (fields : list (generated_struct_field V struct_ty)) l (dst src : V) dq s E :
  generated_fields_own fields l src dq -∗
  WP generated_fields_load fields l dst @ s; E
    {{ ret, ⌜ ret = #(generated_fields_set fields dst src) ⌝ ∗
             generated_fields_own fields l src dq }}.
Proof.
  revert dst.
  induction fields as [|field fields IH] using rev_ind.
  { iIntros (dst) "_". rewrite /generated_fields_load /=.
    iApply wp_value. iSplit; first done. done. }
  iIntros (dst) "H".
  iEval (rewrite generated_fields_own_app /=) in "H".
  iDestruct "H" as "[Hfields [Hfield _]]".
  rewrite /generated_fields_load /generated_fields_load_acc foldl_app /=.
  wp_apply (wp_wand with "[Hfields]").
  { fold (generated_fields_load (V:=V) (struct_ty:=struct_ty) fields l dst).
    iApply (IH with "Hfields"). }
  iIntros (ret) "[-> Hfields]".
  let field_zero := fresh "field_zero" in
  let field_pointsto := fresh "field_pointsto" in
  let field_into_val := fresh "field_into_val" in
  pose (field_zero := generated_field_zero field);
  pose (field_pointsto := generated_field_pointsto field);
  pose (field_into_val := generated_field_into_val field).
  wp_auto. wp_pures.
  iSplit.
  - iPureIntro. rewrite generated_fields_set_app /=. done.
  - rewrite generated_fields_own_app /=. iFrame.
Qed.

Lemma wp_generated_fields_load_acc {V struct_ty}
    `{!ZeroVal V} `{!TypeRepr struct_ty V}
    (fields : list (generated_struct_field V struct_ty)) l
    (init : expr) (dst src : V) dq s E :
  WP init @ s; E {{ ret, ⌜ ret = #dst ⌝ }} -∗
  generated_fields_own fields l src dq -∗
  WP generated_fields_load_acc fields l init @ s; E
    {{ ret, ⌜ ret = #(generated_fields_set fields dst src) ⌝ ∗
             generated_fields_own fields l src dq }}.
Proof.
  induction fields as [|field fields IH] using rev_ind.
  { iIntros "Hinit _". rewrite /generated_fields_load_acc /=.
    iApply (wp_wand with "Hinit").
    iIntros (ret) "->". iSplit; first done. done. }
  iIntros "Hinit H".
  iEval (rewrite generated_fields_own_app /=) in "H".
  iDestruct "H" as "[Hfields [Hfield _]]".
  rewrite /generated_fields_load_acc foldl_app /=.
  wp_apply (wp_wand with "[Hinit Hfields]").
  { iApply (IH with "Hinit Hfields"). }
  iIntros (ret) "[-> Hfields]".
  let field_zero := fresh "field_zero" in
  let field_pointsto := fresh "field_pointsto" in
  let field_into_val := fresh "field_into_val" in
  pose (field_zero := generated_field_zero field);
  pose (field_pointsto := generated_field_pointsto field);
  pose (field_into_val := generated_field_into_val field).
  wp_auto. wp_pures.
  iSplit.
  - iPureIntro. rewrite generated_fields_set_app /=. done.
  - rewrite generated_fields_own_app /=. iFrame.
Qed.

Lemma wp_generated_fields_store {V struct_ty} `{!ZeroVal V} `{!TypeRepr struct_ty V}
    (fields : list (generated_struct_field V struct_ty)) l (old new : V) s E :
  generated_fields_own fields l old 1 -∗
  WP generated_fields_store fields l new @ s; E
    {{ ret, ⌜ ret = #(tt) ⌝ ∗ generated_fields_own fields l new 1 }}.
Proof.
  induction fields as [|field fields IH] using rev_ind.
  { iIntros "_". rewrite /generated_fields_store /=.
    iApply wp_value. iSplit; first done. done. }
  iIntros "H".
  iEval (rewrite generated_fields_own_app /=) in "H".
  iDestruct "H" as "[Hfields [Hfield _]]".
  rewrite /generated_fields_store foldl_app /=.
  wp_apply (wp_wand with "[Hfields]").
  { fold (generated_fields_store (V:=V) (struct_ty:=struct_ty) fields l new).
    iApply (IH with "Hfields"). }
  iIntros (ret) "[-> Hfields]".
  let field_zero := fresh "field_zero" in
  let field_pointsto := fresh "field_pointsto" in
  let field_into_val := fresh "field_into_val" in
  pose (field_zero := generated_field_zero field);
  pose (field_pointsto := generated_field_pointsto field);
  pose (field_into_val := generated_field_into_val field).
  wp_auto. wp_pures.
  iSplit; first done.
  rewrite generated_fields_own_app /=. iFrame.
Qed.

Lemma generated_struct_into_val_typed {V fds}
    `{!ZeroVal V} `{!TypedPointsto V}
    (fields : list (generated_struct_field V (go.StructType fds)))
    `{fields_unfold : !fds =→ generated_fields_decl fields}
    `{struct_repr : !go.TypeReprUnderlying (go.StructType fds) V}
    (Hown : forall l v dq,
      typed_pointsto_def l v dq ⊣⊢ generated_fields_own fields l v dq)
    (Hset : forall v, generated_fields_set fields (zero_val V) v = v) :
  IntoValTypedUnderlying V (go.StructType fds).
Proof.
  pose proof (go.tagged_steps internal) as Hint.
  constructor; intros.
  - iIntros "_ HΦ". wp_pure. clear Hint.
    wp_apply wp_GoPrealloc. iIntros (l) "%Hnotnull".
    wp_pures.
    fold (generated_decls_alloc_var (go.StructType fds)
      (generated_fields_decl fields) v).
    rewrite generated_decls_alloc_var_subst generated_decls_alloc_eq.
    wp_bind (generated_fields_alloc fields l v).
    iApply (wp_wand with "[]").
    { iApply wp_generated_fields_alloc. }
    iIntros (ret) "Hfields".
    wp_pures. iApply "HΦ".
    iApply typed_pointsto_combine; first done.
    rewrite Hown. iExact "Hfields".
  - iIntros "Hl HΦ".
    iDestruct (typed_pointsto_not_null with "Hl") as %Hnotnull.
    iDestruct (typed_pointsto_split with "Hl") as "Hfields".
    iEval (rewrite Hown) in "Hfields".
    wp_pure.
    fold (generated_decls_load_acc (go.StructType fds)
      (generated_fields_decl fields) l (GoZeroVal (go.StructType fds) #())).
    rewrite generated_decls_load_acc_eq.
    iApply (wp_wand with "[Hfields]").
    { iApply (wp_generated_fields_load_acc fields l
        (GoZeroVal (go.StructType fds) #()) (zero_val V) v dq with "[] Hfields").
      wp_pure. wp_pure. done. }
    clear Hint. iIntros (ret) "[-> Hfields]". rewrite Hset.
    iApply "HΦ". iApply typed_pointsto_combine; first done.
    rewrite Hown. iExact "Hfields".
  - iIntros "Hl HΦ".
    iDestruct (typed_pointsto_not_null with "Hl") as %Hnotnull.
    iDestruct (typed_pointsto_split with "Hl") as "Hfields".
    iEval (rewrite Hown) in "Hfields".
    wp_pure. clear Hint.
    lazymatch goal with
    | |- environments.envs_entails ?Delta _ =>
        change (environments.envs_entails Delta
          (WP (generated_decls_store (go.StructType fds)
            (generated_fields_decl fields) l w) @ s; E {{ ret, Φ ret }})%I)
    end.
    rewrite generated_decls_store_eq.
    iApply (wp_wand with "[Hfields]").
    { iApply (wp_generated_fields_store fields l v w with "Hfields"). }
    iIntros (ret) "[-> Hfields]". iApply "HΦ".
    iApply typed_pointsto_combine; first done.
    rewrite Hown. iExact "Hfields".
  - exact _.
Qed.

End generated_struct.
