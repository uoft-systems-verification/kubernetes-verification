From New.proof Require Import wp_keep.
From New.proof Require Import prelude empty_ffi util.
From New.proof Require Export sort.
From New.proof.map Require Import for_range.
From New.object_specs Require Export prelude.
From New.proof.k8s_io.api.core Require Export v1.
From New.proof.k8s_io.kubernetes.pkg Require Export controller_init.
From New.proof.k8s_io.apimachinery.pkg.api Require Import meta.
From New.proof.k8s_io.apimachinery.pkg.apis.meta Require Import v1.
From New.proof.k8s_io.kubernetes.pkg.api.v1 Require Import pod.

Local Transparent ObjectMetaV.deepown ObjectMetaView.ObjectMetaV.deepown.
Local Opaque TimeV.deepown TimeView.TimeV.deepown TimeView.LocationV.deepown.

(* Collect transient allocations from imports before checking large program proofs. *)
Optimize Heap.

Section proof.
Context `{hG: !heapGS Σ} `{!ffi_semantics _ _}.
Context {sem : go.Semantics}
  {package_sem : controller.Assumptions}
  {apps_v1_sem : code.k8s_io.api.apps.v1.v1.Assumptions}
  {controller_core_v1_sem : core_v1.Assumptions}
  {controller_meta_v1_sem : meta_v1.Assumptions}.
Collection W := sem + package_sem.
Local Set Default Proof Using "All".

#[local] Existing Instance controller_core_v1_sem.
#[local] Existing Instance controller_meta_v1_sem.

#[local] Instance controller_labels_sem : labels.Assumptions :=
  controller.import_labels_Assumption.

(* Literal construction converts the named label map to its underlying map.
   Fix both underlying types instead of searching for intermediate types. *)
#[local] Instance labels_set_to_map (l : loc) :
  PureWp True (Convert labels.Set' (go.MapType go.string go.string) #l) #l | 0.
Proof using package_sem.
  apply pure_wp_go_step_det.
  eapply (go.convert_underlying (from_under:=go.MapType go.string go.string)
    (to_under:=go.MapType go.string go.string)).
  apply go.is_convert_underlying_same.
Qed.

(** An abstract sortable element keeps a pod, its pointer, and its rank
    together, matching the coupled swaps performed by [ActivePodsWithRanks]. *)
Record active_pod_with_rank := {
  active_pod_ptr : loc;
  active_pod_value : PodV.t;
  active_pod_rank : w64;
}.

Fixpoint active_pods_with_ranks_entries
    (ptrs : list loc) (pods : list PodV.t) (ranks : list w64) : list active_pod_with_rank :=
  match ptrs, pods, ranks with
  | ptr :: ptrs, pod :: pods, rank :: ranks =>
      {| active_pod_ptr := ptr; active_pod_value := pod; active_pod_rank := rank |} ::
        active_pods_with_ranks_entries ptrs pods ranks
  | _, _, _ => []
  end.

Lemma active_pods_with_ranks_entries_ptrs ptrs pods ranks :
  length ptrs = length pods → length ptrs = length ranks →
  active_pod_ptr <$> active_pods_with_ranks_entries ptrs pods ranks = ptrs.
Proof.
  revert pods ranks. induction ptrs as [|ptr ptrs IH]; intros [|pod pods] [|rank ranks];
    simpl; intros; try congruence.
  f_equal. apply IH; lia.
Qed.

Lemma active_pods_with_ranks_entries_pods ptrs pods ranks :
  length ptrs = length pods → length ptrs = length ranks →
  active_pod_value <$> active_pods_with_ranks_entries ptrs pods ranks = pods.
Proof.
  revert pods ranks. induction ptrs as [|ptr ptrs IH]; intros [|pod pods] [|rank ranks];
    simpl; intros; try congruence.
  f_equal. apply IH; lia.
Qed.

Lemma active_pods_with_ranks_entries_ranks ptrs pods ranks :
  length ptrs = length pods → length ptrs = length ranks →
  active_pod_rank <$> active_pods_with_ranks_entries ptrs pods ranks = ranks.
Proof.
  revert pods ranks. induction ptrs as [|ptr ptrs IH]; intros [|pod pods] [|rank ranks];
    simpl; intros; try congruence.
  f_equal. apply IH; lia.
Qed.

Definition active_pods_with_ranks_contents dq
    (ranked : controller.ActivePodsWithRanks.t) (entries : list active_pod_with_rank) : iProp Σ :=
  ranked.(controller.ActivePodsWithRanks.Pods') ↦* (active_pod_ptr <$> entries) ∗
  ranked.(controller.ActivePodsWithRanks.Rank') ↦* (active_pod_rank <$> entries) ∗
  ([∗ list] ptr;pod ∈ (active_pod_ptr <$> entries);(active_pod_value <$> entries),
    PodV.deepown_l ptr pod dq).

(** The model API omits these Kubernetes method bodies, so their method-level
    contracts are the controller-specific trusted boundary. *)
Lemma wp_active_pods_with_ranks_len dq ranked entries :
  {{{ active_pods_with_ranks_contents dq ranked entries }}}
    ranked @! controller.ActivePodsWithRanks @! "Len" #()
  {{{ (n : w64), RET #n; active_pods_with_ranks_contents dq ranked entries ∗
      ⌜ sint.nat n = length entries ∧ 0 ≤ sint.Z n ⌝
  }}}.
Proof. Admitted.

Lemma wp_active_pods_with_ranks_less dq ranked entries (i j : w64) :
  0 ≤ sint.Z i < length entries → 0 ≤ sint.Z j < length entries →
  {{{ active_pods_with_ranks_contents dq ranked entries }}}
    ranked @! controller.ActivePodsWithRanks @! "Less" #i #j
  {{{ (b : bool), RET #b; active_pods_with_ranks_contents dq ranked entries }}}.
Proof. Admitted.

Lemma wp_active_pods_with_ranks_swap dq ranked entries (i j : w64) :
  0 ≤ sint.Z i < length entries → 0 ≤ sint.Z j < length entries →
  {{{ active_pods_with_ranks_contents dq ranked entries }}}
    ranked @! controller.ActivePodsWithRanks @! "Swap" #i #j
  {{{ RET #(); active_pods_with_ranks_contents dq ranked
      (list_swap entries (sint.nat i) (sint.nat j))
  }}}.
Proof. Admitted.

#[global] Instance active_pods_with_ranks_sort_interface dq :
  SortInterfaceSpec controller.ActivePodsWithRanks
    (active_pods_with_ranks_contents dq).
Proof.
  constructor.
  - apply wp_active_pods_with_ranks_len.
  - apply wp_active_pods_with_ranks_less.
  - apply wp_active_pods_with_ranks_swap.
Qed.

(** [ReplicaSetsByCreationTimestamp.Less]: older first, ties broken by name. *)
Definition rs_creation_time (rs : ReplicaSetV.t) : TimeView.TimeV.t :=
  rs.(ReplicaSetV.ObjectMeta').(ObjectMetaV.CreationTimestamp').(MetaTimeView.TimeV.Time').

Definition rs_name (rs : ReplicaSetV.t) : go_string :=
  rs.(ReplicaSetV.ObjectMeta').(ObjectMetaV.Name').

Definition rs_created_before (a b : ReplicaSetV.t) : Prop :=
  if decide (time_equal (rs_creation_time a) (rs_creation_time b)) then
    go.go_string_lt (rs_name a) (rs_name b)
  else time_before (rs_creation_time a) (rs_creation_time b).

#[global] Instance rs_created_before_dec : RelDecision rs_created_before.
Proof. intros a b. rewrite /rs_created_before. case_decide; apply _. Defined.

(** Go compares two times by their monotonic readings when both have one and
    by wall clock otherwise, so [Before] is a strict weak order only on a set
    of times that all compare the same way. Times from [time.Now] all carry a
    monotonic reading; times decoded from the API server carry none. *)
Definition creation_times_comparable (rss : list ReplicaSetV.t) : Prop :=
  (∀ a b, a ∈ rss → b ∈ rss → time_both_monotonic (rs_creation_time a) (rs_creation_time b)) ∨
  (∀ a b, a ∈ rss → b ∈ rss → ¬ time_both_monotonic (rs_creation_time a) (rs_creation_time b)).

(* The sorted elements keep each pointer with its ReplicaSet. *)
Definition rs_entry_created_before (a b : loc * ReplicaSetV.t) : Prop :=
  rs_created_before a.2 b.2.

#[global] Instance rs_entry_created_before_dec : RelDecision rs_entry_created_before.
Proof. intros a b. rewrite /rs_entry_created_before. apply _. Defined.

(* On comparable times, [rs_created_before] is the lexicographic order on a
   numeric key ([ext] when both times are monotonic, (seconds, nanoseconds)
   otherwise) followed by the name, so it is a strict weak order. *)
Lemma rs_created_before_strict_weak_order (entries : list (loc * ReplicaSetV.t)) :
  creation_times_comparable entries.*2 →
  strict_weak_order_on rs_entry_created_before entries.
Proof.
  intros Hcmp.
  set key_lt := λ (f : ReplicaSetV.t → Z * Z) (a b : ReplicaSetV.t),
    (f a).1 < (f b).1 ∨
    ((f a).1 = (f b).1 ∧ ((f a).2 < (f b).2 ∨
      ((f a).2 = (f b).2 ∧ go.go_string_lt (rs_name a) (rs_name b)))).
  assert (∀ f (xs : list ReplicaSetV.t),
    (∀ a b, a ∈ xs → b ∈ xs → rs_created_before a b ↔ key_lt f a b) →
    strict_weak_order_on rs_created_before xs) as Hkey_order.
  { intros f xs Hkey.
    (* Incomparable elements have the same key and name. *)
    assert (∀ a b, ¬ key_lt f a b → ¬ key_lt f b a → f a = f b ∧ rs_name a = rs_name b)
      as Hincomparable.
    { intros a b. rewrite /key_lt. destruct (f a) as [a1 a2], (f b) as [b1 b2]. simpl.
      intros Hab Hba.
      assert (a1 = b1) as <- by lia.
      assert (a2 = b2) as <- by lia.
      split; [done|].
      destruct (trichotomyT (@lexico go_string _) (rs_name a) (rs_name b)) as [[?|?]|?];
        [|done|].
      - exfalso. apply Hab. right. split; [done|right; done].
      - exfalso. apply Hba. right. split; [done|right; done]. }
    split_and!.
    - intros x Hx. rewrite Hkey //. rewrite /key_lt.
      intros [?|[_ [?|[_ Hlt]]]]; [lia|lia|].
      exact (irreflexivity (@lexico go_string _) _ Hlt).
    - intros x y z Hx Hy Hz. rewrite !Hkey //. rewrite /key_lt.
      destruct (f x) as [x1 x2], (f y) as [y1 y2], (f z) as [z1 z2]. simpl.
      intros [?|[? [?|[? Hxy]]]] [?|[? [?|[? Hyz]]]];
        try (left; lia); try (right; split; [lia|left; lia]).
      right. split; [lia|]. right. split; [lia|].
      exact (transitivity (R:=@lexico go_string _) Hxy Hyz).
    - intros x y z Hx Hy Hz. rewrite !Hkey //.
      intros Hxy Hyx Hyz Hzy.
      destruct (Hincomparable x y Hxy Hyx) as [Hf1 Hn1].
      destruct (Hincomparable y z Hyz Hzy) as [Hf2 Hn2].
      rewrite /key_lt. rewrite Hf1 Hf2 Hn1 Hn2.
      split; intros [?|[_ [?|[_ Hlt]]]]; try lia;
        exact (irreflexivity (@lexico go_string _) _ Hlt). }
  assert (strict_weak_order_on rs_created_before entries.*2) as Hrss.
  { destruct Hcmp as [Hm|Hw].
    - apply (Hkey_order (λ rs, (sint.Z (rs_creation_time rs).(TimeView.TimeV.ext'), 0))).
      intros a b Ha Hb. specialize (Hm a b Ha Hb).
      assert (time_equal (rs_creation_time a) (rs_creation_time b) ↔
        (rs_creation_time a).(TimeView.TimeV.ext') = (rs_creation_time b).(TimeView.TimeV.ext'))
        as Hequal by (rewrite /time_equal decide_True //).
      assert (time_before (rs_creation_time a) (rs_creation_time b) ↔
        sint.Z (rs_creation_time a).(TimeView.TimeV.ext') <
        sint.Z (rs_creation_time b).(TimeView.TimeV.ext'))
        as Hbefore by (rewrite /time_before decide_True //).
      rewrite /rs_created_before /key_lt /=. case_decide as Heq.
      + apply Hequal in Heq. rewrite Heq.
        split; [intros; right; split; [done|right; done]|].
        intros [?|[_ [?|[_ ?]]]]; [lia|lia|done].
      + rewrite Hequal in Heq. rewrite Hbefore. split; [intros; left; done|].
        intros [?|[Hs [?|[_ _]]]]; [done|lia|].
        exfalso. apply Heq. apply word.signed_inj. exact Hs.
    - apply (Hkey_order (λ rs, (sint.Z (time_sec (rs_creation_time rs)),
                                sint.Z (time_nsec (rs_creation_time rs))))).
      intros a b Ha Hb. specialize (Hw a b Ha Hb).
      assert (time_equal (rs_creation_time a) (rs_creation_time b) ↔
        time_sec (rs_creation_time a) = time_sec (rs_creation_time b) ∧
        time_nsec (rs_creation_time a) = time_nsec (rs_creation_time b))
        as Hequal by (rewrite /time_equal decide_False //).
      assert (time_before (rs_creation_time a) (rs_creation_time b) ↔
        sint.Z (time_sec (rs_creation_time a)) < sint.Z (time_sec (rs_creation_time b)) ∨
        (time_sec (rs_creation_time a) = time_sec (rs_creation_time b) ∧
         sint.Z (time_nsec (rs_creation_time a)) < sint.Z (time_nsec (rs_creation_time b))))
        as Hbefore by (rewrite /time_before decide_False //).
      rewrite /rs_created_before /key_lt /=. case_decide as Heq.
      + apply Hequal in Heq. destruct Heq as [Hs Hn]. rewrite Hs Hn.
        split; [intros; right; split; [done|right; done]|].
        intros [?|[_ [?|[_ ?]]]]; [lia|lia|done].
      + rewrite Hequal in Heq. rewrite Hbefore. split.
        * intros [?|[Hs ?]]; [left; done|]. right. rewrite Hs. split; [done|left; done].
        * intros [?|[Hs [?|[Hn _]]]]; [left; done|right; split; [|done]|].
          -- apply word.signed_inj. exact Hs.
          -- exfalso. apply Heq. split; apply word.signed_inj; done. }
  destruct Hrss as (Hirr & Htrans & Hinc).
  assert (∀ e, e ∈ entries → e.2 ∈ entries.*2) as Hin.
  { intros e He. apply list_elem_of_fmap_2. exact He. }
  rewrite /rs_entry_created_before. split_and!.
  - intros x Hx. apply Hirr, Hin, Hx.
  - intros x y z Hx Hy Hz. apply Htrans; apply Hin; done.
  - intros x y z Hx Hy Hz. apply Hinc; apply Hin; done.
Qed.

Definition rs_by_creation_contents dq
    (sl : controller.ReplicaSetsByCreationTimestamp.t) (entries : list (loc * ReplicaSetV.t)) : iProp Σ :=
  is_pkg_init controller ∗
  sl ↦* entries.*1 ∗
  ([∗ list] e ∈ entries, ReplicaSetV.deepown_l e.1 e.2 dq).

Lemma wp_ReplicaSetsByCreationTimestamp__Len dq sl entries :
  {{{ rs_by_creation_contents dq sl entries }}}
    sl @! controller.ReplicaSetsByCreationTimestamp @! "Len" #()
  {{{ (n : w64), RET #n;
      rs_by_creation_contents dq sl entries ∗
      ⌜ sint.nat n = length entries ∧ 0 ≤ sint.Z n ⌝
  }}}.
Proof.
  wp_start as "(#Hinit & Hsl & Hentries)".
  wp_pures. wp_auto.
  iDestruct (own_slice_len with "Hsl") as %[Hlen Hnonnegative].
  iApply "HΦ". iFrame "Hinit Hsl Hentries". iPureIntro.
  rewrite length_fmap in Hlen. split; [symmetry|]; done.
Qed.

(* Less reads the creation timestamps, whose views are pure. *)
Local Transparent MetaTimeView.TimeV.deepown.
Lemma wp_ReplicaSetsByCreationTimestamp__Less dq sl entries (i j : w64) x y :
  0 ≤ sint.Z i → 0 ≤ sint.Z j → entries !! sint.nat i = Some x → entries !! sint.nat j = Some y →
  {{{ rs_by_creation_contents dq sl entries }}}
    sl @! controller.ReplicaSetsByCreationTimestamp @! "Less" #i #j
  {{{ RET #(bool_decide (rs_entry_created_before x y)); rs_by_creation_contents dq sl entries }}}.
Proof.
  intros Hi Hj Hx Hy.
  wp_start as "(#Hinit & Hsl & Hentries)".
  (* Less reads only the CreationTimestamp and Name fields of the two
     ReplicaSets, so open an entry down to just those two fields. *)
  iAssert (□ ∀ p rs, ReplicaSetV.deepown_l p rs dq -∗
    ∃ ct_c,
      (p.[code.k8s_io.api.apps.v1.v1.ReplicaSet.t, "ObjectMeta"]).[
        code.k8s_io.apimachinery.pkg.apis.meta.v1.v1.ObjectMeta.t, "CreationTimestamp"] ↦{dq} ct_c ∗
      (p.[code.k8s_io.api.apps.v1.v1.ReplicaSet.t, "ObjectMeta"]).[
        code.k8s_io.apimachinery.pkg.apis.meta.v1.v1.ObjectMeta.t, "Name"] ↦{dq} rs_name rs ∗
      ⌜ (TimeV.of_go ct_c).(TimeV.Time') = rs_creation_time rs ⌝ ∗
      ((p.[code.k8s_io.api.apps.v1.v1.ReplicaSet.t, "ObjectMeta"]).[
         code.k8s_io.apimachinery.pkg.apis.meta.v1.v1.ObjectMeta.t, "CreationTimestamp"] ↦{dq} ct_c -∗
       (p.[code.k8s_io.api.apps.v1.v1.ReplicaSet.t, "ObjectMeta"]).[
         code.k8s_io.apimachinery.pkg.apis.meta.v1.v1.ObjectMeta.t, "Name"] ↦{dq} rs_name rs -∗
       ReplicaSetV.deepown_l p rs dq))%I as "#Hacc".
  { iIntros "!>" (p rs) "H".
    iDestruct "H" as (c) "[Hl Hc]".
    iDestruct (struct_fields_split (V:=code.k8s_io.api.apps.v1.v1.ReplicaSet.t) with "Hl")
      as "[Hf %Hnn]".
    iNamedPrefix "Hf" "Hf_".
    iDestruct (struct_fields_split (V:=code.k8s_io.apimachinery.pkg.apis.meta.v1.v1.ObjectMeta.t)
      with "Hf_ObjectMeta") as "[Hom %Hom_nn]".
    iNamedPrefix "Hom" "Hom_".
    iNamed "Hc". iNamedPrefix "Hdeepown_objectmeta" "Hm_".
    iEval (rewrite /MetaTimeView.TimeV.deepown) in "Hm_Hdeepown_creationtimestamp".
    iDestruct "Hm_Hdeepown_creationtimestamp" as %Hct.
    iEval (rewrite Hm_Hdeepown_name) in "Hom_Name".
    iExists _. iFrame "Hom_CreationTimestamp Hom_Name".
    iSplit; [iPureIntro; rewrite /rs_creation_time -Hct; done|].
    iIntros "Hom_CreationTimestamp Hom_Name".
    iEval (rewrite /rs_name -Hm_Hdeepown_name) in "Hom_Name".
    iCombineNamed "Hom_*" as "Hom".
    iAssert (typed_pointsto_def (p.[code.k8s_io.api.apps.v1.v1.ReplicaSet.t, "ObjectMeta"])
      c.(code.k8s_io.api.apps.v1.v1.ReplicaSet.ObjectMeta') dq) with "[Hom]" as "Hom".
    { iNamed "Hom". destruct c as [tm om sp st]. destruct om. simpl. iFrame. }
    iDestruct (struct_fields_combine _ _ _ Hom_nn with "Hom") as "Hf_ObjectMeta".
    iCombineNamed "Hf_*" as "Hf".
    iAssert (typed_pointsto_def p c dq) with "[Hf]" as "Hf".
    { iNamed "Hf". destruct c. simpl. iFrame. }
    iDestruct (struct_fields_combine _ _ _ Hnn with "Hf") as "Hl".
    iExists c. iFrame "Hl Hdeepown_spec Hdeepown_status".
    iSplit; [done|].
    iCombineNamed "Hm_Hdeepown_*" as "Hm". iNamed "Hm".
    iFrame. iFrame "%". }
  iDestruct (own_slice_len with "Hsl") as %[Hlen _]. rewrite length_fmap in Hlen.
  assert (entries.*1 !! sint.nat i = Some x.1) as Hpx by (rewrite list_lookup_fmap Hx //).
  assert (entries.*1 !! sint.nat j = Some y.1) as Hpy by (rewrite list_lookup_fmap Hy //).
  pose proof (lookup_lt_Some _ _ _ Hx) as Hi_lt.
  pose proof (lookup_lt_Some _ _ _ Hy) as Hj_lt.
  wp_auto.
  (* Every [rsList[k]] in Less reloads the slice element. *)
  Local Ltac load_entry k Hp :=
    rewrite -> decide_True by word;
    iDestruct (own_slice_elem_acc (sint.Z k) with "Hsl") as "[Hptr Hrestore]"; [word|exact Hp|];
    wp_auto;
    iDestruct ("Hrestore" with "Hptr") as "Hsl";
    iEval (rewrite (list_insert_id _ _ _ Hp)) in "Hsl".
  load_entry j Hpy. load_entry i Hpx.
  iAssert (is_pkg_init code.k8s_io.apimachinery.pkg.apis.meta.v1.pkg_id.v1) as "#Hmeta".
  { iPkgInit. }
  destruct (decide (sint.nat i = sint.nat j)) as [Hij|Hij].
  - (* The same ReplicaSet on both sides: its timestamp equals itself, and a
       name is not less than itself. *)
    assert (y = x) as -> by (rewrite -Hij in Hy; congruence).
    iDestruct (big_sepL_lookup_acc with "Hentries") as "[Hex Hrest]"; [exact Hx|].
    iDestruct ("Hacc" with "Hex") as (ctx) "(Hctx & Hnx & %Hctx & Hclose_x)".
    assert (∃ dh, dq = dh ⋅ dh) as [dh Hdh].
    { destruct dq as [q| |q].
      - exists (DfracOwn (q/2)). rewrite dfrac_op_own Qp.div_2 //.
      - exists DfracDiscarded. done.
      - exists (DfracBoth (q/2)).
        change (DfracBoth (q/2) ⋅ DfracBoth (q/2)) with (DfracBoth (q/2 + q/2)).
        rewrite Qp.div_2 //. }
    iEval (rewrite Hdh) in "Hctx". iDestruct "Hctx" as "[Hctx1 Hctx2]".
    wp_apply (New.proof.k8s_io.apimachinery.pkg.apis.meta.v1.wp_Time__Equal
      (package_sem:=controller_meta_v1_sem) with "[$Hmeta $Hctx1 $Hctx2]").
    iIntros "[Hctx1 Hctx2]".
    iCombine "Hctx1 Hctx2" as "Hctx". iEval (rewrite -Hdh) in "Hctx".
    assert (time_equal (TimeV.Time' (TimeV.of_go ctx)) (TimeV.Time' (TimeV.of_go ctx)))
      as Hrefl by (rewrite /time_equal; case_decide; done).
    rewrite (bool_decide_eq_true_2 _ Hrefl).
    wp_auto. load_entry i Hpx. load_entry j Hpy.
    iDestruct ("Hclose_x" with "Hctx Hnx") as "Hex".
    iSpecialize ("Hrest" with "Hex").
    iSpecialize ("HΦ" with "[$Hinit $Hsl $Hrest]").
    iExactEq "HΦ". do 2 f_equal. apply bool_decide_ext.
    rewrite Hctx in Hrefl.
    rewrite /rs_entry_created_before /rs_created_before decide_True //.
  - iDestruct (big_sepL_delete with "Hentries") as "[Hex Hrest]"; [exact Hx|].
    iDestruct (big_sepL_lookup_acc with "Hrest") as "[Hey Hrest]"; [exact Hy|].
    rewrite decide_False; [congruence|].
    iDestruct ("Hacc" with "Hex") as (ctx) "(Hctx & Hnx & %Hctx & Hclose_x)".
    iDestruct ("Hacc" with "Hey") as (cty) "(Hcty & Hny & %Hcty & Hclose_y)".
    wp_apply (New.proof.k8s_io.apimachinery.pkg.apis.meta.v1.wp_Time__Equal
      (package_sem:=controller_meta_v1_sem) with "[$Hmeta $Hctx $Hcty]").
    iIntros "[Hctx Hcty]".
    rewrite Hctx Hcty.
    wp_if_destruct.
    + (* Equal times: compare names. *)
      load_entry i Hpx. load_entry j Hpy.
      iDestruct ("Hclose_x" with "Hctx Hnx") as "Hex".
      iDestruct ("Hclose_y" with "Hcty Hny") as "Hey".
      iSpecialize ("Hrest" with "Hey").
      iAssert ([∗ list] e ∈ entries, ReplicaSetV.deepown_l e.1 e.2 dq)%I
        with "[Hex Hrest]" as "Hentries".
      { iApply big_sepL_delete; [exact Hx|]. iFrame. }
      iSpecialize ("HΦ" with "[$Hinit $Hsl $Hentries]").
      iExactEq "HΦ". do 2 f_equal. apply bool_decide_ext.
      rewrite /rs_entry_created_before /rs_created_before decide_True //.
    + (* Different times: Before decides. *)
      load_entry j Hpy. load_entry i Hpx.
      wp_apply (New.proof.k8s_io.apimachinery.pkg.apis.meta.v1.wp_Time__Before
        (package_sem:=controller_meta_v1_sem) with "[$Hmeta $Hctx $Hcty]").
      iIntros "[Hctx Hcty]".
      rewrite Hctx Hcty.
      iDestruct ("Hclose_x" with "Hctx Hnx") as "Hex".
      iDestruct ("Hclose_y" with "Hcty Hny") as "Hey".
      iSpecialize ("Hrest" with "Hey").
      iAssert ([∗ list] e ∈ entries, ReplicaSetV.deepown_l e.1 e.2 dq)%I
        with "[Hex Hrest]" as "Hentries".
      { iApply big_sepL_delete; [exact Hx|]. iFrame. }
      iSpecialize ("HΦ" with "[$Hinit $Hsl $Hentries]").
      wp_pures. iExactEq "HΦ". do 2 f_equal. apply bool_decide_ext.
      rewrite /rs_entry_created_before /rs_created_before decide_False //.
Qed.

Local Opaque MetaTimeView.TimeV.deepown.

Lemma wp_ReplicaSetsByCreationTimestamp__Swap dq sl entries (i j : w64) :
  0 ≤ sint.Z i < length entries → 0 ≤ sint.Z j < length entries →
  {{{ rs_by_creation_contents dq sl entries }}}
    sl @! controller.ReplicaSetsByCreationTimestamp @! "Swap" #i #j
  {{{ RET #();
      rs_by_creation_contents dq sl (list_swap entries (sint.nat i) (sint.nat j))
  }}}.
Proof.
  intros Hi Hj.
  destruct Hi as [Hi_nonnegative Hi_upper].
  destruct Hj as [Hj_nonnegative Hj_upper].
  wp_start as "(#Hinit & Hsl & Hentries)".
  wp_pures.
  iDestruct (own_slice_len with "Hsl") as %[Hlen Hnonnegative].
  rewrite length_fmap in Hlen.
  assert (sint.Z (slice.len sl) = Z.of_nat (length entries)) as Hlen_Z.
  { replace (sint.Z (slice.len sl)) with
      (Z.of_nat (sint.nat (slice.len sl))) by word.
    rewrite <-Hlen. done. }
  wp_auto.
  assert (∃ ci, (fst <$> entries) !! sint.nat i = Some ci)
    as [ci Hci_lookup].
  { apply lookup_lt_is_Some_2. rewrite length_fmap.
    apply Nat2Z.inj_lt.
    replace (Z.of_nat (sint.nat i)) with (sint.Z i) by word. exact Hi_upper. }
  assert (∃ cj, (fst <$> entries) !! sint.nat j = Some cj)
    as [cj Hcj_lookup].
  { apply lookup_lt_is_Some_2. rewrite length_fmap.
    apply Nat2Z.inj_lt.
    replace (Z.of_nat (sint.nat j)) with (sint.Z j) by word. exact Hj_upper. }
  rewrite -> decide_True by
    (split; [exact Hj_nonnegative|rewrite Hlen_Z; exact Hj_upper]).
  wp_apply (wp_load_slice_index with "[$Hsl]");
    [exact Hj_nonnegative|iPureIntro; exact Hcj_lookup|].
  iIntros "Hsl". wp_auto.
  rewrite -> decide_True by
    (split; [exact Hi_nonnegative|rewrite Hlen_Z; exact Hi_upper]).
  wp_apply (wp_load_slice_index with "[$Hsl]");
    [exact Hi_nonnegative|iPureIntro; exact Hci_lookup|].
  iIntros "Hsl". wp_auto.
  rewrite -> decide_True by
    (split; [exact Hi_nonnegative|rewrite Hlen_Z; exact Hi_upper]).
  wp_auto.
  wp_apply (wp_store_slice_index with "[$Hsl]").
  { iPureIntro. rewrite length_fmap.
    split; [exact Hi_nonnegative|exact Hi_upper]. }
  iIntros "Hsl". wp_auto.
  rewrite -> decide_True by
    (split; [exact Hj_nonnegative|rewrite Hlen_Z; exact Hj_upper]).
  wp_auto.
  wp_apply (wp_store_slice_index with "[$Hsl]").
  { iPureIntro. rewrite length_insert length_fmap.
    split; [exact Hj_nonnegative|exact Hj_upper]. }
  iIntros "Hsl". wp_auto.
  iApply "HΦ". rewrite /rs_by_creation_contents list_swap_fmap.
  iFrame "Hinit".
  iSplitL "Hsl".
  { rewrite /list_swap Hci_lookup Hcj_lookup. iFrame "Hsl". }
  iEval (rewrite (big_sepL_permutation
    (fun e => ReplicaSetV.deepown_l e.1 e.2 dq)
    entries (list_swap entries (sint.nat i) (sint.nat j))
    (list_swap_permutation entries (sint.nat i) (sint.nat j))))
    in "Hentries".
  iFrame "Hentries".
Qed.

#[global] Instance rs_by_creation_sort_interface dq :
  SortInterfaceRelSpec controller.ReplicaSetsByCreationTimestamp
    (rs_by_creation_contents dq) rs_entry_created_before.
Proof.
  constructor.
  - apply wp_ReplicaSetsByCreationTimestamp__Len.
  - apply wp_ReplicaSetsByCreationTimestamp__Less.
  - apply wp_ReplicaSetsByCreationTimestamp__Swap.
Qed.

Definition pod_from_template (template : PodTemplateSpecV.t) (pod : PodV.t) : Prop :=
  pod.(PodV.Spec') = template.(PodTemplateSpecV.Spec') ∧
  pod.(PodV.ObjectMeta').(ObjectMetaV.Labels') =
    Some (default ∅ template.(PodTemplateSpecV.ObjectMeta').(ObjectMetaV.Labels')) ∧
  pod.(PodV.ObjectMeta').(ObjectMetaV.Annotations') =
    Some (default ∅ template.(PodTemplateSpecV.ObjectMeta').(ObjectMetaV.Annotations')) ∧
  pod.(PodV.ObjectMeta').(ObjectMetaV.Finalizers') =
    Some (default [] template.(PodTemplateSpecV.ObjectMeta').(ObjectMetaV.Finalizers')).

Definition generated_pod_meta (template : PodTemplateSpecV.t)
    (parent_name : go_string) (owners : option (list OwnerReferenceV.t)) :
    ObjectMetaV.t :=
  ObjectMetaV.mk ""%go (parent_name ++ "-"%go) ""%go ""%go ""%go ""%go
    (W64 0) TimeV.zero None None
    (Some (default ∅ template.(PodTemplateSpecV.ObjectMeta').(ObjectMetaV.Labels')))
    (Some (default ∅
      template.(PodTemplateSpecV.ObjectMeta').(ObjectMetaV.Annotations')))
    owners
    (Some (default []
      template.(PodTemplateSpecV.ObjectMeta').(ObjectMetaV.Finalizers')))
    None.

Definition generated_pod (template : PodTemplateSpecV.t)
    (parent_name : go_string) (owners : option (list OwnerReferenceV.t)) :
    PodV.t :=
  PodV.mk (zero_val v1.TypeMeta.t)
    (generated_pod_meta template parent_name owners)
    template.(PodTemplateSpecV.Spec') PodStatusV.zero.

Lemma generated_pod_parent_ref template parent_name ref kind uid :
  OwnerReferenceV.refers_to_controller ref kind parent_name uid →
  obj_parent_ref_is (KObjectV.Pod (generated_pod template parent_name (Some [ref])))
    kind parent_name uid.
Proof.
  intros (Hkind & Hname & Huid & _ & Hcontroller).
  rewrite /obj_parent_ref_is /meta_parent_ref_is /meta_parent_ref
    /generated_pod /generated_pod_meta /=.
  rewrite Hcontroller /= Hkind Hname Huid. done.
Qed.

Lemma generated_pod_valid_create template parent_name ref namespace :
  PodTemplateSpecV.valid template →
  valid_dns1123_subdomain parent_name →
  length parent_name < 58 →
  valid_finalizers template.(PodTemplateSpecV.ObjectMeta').(ObjectMetaV.Finalizers') →
  OwnerReferenceV.valid ref →
  namespace ≠ ""%go →
  valid_namespace namespace →
  KObjectV.valid_create "Pod"%go namespace
    (KObjectV.Pod (generated_pod template parent_name (Some [ref]))).
Proof.
  intros Htemplate Hname Hlen Hfinalizers Href Hnamespace_nonempty Hnamespace_valid.
  pose proof (PodTemplateSpecV.generated_spec_valid template Htemplate) as [Hannotations_full Hspec_full].
  destruct Htemplate as (Hlabels & Hannotations & Hspec & _).
  rewrite /KObjectV.valid_create /= /PodV.valid_create
    /generated_pod /generated_pod_meta /=.
  split_and!.
  - done.
  - exact Hnamespace_nonempty.
  - exact Hnamespace_valid.
  - apply zero_typemeta_valid_create.
  - rewrite /ObjectMetaV.valid_create /=.
    split_and!.
    + apply valid_generate_name_of_valid_prefix.
      exists parent_name. split_and!; [done| |].
      * intros ->. inversion Hname as [Hsyntax _]. inversion Hsyntax.
      * unfold valid_name, PodV.kind. right. split; [left; done|exact Hname].
    + rewrite length_app /=. lia.
    + left. done.
    + destruct template.(PodTemplateSpecV.ObjectMeta').(ObjectMetaV.Labels') as [labels|];
        simpl in *; [exact Hlabels|apply map_Forall_empty].
    + destruct template.(PodTemplateSpecV.ObjectMeta').(ObjectMetaV.Annotations') as [annotations|];
        simpl in *; [destruct Hannotations as [Hannotations _]; exact Hannotations|apply map_Forall_empty].
    + destruct template.(PodTemplateSpecV.ObjectMeta').(ObjectMetaV.Annotations') as [annotations|];
        simpl in *; [destruct Hannotations as [_ Hannotations]; exact Hannotations|done].
    + intros i1 i2 or1 or2 H1 H2 _ _.
      pose proof (lookup_lt_Some _ _ _ H1) as Hi1.
      pose proof (lookup_lt_Some _ _ _ H2) as Hi2. simpl in Hi1, Hi2. lia.
    + intros owner Howner. rewrite list_elem_of_singleton in Howner. subst owner. exact Href.
    + destruct template.(PodTemplateSpecV.ObjectMeta').(ObjectMetaV.Finalizers') as [finalizers|];
        simpl in *; [exact Hfinalizers|constructor].
    + apply valid_managed_fields_none.
  - exact Hspec.
  - exact Hannotations_full.
  - exact Hspec_full.
Qed.

(** The complete status view includes Phase; the helper only reads the Pod. *)
Lemma wp_IsPodActive (pod_l : loc) (pod : PodV.t) (dq : dfrac) :
  {{{ is_pkg_init controller ∗
      "Hpod" ∷ PodV.deepown_l pod_l pod dq
  }}}
    @! controller.IsPodActive #pod_l
  {{{ (active : bool), RET #active; PodV.deepown_l pod_l pod dq }}}.
Proof. Admitted.

(* A pod is terminating when it is not terminal and has a deletion timestamp.
   The terminal check is trusted ([wp_IsPodTerminal]), so the result is some
   boolean; the pod is unchanged. *)
Lemma wp_IsPodTerminating (pod_l : loc) (pod : PodV.t) (dq : dfrac) :
  {{{ is_pkg_init controller ∗
      "Hpod" ∷ PodV.deepown_l pod_l pod dq
  }}}
    @! controller.IsPodTerminating #pod_l
  {{{ (terminating : bool), RET #terminating; PodV.deepown_l pod_l pod dq }}}.
Proof.
  wp_start as "H". iNamed "H". wp_auto_keep.
  wp_apply_keep (wp_IsPodTerminal with "[$Hpod]").
  iIntros (terminal) "Hpod".
  destruct terminal; wp_auto_keep.
  - by iApply "HΦ".
  - iDestruct "Hpod" as (c) "[Hl Hc]".
    wp_auto_keep.
    iApply "HΦ". iExists c. iFrame.
Qed.

(* [FilterTerminatingPods] returns some of its input pods; only the length of
   the result is used (for the terminating-replicas count). The input slice and
   pods are only read and are returned. *)
Lemma wp_FilterTerminatingPods sl dq_sl ptrs pods dq :
  {{{ is_pkg_init controller ∗
      "Hsl" ∷ sl ↦*{dq_sl} ptrs ∗
      "Hpods" ∷ ([∗ list] ptr;pod ∈ ptrs;pods, PodV.deepown_l ptr pod dq)
  }}}
    @! controller.FilterTerminatingPods #sl
  {{{ sl' (ptrs' : list loc), RET #sl';
      sl' ↦* ptrs' ∗
      ⌜ length ptrs' ≤ length ptrs ⌝ ∗
      sl ↦*{dq_sl} ptrs ∗
      ([∗ list] ptr;pod ∈ ptrs;pods, PodV.deepown_l ptr pod dq)
  }}}.
Proof.
  wp_start as "H". iNamed "H". wp_auto_keep.
  iDestruct (own_slice_len with "Hsl") as %(Hsl_len1 & Hsl_len2).
  iDestruct (big_sepL2_length with "Hpods") as %Hlen.
  set I := (∃ (i : w64) (p : loc) (result : slice.t) (ptrs' : list loc),
    "i" ∷ i_ptr ↦ i ∗
    "p" ∷ p_ptr ↦ p ∗
    "result" ∷ result_ptr ↦ result ∗
    "Hresult" ∷ result ↦* ptrs' ∗
    "Hresult_cap" ∷ own_slice_cap loc result (DfracOwn 1) ∗
    "Hpods" ∷ ([∗ list] ptr;pod ∈ ptrs;pods, PodV.deepown_l ptr pod dq) ∗
    "%Hresult_len" ∷ ⌜ length ptrs' ≤ sint.nat i ⌝ ∗
    "%Hi" ∷ ⌜ 0 ≤ sint.Z i ≤ sint.Z (slice.len sl) ⌝)%I.
  iAssert I with "[i p result Hpods]" as "Hloop".
  { iExists (W64 0), null, slice.nil, []. iFrame.
    iSplitR; first iApply own_slice_nil.
    iSplitR; first iApply own_slice_cap_nil.
    iPureIntro. simpl. word. }
  wp_for_keep "Hloop".
  wp_if_destruct_keep.
  - list_elem ptrs (sint.Z i) as this_ptr.
    assert (∃ this_pod, pods !! sint.nat i = Some this_pod) as [this_pod Hthis_pod].
    { apply lookup_lt_is_Some_2. rewrite -Hlen. apply (lookup_lt_Some _ _ _ Hthis_ptr_lookup). }
    rewrite decide_True; first word.
    wp_apply_keep (wp_load_slice_index with "[$Hsl]"); [word| |].
    { iPureIntro. exact Hthis_ptr_lookup. }
    iIntros "Hsl". wp_auto_keep.
    iDestruct (big_sepL2_lookup_acc with "Hpods") as "[Hthis Hpods]";
      [exact Hthis_ptr_lookup|exact Hthis_pod|].
    wp_apply_keep (wp_IsPodTerminating with "[$Hthis]").
    iIntros (terminating) "Hthis".
    iDestruct ("Hpods" with "Hthis") as "Hpods".
    destruct terminating; wp_auto_keep.
    + wp_apply_keep wp_slice_literal. iSplitR; first done. iIntros (sl0) "[Hsl0 _]". wp_auto_keep.
      wp_apply_keep (wp_slice_append with "[$Hresult $Hresult_cap $Hsl0]").
      iIntros (result') "(Hresult & Hresult_cap & _)". wp_auto_keep.
      iApply wp_for_post_do. wp_auto_keep.
      iFrame "HΦ Hsl".
      iExists (word.add i (W64 1)), this_ptr, result', (ptrs' ++ [this_ptr]). iFrame.
      iPureIntro. rewrite length_app /=. split; word.
    + iApply wp_for_post_do. wp_auto_keep.
      iFrame "HΦ Hsl".
      iExists (word.add i (W64 1)), this_ptr, result, ptrs'. iFrame.
      iPureIntro. split; word.
  - iApply "HΦ". iFrame. iPureIntro. word.
Qed.

Lemma wp_getPodsLabelSet template_l template dq :
  {{{ "Hinit" ∷ is_pkg_init controller ∗
      "Htemplate" ∷ PodTemplateSpecV.deepown_l template_l template dq
  }}}
    @! controller.getPodsLabelSet #template_l
  {{{ labels_l, RET #labels_l;
      PodTemplateSpecV.deepown_l template_l template dq ∗
      labels_l ↦$ default ∅
        template.(PodTemplateSpecV.ObjectMeta').(ObjectMetaV.Labels')
  }}}.
Proof.
  wp_start as "H". iNamed "H".
  iDestruct "Htemplate" as (template_c) "[Htemplate_l Htemplate]".
  iNamedPrefix "Htemplate" "Htemplate_".
  iNamedPrefix "Htemplate_Hdeepown_objectmeta" "Hmeta_".
  iDestruct (struct_fields_split with "Htemplate_l") as
    "[Htemplate_fields %Htemplate_nonnull]".
  iNamedPrefix "Htemplate_fields" "Htemplate_field_".
  iDestruct (struct_fields_split with "Htemplate_field_ObjectMeta") as
    "[Hmeta_fields %Hmeta_nonnull]".
  iNamedPrefix "Hmeta_fields" "Hmeta_field_".
  wp_auto_keep.
  rewrite go.make1_underlying.
  rewrite (go.is_underlying (t := labels.Set')
    (tunder := labels.Set'ⁱᵐᵖˡ)).
  wp_apply_keep wp_map_make1 as (labels_l) "Hlabels".
  wp_pures_keep.
  iCombineNamed "Hmeta_field_*" as "Hmeta_fields".
  iAssert (typed_pointsto_def
      (template_l.[v1.PodTemplateSpec.t, "ObjectMeta"])
      template_c.(v1.PodTemplateSpec.ObjectMeta') dq)
    with "[Hmeta_fields]" as "Hobjectmeta".
  { iNamed "Hmeta_fields". simpl. rewrite /named. iFrame. }
  iDestruct (struct_fields_combine (V:=v1.ObjectMeta.t)
      (template_l.[v1.PodTemplateSpec.t, "ObjectMeta"])
      template_c.(v1.PodTemplateSpec.ObjectMeta') dq Hmeta_nonnull
      with "Hobjectmeta") as "Hobjectmeta".
  iCombineNamed "Htemplate_field_*" as "Htemplate_fields".
  iAssert (typed_pointsto_def template_l template_c dq)
    with "[Htemplate_fields Hobjectmeta]" as "Htemplate_l".
  { iNamed "Htemplate_fields". simpl. rewrite /named. iFrame. }
  iDestruct (struct_fields_combine (V:=v1.PodTemplateSpec.t)
      template_l template_c dq Htemplate_nonnull with "Htemplate_l")
    as "Htemplate_l".
  destruct template.(PodTemplateSpecV.ObjectMeta').(ObjectMetaV.Labels')
    as [labels|] eqn:Hlabels_opt.
  - iDestruct "Hmeta_Hdeepown_labels_some" as (labels_c)
      "[Hlabels_src %Hlabels_c]".
    subst labels_c.
    wp_apply_keep (wp_map_for_range_return_func (key_type:=go.string)
      (λ (keys : list go_string) i,
        ∃ (last_value last_key : go_string),
          "v" ∷ v_ptr ↦ last_value ∗
          "k" ∷ k_ptr ↦ last_key ∗
          "desiredLabels" ∷ desiredLabels_ptr ↦ labels_l ∗
          "Hlabels" ∷ labels_l ↦$ map_prefix keys i labels)%I
      with "Hlabels_src").
    { done. }
    iIntros (keys) "%Hkeys".
    iSplitL "v k desiredLabels Hlabels".
    { iExists ""%go, ""%go. iFrame.
      rewrite map_prefix_empty. iFrame. }
    iSplitL "".
    { iModIntro. iIntros (i key value) "%Hiter Hloop".
      destruct Hkeys as [Hkeys_dom [Hkeys_len Hkeys_nodup]].
      destruct Hiter as [Hi_bounds [Hkey_lookup Hvalue_lookup]].
      destruct Hi_bounds as [Hi_nonneg Hi_upper].
      iDestruct "Hloop" as (last_value last_key)
        "(v & k & desiredLabels & Hlabels)".
      wp_pures_keep.
      simpl subst'.
      wp_auto_keep.
      wp_apply_keep (wp_map_insert (K:=go_string) (V:=go_string)
        go.string labels_l (map_prefix keys i labels) key value
        with "Hlabels") as "Hlabels".
      iRight. iSplit; [done|].
      iExists value, key. iFrame.
      rewrite -map_prefix_insert; done. }
    iIntros "Hlabels_src Hloop".
    iDestruct "Hloop" as (last_value last_key)
      "(v & k & desiredLabels & Hlabels)".
    destruct Hkeys as [Hkeys_dom [Hkeys_len Hkeys_nodup]].
    rewrite (map_prefix_all keys labels Hkeys_dom Hkeys_len).
    wp_auto_keep.
    iAssert ((match template.(PodTemplateSpecV.ObjectMeta').(ObjectMetaV.Labels') with
      | Some labels' => ∃ labels_c,
          template_c.(v1.PodTemplateSpec.ObjectMeta').(v1.ObjectMeta.Labels') ↦${dq} labels_c ∗
          ⌜labels_c = labels'⌝
      | None => True
      end)%I) with "[Hlabels_src]" as "Hmeta_Hdeepown_labels_some".
    { rewrite Hlabels_opt. iExists labels.
      iSplitL "Hlabels_src"; [iExact "Hlabels_src"|done]. }
    iCombineNamed "Hmeta_*" as "Hobjectmeta".
    iAssert (ObjectMetaV.deepown
        template_c.(v1.PodTemplateSpec.ObjectMeta')
        template.(PodTemplateSpecV.ObjectMeta') dq)
      with "[Hobjectmeta]" as "Hobjectmeta".
    { rewrite /ObjectMetaV.deepown Hlabels_opt /=. iNamed "Hobjectmeta".
      iFrame. iFrame "%". }
    iApply ("HΦ" $! labels_l). iFrame "Hlabels".
    iExists template_c. iFrame "Htemplate_l".
    rewrite /PodTemplateSpecV.deepown. iFrame.
  - assert (template_c.(v1.PodTemplateSpec.ObjectMeta').(v1.ObjectMeta.Labels') =
        map.nil) as Hlabels_nil.
    { apply Hmeta_Hdeepown_labels_none. done. }
    rewrite Hlabels_nil.
    wp_apply_keep (wp_map_for_range_nil go.string go.string).
    wp_pures_keep.
    iCombineNamed "Hmeta_*" as "Hobjectmeta".
    iAssert (ObjectMetaV.deepown
        template_c.(v1.PodTemplateSpec.ObjectMeta')
        template.(PodTemplateSpecV.ObjectMeta') dq)
      with "[Hobjectmeta]" as "Hobjectmeta".
    { rewrite /ObjectMetaV.deepown Hlabels_opt /=. iNamed "Hobjectmeta".
      iFrame. iFrame "%". }
    iApply ("HΦ" $! labels_l).
    iFrame "Hlabels".
    iExists template_c. iFrame "Htemplate_l".
    rewrite /PodTemplateSpecV.deepown. iFrame.
Qed.

Lemma wp_getPodsFinalizers template_l template dq :
  {{{ is_pkg_init controller ∗
      PodTemplateSpecV.deepown_l template_l template dq
  }}}
    @! controller.getPodsFinalizers #template_l
  {{{ finalizers_sl, RET #finalizers_sl;
      PodTemplateSpecV.deepown_l template_l template dq ∗
      finalizers_sl ↦* default []
        template.(PodTemplateSpecV.ObjectMeta').(ObjectMetaV.Finalizers') ∗
      own_slice_cap go_string finalizers_sl (DfracOwn 1) ∗
      ⌜ finalizers_sl ≠ slice.nil ⌝
  }}}.
Proof.
  wp_start as "Htemplate".
  iDestruct "Htemplate" as (template_c) "[Htemplate_l Htemplate]".
  iNamedPrefix "Htemplate" "Htemplate_".
  iNamedPrefix "Htemplate_Hdeepown_objectmeta" "Hmeta_".
  iDestruct (struct_fields_split with "Htemplate_l") as
    "[Htemplate_fields %Htemplate_nonnull]".
  iNamedPrefix "Htemplate_fields" "Htemplate_field_".
  iDestruct (struct_fields_split with "Htemplate_field_ObjectMeta") as
    "[Hmeta_fields %Hmeta_nonnull]".
  iNamedPrefix "Hmeta_fields" "Hmeta_field_".
  iAssert (∃ finalizers,
      template_c.(v1.PodTemplateSpec.ObjectMeta').(v1.ObjectMeta.Finalizers')
        ↦*{dq} finalizers ∗
      ⌜finalizers = default []
        template.(PodTemplateSpecV.ObjectMeta').(ObjectMetaV.Finalizers')⌝)%I
    with "[Hmeta_Hdeepown_finalizers_some]" as
      (finalizers) "[Hfinalizers_src %Hfinalizers]".
  { destruct template.(PodTemplateSpecV.ObjectMeta').(ObjectMetaV.Finalizers')
      as [finalizers|] eqn:Hfinalizers_opt; simpl.
    - iExists finalizers. iSplitL; first iFrame. done.
    - assert (template_c.(v1.PodTemplateSpec.ObjectMeta').(v1.ObjectMeta.Finalizers') =
          slice.nil) as Hfinalizers_nil.
      { apply Hmeta_Hdeepown_finalizers_none. done. }
      rewrite Hfinalizers_nil. iExists []. iSplit; last done.
      iApply own_slice_nil. }
  subst finalizers.
  iDestruct (own_slice_len with "Hfinalizers_src") as
    %[Hfinalizers_len Hfinalizers_len_nonnegative].
  assert (Hmake3 : ∀ stk E (len cap : u64),
    0 ≤ sint.Z len ≤ sint.Z cap →
    {{{ True }}}
      #(functions go.make3 [go.SliceType go.string]) #len #cap @ stk; E
    {{{ sl, RET #sl;
        sl ↦* (replicate (sint.nat len) (zero_val go_string)) ∗
        own_slice_cap go_string sl (DfracOwn 1) ∗
        ⌜sl ≠ slice.nil⌝
    }}}).
  { intros stk E len cap Hbounds. wp_start.
    wp_if_destruct; first (exfalso; word).
    wp_if_destruct; first (exfalso; word).
    case_bool_decide; wp_auto_keep.
    - subst cap. assert (len = W64 0) by word. subst len.
      wp_apply_keep wp_ArbitraryInt. iIntros (x) "_".
      wp_auto_keep. iApply "HΦ".
      iDestruct (own_slice_empty with "[]") as "$"; simpl.
      { word. }
      { word. }
      { by iApply array_empty. }
      iDestruct own_slice_cap_empty as "$"; simpl.
      { word. }
      { word. }
      iPureIntro. intros Hnil.
      apply (f_equal slice.ptr) in Hnil.
      apply (f_equal addr_id) in Hnil.
      rewrite /loc_add addr_id_of_plus /addr_id /null /= in Hnil. lia.
    - iApply "HΦ".
      rewrite own_slice_unseal /own_slice_def /=.
      iDestruct (array_split len with "p") as "[Hsl Hcap]"; first word.
      simpl. rewrite take_replicate.
      iSplitL "Hsl".
      { iRight. iSplitL; last word.
        replace (_ `min` _)%nat with (sint.nat len) by word. iFrame. }
      rewrite own_slice_cap_unseal /own_slice_cap_def /=.
      iSplitL "Hcap".
      { iRight. iSplitR; first word. iFrame. }
      iPureIntro. intros Hnil.
      apply (f_equal slice.cap) in Hnil. simpl in Hnil. word. }
  assert (Hmake2 : ∀ stk E (len : u64),
    {{{ ⌜0 ≤ sint.Z len⌝ }}}
      #(functions go.make2 [go.SliceType go.string]) #len @ stk; E
    {{{ sl, RET #sl;
        sl ↦* (replicate (sint.nat len) (zero_val go_string)) ∗
        own_slice_cap go_string sl (DfracOwn 1) ∗
        ⌜sl ≠ slice.nil⌝
    }}}).
  { intros stk E len. wp_start as "%Hlen".
    wp_apply_keep Hmake3; first word.
    iIntros (sl) "Hsl". iApply "HΦ". iFrame. }
  wp_auto_keep.
  wp_apply_keep Hmake2; first word.
  iIntros (finalizers_sl)
    "(Hfinalizers & Hfinalizers_cap & %Hfinalizers_non_nil)".
  iEval (rewrite -Hfinalizers_len) in "Hfinalizers".
  wp_auto_keep.
  wp_apply_keep (wp_slice_copy with "[$Hfinalizers $Hfinalizers_src]") as (n)
    "(%Hcopied & Hfinalizers & Hfinalizers_src)".
  iAssert (finalizers_sl ↦* default []
      template.(PodTemplateSpecV.ObjectMeta').(ObjectMetaV.Finalizers'))
    with "[Hfinalizers]" as "Hfinalizers".
  { iEval (rewrite length_replicate) in "Hfinalizers".
    iEval (rewrite take_ge; last done) in "Hfinalizers".
    assert (length (replicate
        (length (default [] (ObjectMetaV.Finalizers'
          (PodTemplateSpecV.ObjectMeta' template)))) (zero_val go_string)) ≤
      length (default [] (ObjectMetaV.Finalizers'
        (PodTemplateSpecV.ObjectMeta' template))))%nat as Hdrop.
    { rewrite length_replicate. done. }
    iEval (rewrite (drop_ge _ _ Hdrop)) in "Hfinalizers".
    iEval (rewrite app_nil_r) in "Hfinalizers".
    iExact "Hfinalizers". }
  wp_pures_keep.
  iCombineNamed "Hmeta_field_*" as "Hmeta_fields".
  iAssert (typed_pointsto_def
      (template_l.[v1.PodTemplateSpec.t, "ObjectMeta"])
      template_c.(v1.PodTemplateSpec.ObjectMeta') dq)
    with "[Hmeta_fields]" as "Hobjectmeta_l".
  { iNamed "Hmeta_fields". simpl. rewrite /named. iFrame. }
  iDestruct (struct_fields_combine (V:=v1.ObjectMeta.t)
      (template_l.[v1.PodTemplateSpec.t, "ObjectMeta"])
      template_c.(v1.PodTemplateSpec.ObjectMeta') dq Hmeta_nonnull
      with "Hobjectmeta_l") as "Hobjectmeta_l".
  iCombineNamed "Htemplate_field_*" as "Htemplate_fields".
  iAssert (typed_pointsto_def template_l template_c dq)
    with "[Htemplate_fields Hobjectmeta_l]" as "Htemplate_l".
  { iNamed "Htemplate_fields". simpl. rewrite /named. iFrame. }
  iDestruct (struct_fields_combine (V:=v1.PodTemplateSpec.t)
      template_l template_c dq Htemplate_nonnull with "Htemplate_l")
    as "Htemplate_l".
  iAssert ((match template.(PodTemplateSpecV.ObjectMeta').(ObjectMetaV.Finalizers') with
    | Some finalizers' =>
        template_c.(v1.PodTemplateSpec.ObjectMeta').(v1.ObjectMeta.Finalizers') ↦*{dq} finalizers'
    | None => True
    end)%I) with "[Hfinalizers_src]" as "Hmeta_Hdeepown_finalizers_some".
  { destruct template.(PodTemplateSpecV.ObjectMeta').(ObjectMetaV.Finalizers')
      as [finalizers|] eqn:Hfinalizers_opt; simpl.
    - iFrame.
    - iClear "Hfinalizers_src". done. }
  iCombineNamed "Hmeta_*" as "Hobjectmeta".
  iAssert (ObjectMetaV.deepown
      template_c.(v1.PodTemplateSpec.ObjectMeta')
      template.(PodTemplateSpecV.ObjectMeta') dq)
    with "[Hobjectmeta]" as "Hobjectmeta".
  { rewrite /ObjectMetaV.deepown.
    iNamed "Hobjectmeta". iFrame. iFrame "%". }
  iApply ("HΦ" $! finalizers_sl).
  iFrame "Hfinalizers Hfinalizers_cap".
  iSplitL "Htemplate_l Hobjectmeta Htemplate_Hdeepown_spec".
  { iExists template_c. iFrame "Htemplate_l".
    rewrite /PodTemplateSpecV.deepown. iFrame. }
  done.
Qed.

Lemma wp_getPodsAnnotationSet template_l template dq :
  {{{ is_pkg_init controller ∗
      PodTemplateSpecV.deepown_l template_l template dq
  }}}
    @! controller.getPodsAnnotationSet #template_l
  {{{ annotations_l, RET #annotations_l;
      PodTemplateSpecV.deepown_l template_l template dq ∗
      annotations_l ↦$ default ∅
        template.(PodTemplateSpecV.ObjectMeta').(ObjectMetaV.Annotations')
  }}}.
Proof.
  wp_start as "Htemplate".
  iDestruct "Htemplate" as (template_c) "[Htemplate_l Htemplate]".
  iNamedPrefix "Htemplate" "Htemplate_".
  iNamedPrefix "Htemplate_Hdeepown_objectmeta" "Hmeta_".
  iDestruct (struct_fields_split with "Htemplate_l") as
    "[Htemplate_fields %Htemplate_nonnull]".
  iNamedPrefix "Htemplate_fields" "Htemplate_field_".
  iDestruct (struct_fields_split with "Htemplate_field_ObjectMeta") as
    "[Hmeta_fields %Hmeta_nonnull]".
  iNamedPrefix "Hmeta_fields" "Hmeta_field_".
  wp_auto_keep.
  rewrite go.make1_underlying.
  rewrite (go.is_underlying (t := labels.Set')
    (tunder := labels.Set'ⁱᵐᵖˡ)).
  wp_apply_keep wp_map_make1 as (annotations_l) "Hannotations".
  wp_pures_keep.
  iCombineNamed "Hmeta_field_*" as "Hmeta_fields".
  iAssert (typed_pointsto_def
      (template_l.[v1.PodTemplateSpec.t, "ObjectMeta"])
      template_c.(v1.PodTemplateSpec.ObjectMeta') dq)
    with "[Hmeta_fields]" as "Hobjectmeta".
  { iNamed "Hmeta_fields". simpl. rewrite /named. iFrame. }
  iDestruct (struct_fields_combine (V:=v1.ObjectMeta.t)
      (template_l.[v1.PodTemplateSpec.t, "ObjectMeta"])
      template_c.(v1.PodTemplateSpec.ObjectMeta') dq Hmeta_nonnull
      with "Hobjectmeta") as "Hobjectmeta".
  iCombineNamed "Htemplate_field_*" as "Htemplate_fields".
  iAssert (typed_pointsto_def template_l template_c dq)
    with "[Htemplate_fields Hobjectmeta]" as "Htemplate_l".
  { iNamed "Htemplate_fields". simpl. rewrite /named. iFrame. }
  iDestruct (struct_fields_combine (V:=v1.PodTemplateSpec.t)
      template_l template_c dq Htemplate_nonnull with "Htemplate_l")
    as "Htemplate_l".
  destruct template.(PodTemplateSpecV.ObjectMeta').(ObjectMetaV.Annotations')
    as [annotations|] eqn:Hannotations_opt.
  - iDestruct "Hmeta_Hdeepown_annotations_some" as (annotations_c)
      "[Hannotations_src %Hannotations_c]".
    subst annotations_c.
    wp_apply_keep (wp_map_for_range_return_func (key_type:=go.string)
      (λ (keys : list go_string) i,
        ∃ (last_value last_key : go_string),
          "v" ∷ v_ptr ↦ last_value ∗
          "k" ∷ k_ptr ↦ last_key ∗
          "desiredAnnotations" ∷ desiredAnnotations_ptr ↦ annotations_l ∗
          "Hannotations" ∷ annotations_l ↦$ map_prefix keys i annotations)%I
      with "Hannotations_src").
    { done. }
    iIntros (keys) "%Hkeys".
    iSplitL "v k desiredAnnotations Hannotations".
    { iExists ""%go, ""%go. iFrame.
      rewrite map_prefix_empty. iFrame. }
    iSplitL "".
    { iModIntro. iIntros (i key value) "%Hiter Hloop".
      destruct Hkeys as [Hkeys_dom [Hkeys_len Hkeys_nodup]].
      destruct Hiter as [Hi_bounds [Hkey_lookup Hvalue_lookup]].
      destruct Hi_bounds as [Hi_nonneg Hi_upper].
      iDestruct "Hloop" as (last_value last_key)
        "(v & k & desiredAnnotations & Hannotations)".
      wp_pures_keep. simpl subst'. wp_auto_keep.
      wp_apply_keep (wp_map_insert (K:=go_string) (V:=go_string)
        go.string annotations_l (map_prefix keys i annotations) key value
        with "Hannotations") as "Hannotations".
      iRight. iSplit; [done|].
      iExists value, key. iFrame.
      rewrite -map_prefix_insert; done. }
    iIntros "Hannotations_src Hloop".
    iDestruct "Hloop" as (last_value last_key)
      "(v & k & desiredAnnotations & Hannotations)".
    destruct Hkeys as [Hkeys_dom [Hkeys_len Hkeys_nodup]].
    rewrite (map_prefix_all keys annotations Hkeys_dom Hkeys_len).
    wp_auto_keep.
    iAssert ((match template.(PodTemplateSpecV.ObjectMeta').(ObjectMetaV.Annotations') with
      | Some annotations' => ∃ annotations_c,
          template_c.(v1.PodTemplateSpec.ObjectMeta').(v1.ObjectMeta.Annotations')
            ↦${dq} annotations_c ∗ ⌜annotations_c = annotations'⌝
      | None => True
      end)%I) with "[Hannotations_src]" as
        "Hmeta_Hdeepown_annotations_some".
    { rewrite Hannotations_opt. iExists annotations.
      iSplitL "Hannotations_src"; [iExact "Hannotations_src"|done]. }
    iCombineNamed "Hmeta_*" as "Hobjectmeta".
    iAssert (ObjectMetaV.deepown
        template_c.(v1.PodTemplateSpec.ObjectMeta')
        template.(PodTemplateSpecV.ObjectMeta') dq)
      with "[Hobjectmeta]" as "Hobjectmeta".
    { rewrite /ObjectMetaV.deepown Hannotations_opt /=.
      iNamed "Hobjectmeta". iFrame. iFrame "%". }
    iApply ("HΦ" $! annotations_l). iFrame "Hannotations".
    iExists template_c. iFrame "Htemplate_l".
    rewrite /PodTemplateSpecV.deepown. iFrame.
  - assert (template_c.(v1.PodTemplateSpec.ObjectMeta').(v1.ObjectMeta.Annotations') =
        map.nil) as Hannotations_nil.
    { apply Hmeta_Hdeepown_annotations_none. done. }
    rewrite Hannotations_nil.
    wp_apply_keep (wp_map_for_range_nil go.string go.string).
    wp_pures_keep.
    iCombineNamed "Hmeta_*" as "Hobjectmeta".
    iAssert (ObjectMetaV.deepown
        template_c.(v1.PodTemplateSpec.ObjectMeta')
        template.(PodTemplateSpecV.ObjectMeta') dq)
      with "[Hobjectmeta]" as "Hobjectmeta".
    { rewrite /ObjectMetaV.deepown Hannotations_opt /=.
      iNamed "Hobjectmeta". iFrame. iFrame "%". }
    iApply ("HΦ" $! annotations_l). iFrame "Hannotations".
    iExists template_c. iFrame "Htemplate_l".
    rewrite /PodTemplateSpecV.deepown. iFrame.
Qed.

Lemma wp_getPodsPrefix controller_name :
  {{{ is_pkg_init controller ∗
      ⌜ valid_dns1123_subdomain controller_name ⌝
  }}}
    @! controller.getPodsPrefix #controller_name
  {{{ RET #(controller_name ++ "-"%go); True }}}.
Proof. Admitted.

Lemma wp_PodControllerIndexKey namespace ownerReference owner_reference dq:
  {{{ is_pkg_init controller ∗
      ownerReference ↦{dq} owner_reference
  }}}
    @! controller.PodControllerIndexKey #namespace #ownerReference
  {{{ index_key, RET #index_key;
      ⌜ index_key = namespace ++ "/"%go ++
        owner_reference.(v1.OwnerReference.Kind') ++ "/"%go ++
        owner_reference.(v1.OwnerReference.Name') ++ "/"%go ++
        owner_reference.(v1.OwnerReference.UID')⌝
  }}}.
Proof.
  wp_start as "HownerReference".
  iDestruct (typed_pointsto_not_null with "HownerReference") as %HownerReference_nonnull.
  wp_auto_keep.
  rewrite -> bool_decide_false by exact HownerReference_nonnull.
  wp_auto_keep.
  iApply "HΦ". iPureIntro. rewrite !app_assoc. done.
Qed.

Lemma wp_PodControllerIndexKey_nil (namespace : go_string) :
  {{{ is_pkg_init controller }}}
    @! controller.PodControllerIndexKey #namespace #(null : loc)
  {{{ RET #namespace; True }}}.
Proof.
  wp_start as "Hinit".
  wp_auto_keep.
  iApply "HΦ". done.
Qed.

Lemma wp_GetPodFromTemplate template_l obj controller_ref_l template_dq
    parent_dq template parent_l parent controller_ref :
  {{{ "Hinit" ∷ is_pkg_init controller ∗
      "Htemplate" ∷ PodTemplateSpecV.deepown_l template_l template template_dq ∗
      "Hparent_meta" ∷ ObjectMetaV.deepown_l
        (KObjectV.objectmeta_ptr parent_l parent)
        (KObjectV.objectmeta parent) parent_dq ∗
      "Hcontroller_ref" ∷
        (match controller_ref with
        | Some ref => OwnerReferenceV.deepown_l controller_ref_l ref 1
        | None => ⌜ controller_ref_l = null ⌝
        end) ∗
      "%Hparent_interface" ∷
        ⌜ KObjectV.valid_interface obj parent_l parent ⌝ ∗
      "%Hparent_name_valid" ∷
        ⌜ valid_dns1123_subdomain
            (KObjectV.objectmeta parent).(ObjectMetaV.Name') ⌝
  }}}
    @! controller.GetPodFromTemplate #template_l #(interface.ok obj) #controller_ref_l
  {{{ pod_l, RET (#pod_l, #interface.nil);
      "Hpod" ∷ PodV.deepown_l pod_l
        (generated_pod template
          (KObjectV.objectmeta parent).(ObjectMetaV.Name')
          (match controller_ref with
          | Some ref => Some [ref]
          | None => None
          end)) 1 ∗
      "Htemplate" ∷
        PodTemplateSpecV.deepown_l template_l template template_dq ∗
      "Hparent_meta" ∷ ObjectMetaV.deepown_l
        (KObjectV.objectmeta_ptr parent_l parent)
        (KObjectV.objectmeta parent) parent_dq
  }}}.
Proof.
  wp_start as "H". iNamed "H".
  iDestruct "Hinit" as "#Hinit".
  iAssert (is_pkg_init code.k8s_io.api.core.v1.pkg_id.v1)
    as "#Hcore_v1".
  { iPkgInit. }
  wp_alloc controllerRef_ptr as "controllerRef".
  wp_pures_keep.
  wp_alloc parentObject_ptr as "parentObject".
  wp_pures_keep.
  wp_alloc template_ptr as "template_ptr".
  wp_auto_keep.
  wp_apply_keep (wp_getPodsLabelSet with "[$Hinit $Htemplate]").
  iIntros (labels_l) "[Htemplate Hlabels]".
  wp_auto_keep.
  wp_apply_keep (wp_getPodsFinalizers with "[$Hinit $Htemplate]").
  iIntros (finalizers_sl) "(Htemplate & Hfinalizers & Hfinalizers_cap & %Hfinalizers_not_nil)".
  wp_auto_keep.
  wp_apply_keep (wp_getPodsAnnotationSet with "[$Hinit $Htemplate]").
  iIntros (annotations_l) "[Htemplate Hannotations]".
  wp_auto_keep.
  wp_apply_keep wp_Accessor. 1: iPureIntro; done.
  wp_apply_keep (wp_GetName_deepown_kobject obj parent_l parent with "[$Hparent_meta]"). 1: done.
  iIntros "Hparent_meta".
  wp_auto_keep.
  (* Apply the spec directly to avoid [wp_apply] traversing the large continuation. *)
  remember (KObjectV.objectmeta parent).(ObjectMetaV.Name') as controller_name eqn:Hcontroller_name in *.
  wp_bind (@! controller.getPodsPrefix #controller_name)%E.
  iApply (wp_getPodsPrefix controller_name with "[]").
  { iFrame "#". done. }
  iNext. iIntros "_". subst controller_name.
  wp_auto_keep.
  wp_alloc pod_l as "Hpod_l".
  destruct controller_ref as [ref|].
  - iDestruct "Hcontroller_ref" as (ref_c) "[Href_l Href]".
    iDestruct (typed_pointsto_not_null with "Href_l") as "%Href_not_null".
    iDestruct (struct_fields_split (V:=v1.Pod.t) with "Hpod_l") as
      "[Hpod_fields %Hpod_l_not_null]".
    iNamedPrefix "Hpod_fields" "Hpod_".
    iDestruct (struct_fields_split (V:=v1.ObjectMeta.t)
      with "Hpod_ObjectMeta") as "[Hmeta_fields %Hmeta_l_not_null]".
    iNamedPrefix "Hmeta_fields" "Hmeta_".
    wp_auto_keep.
    rewrite -> bool_decide_false by exact Href_not_null.
    wp_pures_keep.
    wp_auto_keep.
    wp_apply_keep (wp_slice_literal
      (V:=v1.OwnerReference.t) (t:=v1.OwnerReference)).
    iSplitR; first done.
    iIntros (ref_sl_ptr) "[Href_sl Href_sl_cap]".
    set ref_sl : slice.t := {| slice.ptr := ref_sl_ptr;
      slice.len := W64 1; slice.cap := W64 1 |}.
    iAssert (ref_sl ↦* [ref_c])%I with "[Href_sl]" as "Href_sl".
    { iExactEq "Href_sl". f_equal. }
    subst ref_sl.
    iPoseProof (own_slice_nil (V:=v1.OwnerReference.t) (DfracOwn 1))
      as "Howners".
    iPoseProof (own_slice_cap_nil (V:=v1.OwnerReference.t)) as "Howners_cap".
    wp_auto_keep.
    wp_apply_keep (wp_slice_append
      (st:=go.SliceType v1.OwnerReference)
      (t:=v1.OwnerReference) (V:=v1.OwnerReference.t)
      slice.nil ([] : list v1.OwnerReference.t)
      {| slice.ptr := ref_sl_ptr; slice.len := W64 1;
        slice.cap := W64 1 |} [ref_c] (DfracOwn 1) with
      "[$Howners $Howners_cap $Href_sl]").
    iIntros (owners_sl)
      "(Howners_result & Howners_cap_result & Href_sl_back)".
    wp_auto_keep.
    iPoseProof (PodTemplateSpecV.deepown_l_split with "Htemplate") as
      "(%Htemplate_l_not_null & Htemplate_meta & Htemplate_spec)".
    iDestruct "Htemplate_spec" as
      (template_spec_phy) "[Htemplate_spec_ptr Htemplate_spec]".
    wp_apply_keep (wp_PodSpec__DeepCopy
      with "[$Hcore_v1 $Htemplate_spec_ptr $Htemplate_spec]").
    iIntros (spec_copy_l)
      "(Hspec_copy & Htemplate_spec_ptr & Htemplate_spec)".
    iDestruct "Hspec_copy" as (spec_c) "[Hspec_copy_l Hspec_copy]".
    wp_auto_keep.
    iAssert (PodSpecV.deepown_l
        (PodTemplateSpecV.spec_ptr template_l)
        template.(PodTemplateSpecV.Spec') template_dq)
      with "[Htemplate_spec_ptr Htemplate_spec]" as "Htemplate_spec".
    { iExists template_spec_phy. iFrame. }
    iPoseProof (PodTemplateSpecV.deepown_l_restore _ _ _
      Htemplate_l_not_null with "[$Htemplate_meta $Htemplate_spec]") as
      "Htemplate".
    iDestruct (own_map_not_nil with "Hlabels") as "%Hlabels_not_nil".
    iDestruct (own_map_not_nil with "Hannotations") as
      "%Hannotations_not_nil".
    iDestruct (own_slice_len with "Howners_result") as "%Howners_len".
    assert (owners_sl ≠ slice.nil) as Howners_not_nil.
    { intros ->. simpl in Howners_len. word. }
    iAssert (∃ labels_c,
        labels_l ↦$ labels_c ∗
        ⌜ labels_c = default ∅
          template.(PodTemplateSpecV.ObjectMeta').(ObjectMetaV.Labels') ⌝)%I
      with "[Hlabels]" as "Hlabels_some".
    { iExists _. iFrame. done. }
    iAssert (∃ annotations_c,
        annotations_l ↦$ annotations_c ∗
        ⌜ annotations_c = default ∅
          template.(PodTemplateSpecV.ObjectMeta').(ObjectMetaV.Annotations') ⌝)%I
      with "[Hannotations]" as "Hannotations_some".
    { iExists _. iFrame. done. }
    iAssert (deepown_slice OwnerReferenceV.deepown owners_sl (Some [ref]) 1)%I
      with "[Howners_result Howners_cap_result Href]" as "Howners_deepown".
    { rewrite /deepown_slice. iSplit.
      { iPureIntro. split; [contradiction|discriminate]. }
      iExists [ref_c]. simpl. iFrame. }
    iRename "Hfinalizers" into "Hfinalizers_some".
    set pod_meta_c : v1.ObjectMeta.t :=
      v1.ObjectMeta.mk ""%go
        ((KObjectV.objectmeta parent).(ObjectMetaV.Name') ++ "-"%go)
        ""%go ""%go ""%go ""%go (W64 0) (zero_val v1.Time.t)
        null null labels_l annotations_l owners_sl finalizers_sl slice.nil.
    iCombineNamed "Hmeta_*" as "Hmeta_fields".
    iAssert (typed_pointsto_def (PodV.objectmeta_ptr pod_l)
        pod_meta_c (DfracOwn 1))%I with "[Hmeta_fields]" as "Hmeta_fields".
    { rewrite /PodV.objectmeta_ptr /pod_meta_c /=.
      iNamed "Hmeta_fields". iFrame. }
    iDestruct (struct_fields_combine (V:=v1.ObjectMeta.t)
      (PodV.objectmeta_ptr pod_l) pod_meta_c (DfracOwn 1)
      Hmeta_l_not_null with "Hmeta_fields") as "Hmeta_l".
    iPoseProof (TimeV.deepown_zero (Σ:=Σ) (DfracOwn 1)) as "Htime".
    iAssert (deepown_slice ManagedFieldsEntryV.deepown slice.nil None 1)%I as "Hmanaged".
    { iApply deepown_slice_nil. }
    iAssert (ObjectMetaV.deepown pod_meta_c
        (generated_pod_meta template
          (KObjectV.objectmeta parent).(ObjectMetaV.Name') (Some [ref])) 1)%I
      with "[Htime Hlabels_some Hannotations_some Howners_deepown Hfinalizers_some Hfinalizers_cap Hmanaged]"
      as "Hmeta".
    { rewrite /ObjectMetaV.deepown /generated_pod_meta /pod_meta_c /=.
      iFrame "Htime Hlabels_some Hannotations_some Howners_deepown Hfinalizers_some Hfinalizers_cap Hmanaged".
      iPureIntro. Timeout 10 naive_solver. }
    iAssert (ObjectMetaV.deepown_l (PodV.objectmeta_ptr pod_l)
        (generated_pod_meta template
          (KObjectV.objectmeta parent).(ObjectMetaV.Name') (Some [ref])) 1)%I
      with "[Hmeta_l Hmeta]" as "Hpod_meta".
    { iExists pod_meta_c. iFrame. }
    iAssert (PodSpecV.deepown_l (PodV.spec_ptr pod_l)
        template.(PodTemplateSpecV.Spec') 1)%I
      with "[Hpod_Spec Hspec_copy]" as "Hpod_spec".
    { iExists spec_c. iFrame. }
    iPoseProof (PodStatusV.deepown_zero (Σ:=Σ) (DfracOwn 1)) as
      "Hstatus".
    iAssert (PodStatusV.deepown_l (PodV.status_ptr pod_l)
        PodStatusV.zero 1)%I with "[Hpod_Status Hstatus]" as "Hpod_status".
    { iExists (zero_val v1.PodStatus.t). iFrame. done. }
    iPoseProof (PodV.deepown_l_restore pod_l
      (generated_pod template
        (KObjectV.objectmeta parent).(ObjectMetaV.Name') (Some [ref])) 1
      Hpod_l_not_null with
      "[$Hpod_TypeMeta $Hpod_meta $Hpod_spec $Hpod_status]") as "Hpod".
    iApply ("HΦ" $! pod_l).
    iFrame "Hpod Htemplate Hparent_meta".
  - iDestruct "Hcontroller_ref" as "%Hcontroller_ref_l".
    subst controller_ref_l.
    wp_auto_keep.
    iDestruct (struct_fields_split (V:=v1.Pod.t) with "Hpod_l") as
      "[Hpod_fields %Hpod_l_not_null]".
    iNamedPrefix "Hpod_fields" "Hpod_".
    iDestruct (struct_fields_split (V:=v1.ObjectMeta.t)
      with "Hpod_ObjectMeta") as "[Hmeta_fields %Hmeta_l_not_null]".
    iNamedPrefix "Hmeta_fields" "Hmeta_".
    iPoseProof (PodTemplateSpecV.deepown_l_split with "Htemplate") as
      "(%Htemplate_l_not_null & Htemplate_meta & Htemplate_spec)".
    iDestruct "Htemplate_spec" as
      (template_spec_phy) "[Htemplate_spec_ptr Htemplate_spec]".
    wp_apply_keep (wp_PodSpec__DeepCopy
      with "[$Hcore_v1 $Htemplate_spec_ptr $Htemplate_spec]").
    iIntros (spec_copy_l)
      "(Hspec_copy & Htemplate_spec_ptr & Htemplate_spec)".
    iDestruct "Hspec_copy" as (spec_c) "[Hspec_copy_l Hspec_copy]".
    wp_auto_keep.
    iAssert (PodSpecV.deepown_l
        (PodTemplateSpecV.spec_ptr template_l)
        template.(PodTemplateSpecV.Spec') template_dq)
      with "[Htemplate_spec_ptr Htemplate_spec]" as "Htemplate_spec".
    { iExists template_spec_phy. iFrame. }
    iPoseProof (PodTemplateSpecV.deepown_l_restore _ _ _
      Htemplate_l_not_null with "[$Htemplate_meta $Htemplate_spec]") as
      "Htemplate".
    iDestruct (own_map_not_nil with "Hlabels") as "%Hlabels_not_nil".
    iDestruct (own_map_not_nil with "Hannotations") as
      "%Hannotations_not_nil".
    iAssert (∃ labels_c,
        labels_l ↦$ labels_c ∗
        ⌜ labels_c = default ∅
          template.(PodTemplateSpecV.ObjectMeta').(ObjectMetaV.Labels') ⌝)%I
      with "[Hlabels]" as "Hlabels_some".
    { iExists _. iFrame. done. }
    iAssert (∃ annotations_c,
        annotations_l ↦$ annotations_c ∗
        ⌜ annotations_c = default ∅
          template.(PodTemplateSpecV.ObjectMeta').(ObjectMetaV.Annotations') ⌝)%I
      with "[Hannotations]" as "Hannotations_some".
    { iExists _. iFrame. done. }
    iRename "Hfinalizers" into "Hfinalizers_some".
    set pod_meta_c : v1.ObjectMeta.t :=
      v1.ObjectMeta.mk ""%go
        ((KObjectV.objectmeta parent).(ObjectMetaV.Name') ++ "-"%go)
        ""%go ""%go ""%go ""%go (W64 0) (zero_val v1.Time.t)
        null null labels_l annotations_l slice.nil finalizers_sl slice.nil.
    iCombineNamed "Hmeta_*" as "Hmeta_fields".
    iAssert (typed_pointsto_def (PodV.objectmeta_ptr pod_l)
        pod_meta_c (DfracOwn 1))%I with "[Hmeta_fields]" as "Hmeta_fields".
    { rewrite /PodV.objectmeta_ptr /pod_meta_c /=.
      iNamed "Hmeta_fields". iFrame. }
    iDestruct (struct_fields_combine (V:=v1.ObjectMeta.t)
      (PodV.objectmeta_ptr pod_l) pod_meta_c (DfracOwn 1)
      Hmeta_l_not_null with "Hmeta_fields") as "Hmeta_l".
    iPoseProof (TimeV.deepown_zero (Σ:=Σ) (DfracOwn 1)) as "Htime".
    iAssert (deepown_slice ManagedFieldsEntryV.deepown slice.nil None 1)%I as "Hmanaged".
    { iApply deepown_slice_nil. }
    iAssert (deepown_slice OwnerReferenceV.deepown slice.nil None 1)%I as "Howners_deepown".
    { iApply deepown_slice_nil. }
    iAssert (ObjectMetaV.deepown pod_meta_c
        (generated_pod_meta template
          (KObjectV.objectmeta parent).(ObjectMetaV.Name') None) 1)%I
      with "[Htime Hlabels_some Hannotations_some Hfinalizers_some Hfinalizers_cap
        Hmanaged Howners_deepown]"
      as "Hmeta".
    { rewrite /ObjectMetaV.deepown /generated_pod_meta /pod_meta_c /=.
      iFrame "Htime Hlabels_some Hannotations_some Hfinalizers_some Hfinalizers_cap
        Hmanaged Howners_deepown".
      iPureIntro. Timeout 10 naive_solver. }
    iAssert (ObjectMetaV.deepown_l (PodV.objectmeta_ptr pod_l)
        (generated_pod_meta template
          (KObjectV.objectmeta parent).(ObjectMetaV.Name') None) 1)%I
      with "[Hmeta_l Hmeta]" as "Hpod_meta".
    { iExists pod_meta_c. iFrame. }
    iAssert (PodSpecV.deepown_l (PodV.spec_ptr pod_l)
        template.(PodTemplateSpecV.Spec') 1)%I
      with "[Hpod_Spec Hspec_copy]" as "Hpod_spec".
    { iExists spec_c. iFrame. }
    iPoseProof (PodStatusV.deepown_zero (Σ:=Σ) (DfracOwn 1)) as
      "Hstatus".
    iAssert (PodStatusV.deepown_l (PodV.status_ptr pod_l)
        PodStatusV.zero 1)%I with "[Hpod_Status Hstatus]" as "Hpod_status".
    { iExists (zero_val v1.PodStatus.t). iFrame. done. }
    iPoseProof (PodV.deepown_l_restore pod_l
      (generated_pod template
        (KObjectV.objectmeta parent).(ObjectMetaV.Name') None) 1
      Hpod_l_not_null with
      "[$Hpod_TypeMeta $Hpod_meta $Hpod_spec $Hpod_status]") as "Hpod".
    iApply ("HΦ" $! pod_l).
    iFrame "Hpod Htemplate Hparent_meta".
Qed.

End proof.
