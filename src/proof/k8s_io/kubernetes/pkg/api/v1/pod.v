From New.proof Require Import prelude empty_ffi.
From New.proof.k8s_io.kubernetes.pkg.api.v1 Require Export pod_init.
From New.proof.kubernetes_types Require Export prelude.

(* [pod] alone is ambiguous once kubernetes_types is imported. *)
Module podutil := code.k8s_io.kubernetes.pkg.api.v1.pod.pod.
Notation podutil_pkg := code.k8s_io.kubernetes.pkg.api.v1.pod.pkg_id.pod.

Section proof.
Context `{hG: !heapGS Σ} `{!ffi_semantics _ _}.
(* The object-type instances are section variables, as in controller.v, so
   callers can use these specs with the instances of their own package. *)
Context {sem : go.Semantics} {package_sem : podutil.Assumptions}
  {pod_meta_v1_sem : code.k8s_io.apimachinery.pkg.apis.meta.v1.v1.Assumptions}
  {pod_core_v1_sem : code.k8s_io.api.core.v1.v1.Assumptions}
  {pod_apps_v1_sem : code.k8s_io.api.apps.v1.v1.Assumptions}.
Collection W := sem + package_sem.
Local Set Default Proof Using "All".

#[local] Existing Instance pod_meta_v1_sem.
#[local] Existing Instance pod_core_v1_sem.

Definition condition_has_type (ty : go_string) (c : v1.PodCondition.t) : Prop :=
  c.(v1.PodCondition.Type') = ty.

#[global] Instance condition_has_type_dec ty c : Decision (condition_has_type ty c).
Proof. rewrite /condition_has_type. apply _. Defined.

(* The pointer [GetPodConditionFromList] returns: the address of the first
   condition of type [ty] in the slice, or nil. *)
Definition condition_ref (sl : slice.t) (cs : list v1.PodCondition.t) (ty : go_string) : loc :=
  match list_find (condition_has_type ty) cs with
  | Some (j, _) => slice_index_ref v1.PodCondition.t (Z.of_nat j) sl
  | None => null
  end.

(* Readiness of a Go conditions list, as computed by [IsPodReadyConditionTrue]. *)
Definition conditions_ready (cs : list v1.PodCondition.t) : bool :=
  match list_find (condition_has_type "Ready"%go) cs with
  | Some (_, c) => bool_decide (c.(v1.PodCondition.Status') = "True"%go)
  | None => false
  end.

Lemma conditions_ready_view (s : PodStatusV.t) cs :
  s.(PodStatusV.Conditions') = PodConditionV.of_go <$> cs →
  PodStatusV.ready s = conditions_ready cs.
Proof.
  intros Hconds.
  rewrite /PodStatusV.ready /conditions_ready Hconds list_find_fmap.
  rewrite /condition_has_type /compose /=.
  by destruct (list_find _ cs) as [[j c]|].
Qed.

Lemma wp_GetPodConditionFromList (sl : slice.t) (cs : list v1.PodCondition.t) dq (ty : go_string) :
  {{{ is_pkg_init podutil_pkg ∗
      sl ↦*{dq} cs
  }}}
    @! podutil.GetPodConditionFromList #sl #ty
  {{{ (i : w64), RET (#i, #(condition_ref sl cs ty)); sl ↦*{dq} cs }}}.
Proof.
  wp_start as "Hsl".
  iDestruct (own_slice_len with "Hsl") as %(Hlen1 & Hlen2).
  wp_auto.
  wp_if_destruct.
  { (* A nil slice holds no conditions. *)
    destruct cs as [|c cs]; last (simpl in Hlen1; rewrite /slice.nil /= in Hlen1; word).
    replace null with (condition_ref slice.nil [] ty) by done.
    by iApply ("HΦ" with "Hsl"). }
  (* The range loop's own counter shares the name "i" with the user variable. *)
  wp_alloc j_ptr as "j". wp_auto.
  set I := (∃ (j k : w64),
    "j" ∷ j_ptr ↦ j ∗
    "i" ∷ i_ptr ↦ k ∗
    "Hsl" ∷ sl ↦*{dq} cs ∗
    "%Hprefix" ∷ ⌜ Forall (λ c, ¬ condition_has_type ty c) (take (sint.nat j) cs) ⌝ ∗
    "%Hj" ∷ ⌜ 0 ≤ sint.Z j ≤ sint.Z (slice.len sl) ⌝)%I.
  iAssert I with "[i j Hsl]" as "Hloop".
  { iExists (W64 0), (W64 0). iFrame. rewrite take_0. iPureIntro. split; [constructor|word]. }
  wp_for "Hloop".
  wp_if_destruct.
  - list_elem cs (sint.Z j) as this.
    rewrite decide_True; first (pose proof (lookup_lt_Some _ _ _ Hthis_lookup); word).
    wp_apply (wp_load_slice_index with "[$Hsl]"); [word| |].
    { iPureIntro. exact Hthis_lookup. }
    iIntros "Hsl". wp_auto.
    rewrite decide_True; first word.
    iDestruct (own_slice_elem_acc (sint.Z j) with "Hsl") as "[Hthis Hsl_restore]"; [word|exact Hthis_lookup|].
    wp_auto.
    iDestruct ("Hsl_restore" with "Hthis") as "Hsl".
    rewrite list_insert_id //.
    destruct (decide (this.(v1.PodCondition.Type') = ty)) as [Hty|Hty].
    + (* The first condition of type [ty]. *)
      rewrite bool_decide_true //. wp_auto. rewrite decide_True; first word.
      wp_auto. iApply wp_for_post_return. wp_auto.
      assert (condition_ref sl cs ty = slice_index_ref v1.PodCondition.t (sint.Z j) sl) as ->.
      { rewrite /condition_ref.
        replace (list_find (condition_has_type ty) cs) with (Some (sint.nat j, this)).
        { f_equal. word. }
        symmetry. apply list_find_Some. split_and!; [done|done|].
        intros k' y Hy Hk'.
        rewrite Forall_lookup in Hprefix. apply (Hprefix k').
        rewrite lookup_take_lt //. }
      by iApply ("HΦ" with "Hsl").
    + rewrite bool_decide_false //. wp_auto.
      iApply wp_for_post_do. wp_auto.
      iFrame "HΦ conditionType conditions".
      iExists (word.add j (W64 1)), j. iFrame.
      assert (sint.nat (word.add j (W64 1)) = S (sint.nat j)) as -> by word.
      rewrite (take_S_r _ _ this) // Forall_app Forall_singleton.
      iPureIntro. split; last word. split; first done. rewrite /condition_has_type. done.
  - (* No condition of type [ty]. *)
    assert (take (sint.nat j) cs = cs) as Htake by (apply take_ge; word).
    rewrite Htake in Hprefix.
    replace null with (condition_ref sl cs ty).
    { by iApply ("HΦ" with "Hsl"). }
    rewrite /condition_ref. by rewrite (proj2 (list_find_None _ _) Hprefix).
Qed.

Lemma wp_GetPodCondition (status_l : loc) (status : v1.PodStatus.t) dq_l (cs : list v1.PodCondition.t) dq
    (ty : go_string) :
  {{{ is_pkg_init podutil_pkg ∗
      status_l ↦{dq_l} status ∗
      status.(v1.PodStatus.Conditions') ↦*{dq} cs
  }}}
    @! podutil.GetPodCondition #status_l #ty
  {{{ (i : w64), RET (#i, #(condition_ref status.(v1.PodStatus.Conditions') cs ty));
      status_l ↦{dq_l} status ∗ status.(v1.PodStatus.Conditions') ↦*{dq} cs
  }}}.
Proof.
  wp_start as "[Hstatus Hsl]".
  iDestruct (typed_pointsto_not_null with "Hstatus") as %Hnot_null.
  wp_auto.
  rewrite bool_decide_false //. wp_auto.
  wp_apply (wp_GetPodConditionFromList with "[$Hsl]").
  iIntros (i) "Hsl". wp_auto.
  iApply "HΦ". iFrame.
Qed.

Lemma wp_GetPodReadyCondition (status : v1.PodStatus.t) (cs : list v1.PodCondition.t) dq :
  {{{ is_pkg_init podutil_pkg ∗
      status.(v1.PodStatus.Conditions') ↦*{dq} cs
  }}}
    @! podutil.GetPodReadyCondition #status
  {{{ RET #(condition_ref status.(v1.PodStatus.Conditions') cs "Ready"%go);
      status.(v1.PodStatus.Conditions') ↦*{dq} cs
  }}}.
Proof.
  wp_start as "Hsl". wp_auto.
  wp_apply (wp_GetPodCondition with "[$status $Hsl]").
  iIntros (i) "[status Hsl]". wp_auto.
  by iApply "HΦ".
Qed.

Lemma wp_IsPodReadyConditionTrue (status : v1.PodStatus.t) (cs : list v1.PodCondition.t) dq :
  {{{ is_pkg_init podutil_pkg ∗
      status.(v1.PodStatus.Conditions') ↦*{dq} cs
  }}}
    @! podutil.IsPodReadyConditionTrue #status
  {{{ RET #(conditions_ready cs); status.(v1.PodStatus.Conditions') ↦*{dq} cs }}}.
Proof.
  wp_start as "Hsl". wp_auto.
  wp_apply (wp_GetPodReadyCondition with "[$Hsl]").
  iIntros "Hsl". wp_auto.
  rewrite /conditions_ready /condition_ref.
  destruct (list_find (condition_has_type "Ready"%go) cs) as [[j c]|] eqn:Hfind.
  - apply list_find_Some in Hfind as (Hlookup & _ & _).
    iDestruct (own_slice_elem_acc (Z.of_nat j) with "Hsl") as "[Hc Hrestore]";
      [lia|rewrite Nat2Z.id //|].
    iDestruct (typed_pointsto_not_null with "Hc") as %Hnot_null.
    rewrite (bool_decide_false (_ = null) Hnot_null). wp_auto.
    iDestruct ("Hrestore" with "Hc") as "Hsl".
    rewrite Nat2Z.id list_insert_id //.
    by iApply "HΦ".
  - (* No ready condition: the nil check short-circuits. *)
    rewrite bool_decide_true //. wp_auto.
    by iApply "HΦ".
Qed.

(* [IsPodReady] computes [PodStatusV.ready] and leaves the pod unchanged. *)
Lemma wp_IsPodReady (pod_l : loc) (p : PodV.t) dq :
  {{{ is_pkg_init podutil_pkg ∗
      PodV.deepown_l pod_l p dq
  }}}
    @! podutil.IsPodReady #pod_l
  {{{ RET #(PodStatusV.ready p.(PodV.Status')); PodV.deepown_l pod_l p dq }}}.
Proof.
  wp_start as "(%c & Hl & Hc)". iNamed "Hc".
  iDestruct "Hdeepown_podstatus" as (cs) "[Hsl %Hconds]".
  wp_auto.
  wp_apply (wp_IsPodReadyConditionTrue with "[$Hsl]").
  iIntros "Hsl".
  rewrite (conditions_ready_view _ _ Hconds). wp_auto.
  iApply "HΦ". iExists c. iFrame "∗ %".
Qed.


(* Trusted: [IsPodTerminal] checks [status.phase] through the untranslated
   [IsPodPhaseTerminal], and [PodStatusV] does not represent the phase. The spec
   only assumes that it returns some boolean and leaves the pod unchanged; it
   can be proven once the phase is represented. *)
Lemma wp_IsPodTerminal (pod_l : loc) (p : PodV.t) dq :
  {{{ is_pkg_init podutil_pkg ∗
      PodV.deepown_l pod_l p dq
  }}}
    @! podutil.IsPodTerminal #pod_l
  {{{ (b : bool), RET #b; PodV.deepown_l pod_l p dq }}}.
Proof. Admitted.

(* Trusted: availability also compares the ready condition's transition time
   with [now], and the time operations it uses (metav1.Time.IsZero,
   time.Time.Add and time.Time.Compare) are not modelled. This spec only
   assumes that the helper terminates, returns some boolean, and leaves the pod
   unchanged. Readiness alone is proven: see [wp_IsPodReady]. *)
Lemma wp_IsPodAvailable pod_l pod dq (min_ready_seconds : w32) (now : val) :
  {{{ is_pkg_init podutil_pkg ∗
      PodV.deepown_l pod_l pod dq
  }}}
    @! podutil.IsPodAvailable #pod_l #min_ready_seconds now
  {{{ (b : bool), RET #b; PodV.deepown_l pod_l pod dq }}}.
Proof. Admitted.

End proof.
