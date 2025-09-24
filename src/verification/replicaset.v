From verification Require Import prelude empty_ffi.
From verification Require Import replicaset_init.
Require Import New.code.k8s_io.api.core.v1.
Require Import New.code.k8s_io.kubernetes.pkg.controller.
(* From New.code.k8s_io.api.core.v1 Require Import Pod. *)

Section proof.
Context `{hG: !heapGS Σ}.
Context `{!globalsGS Σ} {go_ctx: GoContext}.


Lemma wp_PodKey (pod: loc) (name namespace: go_string) :
  {{{ is_pkg_init replicaset ∗
      "name" :: pod ↦s[v1.Pod :: "Name"] name ∗
      "namespace" :: pod ↦s[v1.Pod :: "Namespace"] namespace }}}
    @! controller.PodKey #pod
  {{{ RET #(namespace ++ "/" ++ name)%go;
      pod ↦s[v1.Pod :: "Name"] name ∗
      pod ↦s[v1.Pod :: "Namespace"] namespace }}}.
Proof.
Admitted.

Lemma wp_getPodKeys (pods: slice.t) (pods_els: list loc) :
  {{{ is_pkg_init replicaset ∗
      "pods" :: pods ↦* pods_els ∗
      "pods_els" :: ([∗ list] pod_l ∈ pods_els,
         ∃ (name namespace: go_string),
          "name" :: pod_l ↦s[v1.Pod :: "Name"] name ∗
          "namespace" :: pod_l ↦s[v1.Pod :: "Namespace"] namespace) }}}
    @! replicaset.getPodKeys #pods
    {{{ (keys: slice.t) (keys_els: list go_string), RET #keys;
      pods ↦* pods_els ∗
      keys ↦* keys_els ∗
      ⌜length keys_els = length pods_els⌝ ∗
      ([∗ list] i ↦ pod_l; key ∈ pods_els; keys_els,
         ∃ (name namespace: go_string),
           pod_l ↦s[v1.Pod :: "Name"] name ∗
           pod_l ↦s[v1.Pod :: "Namespace"] namespace ∗
           ⌜key = (namespace ++ "/" ++ name)%go⌝) }}}.
Proof.
  wp_start as "H". iNamed "H".
  iDestruct (own_slice_len with "pods") as %Hlen.
  wp_alloc pods_ptr as "pods_ptr". wp_auto.
  iRename "podKeys" into "podKeys_ptr".
  wp_apply (wp_slice_make3 (V:=go_string)).
  {  word. }
  iIntros (keys) "(keys & own_keys_cap & %Heq)". wp_auto.
  iRename "pod" into "pod_ptr".
  (* unfold slice.for_range to a loop *)
  Transparent slice.for_range. wp_call.
  wp_alloc i_ptr as "i_ptr".
  wp_pures.

  set I := (
    ∃ (i: w64) (keys: slice.t) (p: loc) (keys_els: list go_string),
      "i_ptr" :: i_ptr ↦ i ∗
      "podKeys_ptr" :: podKeys_ptr ↦ keys ∗
      "pod_ptr" :: pod_ptr ↦ p ∗
      "keys" :: keys ↦* keys_els ∗
      "own_keys_cap" :: own_slice_cap go_string keys (DfracOwn 1) ∗
      "%Hrange" :: ⌜0 ≤ sint.Z i ≤ sint.Z (slice.len_f pods)⌝ ∗
      "%Hlen_keys" :: ⌜length keys_els = uint.nat i⌝ ∗
      "Hprei" :: ([∗ list] j ↦ pod_l; key ∈ take (uint.nat i) pods_els; keys_els,
        ∃ (name namespace: go_string),
           pod_l ↦s[v1.Pod :: "Name"] name ∗
           pod_l ↦s[v1.Pod :: "Namespace"] namespace ∗
           ⌜key = (namespace ++ "/" ++ name)%go⌝) ∗
      "Hposti" :: ([∗ list] pod_l ∈ drop (uint.nat i) pods_els,
                    ∃ (name namespace: go_string),
                      pod_l ↦s[v1.Pod :: "Name"] name ∗
                      pod_l ↦s[v1.Pod :: "Namespace"] namespace)
  )%I.

  iAssert (I) with "[podKeys_ptr pod_ptr keys own_keys_cap pods_els i_ptr]" as "Hinv".
  {
    iExists (W64 0), keys, (default_val loc), [].
    iFrame "podKeys_ptr pod_ptr keys own_keys_cap i_ptr".
    iSplit; [iPureIntro; word|].
    iSplit; [iPureIntro; done|].
    iSplit.
    - rewrite take_0. by rewrite big_sepL2_nil.
    - rewrite drop_0. iFrame "pods_els".
  }

  wp_for "Hinv".
  iDestruct (own_slice_len with "pods") as %Hslicelen.

  wp_if_destruct; try wp_auto.
  - wp_bind (![# ptrT] (slice.elem_ref (# ptrT) (# pods) (# i)))%E.
    wp_pure.
    { word. }
    assert ((sint.nat i < length pods_els)%nat) as Hi by word.
    pose proof (list_lookup_lt pods_els (sint.nat i) Hi) as [x Hx].
    assert (uint.nat i = sint.nat i) as Hui by word.
    assert (pods_els !! uint.nat i = Some x) as Hix by (rewrite Hui; exact Hx).

    wp_apply (wp_load_slice_elem with "[$pods]") as "pods_i".
    { word. }
    { iPureIntro. exact Hx. }

    (* split "drop (uint.nat i) pods_els" into "x" and "drop (uint.nat (word.add i (W64 1))) pods_els" *)
    iAssert (
      (([∗ list] pod_l ∈ drop (uint.nat (word.add i (W64 1))) pods_els,
        ∃ name namespace : go_string,
          pod_l ↦s[v1.Pod :: "Name"] name ∗
          pod_l ↦s[v1.Pod :: "Namespace"] namespace) ∗
        (∃ name : go_string, x ↦s[v1.Pod :: "Name"] name) ∗
        (∃ namespace : go_string, x ↦s[v1.Pod :: "Namespace"] namespace))%I
    ) with "[Hposti]" as "(Hpostiaddone & ((%name & name) & (%namespace & namespace)))".
    {
      iEval (rewrite (drop_S _ _ _ Hix)) in "Hposti".
      iDestruct "Hposti" as "[Hhead Htail]".
      assert (uint.nat (word.add i (W64 1)) = S (uint.nat i)) as Hsucc by word.
      iEval (rewrite -Hsucc) in "Htail".
      iFrame.
      iDestruct "Hhead" as (name namespace) "[Hname Hnamespace]".
      iSplitL "Hname".
      { iExists name. iExact "Hname". }
      { iExists namespace. iExact "Hnamespace". }
    }

    wp_apply (wp_PodKey with "[$name $namespace]") as "[name namespace]".
    wp_apply (wp_slice_literal) as "%sl sl".
    wp_apply (wp_slice_append with "[$keys $own_keys_cap $sl]") as "%new_keys (new_keys & own_new_keys_cap & sl)".
    (* loop body finished here *)
    set new_keys_els := keys_els ++ [(namespace ++ "/" ++ name)%go].
    (* combine "x" and "take (uint.nat i) pods_els" into "take (uint.nat (word.add i (W64 1)))" *)
    iAssert (
      ([∗ list] pod_l;key ∈ take (uint.nat (word.add i (W64 1))) pods_els;new_keys_els,
        ∃ name namespace : go_string,
          pod_l ↦s[v1.Pod :: "Name"] name ∗
          pod_l ↦s[v1.Pod :: "Namespace"] namespace ∗
          ⌜key = namespace ++ "/"%go ++ name⌝)%I
    ) with "[Hprei name namespace]" as "Hpreiaddone".
    {
      assert (uint.nat (word.add i (W64 1)) = S (uint.nat i)) as Hsucc by word.
      rewrite Hsucc.
      rewrite (take_S_r _ _ _ Hix).
      rewrite big_sepL2_app.
      iApply "Hprei".
      simpl.
      iSplit; [|done].
      iExists name, namespace.
      iFrame.
      iPureIntro. reflexivity.
    }
    iApply wp_for_post_do. wp_auto.
    iFrame "pods_i pods_ptr HΦ".
    (* Prove the loop invariant *)
    iExists (word.add i (W64 1)), new_keys, x, new_keys_els.
    iFrame.
    iSplit; iPureIntro.
    + word.
    + rewrite app_length Hlen_keys /=.
      word.
  - iApply "HΦ".
    iFrame.
    iSplit.
    { iPureIntro. word. }
    assert (length pods_els ≤ uint.nat i).
    { word. }
    rewrite take_ge.
    { word. }
    iFrame.
Qed.


End proof.
