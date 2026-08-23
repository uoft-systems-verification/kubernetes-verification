From New.proof Require Import prelude empty_ffi.
From New.golang.theory Require Export map.
From iris.algebra Require Import gmap.

Section proof.
Context `{hG: !heapGS Σ} `{!ffi_semantics _ _}.
Context {sem : go.Semantics}.
Local Set Default Proof Using "All".

Context `[!ZeroVal K] `[!EqDecision K] `[!Countable K] `[!ZeroVal V]
  `[!go.IntoValInj K].

Lemma wp_map_len_resolved key_type elem_type mref (m : gmap K V) dq
    `{!TypedPointsto K} `{!IntoValTyped K key_type} :
  {{{ mref ↦${dq} m }}}
    #(functions go.len [go.MapType key_type elem_type]) #mref
  {{{ RET #(W64 (size m)); mref ↦${dq} m }}}.
Proof.
  wp_start as "Hm".
  rewrite own_map_unseal. iNamed "Hm".
  unshelve epose proof (go.is_map_domain_exists mv mp His_map) as
    [ks Hks_domain].
  eapply go.is_map_domain_pure in Hks_domain as Hks; last done.
  destruct Hks as [Hks_nodup Hks].
  assert (Forall (λ kv, ∃ (k : K), kv = #k) ks) as Heq.
  { rewrite Forall_forall. intros kv.
    intros Hkv. specialize (Hks kv). specialize (Hdom kv).
    rewrite -Hks in Hkv. apply Hdom in Hkv. done. }
  apply Forall_exists_Forall2_l in Heq as [keys Heq].
  apply Forall2_fmap_2 in Heq. rewrite -list_eq_Forall2 in Heq.
  rewrite list_fmap_id in Heq. subst ks.
  assert (Hkeys_dom : list_to_set keys = dom m).
  { rewrite sets.set_eq. intros k.
    rewrite elem_of_list_to_set.
    specialize (Hks #k). specialize (Hagree k).
    rewrite list_elem_of_fmap_inj in Hks.
    rewrite -Hks Hagree elem_of_dom.
    destruct (m !! k); split; eauto; intros ?; done. }
  assert (Hkeys_len : length keys = size m).
  { apply NoDup_fmap in Hks_nodup; last tc_solve.
    rewrite <- (size_list_to_set (C:=gset K)); last done.
    rewrite Hkeys_dom size_dom. done. }
  wp_apply (_internal_wp_untyped_read with "[Hown]") as "Hown".
  { iExact "Hown". }
  pose proof (go.internal_map_length_step_pure mv ((λ k : K, #k) <$> keys)
    Hks_domain) as Hlenstep.
  wp_auto.
  iEval (rewrite -Hkeys_len) in "HΦ".
  rewrite map_length.
  iApply "HΦ".
  iExists mv, mp. iFrame "Hown". iFrame "%".
Qed.

Lemma wp_map_len key_type elem_type mref (m : gmap K V) dq
    `{!TypedPointsto K} `{!IntoValTyped K key_type} :
  {{{ mref ↦${dq} m }}}
    (FuncResolve go.len [go.MapType key_type elem_type] #()) #mref
  {{{ RET #(W64 (size m)); mref ↦${dq} m }}}.
Proof.
  wp_start as "Hm". wp_pures.
  wp_apply (wp_map_len_resolved with "Hm").
  iIntros "Hm". iApply "HΦ". iFrame.
Qed.

Lemma wp_map_len_nil_resolved key_type elem_type :
  {{{ True }}}
    #(functions go.len [go.MapType key_type elem_type]) #map.nil
  {{{ RET #(W64 0); True }}}.
Proof.
  (* TODO: Perennial's [MapSemantics] currently has no premise establishing an
     [is_map_domain] for [map.nil].  Add the corresponding nil-map reduction
     upstream, then replace this narrow Go-language compatibility boundary. *)
Admitted.

End proof.
