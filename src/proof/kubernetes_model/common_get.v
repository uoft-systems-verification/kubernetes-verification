From New.proof Require Import prelude empty_ffi.
From New.proof.kubernetes_model Require Export common.

(* Lightweight infrastructure shared by the ordinary and reserved Get
   variants. *)

Section proof.
Context `{hG: !heapGS Σ} `{!ffi_semantics _ _}.
Context {sem : go.Semantics} {package_sem : apimodel.Assumptions}.
Context `{!kubernetesModelG Σ}.
Local Set Default Proof Using "All".

Lemma wp_map_lookup2_KKey elem_type mref (m : gmap KKey.t interface.t) k dq :
  {{{ mref ↦${dq} m }}}
    map.lookup2 apimodel.KKey elem_type #mref #k
  {{{ RET (#(default (zero_val interface.t) (m !! k)), #(bool_decide (is_Some (m !! k)))); mref ↦${dq} m }}}.
Proof.
  wp_start as "Hm".
  rewrite own_map_unseal /own_map_def. iNamed "Hm".
  iDestruct (heap_pointsto_non_null with "Hown") as "%Hnotnil".
  replace (bool_decide (apimodel.KKey.Kind' k = apimodel.KKey.Kind' k)) with true by
    (symmetry; apply bool_decide_eq_true_2; done).
  wp_auto.
  replace (bool_decide (apimodel.KKey.Name' k = apimodel.KKey.Name' k)) with true by
    (symmetry; apply bool_decide_eq_true_2; done).
  wp_auto.
  replace (bool_decide (apimodel.KKey.Namespace' k = apimodel.KKey.Namespace' k)) with true by
    (symmetry; apply bool_decide_eq_true_2; done).
  replace (bool_decide (mref = map.nil)) with false by
    (symmetry; apply bool_decide_eq_false_2; intros ->; apply Hnotnil; done).
  wp_auto.
  wp_apply (_internal_wp_untyped_read with "Hown") as "Hown".
  erewrite go.map_lookup_pure; last done.
  pose proof (Hagree k) as Heq. rewrite Heq. destruct (m !! k); wp_auto.
  - iApply "HΦ". iFrame "∗#%".
  - iApply "HΦ". iFrame "∗#%".
Qed.

End proof.
