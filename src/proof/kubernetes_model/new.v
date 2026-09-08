From New.proof.kubernetes_model Require Export common.
From New.proof Require Import prelude empty_ffi.

Section proof.
Context `{hG: !heapGS Σ} `{!ffi_semantics _ _}.
Context {sem : go.Semantics} {package_sem : apimodel.Assumptions}.
Context `{!kubernetesModelG Σ}.
Local Set Default Proof Using "All".

Lemma wp_NewState :
  {{{ is_pkg_init apimodel }}}
    @! apimodel.NewState #()
  {{{ l γ, RET #l; is_kubernetes γ l }}}.
Proof.
  wp_start as "#Hpkg".
  wp_bind (#(functions go.make1
    [go.MapType apimodel.KKey (go.InterfaceType [])]) #())%E.
  unshelve wp_apply (wp_map_make1
    (K := KKey.t) (V := interface.t)
    apimodel.KKey (go.InterfaceType [])) as
    (phys_state_l) "Hown_phys"; try tc_solve.
  wp_bind (#(functions go.make1
    [go.MapType types.UID (go.StructType [])]) #())%E.
  unshelve wp_apply (wp_map_make1
    (K := types.UID.t) (V := unit)
    types.UID (go.StructType [])) as
    (phys_used_uid_l) "Hown_used_uid"; try tc_solve.
  wp_bind (#(functions go.make1
    [go.MapType go.string (go.StructType [])]) #())%E.
  unshelve wp_apply (wp_map_make1
    (K := go_string) (V := unit)
    go.string (go.StructType [])) as
    (phys_used_rv_l) "Hown_used_rv"; try tc_solve.
  wp_alloc mu_l as "Hmu".
  wp_auto.
  wp_alloc l as "Hl".
  iApply wp_fupd. wp_auto.
  iStructNamed "Hl". simpl.
  iMod kview.init as (γ_state) "Hown_abs".
  iMod cview.init as (γ_children) "Hown_children".
  iMod terminating_children.init as
    (γ_terminating_children) "Hown_terminating_children".
  iMod deletion_observation.init as
    (γ_deletion_observation) "Hown_deletion_observations".
  iAssert (kubernetes_inv
      (mk_γk γ_state γ_children γ_terminating_children
        γ_deletion_observation) l)
    with "[m usedUID usedRV Hown_phys Hown_used_uid Hown_used_rv
      Hown_abs Hown_children Hown_terminating_children
      Hown_deletion_observations]" as "Hinv".
  { iExists phys_state_l, phys_used_uid_l, phys_used_rv_l,
      (∅ : gmap KKey.t interface.t),
      (∅ : gmap types.UID.t unit),
      (∅ : gmap go_string unit),
      (∅ : gmap KKey.t KObjectV.t),
      (∅ : gset types.UID.t),
      (∅ : gset (KKey.t * types.UID.t)).
    iFrame.
    rewrite big_sepM2_empty.
    iPureIntro. split; done. }
  iPersist "mu".
  iMod (init_Mutex with "Hmu [Hinv]") as "#Hmutex".
  { iNext. iExact "Hinv". }
  iApply ("HΦ" $! l
    (mk_γk γ_state γ_children γ_terminating_children
      γ_deletion_observation)).
  iExists mu_l. iFrame "#".
  iModIntro. done.
Qed.

End proof.
