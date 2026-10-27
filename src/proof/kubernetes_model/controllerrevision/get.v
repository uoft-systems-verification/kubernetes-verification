From New.proof Require Import prelude empty_ffi wp_keep.
From New.proof.kubernetes_model Require Export get.

Section proof.
Context `{hG: !heapGS Σ} `{!ffi_semantics _ _}.
Context {sem : go.Semantics} {package_sem : apimodel.Assumptions}.
Context `{!kubernetesModelG Σ}.
Local Set Default Proof Using "All".

Lemma wp_State__ControllerRevisionMutGet γ l key namespace name uid dq kmeta kspec :
  {{{ is_pkg_init apimodel ∗
      "#Hisk" ∷ is_kubernetes γ l ∗
      "%Hkey_def" ∷ ⌜ key = {|
        KKey.Kind' := "ControllerRevision"%go;
        KKey.Namespace' := namespace;
        KKey.Name' := name
      |} ⌝ ∗
      "Hown_meta_frag" ∷ own_meta_frag γ key uid dq kmeta ∗
      "Hown_spec_frag" ∷ own_spec_frag γ key uid dq (ObjectSpecV.ControllerRevisionSpec kspec)
  }}}
    l @! (go.PointerType apimodel.State) @! "ControllerRevisionMutGet"
      #namespace #name
  {{{ revision_l revision, RET (#revision_l, #interface.nil);
      "%Hvalid'" ∷ ⌜ KObjectV.valid (KObjectV.ControllerRevision revision) ⌝ ∗
      "%Hkey_eq" ∷ ⌜ key = ControllerRevisionV.key revision ⌝ ∗
      "%Hmeta_eq" ∷ ⌜ ObjectMetaV.equiv_except_resource_version
        revision.(ControllerRevisionV.ObjectMeta') kmeta ⌝ ∗
      "%Hspec_eq" ∷ ⌜ kspec = (ControllerRevisionV.spec revision) ⌝ ∗
      "Hdeepown_l" ∷ ControllerRevisionV.deepown_l revision_l revision 1 ∗
      "Hown_meta_frag" ∷ own_meta_frag γ key uid dq kmeta ∗
      "Hown_spec_frag" ∷ own_spec_frag γ key uid dq (ObjectSpecV.ControllerRevisionSpec kspec)
  }}}.
Proof.
  iIntros (Φ) "(#Hinit & H) HΦ". iNamed "H". subst key.
  wp_method_call.
  rewrite /apimodel.State__ControllerRevisionMutGetⁱᵐᵖˡ.
  wp_call. wp_auto_keep.
  wp_apply (wp_State__get_some γ l
    {| KKey.Kind' := "ControllerRevision"%go;
       KKey.Namespace' := namespace;
       KKey.Name' := name |}
    uid dq dq kmeta (Some (ObjectSpecV.ControllerRevisionSpec kspec)) None
    with "[$Hinit $Hisk $Hown_meta_frag $Hown_spec_frag]").
  iIntros (i kobj) "Hpost". iNamed "Hpost".
  iDestruct "Hpost" as "((Hown_spec_frag & %Hspec_eq) & _)".
  destruct kobj as [pod|rs|pvc|unused_sts|d|revision];
    try solve [simpl in Hspec_eq; done].
  simpl in Hvalid', Hkey_eq, Hmeta_eq, Hspec_eq.
  assert (Hspec_eq' : kspec = (ControllerRevisionV.spec revision)) by congruence.
  clear Hspec_eq. rename Hspec_eq' into Hspec_eq.
  iDestruct "Hdeepown_i" as (revision_l) "[%Hi Hdeepown_l]".
  wp_auto_keep.
  unfold KObjectV.valid_interface in Hi. destruct Hi as [Hi _]. rewrite Hi.
  change (go.PointerType api_apps_v1.ControllerRevision)
    with (go.PointerType v1.ControllerRevision).
  cbn [interface.ty interface.v].
  replace (if decide
      (go.PointerType v1.ControllerRevision = go.PointerType v1.ControllerRevision)
    then #revision_l else #null)%V with (#revision_l)%V by
    (rewrite decide_True; done).
  replace (bool_decide
      (go.PointerType v1.ControllerRevision = go.PointerType v1.ControllerRevision))
    with true by (symmetry; apply bool_decide_eq_true_2; done).
  wp_auto_keep.
  iApply "HΦ". iFrame. iPureIntro. split_and!; done.
Qed.

Lemma wp_State__ControllerRevisionGet γ l key namespace name uid dq kmeta kspec :
  {{{ is_pkg_init apimodel ∗
      "#Hisk" ∷ is_kubernetes γ l ∗
      "%Hkey_def" ∷ ⌜ key = {|
        KKey.Kind' := "ControllerRevision"%go;
        KKey.Namespace' := namespace;
        KKey.Name' := name
      |} ⌝ ∗
      "Hown_meta_frag" ∷ own_meta_frag γ key uid dq kmeta ∗
      "Hown_spec_frag" ∷ own_spec_frag γ key uid dq (ObjectSpecV.ControllerRevisionSpec kspec)
  }}}
    l @! (go.PointerType apimodel.State) @! "ControllerRevisionGet"
      #namespace #name
  {{{ revision_l revision, RET (#revision_l, #interface.nil);
      "%Hvalid'" ∷ ⌜ KObjectV.valid (KObjectV.ControllerRevision revision) ⌝ ∗
      "%Hkey_eq" ∷ ⌜ key = ControllerRevisionV.key revision ⌝ ∗
      "%Hmeta_eq" ∷ ⌜ ObjectMetaV.equiv_except_resource_version
        revision.(ControllerRevisionV.ObjectMeta') kmeta ⌝ ∗
      "%Hspec_eq" ∷ ⌜ kspec = (ControllerRevisionV.spec revision) ⌝ ∗
      "Hdeepown_l" ∷ ControllerRevisionV.deepown_l revision_l revision 1 ∗
      "Hown_meta_frag" ∷ own_meta_frag γ key uid dq kmeta ∗
      "Hown_spec_frag" ∷ own_spec_frag γ key uid dq (ObjectSpecV.ControllerRevisionSpec kspec)
  }}}.
Proof.
  iIntros (Φ) "(#Hinit & H) HΦ". iNamed "H".
  wp_method_call.
  rewrite /apimodel.State__ControllerRevisionGetⁱᵐᵖˡ.
  wp_call. wp_auto_keep.
  wp_apply (wp_State__ControllerRevisionMutGet
    γ l key namespace name uid dq kmeta kspec
    with "[$Hinit $Hisk $Hown_meta_frag $Hown_spec_frag]").
  { iPureIntro. done. }
  iIntros (revision_l revision) "Hpost".
  wp_auto_keep.
  iApply ("HΦ" with "Hpost").
Qed.


End proof.
