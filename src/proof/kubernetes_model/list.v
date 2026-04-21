From New.proof Require Import prelude empty_ffi.
From New.proof.kubernetes_model Require Export inv common.

Section proof.
Context `{hG: !heapGS Σ} {go_ctx: GoContext}.
Context `{!kviewG Σ}.
Context `{!cviewG Σ}.
Context `{!mono_gsetG types.UID.t Σ}.

Lemma kobject_list_to_pods objs :
  Forall (λ obj, ∃ pod, obj = KObjectV.Pod pod) objs →
  ∃ pods, objs = KObjectV.Pod <$> pods.
Proof.
  induction 1 as [|obj objs [pod ->] _ [pods ->]].
  - exists []. done.
  - exists (pod :: pods). done.
Qed.

Lemma wp_State__objListLocked γ l kind namespace phys_state_l phys_state abs_state used_uid :
  {{{ is_pkg_init apimodel ∗
      "Hstate_m_addr" ∷ l ↦s[apimodel.State :: "m"] phys_state_l ∗
      "Hown_phys" ∷ phys_state_l ↦$ phys_state ∗
      "Hown_abs" ∷ own_kview_auth γ abs_state used_uid ∗
      "Hphys_abs_rep" ∷ ([∗ map] i; obj ∈ phys_state; abs_state, KObjectV.deepown_i i obj 1)
  }}}
    l @ (ptrT.id apimodel.State.id) @ "objListLocked" #kind #namespace
  {{{ sl interfaces objs, RET #sl;
      sl ↦* interfaces ∗
      ([∗ list] i;obj ∈ interfaces;objs, KObjectV.deepown_i i obj 1) ∗
      ⌜ objs ≡ₚ (map_to_list (filter
          (λ kv, kv.1.(KKey.Kind') = kind ∧ v1.namespace_matches namespace kv.1.(KKey.Namespace'))
          abs_state)).*2 ⌝ ∗
      ⌜ Forall KObjectV.valid objs ⌝ ∗
      ⌜ Forall KObjectV.valid_old objs ⌝ ∗
      ⌜ NoDup (KObjectV.key <$> objs) ⌝ ∗
      l ↦s[apimodel.State :: "m"] phys_state_l ∗
      phys_state_l ↦$ phys_state ∗
      own_kview_auth γ abs_state used_uid ∗
      ([∗ map] i; obj ∈ phys_state; abs_state, KObjectV.deepown_i i obj 1)
  }}}.
Proof.
Admitted.

Lemma wp_State__objListLocked_Pod γ l namespace phys_state_l phys_state abs_state used_uid :
  {{{ is_pkg_init apimodel ∗
      "Hstate_m_addr" ∷ l ↦s[apimodel.State :: "m"] phys_state_l ∗
      "Hown_phys" ∷ phys_state_l ↦$ phys_state ∗
      "Hown_abs" ∷ own_kview_auth γ abs_state used_uid ∗
      "Hphys_abs_rep" ∷ ([∗ map] i; obj ∈ phys_state; abs_state, KObjectV.deepown_i i obj 1)
  }}}
    l @ (ptrT.id apimodel.State.id) @ "objListLocked" #"Pod"%go #namespace
  {{{ sl interfaces pods, RET #sl;
      sl ↦* interfaces ∗
      ([∗ list] i;pod ∈ interfaces;pods, KObjectV.deepown_i i (KObjectV.Pod pod) 1) ∗
      ⌜ KObjectV.Pod <$> pods ≡ₚ (map_to_list (filter
          (λ kv, kv.1.(KKey.Kind') = "Pod"%go ∧ v1.namespace_matches namespace kv.1.(KKey.Namespace'))
          abs_state)).*2 ⌝ ∗
      ⌜ Forall PodV.valid pods ⌝ ∗
      ⌜ NoDup (PodV.key <$> pods) ⌝ ∗
      l ↦s[apimodel.State :: "m"] phys_state_l ∗
      phys_state_l ↦$ phys_state ∗
      own_kview_auth γ abs_state used_uid ∗
      ([∗ map] i; obj ∈ phys_state; abs_state, KObjectV.deepown_i i obj 1)
  }}}.
Proof.
  iIntros (Φ) "(#Hinit & Hstate_m_addr & Hown_phys & Hown_abs & Hphys_abs_rep) HΦ".
  wp_apply (wp_State__objListLocked with "[$Hstate_m_addr $Hown_phys $Hown_abs $Hphys_abs_rep]").
  iIntros (sl interfaces objs)
    "(Hsl & Hlist & %Hperm & %Hvalid & %Hvalid_old & %Hnodup & Hstate_m_addr & Hown_phys & Hown_abs & Hphys_abs_rep)".
  iPoseProof (kview.own_auth_valid_forall with "Hown_abs") as "%Habs_valid".
  assert (Forall (λ obj, ∃ pod, obj = KObjectV.Pod pod) objs) as Hobjs_are_pods.
  { rewrite Forall_forall.
    intros obj Hobj_in.
    rewrite Hperm in Hobj_in.
    rewrite <- list_elem_of_In in Hobj_in.
    apply list_elem_of_fmap_1 in Hobj_in as [[key obj'] [Hobj_eq Hin]].
    simpl in Hobj_eq. subst obj'.
    apply elem_of_map_to_list in Hin.
    apply map_lookup_filter_Some in Hin as [Hlookup_abs [Hkind _]].
    pose proof (Habs_valid key obj Hlookup_abs) as [Hkey_eq _].
    destruct obj as [pod|rs].
    - eexists. done.
    - exfalso. subst key. simpl in Hkind. done.
  }
  destruct (kobject_list_to_pods _ Hobjs_are_pods) as [pods ->].
  iEval (rewrite big_sepL2_fmap_r) in "Hlist".
  iApply "HΦ". iFrame.
  iPureIntro. split_and!.
  - exact Hperm.
  - rewrite Forall_fmap in Hvalid_old. exact Hvalid_old.
  - assert (KObjectV.key <$> (KObjectV.Pod <$> pods) = PodV.key <$> pods) as Hkeys_eq.
    { rewrite -list_fmap_compose.
      apply list_fmap_ext. intros i pod Hlookup.
      unfold compose, KObjectV.key, PodV.key, KObjectV.kind, PodV.kind. done. }
    rewrite Hkeys_eq in Hnodup. exact Hnodup.
Qed.

Lemma wp_State__objListLocked_Pod_NamespaceAll γ l phys_state_l phys_state abs_state used_uid :
  {{{ is_pkg_init apimodel ∗
      "Hstate_m_addr" ∷ l ↦s[apimodel.State :: "m"] phys_state_l ∗
      "Hown_phys" ∷ phys_state_l ↦$ phys_state ∗
      "Hown_abs" ∷ own_kview_auth γ abs_state used_uid ∗
      "Hphys_abs_rep" ∷ ([∗ map] i; obj ∈ phys_state; abs_state, KObjectV.deepown_i i obj 1)
  }}}
    l @ (ptrT.id apimodel.State.id) @ "objListLocked" #"Pod"%go #v1.NamespaceAll
  {{{ sl interfaces pods, RET #sl;
      sl ↦* interfaces ∗
      ([∗ list] i;pod ∈ interfaces;pods, KObjectV.deepown_i i (KObjectV.Pod pod) 1) ∗
      ⌜ KObjectV.Pod <$> pods ≡ₚ (map_to_list (filter (λ kv, kv.1.(KKey.Kind') = "Pod"%go) abs_state)).*2 ⌝ ∗
      ⌜ Forall PodV.valid pods ⌝ ∗
      ⌜ NoDup (PodV.key <$> pods) ⌝ ∗
      l ↦s[apimodel.State :: "m"] phys_state_l ∗
      phys_state_l ↦$ phys_state ∗
      own_kview_auth γ abs_state used_uid ∗
      ([∗ map] i; obj ∈ phys_state; abs_state, KObjectV.deepown_i i obj 1)
  }}}.
Proof.
  iIntros (Φ) "(#Hinit & Hstate_m_addr & Hown_phys & Hown_abs & Hphys_abs_rep) HΦ".
  wp_apply (wp_State__objListLocked_Pod with "[$Hstate_m_addr $Hown_phys $Hown_abs $Hphys_abs_rep]").
  iIntros (sl interfaces pods)
    "(Hsl & Hlist & %Hperm & %Hpods_valid & Hstate_m_addr & Hown_phys & Hown_abs & Hphys_abs_rep)".
  iApply "HΦ". iFrame.
  iPureIntro.
  assert (filter
    (λ kv, kv.1.(KKey.Kind') = "Pod"%go ∧
      v1.namespace_matches v1.NamespaceAll kv.1.(KKey.Namespace')) abs_state =
    filter (λ kv, kv.1.(KKey.Kind') = "Pod"%go) abs_state) as Hfilter_eq.
  { apply map_eq. intros k.
    destruct (abs_state !! k) as [obj|] eqn:Hlookup.
    - destruct (decide (k.(KKey.Kind') = "Pod"%go)) as [Hkind|Hkind].
      + transitivity (Some obj).
        * apply map_lookup_filter_Some_2; [done|].
          split; [done|left; done].
        * symmetry. apply map_lookup_filter_Some_2; [done|].
          done.
      + transitivity (@None KObjectV.t).
        * apply map_lookup_filter_None_2. right.
          intros x Hlookup' [Hkind' _].
          apply Hkind. exact Hkind'.
        * symmetry. apply map_lookup_filter_None_2. right.
          intros x Hlookup' Hpred.
          apply Hkind. exact Hpred.
    - transitivity (@None KObjectV.t).
      + apply map_lookup_filter_None_2. left. done.
      + symmetry. apply map_lookup_filter_None_2. left. done.
  }
  rewrite Hfilter_eq in Hperm.
  split; [exact Hperm|exact Hpods_valid].
Qed.

End proof.
