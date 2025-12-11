From Perennial.algebra Require Export auth_map.
From New.proof.github_com.goose_lang.goose.model.channel Require Export auth_set.
Require Export New.proof.sync.

From proof.kubernetes_model Require Export apimodel_init.
From proof.k8s_io.apimachinery.pkg.api Require Export meta.
From proof.k8s_io.apimachinery.pkg.apis.meta Require Export v1.
From proof Require Import prelude empty_ffi.
From proof Require Export well_formed.
From proof.big_op Require Import big_sepL big_sepM.
Export apimodel.apimodel.

Module KKey.
  Global Instance eq_dec : EqDecision KKey.t.
  Proof. solve_decision. Qed.

  Global Instance countable : Countable KKey.t.
  Proof.
    refine (inj_countable'
              (λ k, (KKey.Kind' k,
                     KKey.Name' k,
                     KKey.Namespace' k))
              (λ '(kind, name, namespace),
                KKey.mk kind name namespace)
              _).
    intros []; reflexivity.
  Qed.
End KKey.

Module KObject.
  Inductive t :=
  | Pod (p : PurePod.t)
  | ReplicaSet (rs : PureReplicaSet.t).
End KObject.

Global Existing Instance KKey.eq_dec.
Global Existing Instance KKey.countable.

Section proof.
Context `{hG: !heapGS Σ} {go_ctx: GoContext}.
Context `{!mapG Σ KKey.t interface.t}.
Context `{!mapG Σ KKey.t KObject.t}.
Context `{!mapG Σ KKey.t (gset KKey.t)}.
Context `{!auth_setG Σ KKey.t}.

(* TODO: Need a better spec to differentiate fresh keys from others. *)
Axiom reserved_key: KKey.t → Prop.

Definition mk_pod_key (namespace name: go_string) : KKey.t :=
  {| KKey.Kind' := "Pod"%go; KKey.Namespace' := namespace; KKey.Name' := name;|}.

Definition extract_pod_key pod : KKey.t :=
  mk_pod_key pod.(v1.Pod.ObjectMeta').(v1.ObjectMeta.Namespace') pod.(v1.Pod.ObjectMeta').(v1.ObjectMeta.Name').

Definition extract_kobject_metadata kobj : PureObjectMeta.t :=
  match kobj with
  | KObject.Pod p => p.(PurePod.ObjectMeta')
  | KObject.ReplicaSet rs => rs.(PureReplicaSet.ObjectMeta')
  end.

Definition well_formed_kobject kobj : Prop :=
  match kobj with
  | KObject.Pod p => well_formed_Pod p
  | KObject.ReplicaSet rs => well_formed_ReplicaSet rs
  end.

Definition mk_replicaset_key (namespace name: go_string) : KKey.t :=
  {| KKey.Kind' := "ReplicaSet"%go; KKey.Namespace' := namespace; KKey.Name' := name;|}.

Lemma decide_kind_is_pod kind:
  kind = "Pod"%go →
    bool_decide (kind = "Pod"%go) = true ∧
    bool_decide (kind = "ReplicaSet"%go) = false.
Proof.
  intros Hkind.
  split.
  - apply bool_decide_true; exact Hkind.
  - apply bool_decide_false. intros Hcontra. rewrite Hcontra in Hkind. done.
Qed.

Lemma decide_kind_is_replicaset kind:
  kind = "ReplicaSet"%go →
    bool_decide (kind = "ReplicaSet"%go) = true ∧
    bool_decide (kind = "Pod"%go) = false.
Proof.
  intros Hkind.
  split.
  - apply bool_decide_true; exact Hkind.
  - apply bool_decide_false. intros Hcontra. rewrite Hcontra in Hkind. done.
Qed.

Definition pod_rep k v1 v2 ptr pod pure_pod : iProp Σ :=
  "%Hinterface_is_pod_ptr" ∷ ⌜ v1 = interface.mk (ptrT.id v1.Pod.id) #ptr ⌝ ∗
  "Hpod_ptr" ∷ ptr ↦ pod ∗
  "%Habs_v_is_pod" ∷ ⌜ v2 = KObject.Pod pure_pod ⌝ ∗
  "Hown_pure_pod" ∷ Pod.own pod pure_pod ∗
  "%Hnamespace_match" ∷ ⌜ pure_pod.(PurePod.ObjectMeta').(PureObjectMeta.Namespace') = (KKey.Namespace' k) ⌝ ∗
  "%Hname_match" ∷ ⌜ pure_pod.(PurePod.ObjectMeta').(PureObjectMeta.Name') = (KKey.Name' k) ⌝ ∗
  "%Hwell_formed_Pod" ∷ ⌜ well_formed_Pod pure_pod ⌝.

Definition replicaset_rep k v1 v2 ptr rs pure_rs : iProp Σ :=
  "%Hinterface_is_rs_ptr" ∷ ⌜ v1 = interface.mk (ptrT.id v1.ReplicaSet.id) #ptr ⌝ ∗
  "Hrs_ptr" ∷ ptr ↦ rs ∗
  "%Habs_v_is_rs" ∷ ⌜ v2 = KObject.ReplicaSet pure_rs ⌝ ∗
  "Hown_pure_rs" ∷ ReplicaSet.own rs pure_rs ∗
  "%Hrs_namespace_match" ∷ ⌜ pure_rs.(PureReplicaSet.ObjectMeta').(PureObjectMeta.Namespace') = (KKey.Namespace' k) ⌝ ∗
  "%Hrs_name_match" ∷ ⌜ pure_rs.(PureReplicaSet.ObjectMeta').(PureObjectMeta.Name') = (KKey.Name' k) ⌝ ∗
  "%Hwell_formed_ReplicaSet" ∷ ⌜ well_formed_ReplicaSet pure_rs ⌝.

Definition obj_rep k v1 v2 : iProp Σ :=
  (if bool_decide (KKey.Kind' k = "Pod"%go) then
    ∃ (ptr: loc) (pod: v1.Pod.t) (pure_pod: PurePod.t), pod_rep k v1 v2 ptr pod pure_pod
  else if bool_decide (KKey.Kind' k = "ReplicaSet"%go) then
    ∃ (ptr: loc) (rs: v1.ReplicaSet.t) (pure_rs: PureReplicaSet.t), replicaset_rep k v1 v2 ptr rs pure_rs
  else False)%I.

Definition state_rep (phys_state: gmap KKey.t interface.t) (abs_state: gmap KKey.t KObject.t) : iProp Σ :=
  [∗ map] k ↦ v1; v2 ∈ phys_state; abs_state, obj_rep k v1 v2.

Definition has_controller_parent_of (os: list PureOwnerReference.t) kind name uid : Prop :=
  ∃ i o, os !! i = Some o ∧
    o.(PureOwnerReference.Controller') = Some true ∧
    o.(PureOwnerReference.Kind') = kind ∧
    o.(PureOwnerReference.Name') = name ∧
    o.(PureOwnerReference.UID') = uid.

Definition obj_has_controller_parent_of child kind name uid: Prop :=
  ∃ os, (extract_kobject_metadata child).(PureObjectMeta.OwnerReferences') = Some os ∧
    has_controller_parent_of os kind name uid.

Lemma well_formed_owner_references_has_at_most_one_controller_parent os:
  well_formed_OwnerReferences os →
    ∀ kind1 name1 uid1 kind2 name2 uid2,
      has_controller_parent_of os kind1 name1 uid1 →
        has_controller_parent_of os kind2 name2 uid2 →
          kind1 = kind2 ∧ name1 = name2 ∧ uid1 = uid2.
Proof.
  intros Hwf kind1 name1 uid1 kind2 name2 uid2 H1 H2.
  unfold has_controller_parent_of in H1, H2.
  destruct H1 as (i1 & o1 & Hlookup1 & Hctrl1 & Hkind1 & Hname1 & Huid1).
  destruct H2 as (i2 & o2 & Hlookup2 & Hctrl2 & Hkind2 & Hname2 & Huid2).
  unfold well_formed_OwnerReferences in Hwf.
  assert (i1 = i2) as Heq.
  { apply (Hwf i1 o1 i2 o2).
    split; [|split; [|split]]; assumption. }
  subst i2.
  rewrite Hlookup1 in Hlookup2.
  injection Hlookup2 as ->.
  split.
  - rewrite <- Hkind1. exact Hkind2.
  - split.
    + rewrite <- Hname1. exact Hname2.
    + rewrite <- Huid1. exact Huid2.
Qed.

Lemma well_formed_obj_has_at_most_one_controller_parent obj:
  well_formed_kobject obj →
    ∀ kind1 name1 uid1 kind2 name2 uid2,
      obj_has_controller_parent_of obj kind1 name1 uid1 →
        obj_has_controller_parent_of obj kind2 name2 uid2 →
          kind1 = kind2 ∧ name1 = name2 ∧ uid1 = uid2.
Proof.
  intros Hwf kind1 name1 uid1 kind2 name2 uid2 H1 H2.
  unfold obj_has_controller_parent_of in H1, H2.
  destruct H1 as (os1 & Hownerref1 & Hhas_ctrl1).
  destruct H2 as (os2 & Hownerref2 & Hhas_ctrl2).
  rewrite Hownerref1 in Hownerref2.
  injection Hownerref2 as Hos_eq.
  subst os2.
  destruct obj as [pod | rs].
  - (* Pod case *)
    unfold well_formed_kobject in Hwf.
    unfold well_formed_Pod in Hwf.
    destruct Hwf as (Hwf_meta & _).
    unfold well_formed_ObjectMeta in Hwf_meta.
    destruct Hwf_meta as (_ & _ & _ & _ & _ & Hwf_ownerref).
    simpl in Hownerref1.
    destruct (PureObjectMeta.OwnerReferences' (PurePod.ObjectMeta' pod)) as [os|]; [|discriminate].
    injection Hownerref1 as <-.
    apply well_formed_owner_references_has_at_most_one_controller_parent with (os := os); assumption.
  - (* ReplicaSet case *)
    unfold well_formed_kobject in Hwf.
    unfold well_formed_ReplicaSet in Hwf.
    destruct Hwf as (Hwf_meta & _).
    unfold well_formed_ObjectMeta in Hwf_meta.
    destruct Hwf_meta as (_ & _ & _ & _ & _ & Hwf_ownerref).
    simpl in Hownerref1.
    destruct (PureObjectMeta.OwnerReferences' (PureReplicaSet.ObjectMeta' rs)) as [os|]; [|discriminate].
    injection Hownerref1 as <-.
    apply well_formed_owner_references_has_at_most_one_controller_parent with (os := os); assumption.
Qed.

Definition kubernetes_state_consistent (used_uid: gset go_string) (abs_state: gmap KKey.t KObject.t) (children: gmap KKey.t (gset KKey.t)) (fresh_keys: gset KKey.t) : iProp Σ :=
  (* All parents exist; this means holding a children gmap fragment implies the parent exists in abs_state *)
  "%Hparents_exist" ∷ ⌜ dom children = dom abs_state ⌝ ∗
  (* All children exist *)
  "%Hchildren_exist" ∷ ⌜ ∀ k s, children !! k = Some s → s ⊆ dom abs_state ⌝ ∗
  (* parents and children live in the same namespace *)
  "%Hparents_children_same_namespace" ∷ ⌜ ∀ k s child_key, children !! k = Some s → child_key ∈ s → k.(KKey.Namespace') = child_key.(KKey.Namespace') ⌝ ∗
  (* No one can be their own parent *)
  "%Hno_self_parenting" ∷ ⌜ ∀ k s child_key, children !! k = Some s → child_key ∈ s → child_key ≠ k ⌝ ∗
  (* Each children has only one parent -- the children gsets are disjoint *)
  "%Hchildren_disjoint" ∷ ⌜ ∀ k1 s1 k2 s2, k1 ≠ k2 → children !! k1 = Some s1 → children !! k2 = Some s2 → s1 ## s2 ⌝ ∗
  (* Fresh keys are not used by any existing object *)
  "%Hfresh_keys_absent" ∷ ⌜ fresh_keys ## dom abs_state ⌝ ∗
  (* Fresh keys are reserved *)
  "%Hfresh_keys_reserved" ∷ ⌜ ∀ k, k ∈ fresh_keys → reserved_key k ⌝ ∗
  (* Each object has a unique uid *)
  "%Hno_duplicate_uid" ∷ ⌜ ∀ k1 k2 obj1 obj2, abs_state !! k1 = Some obj1 → abs_state !! k2 = Some obj2 →
    (extract_kobject_metadata obj1).(PureObjectMeta.UID') = (extract_kobject_metadata obj2).(PureObjectMeta.UID') → k1 = k2 ⌝ ∗
  (* Any existing object's uid is in the set used_uid *)
  "%Hexisting_uid_is_used" ∷ ⌜ ∀ k obj, abs_state !! k = Some obj → (extract_kobject_metadata obj).(PureObjectMeta.UID') ∈ used_uid ⌝ ∗
  (* A child is in the children set iff the child has the controller owner reference pointing to the parent *)
  "%Hchildren_point_to_parent" ∷ ⌜ ∀ key_p obj_p key_c obj_c s,
    abs_state !! key_p = Some obj_p → abs_state !! key_c = Some obj_c → children !! key_p = Some s →
      (key_c ∈ s ↔ obj_has_controller_parent_of obj_c key_p.(KKey.Kind') key_p.(KKey.Name') (extract_kobject_metadata obj_p).(PureObjectMeta.UID')) ⌝ ∗
  (* A parent must be some object that has existed; in other words, children cannot guess a parent's uid *)
  "%Hparent_uid_is_used" ∷ ⌜ ∀ k obj kind name uid, abs_state !! k = Some obj →
    obj_has_controller_parent_of obj kind name uid → uid ∈ used_uid ⌝.

Definition is_kubernetes_state_inner γ_state γ_children γ_fresh_keys: iProp Σ :=
  ∃ (phys_state_l: loc) (used_uid_l: loc) (rvc: w64)
    (phys_state: gmap KKey.t interface.t) (used_uid: gmap go_string unit)
    (abs_state: gmap KKey.t KObject.t) (children: gmap KKey.t (gset KKey.t)) (fresh_keys: gset KKey.t),
    "Hstate_m_addr" ∷ (global_addr apimodel.state) ↦s[ apimodel.State :: "m" ] phys_state_l ∗
    "Hstate_used_uid_addr" ∷ (global_addr apimodel.state) ↦s[ apimodel.State :: "usedUID" ] used_uid_l ∗
    "Hstate_rvc_addr" ∷ (global_addr apimodel.state) ↦s[ apimodel.State :: "resourceVersionCounter" ] rvc ∗
    "Hown_phys" ∷ phys_state_l ↦$ phys_state ∗
    "Hown_used_uid" ∷ used_uid_l ↦$ used_uid ∗
    "Hown_abs" ∷ map_ctx γ_state 1 abs_state ∗
    "Hphys_abs_rep" ∷ state_rep phys_state abs_state ∗
    "Hown_children" ∷ map_ctx γ_children 1 children ∗
    "Hown_fresh_keys" ∷ auth_set_auth γ_fresh_keys fresh_keys ∗
    "#Hconsistent" ∷ kubernetes_state_consistent (dom used_uid) abs_state children fresh_keys.

Definition is_kubernetes_state γ_state γ_children γ_fresh_keys : iProp Σ :=
  is_Mutex (global_addr apimodel.stateMu) (is_kubernetes_state_inner γ_state γ_children γ_fresh_keys).

Lemma wp_deepCopy_pod (obj: interface.t) (ptr: loc) (pod: v1.Pod.t) (pure_pod: PurePod.t):
  {{{ is_pkg_init apimodel ∗
      "%interface_is_pod_ptr" ∷ ⌜ obj = interface.mk (ptrT.id v1.Pod.id) #ptr ⌝ ∗
      "pod_ptr" ∷ ptr ↦ pod ∗
      "own_pure_pod" ∷ Pod.own pod pure_pod
  }}}
    @! apimodel.deepCopy #obj
  {{{ (obj': interface.t) (ptr': loc) (pod': v1.Pod.t), RET #obj';
      ⌜ obj' = interface.mk (ptrT.id v1.Pod.id) #ptr' ⌝ ∗
      ptr' ↦ pod' ∗
      Pod.own pod' pure_pod ∗
      ptr ↦ pod ∗
      Pod.own pod pure_pod
  }}}.
Proof.
Admitted.

Lemma wp_deepCopy_replicaset (obj: interface.t) (ptr: loc) (rs: v1.ReplicaSet.t) (pure_rs: PureReplicaSet.t):
  {{{ is_pkg_init apimodel ∗
      "%interface_is_rs_ptr" ∷ ⌜ obj = interface.mk (ptrT.id v1.ReplicaSet.id) #ptr ⌝ ∗
      "rs_ptr" ∷ ptr ↦ rs ∗
      "own_pure_rs" ∷ ReplicaSet.own rs pure_rs
  }}}
    @! apimodel.deepCopy #obj
  {{{ (obj': interface.t) (ptr': loc) (rs': v1.ReplicaSet.t), RET #obj';
      ⌜ obj' = interface.mk (ptrT.id v1.ReplicaSet.id) #ptr' ⌝ ∗
      ptr' ↦ rs' ∗
      ReplicaSet.own rs' pure_rs ∗
      ptr ↦ rs ∗
      ReplicaSet.own rs pure_rs
  }}}.
Proof.
Admitted.

Lemma wp_objGet (key: KKey.t) γ_state γ_children γ_fresh_keys:
  {{{ is_pkg_init apimodel ∗
      "#inv" ∷ is_kubernetes_state γ_state γ_children γ_fresh_keys
  }}}
    @! apimodel.objGet #key
  {{{ (obj: interface.t) (exists': bool), RET (#obj, #exists');
      True
  }}}.
Proof.
Admitted.

(* TODO: revisit this spec *)
Lemma wp_ByIndex_pod_ptsto_mut kind index_name indexed_value
  γ_state γ_children γ_fresh_keys parent_key owned_parent owned_pod_map owned_child_keys:
  {{{ is_pkg_init apimodel ∗
      "#inv" ∷ is_kubernetes_state γ_state γ_children γ_fresh_keys ∗
      "own_parent" ∷ parent_key [[ γ_state ]]↦ owned_parent ∗
      "own_pods" ∷ ([∗ map] key ↦ pod ∈ owned_pod_map, key [[ γ_state ]]↦ KObject.Pod pod) ∗
      "own_child_keys" ∷ parent_key [[ γ_children ]]↦ owned_child_keys ∗
      "%owned_child_keys_equal_dom_owned_pods" ∷ ⌜ owned_child_keys = dom owned_pod_map ⌝ ∗
      "%indexed_value" ∷ ⌜ indexed_value = (extract_kobject_metadata owned_parent).(PureObjectMeta.UID') ⌝ ∗
      "%kind" ∷ ⌜ kind = "Pod"%go ⌝ ∗
      "%index_name" ∷ ⌜ index_name = "podControllerUID"%go ⌝
  }}}
    @! apimodel.ByIndex #kind #index_name #indexed_value
  {{{ (l: slice.t) (err: error.t) (objs: list interface.t) (pods: list v1.Pod.t), RET (#l, #err);
      "l" ∷ l ↦* objs ∗
      "%err_is_nil" ∷ ⌜ err = interface.nil ⌝ ∗
      "obj_pts_to_pod" ∷ ([∗ list] obj ; pod ∈ objs ; pods, ∃ (ptr : loc) (owned_pod : PurePod.t),
        ⌜ obj = interface.mk (ptrT.id v1.Pod.id) #ptr ⌝ ∗
        ptr ↦ pod ∗
        Pod.own pod owned_pod ∗
        ⌜ ∃ k, owned_pod_map !! k = Some owned_pod ⌝ ∗
        ⌜ obj_has_controller_parent_of (KObject.Pod owned_pod) parent_key.(KKey.Kind') parent_key.(KKey.Name') indexed_value ⌝ ∗
        ⌜ well_formed_Pod owned_pod ⌝
      ) ∗
      "%key_set_equal_dom_owned_pods" ∷  ⌜ list_to_set (extract_pod_key <$> pods) = dom owned_pod_map ⌝ ∗
      "own_parent" ∷ parent_key [[ γ_state ]]↦ owned_parent ∗
      "own_pods" ∷ ([∗ map] key ↦ pod ∈ owned_pod_map, key [[ γ_state ]]↦ KObject.Pod pod) ∗
      "own_child_keys" ∷ parent_key [[ γ_children ]]↦ owned_child_keys
  }}}.
Proof.
Admitted.

Lemma wp_generateNewName kind namespace (generate_name : go_string) m (phys_state : gmap KKey.t interface.t):
  {{{ is_pkg_init apimodel ∗
      "m" ∷ m ↦$ phys_state
  }}}
    @! apimodel.generateNewName #kind #namespace #generate_name #m
  {{{ new_name, RET #new_name;
      ⌜ new_name ≠ ""%go ∧ valid_name new_name ⌝ ∗
      ⌜ phys_state !! {| KKey.Kind' := kind; KKey.Namespace' := namespace; KKey.Name' := new_name;|} = None ⌝ ∗
      (* we assume that the generated key never conflicts with fresh_keys *)
      ⌜ ¬ reserved_key {| KKey.Kind' := kind; KKey.Namespace' := namespace; KKey.Name' := new_name;|} ⌝ ∗
      m ↦$ phys_state
  }}}.
Proof.
Admitted.

Lemma wp_generateNewUID m (used_uid : gmap go_string unit):
  {{{ is_pkg_init apimodel ∗
      "m" ∷ m ↦$ used_uid
  }}}
    @! apimodel.generateNewUID #m
  {{{ uid, RET #uid;
      ⌜ used_uid !! uid = None ⌝ ∗
      m ↦$ used_uid
  }}}.
Proof.
Admitted.

Lemma wp_fmt_Sprintf (format: go_string) string_slice (string_list: list interface.t):
  {{{ is_pkg_init fmt ∗
      "string_slice" ∷ string_slice ↦* string_list
  }}}
    @! fmt.Sprintf #format #string_slice
  {{{ (v: go_string), RET #v;
      True
  }}}.
Proof.
Admitted.

Lemma wp_strconv_FormatInt (i: w64) (base: w64):
  {{{ is_pkg_init apimodel }}}
    @! strconv.FormatInt #i #base
  {{{ (v: go_string), RET #v; True }}}.
Proof.
Admitted.

(* If pod has a huge body, this lemma can be used to name the pod body *)
Lemma rename_pod ptr (pod: v1.Pod.t):
  ptr ↦ pod -∗ ∃ pod', ptr ↦ pod' ∗ ⌜ pod' = pod ⌝.
Proof.
  iIntros. iExists pod. iFrame. done.
Qed.

Global Instance wp_struct_make_unit:
  PureWp True
    (struct.make #(structT []) (alist_val []))%struct
    #().
Proof.
  erewrite <- struct_val_aux_nil.
  apply wp_struct_make; cbn; auto.
Qed.

Lemma wp_objCreate_pod_without_name_ptsto_mut kind namespace obj
  to_create_pod_ptr to_create_pod to_create_pure_pod γ_state γ_children γ_fresh_keys parent_key owned_parent owned_child_keys:
  {{{ is_pkg_init apimodel ∗
      "#inv" ∷ is_kubernetes_state γ_state γ_children γ_fresh_keys ∗
      "%Hkind_is_pod" ∷ ⌜ kind = "Pod"%go ⌝ ∗
      "%Hnamespace_is_parent_namespace" ∷ ⌜ namespace = parent_key.(KKey.Namespace') ⌝ ∗
      "%Hnamespace_valid" ∷ ⌜ namespace ≠ ""%go ∧ valid_namespace namespace ⌝ ∗
      "%Hinterface_is_rs_ptr" ∷ ⌜ obj = interface.mk (ptrT.id v1.Pod.id) #to_create_pod_ptr ⌝ ∗
      "Hto_create_pod_ptr" ∷ to_create_pod_ptr ↦ to_create_pod ∗
      "Hdeep_own_to_create_pod" ∷ Pod.own to_create_pod to_create_pure_pod ∗
      "%Hto_create_pure_pod_namespace_valid" ∷ ⌜ to_create_pure_pod.(PurePod.ObjectMeta').(PureObjectMeta.Namespace') = namespace ∨
        to_create_pure_pod.(PurePod.ObjectMeta').(PureObjectMeta.Namespace') = ""%go ⌝ ∗
      "%Hto_create_pure_pod_name_valid" ∷ ⌜ to_create_pure_pod.(PurePod.ObjectMeta').(PureObjectMeta.Name') = ""%go ⌝ ∗
      "%Hto_create_pure_pod_generate_name_valid" ∷ ⌜ to_create_pure_pod.(PurePod.ObjectMeta').(PureObjectMeta.GenerateName') ≠ ""%go ∧
        valid_name to_create_pure_pod.(PurePod.ObjectMeta').(PureObjectMeta.GenerateName') ⌝ ∗
      "%Hto_create_pure_pod_is_child" ∷ ⌜ obj_has_controller_parent_of (KObject.Pod to_create_pure_pod) parent_key.(KKey.Kind') parent_key.(KKey.Name') (extract_kobject_metadata owned_parent).(PureObjectMeta.UID') ⌝ ∗
      "%Hwell_formed_to_create_Pod" ∷ ⌜ well_formed_to_create_Pod to_create_pure_pod ⌝ ∗
      "Hown_parent" ∷ parent_key [[ γ_state ]]↦ owned_parent ∗
      "Hown_child_keys" ∷ parent_key [[ γ_children ]]↦ owned_child_keys
  }}}
    @! apimodel.objCreate #kind #namespace #obj
  {{{ created_obj (err: error.t) created_pod_ptr created_pod created_pure_pod new_key owned_grandchild_keys, RET (#created_obj, #err);
      ⌜ created_obj = interface.mk (ptrT.id v1.Pod.id) #created_pod_ptr ⌝ ∗
      ⌜ err = interface.nil ⌝ ∗
      created_pod_ptr ↦ created_pod ∗
      Pod.own created_pod created_pure_pod ∗
      ⌜ well_formed_Pod created_pure_pod ⌝ ∗
      ⌜ new_key = mk_pod_key namespace created_pure_pod.(PurePod.ObjectMeta').(PureObjectMeta.Name') ⌝ ∗
      ⌜ new_key ∉ owned_child_keys ⌝ ∗
      new_key [[ γ_state ]]↦ (KObject.Pod created_pure_pod) ∗
      parent_key [[ γ_state ]]↦ owned_parent ∗
      parent_key [[ γ_children ]]↦ (owned_child_keys ∪ {[new_key]}) ∗
      new_key [[ γ_children ]]↦ owned_grandchild_keys
      (* TODO: specify that created_pod shares the same content with to_create_pod *)
  }}}.
Proof.
  wp_start as "H". iNamed "H".
  wp_apply wp_with_defer. iIntros (defer) "defer". simpl subst. wp_auto.
  wp_apply wp_globals_get. wp_apply wp_Mutex__Lock; [done|]. iIntros "[Hown_Mutex H]". iNamed "H". wp_auto.
  wp_apply wp_globals_get. wp_apply (wp_deepCopy_pod with "[$Hto_create_pod_ptr $Hdeep_own_to_create_pod]"); [done|].
  iIntros (copied_obj copied_ptr copied_pod) "(-> & Hcopied_ptr & Hdeep_own_copied_pod & Hto_create_pod_ptr & Hdeep_own_to_create_pod)". wp_auto.
  wp_apply wp_Accessor; [done|].
  iIntros (o err) "(-> & ->)". wp_auto.
  assert ((bool_decide (interface.nil = interface.nil)) = true) as nil_is_nil.
  { rewrite bool_decide_true //. }
  rewrite nil_is_nil. wp_auto.
  iDestruct (struct_fields_split with "Hcopied_ptr") as "H". iNamed "H".
  wp_apply (wp_SetNamespace with "[$HObjectMeta]"). iIntros (meta') "(-> & HObjectMeta)". wp_auto.
  wp_apply (wp_GetName with "[$HObjectMeta]"). iIntros (name) "(-> & HObjectMeta)". wp_auto.
  wp_apply (wp_GetGenerateName with "[$HObjectMeta]"). iIntros (generate_name) "(-> & HObjectMeta)". wp_auto.
  iAssert (⌜ v1.ObjectMeta.Name' (v1.Pod.ObjectMeta' copied_pod) = ""%go ⌝%I) as "->".
  { iNamed "Hdeep_own_copied_pod". iNamed "Hown_objectmeta". iPureIntro. congruence. }
  iAssert (⌜ v1.ObjectMeta.GenerateName' (v1.Pod.ObjectMeta' copied_pod) ≠ ""%go ⌝%I) as "%Hgenerate_name_not_empty".
  { iNamed "Hdeep_own_copied_pod". iNamed "Hown_objectmeta". iPureIntro.
    destruct Hto_create_pure_pod_generate_name_valid as [H _]. congruence. }
  wp_auto. wp_if_destruct; [done|]. rewrite bool_decide_false //. wp_auto.
  wp_apply wp_globals_get. wp_apply (wp_generateNewName with "[$Hown_phys]").
  iIntros (new_name) "(%Hnew_name_valid & %Hnew_key_not_in_phys & %Hnew_key_not_reserved & Hown_phys)". wp_auto.
  wp_apply (wp_SetName with "[$HObjectMeta]"). iIntros (meta') "(-> & HObjectMeta)". wp_auto.
  wp_apply wp_globals_get. wp_apply (wp_map_get with "[$Hown_phys]"). iIntros "Hown_phys". wp_auto.
  rewrite /is_Some Hnew_key_not_in_phys. wp_auto.
  wp_apply wp_globals_get. wp_apply (wp_generateNewUID with "[$Hown_used_uid]").
  iIntros (generated_uid) "(%Hgenerated_uid_is_not_used & Hown_used_uid)". wp_auto.
  wp_apply (wp_SetUID with "[$HObjectMeta]"). iIntros (meta') "(-> & HObjectMeta)". wp_auto.
  wp_apply wp_globals_get. wp_apply (wp_map_insert with "[$Hown_used_uid]"). iIntros "Hown_used_uid". wp_auto.
  wp_apply wp_globals_get. wp_apply wp_globals_get. wp_apply wp_globals_get.
  wp_apply wp_strconv_FormatInt. iIntros (rv_str) "_". wp_auto.
  wp_apply (wp_SetResourceVersion with "[$HObjectMeta]"). iIntros (meta') "(-> & HObjectMeta)". wp_auto.
  wp_apply wp_globals_get. wp_apply (wp_map_insert with "[$Hown_phys]"). iIntros "Hown_phys". wp_auto.
  iDestruct (struct_fields_combine (v:=v1.Pod.mk _ _ _ _)
    with "[$HTypeMeta $HObjectMeta $HSpec $HStatus]") as "Hcopied_ptr". simpl.
  iDestruct (rename_pod with "Hcopied_ptr") as (created_pod) "(Hcopied_ptr & %Hcreated_pod_eq)".
  set created_pure_meta := to_create_pure_pod.(PurePod.ObjectMeta')
    <| PureObjectMeta.Namespace' := KKey.Namespace' parent_key |>
    <| PureObjectMeta.Name' := new_name |>
    <| PureObjectMeta.UID' := generated_uid |>
    <| PureObjectMeta.ResourceVersion' := rv_str |>.
  set created_pure_pod := to_create_pure_pod <| PurePod.ObjectMeta' := created_pure_meta |>.
  iAssert (Pod.own created_pod created_pure_pod) with "[Hdeep_own_copied_pod]" as "Hdeep_own_created_pod".
  { iNamed "Hdeep_own_copied_pod". iFrame. iSplitR; [iPureIntro; rewrite Hcreated_pod_eq //|].
    iNamed "Hown_objectmeta". rewrite Hcreated_pod_eq //. iFrame. iPureIntro. done. }
  wp_apply (wp_deepCopy_pod with "[$Hcopied_ptr $Hdeep_own_created_pod]"); [done|].
  iIntros (returned_obj returned_ptr returned_pod) "(-> & Hreturned_ptr & Hdeepown_returned_pod & Hcopied_ptr & Hdeepown_created_pod)". wp_auto.
  set new_key := {| KKey.Kind' := "Pod"; KKey.Name' := new_name; KKey.Namespace' := KKey.Namespace' parent_key |}.
  fold new_key in Hnew_key_not_in_phys. fold new_key in Hnew_key_not_reserved.
  iAssert (⌜ abs_state !! new_key = None ⌝%I) with "[Hphys_abs_rep]" as "%Hnew_key_not_in_abs".
  { iDestruct (big_sepM2_dom with "Hphys_abs_rep") as %Hdom_eq. iPureIntro. apply not_elem_of_dom. apply not_elem_of_dom in Hnew_key_not_in_phys. set_solver. }
  iAssert (⌜ children !! new_key = None ⌝%I) with "[Hconsistent]" as "%Hnew_key_not_in_children".
  { iNamed "Hconsistent". iPureIntro. apply not_elem_of_dom. apply not_elem_of_dom in Hnew_key_not_in_abs. set_solver. }
  iAssert (⌜ abs_state !! parent_key = Some (owned_parent) ⌝%I) with "[Hown_parent Hown_abs]" as "%Hparent_key_in_abs".
  { iDestruct (map_valid with "Hown_abs Hown_parent") as %Hlookup. iPureIntro; exact Hlookup. }
  iAssert (⌜ children !! parent_key = Some (owned_child_keys) ⌝%I) with "[Hown_child_keys Hown_children]" as "%Hparent_key_in_children".
  { iDestruct (map_valid with "Hown_children Hown_child_keys") as %Hlookup. iPureIntro; exact Hlookup. }
  assert (new_key ≠ parent_key) as new_key_neq_parent_key.
  { intros Heq. congruence. }
  iAssert (⌜ <[parent_key:=owned_child_keys ∪ {[new_key]}]> children !! new_key = None ⌝%I) with "[Hconsistent]" as "%Hnew_key_not_in_children_after_update".
  { iNamed "Hconsistent". iPureIntro. apply not_elem_of_dom. apply not_elem_of_dom in Hnew_key_not_in_abs. set_solver. }
  iAssert (⌜ new_key ∉ owned_child_keys ⌝ %I) as "%Hnew_key_not_in_owned_child_keys".
  { iNamed "Hconsistent". iPureIntro.
    assert (owned_child_keys ⊆ dom abs_state) as Howned_in_abs.
    { apply Hchildren_exist with (k := parent_key). exact Hparent_key_in_children. }
    apply not_elem_of_dom in Hnew_key_not_in_abs.
    set_solver. }
  iMod (map_alloc new_key (KObject.Pod created_pure_pod) with "[$Hown_abs]") as "[Hown_abs Hown_pod]"; [eauto|].
  iMod (auth_map.map_update _ _ (owned_child_keys ∪ {[new_key]}) with "Hown_children Hown_child_keys")
    as "[Hown_children Hown_child_keys]".
  iMod (map_alloc new_key ∅ with "[$Hown_children]") as "[Hown_children Hown_grandchild_keys]"; [eauto|].
  set phys_state' := <[new_key:=interface.mk (ptrT.id v1.Pod.id) (# copied_ptr)]> phys_state.
  set used_uid' := <[generated_uid:=()]> used_uid.
  set abs_state' := <[new_key:=KObject.Pod created_pure_pod]> abs_state.
  set children' := (<[new_key:=∅]> (<[parent_key:=owned_child_keys ∪ {[new_key]}]> children)).
  iAssert ((⌜ created_pure_pod.(PurePod.ObjectMeta').(PureObjectMeta.Namespace') = new_key.(KKey.Namespace') ⌝ ∗
      ⌜ created_pure_pod.(PurePod.ObjectMeta').(PureObjectMeta.Name') = new_key.(KKey.Name') ⌝ ∗
      ⌜ well_formed_Pod created_pure_pod ⌝) %I)
  as "(%Hnamespace_match & %Hname_match & %Hwell_formed_Pod)".
  { iPureIntro. split; [done|split;[done|]].
    unfold well_formed_Pod. unfold well_formed_to_create_Pod in Hwell_formed_to_create_Pod.
    split; [|split; [intuition|intuition]].
    unfold well_formed_ObjectMeta. unfold well_formed_to_create_ObjectMeta in Hwell_formed_to_create_Pod. intuition. }
  iAssert (state_rep phys_state' abs_state' %I) with "[Hcopied_ptr Hdeepown_created_pod Hphys_abs_rep]" as "Hphys_abs_rep".
  {
    unfold state_rep. unfold phys_state'. unfold abs_state'.
    rewrite (big_sepM2_insert _ phys_state abs_state new_key _ _ Hnew_key_not_in_phys Hnew_key_not_in_abs).
    iSplitL "Hcopied_ptr Hdeepown_created_pod".
    - unfold obj_rep.
      assert (bool_decide (KKey.Kind' new_key = "Pod"%go) = true) as kind_is_pod.
      { apply bool_decide_true. unfold new_key. simpl. reflexivity. }
      rewrite kind_is_pod.
      iExists copied_ptr, created_pod, created_pure_pod.
      unfold pod_rep. iFrame "#". iFrame. iPureIntro. done.
    - done. }
  iAssert (kubernetes_state_consistent (dom used_uid') abs_state' children' fresh_keys %I)
  as "#Hconsistent'".
  {
    iNamed "Hconsistent".
    assert (dom children' = dom children ∪ {[new_key]}) as Hdom_children_eq.
    {
      unfold children'.
      rewrite !dom_insert_L.
      assert (parent_key ∈ dom children) as Hparent_in_dom.
      { apply elem_of_dom. exists owned_child_keys. exact Hparent_key_in_children. }
      assert ({[parent_key]} ∪ dom children = dom children) as Hparent_union_eq.
      { set_solver. }
      rewrite Hparent_union_eq.
      set_solver.
    }
    assert (PureObjectMeta.UID' (extract_kobject_metadata (KObject.Pod created_pure_pod)) = generated_uid) as Hcreated_pure_pod_uiq_eq.
    { intuition. }
    assert (generated_uid ∉ dom used_uid) as Hgenerated_not_in_used.
    { apply not_elem_of_dom. exact Hgenerated_uid_is_not_used. }
    assert (obj_has_controller_parent_of (KObject.Pod created_pure_pod) (KKey.Kind' parent_key)
      (KKey.Name' parent_key) (PureObjectMeta.UID' (extract_kobject_metadata owned_parent)))
      as Hcreated_pure_pod_has_controller_parent_of_owned_parent by done.
    iPureIntro.
    split; [|split; [|split; [|split; [|split; [|split; [|split; [|split; [|split; [|split ]]]]]]]]].
    { unfold abs_state'. unfold children'. rewrite Hdom_children_eq. rewrite dom_insert_L. set_solver. }
    { intros k s Hlookup.
      unfold children' in Hlookup. unfold abs_state'.
      rewrite lookup_insert_Some in Hlookup.
      destruct Hlookup as [(Hk_eq & Hs_eq) | (Hk_neq & Hlookup)].
      - subst k s. rewrite dom_insert_L. set_solver.
      - rewrite lookup_insert_Some in Hlookup.
        destruct Hlookup as [(Hk_eq_parent & Hs_eq) | (Hk_neq_parent & Hlookup)].
        + subst k s. rewrite dom_insert_L.
          assert (owned_child_keys ⊆ dom abs_state) as children_in_abs.
          { apply Hchildren_exist with (k := parent_key). exact Hparent_key_in_children. }
          set_solver.
        + rewrite dom_insert_L.
          assert (s ⊆ dom abs_state) as s_in_abs.
          { apply Hchildren_exist with (k := k). exact Hlookup. }
          set_solver.
    }
    { intros k s child_key Hlookup Hchild_in_s.
      unfold children' in Hlookup.
      rewrite lookup_insert_Some in Hlookup.
      destruct Hlookup as [(Hk_eq & Hs_eq) | (Hk_neq & Hlookup)].
      - subst k s. set_solver.
      - rewrite lookup_insert_Some in Hlookup.
        destruct Hlookup as [(Hk_eq_parent & Hs_eq) | (Hk_neq_parent & Hlookup)].
        + subst k s.
          assert (child_key ∈ owned_child_keys ∨ child_key = new_key) as Hchild_cases.
          { set_solver. }
          destruct Hchild_cases as [Hchild_in_owned | Hchild_eq_new].
          * apply Hparents_children_same_namespace with (k := parent_key) (s := owned_child_keys); assumption.
          * subst child_key. unfold new_key. simpl. reflexivity.
        + apply Hparents_children_same_namespace with (k := k) (s := s); assumption.
    }
    { intros k s child_key Hlookup Hchild_in_s.
      unfold children' in Hlookup.
      rewrite lookup_insert_Some in Hlookup.
      destruct Hlookup as [(Hk_eq & Hs_eq) | (Hk_neq & Hlookup)].
      - subst k s. set_solver.
      - rewrite lookup_insert_Some in Hlookup.
        destruct Hlookup as [(Hk_eq_parent & Hs_eq) | (Hk_neq_parent & Hlookup)].
        + subst k s.
          assert (child_key ∈ owned_child_keys ∨ child_key = new_key) as Hchild_cases.
          { set_solver. }
          destruct Hchild_cases as [Hchild_in_owned | Hchild_eq_new].
          * apply Hno_self_parenting with (k := parent_key) (s := owned_child_keys); assumption.
          * subst child_key. assumption.
        + apply Hno_self_parenting with (k := k) (s := s); assumption.
    }
    { intros k1 s1 k2 s2 Hk1_neq_k2 Hlookup1 Hlookup2.
      unfold children' in Hlookup1, Hlookup2.
      rewrite lookup_insert_Some in Hlookup1.
      rewrite lookup_insert_Some in Hlookup2.
      destruct Hlookup1 as [(Hk1_eq & Hs1_eq) | (Hk1_neq & Hlookup1)];
      [destruct Hlookup2 as [(Hk2_eq & Hs2_eq) | (Hk2_neq & Hlookup2)] |
       destruct Hlookup2 as [(Hk2_eq & Hs2_eq) | (Hk2_neq & Hlookup2)]].
      - subst k1 k2. contradiction.
      - subst k1 s1.
        rewrite lookup_insert_Some in Hlookup2.
        destruct Hlookup2 as [(Hk2_eq_parent & Hs2_eq) | (Hk2_neq_parent & Hlookup2)];
        [subst k2 s2; set_solver | set_solver].
      - subst k2 s2.
        rewrite lookup_insert_Some in Hlookup1.
        destruct Hlookup1 as [(Hk1_eq_parent & Hs1_eq) | (Hk1_neq_parent & Hlookup1)];
        [subst k1 s1; set_solver | set_solver].
      - rewrite lookup_insert_Some in Hlookup1.
        rewrite lookup_insert_Some in Hlookup2.
        destruct Hlookup1 as [(Hk1_eq_parent & Hs1_eq) | (Hk1_neq_parent & Hlookup1)];
        [destruct Hlookup2 as [(Hk2_eq_parent & Hs2_eq) | (Hk2_neq_parent & Hlookup2)] |
         destruct Hlookup2 as [(Hk2_eq_parent & Hs2_eq) | (Hk2_neq_parent & Hlookup2)]].
        + subst k1 k2. contradiction.
        + subst k1 s1.
          assert (s2 ⊆ dom abs_state) as s2_in_abs.
          { apply Hchildren_exist with (k := k2). exact Hlookup2. }
          assert (owned_child_keys ## s2) as disj.
          { apply Hchildren_disjoint with (k1 := parent_key) (k2 := k2); [|exact Hparent_key_in_children|exact Hlookup2].
            intros Heq. contradiction. }
          assert (new_key ∉ dom abs_state) as key_not_in_abs.
          { apply not_elem_of_dom. exact Hnew_key_not_in_abs. }
          clear -disj s2_in_abs key_not_in_abs.
          set_solver.
        + subst k2 s2.
          assert (s1 ⊆ dom abs_state) as s1_in_abs.
          { apply Hchildren_exist with (k := k1). exact Hlookup1. }
          assert (s1 ## owned_child_keys) as disj.
          { apply Hchildren_disjoint with (k1 := k1) (k2 := parent_key); [|exact Hlookup1|exact Hparent_key_in_children].
            intros Heq. contradiction. }
          assert (new_key ∉ dom abs_state) as key_not_in_abs.
          { apply not_elem_of_dom. exact Hnew_key_not_in_abs. }
          clear -disj s1_in_abs key_not_in_abs.
          set_solver.
        + apply Hchildren_disjoint with (k1 := k1) (k2 := k2); assumption.
    }
    { unfold abs_state'. rewrite dom_insert_L.
      assert (new_key ∉ fresh_keys) as Hkey_not_in_fresh.
      { intros Hin. apply Hfresh_keys_reserved in Hin. contradiction. }
      clear -Hfresh_keys_absent Hkey_not_in_fresh.
      set_solver.
    }
    { apply Hfresh_keys_reserved. }
    { intros k1 k2 obj1 obj2 Hlookup1 Hlookup2 Huid_eq.
      unfold abs_state' in Hlookup1, Hlookup2.
      rewrite lookup_insert_Some in Hlookup1.
      rewrite lookup_insert_Some in Hlookup2.
      destruct Hlookup1 as [(Hk1_eq & Hobj1_eq) | (Hk1_neq & Hlookup1)];
      destruct Hlookup2 as [(Hk2_eq & Hobj2_eq) | (Hk2_neq & Hlookup2)].
      - subst k1 k2. reflexivity.
      - subst k1 obj1.
        exfalso.
        assert ((extract_kobject_metadata obj2).(PureObjectMeta.UID') ∈ dom used_uid) as Hobj2_uid_in_used.
        { apply Hexisting_uid_is_used with (k := k2). exact Hlookup2. }
        rewrite Hcreated_pure_pod_uiq_eq in Huid_eq.
        rewrite <- Huid_eq in Hobj2_uid_in_used.
        contradiction.
      - subst k2 obj2.
        exfalso.
        assert ((extract_kobject_metadata obj1).(PureObjectMeta.UID') ∈ dom used_uid) as obj1_uid_in_used.
        { apply Hexisting_uid_is_used with (k := k1). exact Hlookup1. }
        rewrite Hcreated_pure_pod_uiq_eq in Huid_eq.
        rewrite Huid_eq in obj1_uid_in_used.
        contradiction.
      - apply Hno_duplicate_uid with (obj1 := obj1) (obj2 := obj2); assumption.
    }
    { intros k obj Hlookup_abs_state. unfold abs_state', used_uid'.
      rewrite dom_insert_L. rewrite lookup_insert_Some in Hlookup_abs_state.
      destruct Hlookup_abs_state as [(Hk_eq & Hs_eq) | (Hk_neq & Hlookup_abs_state)].
      - subst k obj. set_solver.
      - set_solver.
    }
    { intros key_p obj_p key_c obj_c s Hlookup_p Hlookup_c Hlookup_children.
      unfold abs_state' in Hlookup_p, Hlookup_c.
      unfold children' in Hlookup_children.
      rewrite lookup_insert_Some in Hlookup_p.
      rewrite lookup_insert_Some in Hlookup_c.
      rewrite lookup_insert_Some in Hlookup_children.
      split.
      { intros Hkey_c_in_s.
        destruct Hlookup_children as [(<- & <-) | (Hkey_p_neq & Hlookup_children)]; [done|].
        destruct Hlookup_p as [(<- & <-) | (Hkey_p_neq' & Hlookup_p)]; [done|].
        destruct Hlookup_c as [(<- & <-) | (Hkey_c_neq & Hlookup_c)].
        - rewrite lookup_insert_Some in Hlookup_children.
          destruct Hlookup_children as [(<- & <-) | (Hkey_p_neq'' & Hlookup_children)].
          + rewrite Hparent_key_in_abs in Hlookup_p. injection Hlookup_p as <-. done.
          + eapply Hchildren_exist in Hlookup_children. apply not_elem_of_dom in Hnew_key_not_in_abs. set_solver.
        - rewrite lookup_insert_Some in Hlookup_children.
          destruct Hlookup_children as [(<- & <-) | (Hkey_p_neq'' & Hlookup_children)].
          + eapply Hchildren_point_to_parent; [done|done|done|]. set_solver.
          + eapply Hchildren_point_to_parent; [done|done|done|done].
      }
      { intros Hobj_has_controller_parent_of.
        destruct Hlookup_c as [(<- & <-) | (Hkey_c_neq & Hlookup_c)].
        - assert (well_formed_kobject (KObject.Pod created_pure_pod)) as Hwell_formed_kobject by done.
          pose proof (well_formed_obj_has_at_most_one_controller_parent (KObject.Pod created_pure_pod) Hwell_formed_kobject
            _ _ _ _ _ _ Hobj_has_controller_parent_of Hcreated_pure_pod_has_controller_parent_of_owned_parent) as (Hkind_eq & Hname_eq & Huid_eq).
          destruct Hlookup_p as [(<- & <-) | (Hkey_p_neq & Hlookup_p)].
          + exfalso.
            pose proof (Hexisting_uid_is_used parent_key owned_parent Hparent_key_in_abs).
            rewrite Hcreated_pure_pod_uiq_eq in Huid_eq.
            rewrite <-Huid_eq in H. done.
          + pose proof (Hno_duplicate_uid _ _ _ _ Hlookup_p Hparent_key_in_abs Huid_eq) as ->.
            destruct Hlookup_children as [(Hkey_p_eq_new & <-) | (Hkey_p_neq' & Hlookup_children)]; [done|].
            rewrite lookup_insert_Some in Hlookup_children.
            destruct Hlookup_children as [(Hkey_p_eq_new & <-) | (Hkey_p_neq'' & Hlookup_children)]; [set_solver|done].
        - destruct Hlookup_p as [(<- & <-) | (Hkey_p_neq & Hlookup_p)].
          + rewrite Hcreated_pure_pod_uiq_eq in Hobj_has_controller_parent_of.
            pose proof (Hparent_uid_is_used _ _ _ _ _ Hlookup_c Hobj_has_controller_parent_of).
            done.
          + destruct Hlookup_children as [(Hkey_p_eq_new & <-) | (Hkey_p_neq' & Hlookup_children)]; [done|].
            rewrite lookup_insert_Some in Hlookup_children.
            destruct Hlookup_children as [(<- & <-) | (Hkey_p_neq'' & Hlookup_children)].
            * rewrite Hparent_key_in_abs in Hlookup_p. injection Hlookup_p as <-.
              pose proof ((proj2 (Hchildren_point_to_parent _ _ _ _ _ Hparent_key_in_abs Hlookup_c Hparent_key_in_children))).
              set_solver.
            * pose proof ((proj2 (Hchildren_point_to_parent _ _ _ _ _ Hlookup_p Hlookup_c Hlookup_children)) Hobj_has_controller_parent_of).
              done.
      }
    }
    { intros k obj kind name uid Hlookup_abs Hhas_parent.
      unfold abs_state' in Hlookup_abs.
      rewrite lookup_insert_Some in Hlookup_abs.
      destruct Hlookup_abs as [(<- & <-) | (Hk_neq & Hlookup_abs)].
      - assert (well_formed_kobject (KObject.Pod created_pure_pod)) as Hwell_formed_kobject by done.
        pose proof (well_formed_obj_has_at_most_one_controller_parent (KObject.Pod created_pure_pod) Hwell_formed_kobject
          _ _ _ _ _ _ Hhas_parent Hcreated_pure_pod_has_controller_parent_of_owned_parent) as (Hkind_eq & Hname_eq & ->).
        pose proof (Hexisting_uid_is_used parent_key owned_parent Hparent_key_in_abs).
        unfold used_uid'. set_solver.
      - pose proof (Hparent_uid_is_used k obj kind name uid Hlookup_abs Hhas_parent).
        unfold used_uid'. set_solver.
    }
  }
  wp_apply (wp_Mutex__Unlock _ (is_kubernetes_state_inner γ_state γ_children γ_fresh_keys)
    with "[$Hown_Mutex $Hstate_m_addr $Hstate_used_uid_addr $Hstate_rvc_addr $Hown_phys $Hown_used_uid $Hown_abs $Hphys_abs_rep $Hown_children $Hown_fresh_keys]").
  { iFrame "#". }
  iApply "HΦ". iFrame "Hreturned_ptr". iFrame. done.
Qed.

Lemma wp_PodCreate_without_name_ptsto_mut namespace to_create_pod_ptr to_create_pod
  γ_state γ_children γ_fresh_keys parent_key owned_parent owned_child_keys:
  {{{ is_pkg_init apimodel ∗
      "#inv" ∷ is_kubernetes_state γ_state γ_children γ_fresh_keys ∗
      "own_parent" ∷ parent_key [[ γ_state ]]↦ owned_parent ∗
      "own_child_keys" ∷ parent_key [[ γ_children ]]↦ owned_child_keys ∗
      "%namespace_valid" ∷ ⌜ namespace = parent_key.(KKey.Namespace') ⌝ ∗
      "to_create_pod_ptr" ∷ to_create_pod_ptr ↦ to_create_pod ∗
      "parent_uid" ∷ has_controller_parent_of to_create_pod.(v1.Pod.ObjectMeta').(v1.ObjectMeta.OwnerReferences') (extract_kobject_metadata owned_parent).(v1.ObjectMeta.UID') ∗
      "#well_formed_to_create_Pod" ∷ well_formed_to_create_Pod to_create_pod ∗
      "%to_create_pod_namespace_valid" ∷ ⌜ to_create_pod.(v1.Pod.ObjectMeta').(v1.ObjectMeta.Namespace') = namespace ∨ to_create_pod.(v1.Pod.ObjectMeta').(v1.ObjectMeta.Namespace') = ""%go ⌝ ∗
      "%to_create_pod_name_valid" ∷ ⌜ to_create_pod.(v1.Pod.ObjectMeta').(v1.ObjectMeta.Name') = ""%go ⌝
  }}}
    @! apimodel.PodCreate #namespace #to_create_pod_ptr
  {{{ created_pod_ptr (err: error.t) created_pod new_key, RET (#created_pod_ptr, #err);
      ⌜ err = interface.nil ⌝ ∗
      created_pod_ptr ↦ created_pod ∗
      well_formed_Pod created_pod ∗
      ⌜ new_key = extract_pod_key created_pod ⌝ ∗
      ⌜ new_key ∉ owned_child_keys ⌝ ∗
      new_key [[ γ_state ]]↦ (KObject.Pod created_pod) ∗
      parent_key [[ γ_state ]]↦ owned_parent ∗
      parent_key [[ γ_children ]]↦ (owned_child_keys ∪ {[new_key]})
      (* TODO: specify that created_pod shares some contents with to_create_pod *)
  }}}.
Proof.
Admitted.

(* TODO: Revisit this spec and see if owned_grandchild_keys is necessary *)
Lemma wp_objDelete_pod_ptsto_mut key
  γ_state γ_children γ_fresh_keys owned_pod parent_key owned_child_keys owned_grandchild_keys:
  {{{ is_pkg_init apimodel ∗
      "#inv" ∷ is_kubernetes_state γ_state γ_children γ_fresh_keys ∗
      "own_pod" ∷ key [[ γ_state ]]↦ (KObject.Pod owned_pod) ∗
      "own_child_keys" ∷ parent_key [[ γ_children ]]↦ owned_child_keys ∗
      "own_grandchild_keys" ∷ key [[ γ_children ]]↦ owned_grandchild_keys ∗
      "%pod_is_child" ∷ ⌜ key ∈ owned_child_keys ⌝ ∗
      "%kind" ∷ ⌜ KKey.Kind' key = "Pod"%go ⌝
  }}}
    @! apimodel.objDelete #key
  {{{ (err: error.t) pod, RET #err;
      "err_is_nil" ∷ ⌜ err = interface.nil ⌝ ∗
      "pod_updated_or_deleted" ∷ ("pod_updated" ∷ (
        "own_pod" ∷ key [[ γ_state ]]↦ (KObject.Pod pod) ∗
        "own_child_keys" ∷ parent_key [[ γ_children ]]↦ owned_child_keys ∗
        "own_grandchild_keys" ∷ key [[ γ_children ]]↦ owned_grandchild_keys ∗
        "%deletiontimestamp_notnull" ∷ ⌜ pod.(v1.Pod.ObjectMeta').(v1.ObjectMeta.DeletionTimestamp') ≠ null ⌝
      ) ∨
      "own_child_keys" ∷ parent_key [[ γ_children ]]↦ (owned_child_keys ∖ {[key]}))
  }}}.
Proof.
  wp_start as "H". iNamed "H".
  wp_apply wp_with_defer.
  iIntros (defer) "defer". simpl subst. wp_auto. iRename "key" into "key_ptr".
  wp_apply wp_globals_get.
  wp_apply wp_Mutex__Lock; [done|].
  iIntros "[own_Mutex H]". iNamed "H". wp_auto.
  wp_apply wp_globals_get. wp_apply wp_globals_get.
  iAssert (⌜ abs_state !! key = Some (KObject.Pod owned_pod) ⌝%I) with "[own_pod own_abs]" as "%key_in_abs".
  { iDestruct (map_valid with "own_abs own_pod") as %Hlookup. iPureIntro; exact Hlookup. }
  iAssert (⌜ children !! parent_key = Some owned_child_keys ⌝%I) with "[own_children own_child_keys]" as "%parent_key_in_children".
  { iDestruct (map_valid with "own_children own_child_keys") as %Hlookup. iPureIntro; exact Hlookup. }
  iAssert (⌜ children !! key = Some owned_grandchild_keys ⌝%I) with "[own_children own_grandchild_keys]" as "%key_in_children".
  { iDestruct (map_valid with "own_children own_grandchild_keys") as %Hlookup. iPureIntro; exact Hlookup. }
  iAssert (⌜ ∃ obj, phys_state !! key = Some obj ⌝%I) with "[phys_abs_rep]" as "%key_in_phys".
  {
    iDestruct (big_sepM2_lookup_r with "phys_abs_rep") as (obj key_in_phys) "_".
    { exact key_in_abs. }
    iPureIntro. exists obj. exact key_in_phys.
  }
  destruct key_in_phys as [obj key_in_phys].
  iDestruct (big_sepM2_split_singleton _ key _ _ phys_state abs_state key_in_phys key_in_abs with "phys_abs_rep") as "[k_rep other_rep]".
  destruct decide_kind_is_pod with (KKey.Kind' key) as [kind_is_pod kind_is_not_replicaset].
  { done. }
  iAssert (∃ (ptr: loc) (pod: v1.Pod.t), pod_rep key obj (KObject.Pod owned_pod) ptr pod)%I 
  with "[k_rep]" as "(%ptr & %pod & pod_rep)".
  { unfold obj_rep. rewrite kind_is_pod. done. }
  iNamed "pod_rep".
  inversion abs_v_is_pod as [Heq]. symmetry in Heq. subst. clear abs_v_is_pod.
  wp_apply (wp_map_get with "[$own_phys]"). iIntros "own_phys". wp_auto.
  rewrite /is_Some key_in_phys. wp_auto.
  wp_apply wp_Accessor.
  { done. }
  iIntros (ret err) "(-> & ->)". wp_auto.
  assert ((bool_decide (interface.nil = interface.nil)) = true) as nil_is_nil.
  { rewrite bool_decide_true //. }
  rewrite nil_is_nil. wp_auto.
  iDestruct (struct_fields_split with "pod_ptr") as "H". iNamed "H".
  wp_apply (wp_GetFinalizers with "[$HObjectMeta]").
  iIntros (finalizers) "(-> & HObjectMeta)". wp_auto.
  wp_if_destruct.
  - wp_apply (wp_GetDeletionTimestamp with "[$HObjectMeta]").
    iIntros (deletion_timestamp) "(-> & HObjectMeta)". wp_auto.
    wp_if_destruct.
    + wp_apply v1.wp_Now.
      iIntros (time) "_". wp_auto.
      wp_apply (wp_SetDeletionTimestamp with "[$HObjectMeta]").
      iIntros (meta') "(-> & HObjectMeta)". wp_auto. wp_bind.
      wp_apply wp_globals_get.
      (* TODO: fix the resource version counter overflow in the Go code *)
      wp_apply wp_globals_get. wp_bind. wp_apply wp_globals_get.
      wp_apply wp_strconv_FormatInt. iIntros (rv_str) "_". wp_auto.
      wp_apply (wp_SetResourceVersion with "[$HObjectMeta]").
      iIntros (meta') "(-> & HObjectMeta)". wp_auto.
      iDestruct (struct_fields_combine (v:=v1.Pod.mk _ _ _ _)
        with "[$HTypeMeta $HObjectMeta $HSpec $HStatus]") as "pod_ptr". simpl.
      iDestruct (rename_pod with "pod_ptr") as "(%updated_pod & pod_ptr & %updated_pod_eq)".
      iMod (auth_map.map_update _ _ (KObject.Pod updated_pod) with "own_abs own_pod")
        as "[own_abs own_pod]".
      iAssert (state_rep phys_state (<[key:=KObject.Pod updated_pod]> abs_state) %I)
      with "[pod_ptr other_rep]" as "phys_abs_rep".
      {
        assert (delete key abs_state = delete key (<[key:=KObject.Pod updated_pod]> abs_state)) as ->.
        { rewrite delete_insert_eq. reflexivity. }
        iAssert (("%namespace_match" ∷ ⌜ updated_pod.(v1.Pod.ObjectMeta').(v1.ObjectMeta.Namespace') = (KKey.Namespace' key) ⌝ ∗
                  "%name_match" ∷ ⌜ updated_pod.(v1.Pod.ObjectMeta').(v1.ObjectMeta.Name') = (KKey.Name' key) ⌝ ∗
                  "#well_formed_Pod" ∷ well_formed_Pod updated_pod)%I)
        as "(% & % & #well_formed_Pod')".
        {
          unfold well_formed_Pod. unfold well_formed_ObjectMeta.
          subst updated_pod. simpl. iFrame "#". done.
        }
        iAssert (obj_rep key (interface.mk (ptrT.id v1.Pod.id) (# ptr)) (KObject.Pod updated_pod)%I)
        with "[pod_ptr]" as "k_rep".
        { unfold obj_rep. rewrite kind_is_pod. iExists ptr, updated_pod. unfold pod_rep. iFrame. iFrame "#". done. }
        assert ((<[key:=KObject.Pod updated_pod]> abs_state) !! key = Some (KObject.Pod updated_pod)) as key_in_new_abs.
        { rewrite lookup_insert. destruct (decide (key = key)) as [|Hcontra]; [reflexivity | contradiction]. }
        iApply (big_sepM2_split_singleton _ key _ (KObject.Pod updated_pod) phys_state (<[key:=KObject.Pod updated_pod]> abs_state)
          key_in_phys key_in_new_abs with "[k_rep other_rep]").
        iFrame.
      }
      iAssert (kubernetes_state_consistent (dom used_uid) (<[key:=KObject.Pod updated_pod]> abs_state) children fresh_keys %I)
      as "consistent'".
      {
        iNamed "consistent".
        assert (parent_key ≠ key) as parent_neq_key.
        { specialize (no_self_parenting parent_key owned_child_keys key parent_key_in_children pod_is_child). done. }
        assert (dom (<[key:=KObject.Pod updated_pod]> abs_state) = dom abs_state) as abs_dom_simpl.
        {
          rewrite dom_insert_L.
          assert ({[key]} ∪ dom abs_state = dom abs_state) as union_eq.
          { set_solver. }
          rewrite union_eq.
          reflexivity.
        }
        assert ((extract_kobject_metadata (KObject.Pod updated_pod)).(v1.ObjectMeta.OwnerReferences') = (extract_kobject_metadata (KObject.Pod owned_pod)).(v1.ObjectMeta.OwnerReferences'))
        as updated_pod_owner_references_eq.
        { simpl. subst updated_pod. simpl. reflexivity. }
        assert ((extract_kobject_metadata (KObject.Pod updated_pod)).(v1.ObjectMeta.UID') = (extract_kobject_metadata (KObject.Pod owned_pod)).(v1.ObjectMeta.UID'))
        as updated_pod_uid_eq.
        { simpl. subst updated_pod. simpl. reflexivity. }
        iSplitR; [|iSplitR; [|iSplitR; [|iSplitR; [|iSplitR; [|iSplitR; [|iSplitR; [|iSplitR; [|iSplitR; [|iSplitR; [|iSplitR ]]]]]]]]]].
        { iPureIntro. set_solver. }
        { iPureIntro. intros k s Hlookup. specialize (children_exist k s Hlookup). rewrite dom_insert_L. set_solver. }
        { iPureIntro. apply parents_children_same_namespace. }
        { iPureIntro. apply no_self_parenting. }
        { iPureIntro. apply children_disjoint. }
        { iPureIntro. rewrite dom_insert_L. set_solver. }
        { iPureIntro. apply fresh_keys_reserved. }
        {
          iPureIntro.
          intros k1 k2 obj1 obj2 Hlookup1 Hlookup2 Huid_eq.
          rewrite lookup_insert_Some in Hlookup1.
          rewrite lookup_insert_Some in Hlookup2.
          destruct Hlookup1 as [(Hk1_eq & Hobj1_eq) | (Hk1_neq & Hlookup_obj1)];
          destruct Hlookup2 as [(Hk2_eq & Hobj2_eq) | (Hk2_neq & Hlookup_obj2)].
          - subst k1 k2. done.
          - subst k1. eapply no_duplicate_uid; [eauto|eauto|].
            rewrite -Huid_eq -Hobj1_eq. done.
          - subst k2. eapply no_duplicate_uid; [eauto|eauto|].
            rewrite Huid_eq -Hobj2_eq. done.
          - eapply no_duplicate_uid; [eauto|eauto|done].
        }
        {
          iPureIntro.
          intros k obj Hlookup.
          rewrite lookup_insert_Some in Hlookup.
          destruct Hlookup as [(Hk_eq & Hobj_eq) | (Hk_neq & Hlookup_obj)].
          - subst k obj. rewrite updated_pod_uid_eq. eapply existing_uid_is_used. done.
          - eapply existing_uid_is_used. done.
        }
        {
          iModIntro.
          iIntros (k s parent child_key child) "(%Hlookup_children & %Hlookup_child & %Hlookup_parent & %Hchild_in_s)".
          rewrite lookup_insert_Some in Hlookup_child.
          rewrite lookup_insert_Some in Hlookup_parent.
          destruct Hlookup_child as [(Heq_child & Hchild_eq) | (Hneq_child & Hlookup_child)];
          destruct Hlookup_parent as [(Heq_parent & Hparent_eq) | (Hneq_parent & Hlookup_parent)].
          - subst child_key k child parent.
            exfalso. by apply (no_self_parenting key s key Hlookup_children Hchild_in_s).
          - subst child_key child.
            rewrite updated_pod_owner_references_eq. iApply "children_point_to_parent". done.
          - subst k parent.
            rewrite updated_pod_uid_eq. iApply "children_point_to_parent". done.
          - iApply ("children_point_to_parent" $! k s parent child_key child). iPureIntro. done.
        }
        {
          iModIntro.
          iIntros (k s parent child_key child) "[(%Hlookup_children & %Hlookup_child & %Hlookup_parent) Hmeta]".
          rewrite lookup_insert_Some in Hlookup_child.
          rewrite lookup_insert_Some in Hlookup_parent.
          destruct Hlookup_child as [(Heq_child & Hchild_eq) | (Hneq_child & Hlookup_child)];
          destruct Hlookup_parent as [(Heq_parent & Hparent_eq) | (Hneq_parent & Hlookup_parent)].
          - subst child_key k child parent.
            rewrite updated_pod_owner_references_eq updated_pod_uid_eq.
            iDestruct ("only_children_point_to_parent" $! key s (KObject.Pod owned_pod) key (KObject.Pod owned_pod)
              with "[Hmeta]") as "%Hkey_in_s".
            { iFrame "Hmeta". iPureIntro. split; [|split]; done. }
            exfalso. by apply (no_self_parenting key s key Hlookup_children Hkey_in_s).
          - subst child_key child.
            rewrite updated_pod_owner_references_eq.
            iApply ("only_children_point_to_parent" $! k s parent key (KObject.Pod owned_pod) with "[Hmeta]").
            iFrame "Hmeta". iPureIntro. split; [|split]; done.
          - subst k parent.
            rewrite updated_pod_uid_eq.
            iApply ("only_children_point_to_parent" $! key s (KObject.Pod owned_pod) child_key child with "[Hmeta]").
            iFrame "Hmeta". iPureIntro. split; [|split]; done.
          - iApply ("only_children_point_to_parent" $! k s parent child_key child with "[Hmeta]").
            iFrame "Hmeta". iPureIntro. split; [|split]; done.
        }
        {
          iModIntro.
          iIntros (k obj uid) "%Hlookup".
          rewrite lookup_insert_Some in Hlookup.
          destruct Hlookup as [(Hk_eq & Hobj_eq) | (Hk_neq & Hlookup_obj)].
          - subst k obj. rewrite updated_pod_owner_references_eq.
            iApply "parent_uid_is_used". done.
          - iApply ("parent_uid_is_used" $! k obj uid). done.
        }
      }
      wp_apply (wp_Mutex__Unlock _ (is_kubernetes_state_inner γ_state γ_children γ_fresh_keys)
      with "[$own_Mutex state_m_addr state_used_uid_addr state_rvc_addr own_phys own_used_uid own_abs phys_abs_rep own_children own_fresh_keys]").
      { iFrame. iFrame "#". }
      iApply "HΦ". iFrame. iSplitR; [done|]. iLeft. iFrame.
      iAssert (⌜ now_ptr ≠ null ⌝%I) with "[now]" as "%now_ptr_not_null".
      { by iDestruct (typed_pointsto_not_null with "now") as %?. }
      iPureIntro. subst updated_pod. done.
    + iDestruct (struct_fields_combine (V:=v1.Pod.t) with "[$HTypeMeta $HObjectMeta $HSpec $HStatus]") as "pod_ptr".
      iAssert (state_rep phys_state abs_state %I) with "[pod_ptr other_rep]" as "phys_abs_rep".
      {
        iApply big_sepM2_split_singleton; [done | done|]. iFrame. unfold obj_rep. rewrite kind_is_pod.
        iExists ptr, owned_pod. iFrame. iFrame "#". done.
      }
      wp_apply (wp_Mutex__Unlock _ (is_kubernetes_state_inner γ_state γ_children γ_fresh_keys)
        with "[$own_Mutex state_m_addr state_used_uid_addr state_rvc_addr own_phys own_used_uid own_abs phys_abs_rep own_children own_fresh_keys]").
      { iFrame. iFrame "#". }
      iApply "HΦ". iSplitR; [done|]. iLeft. iFrame. done.
  - wp_apply wp_globals_get.
    wp_apply (wp_map_delete with "[$own_phys]").
    iIntros "own_phys". wp_auto.
    iDestruct (struct_fields_combine (V:=v1.Pod.t)
      with "[$HTypeMeta $HObjectMeta $HSpec $HStatus]") as "pod_ptr".
    iMod (auth_map.map_delete with "own_pod own_abs") as "own_abs".
    iMod (auth_map.map_update _ _ (owned_child_keys ∖ {[key]}) with "own_children own_child_keys")
      as "[own_children own_child_keys]".
    iMod (auth_map.map_delete with "own_grandchild_keys own_children") as "own_children".
    iAssert (state_rep (delete key phys_state) (delete key abs_state) %I) with "[other_rep]" as "phys_abs_rep".
    { done. }
    iAssert (kubernetes_state_consistent (dom used_uid) (delete key abs_state) (delete key (<[parent_key:=owned_child_keys ∖ {[key]}]> children)) fresh_keys %I)
    as "consistent'".
    {
      iNamed "consistent".
      assert (parent_key ≠ key) as parent_neq_key.
      { specialize (no_self_parenting parent_key owned_child_keys key parent_key_in_children pod_is_child). done. }
      assert (dom (delete key (<[parent_key:=owned_child_keys ∖ {[key]}]> children)) = dom (delete key children) )
      as Hdom_children_eq.
      {
        assert (key ≠ parent_key) as key_neq_parent by (symmetry; exact parent_neq_key).
        rewrite !dom_delete_L dom_insert_L.
        assert (parent_key ∈ dom children) as parent_in_children_dom.
        { apply elem_of_dom. exists owned_child_keys. exact parent_key_in_children. }
        assert ({[parent_key]} ∪ dom children = dom children) as union_eq.
        { set_solver. }
        rewrite union_eq.
        reflexivity.
      }
      iSplitR; [|iSplitR; [|iSplitR; [|iSplitR; [|iSplitR; [|iSplitR; [|iSplitR; [|iSplitR; [|iSplitR; [|iSplitR; [|iSplitR ]]]]]]]]]].
      { iPureIntro. set_solver. }
      {
        iPureIntro. intros k s Hlookup.
        rewrite lookup_delete_Some lookup_insert_Some in Hlookup.
        destruct Hlookup as (Hk_neq_key & [(Hk_eq & Hs_eq) | (Hk_neq_parent & Hlookup)]).
        - subst k s. rewrite dom_delete_L.
          assert (owned_child_keys ⊆ dom abs_state) as owned_children_in_abs.
          { apply children_exist with (k := parent_key). exact parent_key_in_children. }
          set_solver.
        - rewrite dom_delete_L.
          assert (s ⊆ dom abs_state) as s_in_abs by (apply children_exist with (k := k); exact Hlookup).
          assert (s ## owned_child_keys) as s_disj_owned.
          { destruct (decide (k = parent_key)); [congruence|]. eapply children_disjoint; done. }
          assert (key ∉ s) as key_not_in_s.
          { intros Hcontra. assert (key ∈ owned_child_keys) by exact pod_is_child. set_solver. }
          set_solver.
      }
      {
        iPureIntro. intros k s child_key Hlookup Hchild_in_s.
        rewrite lookup_delete_Some lookup_insert_Some in Hlookup.
        destruct Hlookup as (Hk_neq_key & [(Hk_eq & Hs_eq) | (Hk_neq_parent & Hlookup)]).
        - subst k s. eapply parents_children_same_namespace; [exact parent_key_in_children | set_solver].
        - eapply parents_children_same_namespace; done.
      }
      {
        iPureIntro. intros k s child_key Hlookup Hchild_in_s.
        rewrite lookup_delete_Some lookup_insert_Some in Hlookup.
        destruct Hlookup as (Hk_neq_key & [(Hk_eq & Hs_eq) | (Hk_neq_parent & Hlookup)]).
        - subst k s. eapply no_self_parenting; [exact parent_key_in_children | set_solver].
        - eapply no_self_parenting; done.
      }
      {
        iPureIntro. intros k1 s1 k2 s2 Hk1_neq_k2 Hlookup1 Hlookup2.
        rewrite lookup_delete_Some lookup_insert_Some in Hlookup1.
        rewrite lookup_delete_Some lookup_insert_Some in Hlookup2.
        destruct Hlookup1 as (Hk1_neq_key & [(Hk1_eq & Hs1_eq) | (Hk1_neq_parent & Hlookup1)]);
        [destruct Hlookup2 as (Hk2_neq_key & [(Hk2_eq & Hs2_eq) | (Hk2_neq_parent & Hlookup2)]) |
         destruct Hlookup2 as (Hk2_neq_key & [(Hk2_eq & Hs2_eq) | (Hk2_neq_parent & Hlookup2)])].
        - subst k1 k2. contradiction.
        - subst k1 s1.
          assert (owned_child_keys ## s2) as disj_orig.
          { apply children_disjoint with (k1 := parent_key) (k2 := k2); [|assumption|assumption].
            intros Heq. subst. contradiction. }
          set_solver.
        - subst k2 s2.
          assert (s1 ## owned_child_keys) as disj_orig.
          { apply children_disjoint with (k1 := k1) (k2 := parent_key); [|assumption|assumption].
            intros Heq. subst. contradiction. }
          set_solver.
        - apply children_disjoint with (k1 := k1) (k2 := k2); assumption.
      }
      { iPureIntro. rewrite dom_delete_L. set_solver. }
      { iPureIntro. apply fresh_keys_reserved. }
      {
        iPureIntro.
        intros k1 k2 obj1 obj2 Hlookup1 Hlookup2 Huid_eq.
        rewrite lookup_delete_Some in Hlookup1.
        rewrite lookup_delete_Some in Hlookup2.
        destruct Hlookup1 as (Hk1_neq_key & Hlookup_obj1).
        destruct Hlookup2 as (Hk2_neq_key & Hlookup_obj2).
        eapply no_duplicate_uid; [eauto|eauto|done].
      }
      {
        iPureIntro.
        intros k obj Hlookup.
        rewrite lookup_delete_Some in Hlookup.
        destruct Hlookup as (Hk_neq_key & Hlookup_obj).
        eapply existing_uid_is_used. done.
      }
      {
        iModIntro.
        iIntros (k s parent child_key child) "(%Hchildren_lookup & %Hchild_lookup & %Hparent_lookup & %Hchild_in_s)".
        rewrite lookup_delete_Some in Hchildren_lookup.
        rewrite lookup_delete_Some in Hchild_lookup.
        rewrite lookup_delete_Some in Hparent_lookup.
        destruct Hchildren_lookup as (Hk_neq_key, Hchildren_lookup).
        destruct Hchild_lookup as (Hchild_key_neq_key, Hchild_lookup).
        destruct Hparent_lookup as (Hk_neq_key', Hparent_lookup).
        rewrite lookup_insert_Some in Hchildren_lookup.
        destruct Hchildren_lookup as [(Hk_eq, Hs_eq) | (Hk_neq_parent, Hchildren_lookup)].
        - subst k s.
          iApply ("children_point_to_parent" $! parent_key owned_child_keys parent child_key child).
          iPureIntro. split; [|split; [|split]]; try done; set_solver.
        - iApply ("children_point_to_parent" $! k s parent child_key child).
          iPureIntro. split; [|split; [|split]]; done.
      }
      {
        iModIntro.
        iIntros (k s parent child_key child) "[(%Hchildren_lookup & %Hchild_lookup & %Hparent_lookup) Hmeta]".
        rewrite lookup_delete_Some in Hchildren_lookup.
        rewrite lookup_delete_Some in Hchild_lookup.
        rewrite lookup_delete_Some in Hparent_lookup.
        destruct Hchildren_lookup as (Hk_neq_key, Hchildren_lookup).
        destruct Hchild_lookup as (Hchild_key_neq_key, Hchild_lookup).
        destruct Hparent_lookup as (Hk_neq_key', Hparent_lookup).
        rewrite lookup_insert_Some in Hchildren_lookup.
        destruct Hchildren_lookup as [(Hk_eq, Hs_eq) | (Hk_neq_parent, Hchildren_lookup)].
        - subst k s.
          iDestruct ("only_children_point_to_parent" $! parent_key owned_child_keys parent child_key child
            with "[Hmeta]") as "%Hchild_in_owned".
          { iFrame "Hmeta". iPureIntro. split; [|split]; done. }
          iPureIntro. set_solver.
        - iDestruct ("only_children_point_to_parent" $! k s parent child_key child
            with "[Hmeta]") as "%Hchild_in_s".
          { iFrame "Hmeta". iPureIntro. split; [|split]; done. }
          iPureIntro. exact Hchild_in_s.
      }
      {
        iModIntro.
        iIntros (k obj uid) "%Hlookup".
        rewrite lookup_delete_Some in Hlookup.
        destruct Hlookup as (Hk_neq_key & Hlookup_obj).
        iApply ("parent_uid_is_used" $! k obj uid). done.
      }
    }
    wp_apply (wp_Mutex__Unlock _ (is_kubernetes_state_inner γ_state γ_children γ_fresh_keys)
      with "[$own_Mutex state_m_addr state_used_uid_addr state_rvc_addr own_phys own_used_uid own_abs phys_abs_rep own_children own_fresh_keys]").
    { iFrame. iFrame "#". }
    iApply "HΦ". iFrame. done.
    Unshelve.
    done.
Qed.

Lemma wp_PodDelete_ptsto_mut namespace name
  γ_state γ_children γ_fresh_keys owned_pod parent_key owned_child_keys owned_grandchild_keys:
  {{{ is_pkg_init apimodel ∗
      "#inv" ∷ is_kubernetes_state γ_state γ_children γ_fresh_keys ∗
      "own_pod" ∷ (mk_pod_key namespace name) [[ γ_state ]]↦ (KObject.Pod owned_pod) ∗
      "own_child_keys" ∷ parent_key [[ γ_children ]]↦ owned_child_keys ∗
      "own_grandchild_keys" ∷ (mk_pod_key namespace name) [[ γ_children ]]↦ owned_grandchild_keys ∗
      "%pod_is_child" ∷ ⌜ (mk_pod_key namespace name) ∈ owned_child_keys ⌝
  }}}
    @! apimodel.PodDelete #namespace #name
  {{{ (err: error.t) pod, RET #err;
      "err_is_nil" ∷ ⌜ err = interface.nil ⌝ ∗
      "pod_updated_or_deleted" ∷ ("pod_updated" ∷ (
        "own_pod" ∷ (mk_pod_key namespace name) [[ γ_state ]]↦ (KObject.Pod pod) ∗
        "own_child_keys" ∷ parent_key [[ γ_children ]]↦ owned_child_keys ∗
        "own_grandchild_keys" ∷ (mk_pod_key namespace name) [[ γ_children ]]↦ owned_grandchild_keys ∗
        "%deletiontimestamp_notnull" ∷ ⌜ pod.(v1.Pod.ObjectMeta').(v1.ObjectMeta.DeletionTimestamp') ≠ null ⌝
      ) ∨
      "own_child_keys" ∷ parent_key [[ γ_children ]]↦ (owned_child_keys ∖ {[mk_pod_key namespace name]}))
  }}}.
Proof.
  wp_start as "H". iNamed "H". wp_auto.
  wp_apply (wp_objDelete_pod_ptsto_mut with "[$own_pod $own_child_keys $own_grandchild_keys]").
  { iFrame "#". done. }
  iIntros (err pod) "H". iNamed "H". wp_auto. iApply "HΦ". iFrame.
Qed.

Lemma wp_objGet_replicaset_ptsto_mut key γ_state γ_children γ_fresh_keys owned_rs:
  {{{ is_pkg_init apimodel ∗
      "#inv" ∷ is_kubernetes_state γ_state γ_children γ_fresh_keys ∗
      "own_rs" ∷ key [[ γ_state ]]↦ (KObject.ReplicaSet owned_rs) ∗
      "%kind" ∷ ⌜ KKey.Kind' key = "ReplicaSet"%go ⌝
  }}}
    @! apimodel.objGet #key
  {{{ obj exists' rs, RET (#obj, #exists');
      ⌜ exists' = true ⌝ ∗
      (∃ (ptr : loc),
          ⌜ obj = interface.mk (ptrT.id v1.ReplicaSet.id) #ptr ⌝ ∗
          ptr ↦ rs
      ) ∗
      deepcopy_ReplicaSet owned_rs rs ∗
      ⌜ rs.(v1.ReplicaSet.ObjectMeta').(v1.ObjectMeta.Namespace') = (KKey.Namespace' key) ⌝ ∗
      ⌜ rs.(v1.ReplicaSet.ObjectMeta').(v1.ObjectMeta.Name') = (KKey.Name' key) ⌝ ∗
      well_formed_ReplicaSet rs ∗
      key [[ γ_state ]]↦ (KObject.ReplicaSet owned_rs)
  }}}.
Proof.
  wp_start as "H". iNamed "H".
  wp_apply wp_with_defer.
  iIntros (defer) "defer". simpl subst. wp_auto. iRename "key" into "key_ptr".
  wp_apply wp_globals_get.
  wp_apply wp_Mutex__Lock.
  { done. }
  iIntros "[own_Mutex H]". iNamed "H". wp_auto.
  wp_apply wp_globals_get. wp_apply wp_globals_get.
  iAssert (⌜ abs_state !! key = Some (KObject.ReplicaSet owned_rs) ⌝%I) with "[own_rs own_abs]" as "%key_in_abs".
  {
    iDestruct (map_valid with "own_abs own_rs") as %Hlookup.
    iPureIntro; exact Hlookup.
  }
  iAssert (⌜ ∃ obj, phys_state !! key = Some obj ⌝%I) with "[phys_abs_rep]" as "%key_in_phys".
  {
    iDestruct (big_sepM2_lookup_r with "phys_abs_rep") as (obj key_in_phys) "_".
    { exact key_in_abs. }
    iPureIntro. exists obj. exact key_in_phys.
  }
  destruct key_in_phys as [obj key_in_phys].
  iDestruct (big_sepM2_lookup_acc _ _ _ _ _ _ key_in_phys key_in_abs with "phys_abs_rep") as "[k_rep other_rep]".
  destruct decide_kind_is_replicaset with (KKey.Kind' key) as [kind_is_replicaset kind_is_not_pod].
  { done. }
  unfold obj_rep. rewrite kind_is_replicaset kind_is_not_pod.
  iDestruct "k_rep" as "(%ptr & %rs0 & rs_rep)". iNamed "rs_rep".
  inversion abs_v_is_rs as [Heq]. symmetry in Heq. subst. clear abs_v_is_rs.
  wp_apply (wp_map_get with "[$own_phys]"). iIntros "own_phys". wp_auto.
  rewrite /is_Some key_in_phys. wp_auto.
  wp_apply (wp_deepCopy_replicaset with "[$rs_ptr]").
  { iPureIntro. reflexivity. }
  iIntros (obj' ptr' rs') "(%obj'_is_ptr & ptr' & rs'_is_deepcopy_rs & rs_ptr)".
  iPoseProof (well_formed_preserved_by_deepcopy_ReplicaSet owned_rs rs' (KKey.Namespace' key) (KKey.Name' key)
  with "[$rs'_is_deepcopy_rs] [%] [%] [$well_formed_ReplicaSet]") as "(rs'_is_deepcopy_rs & _ & % & % & #rs'_well_formed)".
  { done. }
  { done. }
  wp_auto.
  iAssert (state_rep phys_state abs_state %I) with "[rs_ptr other_rep]" as "phys_abs_rep".
  { iApply "other_rep". iExists ptr, owned_rs. iFrame. iFrame "#". done. }
  wp_apply (wp_Mutex__Unlock _ (is_kubernetes_state_inner γ_state γ_children γ_fresh_keys)
  with "[$own_Mutex state_m_addr state_used_uid_addr state_rvc_addr own_phys own_used_uid own_abs phys_abs_rep own_children own_fresh_keys consistent]").
  { iFrame. iFrame "#". }
  iApply ("HΦ" $! obj' true).
  iSplitR.
  { iPureIntro. done. }
  iFrame. iFrame "#".
  iPureIntro. done.
Qed.

Lemma wp_ReplicaSetMutGet_ptsto_mut namespace name γ_state γ_children γ_fresh_keys owned_rs:
  {{{ is_pkg_init apimodel ∗
      "#inv" ∷ is_kubernetes_state γ_state γ_children γ_fresh_keys ∗
      "own_rs" ∷ (mk_replicaset_key namespace name) [[ γ_state ]]↦ (KObject.ReplicaSet owned_rs)
  }}}
    @! apimodel.ReplicaSetMutGet #namespace #name
  {{{ l (err: error.t) rs, RET (#l, #err);
      ⌜ err = interface.nil ⌝ ∗
      (mk_replicaset_key namespace name) [[ γ_state ]]↦ (KObject.ReplicaSet owned_rs) ∗
      l ↦ rs ∗
      deepcopy_ReplicaSet owned_rs rs ∗
      ⌜ rs.(v1.ReplicaSet.ObjectMeta').(v1.ObjectMeta.Namespace') = namespace ⌝ ∗
      ⌜ rs.(v1.ReplicaSet.ObjectMeta').(v1.ObjectMeta.Name') = name ⌝ ∗
      well_formed_ReplicaSet rs
  }}}.
Proof.
  wp_start as "H". iNamed "H". wp_auto.
  wp_apply (wp_objGet_replicaset_ptsto_mut with "[$own_rs]").
  { iFrame "#". done. }
  iIntros (obj exists' rs') "(%exists'_is_true & (%ptr & %obj_is_ptr & ptr) & deepcopy & % & % & #well_formed & own_rs)".
  subst exists' obj.
  wp_auto.
  unshelve wp_apply wp_interface_checked_type_assert; try tc_solve.
  { iPureIntro. intros ptr_id. exists ptr. done. }
  iIntros (y ok) "%if_ok".
  assert (ok = true) as ok_is_true.
  { destruct ok; [done|]. intuition. }
  subst ok. inversion if_ok.
  assert (ptr = y) as ptr_is_y.
  { apply (inj to_val). done. }
  subst ptr.
  wp_auto.
  iApply "HΦ".
  iFrame. iFrame "#". iPureIntro. done.
Qed.

Lemma wp_ReplicaSetGet_ptsto_mut namespace name γ_state γ_children γ_fresh_keys owned_rs:
  {{{ is_pkg_init apimodel ∗
      "#inv" ∷ is_kubernetes_state γ_state γ_children γ_fresh_keys ∗
      "own_rs" ∷ (mk_replicaset_key namespace name) [[ γ_state ]]↦ (KObject.ReplicaSet owned_rs)
  }}}
    @! apimodel.ReplicaSetGet #namespace #name
  {{{ l (err: error.t) rs dq, RET (#l, #err);
      ⌜ err = interface.nil ⌝ ∗
      (mk_replicaset_key namespace name) [[ γ_state ]]↦ (KObject.ReplicaSet owned_rs) ∗
      l ↦{dq} rs ∗
      deepcopy_ReplicaSet owned_rs rs ∗
      ⌜ rs.(v1.ReplicaSet.ObjectMeta').(v1.ObjectMeta.Namespace') = namespace ⌝ ∗
      ⌜ rs.(v1.ReplicaSet.ObjectMeta').(v1.ObjectMeta.Name') = name ⌝ ∗
      well_formed_ReplicaSet rs
  }}}.
Proof.
  wp_start as "H". iNamed "H". wp_auto.
  wp_apply (wp_ReplicaSetMutGet_ptsto_mut with "[$own_rs]").
  { done. }
  iIntros (l err rs') "(%err_is_nil & own_rs & l & deepcopy & % & % & #well_formed)".
  wp_auto.
  iApply "HΦ". iFrame. iFrame "#". done.
Qed.

End proof.
