From Perennial.algebra Require Export auth_map auth_set.
Require Export New.proof.sync.
From New.proof.kubernetes_model Require Export apimodel_init.
From New.proof.k8s_io.apimachinery.pkg.api Require Export meta.
From New.proof.k8s_io.apimachinery.pkg.apis.meta Require Export v1.
From New.proof Require Import prelude empty_ffi.
From New.proof Require Export pure_objects string.
From New.proof.big_op Require Export big_sepL big_sepM.

Section proof.
Context `{hG: !heapGS Σ} {go_ctx: GoContext}.
Context `{!mapG Σ KKey.t interface.t}.
Context `{!mapG Σ KKey.t PureKObject.t}.
Context `{!mapG Σ KKey.t (gset KKey.t)}.
Context `{!auth_setG Σ KKey.t}.

Definition mk_pod_key (namespace name: go_string) : KKey.t :=
  {| KKey.Kind' := "Pod"%go; KKey.Namespace' := namespace; KKey.Name' := name;|}.

Definition extract_pod_key pod : KKey.t :=
  mk_pod_key pod.(v1.Pod.ObjectMeta').(v1.ObjectMeta.Namespace') pod.(v1.Pod.ObjectMeta').(v1.ObjectMeta.Name').

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

Definition pod_rep v1 v2 ptr pod pure_pod : iProp Σ :=
  "%Hinterface_is_pod_ptr" ∷ ⌜ v1 = interface.mk (ptrT.id v1.Pod.id) #ptr ⌝ ∗
  "%Habs_v_is_pod" ∷ ⌜ v2 = PureKObject.Pod pure_pod ⌝ ∗
  "Hdeepown_l_pod" ∷ PurePod.deepown_l ptr pod pure_pod 1.

Definition replicaset_rep v1 v2 ptr rs pure_rs : iProp Σ :=
  "%Hinterface_is_rs_ptr" ∷ ⌜ v1 = interface.mk (ptrT.id v1.ReplicaSet.id) #ptr ⌝ ∗
  "%Habs_v_is_rs" ∷ ⌜ v2 = PureKObject.ReplicaSet pure_rs ⌝ ∗
  "Hdeepown_l_rs" ∷ PureReplicaSet.deepown_l ptr rs pure_rs 1.

Definition obj_rep k v1 v2 : iProp Σ :=
  (if bool_decide (KKey.Kind' k = "Pod"%go) then
    ∃ (ptr: loc) (pod: v1.Pod.t) (pure_pod: PurePod.t), pod_rep v1 v2 ptr pod pure_pod
  else if bool_decide (KKey.Kind' k = "ReplicaSet"%go) then
    ∃ (ptr: loc) (rs: v1.ReplicaSet.t) (pure_rs: PureReplicaSet.t), replicaset_rep v1 v2 ptr rs pure_rs
  else False)%I.

Definition state_rep (phys_state: gmap KKey.t interface.t) (abs_state: gmap KKey.t PureKObject.t) : iProp Σ :=
  [∗ map] k ↦ v1; v2 ∈ phys_state; abs_state, obj_rep k v1 v2.

Record ghost_well_formed (used_uid: gset go_string) (abs_state: gmap KKey.t PureKObject.t) (children: gmap KKey.t (gset KKey.t)) (fresh_keys: gset KKey.t) : Prop :=
mk_ghost_well_formed {
  Habs_state_well_formed: (∀ k obj, abs_state !! k = Some obj → PureKObject.agree_with_key obj k ∧ PureKObject.well_formed obj);
  Hparents_exist: (dom children = dom abs_state);
  Hchildren_exist : (∀ k s, children !! k = Some s → s ⊆ dom abs_state);
  Hparents_children_same_namespace: (∀ k s child_key, children !! k = Some s → child_key ∈ s → k.(KKey.Namespace') = child_key.(KKey.Namespace'));
  Hno_self_parenting: (∀ k s child_key, children !! k = Some s → child_key ∈ s → child_key ≠ k);
  Hchildren_disjoint: (∀ k1 s1 k2 s2, k1 ≠ k2 → children !! k1 = Some s1 → children !! k2 = Some s2 → s1 ## s2);
  Hfresh_keys_absent: (fresh_keys ## dom abs_state);
  Hfresh_keys_reserved: (∀ k, k ∈ fresh_keys → reserved_derived_name k.(KKey.Name'));
  Hno_duplicate_uid: (∀ k1 k2 obj1 obj2, abs_state !! k1 = Some obj1 → abs_state !! k2 = Some obj2 →
    (PureKObject.metadata obj1).(PureObjectMeta.UID') = (PureKObject.metadata obj2).(PureObjectMeta.UID') → k1 = k2);
  Hexisting_uid_is_used: (∀ k obj, abs_state !! k = Some obj → (PureKObject.metadata obj).(PureObjectMeta.UID') ∈ used_uid);
  Hchildren_point_to_parent: (∀ key_p obj_p key_c obj_c s,
    abs_state !! key_p = Some obj_p → abs_state !! key_c = Some obj_c → children !! key_p = Some s →
      (key_c ∈ s ↔ obj_has_controller_parent_of obj_c key_p.(KKey.Kind') key_p.(KKey.Name') (PureKObject.metadata obj_p).(PureObjectMeta.UID')));
  Hparent_uid_is_used: (∀ k obj kind name uid, abs_state !! k = Some obj →
    obj_has_controller_parent_of obj kind name uid → uid ∈ used_uid);
}.

Record KubernetesGname := mk_γk {
  γ_state : gname;
  γ_children : gname;
  γ_fresh_keys : gname;
}.

Definition kubernetes_inv γ l: iProp Σ :=
  ∃ (phys_state_l: loc) (used_uid_l: loc) (rvc: w64)
    (phys_state: gmap KKey.t interface.t) (used_uid: gmap go_string unit)
    (abs_state: gmap KKey.t PureKObject.t) (children: gmap KKey.t (gset KKey.t)) (fresh_keys: gset KKey.t),
    "Hstate_m_addr" ∷ l ↦s[apimodel.State :: "m"] phys_state_l ∗
    "Hstate_used_uid_addr" ∷ l ↦s[apimodel.State :: "usedUID"] used_uid_l ∗
    "Hstate_rvc_addr" ∷ l ↦s[apimodel.State :: "resourceVersionCounter"] rvc ∗
    "Hown_phys" ∷ phys_state_l ↦$ phys_state ∗
    "Hown_used_uid" ∷ used_uid_l ↦$ used_uid ∗
    "Hown_abs" ∷ map_ctx γ.(γ_state) 1 abs_state ∗
    "Hown_children" ∷ map_ctx γ.(γ_children) 1 children ∗
    "Hown_fresh_keys" ∷ auth_set_auth γ.(γ_fresh_keys) fresh_keys ∗
    "Hphys_abs_rep" ∷ state_rep phys_state abs_state ∗
    "%Hghost_well_formed" ∷ ⌜ ghost_well_formed (dom used_uid) abs_state children fresh_keys ⌝.

Definition is_kubernetes γ l : iProp Σ :=
  ∃ (mu_l: loc),
    "Hmu" ∷ l ↦s[apimodel.State :: "mu"]□ mu_l ∗
    "Hkinv" ∷ is_Mutex mu_l (kubernetes_inv γ l).

Lemma wp_deepCopy_pod (obj: interface.t) (ptr: loc) (pod: v1.Pod.t) (pure_pod: PurePod.t):
  {{{ is_pkg_init apimodel ∗
      ⌜ obj = interface.mk (ptrT.id v1.Pod.id) #ptr ⌝ ∗
      PurePod.deepown_l ptr pod pure_pod 1
  }}}
    @! apimodel.deepCopy #obj
  {{{ (ptr': loc) (pod': v1.Pod.t), RET #(interface.mk (ptrT.id v1.Pod.id) #ptr');
      PurePod.deepown_l ptr' pod' pure_pod 1 ∗
      PurePod.deepown_l ptr pod pure_pod 1
  }}}.
Proof.
Admitted.

Lemma wp_deepCopy_replicaset (obj: interface.t) (ptr: loc) (rs: v1.ReplicaSet.t) (pure_rs: PureReplicaSet.t):
  {{{ is_pkg_init apimodel ∗
      ⌜ obj = interface.mk (ptrT.id v1.ReplicaSet.id) #ptr ⌝ ∗
      PureReplicaSet.deepown_l ptr rs pure_rs 1
  }}}
    @! apimodel.deepCopy #obj
  {{{ (ptr': loc) (rs': v1.ReplicaSet.t), RET #(interface.mk (ptrT.id v1.ReplicaSet.id) #ptr');
      PureReplicaSet.deepown_l ptr' rs' pure_rs 1 ∗
      PureReplicaSet.deepown_l ptr rs pure_rs 1
  }}}.
Proof.
Admitted.

Lemma wp_State__generateNewName (l : loc) (m_ptr : loc) (kind namespace prefix generate_name : go_string) (phys_state : gmap KKey.t interface.t):
  {{{ is_pkg_init apimodel ∗
      ⌜ generate_name = prefix ++ "-"%go ∧ ¬ reserved_name prefix ⌝ ∗
      l ↦s[apimodel.State :: "m"] m_ptr ∗
      m_ptr ↦$ phys_state
  }}}
    l @ (ptrT.id apimodel.State.id) @ "generateNewName" #kind #namespace #generate_name
  {{{ (new_name: go_string), RET #new_name;
      ⌜ new_name ≠ ""%go ∧ valid_name new_name ⌝ ∗
      ⌜ phys_state !! {| KKey.Kind' := kind; KKey.Namespace' := namespace; KKey.Name' := new_name;|} = None ⌝ ∗
      ⌜ unreserved_generated_name new_name ⌝ ∗
      l ↦s[apimodel.State :: "m"] m_ptr ∗
      m_ptr ↦$ phys_state
  }}}.
Proof.
Admitted.

Lemma wp_State__generateNewUIDAndUpdate (l : loc) (used_uid_ptr : loc) (used_uid : gmap go_string unit):
  {{{ is_pkg_init apimodel ∗
      l ↦s[apimodel.State :: "usedUID"] used_uid_ptr ∗
      used_uid_ptr ↦$ used_uid
  }}}
    l @ (ptrT.id apimodel.State.id) @ "generateNewUIDAndUpdate" #()
  {{{ (generated_uid : go_string), RET #generated_uid;
      ⌜ used_uid !! generated_uid = None ⌝ ∗
      l ↦s[apimodel.State :: "usedUID"] used_uid_ptr ∗
      used_uid_ptr ↦$ <[generated_uid:=()]> used_uid
  }}}.
Proof.
Admitted.

Lemma wp_fmt_Sprintf (format: go_string) string_slice (string_list: list interface.t):
  {{{ is_pkg_init fmt ∗
      string_slice ↦* string_list
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

End proof.
