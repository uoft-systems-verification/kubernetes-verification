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
Context `{!mapG Σ KKey.t KObjectV.t}.
Context `{!mapG Σ KKey.t (gset KKey.t)}.
Context `{!auth_setG Σ KKey.t}.

Definition mk_pod_key (namespace name: go_string) : KKey.t :=
  {| KKey.Kind' := "Pod"%go; KKey.Namespace' := namespace; KKey.Name' := name;|}.

Definition mk_replicaset_key (namespace name: go_string) : KKey.t :=
  {| KKey.Kind' := "ReplicaSet"%go; KKey.Namespace' := namespace; KKey.Name' := name;|}.

Definition pod_rep interface_obj ptr (pod: v1.Pod.t) pure_pod : iProp Σ :=
  "%Hinterface_is_pod_ptr" ∷ ⌜ interface_obj = interface.mk (ptrT.id v1.Pod.id) #ptr ⌝ ∗
  "Hdeepown_l_pod" ∷ PodV.deepown_l ptr pure_pod 1.

Definition replicaset_rep interface_obj ptr (rs: v1.ReplicaSet.t) pure_rs : iProp Σ :=
  "%Hinterface_is_rs_ptr" ∷ ⌜ interface_obj = interface.mk (ptrT.id v1.ReplicaSet.id) #ptr ⌝ ∗
  "Hdeepown_l_rs" ∷ ReplicaSetV.deepown_l ptr pure_rs 1.

Definition state_rep (phys_state: gmap KKey.t interface.t) (abs_state: gmap KKey.t KObjectV.t) : iProp Σ :=
  [∗ map] interface_obj; pure_obj ∈ phys_state; abs_state, ∃ ptr (obj: KObject.t),
    ⌜ KObjectV.valid_interface interface_obj ptr pure_obj ⌝ ∗ KObjectV.deepown_l ptr pure_obj 1.

Record ghost_valid (used_uid: gset go_string) (abs_state: gmap KKey.t KObjectV.t) (children: gmap KKey.t (gset KKey.t)) (fresh_keys: gset KKey.t) : Prop :=
mk_ghost_valid {
  Habs_state_valid: (∀ k obj, abs_state !! k = Some obj → k = KObjectV.key obj ∧ KObjectV.valid_old obj);
  Hparents_exist: (dom children = dom abs_state);
  Hchildren_exist : (∀ k s, children !! k = Some s → s ⊆ dom abs_state);
  Hparents_children_same_namespace: (∀ k s child_key, children !! k = Some s → child_key ∈ s → k.(KKey.Namespace') = child_key.(KKey.Namespace'));
  Hno_self_parenting: (∀ k s child_key, children !! k = Some s → child_key ∈ s → child_key ≠ k);
  Hchildren_disjoint: (∀ k1 s1 k2 s2, k1 ≠ k2 → children !! k1 = Some s1 → children !! k2 = Some s2 → s1 ## s2);
  Hfresh_keys_absent: (fresh_keys ## dom abs_state);
  Hfresh_keys_reserved: (∀ k, k ∈ fresh_keys → reserved_derived_name k.(KKey.Name'));
  Hno_duplicate_uid: (∀ k1 k2 obj1 obj2, abs_state !! k1 = Some obj1 → abs_state !! k2 = Some obj2 →
    (KObjectV.objectmeta obj1).(ObjectMetaV.UID') = (KObjectV.objectmeta obj2).(ObjectMetaV.UID') → k1 = k2);
  Hexisting_uid_is_used: (∀ k obj, abs_state !! k = Some obj → (KObjectV.objectmeta obj).(ObjectMetaV.UID') ∈ used_uid);
  Hchildren_point_to_parent: (∀ key_p obj_p key_c obj_c s,
    abs_state !! key_p = Some obj_p → abs_state !! key_c = Some obj_c → children !! key_p = Some s →
      (key_c ∈ s ↔ obj_has_controller_parent_of obj_c key_p.(KKey.Kind') key_p.(KKey.Name') (KObjectV.objectmeta obj_p).(ObjectMetaV.UID')));
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
    (abs_state: gmap KKey.t KObjectV.t) (children: gmap KKey.t (gset KKey.t)) (fresh_keys: gset KKey.t),
    "Hstate_m_addr" ∷ l ↦s[apimodel.State :: "m"] phys_state_l ∗
    "Hstate_used_uid_addr" ∷ l ↦s[apimodel.State :: "usedUID"] used_uid_l ∗
    "Hstate_rvc_addr" ∷ l ↦s[apimodel.State :: "resourceVersionCounter"] rvc ∗
    "Hown_phys" ∷ phys_state_l ↦$ phys_state ∗
    "Hown_used_uid" ∷ used_uid_l ↦$ used_uid ∗
    "Hown_abs" ∷ map_ctx γ.(γ_state) 1 abs_state ∗
    "Hown_children" ∷ map_ctx γ.(γ_children) 1 children ∗
    "Hown_fresh_keys" ∷ auth_set_auth γ.(γ_fresh_keys) fresh_keys ∗
    "Hphys_abs_rep" ∷ state_rep phys_state abs_state ∗
    "%Hghost_valid" ∷ ⌜ ghost_valid (dom used_uid) abs_state children fresh_keys ⌝.

Definition is_kubernetes γ l : iProp Σ :=
  ∃ (mu_l: loc),
    "Hmu" ∷ l ↦s[apimodel.State :: "mu"]□ mu_l ∗
    "Hkinv" ∷ is_Mutex mu_l (kubernetes_inv γ l).

(* The lemma turns the bi-implication form of Hchildren_point_to_parent to implications that are easier to apply. *)
Lemma split_children_point_to_parent (abs_state: gmap KKey.t KObjectV.t) (children: gmap KKey.t (gset KKey.t)):
  (∀ key_p obj_p key_c obj_c s,
    abs_state !! key_p = Some obj_p → abs_state !! key_c = Some obj_c → children !! key_p = Some s →
      (key_c ∈ s ↔ obj_has_controller_parent_of obj_c key_p.(KKey.Kind') key_p.(KKey.Name') (KObjectV.objectmeta obj_p).(ObjectMetaV.UID'))) →
  ((∀ key_p obj_p key_c obj_c s,
    abs_state !! key_p = Some obj_p → abs_state !! key_c = Some obj_c → children !! key_p = Some s →
      obj_has_controller_parent_of obj_c key_p.(KKey.Kind') key_p.(KKey.Name') (KObjectV.objectmeta obj_p).(ObjectMetaV.UID') → key_c ∈ s)) ∧
  ((∀ key_p obj_p key_c obj_c s,
    abs_state !! key_p = Some obj_p → abs_state !! key_c = Some obj_c → children !! key_p = Some s →
      key_c ∈ s → obj_has_controller_parent_of obj_c key_p.(KKey.Kind') key_p.(KKey.Name') (KObjectV.objectmeta obj_p).(ObjectMetaV.UID'))).
Proof.
  intros H.
  split.
  - intros key_p obj_p key_c obj_c s Hp Hc Hs Hparent.
    specialize (H key_p obj_p key_c obj_c s Hp Hc Hs).
    apply H. apply Hparent.
  - intros key_p obj_p key_c obj_c s Hp Hc Hs Hin.
    specialize (H key_p obj_p key_c obj_c s Hp Hc Hs).
    apply H. apply Hin.
Qed.

Lemma wp_deepCopy i pure_obj:
  {{{ is_pkg_init apimodel ∗
      KObjectV.deepown_i i pure_obj 1
  }}}
    @! apimodel.deepCopy #i
  {{{ i', RET #i';
      KObjectV.deepown_i i' pure_obj 1 ∗
      KObjectV.deepown_i i pure_obj 1
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

(* If pod has a huge body, this lemma can be used to name the pod body *)
Lemma rename_pod ptr (pod: v1.Pod.t):
  ptr ↦ pod -∗ ∃ pod', ptr ↦ pod' ∗ ⌜ pod' = pod ⌝.
Proof. iIntros. iExists pod. iFrame. done. Qed.


End proof.
