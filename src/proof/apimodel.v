From Perennial.algebra Require Export auth_map.
From New.proof.github_com.goose_lang.goose.model.channel Require Export auth_set.
Require Export New.proof.sync.

From proof.kubernetes_model Require Export apimodel_init.
From proof.k8s_io.apimachinery.pkg.api Require Export meta.
From proof.k8s_io.apimachinery.pkg.apis.meta Require Export v1.
From proof Require Import prelude empty_ffi.
From proof Require Export deepcopy well_formed.
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
  | Pod (p : v1.Pod.t)
  | ReplicaSet (rs : v1.ReplicaSet.t).
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

Definition extract_kobject_metadata kobj : v1.ObjectMeta.t :=
  match kobj with
  | KObject.Pod p => p.(v1.Pod.ObjectMeta')
  | KObject.ReplicaSet rs => rs.(v1.ReplicaSet.ObjectMeta')
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

Definition pod_rep k v1 v2 ptr pod : iProp Σ :=
  "%interface_is_pod_ptr" ∷ ⌜ v1 = interface.mk (ptrT.id v1.Pod.id) #ptr ⌝ ∗
  "pod_ptr" ∷ ptr ↦ pod ∗
  "%abs_v_is_pod" ∷ ⌜ v2 = KObject.Pod pod ⌝ ∗
  "#pod_nn_well_formed" ∷ pod_nn_well_formed pod (KKey.Namespace' k) (KKey.Name' k).

Definition replicaset_rep k v1 v2 ptr rs : iProp Σ :=
  "%interface_is_rs_ptr" ∷ ⌜ v1 = interface.mk (ptrT.id v1.ReplicaSet.id) #ptr ⌝ ∗
  "rs_ptr" ∷ ptr ↦ rs ∗
  "%abs_v_is_rs" ∷ ⌜ v2 = KObject.ReplicaSet rs ⌝ ∗
  "#replicaset_nn_well_formed" ∷ replicaset_nn_well_formed rs (KKey.Namespace' k) (KKey.Name' k).

Definition obj_rep k v1 v2 : iProp Σ :=
  (if bool_decide (KKey.Kind' k = "Pod"%go) then
    ∃ (ptr: loc) (pod: v1.Pod.t), pod_rep k v1 v2 ptr pod
  else if bool_decide (KKey.Kind' k = "ReplicaSet"%go) then
    ∃ (ptr: loc) (rs: v1.ReplicaSet.t), replicaset_rep k v1 v2 ptr rs
  else False)%I.

Definition state_rep (phys_state: gmap KKey.t interface.t) (abs_state: gmap KKey.t KObject.t) : iProp Σ :=
  [∗ map] k ↦ v1; v2 ∈ phys_state; abs_state, obj_rep k v1 v2.

Definition kubernetes_state_consistent (used_uid: gset go_string) (abs_state: gmap KKey.t KObject.t) (children: gmap KKey.t (gset KKey.t)) (fresh_keys: gset KKey.t) : iProp Σ :=
  (* All parents exist; this means holding a children gmap fragment implies the parent exists in abs_state *)
  "%parents_exist" ∷ ⌜ dom children = dom abs_state ⌝ ∗
  (* All children exist *)
  "%children_exist" ∷ ⌜ ∀ k s, children !! k = Some s → s ⊆ dom abs_state ⌝ ∗
  (* parents and children live in the same namespace *)
  "%parents_children_same_namespace" ∷ ⌜ ∀ k s child_key, children !! k = Some s → child_key ∈ s → k.(KKey.Namespace') = child_key.(KKey.Namespace') ⌝ ∗
  (* No one can be their own parent *)
  "%no_self_parenting" ∷ ⌜ ∀ k s child_key, children !! k = Some s → child_key ∈ s → child_key ≠ k ⌝ ∗
  (* Each children has only one parent -- the children gsets are disjoint *)
  "%children_disjoint" ∷ ⌜ ∀ k1 s1 k2 s2, k1 ≠ k2 → children !! k1 = Some s1 → children !! k2 = Some s2 → s1 ## s2 ⌝ ∗
  (* Fresh keys are not used by any existing object *)
  "%fresh_keys_absent" ∷ ⌜ fresh_keys ## dom abs_state ⌝ ∗
  (* Fresh keys are reserved *)
  "%fresh_keys_reserved" ∷ ⌜ ∀ k, k ∈ fresh_keys → reserved_key k ⌝ ∗
  (* Each object has a unique uid *)
  "%no_duplicate_uid" ∷ ⌜ ∀ k1 k2 obj1 obj2, abs_state !! k1 = Some obj1 → abs_state !! k2 = Some obj2 →
    (extract_kobject_metadata obj1).(v1.ObjectMeta.UID') = (extract_kobject_metadata obj2).(v1.ObjectMeta.UID') → k1 = k2 ⌝ ∗
  (* Any existing object's uid is in the set used_uid *)
  "%existing_uid_is_used" ∷ ⌜ ∀ k obj, abs_state !! k = Some obj → (extract_kobject_metadata obj).(v1.ObjectMeta.UID') ∈ used_uid ⌝ ∗
  (* All of the children have the controller owner reference pointing to the parent's uid *)
  "#children_point_to_parent" ∷ □ (∀ k s parent child_key child,
    ⌜ children !! k = Some s ∧ abs_state !! child_key = Some child ∧ abs_state !! k = Some parent ∧ child_key ∈ s⌝ -∗
      has_controller_parent_of (extract_kobject_metadata child).(v1.ObjectMeta.OwnerReferences') (extract_kobject_metadata parent).(v1.ObjectMeta.UID')
  ) ∗
  (* Only the children have the controller owner reference pointing to the parent's uid *)
  "#only_children_point_to_parent" ∷ □ (∀ k s parent child_key child,
    ⌜ children !! k = Some s ∧ abs_state !! child_key = Some child ∧ abs_state !! k = Some parent ⌝ ∗
    has_controller_parent_of (extract_kobject_metadata child).(v1.ObjectMeta.OwnerReferences') (extract_kobject_metadata parent).(v1.ObjectMeta.UID') -∗
      ⌜ child_key ∈ s ⌝
  ) ∗
  (* A parent must be some object that has existed; in other words, children cannot guess a parent's uid *)
  "#parent_uid_is_used" ∷ □ (∀ k obj uid, ⌜ abs_state !! k = Some obj ⌝ -∗
    has_controller_parent_of (extract_kobject_metadata obj).(v1.ObjectMeta.OwnerReferences') uid -∗
      ⌜ uid ∈ used_uid ⌝).

Definition is_kubernetes_state_inner γ_state γ_children γ_fresh_keys: iProp Σ :=
  ∃ (phys_state_l: loc) (used_uid_l: loc) (rvc: w64)
    (phys_state: gmap KKey.t interface.t) (used_uid: gmap go_string unit)
    (abs_state: gmap KKey.t KObject.t) (children: gmap KKey.t (gset KKey.t)) (fresh_keys: gset KKey.t),
    "state_m_addr" ∷ (global_addr apimodel.state) ↦s[ apimodel.State :: "m" ] phys_state_l ∗
    "state_used_uid_addr" ∷ (global_addr apimodel.state) ↦s[ apimodel.State :: "usedUID" ] used_uid_l ∗
    "state_rvc_addr" ∷ (global_addr apimodel.state) ↦s[ apimodel.State :: "resourceVersionCounter" ] rvc ∗
    "own_phys" ∷ phys_state_l ↦$ phys_state ∗
    "own_used_uid" ∷ used_uid_l ↦$ used_uid ∗
    "own_abs" ∷ map_ctx γ_state 1 abs_state ∗
    "phys_abs_rep" ∷ state_rep phys_state abs_state ∗
    "own_children" ∷ map_ctx γ_children 1 children ∗
    "own_fresh_keys" ∷ auth_set_auth γ_fresh_keys fresh_keys ∗
    "#consistent" ∷ kubernetes_state_consistent (dom used_uid) abs_state children fresh_keys.

Definition is_kubernetes_state γ_state γ_children γ_fresh_keys : iProp Σ :=
  is_Mutex (global_addr apimodel.stateMu) (is_kubernetes_state_inner γ_state γ_children γ_fresh_keys).

Lemma wp_deepCopy_pod (obj: interface.t) (ptr: loc) (pod: v1.Pod.t):
  {{{ is_pkg_init apimodel ∗
      "%interface_is_pod_ptr" ∷ ⌜ obj = interface.mk (ptrT.id v1.Pod.id) #ptr ⌝ ∗
      "pod_ptr" ∷ ptr ↦ pod
  }}}
    @! apimodel.deepCopy #obj
  {{{ (obj': interface.t) (ptr': loc) (pod': v1.Pod.t), RET #obj';
      ⌜ obj' = interface.mk (ptrT.id v1.Pod.id) #ptr' ⌝ ∗
      ptr' ↦ pod' ∗
      deepcopy_Pod pod pod' ∗
      ptr ↦ pod
  }}}.
Proof.
Admitted.

Lemma wp_deepCopy_replicaset (obj: interface.t) (ptr: loc) (rs: v1.ReplicaSet.t):
  {{{ is_pkg_init apimodel ∗
      "%interface_is_rs_ptr" ∷ ⌜ obj = interface.mk (ptrT.id v1.ReplicaSet.id) #ptr ⌝ ∗
      "rs_ptr" ∷ ptr ↦ rs
  }}}
    @! apimodel.deepCopy #obj
  {{{ (obj': interface.t) (ptr': loc) (rs': v1.ReplicaSet.t), RET #obj';
      ⌜ obj' = interface.mk (ptrT.id v1.ReplicaSet.id) #ptr' ⌝ ∗
      ptr' ↦ rs' ∗
      deepcopy_ReplicaSet rs rs' ∗
      ptr ↦ rs
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

Lemma wp_PodGet (namespace name: go_string) γ_state γ_children γ_fresh_keys:
  {{{ is_pkg_init apimodel ∗
      is_kubernetes_state γ_state γ_children γ_fresh_keys
  }}}
    @! apimodel.PodGet #namespace #name
  {{{ (l: loc) (err: error.t) dq2 (pod: v1.Pod.t), RET (#l, #err);
      if decide (err = interface.nil) then
        l ↦{dq2} pod
      else
        True
  }}}.
Proof.
Admitted.

Lemma wp_podControllerUIDIndex_with_controller_parent obj ptr pod:
  {{{ is_pkg_init apimodel ∗
      "%obj_is_ptr" ∷ ⌜ obj = interface.mk (ptrT.id v1.ReplicaSet.id) #ptr ⌝ ∗
      "ptr" ∷ ptr ↦ pod
  }}}
    @! apimodel.podControllerUIDIndex #obj
  {{{ indexed_values (err: error.t) indexed_value_list indexed_value, RET (#indexed_values, #err);
      ⌜ err = interface.nil ⌝ ∗
      indexed_values ↦* indexed_value_list ∗
      ⌜ indexed_value_list = [indexed_value] ⌝ ∗
      (
        has_controller_parent_of pod.(v1.Pod.ObjectMeta').(v1.ObjectMeta.OwnerReferences') indexed_value ∨
        (¬(∃ os o c, has_controller_parent pod.(v1.Pod.ObjectMeta').(v1.ObjectMeta.OwnerReferences') os o c) ∗ ⌜ indexed_value = "_ORPHAN_POD"%go ⌝)
      )
  }}}.
Proof.
Admitted.

Lemma wp_objList_pod_ptsto_mut kind namespace γ_state γ_children γ_fresh_keys owned_pod_map:
  {{{ is_pkg_init apimodel ∗
      "#inv" ∷ is_kubernetes_state γ_state γ_children γ_fresh_keys ∗
      "own_pods" ∷ ([∗ map] key ↦ pod ∈ owned_pod_map, key [[ γ_state ]]↦ KObject.Pod pod) ∗
      "%kind" ∷ ⌜ kind = "Pod"%go ⌝
  }}}
    @! apimodel.objList #kind #namespace
  {{{ (l: slice.t) (objs: list interface.t) (pods: list v1.Pod.t), RET #l;
      l ↦* objs ∗
      ⌜ NoDup (map extract_pod_key pods) ⌝ ∗
      ([∗ list] obj ; pod ∈ objs ; pods, ∃ (ptr : loc),
        ⌜ obj = interface.mk (ptrT.id v1.ReplicaSet.id) #ptr ⌝ ∗
        ptr ↦ pod ∗
        pod_well_formed pod ∗
        ⌜ namespace = ""%go ∨ pod.(v1.Pod.ObjectMeta').(v1.ObjectMeta.Namespace') = namespace ⌝
      ) ∗
      ([∗ map] key ↦ owned_pod ∈ owned_pod_map,
        if bool_decide (namespace = ""%go ∨ key.(KKey.Namespace') = namespace)
        then ∃ pod, ⌜ pod ∈ pods ⌝ ∗ deepcopy_Pod owned_pod pod
        else ∀ pod, ⌜ pod ∈ pods → key ≠ extract_pod_key pod ⌝
      ) ∗
      ([∗ map] key ↦ pod ∈ owned_pod_map, key [[ γ_state ]]↦ KObject.Pod pod)
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
      "%indexed_value" ∷ ⌜ indexed_value = (extract_kobject_metadata owned_parent).(v1.ObjectMeta.UID') ⌝ ∗
      "%kind" ∷ ⌜ kind = "Pod"%go ⌝ ∗
      "%index_name" ∷ ⌜ index_name = "podControllerUID"%go ⌝
  }}}
    @! apimodel.ByIndex #kind #index_name #indexed_value
  {{{ (l: slice.t) (err: error.t) (objs: list interface.t) (pods: list v1.Pod.t), RET (#l, #err);
      "l" ∷ l ↦* objs ∗
      "%err_is_nil" ∷ ⌜ err = interface.nil ⌝ ∗
      "%pods_nodup" ∷ ⌜ NoDup (map extract_pod_key pods) ⌝ ∗
      "obj_pts_to_pod" ∷ ([∗ list] obj ; pod ∈ objs ; pods, ∃ (ptr : loc),
        ⌜ obj = interface.mk (ptrT.id v1.Pod.id) #ptr ⌝ ∗
        ptr ↦ pod
      ) ∗
      "pods_well_formed" ∷ ([∗ list] pod ∈ pods,
        pod_well_formed pod ∗
        has_controller_parent_of pod.(v1.Pod.ObjectMeta').(v1.ObjectMeta.OwnerReferences') indexed_value
      ) ∗
      "pods_found_in_map" ∷ ([∗ list] pod ∈ pods, ∃ owned_pod,
        ⌜ owned_pod_map !! extract_pod_key pod = Some owned_pod ⌝ ∗ deepcopy_Pod owned_pod pod
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
  {{{ name, RET #name;
      ⌜ phys_state !! {| KKey.Kind' := kind; KKey.Namespace' := namespace; KKey.Name' := name;|} = None ⌝ ∗
      (* we assume that the generated key never conflicts with fresh_keys *)
      ⌜ ¬ reserved_key {| KKey.Kind' := kind; KKey.Namespace' := namespace; KKey.Name' := name;|} ⌝ ∗
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
  to_create_pod_ptr to_create_pod γ_state γ_children γ_fresh_keys parent_key owned_parent owned_child_keys:
  {{{ is_pkg_init apimodel ∗
      "#inv" ∷ is_kubernetes_state γ_state γ_children γ_fresh_keys ∗
      "own_parent" ∷ parent_key [[ γ_state ]]↦ owned_parent ∗
      "own_child_keys" ∷ parent_key [[ γ_children ]]↦ owned_child_keys ∗
      "%namespace_valid" ∷ ⌜ namespace = parent_key.(KKey.Namespace') ⌝ ∗
      "%kind" ∷ ⌜ kind = "Pod"%go ⌝ ∗
      "%interface_is_rs_ptr" ∷ ⌜ obj = interface.mk (ptrT.id v1.Pod.id) #to_create_pod_ptr ⌝ ∗
      "to_create_pod_ptr" ∷ to_create_pod_ptr ↦ to_create_pod ∗
      "#to_create_pod_is_child" ∷ has_controller_parent_of to_create_pod.(v1.Pod.ObjectMeta').(v1.ObjectMeta.OwnerReferences') (extract_kobject_metadata owned_parent).(v1.ObjectMeta.UID') ∗
      "#to_create_pod_well_formed" ∷ pod_to_create_well_formed to_create_pod ∗
      "%to_create_pod_namespace_valid" ∷ ⌜ to_create_pod.(v1.Pod.ObjectMeta').(v1.ObjectMeta.Namespace') = namespace ∨ to_create_pod.(v1.Pod.ObjectMeta').(v1.ObjectMeta.Namespace') = ""%go ⌝ ∗
      "%to_create_pod_name_valid" ∷ ⌜ to_create_pod.(v1.Pod.ObjectMeta').(v1.ObjectMeta.Name') = ""%go ⌝
  }}}
    @! apimodel.objCreate #kind #namespace #obj
  {{{ returned_obj (err: error.t) returned_pod_ptr returned_pod new_key created_pod owned_grandchild_keys, RET (#returned_obj, #err);
      ⌜ err = interface.nil ⌝ ∗
      ⌜ returned_obj = interface.mk (ptrT.id v1.Pod.id) #returned_pod_ptr ⌝ ∗
      returned_pod_ptr ↦ returned_pod ∗
      ⌜ new_key ∉ owned_child_keys ⌝ ∗
      new_key [[ γ_state ]]↦ (KObject.Pod created_pod) ∗
      parent_key [[ γ_state ]]↦ owned_parent ∗
      parent_key [[ γ_children ]]↦ (owned_child_keys ∪ {[new_key]}) ∗
      new_key [[ γ_children ]]↦ owned_grandchild_keys ∗
      deepcopy_Pod created_pod returned_pod
      (* TODO: specify that created_pod shares the same content with to_create_pod *)
  }}}.
Proof.
  wp_start as "H". iNamed "H".
  wp_apply wp_with_defer.
  iIntros (defer) "defer". simpl subst. wp_auto.
  wp_apply wp_globals_get.
  wp_apply wp_Mutex__Lock; [done|].
  iIntros "[own_Mutex H]". iNamed "H". wp_auto.
  wp_apply wp_globals_get.
  wp_apply (wp_deepCopy_pod with "[$to_create_pod_ptr]"); [done|].
  iIntros (copied_obj copied_ptr copied_pod) "(-> & copied_ptr & deepcopy_to_create_pod & to_create_pod_ptr)". wp_auto.
  wp_apply wp_Accessor; [done|].
  iIntros (o err) "(-> & ->)". wp_auto.
  assert ((bool_decide (interface.nil = interface.nil)) = true) as nil_is_nil.
  { rewrite bool_decide_true //. }
  rewrite nil_is_nil. wp_auto.
  iDestruct (struct_fields_split with "copied_ptr") as "H". iNamed "H".
  wp_bind.
  wp_apply (wp_SetNamespace with "[$HObjectMeta]").
  iIntros (meta') "(-> & HObjectMeta)". wp_auto.
  wp_apply (wp_GetName with "[$HObjectMeta]").
  iIntros (name) "(-> & HObjectMeta)". wp_auto.
  wp_apply (wp_GetGenerateName with "[$HObjectMeta]").
  iIntros (generate_name) "(-> & HObjectMeta)". wp_auto.
  iAssert (⌜ v1.ObjectMeta.Name' (v1.Pod.ObjectMeta' copied_pod) = ""%go ⌝%I) as "->".
  {
    iDestruct "deepcopy_to_create_pod" as "(_ & deepcopy_ObjectMeta & _ & _)".
    iDestruct "deepcopy_ObjectMeta" as "(%deepcopy_ObjectMeta_pure & _ )".
    iPureIntro. rewrite to_create_pod_name_valid in deepcopy_ObjectMeta_pure. intuition.
  }
  iAssert (⌜ v1.ObjectMeta.GenerateName' (v1.Pod.ObjectMeta' copied_pod) = v1.ObjectMeta.GenerateName' (v1.Pod.ObjectMeta' to_create_pod) ⌝%I) as "%generate_name_eq".
  {
    iDestruct "deepcopy_to_create_pod" as "(_ & deepcopy_ObjectMeta & _ & _)".
    iDestruct "deepcopy_ObjectMeta" as "(%deepcopy_ObjectMeta_pure & _ )".
    iPureIntro. intuition.
  }
  iAssert (⌜ v1.ObjectMeta.GenerateName' (v1.Pod.ObjectMeta' copied_pod) ≠ ""%go ⌝%I) as "%generate_name_not_empty".
  {
    iDestruct "to_create_pod_well_formed" as "(pod_metadata_to_create_well_formed & _ & _)".
    iDestruct "pod_metadata_to_create_well_formed" as "%generate_name_and_name".
    iPureIntro. rewrite generate_name_eq. apply generate_name_and_name. done.
  }
  wp_auto. wp_if_destruct; [done|].
  rewrite bool_decide_false //. wp_auto.
  wp_apply wp_globals_get. wp_apply (wp_generateNewName with "[$own_phys]").
  iIntros (name) "(%new_key_not_in_phys & %new_key_not_reserved & own_phys)". wp_auto.
  wp_apply (wp_SetName with "[$HObjectMeta]").
  iIntros (meta') "(-> & HObjectMeta)". wp_auto.
  wp_apply wp_globals_get.
  wp_apply (wp_map_get with "[$own_phys]"). iIntros "own_phys". wp_auto.
  rewrite /is_Some new_key_not_in_phys. wp_auto.
  wp_apply wp_globals_get.
  wp_apply (wp_generateNewUID with "[$own_used_uid]").
  iIntros (generated_uid) "(%generated_uid_is_not_used & own_used_uid)". wp_auto.
  wp_apply (wp_SetUID with "[$HObjectMeta]").
  iIntros (meta') "(-> & HObjectMeta)". wp_auto.
  wp_apply wp_globals_get.
  wp_apply (wp_map_insert with "[$own_used_uid]").
  iIntros "own_used_uid". wp_auto.
  wp_apply wp_globals_get. wp_apply wp_globals_get. wp_apply wp_globals_get.
  wp_apply wp_strconv_FormatInt. iIntros (rv_str) "_". wp_auto.
  wp_apply (wp_SetResourceVersion with "[$HObjectMeta]").
  iIntros (meta') "(-> & HObjectMeta)". wp_auto.
  wp_apply wp_globals_get.
  wp_apply (wp_map_insert with "[$own_phys]").
  iIntros "own_phys". wp_auto.
  iDestruct (struct_fields_combine (v:=v1.Pod.mk _ _ _ _)
    with "[$HTypeMeta $HObjectMeta $HSpec $HStatus]") as "copied_ptr". simpl.
  iDestruct (rename_pod with "copied_ptr") as "(%created_pod & copied_ptr & %created_pod_eq)".
  wp_apply (wp_deepCopy_pod with "[$copied_ptr]"); [done|].
  iIntros (returned_obj returned_ptr returned_pod) "(-> & returned_ptr & deepcopy_created_pod & copied_ptr)". wp_auto.
  set new_key := {| KKey.Kind' := "Pod"; KKey.Name' := name; KKey.Namespace' := KKey.Namespace' parent_key |}.
  fold new_key in new_key_not_in_phys.
  fold new_key in new_key_not_reserved.
  iAssert (⌜ abs_state !! new_key = None ⌝%I) with "[phys_abs_rep]" as "%new_key_not_in_abs".
  { iDestruct (big_sepM2_dom with "phys_abs_rep") as %dom_eq. iPureIntro. apply not_elem_of_dom. apply not_elem_of_dom in new_key_not_in_phys. set_solver. }
  iAssert (⌜ children !! new_key = None ⌝%I) with "[consistent]" as "%new_key_not_in_children".
  { iNamed "consistent". iPureIntro. apply not_elem_of_dom. apply not_elem_of_dom in new_key_not_in_abs. set_solver. }
  iAssert (⌜ abs_state !! parent_key = Some (owned_parent) ⌝%I) with "[own_parent own_abs]" as "%parent_key_in_abs".
  { iDestruct (map_valid with "own_abs own_parent") as %Hlookup. iPureIntro; exact Hlookup. }
  iAssert (⌜ children !! parent_key = Some (owned_child_keys) ⌝%I) with "[own_child_keys own_children]" as "%parent_key_in_children".
  { iDestruct (map_valid with "own_children own_child_keys") as %Hlookup. iPureIntro; exact Hlookup. }
  assert (new_key ≠ parent_key) as new_key_neq_parent_key.
  { intros Heq. congruence. }
  iAssert (⌜ <[parent_key:=owned_child_keys ∪ {[new_key]}]> children !! new_key = None ⌝%I) with "[consistent]" as "%new_key_not_in_children_after_update".
  { iNamed "consistent". iPureIntro. apply not_elem_of_dom. apply not_elem_of_dom in new_key_not_in_abs. set_solver. }
  iAssert (⌜ new_key ∉ owned_child_keys ⌝ %I) as "%new_key_not_in_owned_child_keys".
  { iNamed "consistent". iPureIntro.
    assert (owned_child_keys ⊆ dom abs_state) as owned_in_abs.
    { apply children_exist with (k := parent_key). exact parent_key_in_children. }
    apply not_elem_of_dom in new_key_not_in_abs.
    set_solver.
  }
  iMod (map_alloc new_key (KObject.Pod created_pod) with "[$own_abs]") as "[own_abs own_pod]"; [eauto|].
  iMod (auth_map.map_update _ _ (owned_child_keys ∪ {[new_key]}) with "own_children own_child_keys")
    as "[own_children own_child_keys]".
  iMod (map_alloc new_key ∅ with "[$own_children]") as "[own_children own_grandchild_keys]"; [eauto|].
  set phys_state' := <[new_key:=interface.mk (ptrT.id v1.Pod.id) (# copied_ptr)]> phys_state.
  set used_uid' := <[generated_uid:=()]> used_uid.
  set abs_state' := <[new_key:=KObject.Pod created_pod]> abs_state.
  set children' := (<[new_key:=∅]> (<[parent_key:=owned_child_keys ∪ {[new_key]}]> children)).
  iAssert (pod_nn_well_formed created_pod new_key.(KKey.Namespace') new_key.(KKey.Name') %I)
  with "[to_create_pod_well_formed]" as "created_pod_nn_well_formed".
  { admit. }
  iAssert (state_rep phys_state' abs_state' %I)
  with "[copied_ptr phys_abs_rep]" as "phys_abs_rep".
  {
    unfold state_rep. unfold phys_state'. unfold abs_state'.
    rewrite (big_sepM2_insert _ phys_state abs_state new_key _ _ new_key_not_in_phys new_key_not_in_abs).
    iSplitL "copied_ptr".
    {
      unfold obj_rep.
      assert (bool_decide (KKey.Kind' new_key = "Pod"%go) = true) as kind_is_pod.
      { apply bool_decide_true. unfold new_key. simpl. reflexivity. }
      rewrite kind_is_pod.
      iExists copied_ptr, created_pod.
      unfold pod_rep. iFrame "#". iFrame. iPureIntro. done.
    }
    { done. }
  }
  iAssert (has_controller_parent_of created_pod.(v1.Pod.ObjectMeta').(v1.ObjectMeta.OwnerReferences') (extract_kobject_metadata owned_parent).(v1.ObjectMeta.UID') %I)
  with "[deepcopy_to_create_pod]" as "#created_pod_is_child".
  { admit. }
  iAssert (kubernetes_state_consistent (dom used_uid') abs_state' children' fresh_keys %I)
  as "consistent'".
  {
    iNamed "consistent".
    assert (dom children' = dom children ∪ {[new_key]}) as children_dom_simpl.
    {
      unfold children'.
      rewrite !dom_insert_L.
      assert (parent_key ∈ dom children) as parent_in_dom.
      { apply elem_of_dom. exists owned_child_keys. exact parent_key_in_children. }
      assert ({[parent_key]} ∪ dom children = dom children) as parent_union_eq.
      { set_solver. }
      rewrite parent_union_eq.
      set_solver.
    }
    assert (created_pod.(v1.Pod.ObjectMeta').(v1.ObjectMeta.UID') = generated_uid) as created_uid_eq.
    { rewrite created_pod_eq. done. }
    assert (generated_uid ∉ dom used_uid) as generated_not_in_used.
    { apply not_elem_of_dom. exact generated_uid_is_not_used. }
    iDestruct "created_pod_nn_well_formed" as "(_ & _ & created_pod_well_formed)".
    iDestruct "created_pod_well_formed" as "(created_pod_metadata_wf & _)".
    iDestruct "created_pod_metadata_wf" as "(_ & #at_most_one_controller_parent)".
    iSplitR; [|iSplitR; [|iSplitR; [|iSplitR; [|iSplitR; [|iSplitR; [|iSplitR; [|iSplitR; [|iSplitR; [|iSplitR; [|iSplitR ]]]]]]]]]].
    { iPureIntro. unfold abs_state'. unfold children'. rewrite children_dom_simpl. rewrite dom_insert_L. set_solver. }
    { iPureIntro.
      intros k s Hlookup.
      unfold children' in Hlookup. unfold abs_state'.
      rewrite lookup_insert_Some in Hlookup.
      destruct Hlookup as [(Hk_eq & Hs_eq) | (Hk_neq & Hlookup)].
      - subst k s. rewrite dom_insert_L. set_solver.
      - rewrite lookup_insert_Some in Hlookup.
        destruct Hlookup as [(Hk_eq_parent & Hs_eq) | (Hk_neq_parent & Hlookup)].
        + subst k s. rewrite dom_insert_L.
          assert (owned_child_keys ⊆ dom abs_state) as children_in_abs.
          { apply children_exist with (k := parent_key). exact parent_key_in_children. }
          set_solver.
        + rewrite dom_insert_L.
          assert (s ⊆ dom abs_state) as s_in_abs.
          { apply children_exist with (k := k). exact Hlookup. }
          set_solver.
    }
    { iPureIntro.
      intros k s child_key Hlookup Hchild_in_s.
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
          * apply parents_children_same_namespace with (k := parent_key) (s := owned_child_keys); assumption.
          * subst child_key. unfold new_key. simpl. reflexivity.
        + apply parents_children_same_namespace with (k := k) (s := s); assumption.
    }
    { iPureIntro.
      intros k s child_key Hlookup Hchild_in_s.
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
          * apply no_self_parenting with (k := parent_key) (s := owned_child_keys); assumption.
          * subst child_key. assumption.
        + apply no_self_parenting with (k := k) (s := s); assumption.
    }
    { iPureIntro.
      intros k1 s1 k2 s2 Hk1_neq_k2 Hlookup1 Hlookup2.
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
          { apply children_exist with (k := k2). exact Hlookup2. }
          assert (owned_child_keys ## s2) as disj.
          { apply children_disjoint with (k1 := parent_key) (k2 := k2); [|exact parent_key_in_children|exact Hlookup2].
            intros Heq. subst. contradiction. }
          assert (new_key ∉ dom abs_state) as key_not_in_abs.
          { apply not_elem_of_dom. exact new_key_not_in_abs. }
          clear -disj s2_in_abs key_not_in_abs.
          set_solver.
        + subst k2 s2.
          assert (s1 ⊆ dom abs_state) as s1_in_abs.
          { apply children_exist with (k := k1). exact Hlookup1. }
          assert (s1 ## owned_child_keys) as disj.
          { apply children_disjoint with (k1 := k1) (k2 := parent_key); [|exact Hlookup1|exact parent_key_in_children].
            intros Heq. subst. contradiction. }
          assert (new_key ∉ dom abs_state) as key_not_in_abs.
          { apply not_elem_of_dom. exact new_key_not_in_abs. }
          clear -disj s1_in_abs key_not_in_abs.
          set_solver.
        + apply children_disjoint with (k1 := k1) (k2 := k2); assumption.
    }
    { iPureIntro. unfold abs_state'. rewrite dom_insert_L.
      assert (new_key ∉ fresh_keys) as key_not_in_fresh.
      { intros Hin. apply fresh_keys_reserved in Hin. contradiction. }
      clear -fresh_keys_absent key_not_in_fresh.
      set_solver.
    }
    { iPureIntro. apply fresh_keys_reserved. }
    { iPureIntro.
      intros k1 k2 obj1 obj2 Hlookup1 Hlookup2 Huid_eq.
      unfold abs_state' in Hlookup1, Hlookup2.
      rewrite lookup_insert_Some in Hlookup1.
      rewrite lookup_insert_Some in Hlookup2.
      destruct Hlookup1 as [(Hk1_eq & Hobj1_eq) | (Hk1_neq & Hlookup1)];
      destruct Hlookup2 as [(Hk2_eq & Hobj2_eq) | (Hk2_neq & Hlookup2)].
      - subst. reflexivity.
      - subst k1 obj1.
        exfalso.
        assert ((extract_kobject_metadata obj2).(v1.ObjectMeta.UID') ∈ dom used_uid) as obj2_uid_in_used.
        { apply existing_uid_is_used with (k := k2). exact Hlookup2. }
        rewrite created_uid_eq in Huid_eq.
        rewrite <- Huid_eq in obj2_uid_in_used.
        contradiction.
      - subst k2 obj2.
        exfalso.
        assert ((extract_kobject_metadata obj1).(v1.ObjectMeta.UID') ∈ dom used_uid) as obj1_uid_in_used.
        { apply existing_uid_is_used with (k := k1). exact Hlookup1. }
        rewrite created_uid_eq in Huid_eq.
        rewrite Huid_eq in obj1_uid_in_used.
        contradiction.
      - apply no_duplicate_uid with (obj1 := obj1) (obj2 := obj2); assumption.
    }
    { iPureIntro. intros k obj Hlookup_abs_state. unfold abs_state', used_uid'.
      rewrite dom_insert_L. rewrite lookup_insert_Some in Hlookup_abs_state.
      destruct Hlookup_abs_state as [(Hk_eq & Hs_eq) | (Hk_neq & Hlookup_abs_state)].
      - subst k obj. set_solver.
      - set_solver.
    }
    { iIntros (k s parent child_key child) "%H".
      destruct H as (Hlookup_children & Hlookup_child & Hlookup_parent & Hchild_in_s).
      unfold children' in Hlookup_children. unfold abs_state' in Hlookup_child, Hlookup_parent.
      rewrite lookup_insert_Some in Hlookup_children.
      destruct Hlookup_children as [(Hk_eq & Hs_eq) | (Hk_neq & Hlookup_children)].
      - subst k s. set_solver.
      - rewrite lookup_insert_Some in Hlookup_children.
        destruct Hlookup_children as [(Hk_eq_parent & Hs_eq) | (Hk_neq_parent & Hlookup_children)].
        + subst k s.
          assert (child_key ∈ owned_child_keys ∨ child_key = new_key) as Hchild_cases.
          { set_solver. }
          destruct Hchild_cases as [Hchild_in_owned | Hchild_eq_new].
          * rewrite lookup_insert_Some in Hlookup_child.
            rewrite lookup_insert_Some in Hlookup_parent.
            destruct Hlookup_child as [(Hchild_eq & Hchild_obj_eq) | (Hchild_neq & Hlookup_child)].
            { subst child_key.
              assert (new_key ∈ owned_child_keys) as contra.
              { exact Hchild_in_owned. }
              assert (owned_child_keys ⊆ dom abs_state) as owned_in_abs.
              { apply children_exist with (k := parent_key). exact parent_key_in_children. }
              apply not_elem_of_dom in new_key_not_in_abs.
              set_solver. }
            { destruct Hlookup_parent as [(Hparent_eq & Hparent_obj_eq) | (Hparent_neq & Hlookup_parent)].
              { apply not_elem_of_dom in new_key_not_in_abs.
                assert (parent_key ∈ dom abs_state) as contra.
                { apply elem_of_dom. exists owned_parent. exact parent_key_in_abs. }
                congruence. }
              { iModIntro.
                iApply "children_point_to_parent". iPureIntro.
                split; [exact parent_key_in_children|].
                split; [exact Hlookup_child|].
                split; [exact Hlookup_parent|].
                exact Hchild_in_owned. } }
          * subst child_key.
            rewrite lookup_insert_Some in Hlookup_child.
            rewrite lookup_insert_Some in Hlookup_parent.
            destruct Hlookup_child as [(Hchild_eq & Hchild_obj_eq) | (Hchild_neq & Hlookup_child)].
            { subst child.
              destruct Hlookup_parent as [(Hparent_eq & Hparent_obj_eq) | (Hparent_neq & Hlookup_parent)].
              { exfalso. apply new_key_neq_parent_key. exact Hparent_eq. }
              { assert (parent = owned_parent) as ->.
                { rewrite parent_key_in_abs in Hlookup_parent. injection Hlookup_parent as ->. reflexivity. }
                iApply "created_pod_is_child". } }
            { congruence. }
        + rewrite lookup_insert_Some in Hlookup_child.
          rewrite lookup_insert_Some in Hlookup_parent.
          destruct Hlookup_child as [(Hchild_eq & Hchild_obj_eq) | (Hchild_neq & Hlookup_child)].
          * subst child_key child.
            destruct Hlookup_parent as [(Hparent_eq & Hparent_obj_eq) | (Hparent_neq & Hlookup_parent)].
            { subst k.
              apply not_elem_of_dom in new_key_not_in_children.
              assert (new_key ∈ dom children) as contra.
              { apply elem_of_dom. exists s. exact Hlookup_children. }
              contradiction. }
            { assert (new_key ∈ s) as new_key_in_s.
              { exact Hchild_in_s. }
              assert (s ⊆ dom abs_state) as s_in_abs.
              { apply children_exist with (k := k). exact Hlookup_children. }
              apply not_elem_of_dom in new_key_not_in_abs.
              set_solver. }
          * destruct Hlookup_parent as [(Hparent_eq & Hparent_obj_eq) | (Hparent_neq & Hlookup_parent)].
            { subst k.
              apply not_elem_of_dom in new_key_not_in_children.
              assert (new_key ∈ dom children) as contra.
              { apply elem_of_dom. exists s. exact Hlookup_children. }
              contradiction. }
            { iModIntro.
              iApply "children_point_to_parent". iPureIntro.
              split; [exact Hlookup_children|].
              split; [exact Hlookup_child|].
              split; [exact Hlookup_parent|].
              exact Hchild_in_s. }
    }
    {
      iModIntro.
      iIntros (k s parent child_key child) "[%H #HparentRef]".
      destruct H as (Hlookup_children & Hlookup_child & Hlookup_parent).
      unfold children' in Hlookup_children. unfold abs_state' in Hlookup_child, Hlookup_parent.
      rewrite lookup_insert_Some in Hlookup_children.
      destruct Hlookup_children as [(Hk_eq & Hs_eq) | (Hk_neq & Hlookup_children)].
      - subst k s.
        rewrite lookup_insert_Some in Hlookup_parent.
        destruct Hlookup_parent as [(Hparent_eq & Hparent_obj_eq) | (Hparent_neq & Hlookup_parent)]; [|congruence].
        subst parent.
        rewrite lookup_insert_Some in Hlookup_child.
        destruct Hlookup_child as [(Hchild_eq & Hchild_obj_eq) | (Hchild_neq & Hlookup_child)].
        + subst child_key child.
          simpl.
          iAssert (⌜(extract_kobject_metadata owned_parent).(v1.ObjectMeta.UID') = created_pod.(v1.Pod.ObjectMeta').(v1.ObjectMeta.UID')⌝%I) as "%uid_eq".
          {
            iDestruct ("at_most_one_controller_parent" $!
              (extract_kobject_metadata owned_parent).(v1.ObjectMeta.UID')
              created_pod.(v1.Pod.ObjectMeta').(v1.ObjectMeta.UID')
              with "created_pod_is_child HparentRef") as "%uid_eq".
            done.
          }
          iAssert (⌜(extract_kobject_metadata owned_parent).(v1.ObjectMeta.UID') ≠ created_pod.(v1.Pod.ObjectMeta').(v1.ObjectMeta.UID')⌝%I) as "%uid_neq".
          {
            iPureIntro.
            intros Heq.
            assert ((extract_kobject_metadata owned_parent).(v1.ObjectMeta.UID') ∈ dom used_uid) as parent_uid_in_used.
            { apply existing_uid_is_used with (k := parent_key). exact parent_key_in_abs. }
            rewrite created_uid_eq in Heq.
            rewrite Heq in parent_uid_in_used.
            contradiction.
          }
          congruence.
        + iAssert (⌜ created_pod.(v1.Pod.ObjectMeta').(v1.ObjectMeta.UID') ∈ dom used_uid ⌝%I) as "%created_pod_uid_is_used".
          { iApply ("parent_uid_is_used" $! child_key child); [done|done]. }
          iAssert (⌜ created_pod.(v1.Pod.ObjectMeta').(v1.ObjectMeta.UID') ∉ dom used_uid ⌝%I) as "%created_pod_uid_is_not_used".
          { rewrite created_uid_eq. iPureIntro. apply not_elem_of_dom. done. }
          done.
      - rewrite lookup_insert_Some in Hlookup_children.
        destruct Hlookup_children as [(Hk_eq & Hs_eq) | (Hk_neq' & Hlookup_children)].
        + subst k s.
          rewrite lookup_insert_Some in Hlookup_parent.
          destruct Hlookup_parent as [(Hparent_eq & Hparent_obj_eq) | (Hparent_neq & Hlookup_parent)]; [congruence|].
          rewrite lookup_insert_Some in Hlookup_child.
          destruct Hlookup_child as [(Hchild_eq & Hchild_obj_eq) | (Hchild_neq & Hlookup_child)].
          * subst child_key. iPureIntro. set_solver.
          * iAssert (⌜ child_key ∈ owned_child_keys ⌝%I) as "%child_key_in_owned_child_keys".
            {
              iApply ("only_children_point_to_parent" $! parent_key owned_child_keys parent child_key child).
              iFrame "#".
              done.
            }
            iPureIntro. set_solver.
        + rewrite lookup_insert_Some in Hlookup_parent.
          destruct Hlookup_parent as [(Hparent_eq & Hparent_obj_eq) | (Hparent_neq & Hlookup_parent)]; [congruence|].
          rewrite lookup_insert_Some in Hlookup_child.
          destruct Hlookup_child as [(Hchild_eq & Hchild_obj_eq) | (Hchild_neq & Hlookup_child)].
          * subst child_key child.
            iAssert (⌜ parent_key = k ⌝%I) as "%k_eq".
            {
              iDestruct ("at_most_one_controller_parent" $!
                (extract_kobject_metadata owned_parent).(v1.ObjectMeta.UID')
                (extract_kobject_metadata parent).(v1.ObjectMeta.UID')
                with "created_pod_is_child HparentRef") as "%uid_eq".
              iPureIntro.
              eapply no_duplicate_uid; [done|done|done].
            }
            done.
          * iApply ("only_children_point_to_parent" $! k s parent child_key child).
            iFrame "#".
            done.
    }
    {
      iModIntro.
      iIntros (k obj uid) "%Hlookup_obj #HparentRef".
      unfold abs_state', used_uid' in Hlookup_obj.
      rewrite lookup_insert_Some in Hlookup_obj.
      destruct Hlookup_obj as [(Hk_eq & Hobj_eq) | (Hk_neq & Hlookup_obj)].
      - subst k obj.
        iDestruct ("at_most_one_controller_parent" $! uid (extract_kobject_metadata owned_parent).(v1.ObjectMeta.UID')
          with "HparentRef created_pod_is_child") as "%uid_eq".
        iPureIntro.
        rewrite dom_insert_L.
        assert ((extract_kobject_metadata owned_parent).(v1.ObjectMeta.UID') ∈ dom used_uid) as parent_uid_in_used.
        { apply existing_uid_is_used with (k := parent_key). exact parent_key_in_abs. }
        rewrite uid_eq. set_solver.
      - iDestruct ("parent_uid_is_used" $! k obj uid with "[] HparentRef") as "%uid_in_used".
        { done. }
        iPureIntro. rewrite dom_insert_L. set_solver.
    }
  }
  wp_bind.
  wp_apply (wp_Mutex__Unlock _ (is_kubernetes_state_inner γ_state γ_children γ_fresh_keys)
    with "[$own_Mutex $state_m_addr $state_used_uid_addr $state_rvc_addr $own_phys $own_used_uid $own_abs $phys_abs_rep $own_children $own_fresh_keys]").
  { iFrame "#". }
  iApply "HΦ". iFrame "returned_ptr". iFrame. iFrame "#". done.
Admitted.

Lemma wp_PodCreate_without_name_ptsto_mut namespace to_create_pod_ptr to_create_pod
  γ_state γ_children γ_fresh_keys parent_key owned_parent owned_child_keys:
  {{{ is_pkg_init apimodel ∗
      "#inv" ∷ is_kubernetes_state γ_state γ_children γ_fresh_keys ∗
      "own_parent" ∷ parent_key [[ γ_state ]]↦ owned_parent ∗
      "own_child_keys" ∷ parent_key [[ γ_children ]]↦ owned_child_keys ∗
      "%namespace_valid" ∷ ⌜ namespace = parent_key.(KKey.Namespace') ⌝ ∗
      "to_create_pod_ptr" ∷ to_create_pod_ptr ↦ to_create_pod ∗
      "parent_uid" ∷ has_controller_parent_of to_create_pod.(v1.Pod.ObjectMeta').(v1.ObjectMeta.OwnerReferences') (extract_kobject_metadata owned_parent).(v1.ObjectMeta.UID') ∗
      "well_formed_for_creation" ∷ pod_to_create_nn_well_formed to_create_pod namespace ""%go
  }}}
    @! apimodel.PodCreate #namespace #to_create_pod_ptr
  {{{ created_pod_ptr (err: error.t) created_pod new_key, RET (#created_pod_ptr, #err);
      ⌜ err = interface.nil ⌝ ∗
      created_pod_ptr ↦ created_pod ∗
      pod_well_formed created_pod ∗
      ⌜ new_key = extract_pod_key created_pod ⌝ ∗
      ⌜ new_key ∉ owned_child_keys ⌝ ∗
      new_key [[ γ_state ]]↦ (KObject.Pod created_pod) ∗
      parent_key [[ γ_state ]]↦ owned_parent ∗
      parent_key [[ γ_children ]]↦ (owned_child_keys ∪ {[new_key]})
      (* TODO: specify that created_pod shares some contents with to_create_pod *)
  }}}.
Proof.
  wp_start as "H". iNamed "H".
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
      with "[pod_ptr other_rep pod_nn_well_formed]" as "phys_abs_rep".
      {
        assert (delete key abs_state = delete key (<[key:=KObject.Pod updated_pod]> abs_state)) as ->.
        { rewrite delete_insert_eq. reflexivity. }
        iAssert (pod_nn_well_formed updated_pod (KKey.Namespace' key) (KKey.Name' key)%I)
        with "[pod_nn_well_formed]" as "pod_nn_well_formed".
        {
          iNamed "pod_nn_well_formed".
          unfold pod_nn_well_formed. unfold pod_well_formed. unfold object_meta_well_formed.
          subst updated_pod. simpl. iFrame. done.
        }
        iAssert (obj_rep key (interface.mk (ptrT.id v1.Pod.id) (# ptr)) (KObject.Pod updated_pod)%I)
        with "[pod_ptr pod_nn_well_formed]" as "k_rep".
        { unfold obj_rep. rewrite kind_is_pod. iExists ptr, updated_pod. iFrame. done. }
        assert ((<[key:=KObject.Pod updated_pod]> abs_state) !! key = Some (KObject.Pod updated_pod)) as key_in_new_abs.
        { rewrite lookup_insert. destruct (decide (key = key)) as [|Hcontra]; [reflexivity | contradiction]. }
        iApply (big_sepM2_split_singleton _ key _ (KObject.Pod updated_pod) phys_state (<[key:=KObject.Pod updated_pod]> abs_state)
          key_in_phys key_in_new_abs with "[k_rep other_rep]").
        iFrame.
      }
      iAssert (kubernetes_state_consistent (<[key:=KObject.Pod updated_pod]> abs_state) children fresh_keys %I)
      with "[consistent]"  as "consistent".
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
        iSplitR; [|iSplitR; [|iSplitR; [|iSplitR; [|iSplitR; [|iSplitR; [|iSplitR; [|iSplitL "children_point_to_parent"]]]]]]].
        { iPureIntro. set_solver. }
        { iPureIntro. intros k s Hlookup. specialize (children_exist k s Hlookup). rewrite dom_insert_L. set_solver. }
        { iPureIntro. apply parents_children_same_namespace. }
        { iPureIntro. apply no_self_parenting. }
        { iPureIntro. apply children_disjoint. }
        { iPureIntro. rewrite dom_insert_L. set_solver. }
        { iPureIntro. apply fresh_keys_reserved. }
        {
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
      wp_apply (wp_Mutex__Unlock _ (is_kubernetes_state_inner γ_state γ_children γ_fresh_keys)
      with "[$own_Mutex state_m_addr state_uc_addr state_rvc_addr own_phys own_abs phys_abs_rep own_children own_fresh_keys consistent]").
      { iFrame. done. }
      iApply "HΦ". iFrame. iSplitR; [done|]. iLeft. iFrame.
      iAssert (⌜ now_ptr ≠ null ⌝%I) with "[now]" as "%now_ptr_not_null".
      { by iDestruct (typed_pointsto_not_null with "now") as %?. }
      iPureIntro. subst updated_pod. done.
    + iDestruct (struct_fields_combine (V:=v1.Pod.t) with "[$HTypeMeta $HObjectMeta $HSpec $HStatus]") as "pod_ptr".
      iAssert (state_rep phys_state abs_state %I) with "[pod_ptr other_rep pod_nn_well_formed]" as "phys_abs_rep".
      {
        iApply big_sepM2_split_singleton; [done | done|]. iFrame. unfold obj_rep. rewrite kind_is_pod.
        iExists ptr, owned_pod. iFrame. done.
      }
      wp_apply (wp_Mutex__Unlock _ (is_kubernetes_state_inner γ_state γ_children γ_fresh_keys)
        with "[$own_Mutex state_m_addr state_uc_addr state_rvc_addr own_phys own_abs phys_abs_rep own_children own_fresh_keys consistent]").
      { iFrame. done. }
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
    iAssert (kubernetes_state_consistent (delete key abs_state) (delete key (<[parent_key:=owned_child_keys ∖ {[key]}]> children)) fresh_keys %I)
    with "[consistent]"  as "consistent".
    {
      iNamed "consistent".
      assert (parent_key ≠ key) as parent_neq_key.
      { specialize (no_self_parenting parent_key owned_child_keys key parent_key_in_children pod_is_child). done. }
      assert (dom (delete key (<[parent_key:=owned_child_keys ∖ {[key]}]> children)) = dom (delete key children) )
      as children_dom_simpl.
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
      iSplitR; [|iSplitR; [|iSplitR; [|iSplitR; [|iSplitR; [|iSplitR; [|iSplitR; [|iSplitL "children_point_to_parent"]]]]]]].
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
    wp_apply (wp_Mutex__Unlock _ (is_kubernetes_state_inner γ_state γ_children γ_fresh_keys)
      with "[$own_Mutex state_m_addr state_uc_addr state_rvc_addr own_phys own_abs phys_abs_rep own_children own_fresh_keys consistent]").
    { iFrame. done. }
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
      replicaset_nn_well_formed rs (KKey.Namespace' key) (KKey.Name' key) ∗
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
  with "[$rs'_is_deepcopy_rs] [$replicaset_nn_well_formed]") as "(rs'_is_deepcopy_rs & replicaset_nn_well_formed & rs'_nn_well_formed)".
  wp_auto.
  iAssert (state_rep phys_state abs_state %I) with "[rs_ptr other_rep replicaset_nn_well_formed]" as "phys_abs_rep".
  { iApply "other_rep". iExists ptr, owned_rs. iFrame. done. }
  wp_apply (wp_Mutex__Unlock _ (is_kubernetes_state_inner γ_state γ_children γ_fresh_keys)
  with "[$own_Mutex state_m_addr state_uc_addr state_rvc_addr own_phys own_abs phys_abs_rep own_children own_fresh_keys consistent]").
  { iFrame. done. }
  iApply ("HΦ" $! obj' true).
  iSplitR.
  { iPureIntro. done. }
  iFrame.
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
      replicaset_nn_well_formed rs namespace name
  }}}.
Proof.
  wp_start as "H". iNamed "H". wp_auto.
  wp_apply (wp_objGet_replicaset_ptsto_mut with "[$own_rs]").
  { iFrame "#". done. }
  iIntros (obj exists' rs') "(%exists'_is_true & (%ptr & %obj_is_ptr & ptr) & deepcopy & well_formed & own_rs)".
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
  iFrame. iPureIntro. done.
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
      replicaset_nn_well_formed rs namespace name
  }}}.
Proof.
  wp_start as "H". iNamed "H". wp_auto.
  wp_apply (wp_ReplicaSetMutGet_ptsto_mut with "[$own_rs]").
  { done. }
  iIntros (l err rs') "(%err_is_nil & own_rs & l & deepcopy & well_formed)".
  wp_auto.
  iApply "HΦ". iFrame. done.
Qed.

End proof.
