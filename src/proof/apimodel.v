From Perennial.algebra Require Export auth_map.
From New.proof.github_com.goose_lang.goose.model.channel Require Export auth_set.
Require Export New.proof.sync.

From proof.kubernetes_model Require Export apimodel_init.
From proof.k8s_io.apimachinery.pkg.api Require Export meta.
From proof.k8s_io.apimachinery.pkg.apis.meta Require Export v1.
From proof Require Import prelude empty_ffi.
From proof Require Export deepcopy well_formed.
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

Definition pod_rep k v1 v2 ptr pod : iProp Σ :=
  "%interface_is_pod_ptr" ∷ ⌜ v1 = interface.mk (ptrT.id v1.Pod.id) #ptr ⌝ ∗
  "pod_ptr" ∷ ptr ↦ pod ∗
  "%abs_v_is_pod" ∷ ⌜ v2 = KObject.Pod pod ⌝ ∗
  "pod_nn_well_formed" ∷ pod_nn_well_formed pod (KKey.Namespace' k) (KKey.Name' k).

Definition replicaset_rep k v1 v2 ptr rs : iProp Σ :=
  "%interface_is_rs_ptr" ∷ ⌜ v1 = interface.mk (ptrT.id v1.ReplicaSet.id) #ptr ⌝ ∗
  "rs_ptr" ∷ ptr ↦ rs ∗
  "%abs_v_is_rs" ∷ ⌜ v2 = KObject.ReplicaSet rs ⌝ ∗
  "replicaset_nn_well_formed" ∷ replicaset_nn_well_formed rs (KKey.Namespace' k) (KKey.Name' k).

Definition state_rep (phys_state: gmap KKey.t interface.t) (abs_state: gmap KKey.t KObject.t) : iProp Σ :=
  [∗ map] k ↦ v1; v2 ∈ phys_state; abs_state,
    if bool_decide (KKey.Kind' k = "Pod"%go) then
      ∃ (ptr: loc) (pod: v1.Pod.t), pod_rep k v1 v2 ptr pod
    else if bool_decide (KKey.Kind' k = "ReplicaSet"%go) then
      ∃ (ptr: loc) (rs: v1.ReplicaSet.t), replicaset_rep k v1 v2 ptr rs
    else False%I.

Axiom kubernetes_state_consistent: gmap KKey.t KObject.t → gmap KKey.t (gset KKey.t) → gset KKey.t → iProp Σ. 

Definition is_kubernetes_state_inner γ_state γ_children γ_fresh_keys: iProp Σ :=
  ∃ (l: loc) (uc: w64) (rvc: w64) (phys_state: gmap KKey.t interface.t) (abs_state: gmap KKey.t KObject.t) (children: gmap KKey.t (gset KKey.t)) (fresh_keys: gset KKey.t),
    "state_m_addr" ∷ (global_addr apimodel.state) ↦s[ apimodel.State :: "m" ] l ∗
    "state_uc_addr" ∷ (global_addr apimodel.state) ↦s[ apimodel.State :: "uidCounter" ] uc ∗
    "state_rvc_addr" ∷ (global_addr apimodel.state) ↦s[ apimodel.State :: "resourceVersionCounter" ] rvc ∗
    "own_phys" ∷ l ↦$ phys_state ∗
    "own_abs" ∷ map_ctx γ_state 1 abs_state ∗
    "phys_abs_rep" ∷ state_rep phys_state abs_state ∗
    "own_children" ∷ map_ctx γ_children 1 children ∗
    "own_fresh_keys" ∷ auth_set_auth γ_fresh_keys fresh_keys ∗
    "consistent" ∷ kubernetes_state_consistent abs_state children fresh_keys.

Definition is_kubernetes_state γ_state γ_children γ_fresh_keys : iProp Σ :=
  is_Mutex (global_addr apimodel.stateMu) (is_kubernetes_state_inner γ_state γ_children γ_fresh_keys).

Definition pod_has_controller_parent_uid (pod: v1.Pod.t) (os: list v1.OwnerReference.t) (o: v1.OwnerReference.t) (c: bool) : iProp Σ :=
  pod.(v1.Pod.ObjectMeta').(v1.ObjectMeta.OwnerReferences') ↦* os ∗
  ⌜ o ∈ os ⌝ ∗
  o.(v1.OwnerReference.Controller') ↦ c ∗
  ⌜ c = true ⌝.

Definition is_pod_controller_uid_index (pod: v1.Pod.t) (indexed_value: go_string) : iProp Σ :=
  (∃ os o c, pod_has_controller_parent_uid pod os o c ∗ ⌜ o.(v1.OwnerReference.UID') = indexed_value ⌝) ∨
  (¬(∃ os o c, pod_has_controller_parent_uid pod os o c) ∗ ⌜ indexed_value = "_ORPHAN_POD"%go ⌝).

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
  wp_start as "H". iNamed "H".
  wp_apply wp_with_defer. simpl subst.
  iIntros (defer) "defer". wp_auto. iRename "key" into "key_ptr".
  wp_apply wp_globals_get.
  wp_apply wp_Mutex__Lock.
  { done. }
  iIntros "[own_Mutex H]". iNamed "H". wp_auto.
  wp_apply wp_globals_get. wp_apply wp_globals_get.
  wp_apply (wp_map_get with "[$own_phys]").
  iIntros "own_phys". wp_auto.
  (* wp_apply (wp_Mutex__Unlock _ (is_kubernetes_state_inner γ_state γ_children γ_fresh_keys)
    with "[$own_Mutex state_m_addr own_phys own_abs phys_abs_rep own_children own_fresh_keys]").
  { iFrame. done. }
  iApply ("HΦ" $! (default interface.nil (phys_state !! key))
                 (bool_decide (is_Some (phys_state !! key)))).
  done. *)
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
      is_pod_controller_uid_index pod indexed_value
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
        (∃ os o c, pod_has_controller_parent_uid pod os o c ∗ ⌜ o.(v1.OwnerReference.UID') = indexed_value ⌝)
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

Lemma wp_PodCreate_without_name namespace to_create_pod_ptr to_create_pod
  γ_state γ_children γ_fresh_keys parent_key owned_parent owned_child_keys:
  {{{ is_pkg_init apimodel ∗
      "#inv" ∷ is_kubernetes_state γ_state γ_children γ_fresh_keys ∗
      "own_parent" ∷ parent_key [[ γ_state ]]↦ owned_parent ∗
      "own_child_keys" ∷ parent_key [[ γ_children ]]↦ owned_child_keys ∗
      "%namespace_valid" ∷ ⌜ namespace = parent_key.(KKey.Namespace') ⌝ ∗
      "to_create_pod_ptr" ∷ to_create_pod_ptr ↦ to_create_pod ∗
      "parent_uid" ∷ (∃ os o c, pod_has_controller_parent_uid to_create_pod os o c ∗
        ⌜ o.(v1.OwnerReference.UID') = (extract_kobject_metadata owned_parent).(v1.ObjectMeta.UID') ⌝) ∗
      "%no_name" ∷ ⌜ to_create_pod.(v1.Pod.ObjectMeta').(v1.ObjectMeta.Name') = ""%go ⌝ ∗
      "%generate_name" ∷ ⌜ to_create_pod.(v1.Pod.ObjectMeta').(v1.ObjectMeta.Name') ≠ ""%go⌝ ∗
      "well_formed_for_creation" ∷ pod_well_formed_for_creation to_create_pod
  }}}
    @! apimodel.objCreate #namespace #to_create_pod_ptr
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
Admitted.

Lemma pod_ptr_implements_v1_object i (ptr: loc):
  i = interface.mk (ptrT.id v1.Pod.id) (# ptr) →
    ∃ (o: v1.Object.t), i = interface.mk v1.Object.id (# o) ∧
      o = interface.mk (ptrT.id v1.ObjectMeta.id) #(struct.field_ref_f v1.Pod "ObjectMeta" ptr).
Proof.
Admitted.

Lemma wp_FormatInt (i: w64) (base: w64):
  {{{ is_pkg_init apimodel }}}
    @! strconv.FormatInt #i #base
  {{{ (v: go_string), RET #v; True }}}.
Proof.
Admitted.

Lemma wp_objDelete_ptsto_mut key γ_state γ_children γ_fresh_keys owned_pod parent_key owned_child_keys:
  {{{ is_pkg_init apimodel ∗
      "#inv" ∷ is_kubernetes_state γ_state γ_children γ_fresh_keys ∗
      "own_pod" ∷ key [[ γ_state ]]↦ (KObject.Pod owned_pod) ∗
      "own_child_keys" ∷ parent_key [[ γ_children ]]↦ owned_child_keys ∗
      "%pod_is_child" ∷ ⌜ key ∈ owned_child_keys ⌝ ∗
      "%kind" ∷ ⌜ KKey.Kind' key = "Pod"%go ⌝
  }}}
    @! apimodel.objDelete #key
  {{{ (err: error.t) pod, RET #err;
      ⌜ err = interface.nil ⌝ ∗
      (
        key [[ γ_state ]]↦ (KObject.Pod pod) ∗
        parent_key [[ γ_children ]]↦ owned_child_keys ∗
        ⌜ pod.(v1.Pod.ObjectMeta').(v1.ObjectMeta.DeletionTimestamp') ≠ null ⌝
      ) ∨
      parent_key [[ γ_children ]]↦ (owned_child_keys ∖ {[key]})
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
  { 
    iDestruct (map_valid with "own_abs own_pod") as %Hlookup.
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
  destruct decide_kind_is_pod with (KKey.Kind' key) as [kind_is_pod kind_is_not_replicaset].
  { done. }
  rewrite kind_is_pod.
  iDestruct "k_rep" as "(%ptr & %rs0 & rs_rep)". iNamed "rs_rep".
  inversion abs_v_is_pod as [Heq]. symmetry in Heq. subst. clear abs_v_is_pod.
  wp_apply (wp_map_get with "[$own_phys]"). iIntros "own_phys". wp_auto.
  rewrite /is_Some key_in_phys. wp_auto.
  destruct (pod_ptr_implements_v1_object (interface.mk (ptrT.id v1.Pod.id) (# ptr)) ptr) as [o [interface_is_object object_is_ptr]].
  { done. }
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
    + wp_apply v1.wp_Now. iIntros (time) "_". wp_auto.
      wp_apply (wp_SetDeletionTimestamp with "[$HObjectMeta]").
      iIntros (meta') "(-> & HObjectMeta)". wp_auto.
      wp_apply wp_globals_get.
      (* TODO: handle resource version counter overflow *)
      wp_apply wp_globals_get. wp_apply wp_globals_get.
      wp_apply wp_FormatInt. iIntros (rv_str) "_". wp_auto.
      wp_apply (wp_SetResourceVersion with "[$HObjectMeta]").
      iIntros (meta') "(-> & HObjectMeta)". wp_auto.
      wp_apply wp_globals_get.
      wp_apply (wp_map_insert with "[$own_phys]").
      iIntros "own_phys". wp_auto.
      iDestruct (struct_fields_combine (v:=v1.Pod.mk _ _ _ _)
        with "[$HTypeMeta $HObjectMeta $HSpec $HStatus]") as "new_pod_ptr". simpl.
      admit.
    + wp_apply wp_globals_get.
      wp_apply (wp_map_insert with "[$own_phys]").
      iIntros "own_phys". wp_auto.
      iDestruct (struct_fields_combine (V:=v1.Pod.t)
        with "[$HTypeMeta $HObjectMeta $HSpec $HStatus]") as "pod_ptr".
      admit.
  - wp_apply wp_globals_get.
    wp_apply (wp_map_delete with "[$own_phys]").
    iIntros "own_phys". wp_auto.
    iDestruct (struct_fields_combine (V:=v1.Pod.t)
        with "[$HTypeMeta $HObjectMeta $HSpec $HStatus]") as "pod_ptr".
    admit.
Admitted.

Lemma wp_PodDelete_ptsto_mut key γ_state γ_children γ_fresh_keys owned_pod parent_key owned_child_keys:
  {{{ is_pkg_init apimodel ∗
      "#inv" ∷ is_kubernetes_state γ_state γ_children γ_fresh_keys ∗
      "own_pod" ∷ key [[ γ_state ]]↦ (KObject.Pod owned_pod) ∗
      "own_child_keys" ∷ parent_key [[ γ_children ]]↦ owned_child_keys ∗
      "%pod_is_child" ∷ ⌜ key ∈ owned_child_keys ⌝ ∗
      "%kind" ∷ ⌜ KKey.Kind' key = "Pod"%go ⌝
  }}}
    @! apimodel.PodDelete #key
  {{{ (err: error.t) pod, RET #err;
      ⌜ err = interface.nil ⌝ ∗
      (
        key [[ γ_state ]]↦ (KObject.Pod pod) ∗
        parent_key [[ γ_children ]]↦ owned_child_keys ∗
        ⌜ pod.(v1.Pod.ObjectMeta').(v1.ObjectMeta.DeletionTimestamp') ≠ null ⌝
      ) ∨
      parent_key [[ γ_children ]]↦ (owned_child_keys ∖ {[key]})
  }}}.
Proof.
Admitted.

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
  rewrite kind_is_replicaset kind_is_not_pod.
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
