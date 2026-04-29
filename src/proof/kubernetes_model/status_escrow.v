From New.proof Require Import prelude empty_ffi.
From New.proof.kubernetes_model Require Export inv.

Section proof.
Context `{hG: !heapGS Σ} {go_ctx: GoContext}.
Context `{!kviewG Σ}.
Context `{!cviewG Σ}.
Context `{!mono_gsetG types.UID.t Σ}.

(*
  This file sketches the ownership pattern for object status after create.

  The Kubernetes API server physically initializes status when it creates an
  object, so the kview allocation rule should still mint an own_status_frag.
  The important point is that the fragment does not have to be returned to the
  controller that called create.  Instead, create can put the fragment into a
  linear pool owned by the controller responsible for that object's status.

  For example, after a Deployment controller creates a ReplicaSet, create can
  return the ReplicaSet's meta/spec fragments to the Deployment controller and
  place the ReplicaSet status fragment in the ReplicaSet status pool.
*)

Inductive status_owner :=
| PodStatusOwner
| ReplicaSetStatusOwner.

(*
  This is the policy function deciding which controller owns status for a newly
  created object.  It is intentionally kind-based here.  If the model later has
  more precise controller identities, this function is the place to refine the
  policy.
*)
Definition status_owner_of_kind (kind : go_string) : option status_owner :=
  if bool_decide (kind = "Pod"%go) then
    Some PodStatusOwner
  else if bool_decide (kind = "ReplicaSet"%go) then
    Some ReplicaSetStatusOwner
  else
    None.

Definition status_owner_of_key (key : KKey.t) : option status_owner :=
  status_owner_of_kind key.(KKey.Kind').

(*
  One escrow entry is just the full status fragment plus a pure proof that it is
  stored in the pool for the right owner.

  This resource is deliberately linear: whoever removes it from the pool owns
  the full status fragment and must put back a status fragment before closing
  the surrounding controller invariant.
*)
Definition status_escrow_entry
    (γ : KubernetesGname) (owner : status_owner)
    (key : KKey.t) (uid : types.UID.t) (status : ObjectStatusV.t) : iProp Σ :=
  ⌜ status_owner_of_key key = Some owner ⌝ ∗
  own_status_frag γ key uid 1 status.

(*
  status_escrows can be read as a finite map of status fragments.  Each map
  entry owns the full own_status_frag for one (key, uid), so the map is a linear
  resource and cannot be duplicated.

  The important point is that this map should be internal API-server/controller
  state, not a resource returned by create to the create caller.  If the public
  create spec returned:

    status_escrows γ ReplicaSetStatusOwner
      (<[(key, uid) := KObjectV.status kobj']> status_pool)

  then the caller would indeed indirectly own the ReplicaSet status fragment and
  could use it to prove an UpdateStatus call.  That would not prevent a
  Deployment controller from updating ReplicaSet status after creating the
  ReplicaSet.

  A better full integration is to hide the status pools inside a Kubernetes
  status invariant, or directly as another field of kubernetes_inv:

    Definition status_escrow_inv γ : iProp Σ :=
      ∃ pod_statuses rs_statuses,
        "Hpod_statuses" ∷ status_escrows γ PodStatusOwner pod_statuses ∗
        "Hrs_statuses" ∷ status_escrows γ ReplicaSetStatusOwner rs_statuses.

    Definition is_status_escrow γ : iProp Σ :=
      inv status_escrowN (status_escrow_inv γ).

  The public create spec would have access to is_status_escrow, open it
  internally at the create linearization point, insert the freshly minted
  own_status_frag into the appropriate pool, and close the invariant.  The
  public create postcondition would return meta/spec ownership but not the
  status pool itself.

  To prevent arbitrary code from using the hidden pool for status updates,
  UpdateStatus should also require a controller-specific capability, allocated
  only to the controller responsible for that status:

    status_update_cap γ ReplicaSetStatusOwner

  The ReplicaSet controller invariant/spec would contain this capability:

    Definition replicaset_controller_inv γ : iProp Σ :=
      "Hrs_status_cap" ∷ status_update_cap γ ReplicaSetStatusOwner ∗
      (* other ReplicaSet-controller resources, such as workqueue state,
         informer/index ownership, and local controller ghost state. *) True.

  The Deployment controller may receive the meta/spec fragments for a ReplicaSet
  it creates, but it should not receive status_update_cap γ ReplicaSetStatusOwner
  and it should not receive status_escrows γ ReplicaSetStatusOwner rs_statuses.
  Therefore it cannot satisfy the UpdateStatus precondition for ReplicaSet
  status.  The pure status_owner_of_key check prevents using a Pod capability on
  a ReplicaSet key; the linear own_status_frag prevents duplicating the actual
  status permission.
*)
Definition status_escrows
    (γ : KubernetesGname) (owner : status_owner)
    (statuses : gmap (KKey.t * types.UID.t) ObjectStatusV.t) : iProp Σ :=
  [∗ map] key_uid ↦ status ∈ statuses,
    status_escrow_entry γ owner (fst key_uid) (snd key_uid) status.

(*
  This is the operation create would use after kview.create_kobj_vs mints
  Hown_status.  The caller receives meta/spec ownership; Hown_status is inserted
  into the owner-specific pool instead.
*)
Lemma status_escrows_insert γ owner statuses key uid status :
  status_owner_of_key key = Some owner →
  statuses !! (key, uid) = None →
  status_escrows γ owner statuses -∗
  own_status_frag γ key uid 1 status -∗
  status_escrows γ owner (<[(key, uid) := status]> statuses).
Proof.
  iIntros (Howner Hfresh) "Hescrows Hstatus".
  rewrite /status_escrows big_sepM_insert //.
  iSplitL "Hstatus".
  - rewrite /status_escrow_entry /=. iFrame. done.
  - iExact "Hescrows".
Qed.

(*
  A status-update proof would typically use a lookup/access lemma for this pool:

    status_escrows γ owner statuses ==∗
      own_status_frag γ key uid 1 old_status ∗
      (∀ new_status,
         own_status_frag γ key uid 1 new_status -∗
         status_escrows γ owner (<[(key, uid) := new_status]> statuses))

  The exact statement should be chosen when status update specs are added,
  because this repository's current update_status_kobj_vs also requires
  own_meta_frag to account for metadata changes such as resourceVersion.

  The two public specs I would aim for are below.  They intentionally do not
  return status_escrows.  The status pool is hidden behind is_status_escrow, and
  UpdateStatus additionally requires a controller-specific status_update_cap.
  UpdateStatus is not yet implemented in apimodel, so the second spec is a
  proposed future shape.  With the current kview algebra it still takes and
  returns own_meta_frag; a cleaner future model could replace that with a
  smaller system-metadata token.

  Proposed create spec:

    Lemma wp_State__create_nameless_with_status_escrow
        γ l kind namespace i kobj parent_key parent_uid children :
      {{{ is_pkg_init apimodel ∗
          "#Hisk" ∷ is_kubernetes γ l ∗
          "#Hstatus_escrow" ∷ is_status_escrow γ ∗
          "%Hvalid" ∷ ⌜ KObjectV.valid_nameless_create kind namespace kobj ⌝ ∗
          "%Hns_nonempty" ∷ ⌜ namespace ≠ ""%go ⌝ ∗
          "%Hns_valid" ∷ ⌜ valid_namespace namespace ⌝ ∗
          "%Hns_eq" ∷ ⌜ namespace = parent_key.(KKey.Namespace') ⌝ ∗
          "%Hpr" ∷ ⌜ obj_parent_ref_is kobj parent_key.(KKey.Kind')
                       parent_key.(KKey.Name') parent_uid ⌝ ∗
          "Hdeepown" ∷ KObjectV.deepown_i i kobj 1 ∗
          "Hown_children_frag" ∷ own_children_frag γ parent_key parent_uid
              1 children
      }}}
        l @ (ptrT.id apimodel.State.id) @ "create" #kind #namespace #i
      {{{ i' kobj' key uid, RET (#i', #interface.nil);
          "%Hvalid'" ∷ ⌜ KObjectV.valid kobj' ⌝ ∗
          "%Hsame_kind" ∷ ⌜ KObjectV.same_kind kobj kobj' ⌝ ∗
          "%Hmeta_created" ∷
            ⌜ ObjectMetaV.nameless_created namespace
                (KObjectV.objectmeta kobj) (KObjectV.objectmeta kobj') ⌝ ∗
          "%Hspec_created" ∷
            ⌜ ObjectSpecV.created (KObjectV.spec kobj)
                (KObjectV.spec kobj') ⌝ ∗
          "%Hstatus_created" ∷
            ⌜ ObjectStatusV.created (KObjectV.status kobj)
                (KObjectV.status kobj') ⌝ ∗
          "%Hkey_eq" ∷ ⌜ key = KObjectV.key kobj' ⌝ ∗
          "%Hkey_fresh" ∷ ⌜ key ∉ children ⌝ ∗
          "%Huid_eq" ∷
            ⌜ uid = (KObjectV.objectmeta kobj').(ObjectMetaV.UID') ⌝ ∗
          "%Hstatus_owner" ∷ ⌜ ∃ status_owner,
              status_owner_of_key key = Some status_owner ⌝ ∗
          "Hdeepown_i" ∷ KObjectV.deepown_i i' kobj' 1 ∗
          "Hown_meta" ∷ own_meta_frag γ key uid 1
              (KObjectV.objectmeta kobj') ∗
          "Hown_spec" ∷ own_spec_frag γ key uid 1 (KObjectV.spec kobj') ∗
          "Hown_children" ∷ own_children_frag γ parent_key parent_uid
              1 (children ∪ {[key]}) ∗
          "Hown_grandchildren" ∷ own_children_frag γ key uid 1 ∅
      }}}.

  The intentionally missing create postcondition is:

    "Hown_status" ∷ own_status_frag γ key uid 1 (KObjectV.status kobj')

  That fragment is consumed by status_escrows_insert inside the create proof
  instead of being returned to the controller that called create.

  Proposed UpdateStatus spec:

    Lemma wp_State__update_status_with_status_escrow
        γ l kind namespace i kobj key uid old_meta status_owner :
      {{{ is_pkg_init apimodel ∗
          "#Hisk" ∷ is_kubernetes γ l ∗
          "#Hstatus_escrow" ∷ is_status_escrow γ ∗
          "#Hstatus_cap" ∷ status_update_cap γ status_owner ∗
          "%Hvalid" ∷ ⌜ KObjectV.valid kobj ⌝ ∗
          "%Hkey_eq" ∷ ⌜ key = KObjectV.key kobj ⌝ ∗
          "%Huid_eq" ∷
            ⌜ uid = (KObjectV.objectmeta kobj).(ObjectMetaV.UID') ⌝ ∗
          "%Hstatus_owner" ∷ ⌜ status_owner_of_key key = Some status_owner ⌝ ∗
          "Hdeepown" ∷ KObjectV.deepown_i i kobj 1 ∗
          "Hown_meta" ∷ own_meta_frag γ key uid 1 old_meta
      }}}
        l @ (ptrT.id apimodel.State.id) @ "updateStatus" #kind #namespace #i
      {{{ i' kobj' stored_old_status new_meta new_status,
          RET (#i', #interface.nil);
          "%Hvalid'" ∷ ⌜ KObjectV.valid kobj' ⌝ ∗
          "%Hkey_eq'" ∷ ⌜ key = KObjectV.key kobj' ⌝ ∗
          "%Huid_eq'" ∷
            ⌜ uid = (KObjectV.objectmeta kobj').(ObjectMetaV.UID') ⌝ ∗
          "%Hmeta_eq" ∷ ⌜ new_meta = KObjectV.objectmeta kobj' ⌝ ∗
          "%Hstatus_eq" ∷ ⌜ new_status = KObjectV.status kobj' ⌝ ∗
          "%Hmeta_updated" ∷
            ⌜ ObjectMetaV.updated old_meta
                (KObjectV.objectmeta kobj) new_meta ⌝ ∗
          "%Hstatus_updated" ∷
            ⌜ ObjectStatusV.updated stored_old_status
                (KObjectV.status kobj) new_status ⌝ ∗
          "Hdeepown_i" ∷ KObjectV.deepown_i i' kobj' 1 ∗
          "Hown_meta" ∷ own_meta_frag γ key uid 1 new_meta
      }}}.

  The intentionally missing UpdateStatus postcondition is also the direct
  status fragment.  The API proof gets temporary access to it by opening
  is_status_escrow after checking Hstatus_cap, then closes the invariant with
  the updated status.  The spec returns neither the updated pool nor:

    "Hown_status" ∷ own_status_frag γ key uid 1 new_status
*)

End proof.
