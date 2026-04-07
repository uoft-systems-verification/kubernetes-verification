From Perennial.algebra Require Export auth_map auth_set.
Require Export New.proof.sync.
From New.proof.kubernetes_model Require Export apimodel_init.
From New.proof.k8s_io.apimachinery.pkg.api Require Export meta.
From New.proof.k8s_io.apimachinery.pkg.apis.meta Require Export v1.
From New.proof Require Import prelude empty_ffi.
From New.proof Require Export pure_objects string.
From New.proof.big_op Require Export big_sepL big_sepM.

Section spec.
Context `{hG: !heapGS Σ} {go_ctx: GoContext}.

(* First, find a new, clean, unified way to define the ownerships *)
(* Second, write weaker spec (e.g., for get) and use the AU spec to prove the weaker spec *)
  (* See chanlib specs *)
(* Third, unify the safety and liveness specs using (inv or stable_tok) *)

Axiom own_auth: gname → KKey.t → types.UID.t → KObjectV.t → gset KKey.t → iProp Σ.

Axiom own_meta_frag: gname → KKey.t → types.UID.t → ObjectMetaV.t → iProp Σ.

Axiom own_spec_frag: gname → KKey.t → types.UID.t → ObjectSpecV.t → iProp Σ.

Axiom own_status_frag: gname → KKey.t → types.UID.t → ObjectStatusV.t → iProp Σ.

Axiom own_children_frag: gname → KKey.t → types.UID.t → gset KKey.t → iProp Σ.

Inductive KeyLifecycle :=
| Idle
| Used.

Axiom own_reserved_key_frag: gname → KKey.t → KeyLifecycle → iProp Σ.

(* A tombstone of the object and its uid. It's persistent. *)
Axiom own_tombstone_p_frag: gname → KKey.t → types.UID.t → iProp Σ.

(* A snapshot of the object given the key, uid, and rv. It's persistent. *)
Axiom own_snapshot_p_frag: gname → KKey.t → types.UID.t → go_string → KObjectV.t → iProp Σ.

Definition own_snapshot_p_frag_of γ kobj: iProp Σ :=
  own_snapshot_p_frag γ
    (KObjectV.key kobj)
    (KObjectV.objectmeta kobj).(ObjectMetaV.UID')
    (KObjectV.objectmeta kobj).(ObjectMetaV.ResourceVersion')
    kobj.

Axiom is_kubernetes: gname → loc → iProp Σ. (* Kubernetes invariant *)

Lemma wp_State__get γ l key:
  {{{ is_pkg_init apimodel ∗
      "#Hisk" ∷ is_kubernetes γ l
  }}}
    l @ (ptrT.id apimodel.State.id) @ "get" #key
  {{{ i (err: error.t) kobj, RET (#i, #err);
      ⌜ err = interface.nil ⌝ ∗
      ⌜ KObjectV.valid kobj ⌝ ∗
      ⌜ key = KObjectV.key kobj ⌝ ∗
      KObjectV.deepown_i i kobj 1 ∗
      own_snapshot_p_frag_of γ kobj
      ∨
      ⌜ err ≠ interface.nil ⌝
  }}}.
Proof. Admitted.

Lemma wp_State__get_none γ l key uid:
  {{{ is_pkg_init apimodel ∗
      "#Hisk" ∷ is_kubernetes γ l ∗
      "#Htomb" ∷ own_tombstone_p_frag γ key uid
  }}}
    l @ (ptrT.id apimodel.State.id) @ "get" #key
  {{{ i (err: error.t) kobj, RET (#i, #err);
      ⌜ err = interface.nil ⌝ ∗
      ⌜ KObjectV.valid kobj ⌝ ∗
      ⌜ key = KObjectV.key kobj ⌝ ∗
      ⌜ uid ≠ (KObjectV.objectmeta kobj).(ObjectMetaV.UID') ⌝ ∗
      KObjectV.deepown_i i kobj 1 ∗
      own_snapshot_p_frag_of γ kobj
      ∨
      ⌜ err ≠ interface.nil ⌝
  }}}.
Proof. Admitted.

Lemma wp_State__get_some_au γ l key:
  ∀ Φ,
  ( is_pkg_init apimodel ∗
    is_kubernetes γ l ∗
    |={⊤,∅}=> ∃ uid kmeta kspec_o kstatus_o i kobj,
      ⌜ uid = kmeta.(ObjectMetaV.UID') ⌝ ∗
      own_meta_frag γ key uid kmeta ∗
      match kspec_o with
      | Some kspec => own_spec_frag γ key uid kspec
      | None => True
      end ∗
      match kstatus_o with
      | Some kstatus => own_status_frag γ key uid kstatus
      | None => True
      end ∗
      ( ⌜ KObjectV.valid kobj ⌝ ∗
        ⌜ key = KObjectV.key kobj ⌝ ∗
        ⌜ kmeta = KObjectV.objectmeta kobj ⌝ ∗
        KObjectV.deepown_i i kobj 1 ∗
        own_meta_frag γ key uid kmeta ∗
        match kspec_o with
        | Some kspec => own_spec_frag γ key uid kspec ∗ ⌜ kspec = KObjectV.spec kobj ⌝
        | None => True
        end ∗
        match kstatus_o with
        | Some kstatus => own_status_frag γ key uid kstatus ∗ ⌜ kstatus = KObjectV.status kobj ⌝
        | None => True
        end ∗
        own_snapshot_p_frag_of γ kobj
          ={∅,⊤}=∗ Φ (#i, #interface.nil)%V
      )
  ) -∗ WP l @ (ptrT.id apimodel.State.id) @ "get" #key {{ Φ }}.
Proof. Admitted.

Lemma wp_State__create_au γ l kind namespace i kobj key parent_key parent_uid:
  ∀ Φ,
  ( is_pkg_init apimodel ∗
    is_kubernetes γ l ∗
    ⌜ KObjectV.valid_create kind namespace kobj ⌝ ∗
    ⌜ namespace = parent_key.(KKey.Namespace') ⌝ ∗
    ⌜ obj_has_controller_parent_of kobj parent_key.(KKey.Kind') parent_key.(KKey.Name') parent_uid ⌝ ∗
    ⌜ key = (KObjectV.key kobj) ⌝ ∗
    KObjectV.deepown_i i kobj 1 ∗
    |={⊤,∅}=> ∃ children i' kobj' uid,
      own_reserved_key_frag γ key Idle ∗
      own_children_frag γ parent_key parent_uid children ∗
      ( ⌜ ObjectMetaV.created namespace (KObjectV.objectmeta kobj) (KObjectV.objectmeta kobj') ⌝ ∗
        ⌜ ObjectSpecV.created (KObjectV.spec kobj) (KObjectV.spec kobj') ⌝ ∗
        ⌜ ObjectStatusV.created (KObjectV.status kobj) (KObjectV.status kobj') ⌝ ∗
        ⌜ KObjectV.valid kobj' ⌝ ∗
        ⌜ key = (KObjectV.key kobj') ⌝ ∗
        ⌜ key ∉ children ⌝ ∗ (* This should be precondition? *)
        ⌜ uid = (KObjectV.objectmeta kobj').(ObjectMetaV.UID') ⌝ ∗
        KObjectV.deepown_i i' kobj' 1 ∗
        own_reserved_key_frag γ key Used ∗
        own_meta_frag γ key uid (KObjectV.objectmeta kobj') ∗
        own_spec_frag γ key uid (KObjectV.spec kobj') ∗
        own_status_frag γ key uid (KObjectV.status kobj') ∗
        own_children_frag γ parent_key parent_uid (children ∪ {[key]}) ∗
        own_children_frag γ key uid ∅ ∗
        own_snapshot_p_frag_of γ kobj'
          ={∅,⊤}=∗ Φ (#i', #interface.nil)%V
      )
  ) -∗ WP l @ (ptrT.id apimodel.State.id) @ "create" #kind #namespace #i {{ Φ }}.
Proof. Admitted.

Lemma wp_State__update_au γ l kind namespace i key uid rv prev_kobj kobj:
  ∀ Φ,
    is_pkg_init apimodel ∗
    is_kubernetes γ l ∗
    own_snapshot_p_frag γ key uid rv prev_kobj ∗
    ⌜ key = KObjectV.key kobj ⌝ ∗
    (* valid_update implies that kobj's rv is equal to prev_kobj's rv *)
    ⌜ KObjectV.valid_update kind namespace prev_kobj kobj ⌝ ∗
    (* simple update doesn't adopt, release, or delete any object *)
    ⌜ ObjectMetaV.simple_update (KObjectV.objectmeta prev_kobj) (KObjectV.objectmeta kobj) ⌝ ∗
    KObjectV.deepown_i i kobj 1 ∗
    ( |={⊤,∅}=> ∃ kmeta kspec i' err kobj',
      own_meta_frag γ key uid kmeta ∗
      own_spec_frag γ key uid kspec ∗
      ( ⌜ kmeta.(ObjectMetaV.ResourceVersion') = rv ⌝ ∗
        ⌜ err = interface.nil ⌝ ∗
        ⌜ KObjectV.valid kobj' ⌝ ∗
        ⌜ ObjectMetaV.updated kmeta (KObjectV.objectmeta kobj) (KObjectV.objectmeta kobj') ⌝ ∗
        ⌜ ObjectSpecV.updated kspec (KObjectV.spec kobj) (KObjectV.spec kobj') ⌝ ∗
        KObjectV.deepown_i i' kobj' 1 ∗
        own_meta_frag γ key uid (KObjectV.objectmeta kobj') ∗
        own_spec_frag γ key uid (KObjectV.spec kobj') ∗
        own_snapshot_p_frag_of γ kobj'
        ∨
        ⌜ kmeta.(ObjectMetaV.ResourceVersion') ≠ rv ⌝ ∗
        ⌜ err ≠ interface.nil ⌝ ∗
        own_meta_frag γ key uid kmeta ∗
        own_spec_frag γ key uid kspec
          ={∅,⊤}=∗ Φ (#i', #interface.nil)%V
      )
    ) -∗ WP l @ (ptrT.id apimodel.State.id) @ "update" #kind #namespace #i {{ Φ }}.
Proof. Admitted.

Lemma wp_State__update_status_au γ l kind namespace i key uid rv prev_kobj kobj:
  ∀ Φ,
    is_pkg_init apimodel ∗
    is_kubernetes γ l ∗
    own_snapshot_p_frag γ key uid rv prev_kobj ∗
    ⌜ key = KObjectV.key kobj ⌝ ∗
    (* valid_update_status implies that kobj's rv is equal to prev_kobj's rv *)
    ⌜ KObjectV.valid_update_status kind namespace prev_kobj kobj ⌝ ∗
    (* simple update_status doesn't modify anything in objectmeta *)
    ⌜ ObjectMetaV.simple_update_status (KObjectV.objectmeta prev_kobj) (KObjectV.objectmeta kobj) ⌝ ∗
    KObjectV.deepown_i i kobj 1 ∗
    ( |={⊤,∅}=> ∃ kmeta kstatus i' err kobj',
      own_meta_frag γ key uid kmeta ∗
      own_status_frag γ key uid kstatus ∗
      ( ⌜ kmeta.(ObjectMetaV.ResourceVersion') = rv ⌝ ∗
        ⌜ err = interface.nil ⌝ ∗
        ⌜ KObjectV.valid kobj' ⌝ ∗
        (* After simple update_status only the resource version should change in objectmeta *)
        ⌜ ObjectMetaV.rv_updated kmeta (KObjectV.objectmeta kobj') ⌝ ∗
        ⌜ ObjectStatusV.updated kstatus (KObjectV.status kobj) (KObjectV.status kobj') ⌝ ∗
        KObjectV.deepown_i i' kobj' 1 ∗
        own_meta_frag γ key uid (KObjectV.objectmeta kobj') ∗
        own_status_frag γ key uid (KObjectV.status kobj') ∗
        own_snapshot_p_frag_of γ kobj'
        ∨
        ⌜ kmeta.(ObjectMetaV.ResourceVersion') ≠ rv ⌝ ∗
        ⌜ err ≠ interface.nil ⌝ ∗
        own_meta_frag γ key uid kmeta ∗
        own_status_frag γ key uid kstatus
          ={∅,⊤}=∗ Φ (#i', #interface.nil)%V
      )
    ) -∗ WP l @ (ptrT.id apimodel.State.id) @ "updateStatus" #kind #namespace #i {{ Φ }}.
Proof. Admitted.

End spec.
