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

Axiom own_meta_frag: gname → KKey.t → types.UID.t → option PureObjectMeta.t → iProp Σ.

Axiom own_weak_spec_frag: gname → KKey.t → types.UID.t → PureObjectSpec.t → iProp Σ.

Axiom own_weak_status_frag: gname → KKey.t → types.UID.t → PureObjectStatus.t → iProp Σ.

Axiom own_weak_children_frag: gname → KKey.t → types.UID.t → gset KKey.t → iProp Σ.

Axiom own_fresh_key_frag: gname → KKey.t → iProp Σ.

(* A snapshot of the object given the key, uid, and rv. It's persistent. *)
Axiom own_snapshot_ro_frag: gname → KKey.t → types.UID.t → go_string → PureKObject.t → iProp Σ.

Definition own_snapshot_ro_frag_of γ kobj: iProp Σ :=
  own_snapshot_ro_frag γ
    (PureKObject.key kobj)
    (PureKObject.objectmeta kobj).(PureObjectMeta.UID')
    (PureKObject.objectmeta kobj).(PureObjectMeta.ResourceVersion')
    kobj.

Axiom is_kubernetes: gname → loc → iProp Σ. (* Kubernetes invariant *)

Axiom valid: PureKObject.t → Prop.

Lemma wp_State__get γ l key:
  {{{ is_pkg_init apimodel ∗
      "#Hisk" ∷ is_kubernetes γ l
  }}}
    l @ (ptrT.id apimodel.State.id) @ "get" #key
  {{{ i (err: error.t) kobj, RET (#i, #err);
      ( ⌜ err = interface.nil ⌝ ∗
        ⌜ valid kobj ⌝ ∗
        ⌜ key = PureKObject.key kobj ⌝ ∗
        PureKObject.deepown_i i kobj 1 ∗
        own_snapshot_ro_frag_of γ kobj
      ) ∨
      ⌜ err ≠ interface.nil ⌝
  }}}.
Proof. Admitted.

Lemma wp_State__get_none γ l key uid:
  {{{ is_pkg_init apimodel ∗
      "#Hisk" ∷ is_kubernetes γ l ∗
      "Hmeta" ∷ own_meta_frag γ key uid None
  }}}
    l @ (ptrT.id apimodel.State.id) @ "get" #key
  {{{ i (err: error.t) kobj, RET (#i, #err);
      (( ⌜ err = interface.nil ⌝ ∗
          ⌜ valid kobj ⌝ ∗
          ⌜ key = PureKObject.key kobj ⌝ ∗
          ⌜ uid ≠ (PureKObject.objectmeta kobj).(PureObjectMeta.UID') ⌝ ∗
          PureKObject.deepown_i i kobj 1 ∗
          own_snapshot_ro_frag_of γ kobj
        ) ∨
        ⌜ err ≠ interface.nil ⌝
      )
      ∗ own_meta_frag γ key uid None 
  }}}.
Proof. Admitted.

Lemma wp_State__get_some γ l key uid kmeta kspec_o kstatus_o:
  {{{ is_pkg_init apimodel ∗
      "#Hisk" ∷ is_kubernetes γ l ∗
      "%Huid" ∷ ⌜ uid = kmeta.(PureObjectMeta.UID') ⌝ ∗
      "Hmeta" ∷ own_meta_frag γ key uid (Some kmeta) ∗
      "Hspec" ∷ (match kspec_o with
                  | Some kspec => own_weak_spec_frag γ key uid kspec
                  | None => True
                  end) ∗
      "Hstatus" ∷ (match kstatus_o with
                  | Some kstatus => own_weak_status_frag γ key uid kstatus
                  | None => True
                  end)
  }}}
    l @ (ptrT.id apimodel.State.id) @ "get" #key
  {{{ i kobj, RET (#i, #interface.nil);
      ⌜ valid kobj ⌝ ∗
      ⌜ key = PureKObject.key kobj ⌝ ∗
      ⌜ kmeta = PureKObject.objectmeta kobj ⌝ ∗
      PureKObject.deepown_i i kobj 1 ∗
      own_meta_frag γ key uid (Some kmeta) ∗
      (match kspec_o with
      | Some kspec => own_weak_spec_frag γ key uid kspec ∗ ⌜ kspec = PureKObject.spec kobj ⌝
      | None => True
      end) ∗
      (match kstatus_o with
      | Some kstatus => own_weak_status_frag γ key uid kstatus ∗ ⌜ kstatus = PureKObject.status kobj ⌝
      | None => True
      end) ∗
      own_snapshot_ro_frag_of γ kobj
  }}}.
Proof. Admitted.

Axiom valid_create: go_string → PureKObject.t → Prop.

Axiom valid_nameless_create: go_string → PureKObject.t → Prop.

Lemma wp_State__create γ l kind namespace i kobj key parent_key parent_uid parent_meta children:
  {{{ is_pkg_init apimodel ∗
      "#Hisk" ∷ is_kubernetes γ l ∗
      "%Hkind_eq" ∷ ⌜ kind = PureKObject.kind kobj ⌝ ∗
      "%Hnamespace_eq" ∷ ⌜ namespace = parent_key.(KKey.Namespace') ⌝ ∗
      "%Hwf" ∷ ⌜ valid_create namespace kobj ⌝ ∗
      "%Hparent_of" ∷ ⌜ obj_has_controller_parent_of kobj parent_key.(KKey.Kind') parent_key.(KKey.Name') parent_uid ⌝ ∗
      "%Hkey_eq" ∷ ⌜ key = (PureKObject.key kobj) ⌝ ∗
      "Hdeepown_i" ∷ PureKObject.deepown_i i kobj 1 ∗
      "Hfresh_key" ∷ own_fresh_key_frag γ key ∗
      "Hparent_meta" ∷ own_meta_frag γ parent_key parent_uid (Some parent_meta) ∗
      "Hchildren" ∷ own_weak_children_frag γ parent_key parent_uid children
  }}}
    l @ (ptrT.id apimodel.State.id) @ "create" #kind #namespace #i
  {{{ i' kobj' uid, RET (#i', #interface.nil);
      ⌜ PureObjectMeta.created namespace (PureKObject.objectmeta kobj) (PureKObject.objectmeta kobj') ⌝ ∗
      ⌜ PureObjectSpec.created (PureKObject.spec kobj) (PureKObject.spec kobj') ⌝ ∗
      ⌜ PureObjectStatus.created (PureKObject.status kobj) (PureKObject.status kobj') ⌝ ∗
      ⌜ valid kobj' ⌝ ∗
      ⌜ key = (PureKObject.key kobj') ⌝ ∗
      ⌜ key ∉ children ⌝ ∗
      ⌜ uid = (PureKObject.objectmeta kobj').(PureObjectMeta.UID') ⌝ ∗
      PureKObject.deepown_i i' kobj' 1 ∗
      own_meta_frag γ key uid (Some (PureKObject.objectmeta kobj')) ∗
      own_weak_spec_frag γ key uid (PureKObject.spec kobj') ∗
      own_weak_status_frag γ key uid (PureKObject.status kobj') ∗
      own_meta_frag γ parent_key parent_uid (Some parent_meta) ∗
      own_weak_children_frag γ parent_key parent_uid (children ∪ {[key]}) ∗
      own_weak_children_frag γ key uid ∅ ∗
      own_snapshot_ro_frag_of γ kobj'
  }}}.
Proof. Admitted.

Lemma wp_State__nameless_create γ l kind namespace i kobj parent_key parent_uid parent_meta children:
  {{{ is_pkg_init apimodel ∗
      "#Hisk" ∷ is_kubernetes γ l ∗
      "%Hkind_eq" ∷ ⌜ kind = PureKObject.kind kobj ⌝ ∗
      "%Hnamespace_eq" ∷ ⌜ namespace = parent_key.(KKey.Namespace') ⌝ ∗
      "%Hparent_of" ∷ ⌜ obj_has_controller_parent_of kobj parent_key.(KKey.Kind') parent_key.(KKey.Name') parent_uid ⌝ ∗
      "%Hwf" ∷ ⌜ valid_nameless_create namespace kobj ⌝ ∗
      "Hdeepown_i" ∷ PureKObject.deepown_i i kobj 1 ∗
      "Hparent_meta" ∷ own_meta_frag γ parent_key parent_uid (Some parent_meta) ∗
      "Hchildren" ∷ own_weak_children_frag γ parent_key parent_uid children
  }}}
    l @ (ptrT.id apimodel.State.id) @ "create" #kind #namespace #i
  {{{ i' kobj' key uid, RET (#i', #interface.nil);
      ⌜ valid kobj' ⌝ ∗
      ⌜ PureObjectMeta.nameless_created namespace (PureKObject.objectmeta kobj) (PureKObject.objectmeta kobj') ⌝ ∗
      ⌜ PureObjectSpec.created (PureKObject.spec kobj) (PureKObject.spec kobj') ⌝ ∗
      ⌜ PureObjectStatus.created (PureKObject.status kobj) (PureKObject.status kobj') ⌝ ∗
      ⌜ key = (PureKObject.key kobj') ⌝ ∗
      ⌜ key ∉ children ⌝ ∗
      ⌜ uid = (PureKObject.objectmeta kobj').(PureObjectMeta.UID') ⌝ ∗
      PureKObject.deepown_i i' kobj' 1 ∗
      own_meta_frag γ key uid (Some (PureKObject.objectmeta kobj')) ∗
      own_weak_spec_frag γ key uid (PureKObject.spec kobj') ∗
      own_weak_status_frag γ key uid (PureKObject.status kobj') ∗
      own_meta_frag γ parent_key parent_uid (Some parent_meta) ∗
      own_weak_children_frag γ parent_key parent_uid (children ∪ {[key]}) ∗
      own_weak_children_frag γ key uid ∅ ∗
      own_snapshot_ro_frag_of γ kobj'
  }}}.
Proof. Admitted.

Axiom deleting: PureObjectMeta.t → PureObjectMeta.t → Prop.

Lemma wp_State__delete γ l key uid kmeta parent_key parent_uid children:
  {{{ is_pkg_init apimodel ∗
      "#Hisk" ∷ is_kubernetes γ l ∗
      "%His_child" ∷ ⌜ key ∈ children ⌝ ∗
      "Hmeta" ∷ own_meta_frag γ key uid (Some kmeta) ∗
      "Hchildren" ∷ own_weak_children_frag γ parent_key parent_uid children
  }}}
    l @ (ptrT.id apimodel.State.id) @ "delete" #key #null #null
  {{{ (kmeta': PureObjectMeta.t), RET #interface.nil;
      (( ⌜ deleting kmeta kmeta' ⌝ ∗
          own_meta_frag γ key uid (Some kmeta') ∗
          own_weak_children_frag γ parent_key parent_uid children
        ) ∨
        own_weak_children_frag γ parent_key parent_uid (children ∖ {[key]})
      )
  }}}.
Proof. Admitted.

Lemma wp_State__delete_uid γ l key uid_ptr uid current_uid kmeta parent_key parent_uid children:
  {{{ is_pkg_init apimodel ∗
      "#Hisk" ∷ is_kubernetes γ l ∗
      "%His_child" ∷ ⌜ key ∈ children ⌝ ∗
      "Huid_ptr" ∷ uid_ptr ↦ uid ∗
      "Hmeta" ∷ own_meta_frag γ key current_uid (Some kmeta) ∗
      "Hchildren" ∷ own_weak_children_frag γ parent_key parent_uid children
  }}}
    l @ (ptrT.id apimodel.State.id) @ "delete" #key #uid_ptr #null
  {{{ (err: error.t) (kmeta': PureObjectMeta.t), RET #err;
      ( ⌜ uid = current_uid ⌝ ∗
        ⌜ err = interface.nil ⌝ ∗
        ((⌜ deleting kmeta kmeta' ⌝ ∗
            own_meta_frag γ key current_uid (Some kmeta') ∗
            own_weak_children_frag γ parent_key parent_uid children
          ) ∨
          own_weak_children_frag γ parent_key parent_uid (children ∖ {[key]})
        )
      ) ∨
      ( ⌜ uid ≠ current_uid ⌝ ∗
        ⌜ err ≠ interface.nil ⌝
      )
  }}}.
Proof. Admitted.

Lemma wp_State__delete_rv γ l key uid_ptr uid rv_ptr rv prev_kobj current_uid kmeta parent_key parent_uid children:
  {{{ is_pkg_init apimodel ∗
      "#Hisk" ∷ is_kubernetes γ l ∗
      "#Hsnapshot" ∷ own_snapshot_ro_frag γ key uid rv prev_kobj ∗
      "%His_child" ∷ ⌜ key ∈ children ⌝ ∗
      "Huid_ptr" ∷ uid_ptr ↦ uid ∗
      "Hrv_ptr" ∷ rv_ptr ↦ rv ∗
      "Hmeta" ∷ own_meta_frag γ key current_uid (Some kmeta) ∗
      "Hchildren" ∷ own_weak_children_frag γ parent_key parent_uid children
  }}}
    l @ (ptrT.id apimodel.State.id) @ "delete" #key #uid_ptr #rv_ptr
  {{{ (err: error.t) (kmeta': PureObjectMeta.t), RET #err;
      ( ⌜ uid = current_uid ⌝ ∗
        ⌜ rv = kmeta.(PureObjectMeta.ResourceVersion') ⌝ ∗
        ⌜ err = interface.nil ⌝ ∗
        ((⌜ deleting kmeta kmeta' ⌝ ∗
            own_meta_frag γ key current_uid (Some kmeta') ∗
            own_weak_children_frag γ parent_key parent_uid children
          ) ∨
          own_weak_children_frag γ parent_key parent_uid (children ∖ {[key]})
        )
      ) ∨
      ( (⌜ uid ≠ current_uid ⌝ ∨ ⌜ rv ≠ kmeta.(PureObjectMeta.ResourceVersion') ⌝) ∗
        ⌜ err ≠ interface.nil ⌝
      )
  }}}.
Proof. Admitted.

(* update satisfies Kubernetes update invariant *)
Axiom valid_update: go_string → PureKObject.t → PureKObject.t → Prop.

(* update from the old meta to the new meta doesn't modify owner references and doesn't trigger deletion *)
Axiom simple_update: PureObjectMeta.t → PureObjectMeta.t → Prop.

Lemma wp_State__update γ l kind namespace i key uid rv prev_kobj kobj kmeta kspec:
  {{{ is_pkg_init apimodel ∗
      "#Hisk" ∷ is_kubernetes γ l ∗
      "#Hsnapshot" ∷ own_snapshot_ro_frag γ key uid rv prev_kobj ∗
      "%Hkind_eq" ∷ ⌜ kind = PureKObject.kind kobj ⌝ ∗
      "%Hkey_eq" ∷ ⌜ key = PureKObject.key kobj ⌝ ∗
      "%Hv" ∷ ⌜ valid kobj ⌝ ∗
      "%Hvu" ∷ ⌜ valid_update namespace prev_kobj kobj ⌝ ∗
      "%Hsu" ∷ ⌜ simple_update (PureKObject.objectmeta prev_kobj) (PureKObject.objectmeta kobj) ⌝ ∗
      "Hdeepown_i" ∷ PureKObject.deepown_i i kobj 1 ∗
      "Hmeta" ∷ own_meta_frag γ key uid (Some kmeta) ∗
      "Hspec" ∷ own_weak_spec_frag γ key uid kspec
  }}}
    l @ (ptrT.id apimodel.State.id) @ "update" #kind #namespace #i
  {{{ i' (err: error.t) kobj', RET (#i', #err);
      ( ⌜ kmeta.(PureObjectMeta.ResourceVersion') = rv ⌝ ∗
        ⌜ err = interface.nil ⌝ ∗
        ⌜ valid kobj' ⌝ ∗
        ⌜ PureObjectMeta.updated kmeta (PureKObject.objectmeta kobj) (PureKObject.objectmeta kobj') ⌝ ∗
        ⌜ PureObjectSpec.updated kspec (PureKObject.spec kobj) (PureKObject.spec kobj') ⌝ ∗
        PureKObject.deepown_i i' kobj' 1 ∗
        own_meta_frag γ key uid (Some (PureKObject.objectmeta kobj')) ∗
        own_weak_spec_frag γ key uid (PureKObject.spec kobj') ∗
        own_snapshot_ro_frag_of γ kobj'
      ) ∨ (
        ⌜ kmeta.(PureObjectMeta.ResourceVersion') ≠ rv ⌝ ∗
        ⌜ err ≠ interface.nil ⌝ ∗
        own_meta_frag γ key uid (Some kmeta) ∗
        own_weak_spec_frag γ key uid kspec
      )
  }}}.
Proof. Admitted.

End spec.
