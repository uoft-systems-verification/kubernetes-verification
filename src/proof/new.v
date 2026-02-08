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

Axiom own_meta_frag: gname → KKey.t → types.UID.t → option ObjectMetaV.t → iProp Σ.

Axiom own_weak_spec_frag: gname → KKey.t → types.UID.t → ObjectSpecV.t → iProp Σ.

Axiom own_weak_status_frag: gname → KKey.t → types.UID.t → ObjectStatusV.t → iProp Σ.

Axiom own_weak_children_frag: gname → KKey.t → types.UID.t → gset KKey.t → iProp Σ.

Axiom own_fresh_key_frag: gname → KKey.t → iProp Σ.

(* A snapshot of the object given the key, uid, and rv. It's persistent. *)
Axiom own_snapshot_ro_frag: gname → KKey.t → types.UID.t → go_string → KObjectV.t → iProp Σ.

Definition own_snapshot_ro_frag_of γ kobj: iProp Σ :=
  own_snapshot_ro_frag γ
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
      ( ⌜ err = interface.nil ⌝ ∗
        ⌜ KObjectV.valid kobj ⌝ ∗
        ⌜ key = KObjectV.key kobj ⌝ ∗
        KObjectV.deepown_i i kobj 1 ∗
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
          ⌜ KObjectV.valid kobj ⌝ ∗
          ⌜ key = KObjectV.key kobj ⌝ ∗
          ⌜ uid ≠ (KObjectV.objectmeta kobj).(ObjectMetaV.UID') ⌝ ∗
          KObjectV.deepown_i i kobj 1 ∗
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
      "%Huid" ∷ ⌜ uid = kmeta.(ObjectMetaV.UID') ⌝ ∗
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
      ⌜ KObjectV.valid kobj ⌝ ∗
      ⌜ key = KObjectV.key kobj ⌝ ∗
      ⌜ kmeta = KObjectV.objectmeta kobj ⌝ ∗
      KObjectV.deepown_i i kobj 1 ∗
      own_meta_frag γ key uid (Some kmeta) ∗
      (match kspec_o with
      | Some kspec => own_weak_spec_frag γ key uid kspec ∗ ⌜ kspec = KObjectV.spec kobj ⌝
      | None => True
      end) ∗
      (match kstatus_o with
      | Some kstatus => own_weak_status_frag γ key uid kstatus ∗ ⌜ kstatus = KObjectV.status kobj ⌝
      | None => True
      end) ∗
      own_snapshot_ro_frag_of γ kobj
  }}}.
Proof. Admitted.

Lemma wp_State__create γ l kind namespace i kobj key parent_key parent_uid parent_meta children:
  {{{ is_pkg_init apimodel ∗
      "#Hisk" ∷ is_kubernetes γ l ∗
      "%Hkind_eq" ∷ ⌜ kind = KObjectV.kind kobj ⌝ ∗
      "%Hnamespace_eq" ∷ ⌜ namespace = parent_key.(KKey.Namespace') ⌝ ∗
      "%Hwf" ∷ ⌜ KObjectV.valid_create namespace kobj ⌝ ∗
      "%Hparent_of" ∷ ⌜ obj_has_controller_parent_of kobj parent_key.(KKey.Kind') parent_key.(KKey.Name') parent_uid ⌝ ∗
      "%Hkey_eq" ∷ ⌜ key = (KObjectV.key kobj) ⌝ ∗
      "Hdeepown_i" ∷ KObjectV.deepown_i i kobj 1 ∗
      "Hfresh_key" ∷ own_fresh_key_frag γ key ∗
      "Hparent_meta" ∷ own_meta_frag γ parent_key parent_uid (Some parent_meta) ∗
      "Hchildren" ∷ own_weak_children_frag γ parent_key parent_uid children
  }}}
    l @ (ptrT.id apimodel.State.id) @ "create" #kind #namespace #i
  {{{ i' kobj' uid, RET (#i', #interface.nil);
      ⌜ ObjectMetaV.created namespace (KObjectV.objectmeta kobj) (KObjectV.objectmeta kobj') ⌝ ∗
      ⌜ ObjectSpecV.created (KObjectV.spec kobj) (KObjectV.spec kobj') ⌝ ∗
      ⌜ ObjectStatusV.created (KObjectV.status kobj) (KObjectV.status kobj') ⌝ ∗
      ⌜ KObjectV.valid kobj' ⌝ ∗
      ⌜ key = (KObjectV.key kobj') ⌝ ∗
      ⌜ key ∉ children ⌝ ∗
      ⌜ uid = (KObjectV.objectmeta kobj').(ObjectMetaV.UID') ⌝ ∗
      KObjectV.deepown_i i' kobj' 1 ∗
      own_meta_frag γ key uid (Some (KObjectV.objectmeta kobj')) ∗
      own_weak_spec_frag γ key uid (KObjectV.spec kobj') ∗
      own_weak_status_frag γ key uid (KObjectV.status kobj') ∗
      own_meta_frag γ parent_key parent_uid (Some parent_meta) ∗
      own_weak_children_frag γ parent_key parent_uid (children ∪ {[key]}) ∗
      own_weak_children_frag γ key uid ∅ ∗
      own_snapshot_ro_frag_of γ kobj'
  }}}.
Proof. Admitted.

Lemma wp_State__nameless_create γ l kind namespace i kobj parent_key parent_uid parent_meta children:
  {{{ is_pkg_init apimodel ∗
      "#Hisk" ∷ is_kubernetes γ l ∗
      "%Hkind_eq" ∷ ⌜ kind = KObjectV.kind kobj ⌝ ∗
      "%Hnamespace_eq" ∷ ⌜ namespace = parent_key.(KKey.Namespace') ⌝ ∗
      "%Hparent_of" ∷ ⌜ obj_has_controller_parent_of kobj parent_key.(KKey.Kind') parent_key.(KKey.Name') parent_uid ⌝ ∗
      "%Hwf" ∷ ⌜ KObjectV.valid_nameless_create namespace kobj ⌝ ∗
      "Hdeepown_i" ∷ KObjectV.deepown_i i kobj 1 ∗
      "Hparent_meta" ∷ own_meta_frag γ parent_key parent_uid (Some parent_meta) ∗
      "Hchildren" ∷ own_weak_children_frag γ parent_key parent_uid children
  }}}
    l @ (ptrT.id apimodel.State.id) @ "create" #kind #namespace #i
  {{{ i' kobj' key uid, RET (#i', #interface.nil);
      ⌜ KObjectV.valid kobj' ⌝ ∗
      ⌜ ObjectMetaV.nameless_created namespace (KObjectV.objectmeta kobj) (KObjectV.objectmeta kobj') ⌝ ∗
      ⌜ ObjectSpecV.created (KObjectV.spec kobj) (KObjectV.spec kobj') ⌝ ∗
      ⌜ ObjectStatusV.created (KObjectV.status kobj) (KObjectV.status kobj') ⌝ ∗
      ⌜ key = (KObjectV.key kobj') ⌝ ∗
      ⌜ key ∉ children ⌝ ∗
      ⌜ uid = (KObjectV.objectmeta kobj').(ObjectMetaV.UID') ⌝ ∗
      KObjectV.deepown_i i' kobj' 1 ∗
      own_meta_frag γ key uid (Some (KObjectV.objectmeta kobj')) ∗
      own_weak_spec_frag γ key uid (KObjectV.spec kobj') ∗
      own_weak_status_frag γ key uid (KObjectV.status kobj') ∗
      own_meta_frag γ parent_key parent_uid (Some parent_meta) ∗
      own_weak_children_frag γ parent_key parent_uid (children ∪ {[key]}) ∗
      own_weak_children_frag γ key uid ∅ ∗
      own_snapshot_ro_frag_of γ kobj'
  }}}.
Proof. Admitted.

Lemma wp_State__delete γ l key uid kmeta parent_key parent_uid children:
  {{{ is_pkg_init apimodel ∗
      "#Hisk" ∷ is_kubernetes γ l ∗
      "%His_child" ∷ ⌜ key ∈ children ⌝ ∗
      "Hmeta" ∷ own_meta_frag γ key uid (Some kmeta) ∗
      "Hchildren" ∷ own_weak_children_frag γ parent_key parent_uid children
  }}}
    l @ (ptrT.id apimodel.State.id) @ "delete" #key #null #null
  {{{ (kmeta': ObjectMetaV.t), RET #interface.nil;
      (( ⌜ ObjectMetaV.deleting kmeta kmeta' ⌝ ∗
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
  {{{ (err: error.t) (kmeta': ObjectMetaV.t), RET #err;
      ( ⌜ uid = current_uid ⌝ ∗
        ⌜ err = interface.nil ⌝ ∗
        ((⌜ ObjectMetaV.deleting kmeta kmeta' ⌝ ∗
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
  {{{ (err: error.t) (kmeta': ObjectMetaV.t), RET #err;
      ( ⌜ uid = current_uid ⌝ ∗
        ⌜ rv = kmeta.(ObjectMetaV.ResourceVersion') ⌝ ∗
        ⌜ err = interface.nil ⌝ ∗
        ((⌜ ObjectMetaV.deleting kmeta kmeta' ⌝ ∗
            own_meta_frag γ key current_uid (Some kmeta') ∗
            own_weak_children_frag γ parent_key parent_uid children
          ) ∨
          own_weak_children_frag γ parent_key parent_uid (children ∖ {[key]})
        )
      ) ∨
      ( (⌜ uid ≠ current_uid ⌝ ∨ ⌜ rv ≠ kmeta.(ObjectMetaV.ResourceVersion') ⌝) ∗
        ⌜ err ≠ interface.nil ⌝
      )
  }}}.
Proof. Admitted.

Lemma wp_State__update γ l kind namespace i key uid rv prev_kobj kobj kmeta kspec:
  {{{ is_pkg_init apimodel ∗
      "#Hisk" ∷ is_kubernetes γ l ∗
      "#Hsnapshot" ∷ own_snapshot_ro_frag γ key uid rv prev_kobj ∗
      "%Hkind_eq" ∷ ⌜ kind = KObjectV.kind kobj ⌝ ∗
      "%Hkey_eq" ∷ ⌜ key = KObjectV.key kobj ⌝ ∗
      "%Hv" ∷ ⌜ KObjectV.valid kobj ⌝ ∗
      "%Hvu" ∷ ⌜ KObjectV.valid_update namespace prev_kobj kobj ⌝ ∗
      "%Hsu" ∷ ⌜ ObjectMetaV.simple_update (KObjectV.objectmeta prev_kobj) (KObjectV.objectmeta kobj) ⌝ ∗
      "Hdeepown_i" ∷ KObjectV.deepown_i i kobj 1 ∗
      "Hmeta" ∷ own_meta_frag γ key uid (Some kmeta) ∗
      "Hspec" ∷ own_weak_spec_frag γ key uid kspec
  }}}
    l @ (ptrT.id apimodel.State.id) @ "update" #kind #namespace #i
  {{{ i' (err: error.t) kobj', RET (#i', #err);
      ( ⌜ kmeta.(ObjectMetaV.ResourceVersion') = rv ⌝ ∗
        ⌜ err = interface.nil ⌝ ∗
        ⌜ KObjectV.valid kobj' ⌝ ∗
        ⌜ ObjectMetaV.updated kmeta (KObjectV.objectmeta kobj) (KObjectV.objectmeta kobj') ⌝ ∗
        ⌜ ObjectSpecV.updated kspec (KObjectV.spec kobj) (KObjectV.spec kobj') ⌝ ∗
        KObjectV.deepown_i i' kobj' 1 ∗
        own_meta_frag γ key uid (Some (KObjectV.objectmeta kobj')) ∗
        own_weak_spec_frag γ key uid (KObjectV.spec kobj') ∗
        own_snapshot_ro_frag_of γ kobj'
      ) ∨ (
        ⌜ kmeta.(ObjectMetaV.ResourceVersion') ≠ rv ⌝ ∗
        ⌜ err ≠ interface.nil ⌝ ∗
        own_meta_frag γ key uid (Some kmeta) ∗
        own_weak_spec_frag γ key uid kspec
      )
  }}}.
Proof. Admitted.

End spec.
