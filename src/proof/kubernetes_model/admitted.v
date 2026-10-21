From New.proof Require Import prelude empty_ffi.
From New.proof.kubernetes_model Require Export common.
From New.proof.k8s_io.apiserver.pkg.registry Require Export rest.

(** The validation/defaulting contracts assume that validation of Go fields
    omitted from the Kubernetes view types succeeds. These contracts do not
    require callers to own or reason about those unmodeled fields.

    TODO: [KObjectV.deepown_l] must existentially own all reachable Go fields,
    including unmodeled fields, so helper calls cannot mutate memory outside
    their separation-logic footprint. *)

Section proof.
Context `{hG: !heapGS Σ} `{!ffi_semantics _ _}.
Context {sem : go.Semantics} {package_sem : apimodel.Assumptions}.
Local Set Default Proof Using "All".


(* deepCopy only reads its argument, so any fraction of it suffices. *)
Lemma wp_deepCopy i obj dq:
  {{{ is_pkg_init apimodel ∗
      KObjectV.deepown_i i obj dq
  }}}
    @! apimodel.deepCopy #(interface.ok i)
  {{{ i', RET #(interface.ok i');
      KObjectV.deepown_i i' obj 1 ∗
      KObjectV.deepown_i i obj dq
  }}}.
Proof.
Admitted.

Lemma wp_storageObjectDeepEqual i1 i2 obj1 obj2 dq1 dq2 :
  {{{ is_pkg_init apimodel ∗
      KObjectV.deepown_i i1 obj1 dq1 ∗
      KObjectV.deepown_i i2 obj2 dq2
  }}}
    @! apimodel.storageObjectDeepEqual #(interface.ok i1) #(interface.ok i2)
  {{{ v, RET #v;
      KObjectV.deepown_i i1 obj1 dq1 ∗
      KObjectV.deepown_i i2 obj2 dq2 ∗
      ⌜ v = true ↔ storage_object_normalize obj1 = storage_object_normalize obj2 ⌝
  }}}.
Proof.
Admitted.

Lemma wp_State__generateNewRVAndUpdate l used_rv_l (used_rv : gmap go_string unit) :
  {{{ is_pkg_init apimodel ∗
      l.[(apimodel.State.t), "usedRV"] ↦ used_rv_l ∗
      used_rv_l ↦$ used_rv
  }}}
    l @! (go.PointerType apimodel.State) @! "generateNewRVAndUpdate" #()
  {{{ rv, RET #rv;
      ⌜ used_rv !! rv = None ⌝ ∗
      ⌜ valid_resource_version rv ⌝ ∗
      l.[(apimodel.State.t), "usedRV"] ↦ used_rv_l ∗
      used_rv_l ↦$ <[rv:=()]> used_rv
  }}}.
Proof.
Admitted.

Lemma wp_validateObjectMeta i (kind : go_string) l o m dq :
  {{{ is_pkg_init apimodel ∗
      ⌜ KObjectV.valid_interface i l o ⌝ ∗
      ObjectMetaV.deepown_l (KObjectV.objectmeta_ptr l o) m dq ∗
      ⌜ ObjectMetaV.valid kind m ⌝
  }}}
    @! apimodel.validateObjectMeta #(interface.ok i) #kind
  {{{ RET #interface.nil;
      ObjectMetaV.deepown_l (KObjectV.objectmeta_ptr l o) m dq
  }}}.
Proof.
Admitted.

Lemma wp_parseResourceVersion rv :
  {{{ is_pkg_init apimodel ∗
      ⌜ valid_resource_version rv ⌝
  }}}
    @! apimodel.parseResourceVersion #rv
  {{{ (ret : w64), RET (#ret, #interface.nil);
    True
  }}}.
Proof. Admitted.

(* A variant of [wp_parseResourceVersion] for any resource version:
   [strconv.ParseUint] is untranslated, so parsing may fail. *)
Lemma wp_parseResourceVersion_general (rv : go_string) :
  {{{ is_pkg_init apimodel }}}
    @! apimodel.parseResourceVersion #rv
  {{{ (ret : w64) (err : interface.t), RET (#ret, #err);
    True
  }}}.
Proof. Admitted.

(* The error reports the parse error's message, which calls [Error] on an
   error value of an untranslated type. *)
Lemma wp_malformedUpdateResourceVersionError (err : interface.t) :
  {{{ is_pkg_init apimodel ∗
      ⌜ err ≠ interface.nil ⌝
  }}}
    @! apimodel.malformedUpdateResourceVersionError #err
  {{{ (err' : interface.t), RET #err';
    ⌜ err' ≠ interface.nil ⌝
  }}}.
Proof. Admitted.

(* delete_graceful and delete_pending_graceful abstract the result of checkGracefulDelete *)
Axiom delete_graceful : KObjectV.t -> DeleteOptionsV.t -> bool.
Axiom delete_pending_graceful : KObjectV.t -> bool.
Axiom delete_new_grace_period_seconds : KObjectV.t -> DeleteOptionsV.t -> option w64.

Lemma wp_checkGracefulDelete i l o options_l options :
  {{{ is_pkg_init apimodel ∗
      "%Hvalid_i" ∷ ⌜ KObjectV.valid_interface i l o ⌝ ∗
      "Hdeepown_l" ∷ KObjectV.deepown_l l o 1 ∗
      "Hdeepown_options_l" ∷ DeleteOptionsV.deepown_l options_l options 1
  }}}
    @! apimodel.checkGracefulDelete #(interface.ok i) #options_l
  {{{ graceful pendingGraceful options',
      RET (#graceful, #pendingGraceful, #interface.nil);
      KObjectV.deepown_l l o 1 ∗
      DeleteOptionsV.deepown_l options_l options' 1 ∗
      ⌜ pendingGraceful = true → (KObjectV.objectmeta o).(ObjectMetaV.DeletionTimestamp') ≠ None ⌝ ∗
      ⌜ graceful = delete_graceful o options ⌝ ∗
      ⌜ pendingGraceful = delete_pending_graceful o ⌝ ∗
      ⌜ options' = (options <| DeleteOptionsV.GracePeriodSeconds' := delete_new_grace_period_seconds o options |>) ⌝
  }}}.
Proof.
Admitted.

Context `{!kubernetesModelG Σ}.

Lemma wp_State__generateNewUIDAndUpdate l used_uid_l (used_uid : gmap types.UID.t unit) :
  {{{ is_pkg_init apimodel ∗
      l.[(apimodel.State.t), "usedUID"] ↦ used_uid_l ∗
      used_uid_l ↦$ used_uid
  }}}
    l @! (go.PointerType apimodel.State) @! "generateNewUIDAndUpdate" #()
  {{{ uid, RET #uid;
      ⌜ used_uid !! uid = None ⌝ ∗
      ⌜ valid_uid uid ⌝ ∗
      l.[(apimodel.State.t), "usedUID"] ↦ used_uid_l ∗
      used_uid_l ↦$ <[uid:=()]> used_uid
  }}}.
Proof.
Admitted.

Lemma wp_State__generateNewName l m_ptr kind namespace generate_name (phys_state : gmap KKey.t interface.t):
  {{{ is_pkg_init apimodel ∗
      ⌜ valid_generate_name kind generate_name ⌝ ∗
      ⌜ length generate_name ≤ 58 ⌝ ∗
      l.[(apimodel.State.t), "m"] ↦ m_ptr ∗
      m_ptr ↦$ phys_state
  }}}
    l @! (go.PointerType apimodel.State) @! "generateNewName" #kind #namespace #generate_name
  {{{ (new_name: go_string), RET #new_name;
      ⌜ new_name ≠ ""%go ⌝ ∗
      ⌜ valid_name kind new_name ⌝ ∗
      ⌜ phys_state !! {| KKey.Kind' := kind; KKey.Namespace' := namespace; KKey.Name' := new_name;|} = None ⌝ ∗
      ⌜ ∀ kind namespace,
          ¬ reserved_key_pred {| KKey.Kind' := kind;
                             KKey.Namespace' := namespace;
                             KKey.Name' := new_name |} ⌝ ∗
      l.[(apimodel.State.t), "m"] ↦ m_ptr ∗
      m_ptr ↦$ phys_state
  }}}.
Proof.
Admitted.

(** This is the single trusted semantic contract for a successful helper
    call. *)
Definition create_helper_result
    (namespace : go_string) (input helper_input helper_result : KObjectV.t) : Prop :=
  KObjectV.created namespace input helper_result ∧
  valid_without_resource_version helper_result ∧
  (KObjectV.objectmeta helper_result).(ObjectMetaV.Name') =
    (KObjectV.objectmeta helper_input).(ObjectMetaV.Name') ∧
  (KObjectV.objectmeta helper_result).(ObjectMetaV.UID') =
    (KObjectV.objectmeta helper_input).(ObjectMetaV.UID').

(** Strong contract for a create satisfying the modeled sufficient validity
    condition. [input] is the submitted create object and [helper_input] is the
    prepared private copy passed to the helper. Under the modeling assumption
    above, validation of unmodeled fields adds no precondition. *)
Lemma wp_applyValidationAndDefaulting_ok
    i l helper_input (request_kind namespace name : go_string) input :
  {{{ is_pkg_init apimodel ∗
      ⌜ KObjectV.valid_interface i l helper_input ⌝ ∗
      ⌜ KObjectV.valid_create request_kind namespace input ⌝ ∗
      ⌜ create_prepared_for_helper namespace name input helper_input ⌝ ∗
      KObjectV.deepown_l l helper_input 1
  }}}
    @! apimodel.applyValidationAndDefaulting #(interface.ok i) #name
  {{{ helper_result, RET #interface.nil;
      KObjectV.deepown_l l helper_result 1 ∗
      ⌜ KObjectV.valid_interface i l helper_result ⌝ ∗
      ⌜ create_helper_result namespace input helper_input helper_result ⌝
  }}}.
Proof. Admitted.

(** General contract used when the helper may reject an update. On failure the
    new object may already have been mutated, so the postcondition returns an
    unconstrained view of that same allocation instead of the original view. *)
Lemma wp_applyValidationAndDefaultingOnUpdate_general
    new_i new_l new_obj old_i old_l old_obj dq (namespace : go_string) :
  {{{ is_pkg_init apimodel ∗
      ⌜ KObjectV.valid_interface new_i new_l new_obj ⌝ ∗
      ⌜ KObjectV.valid_interface old_i old_l old_obj ⌝ ∗
      ⌜ KObjectV.same_kind old_obj new_obj ⌝ ∗
      KObjectV.deepown_l new_l new_obj 1 ∗
      KObjectV.deepown_l old_l old_obj dq
  }}}
    @! apimodel.applyValidationAndDefaultingOnUpdate #(interface.ok new_i) #(interface.ok old_i) #namespace
  {{{ (err : interface.t), RET #err;
      (⌜ err = interface.nil ⌝ ∗
        ∃ updated_obj,
          KObjectV.deepown_l new_l updated_obj 1 ∗
          KObjectV.deepown_l old_l old_obj dq ∗
          ⌜ KObjectV.valid_interface new_i new_l updated_obj ⌝ ∗
          ⌜ applyValidationAndDefaultingOnUpdate_updated namespace old_obj new_obj updated_obj ⌝) ∨
      (⌜ err ≠ interface.nil ⌝ ∗
        ⌜ ¬ conflict_error err ⌝ ∗
        ∃ failed_obj,
          KObjectV.deepown_l new_l failed_obj 1 ∗
          KObjectV.deepown_l old_l old_obj dq ∗
          ⌜ KObjectV.valid_interface new_i new_l failed_obj ⌝)
  }}}.
Proof. Admitted.

(** Strong contract for an update satisfying the modeled sufficient validity
    condition. [input] is the submitted update object and [new_obj] is the
    prepared object passed to the helper. Under the modeling assumption above,
    validation of unmodeled fields adds no precondition. The old object is
    read-only; the helper mutates the new object and returns its resulting
    view. *)
Lemma wp_applyValidationAndDefaultingOnUpdate_ok
    new_i new_l new_obj old_i old_l old_obj dq (namespace : go_string) input :
  {{{ is_pkg_init apimodel ∗
      ⌜ KObjectV.valid_interface new_i new_l new_obj ⌝ ∗
      ⌜ KObjectV.valid_interface old_i old_l old_obj ⌝ ∗
      ⌜ KObjectV.valid old_obj ⌝ ∗
      ⌜ KObjectV.valid_update (KObjectV.kind input) namespace
          (KObjectV.objectmeta old_obj) (KObjectV.spec old_obj) input ⌝ ∗
      ⌜ update_prepared_for_helper namespace old_obj input new_obj ⌝ ∗
      KObjectV.deepown_l new_l new_obj 1 ∗
      KObjectV.deepown_l old_l old_obj dq
  }}}
    @! apimodel.applyValidationAndDefaultingOnUpdate #(interface.ok new_i) #(interface.ok old_i) #namespace
  {{{ updated_obj, RET #interface.nil;
      KObjectV.deepown_l new_l updated_obj 1 ∗
      KObjectV.deepown_l old_l old_obj dq ∗
      ⌜ KObjectV.valid_interface new_i new_l updated_obj ⌝ ∗
      ⌜ applyValidationAndDefaultingOnUpdate_updated namespace old_obj new_obj updated_obj ⌝
  }}}.
Proof. Admitted.

(** General contract used when the status-update helper may reject an update.
    On failure the new object may already have been mutated, so the
    postcondition returns an unconstrained view of that same allocation instead
    of the original view. *)
Lemma wp_applyValidationAndDefaultingOnStatusUpdate_general
    new_i new_l new_obj old_i old_l old_obj dq (namespace : go_string) :
  {{{ is_pkg_init apimodel ∗
      ⌜ KObjectV.valid_interface new_i new_l new_obj ⌝ ∗
      ⌜ KObjectV.valid_interface old_i old_l old_obj ⌝ ∗
      ⌜ KObjectV.same_kind old_obj new_obj ⌝ ∗
      KObjectV.deepown_l new_l new_obj 1 ∗
      KObjectV.deepown_l old_l old_obj dq
  }}}
    @! apimodel.applyValidationAndDefaultingOnStatusUpdate
      #(interface.ok new_i) #(interface.ok old_i) #namespace
  {{{ (err : interface.t), RET #err;
      (⌜ err = interface.nil ⌝ ∗
        ∃ updated_obj,
          KObjectV.deepown_l new_l updated_obj 1 ∗
          KObjectV.deepown_l old_l old_obj dq ∗
          ⌜ KObjectV.valid_interface new_i new_l updated_obj ⌝ ∗
          ⌜ applyValidationAndDefaultingOnStatusUpdate_updated
              namespace old_obj new_obj updated_obj ⌝) ∨
      (⌜ err ≠ interface.nil ⌝ ∗
        ⌜ ¬ conflict_error err ⌝ ∗
        ∃ failed_obj,
          KObjectV.deepown_l new_l failed_obj 1 ∗
          KObjectV.deepown_l old_l old_obj dq ∗
          ⌜ KObjectV.valid_interface new_i new_l failed_obj ⌝)
  }}}.
Proof. Admitted.

(** Trusted: the metadata half of a successful status-update helper call, used
    only by [wp_State__update_status_same_meta_au] and
    [wp_State__update_status_same_meta_general_au]. For a request whose metadata
    is a simple update of [old], the stored object keeps the request's kind,
    TypeMeta and metadata (except the resource version, so the generation too)
    and [old]'s spec. This holds even when the request status is not known to be
    valid: rest.BeforeUpdate only copies generation, UID, timestamps, and grace
    period from [old] (which [valid_simple_update] makes agree with the input),
    and every status strategy's PrepareForUpdate resets the spec to [old]'s.
    kubernetes/staging/src/k8s.io/apiserver/pkg/registry/rest/update.go *)
Definition applyValidationAndDefaultingOnStatusUpdate_meta_preserved
    (namespace : go_string) (old helper_input helper_result : KObjectV.t) : Prop :=
  ∀ input stored,
    update_prepared_for_helper namespace old input helper_input →
    (KObjectV.objectmeta input).(ObjectMetaV.Namespace') = namespace →
    ObjectMetaV.valid_simple_update (KObjectV.objectmeta old) (KObjectV.objectmeta input) →
    update_objects_equiv_except_resource_version helper_result stored →
    KObjectV.same_kind input stored ∧
    KObjectV.typemeta stored = KObjectV.typemeta input ∧
    ObjectMetaV.equiv_except_resource_version (KObjectV.objectmeta stored) (KObjectV.objectmeta input) ∧
    KObjectV.spec stored = KObjectV.spec old.

(** Trusted success contract including metadata preservation. The ordinary
    success specification is derived from this contract in [common_update.v]. *)
Lemma wp_applyValidationAndDefaultingOnStatusUpdate_ok_same_meta
    new_i new_l new_obj old_i old_l old_obj dq
    (request_kind namespace : go_string) input :
  {{{ is_pkg_init apimodel ∗
      ⌜ KObjectV.valid_interface new_i new_l new_obj ⌝ ∗
      ⌜ KObjectV.valid_interface old_i old_l old_obj ⌝ ∗
      ⌜ KObjectV.valid old_obj ⌝ ∗
      ⌜ KObjectV.valid_status_update request_kind namespace
          (KObjectV.objectmeta old_obj) (KObjectV.status old_obj) input ⌝ ∗
      ⌜ update_prepared_for_helper namespace old_obj input new_obj ⌝ ∗
      KObjectV.deepown_l new_l new_obj 1 ∗
      KObjectV.deepown_l old_l old_obj dq
  }}}
    @! apimodel.applyValidationAndDefaultingOnStatusUpdate
      #(interface.ok new_i) #(interface.ok old_i) #namespace
  {{{ updated_obj, RET #interface.nil;
      KObjectV.deepown_l new_l updated_obj 1 ∗
      KObjectV.deepown_l old_l old_obj dq ∗
      ⌜ KObjectV.valid_interface new_i new_l updated_obj ⌝ ∗
      ⌜ applyValidationAndDefaultingOnStatusUpdate_updated
          namespace old_obj new_obj updated_obj ⌝ ∗
      ⌜ applyValidationAndDefaultingOnStatusUpdate_meta_preserved
          namespace old_obj new_obj updated_obj ⌝
  }}}.
Proof. Admitted.

(** Trusted: [wp_applyValidationAndDefaultingOnStatusUpdate_general] together
    with [applyValidationAndDefaultingOnStatusUpdate_meta_preserved] on success.
    The request status need not be valid, so the helper may reject it. *)
Lemma wp_applyValidationAndDefaultingOnStatusUpdate_general_same_meta
    new_i new_l new_obj old_i old_l old_obj dq (namespace : go_string) :
  {{{ is_pkg_init apimodel ∗
      ⌜ KObjectV.valid_interface new_i new_l new_obj ⌝ ∗
      ⌜ KObjectV.valid_interface old_i old_l old_obj ⌝ ∗
      ⌜ KObjectV.same_kind old_obj new_obj ⌝ ∗
      KObjectV.deepown_l new_l new_obj 1 ∗
      KObjectV.deepown_l old_l old_obj dq
  }}}
    @! apimodel.applyValidationAndDefaultingOnStatusUpdate
      #(interface.ok new_i) #(interface.ok old_i) #namespace
  {{{ (err : interface.t), RET #err;
      (⌜ err = interface.nil ⌝ ∗
        ∃ updated_obj,
          KObjectV.deepown_l new_l updated_obj 1 ∗
          KObjectV.deepown_l old_l old_obj dq ∗
          ⌜ KObjectV.valid_interface new_i new_l updated_obj ⌝ ∗
          ⌜ applyValidationAndDefaultingOnStatusUpdate_updated
              namespace old_obj new_obj updated_obj ⌝ ∗
          ⌜ applyValidationAndDefaultingOnStatusUpdate_meta_preserved
              namespace old_obj new_obj updated_obj ⌝) ∨
      (⌜ err ≠ interface.nil ⌝ ∗
        ⌜ ¬ conflict_error err ⌝ ∗
        ∃ failed_obj,
          KObjectV.deepown_l new_l failed_obj 1 ∗
          KObjectV.deepown_l old_l old_obj dq ∗
          ⌜ KObjectV.valid_interface new_i new_l failed_obj ⌝)
  }}}.
Proof. Admitted.

End proof.
