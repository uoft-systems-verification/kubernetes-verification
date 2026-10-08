From New.proof.controllers.serviceaccount Require Export serviceaccount_init.
From New.proof.kubernetes_model Require Export inv.
From New.proof Require Import empty_ffi.

(** A small, specification-facing view of the Namespace fields read by
    [syncNamespace]. The canonical Kubernetes object view does not yet contain
    Namespace objects; this record makes the intended top-level state explicit
    without exposing the Go heap representation. *)
Record namespace_state := {
  namespace_meta : ObjectMetaV.t;
  namespace_phase : go_string;
}.

Definition namespace_key (namespace : namespace_state) : KKey.t := {|
  KKey.Kind' := "Namespace"%go;
  KKey.Namespace' := ""%go;
  KKey.Name' := namespace.(namespace_meta).(ObjectMetaV.Name');
|}.

Definition service_account_key (meta : ObjectMetaV.t) : KKey.t := {|
  KKey.Kind' := "ServiceAccount"%go;
  KKey.Namespace' := meta.(ObjectMetaV.Namespace');
  KKey.Name' := meta.(ObjectMetaV.Name');
|}.

Definition desired_service_account_key (namespace : namespace_state) : KKey.t := {|
  KKey.Kind' := "ServiceAccount"%go;
  KKey.Namespace' := namespace.(namespace_meta).(ObjectMetaV.Name');
  KKey.Name' := "default"%go;
|}.

Definition desired_service_account_keys (namespace : namespace_state) : list KKey.t :=
  [desired_service_account_key namespace].

Definition namespace_is_active (namespace : namespace_state) : Prop :=
  namespace.(namespace_phase) = "Active"%go.

(** [service_accounts] contains only the live ServiceAccounts managed by this
    controller for [namespace]. Unrelated ServiceAccounts are deliberately not
    part of the snapshot. *)
Definition missing_service_account_keys
    (namespace : namespace_state) (service_accounts : list ObjectMetaV.t) : list KKey.t :=
  filter (λ key, key ∉ (service_account_key <$> service_accounts))
    (desired_service_account_keys namespace).

Definition current_state_matches
    (namespace : namespace_state) (service_accounts : list ObjectMetaV.t) : Prop :=
  ¬ namespace_is_active namespace ∨
  ∀ key, key ∈ desired_service_account_keys namespace →
    key ∈ (service_account_key <$> service_accounts).

Definition match_distance
    (namespace : namespace_state) (service_accounts : list ObjectMetaV.t) : nat :=
  if decide (namespace_is_active namespace) then
    length (missing_service_account_keys namespace service_accounts)
  else
    0%nat.

Definition service_accounts_progress_observed
    (service_accounts service_accounts' : list ObjectMetaV.t) : Prop :=
  list_to_set (C := gset KKey.t) (service_account_key <$> service_accounts) ≠
    list_to_set (C := gset KKey.t) (service_account_key <$> service_accounts').

Definition input_requirement (namespace : namespace_state) : Prop :=
  namespace.(namespace_meta).(ObjectMetaV.Namespace') = ""%go ∧
  valid_namespace namespace.(namespace_meta).(ObjectMetaV.Name') ∧
  Forall reserved_key_pred (desired_service_account_keys namespace).

Section specs.
Context `{hG: !heapGS Σ} `{!ffi_semantics _ _}.
Context {sem : go.Semantics}
  {package_sem : code.controllers.serviceaccount.serviceaccount.Assumptions}.
Collection W := sem + package_sem.
#[local] Instance apimodel_sem : apimodel.Assumptions :=
  code.controllers.serviceaccount.serviceaccount.import_apimodel_Assumption.
#[local] Instance object_meta_v1_sem :
    code.k8s_io.apimachinery.pkg.apis.meta.v1.v1.Assumptions :=
  apimodel.import_apis_meta_v1_Assumption.
#[local] Instance object_apps_v1_sem :
    code.k8s_io.api.apps.v1.v1.Assumptions :=
  apimodel.import_api_apps_v1_Assumption.
#[local] Instance object_core_v1_sem :
    code.k8s_io.api.core.v1.v1.Assumptions :=
  apimodel.import_api_core_v1_Assumption.
Context `{!kubernetesModelG Σ}.
Local Set Default Proof Using "All".

Record all_fractions := {
  namespace_dq : dfrac;
  service_account_dq : dfrac;
}.

Definition mutating_fractions dq : all_fractions :=
  {| namespace_dq := dq; service_account_dq := 1 |}.

Definition stability_fractions dq : all_fractions :=
  {| namespace_dq := dq; service_account_dq := dq |}.

(** This is the intended canonical resource bundle. Before these triples can
    be proved non-vacuously, [KObjectV] must be extended with Namespace and
    ServiceAccount cases, and the Namespace phase must receive a status
    fragment, so that this snapshot and the fragments below are related to
    objects in [kubernetes_inv]. *)
Definition owned_resources γ namespace service_accounts fractions (ready : bool) : iProp Σ :=
  "Hown_namespace_meta_frag" ∷ own_meta_frag γ (namespace_key namespace)
    namespace.(namespace_meta).(ObjectMetaV.UID') fractions.(namespace_dq)
      namespace.(namespace_meta) ∗
  "Hown_service_account_frags" ∷ ([∗ list] service_account ∈ service_accounts,
    own_meta_frag γ (service_account_key service_account)
      service_account.(ObjectMetaV.UID') fractions.(service_account_dq) service_account ∗
    own_occupied_reserved_frag γ fractions.(service_account_dq)
      (service_account_key service_account) service_account.(ObjectMetaV.UID')) ∗
  "Hown_missing_service_account_frags" ∷
    ([∗ list] key ∈ missing_service_account_keys namespace service_accounts,
      if ready then
        own_available_reserved_frag γ fractions.(service_account_dq) key
      else
        own_available_reserved_frag γ fractions.(service_account_dq) key ∨
          ∃ uid, own_deleting_reserved_frag γ fractions.(service_account_dq) key uid)%I ∗
  "%Hservice_accounts_managed" ∷ ⌜ Forall
    (λ service_account,
      service_account_key service_account ∈ desired_service_account_keys namespace)
    service_accounts ⌝ ∗
  "%Hservice_accounts_nodup" ∷ ⌜ NoDup (service_account_key <$> service_accounts) ⌝.

(** When every missing fixed-name key is available, one reconciliation either
    reaches the desired state or performs an observable creation that strictly
    decreases the distance. *)
Definition progress_spec γ l key namespace dq service_accounts : iProp Σ :=
  {{{ is_pkg_init code.controllers.serviceaccount.pkg_id.serviceaccount ∗
      "#Hisk" ∷ is_kubernetes γ l ∗
      "#Hglobal_l" ∷ (global_addr apimodel.ModelState) ↦□ l ∗
      "Hresources" ∷ owned_resources γ namespace service_accounts (mutating_fractions dq) true ∗
      "%Hinput_requirement" ∷ ⌜ input_requirement namespace ⌝ ∗
      "%Hnamespace_active" ∷ ⌜ namespace_is_active namespace ⌝ ∗
      "%Hkey_eq" ∷ ⌜ key = namespace.(namespace_meta).(ObjectMetaV.Name') ⌝
  }}}
    @! serviceaccount.syncNamespace #key
  {{{ (service_accounts' : list ObjectMetaV.t), RET #interface.nil;
      owned_resources γ namespace service_accounts' (mutating_fractions dq) false ∗
      ⌜ current_state_matches namespace service_accounts' ∨
        (service_accounts_progress_observed service_accounts service_accounts' ∧
          match_distance namespace service_accounts' <
            match_distance namespace service_accounts) ⌝
  }}}.

(** If a missing fixed-name ServiceAccount may still be deleting, the
    controller need not make immediate progress, but it must not increase the
    distance from the desired state. *)
Definition preservation_spec γ l key namespace dq service_accounts : iProp Σ :=
  {{{ is_pkg_init code.controllers.serviceaccount.pkg_id.serviceaccount ∗
      "#Hisk" ∷ is_kubernetes γ l ∗
      "#Hglobal_l" ∷ (global_addr apimodel.ModelState) ↦□ l ∗
      "Hresources" ∷ owned_resources γ namespace service_accounts (mutating_fractions dq) false ∗
      "%Hinput_requirement" ∷ ⌜ input_requirement namespace ⌝ ∗
      "%Hnamespace_active" ∷ ⌜ namespace_is_active namespace ⌝ ∗
      "%Hkey_eq" ∷ ⌜ key = namespace.(namespace_meta).(ObjectMetaV.Name') ⌝
  }}}
    @! serviceaccount.syncNamespace #key
  {{{ (service_accounts' : list ObjectMetaV.t), RET #interface.nil;
      owned_resources γ namespace service_accounts' (mutating_fractions dq) false ∗
      ⌜ match_distance namespace service_accounts' ≤
        match_distance namespace service_accounts ⌝
  }}}.

(** Once the state matches (because the Namespace is inactive or because the
    desired ServiceAccount exists), reconciliation does not modify the
    Namespace or any managed ServiceAccount. Fractional ownership makes that
    non-mutation guarantee part of the contract. *)
Definition stability_spec γ l key namespace dq service_accounts : iProp Σ :=
  {{{ is_pkg_init code.controllers.serviceaccount.pkg_id.serviceaccount ∗
      "#Hisk" ∷ is_kubernetes γ l ∗
      "#Hglobal_l" ∷ (global_addr apimodel.ModelState) ↦□ l ∗
      "Hresources" ∷ owned_resources γ namespace service_accounts (stability_fractions dq) true ∗
      "%Hkey_eq" ∷ ⌜ key = namespace.(namespace_meta).(ObjectMetaV.Name') ⌝ ∗
      "%Hmatch" ∷ ⌜ current_state_matches namespace service_accounts ⌝
  }}}
    @! serviceaccount.syncNamespace #key
  {{{ (err : interface.t), RET #err;
      owned_resources γ namespace service_accounts (stability_fractions dq) true
  }}}.

End specs.
