Require Export New.proof.sync.
From New.proof.kubernetes_model Require Export apimodel_init.
From New.proof.k8s_io.apimachinery.pkg.api Require Export meta.
From New.proof.k8s_io.apimachinery.pkg.apis.meta Require Export v1.
From New.proof Require Import prelude empty_ffi.
From New.proof Require Export pure_objects string.
From New.proof.big_op Require Export big_sepL big_sepM.
From New.proof.algebra Require Export kview cview tombstone reserved_keys.

Class kubernetesModelG Σ := {
  #[global] kubernetes_model_kviewG :: kviewG Σ;
  #[global] kubernetes_model_cviewG :: cviewG Σ;
  #[global] kubernetes_model_tombstoneG :: tombstoneG Σ;
  #[global] kubernetes_model_reserved_keysG :: reserved_keysG Σ;
}.

Section spec.
Context `{hG: !heapGS Σ} `{!ffi_semantics _ _}.
Context {sem : go.Semantics} {package_sem : apimodel.Assumptions}.
Context `{!kubernetesModelG Σ}.
Local Set Default Proof Using "All".

Record KubernetesGname := mk_γk {
  γ_state : gname;
  γ_children : gname;
  γ_tombstone : gname;
  γ_reserved_keys : gname;
}.

Definition own_kview_auth γ state used_uid : iProp Σ :=
  kview.own_auth γ.(γ_state) state used_uid.

Definition own_meta_frag γ k uid dq m : iProp Σ :=
  kview.own_meta_frag γ.(γ_state) k uid dq m.

Definition own_spec_frag γ k uid dq sp : iProp Σ :=
  kview.own_spec_frag γ.(γ_state) k uid dq sp.

Definition own_status_frag γ k uid dq st : iProp Σ :=
  kview.own_status_frag γ.(γ_state) k uid dq st.

Definition own_children_auth γ state used_reference : iProp Σ :=
  cview.own_auth γ.(γ_children) state used_reference.

Definition own_children_frag γ key uid dq keys : iProp Σ :=
  cview.own_frag γ.(γ_children) key uid dq keys.

Definition own_tombstone_auth γ tombed_uid : iProp Σ :=
  tombstone.own_auth γ.(γ_tombstone) tombed_uid.

Definition own_tombstone_frag γ tombed_uid : iProp Σ :=
  tombstone.own_frag γ.(γ_tombstone) tombed_uid.

Definition own_reserved_auth γ reserved_key_set : iProp Σ :=
  reserved_keys.own_auth γ.(γ_reserved_keys) reserved_key_set.

Definition own_reserved_frag γ key : iProp Σ :=
  reserved_keys.own_frag γ.(γ_reserved_keys) key.

Definition kubernetes_inv γ l : iProp Σ :=
  ∃ (phys_state_l: loc) (phys_used_uid_l: loc) (phys_used_rv_l: loc)
    (phys_state: gmap KKey.t interface.t) (phys_used_uid : gmap types.UID.t unit) (phys_used_rv : gmap go_string unit)
    (abs_state: gmap KKey.t KObjectV.t) (used_uid: gset types.UID.t) (tombed_uid: gset types.UID.t)
    (used_reference: gset (KKey.t * types.UID.t)) (reserved_keys: gset KKey.t),
    "Hstate_m_addr" ∷ l.[(apimodel.State.t), "m"] ↦ phys_state_l ∗
    "Hstate_used_uid_addr" ∷ l.[(apimodel.State.t), "usedUID"] ↦ phys_used_uid_l ∗
    "Hstate_used_rv_addr" ∷ l.[(apimodel.State.t), "usedRV"] ↦ phys_used_rv_l ∗
    "Hown_phys" ∷ phys_state_l ↦$ phys_state ∗
    "Hown_used_uid" ∷ phys_used_uid_l ↦$ phys_used_uid ∗
    "Hown_used_rv" ∷ phys_used_rv_l ↦$ phys_used_rv ∗
    "Hown_abs" ∷ own_kview_auth γ abs_state used_uid ∗
    "Hown_children" ∷ own_children_auth γ abs_state used_reference ∗
    "Hown_tombstone" ∷ own_tombstone_auth γ tombed_uid ∗
    "Hown_reserved" ∷ own_reserved_auth γ reserved_keys ∗
    "Hphys_abs_rep" ∷ ([∗ map] i; obj ∈ phys_state; abs_state,
      match i with
      | interface.ok i_ok => KObjectV.deepown_i i_ok obj 1
      | interface.nil => False%I
      end) ∗
    "%Hused_uid_eq_dom_phys_used_uid" ∷ ⌜ used_uid = dom phys_used_uid ⌝ ∗ 
    "%Hused_uid_eq_set_map_used_reference" ∷ ⌜ used_uid = (set_map (λ v, snd v) used_reference) ⌝ ∗
    "%Htombed_uid_eq_used_uid_sub" ∷ ⌜ tombed_uid = used_uid ∖ map_to_set (λ _ obj, (KObjectV.objectmeta obj).(ObjectMetaV.UID')) abs_state ⌝ ∗
    "%Hreserved_disjoint_abs" ∷ ⌜ reserved_keys ## dom abs_state ⌝.

Definition is_kubernetes γ l : iProp Σ :=
  ∃ (mu_l: loc),
    "Hmu" ∷ l.[(apimodel.State.t), "mu"] ↦□ mu_l ∗
    "Hkinv" ∷ is_Mutex mu_l (kubernetes_inv γ l).

End spec.
