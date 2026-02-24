Require Export New.proof.sync.
From New.proof.kubernetes_model Require Export apimodel_init.
From New.proof.k8s_io.apimachinery.pkg.api Require Export meta.
From New.proof.k8s_io.apimachinery.pkg.apis.meta Require Export v1.
From New.proof Require Import prelude empty_ffi.
From New.proof Require Export pure_objects string.
From New.proof.big_op Require Export big_sepL big_sepM.
From New.proof.algebra Require Export kview cview mono_gset.

Section spec.
Context `{hG: !heapGS Σ} {go_ctx: GoContext}.
Context `{!kviewG Σ}.

Definition obj_parent_ref obj: option (KKey.t * types.UID.t) :=
  match (KObjectV.objectmeta obj).(ObjectMetaV.OwnerReferences') with
  | Some orefs => match list_find (λ oref, oref.(OwnerReferenceV.Controller') = Some true) orefs with
    | Some (_, oref) => Some (
                          {|
                            KKey.Kind' := oref.(OwnerReferenceV.Kind');
                            KKey.Namespace' := (KObjectV.objectmeta obj).(ObjectMetaV.Namespace');
                            KKey.Name' := oref.(OwnerReferenceV.Name');
                          |},
                          oref.(OwnerReferenceV.UID')
                        )
    | None => None
    end
  | None => None
  end.

Definition obj_ref k obj: KKey.t * types.UID.t :=
  (k, (KObjectV.objectmeta obj).(ObjectMetaV.UID')).

Context `{!cviewG KKey.t (KKey.t * types.UID.t) KObjectV.t obj_parent_ref obj_ref Σ}.

Context `{!mono_gsetG types.UID.t Σ}.

Record KubernetesGname := mk_γk {
  γ_state : gname;
  γ_children : gname;
  γ_tombstone : gname;
}.

Definition own_kview_auth γ state used_uids: iProp Σ :=
  kview.own_auth γ.(γ_state) state used_uids.

Definition own_meta_frag γ k uid dq m: iProp Σ :=
  kview.own_meta_frag γ.(γ_state) k uid dq m.

Definition own_spec_frag γ k uid dq sp: iProp Σ :=
  kview.own_spec_frag γ.(γ_state) k uid dq sp.

Definition own_status_frag γ k uid dq st: iProp Σ :=
  kview.own_status_frag γ.(γ_state) k uid dq st.

Definition own_children_auth γ state used_references: iProp Σ :=
  cview.own_auth KKey.t (KKey.t * types.UID.t) KObjectV.t obj_parent_ref obj_ref
  γ.(γ_children) state used_references.

Definition own_children_frag γ key uid dq keys: iProp Σ :=
  cview.own_frag KKey.t (KKey.t * types.UID.t) KObjectV.t obj_parent_ref obj_ref
  γ.(γ_children) (key, uid) dq keys.

Definition own_tombstone_auth γ tombed_uids: iProp Σ :=
  mono_gset.own_auth types.UID.t γ.(γ_tombstone) tombed_uids.

Definition own_tombstone_frag γ tombed_uid: iProp Σ :=
  mono_gset.own_frag types.UID.t γ.(γ_tombstone) tombed_uid.

Definition kubernetes_inv γ l: iProp Σ :=
  ∃ (phys_state_l: loc) (rvc: w64) (phys_state: gmap KKey.t interface.t)
    (abs_state: gmap KKey.t KObjectV.t) (used_uids: gset types.UID.t)
    (tombed_uids: gset types.UID.t) (used_references: gset (KKey.t * types.UID.t)),
    "Hstate_m_addr" ∷ l ↦s[apimodel.State :: "m"] phys_state_l ∗
    "Hstate_rvc_addr" ∷ l ↦s[apimodel.State :: "resourceVersionCounter"] rvc ∗
    "Hown_phys" ∷ phys_state_l ↦$ phys_state ∗
    "Hown_abs" ∷ own_kview_auth γ abs_state used_uids ∗
    "Hown_children" ∷ own_children_auth γ abs_state used_references ∗
    "Hown_tombstone" ∷ own_tombstone_auth γ tombed_uids ∗
    "Hphys_abs_rep" ∷ ([∗ map] i; obj ∈ phys_state; abs_state, KObjectV.deepown_i i obj 1) ∗
    "%Hused_uids_eq" ∷ ⌜ used_uids = (set_map (λ v, snd v) used_references) ⌝ ∗
    "%Htombed_uids_eq" ∷ ⌜ tombed_uids = used_uids ∖ map_to_set (λ _ obj, (KObjectV.objectmeta obj).(ObjectMetaV.UID')) abs_state ⌝.

Definition is_kubernetes γ l : iProp Σ :=
  ∃ (mu_l: loc),
    "Hmu" ∷ l ↦s[apimodel.State :: "mu"]□ mu_l ∗
    "Hkinv" ∷ is_Mutex mu_l (kubernetes_inv γ l).

End spec.
