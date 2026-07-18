From New.proof Require Import prelude empty_ffi.
From New.proof.kubernetes_types Require Export common.

Module PreconditionsV.
Section def.
Context `{hG: !heapGS Σ} `{!ffi_semantics _ _}.
Context {sem : go.Semantics}
  {meta_v1_sem : code.k8s_io.apimachinery.pkg.apis.meta.v1.v1.Assumptions}.
Record t := mk {
  UID' : option types.UID.t;
  ResourceVersion' : option go_string;
}.

Definition deepown (c: v1.Preconditions.t) (v: t) dq: iProp Σ :=
  "%Hdeepown_uid_none" ∷ ⌜ c.(v1.Preconditions.UID') = null ↔ v.(UID') = None⌝ ∗
  "Hdeepown_uid_some" ∷ (match v.(UID') with
  | Some vu => ∃ cu, c.(v1.Preconditions.UID') ↦{dq} cu ∗ ⌜ cu = vu ⌝
  | None => True%I
  end) ∗
  "%Hdeepown_resourceversion_none" ∷ ⌜ c.(v1.Preconditions.ResourceVersion') = null ↔ v.(ResourceVersion') = None⌝ ∗
  "Hdeepown_resourceversion_some" ∷ (match v.(ResourceVersion') with
  | Some vrv => ∃ crv, c.(v1.Preconditions.ResourceVersion') ↦{dq} crv ∗ ⌜ crv = vrv ⌝
  | None => True%I
  end).

Definition deepown_l l v dq: iProp Σ :=
  ∃ c, l ↦{dq} c ∗ deepown c v dq.

Definition valid_interface i (l : loc) : Prop :=
  i = interface.mk (go.PointerType v1.Preconditions) #l.

Definition deepown_i i v dq: iProp Σ :=
  ∃ l, ⌜ valid_interface i l ⌝ ∗ deepown_l l v dq.
End def.
End PreconditionsV.

Module DeleteOptionsV.
Section def.
Context `{hG: !heapGS Σ} `{!ffi_semantics _ _}.
Context {sem : go.Semantics}
  {meta_v1_sem : code.k8s_io.apimachinery.pkg.apis.meta.v1.v1.Assumptions}.
Record t := mk {
  TypeMeta' : v1.TypeMeta.t;
  GracePeriodSeconds' : option w64;
  Preconditions' : option PreconditionsV.t;
  OrphanDependents' : option bool;
  PropagationPolicy' : option go_string;
  (* DryRun' : slice.t; *)
  (* IgnoreStoreReadErrorWithClusterBreakingPotential' : loc; *)
}.

Definition deepown (c: v1.DeleteOptions.t) (v: t) dq: iProp Σ :=
  "%Hdeepown_typemeta" ∷ ⌜ c.(v1.DeleteOptions.TypeMeta') = v.(TypeMeta') ⌝ ∗
  "%Hdeepown_graceperiodseconds_none" ∷ ⌜ c.(v1.DeleteOptions.GracePeriodSeconds') = null ↔ v.(GracePeriodSeconds') = None⌝ ∗
  "Hdeepown_graceperiodseconds_some" ∷ (match v.(GracePeriodSeconds') with
  | Some vgps => ∃ cgps, c.(v1.DeleteOptions.GracePeriodSeconds') ↦{dq} cgps ∗ ⌜ cgps = vgps ⌝
  | None => True%I
  end) ∗
  "%Hdeepown_preconditions_none" ∷ ⌜ c.(v1.DeleteOptions.Preconditions') = null ↔ v.(Preconditions') = None⌝ ∗
  "Hdeepown_preconditions_some" ∷ (match v.(Preconditions') with
  | Some vp => ∃ cp, c.(v1.DeleteOptions.Preconditions') ↦{dq} cp ∗ PreconditionsV.deepown cp vp dq
  | None => True%I
  end) ∗
  "%Hdeepown_orphandependents_none" ∷ ⌜ c.(v1.DeleteOptions.OrphanDependents') = null ↔ v.(OrphanDependents') = None⌝ ∗
  "Hdeepown_orphandependents_some" ∷ (match v.(OrphanDependents') with
  | Some vod => ∃ cod, c.(v1.DeleteOptions.OrphanDependents') ↦{dq} cod ∗ ⌜ cod = vod ⌝
  | None => True%I
  end) ∗
  "%Hdeepown_propagationpolicy_none" ∷ ⌜ c.(v1.DeleteOptions.PropagationPolicy') = null ↔ v.(PropagationPolicy') = None⌝ ∗
  "Hdeepown_propagationpolicy_some" ∷ (match v.(PropagationPolicy') with
  | Some vpp => ∃ cpp, c.(v1.DeleteOptions.PropagationPolicy') ↦{dq} cpp ∗ ⌜ cpp = vpp ⌝
  | None => True%I
  end).

Definition deepown_l l v dq: iProp Σ :=
  ∃ c, l ↦{dq} c ∗ deepown c v dq.

Definition valid_interface i (l : loc) : Prop :=
  i = interface.mk (go.PointerType v1.DeleteOptions) #l.

Definition deepown_i i v dq: iProp Σ :=
  ∃ l, ⌜ valid_interface i l ⌝ ∗ deepown_l l v dq.

(* https://github.com/kubernetes/kubernetes/blob/release-1.34/staging/src/k8s.io/apimachinery/pkg/apis/meta/v1/validation/validation.go#L157 *)
Axiom valid : t -> Prop.

End def.
End DeleteOptionsV.
