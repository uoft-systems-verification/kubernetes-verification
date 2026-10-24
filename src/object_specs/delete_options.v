From New.generatedviews Require Export delete_options.
From New.proof Require Import prelude empty_ffi.

Module PreconditionsV := DeleteOptionsView.PreconditionsV.

Module DeleteOptionsV.
Include DeleteOptionsView.DeleteOptionsV.

(* https://github.com/kubernetes/kubernetes/blob/release-1.34/staging/src/k8s.io/apimachinery/pkg/apis/meta/v1/validation/validation.go#L157 *)
Definition valid (options : t) : Prop :=
  (match options.(OrphanDependents'), options.(PropagationPolicy') with
  | Some _, Some _ => False
  | _, Some policy =>
      policy = "Foreground"%go ∨
      policy = "Background"%go ∨
      policy = "Orphan"%go
  | _, None => True
  end) ∧
  Forall (λ directive, directive = "All"%go) (default [] options.(DryRun')) ∧
  (options.(IgnoreStoreReadErrorWithClusterBreakingPotential') = Some true →
    default [] options.(DryRun') = [] ∧
    options.(PropagationPolicy') = None ∧
    options.(OrphanDependents') = None ∧
    options.(GracePeriodSeconds') = None ∧
    options.(Preconditions') = None).

End DeleteOptionsV.
