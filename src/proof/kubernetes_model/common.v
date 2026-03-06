From New.proof Require Import prelude empty_ffi.
From New.proof.kubernetes_model Require Export apimodel_init.
From New.proof Require Export pure_objects.

Section proof.
Context `{hG: !heapGS Σ} {go_ctx: GoContext}.

Lemma wp_deepCopy i obj:
  {{{ is_pkg_init apimodel ∗
      KObjectV.deepown_i i obj 1
  }}}
    @! apimodel.deepCopy #i
  {{{ i', RET #i';
      KObjectV.deepown_i i' obj 1 ∗
      KObjectV.deepown_i i obj 1
  }}}.
Proof.
Admitted.

Lemma wp_applyValidationAndDefaulting i o (name : go_string):
  {{{ is_pkg_init apimodel ∗
      KObjectV.deepown_i i o 1 ∗
      ⌜ let m := KObjectV.objectmeta o in
        (m.(ObjectMetaV.GenerateName') ≠ ""%go →
          valid_generate_name m.(ObjectMetaV.GenerateName')) ∧
        m.(ObjectMetaV.Name') ≠ ""%go ∧
        valid_name m.(ObjectMetaV.Name') ∧
        m.(ObjectMetaV.Namespace') ≠ ""%go ∧
        valid_namespace m.(ObjectMetaV.Namespace') ∧
        valid_labels m.(ObjectMetaV.Labels') ∧
        valid_annotations m.(ObjectMetaV.Annotations') ∧
        valid_owner_references m.(ObjectMetaV.OwnerReferences') ∧
        valid_finalizers m.(ObjectMetaV.Finalizers') ∧
        valid_managed_fields m.(ObjectMetaV.ManagedFields') ⌝
  }}}
    @! apimodel.applyValidationAndDefaulting #i #name
  {{{ o', RET #interface.nil;
      KObjectV.deepown_i i o' 1 ∗
      ⌜ ObjectMetaV.valid (KObjectV.objectmeta o') ⌝ ∗
      ⌜ KObjectV.objectmeta o' = ((KObjectV.objectmeta o) <| ObjectMetaV.Generation' := W64 1 |>) ⌝ ∗
      ⌜ ObjectSpecV.created (KObjectV.spec o) (KObjectV.spec o') ⌝ ∗
      ⌜ ObjectStatusV.created (KObjectV.status o) (KObjectV.status o') ⌝
  }}}.
Proof.
Admitted.

End proof.
