From New.proof.k8s_io.apiserver.pkg.registry Require Export rest_init.
From New.proof.k8s_io.apimachinery.pkg.apis.meta Require Export v1_init.
From New.proof Require Import prelude empty_ffi.
From New.proof.kubernetes_types Require Import prelude.

Section proof.
Context `{hG: !heapGS Σ} `{!ffi_semantics _ _}.
Context {sem : go.Semantics}
  {package_sem : rest.Assumptions}
  {meta_v1_sem : code.k8s_io.apimachinery.pkg.apis.meta.v1.v1.Assumptions}.
Local Set Default Proof Using "All".

Lemma wp_WipeObjectMetaSystemFields i l o m :
  {{{ is_pkg_init rest ∗
      ⌜ KObjectV.valid_interface i l o ⌝ ∗
      ObjectMetaV.deepown_l (KObjectV.objectmeta_ptr l o) m 1
  }}}
    @! rest.WipeObjectMetaSystemFields #(interface.ok i)
  {{{ time, RET #();
      ObjectMetaV.deepown_l (KObjectV.objectmeta_ptr l o)
        (m <| ObjectMetaV.CreationTimestamp' := time |>
           <| ObjectMetaV.UID' := ""%go |>
           <| ObjectMetaV.DeletionTimestamp' := None |>
           <| ObjectMetaV.DeletionGracePeriodSeconds' := None |>
           <| ObjectMetaV.SelfLink' := ""%go |>) 1
  }}}.
Proof. Admitted.

Lemma wp_FillObjectMetaSystemFields i l o m :
  {{{ is_pkg_init rest ∗
      ⌜ KObjectV.valid_interface i l o ⌝ ∗
      ObjectMetaV.deepown_l (KObjectV.objectmeta_ptr l o) m 1
  }}}
    @! rest.FillObjectMetaSystemFields #(interface.ok i)
  {{{ time uid, RET #();
      ObjectMetaV.deepown_l (KObjectV.objectmeta_ptr l o)
        (m <| ObjectMetaV.CreationTimestamp' := time |>
           <| ObjectMetaV.UID' := uid |>) 1
  }}}.
Proof. Admitted.

(* The call either leaves the object in the request namespace or returns an
   error, which happens only when the object's namespace is set and differs from
   the request namespace. *)
Lemma wp_EnsureObjectNamespaceMatchesRequestNamespace_general ns i l o m :
  {{{ is_pkg_init rest ∗
      ⌜ KObjectV.valid_interface i l o ⌝ ∗
      ObjectMetaV.deepown_l (KObjectV.objectmeta_ptr l o) m 1
  }}}
    @! rest.EnsureObjectNamespaceMatchesRequestNamespace #ns #(interface.ok i)
  {{{ (err : interface.t), RET #err;
      (⌜ err = interface.nil ⌝ ∗
        ObjectMetaV.deepown_l (KObjectV.objectmeta_ptr l o) (m <| ObjectMetaV.Namespace' := ns |>) 1) ∨
      ⌜ err ≠ interface.nil ∧ m.(ObjectMetaV.Namespace') ≠ ""%go ∧ m.(ObjectMetaV.Namespace') ≠ ns ⌝
  }}}.
Proof. Admitted.

(* When the object's namespace is unset or already the request namespace, the
   call succeeds. *)
Lemma wp_EnsureObjectNamespaceMatchesRequestNamespace ns i l o m :
  {{{ is_pkg_init rest ∗
      ⌜ KObjectV.valid_interface i l o ⌝ ∗
      ObjectMetaV.deepown_l (KObjectV.objectmeta_ptr l o) m 1 ∗
      ⌜ m.(ObjectMetaV.Namespace') = ""%go ∨ m.(ObjectMetaV.Namespace') = ns ⌝
  }}}
    @! rest.EnsureObjectNamespaceMatchesRequestNamespace #ns #(interface.ok i)
  {{{ RET #interface.nil;
      ObjectMetaV.deepown_l (KObjectV.objectmeta_ptr l o)
        (m <| ObjectMetaV.Namespace' := ns |>) 1
  }}}.
Proof.
  iIntros (Φ) "(#Hpkg & %Hvalid & Hdeepown & %Hns) HΦ".
  wp_apply (wp_EnsureObjectNamespaceMatchesRequestNamespace_general with "[$Hpkg $Hdeepown]").
  { done. }
  iIntros (err) "[[-> Hdeepown] | (_ & %Hns_set & %Hns_ne)]".
  - iApply "HΦ". iFrame.
  - exfalso. destruct Hns; done.
Qed.

End proof.
