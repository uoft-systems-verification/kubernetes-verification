From New.proof Require Import prelude empty_ffi.
From New.proof.kubernetes_model Require Export inv common.

Section proof.
Context `{hG: !heapGS Σ} {go_ctx: GoContext}.
Context `{!kubernetesModelG Σ}.

Lemma wp_State__update_au γ l kind namespace i kobj :
  ∀ Φ,
    is_pkg_init apimodel ∗
    is_kubernetes γ l ∗
    "%Hvalid" ∷ ⌜ KObjectV.valid kobj ⌝ ∗
    "%Hkind_matches" ∷ ⌜ kind = KObjectV.kind kobj ⌝ ∗
    "%Hns_matches" ∷ ⌜ namespace = (KObjectV.objectmeta kobj).(ObjectMetaV.Namespace') ⌝ ∗
    "Hdeepown_i" ∷ KObjectV.deepown_i i kobj 1 ∗
    ( |={⊤,∅}=> ∃ key uid kmeta kspec,
      "Hown_meta_frag" ∷ own_meta_frag γ key uid 1 kmeta ∗
      "Hown_spec_frag" ∷ own_spec_frag γ key uid 1 kspec ∗
      "%Hkey_eq" ∷ ⌜ key = KObjectV.key kobj ⌝ ∗
      "%Huid_eq" ∷ ⌜ uid = (KObjectV.objectmeta kobj).(ObjectMetaV.UID') ⌝ ∗
      "%Hvalid_meta_update" ∷ ⌜ ObjectMetaV.valid_simple_update kmeta (KObjectV.objectmeta kobj) ⌝ ∗
      "%Hvalid_spec_update" ∷ ⌜ ObjectSpecV.valid_update kspec (KObjectV.spec kobj) ⌝ ∗
      (* Hno_deletion_timestamp ensures that the update doesn't delete the object *)
      "%Hno_deletion_timestamp" ∷ ⌜ kmeta.(ObjectMetaV.DeletionTimestamp') = None ⌝ ∗
      "Hclose" ∷ (
          ∀ i' err kobj',
            ( (⌜ err = interface.nil ⌝ ∗
                ⌜ ObjectMetaV.updated (KObjectV.objectmeta kobj) (KObjectV.objectmeta kobj') ⌝ ∗
                ⌜ ObjectSpecV.updated (KObjectV.spec kobj) (KObjectV.spec kobj') ⌝ ∗
                KObjectV.deepown_i i' kobj' 1 ∗
                own_meta_frag γ key uid 1 (KObjectV.objectmeta kobj') ∗
                own_spec_frag γ key uid 1 (KObjectV.spec kobj')) ∨
              (⌜ err ≠ interface.nil ⌝ ∗
                own_meta_frag γ key uid 1 kmeta ∗
                own_spec_frag γ key uid 1 kspec)
            )
              ={∅,⊤}=∗ ▷ Φ (#i', #err)%V
      )%I
    ) -∗ WP l @ (ptrT.id apimodel.State.id) @ "update" #kind #namespace #i {{ Φ }}.
Proof. Admitted.

End proof.
