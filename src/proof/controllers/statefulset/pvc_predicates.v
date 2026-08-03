From New.proof.controllers.statefulset Require Export top_level.

Definition new_persistent_volume_claim_key
    (set : StatefulSetV.t) (claim_template : PersistentVolumeClaimV.t)
    (ordinal : nat) : KKey.t :=
  PersistentVolumeClaimV.key
    (new_persistent_volume_claim set claim_template ordinal).

Lemma new_persistent_volume_claim_key_eq set claim_template ordinal :
  new_persistent_volume_claim_key set claim_template ordinal =
    desired_pvc_key set
      claim_template.(PersistentVolumeClaimV.ObjectMeta').(ObjectMetaV.Name')
      ordinal.
Proof.
  unfold new_persistent_volume_claim_key, PersistentVolumeClaimV.key,
    PersistentVolumeClaimV.meta_key, desired_pvc_key,
    new_persistent_volume_claim.
  done.
Qed.

Definition persistent_volume_claim_template_insert
    (claim_templates : gmap go_string PersistentVolumeClaimV.t)
    (claim_template : PersistentVolumeClaimV.t) :
    gmap go_string PersistentVolumeClaimV.t :=
  <[claim_template.(PersistentVolumeClaimV.ObjectMeta').(ObjectMetaV.Name') :=
    claim_template]> claim_templates.

Definition persistent_volume_claim_templates_by_name
    (claim_templates : list PersistentVolumeClaimV.t) :
    gmap go_string PersistentVolumeClaimV.t :=
  fold_left persistent_volume_claim_template_insert claim_templates ∅.

Lemma persistent_volume_claim_templates_by_name_snoc claim_templates
    claim_template :
  persistent_volume_claim_templates_by_name
      (claim_templates ++ [claim_template]) =
    persistent_volume_claim_template_insert
      (persistent_volume_claim_templates_by_name claim_templates)
      claim_template.
Proof.
  unfold persistent_volume_claim_templates_by_name.
  by rewrite fold_left_app.
Qed.

Lemma persistent_volume_claim_templates_by_name_dom claim_templates :
  dom (persistent_volume_claim_templates_by_name claim_templates) =
    list_to_set
      ((λ claim_template,
          claim_template.(PersistentVolumeClaimV.ObjectMeta').(ObjectMetaV.Name'))
        <$> claim_templates).
Proof.
  induction claim_templates using rev_ind.
  - rewrite /persistent_volume_claim_templates_by_name /=
      dom_empty_L. done.
  - apply leibniz_equiv. apply set_equiv.
    intros name.
    assert (is_Some
        (persistent_volume_claim_templates_by_name claim_templates !! name) ↔
      name ∈ list_to_set (C:=gset go_string)
        ((λ claim_template,
            claim_template.(PersistentVolumeClaimV.ObjectMeta').(ObjectMetaV.Name'))
          <$> claim_templates)) as Hprevious.
    { rewrite -elem_of_dom IHclaim_templates. done. }
    rewrite persistent_volume_claim_templates_by_name_snoc
      /persistent_volume_claim_template_insert.
    rewrite elem_of_dom lookup_insert_is_Some'.
    rewrite fmap_app elem_of_list_to_set elem_of_app /=.
    rewrite Hprevious elem_of_list_to_set.
    rewrite list_elem_of_singleton.
    split; intros [Hname|Hprevious'];
      [right; symmetry; exact Hname
      |left; exact Hprevious'
      |right; exact Hname
      |left; symmetry; exact Hprevious'].
Qed.
