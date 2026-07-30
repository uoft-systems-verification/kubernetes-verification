From New.proof.kubernetes_types Require Export prelude.

Definition pvc_claim_template_names (sts : StatefulSetV.t) : list go_string :=
  (λ claim_template,
    claim_template.(PersistentVolumeClaimV.ObjectMeta').(ObjectMetaV.Name'))
  <$> sts.(StatefulSetV.Spec').(StatefulSetSpecV.VolumeClaimTemplates').

Definition desired_pvc_name set_name claim_template_name ordinal : go_string :=
  claim_template_name ++ "-"%go ++ set_name ++ "-"%go ++ decimal_string ordinal.

Definition desired_pvc_key sts claim_template_name ordinal : KKey.t := {|
  KKey.Kind' := PersistentVolumeClaimV.kind;
  KKey.Namespace' := sts.(StatefulSetV.ObjectMeta').(ObjectMetaV.Namespace');
  KKey.Name' := desired_pvc_name
    sts.(StatefulSetV.ObjectMeta').(ObjectMetaV.Name') claim_template_name ordinal;
|}.

Definition desired_pvc_key_candidates sts : list KKey.t :=
  concat (
    (λ ordinal,
      (λ claim_template_name, desired_pvc_key sts claim_template_name ordinal)
      <$> pvc_claim_template_names sts)
    <$> seq 0
      (match sts.(StatefulSetV.Spec').(StatefulSetSpecV.Replicas') with
       | Some replicas => sint.nat replicas
       | None => 1%nat
       end)
  ).

(* The official StatefulSet controller stores PVC requirements in maps keyed by
   template name, so duplicate claim-template names collapse to one object key. *)
Definition desired_pvc_keys sts : list KKey.t :=
  elements (list_to_set (C:=gset KKey.t) (desired_pvc_key_candidates sts)).

(* Selector MatchLabels are copied into the claim after the template labels,
   so selector values take precedence when both maps contain the same key.
   The implementation also replaces a nil template label map with an allocated
   empty map, hence the result always stores [Some labels]. *)
Definition new_persistent_volume_claim_labels
    (set : StatefulSetV.t) (claim_template : PersistentVolumeClaimV.t) :
    gmap go_string go_string :=
  let claim_labels :=
    default ∅
      claim_template.(PersistentVolumeClaimV.ObjectMeta').(ObjectMetaV.Labels') in
  let selector_labels :=
    match set.(StatefulSetV.Spec').(StatefulSetSpecV.Selector') with
    | Some selector =>
        default ∅ selector.(LabelSelectorV.MatchLabels')
    | None => ∅
    end in
  selector_labels ∪ claim_labels.

Definition new_persistent_volume_claim
    (set : StatefulSetV.t) (claim_template : PersistentVolumeClaimV.t)
    (ordinal : nat) : PersistentVolumeClaimV.t :=
  let object_meta :=
    claim_template.(PersistentVolumeClaimV.ObjectMeta')
      <| ObjectMetaV.Name' :=
          desired_pvc_name
            set.(StatefulSetV.ObjectMeta').(ObjectMetaV.Name')
            claim_template.(PersistentVolumeClaimV.ObjectMeta').(ObjectMetaV.Name')
            ordinal |>
      <| ObjectMetaV.Namespace' :=
          set.(StatefulSetV.ObjectMeta').(ObjectMetaV.Namespace') |>
      <| ObjectMetaV.OwnerReferences' := None |>
      <| ObjectMetaV.Labels' :=
          Some (new_persistent_volume_claim_labels set claim_template) |> in
  claim_template <| PersistentVolumeClaimV.ObjectMeta' := object_meta |>.

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
