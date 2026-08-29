From New.proof Require Import prelude empty_ffi.
From New.proof Require Export util.
From New.proof Require Export wp_helpers.
From New.proof.kubernetes_types Require Export prelude.
From New.proof.controllers.deployment Require Export deployment_init.
From New.proof.k8s_io.api.apps Require Export v1.
From New.proof.k8s_io.kubernetes.pkg Require Export controller.
From New.proof.k8s_io.apimachinery.pkg.api Require Export errors.

Section proof.
Context `{hG: !heapGS Σ}.
Context {sem : go.Semantics}
  {package_sem : code.controllers.deployment.deployment.Assumptions}.
Collection W := sem + package_sem.
#[local] Instance controller_sem : controller.Assumptions :=
  code.controllers.deployment.deployment.import_controller_Assumption.
#[local] Instance base_apimodel_sem : apimodel.Assumptions | 100 :=
  code.controllers.deployment.deployment.import_apimodel_Assumption.
#[local] Instance object_meta_v1_sem :
    code.k8s_io.apimachinery.pkg.apis.meta.v1.v1.Assumptions :=
  apimodel.import_apis_meta_v1_Assumption.
#[local] Instance object_apps_v1_sem :
    code.k8s_io.api.apps.v1.v1.Assumptions :=
  apimodel.import_api_apps_v1_Assumption.
#[local] Instance object_core_v1_sem :
    code.k8s_io.api.core.v1.v1.Assumptions :=
  code.k8s_io.api.apps.v1.v1.import_core_v1_Assumption.
#[local] Instance intstr_sem : intstr.Assumptions :=
  code.k8s_io.api.apps.v1.v1.import_intstr_Assumption.
#[local] Instance apimodel_sem : apimodel.Assumptions | 0.
Proof using package_sem.
  constructor; try exact object_core_v1_sem; try apply _.
Defined.
Local Set Default Proof Using "All".
(* ---------------------------------------------------------------- *)
(* Gallina model of the pure deployment helpers                      *)
(* ---------------------------------------------------------------- *)

Definition deployment_replicas (d : DeploymentV.t) : w32 :=
  match d.(DeploymentV.Spec').(DeploymentSpecV.Replicas') with
  | Some replicas => replicas
  | None => W32 1
  end.

Definition rs_replicas (rs : ReplicaSetV.t) : w32 :=
  match rs.(ReplicaSetV.Spec').(ReplicaSetSpecV.Replicas') with
  | Some replicas => replicas
  | None => W32 0
  end.

Definition rs_opt_replicas (rs_o : option ReplicaSetV.t) : w32 :=
  match rs_o with
  | Some rs => rs_replicas rs
  | None => W32 0
  end.

(* ---------------------------------------------------------------- *)
(* Ownership helpers for nil-able arguments                          *)
(* ---------------------------------------------------------------- *)

(* Ownership of a possibly-nil *apps.ReplicaSet argument. *)
Definition rs_opt_own (l : loc) (rs_o : option ReplicaSetV.t) dq : iProp Σ :=
  match rs_o with
  | Some rs => ReplicaSetV.deepown_l l rs dq
  | None => ⌜ l = null ⌝
  end.

(* Ownership of a possibly-nil map[string]string argument.  ObjectMetaV models
   an absent label/annotation map as None, and Go ranges over a nil map without
   faulting, so cloneAndAddLabel must accept both. *)
Definition labels_opt_own (l : loc)
    (m_o : option (gmap go_string go_string)) dq : iProp Σ :=
  match m_o with
  | Some m => l ↦${dq} m
  | None => ⌜ l = null ⌝
  end.

(* [ObjectMetaV.deepown] stores the label map as a nullable pair; these move
   between that shape and the argument shape [cloneAndAddLabel] wants, so the
   metadata can be taken apart for the call and put back afterwards. *)
Definition labels_field_own (c : loc)
    (v : option (gmap go_string go_string)) dq : iProp Σ :=
  match v with
  | Some vl => ∃ cl, c ↦${dq} cl ∗ ⌜ cl = vl ⌝
  | None => True
  end.

Lemma labels_opt_own_of_field c v dq :
  ⌜ c = null ↔ v = None ⌝ -∗
  labels_field_own c v dq -∗
  labels_opt_own c v dq.
Proof.
  iIntros "%Hnone Hfield". rewrite /labels_opt_own /labels_field_own.
  destruct v as [vl|].
  - iDestruct "Hfield" as (cl) "[Hcl ->]". iFrame.
  - iPureIntro. apply Hnone. done.
Qed.

Lemma labels_field_own_of_opt c v dq :
  labels_opt_own c v dq -∗ labels_field_own c v dq.
Proof.
  iIntros "H". rewrite /labels_opt_own /labels_field_own.
  destruct v as [vl|]; [iExists vl; iFrame; done|done].
Qed.

(* Lend a pod template's label map to [cloneAndAddLabel] and take it back.
   Both calls in getNewReplicaSet read the deployment's own template, so the
   metadata has to be opened and closed around each. *)
Lemma podtemplate_labels_acc c v dq :
  PodTemplateSpecV.deepown c v dq -∗
  labels_opt_own c.(v1.PodTemplateSpec.ObjectMeta').(v1.ObjectMeta.Labels')
    v.(PodTemplateSpecV.ObjectMeta').(ObjectMetaV.Labels') dq ∗
  (labels_opt_own c.(v1.PodTemplateSpec.ObjectMeta').(v1.ObjectMeta.Labels')
     v.(PodTemplateSpecV.ObjectMeta').(ObjectMetaV.Labels') dq -∗
   PodTemplateSpecV.deepown c v dq).
Proof.
  iIntros "H". iNamed "H".
  iNamedPrefix "Hdeepown_objectmeta" "Hm_".
  iDestruct (labels_opt_own_of_field with "[] Hm_Hdeepown_labels_some")
    as "Hlabels"; [iPureIntro; exact Hm_Hdeepown_labels_none|].
  iFrame "Hlabels".
  iIntros "Hlabels".
  iDestruct (labels_field_own_of_opt with "Hlabels")
    as "Hm_Hdeepown_labels_some".
  rewrite /PodTemplateSpecV.deepown /named.
  iSplitR "Hdeepown_spec"; [|iAssumption].
  rewrite /ObjectMetaV.deepown /named.
  iFrame "%". iFrame.
Qed.

(* getNewReplicaSet stamps the pod-template-hash label onto the deep copy of
   the deployment's template, replacing whatever label map was there. The old
   map's ownership is dropped; the new one is threaded in. *)
Lemma podtemplate_replace_labels c v (l : loc) (m : gmap go_string go_string) :
  l ≠ null →
  PodTemplateSpecV.deepown c v 1 -∗
  l ↦$ m -∗
  PodTemplateSpecV.deepown
    (c <| v1.PodTemplateSpec.ObjectMeta' :=
       c.(v1.PodTemplateSpec.ObjectMeta') <| v1.ObjectMeta.Labels' := l |> |>)
    (v <| PodTemplateSpecV.ObjectMeta' :=
       v.(PodTemplateSpecV.ObjectMeta') <| ObjectMetaV.Labels' := Some m |> |>) 1.
Proof.
  iIntros (Hnn) "H Hm". iNamed "H".
  iNamedPrefix "Hdeepown_objectmeta" "Hm_".
  rewrite /PodTemplateSpecV.deepown /named /=.
  iSplitR "Hdeepown_spec"; [|iAssumption].
  rewrite /ObjectMetaV.deepown /named /=.
  iFrame "%".
  iFrame "Hm_Hdeepown_creationtimestamp Hm_Hdeepown_deletiontimestamp_some
    Hm_Hdeepown_deletiongraceperiodseconds_some Hm_Hdeepown_annotations_some
    Hm_Hdeepown_ownerreferences_some Hm_Hdeepown_finalizers_some
    Hm_Hdeepown_managedfields_some".
  iSplitR; [iPureIntro; split;
    [intros Hc; exfalso; exact (Hnn Hc)|intros Hc; discriminate]|].
  iExists m. iFrame. done.
Qed.

(* cloneSelectorAndAddLabel returns a copy of [selector] whose MatchLabels are
   [selector]'s plus one binding.  A nil MatchLabels is first replaced by a fresh
   empty map, so the result's MatchLabels is always Some. *)
Definition selector_with_label (selector : LabelSelectorV.t)
    (key value : go_string) : LabelSelectorV.t :=
  LabelSelectorV.mk
    (Some (<[key := value]>
      (default ∅ selector.(LabelSelectorV.MatchLabels'))))
    selector.(LabelSelectorV.MatchExpressions').

Definition rs_uid (rs : ReplicaSetV.t) : types.UID.t :=
  rs.(ReplicaSetV.ObjectMeta').(ObjectMetaV.UID').

(* findOldReplicaSets keeps every ReplicaSet whose UID differs from the new
   one's. Keyed on the bare UID rather than the ReplicaSet it came from,
   matching the Go: the loop only ever needs a value to compare against, and
   taking the object would oblige a caller that already owns it through the
   list to own it a second time — which [deepown_l] cannot supply, since three
   of the predicates under it are opaque Axioms. See
   notes/deployment-spec-aug-26.md §3.1. *)
Definition rs_is_old (new_rs_uid : types.UID.t) (rs : ReplicaSetV.t) : Prop :=
  rs_uid rs ≠ new_rs_uid.

#[global] Instance rs_is_old_dec new_rs_uid rs : Decision (rs_is_old new_rs_uid rs).
Proof. unfold rs_is_old. apply _. Defined.

Definition old_replica_set_pairs (ptrs : list loc) (rss : list ReplicaSetV.t)
    (new_rs_uid : types.UID.t) : list (loc * ReplicaSetV.t) :=
  filter (λ pr, rs_is_old new_rs_uid pr.2) (zip ptrs rss).

Definition rs_is_new (new_rs_uid : types.UID.t) (rs : ReplicaSetV.t) : Prop :=
  ¬ rs_is_old new_rs_uid rs.

#[global] Instance rs_is_new_dec new_rs_uid rs : Decision (rs_is_new new_rs_uid rs).
Proof. unfold rs_is_new. apply _. Defined.

(* Interleaving post-states back into positional order.

   [rollout] scales the new ReplicaSet and, separately, every old one, so it
   ends up holding post-states for two disjoint sublists. Its postcondition is
   positional over the list it was given, so the two have to be merged back.
   [big_sepL2_filter_acc] cannot do this: it is an accessor that restores what
   it lent out, which is all the stability proof needs because nothing there is
   written.

   [merge_old_posts] walks the original list, taking each old ReplicaSet's
   post-state from [posts] in order and using [new_post] for the one that is
   not old. *)
Fixpoint merge_old_posts (new_rs_uid : types.UID.t) (rss : list ReplicaSetV.t)
    (new_post : ReplicaSetV.t) (posts : list ReplicaSetV.t)
    : list ReplicaSetV.t :=
  match rss with
  | [] => []
  | rs :: rest =>
      if decide (rs_is_old new_rs_uid rs)
      then match posts with
           | p :: posts' => p :: merge_old_posts new_rs_uid rest new_post posts'
           | [] => rs :: merge_old_posts new_rs_uid rest new_post []
           end
      else new_post :: merge_old_posts new_rs_uid rest new_post posts
  end.

Lemma merge_old_posts_length uid rss new_post posts :
  length (merge_old_posts uid rss new_post posts) = length rss.
Proof.
  revert posts. induction rss as [|rs rest IH]; intros posts; first done.
  simpl. destruct (decide (rs_is_old uid rs)).
  - destruct posts as [|p posts']; simpl; by rewrite IH.
  - simpl. by rewrite IH.
Qed.

(* Anything true of [new_post] and of every old post-state (and, for the
   degenerate short-[posts] case, of the originals) is true of the merge. *)
Lemma merge_old_posts_Forall uid rss new_post posts (Q : ReplicaSetV.t → Prop) :
  Q new_post →
  Forall Q posts →
  Forall Q rss →
  Forall Q (merge_old_posts uid rss new_post posts).
Proof.
  intros Hnew. revert posts.
  induction rss as [|rs rest IH]; intros posts Hposts Hrss;
    first apply Forall_nil_2.
  apply Forall_cons_1 in Hrss as [Hrs Hrest].
  simpl. destruct (decide (rs_is_old uid rs)).
  - destruct posts as [|p posts'].
    + apply Forall_cons_2; [exact Hrs|].
      apply IH; [apply Forall_nil_2|exact Hrest].
    + apply Forall_cons_1 in Hposts as [Hp Hposts'].
      apply Forall_cons_2; [exact Hp|apply IH; [exact Hposts'|exact Hrest]].
  - apply Forall_cons_2; [exact Hnew|apply IH; [exact Hposts|exact Hrest]].
Qed.

(* The recombination itself: post-states held separately for the old sublist
   and for the one ReplicaSet that is not old go back together positionally. *)
Lemma big_sepL2_merge_old_posts uid (rss : list ReplicaSetV.t)
    (new_post : ReplicaSetV.t) (posts : list ReplicaSetV.t)
    (P : ReplicaSetV.t → ReplicaSetV.t → iProp Σ) :
  ([∗ list] rs ∈ filter (rs_is_new uid) rss, P rs new_post) -∗
  ([∗ list] rs;p ∈ filter (rs_is_old uid) rss; posts, P rs p) -∗
  ([∗ list] rs;rs' ∈ rss; merge_old_posts uid rss new_post posts, P rs rs').
Proof.
  revert posts. induction rss as [|rs rest IH]; intros posts.
  { iIntros "_ _". done. }
  rewrite !filter_cons /=.
  destruct (decide (rs_is_old uid rs)) as [Hold|Hnot].
  - destruct (decide (rs_is_new uid rs)) as [Hcontra|_];
      first (exfalso; exact (Hcontra Hold)).
    iIntros "Hnewpart Holds".
    destruct posts as [|p posts'].
    { iDestruct (big_sepL2_nil_inv_r with "Holds") as %Hc. discriminate. }
    iDestruct "Holds" as "[Hp Holds]".
    iSplitL "Hp"; [iExact "Hp"|].
    iApply (IH posts' with "Hnewpart Holds").
  - destruct (decide (rs_is_new uid rs)) as [_|Hcontra];
      last (exfalso; exact (Hcontra Hnot)).
    iIntros "Hnewpart Holds".
    iDestruct "Hnewpart" as "[Hn Hnewpart]".
    iSplitL "Hn"; [iExact "Hn"|].
    iApply (IH posts with "Hnewpart Holds").
Qed.

(* TODO: un-axiomatize. Once PodTemplateSpecV carries enough structure to state
   template equality, template_matches should become a Definition (equality of
   the templates after deleting the pod-template-hash label from each
   ObjectMeta), the two axioms below should become proved lemmas, and
   wp_equalIgnoreHash in replica_sets.v should be discharged rather than
   Admitted.

   equalIgnoreHash compares pod templates ignoring the pod-template-hash label.
   PodTemplateSpecV is axiomatized, so the comparison relation and the spec
   below are trusted, mirroring controller.v's pod_from_template. *)
Parameter template_matches : PodTemplateSpecV.t → PodTemplateSpecV.t → Prop.
Axiom template_matches_dec : ∀ t1 t2, Decision (template_matches t1 t2).
#[global] Existing Instance template_matches_dec.
Axiom template_matches_sym : ∀ t1 t2, template_matches t1 t2 → template_matches t2 t1.

Definition rs_template (rs : ReplicaSetV.t) : PodTemplateSpecV.t :=
  rs.(ReplicaSetV.Spec').(ReplicaSetSpecV.Template').

Definition deployment_template (d : DeploymentV.t) : PodTemplateSpecV.t :=
  d.(DeploymentV.Spec').(DeploymentSpecV.Template').

(* findNewReplicaSet returns the first ReplicaSet whose template matches the
   deployment's, or nil. *)
Definition find_new_replica_set (d : DeploymentV.t) (rss : list ReplicaSetV.t)
    : option (nat * ReplicaSetV.t) :=
  list_find (λ rs, template_matches (rs_template rs) (deployment_template d)) rss.

(* ---------------------------------------------------------------- *)
(* Model of the state-touching helpers                               *)
(* ---------------------------------------------------------------- *)

Definition deployment_unique_label_key : go_string := "pod-template-hash"%go.

(* TODO: un-axiomatize alongside [template_matches]. controller.ComputeHash is
   goose-translated but has no WP spec, so the hash it returns is trusted here
   the same way template equality is. The only property the controller relies on
   is that matching templates hash equally, which is what makes the deterministic
   RS name stable across syncs — that is [template_hash_respects_matches]. *)
Parameter template_hash : PodTemplateSpecV.t → go_string.

(* TRUSTED. [controller.ComputeHash] serializes the template with
   [hashutil.DeepHashObject] and formats the FNV hash; neither the reflection
   nor the hashing is translated, so this is a contract rather than a proof —
   the same class as [wp_equalIgnoreHash]. It says only that the hash is a
   function of the modeled template value, which is what
   [template_hash_respects_matches] then relates to [template_matches].

   The [collisionCount] argument is always nil here: hash-collision handling is
   on deployment.go's excluded-features list. *)
Lemma wp_ComputeHash tmpl_l tmpl_c tmpl dq :
  {{{ is_pkg_init controller ∗
      "Htmpl_l" ∷ tmpl_l ↦{dq} tmpl_c ∗
      "Htmpl" ∷ PodTemplateSpecV.deepown tmpl_c tmpl dq
  }}}
    @! controller.ComputeHash #tmpl_l #null
  {{{ RET #(template_hash tmpl);
      "Htmpl_l" ∷ tmpl_l ↦{dq} tmpl_c ∗
      "Htmpl" ∷ PodTemplateSpecV.deepown tmpl_c tmpl dq
  }}}.
Proof. Admitted.
Axiom template_hash_respects_matches : ∀ t1 t2,
  template_matches t1 t2 → template_hash t1 = template_hash t2.

(* scaleReplicaSet rewrites only the replica count. *)
Definition rs_scaled_spec (rs : ReplicaSetV.t) (n : w32) : ReplicaSetSpecV.t :=
  ReplicaSetSpecV.mk
    (Some n)
    rs.(ReplicaSetV.Spec').(ReplicaSetSpecV.MinReadySeconds')
    rs.(ReplicaSetV.Spec').(ReplicaSetSpecV.Selector')
    rs.(ReplicaSetV.Spec').(ReplicaSetSpecV.Template').

(* The ReplicaSet [scaleReplicaSet] submits: the deep copy with nothing but the
   replica count overwritten. *)
Definition rs_scaled (rs : ReplicaSetV.t) (n : w32) : ReplicaSetV.t :=
  rs <| ReplicaSetV.Spec' := rs_scaled_spec rs n |>.

(* Rescaling preserves everything admission looks at. The replica count is the
   only field that changes, and a non-negative count is still admissible. *)
Lemma rs_scaled_spec_valid_create rs n :
  ReplicaSetSpecV.valid_create rs.(ReplicaSetV.Spec') →
  0 ≤ sint.Z n →
  ReplicaSetSpecV.valid_create (rs_scaled_spec rs n).
Proof.
  rewrite /ReplicaSetSpecV.valid_create /rs_scaled_spec /=.
  intros (_ & Hmin & Hsel & Htmpl) Hn. split_and!; done.
Qed.

Lemma rs_scaled_extra_valid rs n :
  ReplicaSetV.extra_valid rs →
  ReplicaSetV.extra_valid (rs_scaled rs n).
Proof.
  rewrite /ReplicaSetV.extra_valid /ReplicaSetSpecV.extra_valid
    /rs_scaled /rs_scaled_spec /=. done.
Qed.

Lemma rs_scaled_valid_named_create ns rs n :
  ReplicaSetV.valid rs →
  0 ≤ sint.Z n →
  ns = rs.(ReplicaSetV.ObjectMeta').(ObjectMetaV.Namespace') →
  ReplicaSetV.valid_named_create ns (rs_scaled rs n).
Proof.
  rewrite /ReplicaSetV.valid /ReplicaSetV.valid_named_create /rs_scaled /=.
  intros (Htm & _ & Hmeta & Hspec & _) Hn ->.
  split_and!.
  - eapply valid_typemeta_valid_create_typemeta. exact Htm.
  - eapply ObjectMetaV.valid_named_create_of_valid; done.
  - apply rs_scaled_spec_valid_create; [exact (proj1 Hspec)|exact Hn].
Qed.

(* A stored ReplicaSet always has an explicit replica count, so [rs_replicas]
   determines the field rather than merely defaulting it. *)
Lemma rs_replicas_of_valid rs :
  ReplicaSetV.valid rs →
  rs.(ReplicaSetV.Spec').(ReplicaSetSpecV.Replicas') = Some (rs_replicas rs).
Proof.
  intros (_ & _ & _ & Hspec & _).
  destruct Hspec as (_ & replicas & Hreplicas & _).
  rewrite /rs_replicas Hreplicas. done.
Qed.

(* [updated] is [created], which pins the stored count to the submitted one
   after defaulting. The submitted count is explicit here, so nothing defaults. *)
Lemma rs_scaled_spec_updated_replicas rs n stored :
  ReplicaSetSpecV.updated (rs_scaled_spec rs n) stored →
  stored.(ReplicaSetSpecV.Replicas') = Some n.
Proof.
  rewrite /ReplicaSetSpecV.updated /ReplicaSetSpecV.created /rs_scaled_spec /=.
  intros (Hreplicas & _). exact Hreplicas.
Qed.

Lemma deployment_replicas_nonneg d :
  DeploymentV.valid d →
  0 ≤ sint.Z (deployment_replicas d).
Proof.
  intros (_ & _ & _ & Hspec & _).
  destruct Hspec as ((replicas & Hreplicas & Hnonneg) & _).
  rewrite /deployment_replicas Hreplicas. exact Hnonneg.
Qed.

(* Stepping a prefix scan one element forward. *)
Lemma exists_take_S {A} (P : A → Prop) (l : list A) i x :
  l !! i = Some x →
  Exists P (take (S i) l) ↔ Exists P (take i l) ∨ P x.
Proof.
  intros Hx. rewrite (take_S_r _ _ _ Hx) Exists_app Exists_cons Exists_nil.
  tauto.
Qed.

(* An update that leaves the metadata alone is always admissible. *)
Lemma valid_simple_update_refl (m : ObjectMetaV.t) :
  ObjectMetaV.valid_simple_update m m.
Proof. rewrite /ObjectMetaV.valid_simple_update. split_and!; done. Qed.

(* The labels getNewReplicaSet stamps onto the new ReplicaSet's template, and
   the selector it derives, both add the pod-template-hash binding. *)
Definition new_rs_labels (d : DeploymentV.t) : gmap go_string go_string :=
  <[deployment_unique_label_key := template_hash (deployment_template d)]>
    (default ∅
      (deployment_template d).(PodTemplateSpecV.ObjectMeta').(ObjectMetaV.Labels')).

Definition new_rs_selector (d : DeploymentV.t) : option LabelSelectorV.t :=
  (λ selector, selector_with_label selector
     deployment_unique_label_key (template_hash (deployment_template d)))
  <$> d.(DeploymentV.Spec').(DeploymentSpecV.Selector').

Definition new_rs_name (d : DeploymentV.t) : go_string :=
  d.(DeploymentV.ObjectMeta').(ObjectMetaV.Name') ++ "-"%go ++
    template_hash (deployment_template d).

Definition new_rs_key (d : DeploymentV.t) : KKey.t :=
  {|
    KKey.Kind' := ReplicaSetV.kind;
    KKey.Namespace' := d.(DeploymentV.ObjectMeta').(ObjectMetaV.Namespace');
    KKey.Name' := new_rs_name d
  |}.

(* The template stamped onto the new ReplicaSet: the deployment's, with the
   pod-template-hash label added. Note ComputeHash runs on the deep copy
   *before* the label is added, so the hash is of the deployment's template. *)
Definition new_rs_template (d : DeploymentV.t) : PodTemplateSpecV.t :=
  PodTemplateSpecV.mk
    ((deployment_template d).(PodTemplateSpecV.ObjectMeta')
       <| ObjectMetaV.Labels' := Some (new_rs_labels d) |>)
    (deployment_template d).(PodTemplateSpecV.Spec').

(* Stamping the pod-template-hash label preserves the match. This is the whole
   content of EqualIgnoreHash — that label is exactly the one it ignores — so
   it belongs with [template_matches] rather than being derivable from it, and
   it is stated here because [new_rs_template] is. *)
Axiom template_matches_new_rs_template : ∀ d,
  template_matches (new_rs_template d) (deployment_template d).

(* Characterizes the ReplicaSet getNewReplicaSet submits. Stated field-by-field
   because that is what the callers need: [rollout] only ever reads back the
   replica count and the template. *)
Definition is_new_replica_set (d : DeploymentV.t) (rs : ReplicaSetV.t) : Prop :=
  rs.(ReplicaSetV.ObjectMeta').(ObjectMetaV.Name') = new_rs_name d ∧
  rs.(ReplicaSetV.ObjectMeta').(ObjectMetaV.Namespace') =
    d.(DeploymentV.ObjectMeta').(ObjectMetaV.Namespace') ∧
  rs.(ReplicaSetV.ObjectMeta').(ObjectMetaV.Labels') = Some (new_rs_labels d) ∧
  obj_parent_ref_is (KObjectV.ReplicaSet rs) DeploymentV.kind
    d.(DeploymentV.ObjectMeta').(ObjectMetaV.Name')
    d.(DeploymentV.ObjectMeta').(ObjectMetaV.UID') ∧
  rs.(ReplicaSetV.Spec').(ReplicaSetSpecV.Replicas') =
    Some (deployment_replicas d) ∧
  rs.(ReplicaSetV.Spec').(ReplicaSetSpecV.MinReadySeconds') =
    d.(DeploymentV.Spec').(DeploymentSpecV.MinReadySeconds') ∧
  rs.(ReplicaSetV.Spec').(ReplicaSetSpecV.Selector') = new_rs_selector d ∧
  rs_template rs = new_rs_template d.

(* The ReplicaSet [getNewReplicaSet] submits, as a Gallina value. Parameterised
   by the owner reference because [NewControllerRef] is specified relationally
   rather than as a function, so the reference is not computable here. Every
   field the composite literal at deployment.go:135 leaves out is the zero
   value; the status is [ReplicaSetStatusV.zero], the model's stand-in for a
   zero-initialized status. *)
Definition new_replica_set (d : DeploymentV.t) (ref : OwnerReferenceV.t)
    : ReplicaSetV.t :=
  ReplicaSetV.mk
    (zero_val _)
    (ObjectMetaV.mk
      (new_rs_name d)
      ""%go
      d.(DeploymentV.ObjectMeta').(ObjectMetaV.Namespace')
      ""%go
      ""%go
      ""%go
      (W64 0)
      TimeV.zero
      None
      None
      (Some (new_rs_labels d))
      None
      (Some [ref])
      None
      None)
    (ReplicaSetSpecV.mk
      (Some (deployment_replicas d))
      d.(DeploymentV.Spec').(DeploymentSpecV.MinReadySeconds')
      (new_rs_selector d)
      (new_rs_template d))
    ReplicaSetStatusV.zero.

Lemma new_replica_set_is_new d ref :
  OwnerReferenceV.refers_to_controller ref DeploymentV.kind
    d.(DeploymentV.ObjectMeta').(ObjectMetaV.Name')
    d.(DeploymentV.ObjectMeta').(ObjectMetaV.UID') →
  is_new_replica_set d (new_replica_set d ref).
Proof.
  intros (Hkind & Hname & Huid & _ & Hcontroller).
  rewrite /is_new_replica_set /new_replica_set /rs_template /=.
  split_and!; try done.
  rewrite /obj_parent_ref_is /meta_parent_ref_is /meta_parent_ref /=.
  rewrite decide_True; first exact Hcontroller.
  rewrite Hkind Hname Huid. done.
Qed.

(* TRUSTED, and in the same family as [template_hash_respects_matches]:
   controller.ComputeHash formats an FNV-32a hash through
   rand.SafeEncodeString, which yields a short alphanumeric string. That the
   result is a legal label value is a property of code goose does not
   translate. *)
Axiom template_hash_valid_label_value :
  ∀ t, valid_label_value (template_hash t).

Lemma deployment_unique_label_key_valid :
  valid_label_name deployment_unique_label_key.
Proof.
  left.
  unfold valid_qualified_name, qualified_name_syntax.
  cbn. repeat split.
  all: unfold label_alphanumeric, label_extended_character,
    byte_underscore, byte_dot, byte_dash.
  Timeout 20 all: vm_compute.
  (* The true disjunct is the "neither Lt nor Gt" one; [intuition] commits to
     an earlier branch, so point at it. *)
  all: try (right; right; split; discriminate).
  all: try (left; right; right; split; discriminate).
  all: try (right; left; reflexivity).
  all: try discriminate.
  all: try done.
Qed.

Lemma new_rs_labels_valid d :
  valid_labels
    (deployment_template d).(PodTemplateSpecV.ObjectMeta').(ObjectMetaV.Labels') →
  valid_labels (Some (new_rs_labels d)).
Proof.
  rewrite /valid_labels /new_rs_labels. intros Hlabels.
  apply map_Forall_insert_2.
  - split; [apply deployment_unique_label_key_valid
           |apply template_hash_valid_label_value].
  - destruct ((deployment_template d).(PodTemplateSpecV.ObjectMeta').(ObjectMetaV.Labels'))
      as [m|]; [exact Hlabels|apply map_Forall_empty].
Qed.

(* The deployment's selector must not constrain the pod-template-hash label.

   This is a real precondition, not a technicality. getNewReplicaSet stamps
   that label onto the new ReplicaSet's template, and the API server checks
   that a ReplicaSet's selector matches its own template's labels. A match
   expression keyed on pod-template-hash — [DoesNotExist], or [NotIn] the value
   the hash happens to take — would be satisfied by the deployment's template
   and violated by the ReplicaSet's, so the create would be rejected. Upstream
   Kubernetes has the same hazard and avoids it by convention. *)
Definition selector_avoids_hash_label (selector : LabelSelectorV.t) : Prop :=
  ∀ req, req ∈ LabelSelectorV.match_expressions_list selector →
    req.(LabelSelectorRequirementV.Key') ≠ deployment_unique_label_key.

Lemma selected_label_new_rs_labels d k :
  k ≠ deployment_unique_label_key →
  LabelSelectorV.selected_label (Some (new_rs_labels d)) k =
  LabelSelectorV.selected_label
    (deployment_template d).(PodTemplateSpecV.ObjectMeta').(ObjectMetaV.Labels') k.
Proof.
  intros Hk.
  assert (deployment_unique_label_key ≠ k) as Hk'
    by (intros Hc; apply Hk; symmetry; exact Hc).
  rewrite /LabelSelectorV.selected_label /new_rs_labels.
  rewrite (lookup_insert_ne _ _ _ _ Hk').
  destruct ((deployment_template d).(PodTemplateSpecV.ObjectMeta').(ObjectMetaV.Labels'))
    as [m|]; [done|apply lookup_empty].
Qed.

Lemma requirement_matches_selected_label labels1 labels2 req :
  LabelSelectorV.selected_label labels1 req.(LabelSelectorRequirementV.Key') =
  LabelSelectorV.selected_label labels2 req.(LabelSelectorRequirementV.Key') →
  LabelSelectorV.requirement_matches labels1 req →
  LabelSelectorV.requirement_matches labels2 req.
Proof.
  rewrite /LabelSelectorV.requirement_matches. intros Heq. rewrite Heq. done.
Qed.

Lemma valid_namespace_non_empty ns :
  valid_namespace ns → ns ≠ ""%go.
Proof.
  intros [Hsyntax _]. destruct ns as [|b ns]; [contradiction|discriminate].
Qed.

Lemma valid_dns1123_subdomain_non_empty s :
  valid_dns1123_subdomain s → s ≠ ""%go.
Proof.
  intros [Hsyntax _]. destruct s as [|b s]; [contradiction|discriminate].
Qed.

(* The selector stamped onto the new ReplicaSet still matches its template:
   the same binding is added to both, and by [selector_avoids_hash_label] no
   match expression is watching that key. *)
Lemma new_rs_selector_matches d dsel :
  d.(DeploymentV.Spec').(DeploymentSpecV.Selector') = Some dsel →
  LabelSelectorV.matches dsel
    (deployment_template d).(PodTemplateSpecV.ObjectMeta').(ObjectMetaV.Labels') →
  selector_avoids_hash_label dsel →
  LabelSelectorV.matches
    (selector_with_label dsel deployment_unique_label_key
       (template_hash (deployment_template d)))
    (new_rs_template d).(PodTemplateSpecV.ObjectMeta').(ObjectMetaV.Labels').
Proof.
  intros Hdsel [Hml Hreq] Havoid.
  rewrite /new_rs_template /=. split.
  - rewrite /selector_with_label /LabelSelectorV.match_labels /=.
    intros key value Hkey.
    destruct (decide (key = deployment_unique_label_key)) as [->|Hne].
    + rewrite lookup_insert in Hkey. rewrite /new_rs_labels lookup_insert.
      exact Hkey.
    + assert (deployment_unique_label_key ≠ key) as Hne'
        by (intros Hc; apply Hne; symmetry; exact Hc).
      rewrite (lookup_insert_ne _ _ _ _ Hne') in Hkey.
      rewrite /new_rs_labels (lookup_insert_ne _ _ _ _ Hne').
      rewrite /LabelSelectorV.match_labels in Hml.
      destruct (dsel.(LabelSelectorV.MatchLabels')) as [req_m|] eqn:Hdm;
        simpl in Hkey.
      * destruct ((deployment_template d).(PodTemplateSpecV.ObjectMeta').(ObjectMetaV.Labels'))
          as [m|] eqn:Hlm; simpl.
        -- exact (Hml key value Hkey).
        -- rewrite Hml lookup_empty in Hkey. discriminate.
      * rewrite lookup_empty in Hkey. discriminate.
  - rewrite /selector_with_label /LabelSelectorV.match_expressions_list /=.
    apply Forall_forall. intros req Hin.
    eapply requirement_matches_selected_label.
    { symmetry. apply selected_label_new_rs_labels. apply Havoid.
      rewrite list_elem_of_In. exact Hin. }
    rewrite Forall_forall in Hreq. apply Hreq.
    rewrite /LabelSelectorV.match_expressions_list. exact Hin.
Qed.

(* The ReplicaSet getNewReplicaSet submits passes admission. *)
Lemma new_replica_set_valid_named_create d ref dsel :
  DeploymentV.valid d →
  valid_dns1123_subdomain (new_rs_name d) →
  d.(DeploymentV.Spec').(DeploymentSpecV.Selector') = Some dsel →
  selector_avoids_hash_label dsel →
  OwnerReferenceV.valid ref →
  ReplicaSetV.valid_named_create
    d.(DeploymentV.ObjectMeta').(ObjectMetaV.Namespace') (new_replica_set d ref).
Proof.
  intros Hd_valid Hname Hdsel Havoid Href.
  pose proof Hd_valid as (Htm & _ & Hmeta & Hspec & _).
  pose proof Hspec as (Hrepl & Hmin &
    (dsel0 & Hdsel0 & Hsel_valid & Hsel_ne & Hsel_match) & Htmpl).
  assert (dsel0 = dsel) as ->
    by (rewrite Hdsel in Hdsel0; injection Hdsel0; auto).
  rewrite /ReplicaSetV.valid_named_create /new_replica_set /=.
  split_and!.
  - apply zero_typemeta_valid_create.
  - rewrite /ObjectMetaV.valid_named_create /=. split_and!.
    + intros Hc. done.
    + apply valid_dns1123_subdomain_non_empty. exact Hname.
    + right. split; [right; left; done|exact Hname].
    + right. split; [|done].
      apply (ObjectMetaV.valid_namespace_of_valid _ Hmeta).
    + apply new_rs_labels_valid. exact (proj1 Htmpl).
    + done.
    + intros i1 i2 or1 or2 H1 H2 _ _.
      apply lookup_lt_Some in H1. apply lookup_lt_Some in H2.
      simpl in H1, H2. lia.
    + intros or Hin. apply list_elem_of_singleton in Hin as ->. exact Href.
    + done.
    + apply valid_managed_fields_none.
  - rewrite /ReplicaSetSpecV.valid_create /=. split_and!.
    + apply deployment_replicas_nonneg. exact Hd_valid.
    + exact Hmin.
    + exists (selector_with_label dsel deployment_unique_label_key
        (template_hash (deployment_template d))).
      rewrite /new_rs_selector Hdsel /=. split_and!.
      * done.
      * rewrite /LabelSelectorV.valid /selector_with_label /=. split.
        -- rewrite /valid_labels. apply map_Forall_insert_2;
             [split; [apply deployment_unique_label_key_valid
                     |apply template_hash_valid_label_value]|].
           pose proof (proj1 Hsel_valid) as Hsl.
           rewrite /valid_labels in Hsl.
           destruct (dsel.(LabelSelectorV.MatchLabels')) as [m|];
             [exact Hsl|apply map_Forall_empty].
        -- exact (proj2 Hsel_valid).
      * rewrite /LabelSelectorV.empty /selector_with_label /=.
        intros [[Hc|Hc] _]; [discriminate|].
        injection Hc as Hc. exact (insert_non_empty _ _ _ Hc).
      * apply new_rs_selector_matches;
          [exact Hdsel|exact Hsel_match|exact Havoid].
    + rewrite /PodTemplateSpecV.valid /new_rs_template /=. split_and!.
      * apply new_rs_labels_valid. exact (proj1 Htmpl).
      * exact (proj1 (proj2 Htmpl)).
      * exact (proj2 (proj2 Htmpl)).
Qed.

(* What getNewReplicaSet needs of the deployment's selector, in one place.

   The first conjunct is the pod-template-hash condition explained at
   [selector_avoids_hash_label]. The second is a size bound: the model's
   [extra_valid] caps a selector's label count plus expression count at
   2^63-1, and stamping the hash adds one label, so the bound has to hold of
   the stamped selector rather than the original. Both are conditions on the
   deployment the controller is handed, not facts about it. *)
Definition deployment_selector_admissible (d : DeploymentV.t) : Prop :=
  ∀ dsel, d.(DeploymentV.Spec').(DeploymentSpecV.Selector') = Some dsel →
    selector_avoids_hash_label dsel ∧
    LabelSelectorV.extra_valid
      (selector_with_label dsel deployment_unique_label_key
         (template_hash (deployment_template d))).

Lemma new_replica_set_extra_valid d ref :
  deployment_selector_admissible d →
  ReplicaSetV.extra_valid (new_replica_set d ref).
Proof.
  intros Hadm sel Hsel.
  rewrite /new_replica_set /= /new_rs_selector in Hsel.
  destruct (d.(DeploymentV.Spec').(DeploymentSpecV.Selector')) as [dsel|]
    eqn:Hdsel; last done.
  simpl in Hsel. injection Hsel as <-.
  exact (proj2 (Hadm dsel Hdsel)).
Qed.

(* ---------------------------------------------------------------- *)
(* Top-level predicates                                              *)
(* ---------------------------------------------------------------- *)

(* At most one of [rss] matches the deployment's template.

   This is a precondition, not a theorem: [findNewReplicaSet] returns the
   *first* match, so with two matching ReplicaSets a sync could pick either and
   the choice would not be stable across syncs. See notes/deployment-spec.md
   §2b. Carried by [wp_rollout] and [wp_syncDeployment]. *)
Definition unique_new_replica_set (d : DeploymentV.t) (rss : list ReplicaSetV.t)
    : Prop :=
  ∀ i j rs_i rs_j,
    rss !! i = Some rs_i → rss !! j = Some rs_j →
    template_matches (rs_template rs_i) (deployment_template d) →
    template_matches (rs_template rs_j) (deployment_template d) →
    i = j.

(* The deployment's desired state is realized by [rss]: some ReplicaSet carries
   the deployment's template and sits at its replica count, and every other one
   is drained to zero.

   SCOPE — decided, not an oversight. Reviewed 2026-08-27 (questions-08-20.md
   Q1) and deliberately left as template + replica count.

   What this does NOT say: nothing about the pod-template-hash machinery. A
   ReplicaSet satisfying [deployment_realized] need not carry the right name,
   labels, selector, or owner reference. [is_new_replica_set] below pins all
   eight fields, but it applies only to ReplicaSets this controller *creates*.

   Why it is not strengthened: a ReplicaSet adopted from the API server has
   whatever labels and selector its creator gave it, and this controller has no
   adoption logic to fix them up — adoption/release is on deployment.go's
   excluded-features list. Strengthening the predicate would therefore require
   either adding that logic or assuming adopted ReplicaSets already conform.

   What this costs, stated so a reader does not have to discover it: the
   top-level guarantee is convergence *up to template and replica count*. It
   does not by itself establish that the converged ReplicaSet selects the right
   Pods, which is where the end-to-end story would need it (Q10 — composition
   onto the ReplicaSet controller's triple). Any writeup should say this
   plainly; a reviewer will otherwise notice the gap unaided.

   Both top-level triples are stated over this predicate
   ([progress_spec] and [stability_spec] in top_level.v), as are
   [realized_found_at_count] and [realized_old_drained] in stability.v.
   Rescoping it means redoing those. *)
Definition deployment_realized (d : DeploymentV.t) (rss : list ReplicaSetV.t)
    : Prop :=
  ∃ new_rs,
    new_rs ∈ rss ∧
    template_matches (rs_template new_rs) (deployment_template d) ∧
    new_rs.(ReplicaSetV.Spec').(ReplicaSetSpecV.Replicas') =
      Some (deployment_replicas d) ∧
    Forall (λ rs,
      ReplicaSetV.key rs = ReplicaSetV.key new_rs ∨
      rs.(ReplicaSetV.Spec').(ReplicaSetSpecV.Replicas') = Some (W32 0)) rss.

End proof.
