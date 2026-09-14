(* Specification and proof of [slowStartBatch], the concurrent pod-creation
   loop of the ReplicaSet controller (copied verbatim from upstream
   pkg/controller/replicaset).

   [slowStartBatch] forks [batchSize] goroutines per batch, each calling the
   caller-provided closure [fn] once, and waits for the batch with a
   [sync.WaitGroup]. Errors are collected in a buffered channel. The closure
   we verify never fails (it creates one pod from the ReplicaSet's template),
   so no goroutine ever sends on the channel, the batch loop runs to
   completion, and exactly [count] pods are created.

   Concurrency in the proof: the parent's children-set fragment is shared by
   all goroutines of a batch through an Iris invariant. The model's create
   operation exposes a logically atomic specification
   ([wp_State__create_nameless_au]), so each goroutine opens the invariant only
   at the linearization point of its create. The invariant also holds the
   WaitGroup counter and the pods created so far; [Wait] extracts them once
   the counter reaches zero. *)
From New.proof Require Import prelude empty_ffi.
From New.proof.kubernetes_model Require Export create.
From New.proof.controllers.replicaset Require Export top_level.
From New.proof.kubernetes_types Require Export persist.
From New.proof Require Import sync.
From New.golang.theory Require Import chan.
From New.golang.theory.chan.au_spec Require Import chan_au_send.
From New.proof Require Import proof_prelude.

Section proof.
Context `{hG: !heapGS Σ} `{!ffi_semantics _ _}.
Context {sem : go.Semantics}
  {package_sem : code.controllers.replicaset.replicaset.Assumptions}.
Collection W := sem + package_sem.
#[local] Instance base_common_sem : common.Assumptions | 100 :=
  code.controllers.replicaset.replicaset.import_common_Assumption.
#[local] Instance controller_sem : controller.Assumptions :=
  code.controllers.replicaset.replicaset.import_controller_Assumption.
#[local] Instance runtime_sem :
    code.k8s_io.apimachinery.pkg.runtime.runtime.Assumptions :=
  controller.import_runtime_Assumption.
#[local] Instance runtime_object_underlying_eq :
    runtime.Object ≤u runtime.Objectⁱᵐᵖˡ.
Proof using package_sem. apply _. Qed.
#[local] Instance meta_object_underlying_eq :
    meta_v1.Object ≤u meta_v1.Objectⁱᵐᵖˡ.
Proof using package_sem. apply _. Qed.
#[local] Instance base_apimodel_sem : apimodel.Assumptions | 100 :=
  common.import_apimodel_Assumption.
#[local] Instance object_meta_v1_sem :
    code.k8s_io.apimachinery.pkg.apis.meta.v1.v1.Assumptions :=
  apimodel.import_apis_meta_v1_Assumption.
#[local] Instance object_apps_v1_sem :
    code.k8s_io.api.apps.v1.v1.Assumptions :=
  apimodel.import_api_apps_v1_Assumption.
#[local] Instance object_core_v1_sem :
    code.k8s_io.api.core.v1.v1.Assumptions :=
  code.k8s_io.api.apps.v1.v1.import_core_v1_Assumption.
#[local] Instance apimodel_sem : apimodel.Assumptions | 0.
Proof using package_sem.
  constructor; try exact object_core_v1_sem; try apply _.
Defined.
#[local] Instance common_sem : common.Assumptions | 0.
Proof using package_sem.
  constructor; try exact apimodel_sem; try apply _.
Defined.
#[local] Instance sync_sem : sync.Assumptions :=
  code.controllers.replicaset.replicaset.import_sync_Assumption.
Context `{!kubernetesModelG Σ}.
Context `{!KObjectV.ObjectInterfaceAssumptions}.
Local Set Default Proof Using "All".

Definition batchN : namespace := nroot .@ "rs_slow_start_batch".
Definition wgN : namespace := nroot .@ "rs_slow_start_wg".

(** Logically atomic pod creation through the model's [PodCreate], derived from
    [wp_State__create_nameless_au]. *)
Lemma wp_State__PodCreate_nameless_au γ l namespace pod_l pod parent_key parent_uid :
  ∀ Φ,
  ( is_pkg_init apimodel ∗
    "#Hisk" ∷ is_kubernetes γ l ∗
    "%Hvalid" ∷ ⌜ PodV.valid_create PodV.kind namespace pod ⌝ ∗
    "%Hname_empty" ∷ ⌜ pod.(PodV.ObjectMeta').(ObjectMetaV.Name') = ""%go ⌝ ∗
    "%Hns_eq" ∷ ⌜ namespace = parent_key.(KKey.Namespace') ⌝ ∗
    "%Hpr" ∷ ⌜ obj_parent_ref_is (KObjectV.Pod pod) parent_key.(KKey.Kind') parent_key.(KKey.Name') parent_uid ⌝ ∗
    "Hdeepown_l" ∷ PodV.deepown_l pod_l pod 1 ∗
    "Hau" ∷ (|={⊤,∅}=> ∃ children,
      "Hown_children_frag" ∷ own_children_frag γ parent_key parent_uid 1 children ∗
      "Hclose" ∷ (∀ pod_l' pod' key uid,
        ⌜ PodV.valid pod' ⌝ ∗
        ⌜ PodV.created namespace pod pod' ⌝ ∗
        ⌜ key = PodV.key pod' ⌝ ∗
        ⌜ key ∉ children ⌝ ∗
        ⌜ uid = pod'.(PodV.ObjectMeta').(ObjectMetaV.UID') ⌝ ∗
        PodV.deepown_l pod_l' pod' 1 ∗
        own_meta_frag γ key uid 1 pod'.(PodV.ObjectMeta') ∗
        own_spec_frag γ key uid 1 (ObjectSpecV.PodSpec pod'.(PodV.Spec')) ∗
        own_status_frag γ key uid 1 (ObjectStatusV.PodStatus pod'.(PodV.Status')) ∗
        own_unreserved_key_frag γ key ∗
        own_children_frag γ parent_key parent_uid 1 (children ∪ {[key]}) ∗
        own_children_frag γ key uid 1 ∅
        ={∅,⊤}=∗ ▷ Φ (#pod_l', #interface.nil)%V))
  ) -∗ WP l @! (go.PointerType apimodel.State) @! "PodCreate" #namespace #pod_l {{ Φ }}.
Proof.
  iIntros (Φ) "(#Hinit & H)". iNamed "H".
  wp_method_call. rewrite /apimodel.State__PodCreateⁱᵐᵖˡ. wp_call. wp_auto.
  iAssert (KObjectV.deepown_i (interface.mk (go.PointerType v1.Pod) #pod_l) (KObjectV.Pod pod) 1)
    with "[Hdeepown_l]" as "Hdeepown_i".
  { iExists pod_l. iSplit; [iPureIntro; apply KObjectV.valid_interface_Pod|]. iFrame. }
  wp_apply (wp_State__create_nameless_au
    γ l "Pod"%go namespace (interface.mk (go.PointerType v1.Pod) #pod_l)
    (KObjectV.Pod pod) parent_key parent_uid).
  iFrame "#".
  iSplit; [done|]. iSplit; [done|]. iSplit; [done|]. iSplit; [done|]. iSplit; [done|].
  iSplitL "Hdeepown_i"; [iExact "Hdeepown_i"|].
  iMod "Hau" as (children) "[Hown_children_frag Hclose]".
  iModIntro. iExists children. iFrame "Hown_children_frag".
  iIntros (i' kobj' key uid)
    "(%Hvalid' & %Hcreated & %Hkey_eq & %Hkey_fresh & %Huid_eq & Hdeepown_i &
      Hown_meta_frag & Hown_spec_frag & Hown_status_frag & #Hown_unreserved_key_frag &
      Hown_children_frag & Hown_grandchildren_frag)".
  destruct kobj' as [pod'|rs'|pvc'|sts']; try done.
  iDestruct "Hdeepown_i" as (pod_l') "[%Hi' Hdeepown_l']".
  iMod ("Hclose" $! pod_l' pod' key uid with
    "[$Hdeepown_l' $Hown_meta_frag $Hown_spec_frag $Hown_status_frag
      $Hown_unreserved_key_frag $Hown_children_frag $Hown_grandchildren_frag]") as "HΦ".
  { iPureIntro. split_and!; done. }
  iModIntro. iNext.
  unfold KObjectV.valid_interface in Hi'. destruct Hi' as [Hi' _]. rewrite Hi'.
  wp_auto.
  change (go.PointerType api_core_v1.Pod) with (go.PointerType v1.Pod).
  cbn [interface.ty interface.v].
  replace (if decide (go.PointerType v1.Pod = go.PointerType v1.Pod)
           then #pod_l' else #null)%V with (#pod_l')%V by
    (rewrite decide_True; done).
  replace (bool_decide (go.PointerType v1.Pod = go.PointerType v1.Pod)) with true by
    (symmetry; apply bool_decide_eq_true_2; done).
  wp_auto.
  iApply "HΦ".
Qed.

(** Logically atomic contract for one call of the closure passed to
    [slowStartBatch]: it creates exactly one living pod owned by the parent
    [(pk, puid)], updating the parent's children set at its linearization
    point, and returns a nil error. *)
Definition create_pod_au γ (pk : KKey.t) (puid : types.UID.t) (Φ : iProp Σ) : iProp Σ :=
  |={⊤,∅}=> ∃ children,
    "Hown_children_frag" ∷ own_children_frag γ pk puid 1 children ∗
    "Hclose" ∷ (∀ pod',
      ⌜ PodV.valid pod' ⌝ ∗
      ⌜ is_pod_alive pod' ⌝ ∗
      ⌜ PodV.key pod' ∉ children ⌝ ∗
      own_children_frag γ pk puid 1 (children ∪ {[PodV.key pod']}) ∗
      own_meta_frag γ (PodV.key pod') pod'.(PodV.ObjectMeta').(ObjectMetaV.UID') 1 pod'.(PodV.ObjectMeta') ∗
      own_unreserved_key_frag γ (PodV.key pod')
      ={∅,⊤}=∗ ▷ Φ).

Definition is_create_fn γ pk puid (fn : func.t) : iProp Σ :=
  □ (∀ Φ, create_pod_au γ pk puid (Φ #interface.nil) -∗ WP #fn #() {{ Φ }}).

(** Resources describing the pods created so far, on top of the parent's
    initial children set [keys0]. *)
Definition created_pods_res γ pk puid (keys0 : gset KKey.t) (created : list PodV.t) : iProp Σ :=
  "Hown_children_frag" ∷ own_children_frag γ pk puid 1 (keys0 ∪ list_to_set (PodV.key <$> created)) ∗
  "Hcreated_meta_frags" ∷ ([∗ list] pod ∈ created,
    own_meta_frag γ (PodV.key pod) pod.(PodV.ObjectMeta').(ObjectMetaV.UID') 1 pod.(PodV.ObjectMeta')) ∗
  "#Hcreated_unreserved_key_frags" ∷ ([∗ list] pod ∈ created, own_unreserved_key_frag γ (PodV.key pod)) ∗
  "%Hcreated_alive" ∷ ⌜ ∀ pod, pod ∈ created → is_pod_alive pod ⌝ ∗
  "%Hcreated_nodup" ∷ ⌜ NoDup (PodV.key <$> created) ⌝ ∗
  "%Hcreated_fresh" ∷ ⌜ ∀ pod, pod ∈ created → PodV.key pod ∉ keys0 ⌝.

(** Invariant shared by the goroutines of one batch of size [bs].
    - [γc] tokens: each goroutine holds one until it has created its pod.
    - [γd] tokens: a pool of [bs] tokens; a goroutine takes one when it
      creates its pod and returns it when it calls [Done], which proves that
      every [Done] is preceded by a creation.
    - [drained] records that [Wait] has extracted the created pods. *)
Definition batch_inv_body γ γwg γc γd γdr (bs : w64) pk puid keys0 : iProp Σ :=
  ∃ (ctr : w32) (ncreated ndone : nat) (drained : bool) (created : list PodV.t),
    "Hwg_ctr" ∷ own_WaitGroup γwg ctr ∗
    "Hcreate_toks" ∷ own_toks γc ncreated ∗
    "Hdone_pool" ∷ own_toks γd (sint.nat bs - ncreated + ndone) ∗
    "Hdrained_var" ∷ ghost_var γdr (1/2) drained ∗
    "%Hctr" ∷ ⌜ sint.Z ctr = sint.Z bs - Z.of_nat ndone ⌝ ∗
    "%Hncreated" ∷ ⌜ ncreated = length created ⌝ ∗
    "%Hcounts" ∷ ⌜ ndone ≤ ncreated ≤ sint.nat bs ⌝ ∗
    "%Hdrained" ∷ ⌜ drained = true → ndone = sint.nat bs ⌝ ∗
    "Hres" ∷ (⌜ drained = true ⌝ ∨ (⌜ drained = false ⌝ ∗ created_pods_res γ pk puid keys0 created)).

Lemma created_pods_res_snoc γ pk puid keys0 created pod' :
  PodV.valid pod' →
  is_pod_alive pod' →
  PodV.key pod' ∉ keys0 ∪ list_to_set (PodV.key <$> created) →
  (∀ pod, pod ∈ created → is_pod_alive pod) →
  NoDup (PodV.key <$> created) →
  (∀ pod, pod ∈ created → PodV.key pod ∉ keys0) →
  ([∗ list] pod ∈ created,
    own_meta_frag γ (PodV.key pod) pod.(PodV.ObjectMeta').(ObjectMetaV.UID') 1 pod.(PodV.ObjectMeta')) -∗
  ([∗ list] pod ∈ created, own_unreserved_key_frag γ (PodV.key pod)) -∗
  own_children_frag γ pk puid 1 (keys0 ∪ list_to_set (PodV.key <$> created) ∪ {[PodV.key pod']}) -∗
  own_meta_frag γ (PodV.key pod') pod'.(PodV.ObjectMeta').(ObjectMetaV.UID') 1 pod'.(PodV.ObjectMeta') -∗
  own_unreserved_key_frag γ (PodV.key pod') -∗
  created_pods_res γ pk puid keys0 (created ++ [pod']).
Proof.
  intros Hvalid Halive Hfresh Hcreated_alive Hcreated_nodup Hcreated_fresh.
  iIntros "Hcreated_meta_frags #Hcreated_unreserved_key_frags Hown_children_frag Hmeta #Hunres".
  rewrite /created_pods_res.
  iSplitL "Hown_children_frag".
  { iExactEq "Hown_children_frag". rewrite /named. f_equal.
    rewrite !fmap_app. simpl. Timeout 10 set_solver. }
  iSplitL "Hcreated_meta_frags Hmeta".
  { rewrite big_sepL_app big_sepL_singleton. iFrame. }
  iSplit.
  { rewrite big_sepL_app big_sepL_singleton. iFrame "#". }
  iPureIntro. split_and!.
  - intros pod Hpod. apply elem_of_app in Hpod as [Hpod|Hpod].
    + apply Hcreated_alive. done.
    + apply list_elem_of_singleton in Hpod. subst pod. done.
  - rewrite fmap_app /=. apply list.NoDup_app. split_and!.
    + done.
    + intros key Hkey Hkey'. apply list_elem_of_singleton in Hkey'. subst key.
      apply Hfresh. apply elem_of_union_r. apply elem_of_list_to_set. done.
    + apply NoDup_singleton.
  - intros pod Hpod. apply elem_of_app in Hpod as [Hpod|Hpod].
    + apply Hcreated_fresh. done.
    + apply list_elem_of_singleton in Hpod. subst pod. intros Hin.
      apply Hfresh. apply elem_of_union_l. done.
Qed.

Lemma created_pods_res_app γ pk puid keys0 created created0 :
  (∀ pod, pod ∈ created → is_pod_alive pod) →
  NoDup (PodV.key <$> created) →
  (∀ pod, pod ∈ created → PodV.key pod ∉ keys0) →
  ([∗ list] pod ∈ created,
    own_meta_frag γ (PodV.key pod) pod.(PodV.ObjectMeta').(ObjectMetaV.UID') 1 pod.(PodV.ObjectMeta')) -∗
  ([∗ list] pod ∈ created, own_unreserved_key_frag γ (PodV.key pod)) -∗
  created_pods_res γ pk puid (keys0 ∪ list_to_set (PodV.key <$> created)) created0 -∗
  created_pods_res γ pk puid keys0 (created ++ created0).
Proof.
  intros Halive Hnodup Hfresh. iIntros "Hmeta #Hunres". iNamed 1.
  rewrite /created_pods_res.
  iSplitL "Hown_children_frag".
  { iExactEq "Hown_children_frag". rewrite /named. f_equal.
    rewrite !fmap_app. Timeout 10 set_solver. }
  iSplitL "Hmeta Hcreated_meta_frags".
  { rewrite big_sepL_app. iFrame. }
  iSplit.
  { rewrite big_sepL_app. iFrame "#". }
  iPureIntro. split_and!.
  - intros pod Hpod. apply elem_of_app in Hpod as [Hpod|Hpod]; auto.
  - rewrite fmap_app. apply list.NoDup_app. split_and!; [done| |done].
    intros key Hk1 Hk2. apply list_elem_of_fmap in Hk2 as (pod & -> & Hpod).
    apply (Hcreated_fresh pod Hpod). apply elem_of_union_r. apply elem_of_list_to_set. done.
  - intros pod Hpod. apply elem_of_app in Hpod as [Hpod|Hpod]; [auto|].
    intros Hin. apply (Hcreated_fresh pod Hpod). apply elem_of_union_l. done.
Qed.

(** Builtin [min] on two [int]s. *)
Lemma wp_min_int (x y : w64) :
  {{{ True }}}
    #(functions go.min [go.int; go.int]) #x #y
  {{{ RET #(if decide (sint.Z x < sint.Z y) then x else y); True }}}.
Proof.
  wp_start as "_".
  try wp_pures.
  pose proof (go.min_unfold 2 go.int) as [Heq]. simpl in Heq.
  iEval (rewrite Heq). wp_auto.
  wp_if_destruct.
  - iEval (rewrite (decide_True x y l)) in "HΦ". iApply "HΦ". done.
  - assert (¬ (sint.Z x < sint.Z y)) as Hnlt by word.
    iEval (rewrite (decide_False x y Hnlt)) in "HΦ". iApply "HΦ". done.
Qed.

Lemma wp_slowStartBatch γ pk puid keys0 (count initial : w64) (fn : func.t) :
  {{{ "#Hpkg" ∷ is_pkg_init code.controllers.replicaset.pkg_id.replicaset ∗
      "#Hfn" ∷ is_create_fn γ pk puid fn ∗
      "Hown_children_frag" ∷ own_children_frag γ pk puid 1 keys0 ∗
      "%Hcount" ∷ ⌜ 0 ≤ sint.Z count < 2^31 ⌝ ∗
      "%Hinitial" ∷ ⌜ 0 < sint.Z initial ⌝
  }}}
    @! replicaset.slowStartBatch #count #initial #fn
  {{{ (successes : w64) (created : list PodV.t), RET (#successes, #interface.nil);
      "%Hcreated_len" ∷ ⌜ length created = sint.nat count ⌝ ∗
      created_pods_res γ pk puid keys0 created
  }}}.
Proof.
  wp_start as "H". iNamed "H".
  wp_auto.
  iPersist "fn".
  wp_apply wp_min_int. try wp_auto.
  set I := (∃ (remaining successes batchSize : w64) (created : list PodV.t),
    "remaining" ∷ remaining_ptr ↦ remaining ∗
    "successes" ∷ successes_ptr ↦ successes ∗
    "batchSize" ∷ batchSize_ptr ↦ batchSize ∗
    "Hres" ∷ created_pods_res γ pk puid keys0 created ∗
    "%Hremaining" ∷ ⌜ 0 ≤ sint.Z remaining ≤ sint.Z count ⌝ ∗
    "%Hcreated_len" ∷ ⌜ Z.of_nat (length created) = sint.Z count - sint.Z remaining ⌝ ∗
    "%HbatchSize" ∷ ⌜ 0 ≤ sint.Z batchSize ≤ sint.Z remaining ⌝ ∗
    "%HbatchSize_zero" ∷ ⌜ sint.Z batchSize = 0 → sint.Z remaining = 0 ⌝)%I.
  iAssert I with "[remaining successes batchSize Hown_children_frag]" as "Hloop_inv".
  { iExists count, (W64 0), _, []. iFrame.
    iSplitL.
    { rewrite /created_pods_res /= right_id_L. iFrame.
      iSplit; [done|]. iSplit; [done|]. iPureIntro. split_and!.
      - intros pod Hpod. inversion Hpod.
      - constructor.
      - intros pod Hpod. inversion Hpod. }
    iPureIntro. split_and!; try word.
    all: try (simpl; lia).
    all: try (case_decide; intros; word). }
  wp_for "Hloop_inv". wp_if_destruct.
  - (* one batch of [batchSize] goroutines *)
    wp_apply chan.wp_make2; first word.
    iIntros (ch γch) "(#His_chan & _ & Hoc)".
    assert (batchSize ≠ W64 0) as Hbs_nz by (intros ->; word).
    iEval (rewrite (decide_False _ _ Hbs_nz)) in "Hoc".
    try wp_auto.
    iMod (init_WaitGroup wgN with "wg") as (γwg) "(#His_wg & Hwg_ctr & Hwg_waiters)".
    wp_apply (wp_WaitGroup__Add with "[$His_wg]"). try iPkgInit.
    iApply fupd_mask_intro; [solve_ndisj|]. iIntros "Hmask". iNext.
    iExists (W32 0). iFrame "Hwg_ctr". iSplit; [word|].
    iRight. iFrame "Hwg_waiters". iIntros "Hwg_waiters Hwg_ctr".
    iMod "Hmask" as "_". iModIntro.
    try wp_auto.
    (* ghost state for the batch *)
    iMod own_tok_auth_alloc as (γc) "Hauth_c".
    iMod (own_tok_auth_add (sint.nat batchSize) with "Hauth_c") as "[Hauth_c Hcreate_toks]".
    iPersist "Hauth_c".
    iMod own_tok_auth_alloc as (γd) "Hauth_d".
    iMod (own_tok_auth_add (sint.nat batchSize) with "Hauth_d") as "[Hauth_d Hdone_pool]".
    iPersist "Hauth_d".
    iMod (ghost_var_alloc false) as (γdr) "[Hdrained Hdrained_inv]".
    iNamedSuffix "Hres" "_old".
    set keysb := (keys0 ∪ list_to_set (PodV.key <$> created)).
    iMod (own_toks_0 γc) as "Hcreate_toks0".
    iMod (inv_alloc batchN _ (batch_inv_body γ γwg γc γd γdr batchSize pk puid keysb)
      with "[Hwg_ctr Hcreate_toks0 Hdone_pool Hdrained_inv Hown_children_frag_old]") as "#Hbinv".
    { iNext. iExists _, 0%nat, 0%nat, false, [].
      iFrame "Hwg_ctr Hcreate_toks0".
      rewrite Nat.sub_0_r Nat.add_0_r. iFrame "Hdone_pool Hdrained_inv".
      iSplitR; [iPureIntro; rewrite Z.sub_0_r; word|].
      iSplitR; [done|].
      iSplitR; [iPureIntro; lia|].
      iSplitR; [iPureIntro; discriminate|].
      iRight. iSplit; [done|].
      rewrite /created_pods_res /= right_id_L. iFrame "Hown_children_frag_old".
      iSplit; [done|]. iSplit; [done|]. iPureIntro. split_and!.
      - intros pod Hpod. inversion Hpod.
      - constructor.
      - intros pod Hpod. inversion Hpod. }
    (* fork the goroutines *)
    iAssert (∃ (i : w64),
      "i" ∷ i_ptr ↦ i ∗
      "Hcreate_toks" ∷ own_toks γc (sint.nat batchSize - sint.nat i) ∗
      "%Hi" ∷ ⌜ 0 ≤ sint.Z i ≤ sint.Z batchSize ⌝)%I
      with "[i Hcreate_toks]" as "Hinner_inv".
    { iExists (W64 0). rewrite Nat.sub_0_r. iFrame. word. }
    wp_for "Hinner_inv". wp_if_destruct.
    + replace (sint.nat batchSize - sint.nat i)%nat
        with ((sint.nat batchSize - sint.nat (word.add i (W64 1))) + 1)%nat by word.
      iDestruct (own_toks_add with "Hcreate_toks") as "[Hcreate_toks Htok_c]".
      wp_apply (wp_fork with "[Htok_c]").
      { (* the goroutine *)
        wp_pures.
        wp_apply wp_with_defer as "%defer defer". simpl subst.
        wp_auto.
        wp_bind (#fn #())%E.
        iApply "Hfn".
        rewrite /create_pod_au.
        iInv "Hbinv" as ">Hi" "Hclose_inv".
        iApply fupd_mask_intro; [solve_ndisj|]. iIntros "Hmask".
        iNamedSuffix "Hi" "_inv".
        (* the batch has not been drained: this goroutine still holds a create token *)
        iCombine "Hcreate_toks_inv Htok_c" as "Hcreate_toks_inv".
        iCombine "Hauth_c Hcreate_toks_inv" gives %Hcreate_le.
        iDestruct "Hres_inv" as "[%Hdr|[%Hdr Hres_inv]]".
        { exfalso. specialize (Hdrained_inv Hdr). lia. }
        subst drained.
        iNamedSuffix "Hres_inv" "_res".
        iExists _. iFrame "Hown_children_frag_res".
        iIntros (pod') "(%Hvalid' & %Halive' & %Hfresh' & Hown_children_frag & Hmeta & #Hunres)".
        iMod "Hmask" as "_".
        (* take a done token out of the pool *)
        replace (sint.nat batchSize - ncreated + ndone)%nat
          with ((sint.nat batchSize - (ncreated + 1) + ndone) + 1)%nat by lia.
        iDestruct (own_toks_add with "Hdone_pool_inv") as "[Hdone_pool_inv Htok_d]".
        iDestruct (created_pods_res_snoc with
          "Hcreated_meta_frags_res Hcreated_unreserved_key_frags_res
           Hown_children_frag Hmeta Hunres") as "Hres_inv";
          [done|done|done|done|done|done|].
        iMod ("Hclose_inv" with
          "[Hwg_ctr_inv Hcreate_toks_inv Hdone_pool_inv Hdrained_var_inv Hres_inv]") as "_".
        { iNext. iExists ctr, (ncreated + 1)%nat, ndone, false, (created0 ++ [pod']).
          iFrame "Hwg_ctr_inv Hcreate_toks_inv Hdone_pool_inv Hdrained_var_inv".
          iSplitR; [iPureIntro; done|].
          iSplitR; [iPureIntro; rewrite length_app /=; lia|].
          iSplitR; [iPureIntro; lia|].
          iSplitR; [iPureIntro; discriminate|].
          iRight. iSplit; [done|]. iFrame "Hres_inv". }
        iModIntro. iNext.
        wp_auto.
        (* the deferred wg.Done() *)
        wp_apply (wp_WaitGroup__Done with "[$His_wg]"). try iPkgInit.
        iInv "Hbinv" as ">Hi" "Hclose_inv".
        iApply fupd_mask_intro; [solve_ndisj|]. iIntros "Hmask". iNext.
        iNamedSuffix "Hi" "_wg".
        iCombine "Hdone_pool_wg Htok_d" as "Hdone_pool_wg".
        iCombine "Hauth_d Hdone_pool_wg" gives %Hdone_le.
        assert (Z.of_nat (sint.nat batchSize) = sint.Z batchSize) as Hbs_nat by word.
        iExists _. iFrame "Hwg_ctr_wg".
        iSplit; [iPureIntro; word|].
        iIntros "Hwg_ctr_wg".
        iMod "Hmask" as "_".
        iEval (rewrite -Nat.add_assoc) in "Hdone_pool_wg".
        iMod ("Hclose_inv" with
          "[Hwg_ctr_wg Hcreate_toks_wg Hdone_pool_wg Hdrained_var_wg Hres_wg]") as "_".
        { iNext. iExists _, _, (_ + 1)%nat, _, _.
          iFrame "Hwg_ctr_wg Hcreate_toks_wg Hdone_pool_wg Hdrained_var_wg Hres_wg".
          iPureIntro. split_and!.
          all: try word.
          all: try lia.
          all: intros Hdr; exfalso; specialize (Hdrained_wg Hdr); lia. }
        iModIntro. wp_auto. done. }
      wp_for_post. iFrame. iPureIntro. word.
    + (* all goroutines forked: wait for them *)
      try wp_auto.
      iApply fupd_wp.
      iMod fupd_mask_subseteq as "Hmask";
        last iMod (alloc_wait_token _ _ _ 0 with "His_wg Hwg_waiters") as "[Hwg_waiters Hwait_tok]".
      { solve_ndisj. }
      { word. }
      iMod "Hmask" as "_". iModIntro.
      wp_apply (wp_WaitGroup__Wait with "[$His_wg $Hwait_tok]"). try iPkgInit.
      iInv "Hbinv" as ">Hi" "Hclose_inv".
      iApply fupd_mask_intro; [solve_ndisj|]. iIntros "Hmask". iNext.
      iNamedSuffix "Hi" "_inv".
      iExists ctr. iFrame "Hwg_ctr_inv".
      iIntros "%Hctr_zero Hwg_ctr_inv".
      iDestruct (ghost_var_agree with "Hdrained Hdrained_var_inv") as %<-.
      iDestruct "Hres_inv" as "[%Hdr|[_ Hres_inv]]"; first discriminate.
      iCombine "Hauth_c Hcreate_toks_inv" gives %Hcreate_le.
      iMod (ghost_var_update_halves true with "Hdrained Hdrained_var_inv")
        as "[Hdrained Hdrained_var_inv]".
      iMod "Hmask" as "_".
      iMod ("Hclose_inv" with
        "[Hwg_ctr_inv Hcreate_toks_inv Hdone_pool_inv Hdrained_var_inv]") as "_".
      { iNext. iExists ctr, ncreated, ndone, true, created0.
        iFrame "Hwg_ctr_inv Hcreate_toks_inv Hdone_pool_inv Hdrained_var_inv".
        iSplitR; [iPureIntro; done|].
        iSplitR; [iPureIntro; done|].
        iSplitR; [iPureIntro; done|].
        iSplitR; [iPureIntro; intros _; lia|].
        iLeft. done. }
      iModIntro. iIntros "Hwait_tok".
      assert (length created0 = sint.nat batchSize) as Hcreated0_len by lia.
      (* the error channel is untouched: no goroutine failed *)
      wp_auto.
      wp_func_call. wp_call.
      wp_apply (wp_Len with "[$His_chan]"). iIntros (len1) "%Hlen1".
      wp_auto.
      wp_func_call. wp_call.
      wp_apply (wp_Len with "[$His_chan]"). iIntros (len2) "%Hlen2".
      wp_auto.
      wp_if_destruct.
      { (* receiving from the empty buffered channel blocks forever *)
        wp_bind (chan.receive _ _)%E.
        iApply (chan.wp_receive with "[$His_chan]").
        iIntros "_". rewrite /recv_au.
        iApply fupd_mask_intro; [set_solver|]. iIntros "_". iNext.
        iExists (chanstate.Buffered []). by iFrame "Hoc". }
      try wp_auto.
      wp_for_post.
      wp_apply wp_min_int. try wp_auto.
      iDestruct (created_pods_res_app with
        "Hcreated_meta_frags_old Hcreated_unreserved_key_frags_old Hres_inv") as "Hres";
        [done|done|done|].
      iFrame "HΦ".
      iExists (word.sub remaining batchSize), _, _, (created ++ created0).
      iFrame "remaining successes batchSize Hres".
      assert (Z.of_nat (sint.nat batchSize) = sint.Z batchSize) as Hbs_nat by word.
      assert (sint.Z (word.sub remaining batchSize) = sint.Z remaining - sint.Z batchSize)
        as Hsub by word.
      iPureIntro. split_and!; try word.
      all: try (rewrite length_app Nat2Z.inj_add Hcreated0_len; lia).
      all: try (case_decide; intros; word).
  - (* batchSize = 0: nothing left to create *)
    assert (sint.Z remaining = 0) as Hrem0 by (apply HbatchSize_zero; word).
    assert (Z.of_nat (sint.nat count) = sint.Z count) as Hcount_nat by word.
    try wp_auto.
    iApply ("HΦ" $! successes created).
    iFrame. iPureIntro. lia.
Qed.

End proof.
