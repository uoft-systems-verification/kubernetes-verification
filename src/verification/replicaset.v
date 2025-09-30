From verification Require Import prelude empty_ffi.
From verification Require Import replicaset_init.
Require Import New.code.k8s_io.api.core.v1.
Require Import New.code.k8s_io.api.apps.v1.
Require Import New.code.k8s_io.apimachinery.pkg.apis.meta.v1.
Require Import New.code.k8s_io.kubernetes.pkg.controller.


Section proof.
Context `{hG: !heapGS Σ}.
Context `{!globalsGS Σ} {go_ctx: GoContext}.

Lemma wp_PodKey (pod: loc) (name namespace: go_string) :
  {{{ is_pkg_init replicaset ∗
      struct.field_ref_f v1.Pod "ObjectMeta" pod ↦s[v1.ObjectMeta :: "Name"] name ∗
      struct.field_ref_f v1.Pod "ObjectMeta" pod ↦s[v1.ObjectMeta :: "Namespace"] namespace
  }}}
    @! controller.PodKey #pod
  {{{ RET #(namespace ++ "/" ++ name)%go;
      struct.field_ref_f v1.Pod "ObjectMeta" pod ↦s[v1.ObjectMeta :: "Name"] name ∗
      struct.field_ref_f v1.Pod "ObjectMeta" pod ↦s[v1.ObjectMeta :: "Namespace"] namespace
  }}}.
Proof.
Admitted.

(* TODO: add the precondition on p *)
Lemma wp_IsPodActive (p: loc) :
  {{{ is_pkg_init replicaset }}}
    @! controller.IsPodActive #p
  {{{ (v: bool), RET #v; True }}}.
Proof.
Admitted.

Lemma wp_Now :
  {{{ is_pkg_init replicaset }}}
    @! v1.Now #()
  {{{ (now: v1.Time.t), RET #now; True }}}.
Proof.
Admitted.

Lemma wp_getPodsRankedByRelatedPodsOnSameNode (podsToRank relatedPods: slice.t) (podsToRank_els relatedPods_els: list loc) :
  {{{ is_pkg_init replicaset ∗
      "podsToRank" :: podsToRank ↦* podsToRank_els ∗
      "relatedPods" :: relatedPods ↦* relatedPods_els ∗
      "podsToRank_els" :: ([∗ list] pod_l ∈ podsToRank_els,
        ∃ (nodename: go_string),
          struct.field_ref_f v1.Pod "Spec" pod_l ↦s[v1.PodSpec :: "NodeName"] nodename) ∗
      "relatedPods_els" :: ([∗ list] pod_l ∈ relatedPods_els,
        ∃ (nodename: go_string),
          struct.field_ref_f v1.Pod "Spec" pod_l ↦s[v1.PodSpec :: "NodeName"] nodename)
  }}}
    @! replicaset.getPodsRankedByRelatedPodsOnSameNode #podsToRank #relatedPods
  {{{ ranks now,
      RET #{| 
        controller.ActivePodsWithRanks.Pods' := podsToRank;
        controller.ActivePodsWithRanks.Rank' := ranks;
        controller.ActivePodsWithRanks.Now' := now;
      |};
      podsToRank ↦* podsToRank_els ∗
      ([∗ list] pod_l ∈ podsToRank_els,
        ∃ (nodename: go_string),
          struct.field_ref_f v1.Pod "Spec" pod_l ↦s[v1.PodSpec :: "NodeName"] nodename)
  }}}.
Proof.
  wp_start as "H". iNamed "H".
  wp_alloc relatedPods_l as "relatedPods_l". wp_pures.
  wp_alloc podsToRank_l as "podsToRank_l". wp_pures.
  wp_alloc podsOnNode_l as "podsOnNode_l". wp_pures.
  wp_apply (wp_map_make (K:=go_string) (V:=w64)); [done..|].
  iIntros (podsOnNode) "podsOnNode". wp_auto.
  iRename "pod" into "pod_ptr".
  Transparent slice.for_range. wp_call.
  wp_auto.
  iRename "i" into "i_ptr".
  iDestruct (own_slice_len with "relatedPods") as %relatedPodslen.
  set I := (
    ∃ (i: w64) (p: loc) (m: gmap go_string w64),
      "i_ptr" :: i_ptr ↦ i ∗
      "pod_ptr" :: pod_ptr ↦ p ∗
      "podsOnNode" :: podsOnNode ↦$ m ∗
      "%Hi" :: ⌜0 ≤ sint.Z i ≤ sint.Z (slice.len_f relatedPods)⌝
  )%I.
  iAssert (I) with "[i_ptr pod_ptr podsOnNode]" as "Hinv".
  {
    iExists (W64 0), (default_val loc), ∅.
    iFrame.
    iPureIntro.
    word.
  }
  wp_for "Hinv".
  wp_if_destruct; wp_auto.
  - wp_pure.
    { word. }
    assert ((sint.nat i < length relatedPods_els)%nat) as HlenrelatedPods_els by word.
    pose proof (list_lookup_lt relatedPods_els (sint.nat i) HlenrelatedPods_els) as [x Hx].
    wp_apply (wp_load_slice_elem with "[$relatedPods]") as "relatedPods".
    { word. }
    {
      iPureIntro.
      exact Hx.
    }
    wp_apply wp_IsPodActive.
    iIntros (v) "_".
    destruct v; wp_auto.
    + iDestruct (big_sepL_lookup_acc with "relatedPods_els") as "[x others]".
      { exact Hx. }
      iDestruct "x" as (nodename) "x".
      wp_auto.
      wp_apply (wp_map_get with "[$podsOnNode]").
      iIntros "podsOnNode". wp_auto.
      wp_apply (wp_map_insert with "[$podsOnNode]").
      iIntros "podsOnNode". wp_auto.
      iAssert ((
        [∗ list] pod_l ∈ relatedPods_els,
          ∃ nodename : go_string,
            struct.field_ref_f v1.Pod "Spec" pod_l ↦s[v1.PodSpec :: "NodeName"] nodename
        )%I) with "[x others]" as "relatedPods_els".
      {
        iApply "others".
        iExists nodename.
        iFrame.
      }
      iApply wp_for_post_do. wp_auto.
      iFrame.
      iPureIntro. word.
    + iApply wp_for_post_do. wp_auto.
      iFrame.
      iPureIntro. word.
  - iClear "i_ptr".
    iClear "pod_ptr".
    clear pod_ptr i_ptr i n Hi I.
    iDestruct (own_slice_len with "podsToRank") as %podsToRanklen.
    wp_apply (wp_slice_make2 (V:=w64)).
    { iPureIntro. word. }
    iRename "ranks" into "ranks_ptr".
    iIntros (ranks) "[ranks rankscap]". wp_auto.
    iDestruct (own_slice_len with "ranks") as %rankslen.
    rewrite length_replicate in rankslen.
    iRename "pod" into "pod_ptr".
    iRename "i" into "i_ptr".
    Transparent slice.for_range. wp_call.
    wp_alloc j_ptr as "j_ptr". wp_auto.
    set I := (
      ∃ (i: w64) (j: w64) (p: loc) (ranks_els: list w64) (m: gmap go_string w64),
        "i_ptr" :: i_ptr ↦ i ∗
        "j_ptr" :: j_ptr ↦ j ∗
        "pod_ptr" :: pod_ptr ↦ p ∗
        "ranks" :: ranks ↦* ranks_els ∗
        "podsOnNode" :: podsOnNode ↦$ m ∗
        "%Hj" :: ⌜0 ≤ sint.Z j ≤ sint.Z (slice.len_f podsToRank)⌝ ∗
        "%rankslen" :: ⌜sint.nat (slice.len_f podsToRank) = sint.nat (slice.len_f ranks)
          ∧ length ranks_els = sint.nat (slice.len_f ranks)
          ∧ 0 ≤ sint.Z (slice.len_f ranks)⌝
    )%I.
    iAssert (I) with "[i_ptr j_ptr pod_ptr ranks podsOnNode]" as "Hinv".
    {
      iExists (default_val w64), (W64 0), (default_val loc), (replicate (sint.nat (slice.len_f podsToRank)) (default_val w64)), m.
      iFrame.
      iPureIntro.
      rewrite length_replicate.
      word.
    }
    wp_for "Hinv".
    wp_if_destruct; wp_auto.
    + wp_pure.
      { word. }
      assert ((sint.nat j < length podsToRank_els)%nat) as HlenpodsToRank_els by word.
      pose proof (list_lookup_lt podsToRank_els (sint.nat j) HlenpodsToRank_els) as [x Hx].
      wp_apply (wp_load_slice_elem with "[$podsToRank]") as "podsToRank".
      { word. }
      {
        iPureIntro.
        exact Hx.
      }
      iDestruct (big_sepL_lookup_acc with "podsToRank_els") as "[x others]".
      { exact Hx. }
      iDestruct "x" as (nodename) "x". wp_auto.
      wp_apply (wp_map_get with "[$podsOnNode]").
      iIntros "podsOnNode". wp_auto.
      wp_pure.
      { word. }
      assert ((sint.nat j < length ranks_els)%nat) as Hlenranks_els by word.
      pose proof (list_lookup_lt ranks_els (sint.nat j) Hlenranks_els) as [y Hy].
      wp_apply (wp_store_slice_elem with "[$ranks]") as "ranks".
      { word. }
      iAssert ((
        [∗ list] pod_l ∈ podsToRank_els,
          ∃ nodename : go_string,
            struct.field_ref_f v1.Pod "Spec" pod_l ↦s[v1.PodSpec :: "NodeName"] nodename
        )%I) with "[x others]" as "podsToRank_els".
      {
        iApply "others".
        iExists nodename.
        iFrame.
      }
      iApply wp_for_post_do. wp_auto.
      iFrame.
      iSplit; iPureIntro.
      { word. }
      { rewrite length_insert. word. }
    + wp_apply wp_Now.
      iIntros (now) "_". wp_auto.
      iApply "HΦ".
      iFrame.
Qed.

Lemma wp_getPodKeys (pods: slice.t) (pods_els: list loc) :
  {{{ is_pkg_init replicaset ∗
      "pods" :: pods ↦* pods_els ∗
      "pods_els" :: ([∗ list] pod_l ∈ pods_els,
        ∃ (name namespace: go_string),
          struct.field_ref_f v1.Pod "ObjectMeta" pod_l ↦s[v1.ObjectMeta :: "Name"] name ∗
          struct.field_ref_f v1.Pod "ObjectMeta" pod_l ↦s[v1.ObjectMeta :: "Namespace"] namespace)
  }}}
    @! replicaset.getPodKeys #pods
  {{{ (keys: slice.t) (keys_els: list go_string), RET #keys;
    pods ↦* pods_els ∗
    keys ↦* keys_els ∗
    ⌜length keys_els = length pods_els⌝ ∗
    ([∗ list] i ↦ pod_l; key ∈ pods_els; keys_els,
      ∃ (name namespace: go_string),
        struct.field_ref_f v1.Pod "ObjectMeta" pod_l ↦s[v1.ObjectMeta :: "Name"] name ∗
        struct.field_ref_f v1.Pod "ObjectMeta" pod_l ↦s[v1.ObjectMeta :: "Namespace"] namespace ∗
        ⌜key = (namespace ++ "/" ++ name)%go⌝)
  }}}.
Proof.
  wp_start as "H". iNamed "H".
  iDestruct (own_slice_len with "pods") as %Hlen.
  wp_alloc pods_l as "pods_l". wp_auto.
  iRename "podKeys" into "podKeys_ptr".
  wp_apply (wp_slice_make3 (V:=go_string)).
  {  word. }
  iIntros (keys) "(keys & own_keys_cap & %Heq)". wp_auto.
  iRename "pod" into "pod_ptr".
  (* unfold slice.for_range to a loop *)
  Transparent slice.for_range. wp_call.
  wp_alloc i_ptr as "i_ptr".
  wp_pures.

  set I := (
    ∃ (i: w64) (keys: slice.t) (p: loc) (keys_els: list go_string),
      "i_ptr" :: i_ptr ↦ i ∗
      "podKeys_ptr" :: podKeys_ptr ↦ keys ∗
      "pod_ptr" :: pod_ptr ↦ p ∗
      "keys" :: keys ↦* keys_els ∗
      "own_keys_cap" :: own_slice_cap go_string keys (DfracOwn 1) ∗
      "%Hrange" :: ⌜0 ≤ sint.Z i ≤ sint.Z (slice.len_f pods)⌝ ∗
      "%Hlen_keys" :: ⌜length keys_els = sint.nat i⌝ ∗
      "Hprei" :: ([∗ list] j ↦ pod_l; key ∈ take (sint.nat i) pods_els; keys_els,
        ∃ (name namespace: go_string),
          struct.field_ref_f v1.Pod "ObjectMeta" pod_l ↦s[v1.ObjectMeta :: "Name"] name ∗
          struct.field_ref_f v1.Pod "ObjectMeta" pod_l ↦s[v1.ObjectMeta :: "Namespace"] namespace ∗
          ⌜key = (namespace ++ "/" ++ name)%go⌝) ∗
      "Hposti" :: ([∗ list] pod_l ∈ drop (sint.nat i) pods_els,
        ∃ (name namespace: go_string),
          struct.field_ref_f v1.Pod "ObjectMeta" pod_l ↦s[v1.ObjectMeta :: "Name"] name ∗
          struct.field_ref_f v1.Pod "ObjectMeta" pod_l ↦s[v1.ObjectMeta :: "Namespace"] namespace)
  )%I.

  iAssert (I) with "[podKeys_ptr pod_ptr keys own_keys_cap pods_els i_ptr]" as "Hinv".
  {
    iExists (W64 0), keys, (default_val loc), [].
    iFrame "podKeys_ptr pod_ptr keys own_keys_cap i_ptr".
    iSplit; [iPureIntro; word|].
    iSplit; [iPureIntro; done|].
    iSplit.
    - rewrite take_0. by rewrite big_sepL2_nil.
    - rewrite drop_0. iFrame "pods_els".
  }

  wp_for "Hinv".
  iDestruct (own_slice_len with "pods") as %Hslicelen.

  wp_if_destruct; try wp_auto.
  - wp_bind (![# ptrT] (slice.elem_ref (# ptrT) (# pods) (# i)))%E.
    wp_pure.
    { word. }
    assert ((sint.nat i < length pods_els)%nat) as Hi by word.
    pose proof (list_lookup_lt pods_els (sint.nat i) Hi) as [x Hx].

    wp_apply (wp_load_slice_elem with "[$pods]") as "pods_i".
    { word. }
    { iPureIntro. exact Hx. }

    (* split "drop (uint.nat i) pods_els" into "x" and "drop (uint.nat (word.add i (W64 1))) pods_els" *)
    iAssert (
      (([∗ list] pod_l ∈ drop (sint.nat (word.add i (W64 1))) pods_els,
        ∃ name namespace : go_string,
          struct.field_ref_f v1.Pod "ObjectMeta" pod_l ↦s[v1.ObjectMeta :: "Name"] name ∗
          struct.field_ref_f v1.Pod "ObjectMeta" pod_l ↦s[v1.ObjectMeta :: "Namespace"] namespace) ∗
        (∃ name : go_string, struct.field_ref_f v1.Pod "ObjectMeta" x ↦s[v1.ObjectMeta :: "Name"] name) ∗
        (∃ namespace : go_string, struct.field_ref_f v1.Pod "ObjectMeta" x ↦s[v1.ObjectMeta :: "Namespace"] namespace))%I
    ) with "[Hposti]" as "(Hpostiaddone & ((%name & name) & (%namespace & namespace)))".
    {
      iEval (rewrite (drop_S _ _ _ Hx)) in "Hposti".
      iDestruct "Hposti" as "[Hhead Htail]".
      assert (sint.nat (word.add i (W64 1)) = S (sint.nat i)) as Hsucc by word.
      iEval (rewrite -Hsucc) in "Htail".
      iFrame.
      iDestruct "Hhead" as (name namespace) "[Hname Hnamespace]".
      iSplitL "Hname".
      { iExists name. iExact "Hname". }
      { iExists namespace. iExact "Hnamespace". }
    }

    wp_apply (wp_PodKey with "[$name $namespace]") as "[name namespace]".
    wp_apply (wp_slice_literal) as "%sl sl".
    wp_apply (wp_slice_append with "[$keys $own_keys_cap $sl]") as "%new_keys (new_keys & own_new_keys_cap & sl)".
    (* loop body finished here *)
    set new_keys_els := keys_els ++ [(namespace ++ "/" ++ name)%go].
    (* combine "x" and "take (sint.nat i) pods_els" into "take (sint.nat (word.add i (W64 1)))" *)
    iAssert (
      ([∗ list] pod_l;key ∈ take (sint.nat (word.add i (W64 1))) pods_els;new_keys_els,
        ∃ name namespace : go_string,
          struct.field_ref_f v1.Pod "ObjectMeta" pod_l ↦s[v1.ObjectMeta :: "Name"] name ∗
          struct.field_ref_f v1.Pod "ObjectMeta" pod_l ↦s[v1.ObjectMeta :: "Namespace"] namespace ∗
          ⌜key = namespace ++ "/"%go ++ name⌝)%I
    ) with "[Hprei name namespace]" as "Hpreiaddone".
    {
      assert (sint.nat (word.add i (W64 1)) = S (sint.nat i)) as Hsucc by word.
      rewrite Hsucc.
      rewrite (take_S_r _ _ _ Hx).
      rewrite big_sepL2_app.
      iApply "Hprei".
      simpl.
      iSplit; [|done].
      iExists name, namespace.
      iFrame.
      iPureIntro. reflexivity.
    }
    iApply wp_for_post_do. wp_auto.
    iFrame "pods_i pods_l HΦ".
    (* Prove the loop invariant *)
    iExists (word.add i (W64 1)), new_keys, x, new_keys_els.
    iFrame.
    iSplit; iPureIntro.
    + word.
    + rewrite app_length Hlen_keys /=.
      word.
  - iApply "HΦ".
    iFrame.
    iSplit.
    { iPureIntro. word. }
    assert (length pods_els ≤ sint.nat i).
    { word. }
    rewrite take_ge.
    { word. }
    iFrame.
Qed.

End proof.
