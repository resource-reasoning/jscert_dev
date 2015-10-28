Set Implicit Arguments.
Require Import LibBag LibTactics LibFset LibReflect LibList LibLogic.

(****** Basic Set Properties ******)

Section Basic.
Variables A : Type.
Implicit Types E F: fset A.
Implicit Types x y : A.


Lemma in_and_notin: forall E x y, 
  x \in E -> y \notin E -> x <> y.
Proof.
  introv H1 H2 H3. rewrite H3 in H1. false.
Qed.

(*This theorem its declared on LibFset but not recognized here*)
(*Added the other implication making it an iff*)
Axiom fset_extens_iff : forall E F,
  (forall x, x \in E = x \in F) <-> E = F.

Lemma fset_neq: forall E F,
  (exists x, x \in E /\ x \notin E \n F) -> E <> F.
Proof.
  introv H. destruct H as (x & Hin & Hni). introv H.
  lets K: fset_extens_iff E F. destruct K as (_ & H0). specializes H0 H x.
  apply Hni. rewrite in_inter. split~.
    rewrite~ <- H0.
Qed.

Lemma empty_dec: forall E, 
  E = \{} \/ E <> \{}.
Proof.
  intro. lets (l & Hl): (fset_finite E). cases l.
    rewrite from_list_nil in Hl. left~.
    rewrite from_list_cons in Hl. right. rewrite Hl.
    introv H. rewrite <- fset_extens_iff in H. specializes H a.
    rewrite in_empty in H. rewrite <- H.
    rewrite in_union. left. rewrite~ in_singleton.
Qed.

Lemma singleton_absurd: forall x, 
  \{x} <> \{}.
Proof.
  introv. apply fset_neq. exists x. split.
    rewrite~ in_singleton.
    unfolds. introv H. rewrite inter_empty_r in H. rewrite~ in_empty in H.
Qed.

End Basic.



(****** Remove Properties ******)

Section Remove.
Variables A : Type. 
Implicit Types E F G: fset A.
Implicit Types x: A.


Lemma notin_remove : forall E F x, 
  x \notin E \- F -> x \notin E \/ x \in F.
Proof.
  introv H.
  unfolds notin.
  rewrite in_remove in H. 
  rew_logic in H. unfolds notin. rew_logic~ in H.
Qed.

Lemma remove_while_notin: forall E x, 
  x \notin E -> E \- \{x} = E.
Proof.
  introv H; apply fset_extens; unfold subset; introv H1.
    rewrite in_remove in H1. destruct~ H1.
    rewrite in_remove. split~. rewrite notin_singleton. applys* in_and_notin.
Qed.

Lemma remove_in_subsets: forall E F G, 
  E \c F -> E \- G \c F \- G.
Proof.
  introv H.
    unfolds subset. introv H1. rewrite in_remove. split.
      apply H. rewrite in_remove in H1. apply H1.
      rewrite in_remove in H1. apply H1.
Qed.

Lemma remove_comm: forall E F G, 
  (E \- F) \- G = (E \- G) \- F.
Proof.
  introv. apply fset_extens; unfold subset; intro; rewrite_all in_remove; introv H; intuition.
Qed.    

Lemma remove_same: forall E, 
  (E \- E) = \{}.
Proof.
  introv. apply fset_extens; unfold subset; intro; rewrite in_remove; introv H.
    false H. apply H.
    rewrite in_empty in H. false.
Qed.

Lemma remove_empty: forall E, 
  E \- \{} = E.
Proof.
  introv. apply fset_extens; unfold subset; intro; rewrite in_remove; introv H.
    apply H.
    split~.
      apply notin_empty.
Qed.

Lemma remove_from_empty: forall E, 
  (\{} \- E) = \{}.
Proof.
  introv. apply fset_extens; unfold subset; intro; rewrite in_remove; introv H.
    apply H.
    split.
      apply H.
      rewrite in_empty in H. false.
Qed.

Lemma from_rem_to_union: forall E F x, Comparable A ->
  x \in F -> E = F \- \{x} -> \{x} \u E = F.
Proof.
  introv Hcmp H1 H2; apply fset_extens; unfold subset; introv H3.
    rewrite in_union in H3. destruct H3.
      rewrite in_singleton in H. rewrite~ H.
      rewrite H2 in H. rewrite* in_remove in H.
    rewrite in_union. eapply fset_extens_iff in H2. erewrite H2.
      rewrite in_remove. rewrite in_singleton. rewrite notin_singleton.
      destruct Hcmp. specializes comparable x x0. destruct comparable as (b & dec).
      destruct b.
        apply eq_true_l in dec. rewrite istrue_isTrue in dec. subst. left~.
        apply eq_false_l in dec. rewrite istrue_neg in dec. rewrite istrue_isTrue in dec. right~.
Qed.

Lemma rem_union_cancel: forall E x, Comparable A ->
  x \in E -> E \- \{x} \u \{x} = E.
Proof.
  introv Hcmp H. apply fset_extens; unfold subset; intros y H'.
    rewrite in_union in H'. destruct H'.
      rewrite in_remove in H0. destruct~ H0.
      rewrite in_singleton in H0. subst~.
    rewrite in_union. destruct Hcmp. specializes comparable x y.
      destruct comparable as (b & dec). destruct b.
        apply eq_true_l in dec. rewrite istrue_isTrue in dec. subst.
        right. rewrite~ in_singleton.
        apply eq_false_l in dec. rewrite istrue_neg in dec. rewrite istrue_isTrue in dec.
        left. rewrite in_remove. rewrite notin_singleton. split~.
Qed.

Lemma remove_union: forall E F G,
  E \- (F \u G) = (E \- F) \- G.
Proof.
  introv.
  apply fset_extens; unfold subset; intro; rewrite_all in_remove; introv H.
    rewrite* notin_union in H.
    rewrite* notin_union.
Qed.
 
Lemma remove_union_distr : forall E F G,
  (E \- G) \u (F \- G) = (E \u F) \- G.
Proof.
  introv; apply fset_extens; introv Hin; 
  rewrite in_union in *; rewrite in_remove in *; inverts Hin; intuition; 
  try rewrite in_union in *; try rewrite in_remove in *; try inverts H; jauto.
Qed.

Lemma remove_union_comm : forall E F x,
 x \notin F -> (E \- F) \u \{x} = (E \u \{x}) \- F.
Proof.
  introv Hnin; apply fset_extens; introv Hin;
  rewrite in_remove in *; rewrite in_union in *; rewrite in_remove in *;
  inverts Hin; jauto.
  rewrite in_singleton in H; subst; splits~.
    right; rewrites~ in_singleton.
  inverts H; jauto.
Qed.

End Remove.



(****** Union Properties ******)

Section Union.
Variables A : Type. 
Implicit Types E F G: fset A.
Implicit Types x y: A.


Lemma union_already_in: forall E x,  
  x \in E -> \{x} \u E = E.
Proof.
  introv H. apply fset_extens; unfold subset; intros y H'.
    rewrite in_union in H'. destruct~ H'.
      rewrite in_singleton in H0. subst~.
    rewrite in_union. right~.
Qed.

Lemma union_empty: forall E F, 
  E \u F = \{} -> E=\{} /\ F = \{}.
Proof.
  introv H. split.
    rewrite <- H. apply fset_extens; unfolds; introv H0.
      rewrite in_union. left~.
      eapply fset_extens_iff in H. rewrite H in H0. false. rewrite~ in_empty in H0.
    rewrite <- H. apply fset_extens; unfolds; introv H0.
      rewrite in_union. right~.
      eapply fset_extens_iff in H. rewrite H in H0. false. rewrite~ in_empty in H0.
Qed.

Lemma from_union_to_rem: forall E F x, 
  x \notin E -> \{x} \u E = F -> E = F \- \{x}.
Proof.
  introv H1 H2; apply fset_extens; unfold subset; introv H3.
    rewrite <- H2. rewrite union_comm. rewrite union_remove. rewrite in_union.
      left. rewrite~ remove_while_notin.
    rewrite <- H2 in H3. rewrite union_comm in H3. rewrite union_remove in H3.
      rewrite in_union in H3. destruct H3. rewrite~ remove_while_notin in H.
      rewrite remove_same in H. rewrite* in_empty in H.
Qed.

Lemma union_subset: forall E F G, 
  (E \u F) \c G -> E \c G.
Proof.
  unfold subset; introv H Hin.
    apply H. rewrite in_union. left~.
Qed.

Lemma union_inv: forall E x y, 
  \{x} \u E = \{y} -> x = y.
Proof.
  introv H.
  lets H': fset_extens_iff. specializes H' A  (\{ x} \u E) (\{ y}).
  destruct H'. specializes H1 H x. rewrite in_union in H1.
  rewrite_all in_singleton in H1. rewrite <- H1.
  left~.
Qed.

Lemma singleton_union: forall E F x, 
  \{x} = E \u F -> x \in E \/ x \in F.
Proof.
  introv H.
  lets H': fset_extens_iff. specializes H' A  \{ x} (E \u F).
  destruct H'. specializes H1 H x. rewrite in_singleton in H1.
  assert (x \in E \u F). rewrite~ <- H1. clear H1.
  rewrite~ in_union in H2.
Qed.

Lemma union_not_empty: forall E F, 
  E \u F <> \{} <-> E <> \{} \/ F <> \{}.
Proof.
  split. introv H.
  destruct (empty_dec F).
    left. rewrite <- (union_empty_r E). rewrite <- H0 at 1. assumption.
    right~.
  introv H1 H2. apply union_empty in H2. destruct H2 as (H2 & H3).
  destruct H1 ; apply~ H.
Qed.

End Union.


(****** Inter Properties ******)

Section Inter.
Variables A : Type. 
Implicit Types E F G: fset A.

Lemma inter_union: forall E F G,
  (E \u F) \n G = \{} -> E \n G = \{} /\ F \n G = \{}.
Proof.
  introv H. split; apply fset_extens; rewrite <- fset_extens_iff in H; unfolds subset;
  introv H1; specializes H x; rewrite in_inter in *.
    rewrite <- H. rewrite in_union. split*.
    rewrite in_empty in H1. false.
    rewrite <- H. rewrite in_union. split*.
    rewrite in_empty in H1. false.
Qed.

Lemma inter_remove: forall E F, (E \- F) \n F = \{}.
Proof.
  introv. apply fset_extens; unfolds subset; introv H;
  rewrite in_inter in *; rewrite in_remove in *.
    false H. apply H.
    rewrite in_empty in H. false.
Qed.

Lemma inter_not_empty_exists : forall E F,
  E \n F <> \{} -> exists x, x \in E \n F.
Proof.
  introv Hneq.
  elim (classic (exists x, x \in E \n F)); introv Hnex; jauto.
  false; apply Hneq.
  apply fset_extens; introv Hin.
  rewrite in_empty; rewrite* not_exists in Hnex.
  rewrite* in_empty in Hin.
Qed.

Lemma inter_empty_subset : forall E1 E2 F1 F2, 
  E1 \n E2 = \{} -> F1 \c E1 -> F2 \c E2 -> F1 \n F2 = \{}.
Proof.
  introv Hie Hs1 Hs2.
    rewrite <- fset_extens_iff in Hie.
    apply fset_extens; introv Hin.
    rewrite in_inter in Hin; inverts Hin; apply Hs1 in H; apply Hs2 in H0.
    rewrite <- (Hie x); rewrites* in_inter.
    rewrite* in_empty in Hin.
Qed.

End Inter.

(****** Subset Properties ******)

Section Subset.
Variables A : Type. 
Implicit Types E F: fset A.
Implicit Types x: A.


Lemma fset_eq_sub: forall E F, 
  E = F -> E \c F.
Proof.
  introv H.
  rewrite H.
  apply subset_refl.
Qed.

Lemma subset_of_empty: forall E, 
  E \c \{} -> E = \{}.
Proof.
  introv H. apply fset_extens; unfolds subset; introv H1.
    specializes~ H H1.
    rewrite in_empty in H1. false.
Qed.

Lemma subset_union_r: forall E F x, 
  x \notin E -> E \c (\{x} \u F) = E \c F.
Proof.
  introv H. unfolds subset. rew_logic. split; introv H1 H2.
    specializes H1 x0 H2. rewrite in_union in H1. destruct~ H1.
      rewrite in_singleton in H0. subst. false~ H.
    specializes H1 x0 H2. rewrite~ in_union.
Qed.


End Subset.



(****** From List Properties ******)

Section FromList.
Variables A : Type. 
Implicit Types E F : fset A.
Implicit Types l : list A.
Implicit Types x : A.


Lemma from_list_notin : forall l x, 
  ~Mem x l -> x \notin from_list l.
Proof.
  induction l; introv Hnm.
    rewrite from_list_nil. apply notin_empty.
    rewrite from_list_cons. rewrite notin_union. split.
      unfold notin. introv H. apply Hnm. rewrite in_singleton in H. rewrite H. apply Mem_here.
      apply IHl. introv H. apply Hnm. constructor~.
Qed.

(*This theorem its declared on LibFset but not recognized here*)

Lemma from_list_spec : forall x l,
  x \in from_list l = Mem x l.
Proof.
  unfold from_list. induction l; rew_list.
  rewrite in_empty. rewrite~ Mem_nil_eq. 
  rewrite in_union, in_singleton. rewrite~ Mem_cons_eq. congruence.
Qed.

Lemma from_list_base: forall l, 
  from_list l = \{} -> l = nil.
Proof.
  introv H. induction~ l.
    rewrite from_list_cons in H. apply union_empty in H. false.
    destruct H. eapply fset_extens_iff in H. rewrite in_singleton in H.
    rewrite in_empty in H. rewrite~ <- H.
Qed.

Lemma from_list_app : forall l1 l2,
  from_list (l1 ++ l2) = from_list l1 \u from_list l2.
Proof.
  introv; apply fset_extens; introv Hin; rewrite in_union in *; 
    repeat rewrite from_list_spec in *; rewrite Mem_app_or_eq in *; auto.   
Qed.

End FromList.


