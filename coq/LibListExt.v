Set Implicit Arguments. 
Generalizable Variables A B.

Require Import LibReflect LibTactics LibList LibListSorted LibNat LibFset LibFsetExt LibVar.



(** Fixing implicit arguments *)

Implicit Arguments nil [[A]].
Implicit Arguments cons [[A]].


(****** Definitions ******)

Section Defs.

Variables A B : Type.
Implicit Types E : fset A.
Implicit Types l t : list A.
Implicit Types x : A. 

(* to_list (magically) transforms a finite set into a list *)
Parameter to_list : fset A -> list A.

(* Removing one occurrence of an element in a list *)
Fixpoint removeOne x l :=
  match l with
   | nil     => nil
   | y :: l' => If (x = y)
                    then l' 
                    else y :: (removeOne x l')
  end.

(* Removing one occurrence of all the elements from a given list in a given list *)
Fixpoint removeN l t :=
  match l with
   | nil     => t
   | y :: l' => removeOne y (removeN l' t)
  end.

(* Checking if there are duplicate elements in the list *)
Fixpoint noDup l :=
  match l with
   | nil     => True
   | y :: l' => ~(Mem y l') /\ (noDup l')
  end.

(* Removing duplicate elements from a list *)
Fixpoint remDup l :=
  match l with
   | nil     => nil
   | y :: l' => If (Mem y l') 
                    then remDup l' 
                    else y :: (remDup l')
  end.

(* Counting the number of occurrences of an element in a list *)
Fixpoint count x l :=
  match l with
   | nil     => 0
   | y :: l' => (If (x = y) 
                     then 1 
                     else 0) + count x l'
  end.

End Defs.

Implicit Arguments removeOne [[A]].
Implicit Arguments removeN [[A]].
Implicit Arguments noDup [[A]].
Implicit Arguments remDup [[A]].
Implicit Arguments count [[A]].

(****** Count Properties ******)

Section Count.
Variables A: Type.
Implicit Types E : fset A.
Implicit Types l : list A.
Implicit Types x : A. 

(* No elements occur in nil *)
Lemma count_nil : forall x, count x nil = 0.
Proof. auto. Qed.

(* Count and positive cons *)
Lemma count_cons_pos : forall x l, count x (x :: l) = 1 + count x l.
Proof. introv; simpl; cases_if*. Qed.

(* Compatibility of count with positive cons *)
Lemma count_cons_cancel : forall x l1 l2, count x (x :: l1) = count x (x :: l2) -> count x l1 = count x l2.
Proof. introv; repeat rewrite count_cons_pos; nat_math. Qed.

(* IMPORTANT : An element is a member in a list IFF it occurs in the list at least once *)
Lemma count_Mem : forall x l, 
  count x l > 0 <-> Mem x l.
Proof.
  induction l.
    simpl; split; intro H. 
      nat_math.
      rewrites* Mem_nil_eq in H.
      simpl; cases_if.
      splits; try nat_math.
      intros _; constructor.
      rewrite plus_0_l; rewrite IHl.
      rewrite Mem_cons_eq; splits*.
Qed.

(* Compatibility of count and append *)
Lemma count_app_plus : forall x l1 l2, count x (l1 ++ l2) = count x l1 + count x l2.
Proof.
  inductions l1; introv.
    rewrite app_nil_l; simpls~.
    specialize (IHl1 l2); rewrite app_cons; simpls~; cases_if*; nat_math.
Qed.

End Count.

(****** Mem Properties ******)

(* Decision procedure for var membership *)
Fixpoint Mem_dec (a : var) (l : list var) : bool :=
  match l with
    | nil => false
    | (x :: l) => ifb (a = x) then true else (Mem_dec a l)
  end.

(* Finding out if a var is in a list is decidable *)
Instance Mem_var_decidable : forall (a : var) (l : list var), Decidable (Mem a l).  
Proof.
  intros.  
  applys~ decidable_make (Mem_dec a l).
  induction l; simpls~.
    symmetry; rewrite Mem_nil_eq; applys~ isTrue_false.
    cases_if~; subst; rewrites isTrue_def; cases_if*.
      false; apply H; constructor.
      inverts H; try solve [false].
      rewrites IHl; applys~ isTrue_true.
      rewrites IHl; rewrite Mem_cons_eq in H; rew_logic in H.
      applys* isTrue_false.      
Qed.
 
(****** Rem Dup Properties ******)

Section RemDup.
Variables A: Type.
Implicit Types E : fset A.
Implicit Types l : list A.
Implicit Types x : A. 

(* If the removal of duplicate elements results in nil, the original list was also nil *)
Lemma remdup_inv: forall l, remDup l = nil -> l = nil.
Proof.
  introv H. induction l; simpls~. cases_if.
  apply IHl in H. subst. false. rewrite~ Mem_nil_eq in H0.
Qed.

(* All the elements are preserved (but not their count) once we have removed duplicates *)
Lemma mem_remdup: forall l x, Mem x (remDup l) -> Mem x l.
Proof.
  induction l; simpls~. cases_if~; simpls; introv Hm.
    constructor. applys~ IHl.
    rewrite Mem_cons_eq in *. destruct Hm.
      left~.
      right~.
Qed.

(* In fact, we can go a little stronger *)
Lemma mem_remdup_iff: forall l x, 
  Mem x (remDup l) <-> Mem x l.
Proof.
  introv; split; intro Hm; [applys~ mem_remdup | ].
  induction l; simpls~; cases_if*; rewrite Mem_cons_eq in Hm; inverts* Hm; constructor~.      
Qed.

(* There are no duplicates in the list from which we have removed duplicates *)
Lemma nodup_remdup: forall l,
  noDup (remDup l).
Proof.
  introv. induction l; simpls~.
    cases_if~. simpls. split~.
      introv H'. apply H. apply~ mem_remdup.
Qed.          
    
(* from_list does not take into account duplicate elements *)
Lemma remdup_eq_fl: forall l,
  from_list l = from_list (remDup l).
Proof.
  induction l; simpls~; cases_if; rewrite_all from_list_cons.
    rewrite <- IHl. rewrite~ union_already_in.
    rewrite~ from_list_spec. rewrite~ IHl.
Qed.

(* For every finite set, we can find a corresponding list which has no duplicate elements *)
Lemma fset_nodup : forall E,
  exists L, E = from_list L /\ noDup L.
Proof.
  introv.
  lets (L & HL): fset_finite A E.
  exists (remDup L). split.
    rewrite~ <- remdup_eq_fl.
    apply nodup_remdup.
Qed.

End RemDup.

(****** List Elementary Facts ******)

Section ListBasic.
Variables A: Type.
Implicit Types l t r s : list A.
Implicit Types n : nat.

(* If the length of the list is 0, the list is nil *)
Lemma length0 : forall l, length l = 0 -> l = nil.
Proof.
  introv.
  induction l.
    reflexivity.
    simpl. introv H. exfalso. discriminate.
Qed.

(* If the length of the list is not zero, we can guarantee the existence of at least one element in it *)
Lemma lengthn : forall l n,
  length l = S n -> exists y ys, l = y::ys .
Proof.
  introv.
  induction l.
    simpls. introv H. exfalso. rewrite length_nil in H. nat_math.
    introv H. exists~ a l.
Qed.

(* If there is an element occurring in the list, the length of the list is not zero *)
Lemma mem_len_pos : forall l x, Mem x l -> length l > 0.
Proof.
  introv Hm. induction l.
    false. rewrite~ Mem_nil_eq in Hm.
    rew_list. nat_math.
Qed.

(* If an element is a member of a list, it is also a member in any list resulting from appending to the right *)
Lemma mem_app_inv1: forall l t u x, l = t ++ u -> Mem x t -> Mem x l.
Proof.
  introv H Hm. rewrite H. rewrite Mem_app_or_eq. left~.
Qed.

(* If an element is a member of a list, it is also a member in any list resulting from appending to the left *)
Lemma mem_app_inv2: forall l t u x, l = t ++ u -> Mem x u -> Mem x l.
Proof.
  introv H Hm. rewrite H. rewrite Mem_app_or_eq. right~.
Qed.

(* Compatibility of equality with append  *)
Lemma length_app_inv: forall l t r s,
  length l = length r -> length t = length s -> l ++ t= r ++ s ->
    l = r /\  t = s.
Proof.
  induction l; introv Hl1 Hl2 Hb.
    symmetry in Hl1. apply length0 in Hl1. rewrite Hl1 in Hb. split~.
    remember Hl1. clear Heqe. rewrite length_cons in e.
    symmetry in e. apply lengthn in e. destruct e as ( y & ys & Hr).
    subst. rew_app in Hb. inverts Hb.
    assert (length l = length ys); auto.
    specializes IHl (>> t ys s H Hl2 H1). destruct IHl.
    subst~.
Qed.

(* IMPORTANT : The relationship between Forall and Mem *)
Lemma Forall_Mem : forall l (P : A -> Prop),
  (forall x, Mem x l -> P x) <-> Forall P l.
Proof.
  split; induction l; try constructor~.
    assert (Mem a (a :: l)) by constructor; auto.
    apply IHl; intros x Hm.
    specialize (H x); assert (Mem x (a :: l)) by constructor~; auto.
    introv _ Hm; rewrites* Mem_nil_eq in Hm.
    introv Hf Hm; inverts Hf.
    inverts~ Hm.
Qed. 

End ListBasic.

(****** Remove One/ Remove N Properties ******)

Section RemoveOne.
Variables A: Type.
Implicit Types E : fset A.
Implicit Types l : list A.
Implicit Types x : A.

(* If an element is in the list after removal, it was there before as well  *)
Lemma mem_rem1_l: forall l x y, Mem x (removeOne y l) -> Mem x l.
Proof.
  induction l; introv Hm; simpls~.
    cases_if.
      constructor~.
      rewrite Mem_cons_eq in *. destruct* Hm.
Qed.

(* All elements different from the one removed remain in the list *)
Lemma mem_rem1_r: forall l x y, x <> y -> Mem x l -> Mem x (removeOne y l).
Proof.
  induction l; introv Hne Hm; simpls~.
    cases_if; rewrite Mem_cons_eq in *; destruct* Hm.
Qed.      

(* Removal is idempotent in the presence of absence *)
Lemma rem1_notin_list: forall l x,
  ~Mem x l -> removeOne x l = l.
Proof.
  introv H. induction l; simpls~.
    cases_if.
      false H. constructor.
      rewrite~ IHl. introv H'. apply H. constructor~.
Qed.

(* In a list with no duplicates, once you remove the element once, it has really been removed *)
Lemma from_list_rem1: forall l x, noDup l ->
  from_list l \- \{x} = from_list (removeOne x l).
Proof.
  introv Hnd. induction l; simpls.
    rewrite_all from_list_nil. apply remove_from_empty.
    cases_if; rewrite_all from_list_cons.
      rewrite union_remove. rewrite remove_same. rewrite union_empty_l. rewrite* IHl.
        rewrite* rem1_notin_list.
      rewrite union_remove. rewrite remove_while_notin.
        rewrite* IHl.
        rewrite~ notin_singleton.
Qed.

(* Length decreases by one after a successful removal *)
Lemma length_rem1 : forall l x,
  Mem x l -> length (removeOne x l) = length l - 1.
Proof.
  induction l; introv Hm.
    simpls~.
    rewrite length_cons. simpls. cases_if~.
      nat_math.
      rewrite length_cons. rewrite Mem_cons_eq in Hm. destruct* Hm. rewrite~ IHl.
        apply mem_len_pos in H0. nat_math.
Qed.

(* removeOne is commutative *)
Lemma rem1_comm: forall l x y,
  removeOne x (removeOne y l) = removeOne y (removeOne x l).
Proof.
  induction l; introv ; simpls~.
    cases_if; cases_if~; simpls~; cases_if~; cases_if~.
      rewrite~ IHl.
Qed.

(* removeOne commutes with Mem as well *)
Lemma rem1_mem_comm: forall l x y, Mem x l ->
Mem y (removeOne x l) -> Mem x (removeOne y l).
Proof.
  induction l; introv Hl1 Hl2; simpls~.
    cases_if; cases_if~; rewrite Mem_cons_eq in *.
      destruct* Hl1.
      left~.
      right. applys* IHl.
Qed.

(* removeOne commutes with removeN *)
Lemma rem1_remN_comm: forall l t x, removeOne x (removeN l t) = removeN l (removeOne x t).
Proof.
  induction l; introv; simpls~.
  rewrite (IHl (removeOne x t) a). rewrite rem1_comm.
  do 2 rewrite IHl; auto.
Qed.

(* The number of occurrences of an element is reduced by one after successful removal *)
Lemma count_removeOne_pos : forall l x,
  Mem x l -> count x (removeOne x l) = count x l - 1.
Proof.
  induction l; introv Hm.
    rewrite* Mem_nil_eq in Hm.
  inverts Hm.
  simpl; cases_if*; nat_math.
  elim (classic (x = a)); introv Hneq; subst.
    simpl; cases_if*; nat_math.
    simpl; cases_if*; simpl; cases_if*.
Qed.

(* The number of occurrences of an element remains the same after unsuccessful removal *)
Lemma count_removeOne_neg : forall l x y,
  x <> y -> count x (removeOne y l) = count x l.
Proof.
  induction l; introv Hneq.
    simpls~.
  simpl; cases_if*; simpl; cases_if*. 
Qed.

(* If the number of occurrences of every element is the same for two lists, then the lengths of these two lists are equal *)
Lemma count_length : forall l1 l2, 
  (forall x, count x l1 = count x l2) -> length l1 = length l2.
Proof.
  inductions l1; introv; introv Hyp.
    simpls; rew_length.
    elim (classic (length l2 = 0)); intro Hneq; jauto.
    assert (Hge : length l2 > 0) by nat_math; clear Hneq.   
    assert (forall n : nat, n > 0 -> exists m, n = S m).
      induction n; try nat_math.
      destruct n; intros. 
        exists~ 0.
        exists~ (S n).
    specialize (H (length l2) Hge).
    destruct H as (m & H); apply lengthn in H.    
    destruct H as (y & ys & H); subst.
    specialize (Hyp y); simpl in Hyp; cases_if*.
    assert (Hm : Mem a l2) by (specialize (Hyp a); simpl in Hyp; cases_if*; rewrite <- count_Mem; nat_math).
    assert (Heq : length l2 = length (a :: (removeOne a l2))).
      specialize (Hyp a); simpl in Hyp; cases_if*.
    elim (classic (length l2 = 0)); intro H'.
      apply length0 in H'; rewrite H' in Hm; rewrites* Mem_nil_eq in Hm.
      rew_length; rewrites~ length_rem1; nat_math.
    rewrite Heq; rew_length.
    specialize (IHl1 (removeOne a l2)).
    rewrite IHl1; try nat_math.
    introv; specialize (Hyp x).    
    simpl in Hyp; cases_if*.
    rewrites~ count_removeOne_pos; nat_math.
    rewrite plus_0_l in Hyp; rewrite Hyp.
    rewrites~ count_removeOne_neg.
Qed.

End RemoveOne.

(****** No Dup Properties ******)

Section NoDup.
Variable A: Type.
Implicit Types l t: list A.
Implicit Types x y : A.

(* Preservation of no duplication under removal of one element from an append *)
Lemma nodup_middle: forall l t y,
  noDup (l ++ y::t) -> ~Mem y (l ++ t) /\ noDup (l ++ t).
Proof.
  introv H. induction l.
    simpls~.
    rew_app in *. simpls. destructs H.
    specializes IHl H0. splits*.
      rewrites Mem_app_or_eq in *. assert ( ~Mem a l /\ ~Mem a (y :: t)).
        split. introv H1. apply H. left~. introv H1. apply H. right~.
      destruct H1. rewrite <- app_cons. rewrites Mem_app_or_eq. introv H3.
      assert (~Mem y l /\ ~Mem y t).
        split. introv H'. apply IHl. left~. introv H'. apply IHl. right~.
        destruct H4. assert (Mem y (a::l)).
          elim H3. introv H'. assumption. introv H'. false~ H5.
        rewrite Mem_cons_eq in H6. assert (y = a).
          elim H6. introv H'. assumption. introv H'. false~ H4.
        rewrite Mem_cons_eq in H2. rew_logic in H2. destruct H2. apply~ H2.
      introv H'. apply H. rewrites Mem_app_or_eq in *. right. rewrites* Mem_cons_eq.
Qed.

(* The absence of duplicates is invariant under removeOne *)
Lemma nodup_rem1 : forall l x, noDup l -> noDup (removeOne x l).
Proof.
  introv Hnd. induction l; simpls~.
    cases_if*.
    simpls. split.
      introv H'. apply Hnd. applys* mem_rem1_l.
      applys* IHl.
Qed.

(* Absence of duplicates goes through the append *)
Lemma nodup_app_inv: forall l t,
  noDup (l ++ t) -> noDup l /\ noDup t.
Proof.
  introv Hnd. splits.
    induction l.
      simpls~.
      rew_app in Hnd. simpl in Hnd. destruct Hnd. simpl. split.
        rewrite Mem_app_or_eq in H. introv H1. apply H.
          left~.
        applys~ IHl.
    induction t.
      simpls~.
      apply nodup_middle in Hnd. destruct Hnd.
      simpl. split.
        rewrite Mem_app_or_eq in H. introv H1. apply H.
          right~.
        applys~ IHt.
Qed.

(* Commutativity and absence of duplicates, for part of an append *)
Lemma nodup_app_comm_step: forall l t x, noDup (x::l ++ t) = noDup (l ++ x::t).
Proof.
  induction l; introv.
    simpls~.
    rew_app. simpls. rewrite <- IHl. rew_logic.
    splits; introv H; destructs H; splits~;
    rewrite_all Mem_app_or_eq in *; rewrite_all Mem_cons_eq in *;
    rew_logic in *; rewrite_all Mem_app_or_eq in *; splits*.
Qed.

(* Absence of duplicates is invariant under append commutation *)
Lemma nodup_app_comm: forall l t, noDup (l ++ t) = noDup (t ++ l).
Proof.
  induction l; introv; rew_app~.
    simpl. rewrite IHl.
    rewrite Mem_app_or_eq.
    assert ((Mem a l \/ Mem a t) = (Mem a t \/ Mem a l)).
      rew_logic. intuition.
    rewrite H. rewrite <- Mem_app_or_eq. clear H.
    assert ((~ Mem a (t ++ l) /\ noDup (t ++ l)) = noDup (a::t++l)). simpls~.
    rewrite H. clear H IHl.
    apply nodup_app_comm_step.
Qed.

(* In a list of no duplicates, all members occur only once *)
Lemma nodup_count : forall l, 
  noDup l <-> (forall x, Mem x l -> count x l = 1).
Proof.
  introv; split. 
  inductions l; introv Hd Hm.
    rewrite* Mem_nil_eq in Hm.
    rewrite Mem_cons_eq in Hm; inverts Hm; simpl; cases_if*; inverts* Hd.
      rewrite <- count_Mem in H; nat_math.
  inductions l; introv Hc; constructor;
    assert (Hm : Mem a (a :: l)) by constructor; lets Hc' : Hc; specialize (Hc a Hm); simpl in Hc; cases_if*;
    assert (Hnm : ~ Mem a l) by (rewrite <- count_Mem; nat_math); auto.
  apply IHl; introv Hm'.     
    elim (classic (x = a)); introv Hneq; substs*.
    specialize (Hc' x); simpl in Hc'; cases_if*; rewrite plus_0_l in Hc'; apply Hc'; constructor~.
Qed.

(* No duplicates in append IFF No duplicates in each and intersection empty *)
Lemma nodup_app_iff : forall l t, noDup (l ++ t) <-> noDup l /\ noDup t /\ (from_list l \n from_list t = \{}).
Proof.
  induction l using (measure_induction length); destruct l; introv; [ | split]; try intro Hyp.
    simpl; rewrite from_list_nil; rewrite app_nil_l; rewrite* inter_empty_l.
    splits; try apply (nodup_app_inv _ _ Hyp).
    apply not_not_elim; intro Hnempty; apply inter_not_empty_exists in Hnempty.
    destruct Hnempty as (x & Hin).
    rewrite in_inter in Hin; repeat rewrite from_list_spec in Hin.
    eapply nodup_count with (x := x) in Hyp.
    repeat rewrite <- count_Mem in Hin.
    rewrite count_app_plus in Hyp; nat_math.
    applys* Mem_app_or.
    destruct Hyp as (Hnd1 & Hnd2 & Hninter).
    rewrite nodup_count in *. 
    introv Hm; rewrite count_app_plus; rewrite Mem_app_or_eq in Hm; inverts* Hm.
    assert (~ Mem x t).
      introv H1; false.
      assert (Hin : x \in (from_list (a :: l) \n from_list t)).
        rewrite in_inter; split; rewrites~ from_list_spec.
      rewrite <- fset_extens_iff in Hninter; specialize (Hninter x).
      rewrite in_empty in Hninter; rewrites~ <- Hninter.
    rewrite (Hnd1 x H0); rewrite <- count_Mem in H1; nat_math.
    assert (~ Mem x (a :: l)).
      introv H1; false.
      assert (Hin : x \in (from_list (a :: l) \n from_list t)).
        rewrite in_inter; split; rewrites~ from_list_spec.
      rewrite <- fset_extens_iff in Hninter; specialize (Hninter x).
      rewrite in_empty in Hninter; rewrites~ <- Hninter.
    rewrite (Hnd2 x H0); rewrite <- count_Mem in H1; nat_math.
Qed.

End NoDup.

(************* Split/Combine properties *************)

Section SplitCombine.
Variables A B: Type.
Implicit Types l t : list A.
Implicit Types r s : list B.
Implicit Types a b c d : list (A*B).
Implicit Types x : A.
Implicit Types y : B.
Implicit Types z : (A*B).

(* Membership and combine *)
Lemma mem_comb: forall l r x y, length l = length r ->
  Mem (x,y) (combine l r) -> Mem x l /\ Mem y r.
Proof.
  induction l; introv Hl Hm. 
    simpls; rewrites* Mem_nil_eq in Hm.
  lets Hl' : Hl; rew_length in Hl; symmetry in Hl; apply lengthn in Hl.
  destruct Hl as (b & lb' & Heq); subst.
  simpl in Hm; inverts Hm; split; constructor; eapply IHl; assert (Hl'': length l = length lb') by auto; try apply Hl''; try  apply H0.
Qed.

(* Length of the combined list is equal to the length of the original lists *)
Lemma length_combine: forall l r,
  length l = length r -> length (combine l r) = length l.
Proof.
  induction l; simpls~.
  introv Hl; lets Hl' : Hl; rew_length in Hl; symmetry in Hl; apply lengthn in Hl.
  destruct Hl as (b & lb' & Heq); subst.
  rew_length in *; rewrite IHl; nat_math.
Qed.

(* Effective obtaining of the two lists for split *)
Lemma split_spec : forall (l : list (A * B)),
  exists l1 l2, (l1, l2) = split l.
Proof.
  induction l.
    simpl; exists~ (@nil A) (@nil B).
    destruct IHl as (l1l & l2l & Heql).
    rewrite (surjective_pairing a).
    simpl; rewrite <- Heql.
    exists~ (fst a :: l1l) (snd a :: l2l).
Qed.

(* Inverseness of split and combine *)
Lemma combine_split : forall l r, length l = length r ->
      split (combine l r) = (l,r).
Proof.
  induction l; introv Hl; simpls~.
    rew_length in Hl; symmetry in Hl; apply length0 in Hl; substs~.
  lets Hl' : Hl; rew_length in Hl; symmetry in Hl; apply lengthn in Hl.
  destruct Hl as (y & r' & Heq); subst.
  assert (Hl'': length l = length r') by auto.
  specialize (IHl r' Hl''); symmetry in IHl.  
  rewrite (split_cons) with (l1 := l) (l2 := r'); auto.
Qed.

(* First passes through split *)
Lemma fst_split_cons: forall a z,
  fst (split (z::a)) =  (fst z) :: (fst (split a)).
Proof.
  introv.
  lets (l1a & l2a & Heqa) : (split_spec a); rewrite <- Heqa.
  rewrite (surjective_pairing z) at 1.
  rewrite split_cons with (l1 := l1a) (l2 := l2a); auto.
Qed.  

(* Second passes through split *)
Lemma snd_split_cons: forall a z,
  snd (split (z::a)) =  (snd z) :: (snd (split a)).
Proof.
  introv.
  lets (l1a & l2a & Heqa) : (split_spec a); rewrite <- Heqa.
  rewrite (surjective_pairing z) at 1.
  rewrite split_cons with (l1 := l1a) (l2 := l2a); auto.
Qed.

(* The length of the first split list is equal to the length of the original list *)
Lemma split_length_l : forall a,
      length (fst (split a)) = length a.
Proof.
  induction a.
    simpls~.
    rewrite fst_split_cons; rew_length; auto.
Qed.

(* The length of the second split list is equal to the length of the original list *)
Lemma split_length_r : forall a,
  length (snd (split a)) = length a.
Proof.
  induction a.
    simpls~.
    rewrite snd_split_cons; rew_length; auto.
Qed.

(* First passes through both split and append *)
Lemma fst_split_step: forall a b,
  fst (split (a ++ b)) =  fst (split a) ++ fst (split b).
Proof.
  inductions a; introv.
    simpl; repeat rewrites~ app_nil_l.
    rewrite fst_split_cons.
    repeat rewrite (app_cons); rewrite <- IHa.
    rewrites~ fst_split_cons.
Qed.

(* First passes through both split and append EVEN MORE *)
Lemma fst_split: forall a b c d, fst (split (a ++ b ++ c ++ d)) = 
  fst (split a) ++ fst (split b) ++ fst (split c) ++ fst (split d).
Proof.
  introv. rewrite_all~ fst_split_step.
Qed.

(* Second passes through both split and append *)
Lemma snd_split_step: forall a b,
  snd (split (a ++ b)) =  snd (split a) ++ snd (split b).
Proof.
  inductions a; introv.
    simpl; repeat rewrites~ app_nil_l.
    rewrite snd_split_cons.
    repeat rewrite (app_cons); rewrite <- IHa.
    rewrites~ snd_split_cons.
Qed.

(* Second passes through both split and append EVEN MORE *)
Lemma snd_split: forall a b c d, snd (split (a ++ b ++ c ++ d)) = 
  snd (split a) ++ snd (split b) ++ snd (split c) ++ snd (split d).
Proof.
  introv. rewrite_all~ snd_split_step.
Qed.

(* The other direction for the inverseness of split and combine  *)
Lemma split_combine_fs: forall a,
 a = combine (fst (split a)) (snd (split a)).
Proof.
  induction a.
    simpls~.
    rewrite fst_split_cons; rewrite snd_split_cons.
    simpl; rewrite IHa at 1.
    rewrite (surjective_pairing a) at 1; auto.
Qed.

(* If a combined list is equal to nil, then both of its constituent lists are also equal to nil *)
Lemma combine_inv: forall l r,
  length l = length r -> combine l r = nil -> l = nil /\ r = nil.
Proof.
  introv Hl Hc. split.
    induction r.
      rewrite length_nil in Hl. apply length0 in Hl. rewrite~ Hl.
      rewrite length_cons in Hl. apply lengthn in Hl.
       destruct Hl as (z & zs & Hz). rewrite Hz in Hc. simpls. false.
    symmetry in Hl. induction l. 
      rewrite length_nil in Hl. apply length0 in Hl. rewrite~ Hl.
      rewrite length_cons in Hl. apply lengthn in Hl.
       destruct Hl as (z & zs & Hz). rewrite Hz in Hc. simpls. false.
Qed.

(* If combined lists are equal, the left constituent lists are also equal *)
Lemma combine_equal_inv_l: forall l t r s,
  length l = length r -> length t = length s ->
  combine l r = combine t s -> l = t.
Proof.
  induction l; induction t; introv Hl1 Hl2 Hp.
    reflexivity.
    rewrite length_nil in Hl1. symmetry in Hl1. apply length0 in Hl1.
     rewrite length_cons in Hl2. symmetry in Hl2. apply lengthn in Hl2.
     destruct Hl2 as (z & zs & Hz). rewrite Hz in Hp. simpls. false.
    rewrite length_nil in Hl2. symmetry in Hl2. apply length0 in Hl2.
     rewrite length_cons in Hl1. symmetry in Hl1. apply lengthn in Hl1.
     destruct Hl1 as (z & zs & Hz). rewrite Hz in Hp. simpls. false.
    rewrite length_cons in Hl1. symmetry in Hl1.
     lets Hl1': (lengthn r Hl1).
     rewrite length_cons in Hl2. symmetry in Hl2.
     lets Hl2': (lengthn s Hl2).
     destruct Hl1' as (b & bs & Hb). rewrite Hb in Hp.
     destruct Hl2' as (c & cs & Hc). rewrite Hc in Hp. simpls.
     inverts Hp.
     erewrite* IHl.
       rewrite Hb in Hl1. rewrite length_cons in Hl1. nat_math. 
       rewrite Hc in Hl2. rewrite length_cons in Hl2. nat_math.
Qed.

(* If combined lists are equal, the right constituent lists are also equal *)
Lemma combine_equal_inv_r: forall r s l t,
  length l = length r -> length t = length s ->
    combine l r = combine t s -> r = s.
Proof.
  induction r; induction s; introv Hl1 Hl2 Hp.
    reflexivity.
    rewrite length_nil in Hl1. apply length0 in Hl1. rewrite Hl1 in Hp.
     rewrite length_cons in Hl2. apply lengthn in Hl2.
     destruct Hl2 as (z & zs & Hz). rewrite Hz in Hp. simpls. false.
    rewrite length_nil in Hl2. apply length0 in Hl2. rewrite Hl2 in Hp.
     rewrite length_cons in Hl1. apply lengthn in Hl1.
     destruct Hl1 as (z & zs & Hz). rewrite Hz in Hp. simpls. false.
    rewrite length_cons in Hl1.
     lets Hl1': (lengthn l Hl1).
     rewrite length_cons in Hl2.
     lets Hl2': (lengthn t Hl2).
     destruct Hl1' as (b & bs & Hb). rewrite Hb in Hp.
     destruct Hl2' as (c & cs & Hc). rewrite Hc in Hp. simpls.
     inverts Hp.
     erewrite* IHr.
       rewrite Hb in Hl1. rewrite length_cons in Hl1. nat_math. 
       rewrite Hc in Hl2. rewrite length_cons in Hl2. nat_math.
Qed.

(* If combined lists are equal, both constituent lists are also equal *)
Lemma combine_equal_inv: forall l t r s,
  length l = length r -> length t = length s ->
    combine l r = combine t s -> l = t /\ r = s.
Proof.
  introv Hl1 Hl2 Hc. split.
    applys* (combine_equal_inv_l l t r s).
    applys* (combine_equal_inv_r r s l t).
Qed.

(* Uniqueness of pair in uniquess of single element *)
Lemma combine_nodup_pair_unique_fst : forall l r, 
  length l = length r -> 
  noDup l -> 
  forall x, Mem x l -> 
            exists y, Mem y r                  /\ 
                      Mem (x, y) (combine l r) /\ 
                      (forall y', Mem (x, y') (combine l r) -> y' = y).
Proof.
  induction l using (measure_induction length); destruct l; introv Hl Hnd Hm.
    rewrite* Mem_nil_eq in Hm.      
  lets Hl' : Hl; symmetry in Hl'; rew_length in Hl'; apply lengthn in Hl'; destruct Hl' as (b & r' & Heq); subst; rename r' into r.
  rewrite Mem_cons_eq in Hm; inverts Hm.
    exists b; splits; simpls; try solve [constructor].
    introv Hm; rewrite Mem_cons_eq in Hm; inverts Hm.
      inverts~ H0.
    apply mem_comb in H0; try solve [rew_length in *; nat_math]; false*.    
    assert (Hneq : x <> a) by (simpls; intro Heq; subst; false*).
    assert (Hl' : length l = length r) by (rew_length in *; nat_math).    
    assert (Hlt : length l < length (a :: l)) by (rew_length; nat_math).
    assert (Hndl : noDup l) by simpls*.
    lets (y & Hmyr & Hmxy & Hfy) : (H l Hlt r Hl' Hndl x H0). 
    exists y; splits; simpls; try solve [constructor~].
      introv Hm; rewrite Mem_cons_eq in Hm; inverts Hm; auto; inverts* H1.
Qed.

(* Uniqueness of pair in uniquess of single element *)
Lemma combine_nodup_pair_unique_snd : forall r l, length l = length r -> 
  noDup r -> forall y, Mem y r -> exists x, Mem x l /\ Mem (x, y) (combine l r) /\ (forall x', Mem (x', y) (combine l r) -> x' = x).
Proof.
  induction r using (measure_induction length); destruct r; introv Hl Hnd Hm.
    rewrite* Mem_nil_eq in Hm.      
  lets Hl' : Hl; rew_length in Hl'; apply lengthn in Hl'; destruct Hl' as (a & l' & Heq); subst; rename l' into l.
  rewrite Mem_cons_eq in Hm; inverts Hm.
    exists a; splits; simpls; try solve [constructor].
    introv Hm; rewrite Mem_cons_eq in Hm; inverts Hm.
      inverts~ H0.
    apply mem_comb in H0; try solve [rew_length in *; nat_math]; false*.    
    assert (Hneq : y <> b) by (simpls; intro Heq; subst; false*).
    assert (Hl' : length l = length r) by (rew_length in *; nat_math).    
    assert (Hlt : length r < length (b :: r)) by (rew_length; nat_math).
    assert (Hndr : noDup r) by simpls*.
    lets (y' & Hmyr & Hmxy & Hfy) : (H r Hlt l Hl' Hndr y H0). 
    exists y'; splits; simpls; try solve [constructor~].
      introv Hm; rewrite Mem_cons_eq in Hm; inverts Hm; auto; inverts* H1.
Qed.

(* Invariance of membership under remDup and split *)
Lemma mem_fst_split_remdup : forall l r x, length l = length r ->
  Mem x (fst (split (remDup (combine l r)))) -> Mem x l.
Proof.
  inductions l; introv Hl Hm; auto.
    lets Hl' : Hl; symmetry in Hl'; rew_length in Hl'; apply lengthn in Hl'; destruct Hl' as (b & r' & Heq); subst; rename r' into r.
    simpls; cases_if.
    elim (classic (x = a)); intro Hneq; subst; constructor; apply IHl with (r := r); auto.
    rewrite fst_split_cons in Hm; rewrite Mem_cons_eq in Hm; inverts* Hm; constructor; apply IHl with (r := r); auto.
Qed.

(* Existence of second element of combine  *)
Lemma combine_exists_fst : forall l r x, length l = length r ->
  Mem x l -> exists y, Mem (x, y) (combine l r).
Proof.
  induction l; introv Hl Hm.
    simpls; rewrite* Mem_nil_eq in Hm.
    lets Hl' : Hl; symmetry in Hl'; rew_length in Hl'; apply lengthn in Hl'; destruct Hl' as (b & r' & Heq); subst; rename r' into r.    
    simpl; rewrite Mem_cons_eq in Hm; inverts Hm. 
      exists b; constructor.
      assert (Hl' : length l = length r) by auto.    
      lets (y & Hy) : (IHl r x Hl' H).
      exists y; constructor~.
Qed.

(* Existence of first element of combine *)
Lemma combine_exists_snd : forall r l y, length l = length r ->
  Mem y r -> exists x, Mem (x, y) (combine l r).
Proof.
  inductions r; introv Hl Hm.
    simpls; rewrite* Mem_nil_eq in Hm.
    lets Hl' : Hl; rew_length in Hl'; apply lengthn in Hl'; destruct Hl' as (b & l' & Heq); subst; rename l' into l.
    simpl; rewrite Mem_cons_eq in Hm; inverts Hm. 
      exists b; constructor.
      assert (Hl' : length l = length r) by auto.    
      lets (x & Hx) : (IHr l y Hl' H).
      exists x; constructor~.
Qed.

(* Connecting non-duplication of combined lists and membership *)
Lemma combine_remdup_fst_iff : forall l r x, length l = length r ->
  (Mem x (fst (split (remDup (combine l r)))) <-> Mem x l).
Proof.
  introv Hl; split; inductions l; try solve [simpls~]; 
  introv Hm; lets Hl' : Hl; symmetry in Hl'; apply lengthn in Hl'; destruct Hl' as (b & r' & Heq); subst; rename r' into r.
    elim (classic (x = a)); introv Hneq; subst; constructor.
    apply (IHl r); try solve [rew_length in *; nat_math].
    simpls; cases_if*.
    rewrite fst_split_cons in Hm; simpls.
    rewrite Mem_cons_eq in Hm; inverts* Hm.
    rewrite Mem_cons_eq in Hm; inverts Hm; simpl; cases_if*.  
    apply (IHl r); try solve [rew_length in *; nat_math].
    apply mem_comb in H; try solve [rew_length in *; nat_math]; jauto.
    rewrite fst_split_cons; simpl; constructor.
    elim (classic (x = a)); introv Hneq; subst; rewrite fst_split_cons.
       simpl; constructor. 
       constructor~.
Qed.

Lemma combine_remdup_snd_iff : forall r l y, length l = length r ->
  (Mem y (snd (split (remDup (combine l r)))) <-> Mem y r).
Proof.  
  introv Hl; split; inductions r. 
  rew_length in *; apply length0 in Hl; subst; simpls~.
  introv Hm; lets Hl' : Hl; apply lengthn in Hl'; destruct Hl' as (b & l' & Heq); subst; rename l' into l.
    elim (classic (y = a)); introv Hneq; subst; constructor.
    apply (IHr l); try solve [rew_length in *; nat_math].
    simpls; cases_if*.
    rewrite snd_split_cons in Hm; simpls.
    rewrite Mem_cons_eq in Hm; inverts* Hm.
    rew_length in *; apply length0 in Hl; subst; simpls~.
    introv Hm; lets Hl' : Hl; apply lengthn in Hl'; destruct Hl' as (b & l' & Heq); subst; rename l' into l.
    rewrite Mem_cons_eq in Hm; inverts Hm; simpl; cases_if*.  
    apply (IHr l); try solve [rew_length in *; nat_math].
    apply mem_comb in H; try solve [rew_length in *; nat_math]; jauto.
    rewrite snd_split_cons; simpl; constructor.
    elim (classic (y = a)); introv Hneq; subst; rewrite snd_split_cons.
       simpl; constructor. 
       constructor~.
Qed.

Lemma combine_remdup_snd : forall l r y, length l = length r ->
  Mem y (snd (split (remDup (combine l r)))) -> Mem y r.
Proof.
  inductions l; introv Hl Hm.
    simpls; rewrite* Mem_nil_eq in Hm.
    lets Hl' : Hl; symmetry in Hl'; apply lengthn in Hl'; destruct Hl' as (b & r' & Heq); subst; rename r' into r.
    elim (classic (y = b)); introv Hneq; subst; constructor.
    apply (IHl r); try solve [rew_length in *; nat_math].
    simpls; cases_if*.
    rewrite snd_split_cons in Hm; simpls.
    rewrite Mem_cons_eq in Hm; inverts* Hm.
Qed.

Lemma combine_remdup_count_fst : forall l r x, length l = length r ->
  count x (fst (split (remDup (combine l r)))) <= count x l.
Proof.
  induction l using (measure_induction length); destruct l.
    simpl; nat_math.
  introv Hl; lets Hl' : Hl; symmetry in Hl'; apply lengthn in Hl'; destruct Hl' as (b & r' & Heq); subst; rename r' into r.
  assert (Hl1 : length l < length (a :: l)) by (rew_length; nat_math).
  assert (Hl2 : length l = length r) by auto.
  simpl; repeat cases_if*.
    specialize (H l Hl1 r a Hl2); nat_math.
    rewrite fst_split_cons; simpl; cases_if*.
    specialize (H l Hl1 r a Hl2); nat_math.
    rewrite fst_split_cons; simpl; cases_if*.
Qed.

Lemma combine_remdup_count_snd : forall r l y, length l = length r ->
  count y (snd (split (remDup (combine l r)))) <= count y r.
Proof.
  induction r using (measure_induction length); destruct r; introv Hl.
    rew_length in *; apply length0 in Hl; subst; simpl; nat_math.
  lets Hl' : Hl; apply lengthn in Hl'; destruct Hl' as (a & l' & Heq); subst; rename l' into l.
  assert (Hl1 : length r < length (b :: r)) by (rew_length; nat_math).
  assert (Hl2 : length l = length r) by auto.
  simpl; repeat cases_if*.
    specialize (H r Hl1 l b Hl2); nat_math.
    rewrite snd_split_cons; simpl; cases_if*.
    specialize (H r Hl1 l b Hl2); nat_math.
    rewrite snd_split_cons; simpl; cases_if*.
Qed.

Lemma combine_count_2_fst : forall l r x, length l = length r ->
  count x (fst (split (remDup (combine l r)))) = 2 ->
  exists y' y'', y' <> y'' /\ Mem (x, y') (remDup (combine l r)) /\ Mem (x, y'') (remDup (combine l r)).
Proof.
  induction l using (measure_induction length); destruct l; introv Hl Hceq.
    simpls; nat_math.
  lets Hl' : Hl; symmetry in Hl'; apply lengthn in Hl'; destruct Hl' as (b & r' & Heq); subst; rename r' into r.
  assert (Hl1 : length l < length (a :: l)) by (rew_length; nat_math).
  assert (Hl2 : length l = length r) by auto.  
  simpls; repeat cases_if*.
  elim (classic (x = a)); intro Hneq; subst; [clear H | ]; rewrite fst_split_cons in Hceq; simpls; cases_if*.
    assert (Hc : Mem a (fst (split (remDup (combine l r))))) by (rewrite <- count_Mem; nat_math); clear Hceq.
    rewrite combine_remdup_fst_iff in Hc; auto.
    lets (y & Hy) : combine_exists_fst a Hl2 Hc.  
    exists b y; splits; try constructor~.
      intro Heq; subst*.
      rewrites~ mem_remdup_iff.    
    rewrite plus_0_l in Hceq.
    lets (y' & y'' & Hneqy'y'' & Hmy' & Hmy'') : (H l Hl1 r x Hl2 Hceq).
    exists y' y''; splits~; simpls; rewrite Mem_cons_eq; right; auto.
Qed.

Lemma combine_count_2_snd : forall r l y, length l = length r ->
  count y (snd (split (remDup (combine l r)))) = 2 ->
  exists x' x'', x' <> x'' /\ Mem (x', y) (remDup (combine l r)) /\ Mem (x'', y) (remDup (combine l r)).
Proof.
  induction r using (measure_induction length); destruct r; introv Hl Hceq.
    rew_length; apply length0 in Hl; subst; simpls; nat_math.
  lets Hl' : Hl; apply lengthn in Hl'; destruct Hl' as (a & l' & Heq); subst; rename l' into l.
  assert (Hl1 : length r < length (b :: r)) by (rew_length; nat_math).
  assert (Hl2 : length l = length r) by auto.  
  simpls; repeat cases_if*.
  elim (classic (y = b)); intro Hneq; subst; [clear H | ]; rewrite snd_split_cons in Hceq; simpls; cases_if*.
    assert (Hc : Mem b (snd (split (remDup (combine l r))))) by (rewrite <- count_Mem; nat_math); clear Hceq.
    rewrite combine_remdup_snd_iff in Hc; auto.
    lets (x & Hx) : combine_exists_snd b Hl2 Hc.  
    exists a x; splits; try constructor~.
      intro Heq; subst*.
      rewrites~ mem_remdup_iff.    
    rewrite plus_0_l in Hceq.
    lets (y' & y'' & Hneqy'y'' & Hmy' & Hmy'') : (H r Hl1 l y Hl2 Hceq).
    exists y' y''; splits~; simpls; rewrite Mem_cons_eq; right; auto.
Qed.

(* If the second part of the combine has no duplicates, neither does the combine *)
Lemma nodup_combine_fst : forall l r, length l = length r ->
  noDup l -> noDup (combine l r).
Proof.
  inductions l; introv Hl Hnd.
    simpls~.
    lets Hl' : Hl; symmetry in Hl'; rew_length in Hl'; apply lengthn in Hl'; destruct Hl' as (b & r' & Heq); subst; rename r' into r.
    simpl; split.
      intro Hin; apply mem_comb in Hin; simpls*.
      apply IHl; simpls*; rew_length in *; nat_math.
Qed.

(* If the second part of the combine has no duplicates, neither does the combine *)
Lemma nodup_combine_snd : forall l r, length l = length r ->
  noDup r -> noDup (combine l r).
Proof.
  introv; generalize l; clear l.
  inductions r; introv Hl Hnd.
    rew_length in Hl; apply length0 in Hl; subst; simpls~.
    lets Hl' : Hl; rew_length in Hl'; apply lengthn in Hl'; destruct Hl' as (b & l' & Heq); subst; rename l' into l.
    simpl; split.
      intro Hin; apply mem_comb in Hin; simpls*.
      apply IHr; simpls*; rew_length in *; nat_math.
Qed.

End SplitCombine.

Hint Resolve fst_split_cons snd_split_cons split_length_l split_length_r split_combine_fs.
Hint Rewrite fst_split_cons snd_split_cons split_length_l split_length_r
: rew_split.

(************* SubLists Existentials properties *************)

Section SubLists.
Variables A B: Type.
Implicit Types x : A.
Implicit Types y : B.
Implicit Types l t u v : list A.
Implicit Types r s w : list B.
Implicit Types a b c d : list (A*B).

Lemma sublists_l: forall l r a b c d, length l = length r ->
  a ++ b ++ c ++ d = combine l r -> exists e f g h, l = e ++ f ++ g ++ h
  /\ length e = length a  /\  length f = length b
  /\ length g = length c  /\  length h = length d.
Proof.
  introv Hls Hcm.
  exists (fst(split a)) (fst(split b)) (fst(split c)) (fst(split d)).
  split. assert (fst (split (combine l r)) = fst (split (a++b++c++d))).
    rewrite~ Hcm.
  rewrite~ combine_split in H. simpl in H. rewrite~ <- fst_split.
  splits; rewrite~ split_length_l.
Qed.

Lemma sublists_r: forall l r a b c d, length l = length r ->
  a ++ b ++ c ++ d = combine l r -> exists e f g h, r = e ++ f ++ g ++ h
  /\ length e = length a  /\  length f = length b
  /\ length g = length c  /\  length h = length d.
Proof.
  introv Hls Hcm.
  exists (snd(split a)) (snd(split b)) (snd(split c)) (snd(split d)).
  split. assert (snd (split (combine l r)) = snd (split (a++b++c++d))).
    rewrite~ Hcm.
  rewrite~ combine_split in H. simpl in H. rewrite~ <- snd_split.
  splits; rewrite~ split_length_r.
Qed.

Lemma sublists_2: forall l t u v r, length (l ++ t ++ u ++ v) = length r ->
  exists e f g h, r = e ++ f ++ g ++ h
  /\ length l = length e  /\  length t = length f
  /\ length u = length g  /\  length v = length h.
Proof.
  introv H. asserts Hl: (length l <= length r).
    rewrite <- H. rewrite length_app; nat_math.
  lets (r' & Hl' & Ht) : (take_struct (length l) r Hl).
  assert (length (t ++ u ++ v) = length r').
    rewrite Ht in H. rewrite_all length_app in *. rewrite~ length_take in H. nat_math.
  asserts Hb: (length t <= length r').
    rewrite <- H0. rewrite length_app; nat_math.
  lets (r'' & Hb' & Ht') : (take_struct (length t) r' Hb).    
  assert (length (u ++ v) = length r'').
    rewrite Ht' in Ht. rewrite Ht in H. rewrite_all length_app in *. rewrite~ length_take in H. nat_math.
  asserts Hu: (length u <= length r'').
    rewrite <- H1. rewrite length_app; nat_math.
  lets (r''' & Hu' & Ht'') : (take_struct (length u) r'' Hu).    
  assert (length v = length r''').
    rewrite Ht'' in Ht'. rewrite Ht' in Ht. rewrite Ht in H. rewrite_all length_app in *. rewrite~ length_take in H. nat_math.
  asserts Hv: (length v <= length r''').
    rewrite <- H2. nat_math.
  lets (r'''' & Hv' & Ht''') : (take_struct (length v) r''' Hv).
  exists (take (length l) r) (take (length t) r') (take (length u) r'') (take (length v) r''').
    split.
      assert (r'''' = nil).
        assert (length r''' = length (take (length v) r''' ++ r'''')).
          rewrite Ht''' at 1. reflexivity.
        apply length_zero_inv. rewrite length_app in H3. nat_math.
      rewrite H3 in Ht'''. rew_app in Ht'''. rewrite Ht''' in Ht''.
        rewrite Ht'' in Ht'. rewrite~ Ht' in Ht.
      splits*.
Qed.

Lemma take_drop_nth: forall n x l, (LibList.Nth n l x) -> l = take n l ++ (x::nil) ++ drop (n+1) l.
Proof.
  induction n; introv Hn.
    inverts Hn. simpl. rew_app~.
    inverts Hn. simpl. rewrite app_cons. rewrite~ <- IHn.
Qed.

Lemma sublists_3: forall x l r, length l = length r -> Mem x l ->
  exists y u v s w,
  l = u ++ (x::nil) ++ v
  /\ r = s ++ (y::nil) ++ w
  /\ length u = length s
  /\ length v = length w.
Proof.
  introv Hls Hm.
  assert (LibList.mem x l).
    clear Hls. induction l.
      rewrite mem_nil. rewrite Mem_nil_eq in Hm. false.
      rewrite mem_cons. rewrite Mem_cons_eq in Hm. rew_reflect. destruct Hm.
        subst. left~.
        right~.
  lets (n & Hn): mem_Nth H. apply (take_drop_nth) in Hn.
  lets (e&f&g&h&Happ&Hl1&Hl2&Hl3&Hl4): sublists_2 (take n l) (x :: nil) (drop (n + 1) l) (nil:list A) r.
    rew_app in *. rewrite~ <- Hn.
  lets Hl2': Hl2. rewrite length_cons in Hl2'. symmetry in Hl2'.
  apply lengthn in Hl2'. destruct Hl2' as (y & f' & Hs).
  assert (f' = nil).
    subst f. rewrite_all length_cons in Hl2. rewrite length_nil in Hl2.
    assert (length f' = 0). nat_math.
    apply length0 in H0. assumption.
  subst f f'.
  exists y (take n l) (drop (n+1) l) e (g++h). splits~.
    rewrite length_app. rewrite length_nil in Hl4. nat_math.
Qed.

End SubLists.

(************* Permut properties *************)

Section Permutation.
Variables A B: Type.
Implicit Types l t u v : list A.
Implicit Types r s y z : list B.
Implicit Types a b c d : list (A*B).
Implicit Types x : A.

(* If one list is a permutation of another, then their lengths are the same *)
Lemma permut_len: forall l t, permut l t -> length l = length t.
Proof.
  induction 1; simpls~. rewrite <- IHrtclosure. inverts H.
    rew_length; nat_math.
Qed.

(* If an element is the head of a list, it is also a member of any permutation of that list *)
Lemma mem_of_permuts: forall l t x, permut l (x::t) -> Mem x l.
Proof.
  introv H. inductions H; simpls~.
    constructor.
    inverts H.
    rewrite_all* Mem_app_or_eq in*.
Qed.

(* If an element is a member of one list, it is also a member of any permutation of that list *)
Lemma permut_mem: forall l t x, permut l t -> Mem x l -> Mem x t.
Proof.
  introv Hp. inductions Hp.
    introv H. assumption.
    induction H. introv Hm.
    rewrite_all Mem_app_or_eq in Hm. rewrite_all Mem_app_or_eq in IHHp.
    applys* IHHp.
Qed.

(* Sets of elements of list that are permutations of each other are the same *)
Lemma permut_from_list: forall l t, permut l t -> from_list l = from_list t.
Proof.
  introv Hp; apply fset_extens; unfold subset; introv H.
    rewrite from_list_spec in *. eapply permut_mem; eauto.
    rewrite from_list_spec in *. apply permut_sym in Hp. eapply permut_mem; eauto.
Qed.

(* If two lists are permutations of each other, then the number of occurrences for any element is the same for both these lists *) 
Lemma permut_count : forall l t, permut l t -> forall x, count x l = count x t. 
Proof.
  introv Hp. inductions Hp; auto.
  induction H; introv; specialize (IHHp x). 
  repeat rewrite count_app_plus; repeat rewrite count_app_plus in IHHp; nat_math.
Qed.

(* If a list is a permutation of nil, then it is equal to nil *)
Lemma permut_of_nil: forall l, permut l nil -> l = nil.
Proof.
  introv H. inductions H; simpls~. inverts H.
  symmetry in H1; apply nil_eq_app_inv in H1; destruct H1.
  symmetry in H1; apply nil_eq_app_inv in H1; destruct H1.
  symmetry in H2; apply nil_eq_app_inv in H2; destruct H2.
  subst~.
Qed.

(* Permutation is preserved under the flipping of first two elements of the list *)
Lemma permut_flip_first_two : forall l t x x',
  permut l (x :: x' :: t) -> permut l (x' :: x :: t).
Proof.
    introv Hp.
    replace (x' :: x :: t) with ((x' :: nil) ++ (x :: nil) ++ t); auto.
    apply permut_trans with (l2 := (x :: nil) ++ (x' :: nil) ++ t); try applys~ permut_get_2; auto.
Qed.

(* If an element is member of a list, then there exists the permutation of that list where that element is the head *)
Lemma permut_mem_exists : forall l x,
  Mem x l -> exists l', permut l (x :: l').
Proof.
  induction l; introv Hm.
    rewrite* Mem_nil_eq in Hm.
    elim (classic (x = a)); intro Hneq; subst.
      exists l; apply permut_refl.
    inverts* Hm.
    specialize (IHl x H0); destruct IHl as (l'' & Hl'').
    exists (a :: l'').
    apply permut_trans with (a :: x :: l''); try (apply permut_flip_first_two; apply permut_refl).
    applys~ permut_cons.
Qed.

(* Two lists are permutations of each other IFF every element occurs the same number of times in each of them *)
Lemma permut_count_forall : forall l t, 
  permut l t <-> (forall x, count x l = count x t).
Proof.
  introv; splits.  
    intro Hp;applys~ permut_count.   
  generalize t; clear t; induction l using (measure_induction length).
  introv Hc.
  lets Hl : count_length Hc.
  destruct l.
  symmetry in Hl; rew_length in Hl; apply length0 in Hl; substs~.
  lets Hl' : Hl; unfold length at 1 in Hl; simpl in Hl; symmetry in Hl; apply lengthn in Hl.
  destruct Hl as (y & t' & Heq); subst.   
  assert (Hl : length l = length t') by auto.
  elim (classic (a = y)); introv Heqay; subst.
    apply permut_cons; apply H.
      rew_length; nat_math.
      introv; specialize (Hc x).
      simpl in Hc; cases_if*.
      assert (Hmyl : Mem y l).
        specialize (Hc y); simpl in Hc; repeat cases_if*.
        rewrite <- count_Mem; nat_math.
      assert (Hmat' : Mem a t').
        specialize (Hc a); simpl in Hc; repeat cases_if*.
        rewrite <- count_Mem; nat_math.
   lets Hexl : (permut_mem_exists Hmyl); destruct Hexl as (l' & Hpl').
   lets Hext : (permut_mem_exists Hmat'); destruct Hext as (t'' & Hpt'').
   apply permut_trans with (a :: y :: l'); try applys~ permut_cons.
   apply permut_trans with (y :: a :: t''); try (applys~ permut_cons; applys~ permut_sym).
   apply permut_flip_first_two; repeat apply permut_cons; apply H.
     apply permut_len in Hpl'; rew_length in *; nat_math.
     introv; specialize (Hc x).   
     apply permut_count with (x := x) in Hpl'.
     apply permut_count with (x := x) in Hpt''.
     simpl in Hc; rewrite Hpl' in Hc; rewrite Hpt'' in Hc; simpl in Hc.
     repeat cases_if*; nat_math.
Qed.

(* Permutation is preserved under addition or removal of (the same) head element *)
Lemma permut_cons_iff : forall l1 l1' x,
  permut l1 l1' <-> permut (x :: l1) (x :: l1').
Proof.
  introv; split.
    applys~ permut_cons.
  introv Hp.
  lets Hl : (permut_len Hp).  
  lets Hm : Hp; rewrite permut_count_forall in Hm.
  rewrite permut_count_forall; introv.
  specialize (Hm x0).
  simpl in Hm; repeat cases_if*.
Qed.

(* If an element is a member of a list, then when we remove it and add it back at the head, we get a permutation of that list *)  
Lemma permut_cons_rem1: forall l x,
  Mem x l -> permut l (x::(removeOne x l)).
Proof.
  introv Hm. induction l; simpls.
    false. rewrite~ Mem_nil_eq in Hm.
    cases_if.
      permut_simpl.
      permut_simpl. rew_app. applys* IHl.
      inverts* Hm.
Qed.

(* Permutation is preserved under successful removal of one element *)    
Lemma rem1_permuts: forall l t x, Mem x l -> Mem x t ->
  permut (removeOne x l) (removeOne x t) -> permut l t.
Proof.
  introv Hm1 Hm2 Hp.
  apply (permut_cons x) in Hp. eapply permut_trans.
    applys* permut_cons_rem1.
    apply permut_sym. eapply permut_trans.
      applys* permut_cons_rem1.
      applys~ permut_sym.
Qed.

(* Permutation is preserved under head removal, left to right *)
Lemma permut_rem1_r: forall l t x,
  permut (x::l) t -> permut l (removeOne x t).
Proof.
  induction l; introv Hp.
  lets Hl : Hp; apply permut_len in Hl.
  apply permut_mem with (x := x) in Hp; try constructor.
  lets Hl' : Hl; unfold length at 1 in Hl; simpl in Hl; symmetry in Hl; apply lengthn in Hl.
  destruct Hl as (y & t' & Heq); subst.
  assert (t' = nil) by (apply length0; rew_length in *; nat_math); subst. 
  inverts Hp; simpl; cases_if*. 
    rewrite Mem_nil_eq in H0; intuition. 

  repeat rewrite permut_count_forall; intros.
  assert (Heq : length (x :: a :: l) = length t) by applys~ permut_len.
  lets Hl' : Heq; rew_length in Heq; symmetry in Heq; apply lengthn in Heq.
  destruct Heq as (y & t' & Heq); subst.
  elim (classic (x0 = x)); introv Heq; subst.
    rewrite count_removeOne_pos; rewrite permut_count_forall in Hp.  
    simpls; specialize (Hp x); repeat cases_if*; nat_math.
    apply count_Mem; specialize (Hp x); rewrite count_cons_pos in Hp; nat_math.
    rewrites~ count_removeOne_neg; rewrite permut_count_forall in Hp.
    simpls; specialize (Hp x0); repeat cases_if*; nat_math.
Qed.

(* Permutation is preserved under head removal, right to left *)
Lemma permut_rem1_l: forall t l x, Mem x t ->
  permut l (removeOne x t) -> permut (x::l) t.
Proof.
  intros t. induction t; simpls; introv Hm Hp.
    false. rewrite~ Mem_nil_eq in Hm.
    cases_if.
      permut_simpl. assumption.
      applys* rem1_permuts (x::l) (a::t) a.
        apply Mem_next. applys* mem_of_permuts.
        constructor.
      simpl. cases_if. cases_if.
      applys* IHt. inverts* Hm.
        eapply permut_sym in Hp. apply permut_rem1_r in Hp. applys~ permut_sym.
Qed.

(* Permutation is preserved under head removal, right to left *)
Lemma permut_rem1_lr: forall l t x, permut l t -> permut (removeOne x l) (removeOne x t).
Proof.
  induction l; simpls; introv H.
    apply permut_sym in H. apply permut_of_nil in H. subst~.
    cases_if.
      apply permut_rem1_r in H; auto.
      apply permut_rem1_l. apply permut_sym in H. apply mem_of_permuts in H.
      applys~ mem_rem1_r.
      rewrite rem1_comm. apply IHl. apply permut_rem1_r in H; auto.
Qed.

(* If one removes all of the elements from a permutation, nothing remains *)
Lemma remN_same_perm: forall l t, permut l t -> removeN l t = nil.
Proof.
  induction l; introv Hp; simpls~.
    apply permut_sym in Hp. apply permut_of_nil in Hp; auto.
    rewrite rem1_remN_comm. rewrite~ IHl. apply~ permut_rem1_r.
Qed.

(* Elements that have not been removed remain in the list *)
Lemma permut_remN_mem: forall l t x, permut (x::l) t -> Mem x (removeN l t).
Proof.
  induction l; introv Hp; simpls~.
    eapply mem_of_permuts. applys* permut_sym.
    rewrite rem1_remN_comm. apply IHl. apply permut_rem1_r.
    apply permut_sym. eapply permut_trans. apply permut_sym. eauto.
    permut_simpl.
Qed.

(* Append and removal of elements *)
Lemma permut_remN_r: forall l t u,
  permut (l ++ t) u -> permut l (removeN t u).
Proof.
  induction l; introv Hp; simpls.
    rew_list in Hp. apply remN_same_perm in Hp. rewrite~ <- Hp.
    rew_list in Hp. apply permut_sym in Hp. lets Hm: mem_of_permuts Hp.
    apply permut_sym in Hp. lets H': Hp. apply permut_rem1_r in Hp. specializes IHl Hp.
    rewrite <- rem1_remN_comm in IHl. apply permut_rem1_l in IHl; auto.
    apply permut_remN_mem in H'.
    clear IHl Hp Hm.
    induction l.
      simpls~.
      rew_list in H'. simpls. apply IHl. applys* mem_rem1_l.
Qed.

(* Combine and append distribute *)
Lemma permut_combine_step: forall l t r s,
  length l = length r ->  length t = length s ->
  combine (l ++ t) (r ++ s) = combine l r ++ combine t s.
Proof.
 induction l; introv H1 H2.
    symmetry in H1. apply length_zero_inv in H1. subst r. rew_app; simpls~.

    remember H1. clear Heqe. rew_length in H1. symmetry in H1.
    apply lengthn in H1. destruct H1 as (a0 & r0 & Hr).
    subst r. rew_app. simpls. rew_app. rewrite~ IHl.
Qed.

(* When the order of the combined sublists is changed, the result is the permutation of the original list *)
Lemma permut_combine: forall l t u v r s y z,
  length l = length r -> length t = length s ->
  length u = length y -> length v = length z ->
  permut (combine (l ++ t ++ u ++ v) (r ++ s ++ y ++ z))
  (combine (l ++ u ++ t ++ v) (r ++ y ++ s ++ z)).
Proof.
  introv H1 H2 H3 H4.
  rewrite_all permut_combine_step; rew_length; auto.
  permut_simpl.
Qed.

(* Permutations preserve absence of duplicates *)
Lemma permut_nodup: forall l t, permut l t -> noDup l -> noDup t.
Proof.
  induction l; introv Hp Hnd.
    apply permut_sym in Hp. apply permut_of_nil in Hp. rewrite~ Hp.
    assert (noDup (removeOne a t) -> noDup t).
      clear IHl. gen l. induction t; introv Hp Hnd Hnd1; simpls~.
        cases_if. split~.
          introv H'. apply Hnd. rewrite <- permut_cons_iff in Hp.
          apply permut_sym in Hp. applys* permut_mem t l.
        split~; simpls.
          introv H'. apply Hnd1. applys~ mem_rem1_r.
          apply permut_sym in Hp. apply permut_rem1_r in Hp. apply permut_sym in Hp.
          eapply IHt.
            simpl in Hp. cases_if~. eassumption. split.
              introv H'. apply Hnd. applys* mem_rem1_l.
              applys* nodup_rem1.
            apply Hnd1.
    apply H. apply permut_rem1_r in Hp. simpls. applys* IHl.
Qed.

(* If two lists have no duplicates and the sets obtained from them are the same, then they are permutations of each other *)
Lemma permut_ndfl: forall l t,
  noDup l -> noDup t -> 
  from_list l = from_list t -> 
  permut l t.
Proof.
  intro l. induction l; simpls.
    introv Hnd1 Hnd2 Hfv. rewrite from_list_nil in Hfv.
      symmetry in Hfv. apply from_list_base in Hfv. rewrite~ Hfv.
  introv Hnd1 Hnd2 Hfv. applys* permut_rem1_l.
    rewrite from_list_cons in Hfv. rewrite <- from_list_spec. rewrite <- Hfv.
      rewrite in_union. left. rewrite~ in_singleton.
    applys* IHl.
      apply~ nodup_rem1.
      rewrite from_list_cons in Hfv. apply from_union_to_rem in Hfv.
        rewrite Hfv. applys* from_list_rem1.
        applys* from_list_notin.
Qed.

(* Constructing the second part of combine when the first ones are permutations of each other *)
Lemma permut_exists: forall l t,
  permut l t -> forall r, length l = length r ->
    exists s, permut r s /\ permut (combine l r) (combine t s).
Proof.
  intros l t Hp. inductions Hp; introv Hl.
    exists~ r.
    inverts H.
    lets (rs1 & rs2 & rs3 & rs4 & Hrs & Hl1 & Hl2 & Hl3 & Hl4):
      (sublists_2 l1 l2 l3 l4 r Hl).
    assert (length (l1 ++ l3 ++ l2 ++ l4) = length (rs1 ++ rs3 ++ rs2 ++ rs4)).
      rewrite Hrs in Hl. rewrite_all length_app in *; nat_math.
    specialize (IHHp (rs1 ++ rs3 ++ rs2 ++ rs4) H). destruct IHHp as (ps & Hp' & Hc').
    exists ps. split.
      assert (permut r (rs1 ++ rs3 ++ rs2 ++ rs4)).
        rewrite Hrs. permut_simpl.
        eapply permut_trans. eassumption. assumption.
      forwards* Hpc: (permut_combine l1 l2 l3 l4).
        rewrite Hrs.
        eapply permut_trans. eassumption. assumption.
Qed.

(* Constructing the corresponding permutations for sublists, under permutation of the combined lists  *)
Lemma permut_exists2: forall l r a b c d,
  length l = length r -> a ++ b ++ c ++ d = combine l r ->
  exists l' r', permut l l' /\ permut r r'
  /\ length l' = length r'
  /\ a ++ c ++ b ++ d = combine l' r'.
Proof.
  introv Hls Hcm.
  lets (l1 & l2 & l3 & l4 & Hc & Hll1 & Hll2 & Hll3 & Hll4):
    (sublists_l l r a b c d Hls Hcm).
  lets (r1 & r2 & r3 & r4 & Hc' & Hlr1 & Hlr2 & Hlr3 & Hlr4):
    (sublists_r l r a b c d Hls Hcm).
  subst l r.
  exists (l1 ++ l3 ++ l2 ++ l4). exists (r1 ++ r3 ++ r2 ++ r4).
  splits.
    permut_simpl. permut_simpl.
    rewrite_all length_app; nat_math.
    do 3 rewrite permut_combine_step in Hcm; try rewrite_all length_app; try nat_math.
    apply length_app_inv in Hcm; destruct Hcm.
    apply length_app_inv in H0; destruct H0.
    apply length_app_inv in H1; destruct H1.
    subst.
    rewrite <- permut_combine_step; try nat_math.
    rewrite <- permut_combine_step; try rewrite_all length_app; try nat_math.
    rewrite~ <- permut_combine_step; try rewrite_all length_app; try nat_math.
    symmetry. rewrite length_combine; nat_math.
    symmetry. rewrite length_combine; nat_math.
    symmetry. rewrite length_combine; nat_math.
    symmetry. rewrite_all length_app. rewrite_all length_combine; nat_math.
    symmetry. rewrite length_combine; nat_math.
    symmetry. rewrite_all length_app. rewrite_all length_combine; nat_math.
Qed.

Lemma noDup_fst_remDup_combine : forall l l1 l2 r r1 r2, 
  length l = length r -> length l1 = length r1 -> length l2 = length r2 ->
  noDup l -> noDup l1 -> noDup l2 ->
  (forall g, Mem g (combine l1 r1) -> Mem g (combine l r)) -> (forall g, Mem g (combine l2 r2) -> Mem g (combine l r)) -> 
    noDup (fst (split (remDup (combine (l1 ++ l2) (r1 ++ r2))))).
  Proof.
    introv Hl0 Hl1 Hl2 Hnd0 Hnd1 Hnd2 Hmem1 Hmem2.
    rewrite nodup_count.
    assert (Hl : length (l1 ++ l2) = length (r1 ++ r2)) by (repeat rewrite length_app; nat_math).
    introv Hm; lets Hm' : Hm; rewrite combine_remdup_fst_iff in Hm'; auto.
    lets Hc : combine_remdup_count_fst (l1 ++ l2) (r1 ++ r2) x Hl.
    assert (Hc' : count x (l1 ++ l2) <= 2).
      rewrite nodup_count in Hnd1, Hnd2; rewrite count_app_plus.
      elim (classic (Mem x l2)); elim (classic (Mem x l1)); introv Hmp Hmq;
      try specialize (Hnd1 x Hmp); try specialize (Hnd2 x Hmq); rewrite <- count_Mem in Hmp, Hmq; try nat_math.
    assert (Hc'' : count x (fst (split (remDup (combine (l1 ++ l2) (r1 ++ r2))))) = 0 \/ 
                   count x (fst (split (remDup (combine (l1 ++ l2) (r1 ++ r2))))) = 1 \/ 
                   count x (fst (split (remDup (combine (l1 ++ l2) (r1 ++ r2))))) = 2) by nat_math.
    inverts Hc''; try inverts H; auto.
      rewrite <- count_Mem in Hm; nat_math.
      assert (H10 : count x (l1 ++ l2) = 2) by nat_math; clear Hc'; false.
      rewrite count_app_plus in H10; elim (classic (Mem x l2)); elim (classic (Mem x l1)); introv Hmp Hmq; 
      lets Hnd1bis : Hnd1; lets Hnd2bis : Hnd2; 
      rewrite nodup_count in Hnd1bis, Hnd2bis;     
      try specialize (Hnd1bis x Hmp); try specialize (Hnd2bis x Hmq); try solve [rewrite <- count_Mem in Hmp, Hmq; nat_math].
      apply combine_count_2_fst in H0; repeat rewrite length_app; try nat_math; destruct H0 as (y' & y'' & Hneqy'y'' & Hmy' & Hmy'').
      assert (Hin : Mem (x, y') (combine l r) /\ Mem (x, y'') (combine l r)).
        rewrite mem_remdup_iff in *; rewrite permut_combine_step in *; auto; rewrite Mem_app_or_eq in *; auto.
        inverts Hmy'; inverts Hmy''; jauto.
      destruct Hin as (Hin1 & Hin2).
      assert (Hmxl : Mem x l) by (apply mem_comb in Hin1; jauto).
      lets Hunl : combine_nodup_pair_unique_fst l r Hl0 Hnd0 x; specialize (Hunl Hmxl).
        destruct Hunl as (Y & HmY & HmlY & HmunqY).
      lets Hypy' : HmunqY y' Hin1; lets Hypy'' : HmunqY y'' Hin2; subst y' y''; jauto.
Qed.

Lemma noDup_snd_remDup_combine : forall l l1 l2 r r1 r2, 
  length l = length r -> length l1 = length r1 -> length l2 = length r2 ->
  noDup r -> noDup r1 -> noDup r2 ->
  (forall g, Mem g (combine l1 r1) -> Mem g (combine l r)) -> (forall g, Mem g (combine l2 r2) -> Mem g (combine l r)) -> 
    noDup (snd (split (remDup (combine (l1 ++ l2) (r1 ++ r2))))).
  Proof.
    introv Hl0 Hl1 Hl2 Hnd0 Hnd1 Hnd2 Hmem1 Hmem2.
    rewrite nodup_count.
    assert (Hl : length (l1 ++ l2) = length (r1 ++ r2)) by (repeat rewrite length_app; nat_math).
    introv Hm; lets Hm' : Hm; rewrite combine_remdup_snd_iff in Hm'; auto.
    lets Hc : (combine_remdup_count_snd (r1 ++ r2) (l1 ++ l2) x Hl).
    assert (Hc' : count x (r1 ++ r2) <= 2).
      rewrite nodup_count in Hnd1, Hnd2; rewrite count_app_plus.
      elim (classic (Mem x r2)); elim (classic (Mem x r1)); introv Hmp Hmq;
      try specialize (Hnd1 x Hmp); try specialize (Hnd2 x Hmq); rewrite <- count_Mem in Hmp, Hmq; try nat_math.
    assert (Hc'' : count x (snd (split (remDup (combine (l1 ++ l2) (r1 ++ r2))))) = 0 \/ 
                   count x (snd (split (remDup (combine (l1 ++ l2) (r1 ++ r2))))) = 1 \/ 
                   count x (snd (split (remDup (combine (l1 ++ l2) (r1 ++ r2))))) = 2) by nat_math.
    inverts Hc''; try inverts H; auto.
      rewrite <- count_Mem in Hm; nat_math.
      assert (H10 : count x (r1 ++ r2) = 2) by nat_math; clear Hc'; false.
      rewrite count_app_plus in H10; elim (classic (Mem x r2)); elim (classic (Mem x r1)); introv Hmp Hmq; 
      lets Hnd1bis : Hnd1; lets Hnd2bis : Hnd2; 
      rewrite nodup_count in Hnd1bis, Hnd2bis;     
      try specialize (Hnd1bis x Hmp); try specialize (Hnd2bis x Hmq); try solve [rewrite <- count_Mem in Hmp, Hmq; nat_math].
      apply combine_count_2_snd in H0; repeat rewrite length_app; try nat_math; destruct H0 as (y' & y'' & Hneqy'y'' & Hmy' & Hmy'').
      assert (Hin : Mem (y', x) (combine l r) /\ Mem (y'', x) (combine l r)).
        rewrite mem_remdup_iff in *; rewrite permut_combine_step in *; auto; rewrite Mem_app_or_eq in *; auto.
        inverts Hmy'; inverts Hmy''; jauto.
      destruct Hin as (Hin1 & Hin2).
      assert (Hmxl : Mem x r) by (apply mem_comb in Hin1; jauto).
      lets Hunl : combine_nodup_pair_unique_snd r l Hl0 Hnd0 x; specialize (Hunl Hmxl).
        destruct Hunl as (Y & HmY & HmlY & HmunqY).
      lets Hypy' : HmunqY y' Hin1; lets Hypy'' : HmunqY y'' Hin2; subst y' y''; jauto.
Qed.

End Permutation.

Section Permutation2.
Variables A B: Type.
Implicit Types l t u v : list A.
Implicit Types r s y z : list B.
Implicit Types a b c d : list (A*B).
Implicit Types x : A.

(* Permutation of combined lists implies permutation of first constituent  *)
Lemma permut_inv_l: forall l t r s,
  length l = length r -> length t = length s ->
    permut (combine l r) (combine t s) -> permut l t.
Proof.
  introv Hl1 Hl2.
  set (lr := combine l r); set (ts := combine t s).
  intro Hp; inductions Hp; subst lr ts.
     lets H: combine_equal_inv. 
     lets (H1 & H2): (>> combine_equal_inv A B l t r s Hl1 Hl2 x). rewrite~ H1. 
     inverts H. 
     forwards~ (l' & r' & Hp1' & Hp1'' & Hl' & H1'): (permut_exists2 l r l1 l2 l3 l4). 
     eapply permut_trans. eassumption. 
     applys IHHp; try eassumption; simpls~. rewrite~ H1'. 
Qed.

(* Permutation of combined lists imples permutation of second constituent *)
Lemma permut_inv_r: forall r s l t,
  length l = length r -> length t = length s ->
    permut (combine l r) (combine t s) -> permut r s.
Proof.
  introv Hl1 Hl2.
  set (lr := combine l r); set (ts := combine t s).
  intro Hp; inductions Hp; subst lr ts.
    lets H: combine_equal_inv. 
    lets (H1 & H2): (>> combine_equal_inv A B l t r s Hl1 Hl2 x). rewrite~ H2. 
     inverts H. 
     lets~ (xs' & rs' & Hp1' & Hp1'' & Hl' & H1'): (permut_exists2 l r l1 l2 l3 l4). 
     eapply permut_trans. eassumption. 
    applys IHHp; try eassumption; simpls~. rewrite~ H1'.
Qed.
  
End Permutation2.

(****** To List Properties ******)

Section ToList.
Variables A: Type.
Implicit Types E F : fset A.
Implicit Types l : list A.
Implicit Types x : A.

(* from_list and to_list are inverse *)
Axiom from_to_list : forall E, 
  from_list (to_list E) = E.

(* to_list and from_list produce a permutation *)
Axiom to_from_list : forall l, 
  permut l (to_list (from_list l)).

(* to_list always produces a list in which there are no duplicates *)
Axiom nodup_tolist: forall E, 
  noDup (to_list E).

(* If two sets are equal, to_list yields permuted lists *)
Lemma permut_to_list: forall E F, 
  E = F -> permut (to_list E) (to_list F).
Proof.
  introv H. rewrite H. permut_simpl.
Qed.

(* Compatibility of to_list with adding an element into the set *)
Lemma to_list_cons_union: forall E x, x \notin E ->
  permut (x::(to_list E)) (to_list (E \u \{x})).
Proof.
  introv Hni. applys~ permut_ndfl.
    simpl. split.
      rewrite <- from_list_spec. rewrite~ from_to_list.
      apply nodup_tolist.
    apply nodup_tolist.
    rewrite from_list_cons. rewrite_all from_to_list. rewrite~ union_comm.
Qed.

(* Compatibility of to_list with removing an element *)
Lemma rem1_to_list_perm: forall E x,
  permut (removeOne x (to_list E)) (to_list (E \- \{x})).
Proof.
  introv. applys~ permut_ndfl.
    apply nodup_rem1. apply nodup_tolist.
    apply nodup_tolist.
    rewrite <- from_list_rem1. rewrite_all~ from_to_list.
      apply nodup_tolist.
Qed.

(* Compatibility of to_list with removing a list of elements *)
Lemma remN_to_list_perm: forall E l,
  permut (removeN l (to_list E)) (to_list (E \- from_list l)).
Proof.
  induction l; simpls~.
    rewrite from_list_nil. rewrite~ remove_empty.
    rewrite from_list_cons. rewrite union_comm. rewrite remove_union.
    apply permut_sym. eapply permut_trans. apply permut_sym.
    apply rem1_to_list_perm. applys~ permut_rem1_lr. applys~ permut_sym.
Qed.

(* from_list of two concatenated to_lists is a union of the corresponding sets *)
Lemma from_to_list_union : forall (l1 l2 : fset A),
  from_list (to_list l1 ++ to_list l2) = l1 \u l2.
Proof.
  introv; apply fset_extens; introv.
  rewrite from_list_spec; rewrite Mem_app_or_eq; intro Hm; elim Hm; clear Hm; intro Hm; rewrite in_union; [left | right]; rewrite <- from_to_list.  
  induction (to_list l1).
    rewrites~ Mem_nil_eq in Hm; false.
    rewrites~ from_list_spec.
  induction (to_list l2).
    rewrites~ Mem_nil_eq in Hm; false.
    rewrites~ from_list_spec.
  rewrite in_union; intro Hm; elim Hm; clear Hm; intro Hm; rewrite from_list_spec; rewrite Mem_app_or_eq; [left | right]; rewrite <- from_to_list in Hm; rewrite from_list_spec in Hm; auto.
Qed.

(****** Forall Properties ******)

(* If a property holds for all elements, it holds for every corresponding list *)
Lemma Forall_forall: forall (P:A -> Prop), (forall x, P x) ->
  (forall xs, Forall (fun x => P x) xs).
Proof.
  introv H. induction xs.
    apply Forall_nil.
    applys~ Forall_cons.
Qed.

(* If P holds for a list, it holds for every one of its members *)
Lemma Forall_mem: forall xs P x, Mem x xs -> Forall (fun x => P x) xs -> P x.
Proof.
  induction xs; introv Hm Hf.
    rewrite Mem_nil_eq in Hm. false.
    rewrite Mem_cons_eq in Hm. inverts Hf. destruct Hm.
      subst~.
      applys* IHxs.
Qed.

(* If P holds for a list, it holds for its every subset *)
Lemma Forall_subset: forall (xs : list A) ys P, Forall (fun x => P x) xs -> (from_list ys \c from_list xs) -> Forall (fun x => P x) ys.
Proof.
  introv Hf Hs.
  rewrite <- Forall_Mem in *; introv Hm; specialize (Hf x).
  rewrite <- from_list_spec in *; auto.
Qed.

End ToList.
