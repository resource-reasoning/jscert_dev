Set Implicit Arguments.
Require Import Shared.
Require Import JsSyntax JsSyntaxAux JsCommon JsCommonAux JsPreliminary.

Require Import LibBag LibFset LibFsetExt LibListExt.

(* ************************************ *)
(** * Auxiliary tactics                 *)

Ltac false_right := let H := fresh "H" in (try solve [right; introv H; inverts* H]).


(* ************************************ *)
(** * Induction in type                 *)

Lemma peano_induction_type : 
  forall (P : nat -> Type),
    (forall n, (forall m, m < n -> P m) -> P n) ->
    (forall n, P n).
Proof.
  introv H. cuts* K: (forall n m, m < n -> P m).
  induction n; introv Le. 

  destruct m; false; nat_math.
  apply H. intros. apply IHn. nat_math. 
Qed.

Lemma measure_induction_type : 
  forall (A:Type) (mu:A->nat) (P:A->Type),
    (forall x, (forall y, mu y < mu x -> P y) -> P x) ->
    (forall x, P x).
Proof.
  introv IH. intros x. gen_eq n: (mu x). gen x.
  induction n using peano_induction_type. introv Eq. subst*.
Qed.

(* *********************************************************************** *)
(**  Retrieving information from an indexed list - last occurrence matters *)

Section Φ.

Context (T : Type).
Context (T_dec : forall (t1 t2 : T), {t1 = t2} + {~ t1 = t2}).

Fixpoint Φ {T : Type} (ρ : list (string * T)) (idx : string) : option T :=
match ρ with
 | nil => None
 | (id, t) :: ρ => let Φρ := Φ ρ idx in
                   ifb (id = idx) then match Φρ with 
                                        | None => Some t
                                        | _    => Φρ
                                       end
                                  else Φρ
end.

Lemma Φ_dec : forall (ρ : list (string * T)) idx oT, {Φ ρ idx = oT} + {~ Φ ρ idx = oT}.
Proof.
  induction ρ as [ | (x & τ) ρ]; introv; simpls.
  + destruct oT; [right | left]; auto; try discriminate. 
  + destruct (string_dec x idx); cases_if*. 
    - destruct (Φ ρ idx); jauto.
      * destruct oT; [ | right; discriminate].
        destruct ((rm T_dec) t t0) as [Heq | Hneq]; subst; jauto.
        right; fequals. 
      * destruct oT; [ | right; discriminate].
        destruct ((rm T_dec) τ t) as [Heq | Hneq]; subst; jauto.
        right; fequals. 
    - rewrite decide_spec in H. apply isTrue_false in n. false*. 
Qed.

End Φ.

(* ******************************************** *)
(**  Auxiliary decidability lemmas              *)

Section aux_dec_lemmas.

Context (T : Type).
Context (T_dec : forall (t1 t2 : T), {t1 = t2} + {~ t1 = t2}).

(* Membership in a list is decidable *)
Lemma Mem_decidable : forall (t : T) (lT : list T), 
  {Mem t lT} + {~ Mem t lT}.
Proof with false_right.
  inductions lT...
  inverts IHlT as IHlT. 

  + left; constructor~.

  + specializes T_dec t a. inverts T_dec as T_dec... 
    left; constructor~.
Qed.

(* Existence of duplicates in a list is decidable *)
Lemma noDup_decidable : forall (lT : list T), 
  {noDup lT} + {~ noDup lT}.
Proof with false_right.
  inductions lT.
  
  + left; constructor~.
  + inverts IHlT as IHlT... 
    lets Hm : (@Mem_decidable a lT). inverts Hm as Hm...
    left; constructor~.
Qed.

End aux_dec_lemmas. 

(*************************************************************)
(** ** Variables and patched finite maps on variables        *)

Definition var := string.


(**************************************************************)
(** ** Types and Environments for DefensiveJS                 *)

(* Types *)
Inductive τ_main : Type :=
 | τη : τ_main (* numbers   *)
 | τβ : τ_main (* booleans  *)
 | τσ : τ_main (* strings   *)
 | τυ : τ_main (* undefined *)
 | το : list (var * τ_main) -> τ_main                          (* object   *)
 | τα : τ_main -> nat -> τ_main                                (* array    *)
 | τϕ : list τ_main -> τ_main -> τ_main                        (* function *)
 | τμ : list τ_main -> list (var * τ_main) -> τ_main -> τ_main (* method   *)
.

(* Object types *)
Definition djs_obj_type := list (var * τ_main).



(**************************************************************)
(** ** We have main and auxiliary types. Main types are
       reserved for proper terms, whereas auxiliary types
       are reserved for intermediate terms in pretty-big-step
       style.                 
 *) 
Inductive type : Type :=
 | type_main : τ_main -> type
 | τξ        : type
.

Coercion type_main : τ_main >-> type.

Notation "{{ ρ }}"         := (το ρ) (at level 59).
Notation "[[ τ , n ]]"     := (τα τ n) (at level 59).
Notation "〈 lτ → τ 〉"     := (τϕ lτ τ) (at level 59).
Notation "《 lτ [ ρ ] → τ 》" := (τμ lτ ρ τ) (at level 59).

(* Scope frame kinds *)
Inductive κ := | κϕ : κ | κω : κ.

(* Typing Environments *)
Definition typ_env := list (djs_obj_type * κ).  

Notation "∅" := (@nil (djs_obj_type * κ)) (at level 60).

(**************************************************************)
(** ** Syntactic categories                                   *)

(* Literals *)
Inductive djs_λ := 
 | djs_η : number -> djs_λ             (* Number  literals *)
 | djs_σ : string -> djs_λ             (* String  literals *)
 | djs_β : bool -> djs_λ               (* Boolean literals *)
 | djs_α : list djs_ε -> djs_λ         (* Array   literals *)
 | djs_ο : list (var * djs_ε) -> djs_λ (* Object  literals *)

with djs_unop := 
 | djs_unop_add         (* Conversion string -> number  *)
 | djs_unop_not         (* Conversion ______ -> boolean *)
 | djs_unop_neg         (* Unary minus *)
 | djs_unop_bitwise_neg (* Unary bitwise negation *)

with djs_binop :=
  | djs_binop_add (* + Addition       *)
  | djs_binop_sub (* - Subtraction    *)
  | djs_binop_mul (* * Multiplication *)
  | djs_binop_div (* / Division       *)
  | djs_binop_mod (* % Modulus        *)

  | djs_binop_band (* &   Bitwise and          *)
  | djs_binop_bor  (* |   Bitwise or           *)
  | djs_binop_bxor (* ^   Bitwise xor          *)
  | djs_binop_lsh  (* <<  Shift left           *)
  | djs_binop_rsh  (* >>  Shift right          *)
  | djs_binop_ursh (* >>> Unsigned shift right *)

  | djs_binop_and (* && Boolean and *)
  | djs_binop_or  (* || Boolean or  *)

  | djs_binop_eq  (* == Equality   *)
  | djs_binop_neq (* != Inequality *)
  | djs_binop_gt  (* >  *)
  | djs_binop_lt  (* <  *)
  | djs_binop_ge  (* >= *)
  | djs_binop_le  (* <= *)

(* Left-hand-side expressions *)
with djs_λε :=
 | djs_var  : var -> djs_λε                   (* Variable *)
 | djs_prop : djs_ε -> var -> djs_λε          (* Property accessor *)
 | djs_cai  : djs_ε -> nat -> djs_λε          (* Constant array index *)
 | djs_ii   : djs_ε -> djs_ε -> nat -> djs_λε (* Integer index *)
 | djs_bai  : djs_ε -> djs_ε -> djs_λε        (* Bounded array index *)

(* Expressions *)
with djs_ε := 
 | djs_ε_l     : djs_λ -> djs_ε                       (* Literal expression *)
 | djs_ε_λε    : djs_λε -> djs_ε                      (* Left-hand-side expression *)
 | djs_ε_ass   : djs_λε -> djs_ε -> djs_ε             (* Assignment *)
 | djs_ε_unop  : djs_unop  -> djs_ε -> djs_ε          (* Unary operators *)
 | djs_ε_binop : djs_binop -> djs_ε -> djs_ε -> djs_ε (* Binary operators *)
 | djs_ε_func  : djs_ϕ -> list djs_ε -> djs_ε         (* Functions *)
 | djs_csi     : djs_ε -> djs_ε -> string -> djs_ε    (* Conditional string index *)

(* Statements *)
with djs_stat :=
 | djs_stat_expr  : djs_ε -> djs_stat                         (* Expressions *)
 | djs_stat_with  : djs_ε -> djs_stat -> djs_stat             (* With statement *)
 | djs_stat_if    : djs_ε -> djs_stat -> djs_stat -> djs_stat (* If statement *)
 | djs_stat_while : djs_ε -> djs_stat -> djs_stat             (* While statement *)
 | djs_stat_seq   : list djs_stat -> djs_stat                 (* A sequence of statements *)

(* Functions *)
with djs_ϕ := 
 | djs_ϕ_main : djs_obj_type -> list (var * djs_δε) -> djs_stat -> djs_ε -> djs_ϕ

(* Defined expressions *)
with djs_δε :=
 | djs_δε_expr : djs_ε -> djs_δε (* Expressions *)
 | djs_δε_func : djs_ϕ -> djs_δε (* Functions   *)

(* Programs *)
with djs_π :=
 | djs_π_main : djs_ϕ -> djs_π

(* Intermediate terms *)
with djs_iterm :=
 | djs_εϕ_aux : list (djs_ε * τ_main) -> djs_iterm
 | djs_ϕ_aux  : djs_obj_type -> list (var * djs_δε) -> djs_stat ->  djs_ε -> djs_obj_type -> τ_main -> djs_iterm

(* Terms *)
with djs_term :=
 | djs_term_λ  : djs_λ     -> djs_term
 | djs_term_λε : djs_λε    -> djs_term
 | djs_term_ε  : djs_ε     -> djs_term
 | djs_term_s  : djs_stat  -> djs_term
 | djs_term_ϕ  : djs_ϕ     -> djs_term
 | djs_term_δε : djs_δε    -> djs_term
 | djs_term_π  : djs_π     -> djs_term 
 | djs_interm  : djs_iterm -> djs_term
.

Coercion djs_term_λ  : djs_λ     >-> djs_term.
Coercion djs_term_λε : djs_λε    >-> djs_term.
Coercion djs_term_ε  : djs_ε     >-> djs_term.
Coercion djs_term_s  : djs_stat  >-> djs_term.
Coercion djs_term_ϕ  : djs_ϕ     >-> djs_term.
Coercion djs_term_δε : djs_δε    >-> djs_term.
Coercion djs_term_π  : djs_π     >-> djs_term.
Coercion djs_interm  : djs_iterm >-> djs_term.

Definition djs_obj := list (var * djs_ε).

Implicit Type τ  : τ_main.
Implicit Type λ  : djs_λ.
Implicit Type ε  : djs_ε.
Implicit Type λε : djs_λε.
Implicit Type s  : djs_stat.
Implicit Type ϕ  : djs_ϕ.
Implicit Type δε : djs_δε.
Implicit Type π  : djs_π.
Implicit Type ι   : djs_iterm.
Implicit Type T  : djs_term.
Implicit Type τρ : djs_obj_type.
Implicit Type ρ  : djs_obj.

Implicit Type η : number.
Implicit Type σ : string.
Implicit Type β : bool.

Implicit Type Γ : typ_env.


(**************************************************************)
(** ** Term size                                              *)

Section Sizes.

Open Local Scope nat_scope.

(* Size of main types *)
Fixpoint djs_size_τ τ :=
match τ with
 | τη | τσ | τβ | τυ => 1
 | τα τ _ => S (djs_size_τ τ) 

 | το τρ => S ((fix djs_size_τρ τρ : nat :=
              match τρ with 
               | nil => 1
               | (_, τ) :: τρ => djs_size_τ τ + djs_size_τρ τρ
              end) τρ)
              
 | τϕ lτ τ => S (((fix djs_size_lτ lτ : nat :=
                   match lτ with 
                    | nil => 1
                    | τ :: lτ => djs_size_τ τ + djs_size_lτ lτ
                   end) lτ) + djs_size_τ τ)

 | τμ lτ τρ τ => S (((fix djs_size_lτ lτ : nat :=
                      match lτ with 
                       | nil => 1
                       | τ :: lτ => djs_size_τ τ + djs_size_lτ lτ
                      end) lτ) +
                    ((fix djs_size_τρ τρ : nat :=
                      match τρ with 
                       | nil => 1
                       | (_, τ) :: τρ => djs_size_τ τ + djs_size_τρ τρ
                      end) τρ) + djs_size_τ τ)
end.

(* Size of types *)
Definition djs_size_type τm :=
match τm with
 | type_main τ => djs_size_τ τ
 | τξ => 1
end.

(* Size of literals *)
Fixpoint djs_size_λ λ : nat :=
match λ with
 | djs_η _  => 1
 | djs_σ _  => 1
 | djs_β _  => 1
 | djs_α lε => S ((fix djs_size_lε (lε : list djs_ε) : nat :=
                    match lε with 
                     | nil => 1
                     | ε :: lε => djs_size_ε ε + djs_size_lε lε
                    end) lε)
 | djs_ο ρ => S ((fix djs_size_ρ ρ : nat :=
                  match ρ with
                   | nil => 1
                   | (_, ε) :: ρ => djs_size_ε ε + djs_size_ρ ρ
                  end) ρ)
end 

(* Size of lhs-expressions *)
with djs_size_λε λε : nat :=
match λε with
 | djs_var  _       => 1
 | djs_prop ε  _    => S (djs_size_ε ε)
 | djs_cai  ε  _    => S (djs_size_ε ε)
 | djs_ii   ε1 ε2 _ => S (djs_size_ε ε1 + djs_size_ε ε2)
 | djs_bai  ε1 ε2   => S (djs_size_ε ε1 + djs_size_ε ε2)
end

(* Size of expressions *)
with djs_size_ε ε : nat :=
match ε with
 | djs_ε_l     λ       => S (djs_size_λ λ)
 | djs_ε_λε    λε      => S (djs_size_λε λε)
 | djs_ε_ass   λε ε    => S (djs_size_λε λε + djs_size_ε ε)
 | djs_ε_unop  _ ε     => S (djs_size_ε ε)
 | djs_ε_binop _ ε1 ε2 => S (djs_size_ε ε1 + djs_size_ε ε2)
 | djs_ε_func  ϕ lε    => S (djs_size_ϕ ϕ + 
                             ((fix djs_size_lε (lε : list djs_ε) : nat :=
                               match lε with 
                                | nil => 1
                                | ε :: lε => djs_size_ε ε + djs_size_lε lε
                               end) lε))
 | djs_csi     ε1 ε2 _ => S (djs_size_ε ε1 + djs_size_ε ε2)
end

(* Size of statements *)
with djs_size_stat s :=
match s with
 | djs_stat_expr  ε        => S (djs_size_ε ε)
 | djs_stat_with  ε  s     => S (djs_size_ε ε + djs_size_stat s) 
 | djs_stat_if    ε  s1 s2 => S (djs_size_ε ε + djs_size_stat s1 + djs_size_stat s2)
 | djs_stat_while ε  s     => S (djs_size_ε ε + djs_size_stat s) 
 | djs_stat_seq   ls       => S ((fix djs_size_ls (ls : list djs_stat) : nat :=
                                  match ls with 
                                   | nil => 1
                                   | s :: ls => djs_size_stat s + djs_size_ls ls
                                  end) ls)
end

(* Size of functions *)
with djs_size_ϕ ϕ := 
match ϕ with
 | djs_ϕ_main _ lvδε s ε => S (S (((fix djs_size_lvδε lvδε : nat :=
                                      match lvδε with 
                                        | nil => 1
                                        | (_, δε) :: lvδε => djs_size_δε δε + djs_size_lvδε lvδε
                                      end) lvδε)
                                  + djs_size_stat s + djs_size_ε ε))
end

(* Size of defined expressions *)
with djs_size_δε δε :=
match δε with
 | djs_δε_expr ε => S (djs_size_ε ε)
 | djs_δε_func ϕ => S (djs_size_ϕ ϕ)
end

(* Size of programs *)
with djs_size_π π :=
match π with
 | djs_π_main ϕ => S (djs_size_ϕ ϕ)
end

(* Size of intermediate terms *)
with djs_size_ι ι :=
match ι with
 | djs_εϕ_aux lετ => S ((fix djs_size_lετ (lετ : list (djs_ε * τ_main)) : nat :=
                               match lετ with 
                                | nil => 1
                                | (ε, _) :: lετ => djs_size_ε ε + djs_size_lετ lετ
                               end) lετ)

 | djs_ϕ_aux ly lvδε s ε _ _ => S (((fix djs_size_lvδε lvδε : nat :=
                                     match lvδε with 
                                      | nil => 1
                                      | (_, δε) :: lvδε => djs_size_δε δε + djs_size_lvδε lvδε
                                            end) lvδε)
                                      + djs_size_stat s + djs_size_ε ε)
end

with djs_size_term T :=
match T with
 | djs_term_λ  λ  => djs_size_λ λ
 | djs_term_λε λε => djs_size_λε λε
 | djs_term_ε  ε  => djs_size_ε  ε
 | djs_term_s  s  => djs_size_stat s
 | djs_term_ϕ  ϕ  => djs_size_ϕ ϕ
 | djs_term_δε δε => djs_size_δε δε
 | djs_term_π  π  => djs_size_π π
 | djs_interm  ι   => djs_size_ι ι
end.

(* Term size is always positive *)
Lemma djs_size_term_positive : forall T, djs_size_term T > 0.
Proof.
  induction T using (measure_induction_type djs_size_term).
  destruct T; destruct d; simpls; nat_math. 
Qed.  

End Sizes.

(**************************************************************)
(** ** Decidability of equality for types and terms            *)

(* Equality of types is decidable *)
Lemma djs_type_eq_dec : forall (τ1 τ2 : type), {τ1 = τ2} + {τ1 <> τ2}.
Proof with (false_right; try solve [left; auto]).
  induction τ1 using (measure_induction_type djs_size_type). 

  destruct τ1; destruct τ2...
  destruct τ; destruct τ0...

  gen l0; inductions l; destruct l0...
  destruct a; destruct p; destruct (string_dec v v0)...
  subst. lets Hτ : X τ τ0. simpls; nat_math.
  lets Hl : IHl l0. intros. apply X. simpls; nat_math.
  inverts Hτ as Hτ; try inverts Hτ; inverts Hl as Hl; try inverts Hl...

  lets Hτ : X τ τ0. simpls; nat_math.
  lets Hn : eq_nat_dec n n0.
  inverts Hτ as Hτ; try inverts Hτ; inverts Hn...

  lets Hτ : X τ τ0. simpls; nat_math.
  inverts Hτ as Hτ; try inverts Hτ...
  gen l0; inductions l; destruct l0...
  lets Hτ : X a τ. simpls; nat_math.
  inverts Hτ as Hτ; try inverts Hτ...
  lets Hl : IHl τ0 l0. intros. apply X. simpls; nat_math.
  inverts Hl as Hl; try inverts Hl...

  lets Hτ : X τ τ0. simpls; nat_math.
  inverts Hτ as Hτ; try inverts Hτ...
  gen l0 l1 l2; inductions l; intros; destruct l1...
  gen l2; inductions l0; intros; destruct l2...
  destruct a; destruct p; destruct (string_dec v v0)...
  subst. lets Hτ : X τ τ1. simpls; nat_math.
  lets Hl : IHl0 l2. intros. apply X. simpls; nat_math.
  inverts Hτ as Hτ; try inverts Hτ; inverts Hl as Hl; try inverts Hl...
  lets Hτ : X a τ. simpls; nat_math.
  inverts Hτ as Hτ; try inverts Hτ...
  clear IHl. gen l0 l1 l2; inductions l; intros; destruct l1...
  gen l2; inductions l0; intros; destruct l2...
  destruct a; destruct p; destruct (string_dec v v0)...
  subst. lets Hτ : X τ1 τ2. simpls; nat_math.
  lets Hl : IHl0 l2. intros. apply X. simpls; nat_math.
  inverts Hτ as Hτ; try inverts Hτ; inverts Hl as Hl; try inverts Hl...
  lets Hτ : X a τ1. simpls; nat_math. inverts Hτ as Hτ; try inverts Hτ...
  lets Hl : IHl τ0 τ l0 l1 l2. intros. apply X. simpls; nat_math.
  inverts Hl as Hl; try inverts Hl...  
Qed.

(* Equality on numbers is decidable  *)
Lemma number_eq_dec : forall n1 n2 : number, {n1 = n2} + {n1 <> n2}.
Proof with (false_right; auto; try solve [intuition]).
  inductions n1; destruct n2...

  + destruct b; destruct b0... 
  + destruct b; destruct b0... 
  + lets Hm : Pos.eq_dec m m0.
    lets He : Z.eq_dec e e1.
    destruct b; destruct b0; intuition; subst... 

    assert (e0 = e2) by (apply proof_irrelevance); subst*.
    assert (e0 = e2) by (apply proof_irrelevance); subst*.  
Qed.

(* Equality of terms is decidable *)
Lemma djs_term_eq_dec : forall (T1 T2 : djs_term), {T1 = T2} + {T1 <> T2}.
Proof with (false_right; try solve [left; auto]).
  induction T1 using (measure_induction_type djs_size_term). 

  destruct T1; destruct T2...

  + destruct d; destruct d0...
    - destruct (number_eq_dec n n0); substs*...
    - destruct (string_dec s s0); substs*...
    - destruct b; destruct b0...
    - cut ({l = l0} + {l <> l0}). 
      * introv Hyp; destruct Hyp; [substs* | ]...
      * inductions l; destruct l0...
        lets Hd : X a d. simpls; nat_math.
        inverts Hd... inverts H.
        specializes IHl l0.
        introv Hs; introv. apply X. 
        simpls; nat_math.
        destruct IHl... substs*.
    - cut ({l = l0} + {l <> l0}). 
      * introv Hyp; destruct Hyp; [substs* | ]...
      * inductions l; destruct l0...
        destruct a; destruct p.
        destruct (string_dec v v0); substs...
        lets Hd : X d d0. simpls; nat_math.
        inverts Hd... inverts H.
        specializes IHl l0.
        introv Hs; introv. apply X. 
        simpls; nat_math.
        destruct IHl... substs*.

  + destruct d; destruct d0...
    - destruct (string_dec v v0); substs...
    - destruct (string_dec v v0); substs...
      lets H : X d d0; [simpls; nat_math | inverts H; try inverts H0]...
    - destruct (eq_nat_dec n n0); substs...
      lets H : X d d0; [simpls; nat_math | inverts H; try inverts H0]...
    - destruct (eq_nat_dec n n0); substs...
      lets H : X d d0; [simpls; nat_math | inverts H; try inverts H0]...
      lets H : X d1 d2; [simpls; nat_math | inverts H; try inverts H0]...
    - lets H : X d d0; [simpls; nat_math | inverts H; try inverts H0]...
      lets H : X d1 d2; [simpls; nat_math | inverts H; try inverts H0]...
  
  + destruct d; destruct d0...
    - lets H : X d d0; [simpls; nat_math | inverts H; try inverts H0]...
    - lets H : X d d0; [simpls; nat_math | inverts H; try inverts H0]...
    - lets H : X d d0; [simpls; nat_math | inverts H; try inverts H0]...
      lets H : X d1 d2; [simpls; nat_math | inverts H; try inverts H0]...
    - lets H : X d1 d2; [simpls; nat_math | inverts H; try inverts H0]...
      destruct d; destruct d0...
    - lets H : X d2 d0_1; [simpls; nat_math | inverts H; try inverts H0]...
      lets H : X d3 d0_2; [simpls; nat_math | inverts H; try inverts H0]...
      destruct d; destruct d1...
    - lets H : X d d0; [simpls; nat_math | inverts H; try inverts H0]...
      cut ({l = l0} + {l <> l0}). 
      * introv Hyp; destruct Hyp; [substs* | ]...
      * inductions l; destruct l0...
        lets Hd : X a d. simpls; nat_math.
        inverts Hd... inverts H.
        specializes IHl d0 l0.
        destruct IHl; substs... 
        introv Hs; introv. 
        apply X. simpls; nat_math.
    - lets H : X d1 d0_1; [simpls; nat_math | inverts H; try inverts H0]...
      lets H : X d2 d0_2; [simpls; nat_math | inverts H; try inverts H0]...
      destruct (string_dec s s0); subst...
  
  + destruct d; destruct d0...
    - lets H : X d d0; [simpls; nat_math | inverts H; try inverts H0]...
    - lets H : X d d0; [simpls; nat_math | inverts H; try inverts H0]...
      lets H : X d1 d2; [simpls; nat_math | inverts H; try inverts H0]...
    - lets H : X d1 d; [simpls; nat_math | inverts H; try inverts H0]...
      lets H : X d2 d0_1; [simpls; nat_math | inverts H; try inverts H0]...
      lets H : X d3 d0_2; [simpls; nat_math | inverts H; try inverts H0]...
    - lets H : X d d0; [simpls; nat_math | inverts H; try inverts H0]...
      lets H : X d1 d2; [simpls; nat_math | inverts H; try inverts H0]...
    - cut ({l = l0} + {l <> l0}). 
      * introv Hyp; destruct Hyp; [substs* | ]...
      * inductions l; destruct l0...
        lets Hd : X a d. simpls; nat_math.
        inverts Hd... inverts H.
        specializes IHl l0. 
        introv Hs; introv. apply X. 
        simpls; nat_math.
        destruct IHl; substs... 

  + destruct d; destruct d0.
    lets H : X d1 d3; [simpls; nat_math | inverts H; try inverts H0]...
    lets H : X d2 d4; [simpls; nat_math | inverts H; try inverts H0]...
    cut ({l = l0} + {l <> l0}). 
      * introv Hyp; destruct Hyp; [substs* | ]...
        cut ({d = d0} + {d <> d0}). 
          introv Hyp; destruct Hyp; [substs* | ]...
          inductions d; destruct d0...
          destruct a; destruct p.
          destruct (string_dec v v0); substs...
          destruct (djs_type_eq_dec τ τ0); substs... 
          inverts e. specializes IHd d0 l0 d3 d4.
          destruct IHd; substs...
          introv Hs; introv. apply X. 
          simpls; nat_math.
      * clear d0. inductions l; destruct l0...
        destruct a; destruct p.
        destruct (string_dec v v0); substs...
        lets H : X d0 d1; substs... 
        simpls; nat_math.
        inverts H; try inverts H0...
        specializes IHl l0 d3 d4.
        destruct IHl; substs...
        introv Hs; introv. apply X. 
        simpls; nat_math.
  + destruct d; destruct d0...
    - lets H : X d d0; [simpls; nat_math | inverts H; try inverts H0]...
    - lets H : X d d0; [simpls; nat_math | inverts H; try inverts H0]...

  + destruct d; destruct d0...
    lets H : X d d0; [simpls; nat_math | inverts H; try inverts H0]...

  + destruct d; destruct d0...
    - cut ({l = l0} + {l <> l0}). 
      * introv Hyp; destruct Hyp; [substs* | ]...
      * inductions l; destruct l0...
        destruct a; destruct p.
        lets H : X d d0; [simpls; nat_math | inverts H; try inverts H0]...
        destruct (djs_type_eq_dec τ τ0); substs... inverts e. 
        specializes IHl l0.
        introv Hs; introv. apply X. 
        simpls; nat_math.
        inverts IHl; substs...

    - destruct (djs_type_eq_dec τ τ0); substs... inverts e. 
      lets H : X d1 d4; [simpls; nat_math | inverts H; try inverts H0]...
      lets H : X d2 d5; [simpls; nat_math | inverts H; try inverts H0]...
      assert ({l = l0} + {l <> l0}).
      {
        clear - X. inductions l; destruct l0...
        destruct a; destruct p.
        destruct (string_dec v v0); substs...
        lets H : X d0 d1; [simpls; nat_math | inverts H; try inverts H0]...
        destruct (IHl d3 l0 d4 d5 τ0); substs...
        introv Hs; apply X; simpls; nat_math.
      }
      assert ({d = d0} + {d <> d0}).
      {
        clear - X. inductions d; destruct d0...
        destruct a; destruct p.
        destruct (string_dec v v0); substs...
        destruct (djs_type_eq_dec τ τ1); substs... inverts e.
        destruct (IHd l d3 d0 d4 d5 τ0); substs...
        introv Hs; apply X; simpls; nat_math.
      }
      assert ({d3 = d6} + {d3 <> d6}).
      {
        clear - X. inductions d3; destruct d6...
        destruct a; destruct p.
        destruct (string_dec v v0); substs...
        destruct (djs_type_eq_dec τ τ1); substs... inverts e.
        destruct (IHd3 d4 d5 d6 τ0); substs...
        introv Hs; apply X; simpls; nat_math.
      } intuition; subst...
Qed.


(**************************************************************)
(** ** Typing                                                 *)

Section Typing.

Reserved Notation "Γ |- Τ ∷ τ" (at level 60).

Inductive types : typ_env -> djs_term -> type -> Prop := 

 (* Literals *)
 | typing_Num    : forall Γ η, Γ |- (djs_η η) ∷ τη 
 | typing_String : forall Γ σ, Γ |- (djs_σ σ) ∷ τσ
 | typing_Bool   : forall Γ β, Γ |- (djs_β β) ∷ τβ

 | typing_Array_cn : forall ε τ Γ, 
                       Γ |- ε ∷ τ -> 
                       Γ |- (djs_α (ε :: nil)) ∷ [[τ, 1]]

 | typing_Array_cc : forall ε1 τ Γ ε2 lε n,
                       Γ |- ε1 ∷ τ -> 
                       Γ |- djs_α (ε2 :: lε) ∷ [[τ, n]] -> 
                       Γ |- (djs_α (ε1 :: ε2 :: lε)) ∷ [[τ, S n]]

 | typing_Object_nil : forall Γ, Γ |- djs_ο nil ∷ {{ nil }}

 (* 
    Requirement : no variable can be equal to "this"
    Choice      : variables cannot be duplicated
 *)
 | typing_Object_cons : forall x ε τ Γ τρ ρ, 
                            x <> "this" ->
                            Γ |- ε ∷ τ ->
                            Γ |- (djs_ο ρ) ∷ {{ τρ }} ->
                            Γ |- djs_ο ((x, ε) :: ρ) ∷ {{ (x, τ) :: τρ }}

 (* Left-hand-side expressions *)
 | typing_VarLoc : forall Γ τρ x τ κ, 
                     Φ τρ x = Some τ ->
                     ((τρ, κ) :: Γ) |- djs_term_λε (djs_var x) ∷ τ

 | typing_VarFS  : forall Γ τρ x τ,
                     let lx := fst (split τρ) in
                     ~ Mem x lx -> Γ |- (djs_var x) ∷ τ -> 
                       ((τρ, κϕ) :: Γ) |- (djs_var x) ∷ τ

 | typing_Prop : forall Γ ε τρ, 
                   Γ |- ε ∷ (το τρ) -> 
                   forall x τ, 
                     Φ τρ x = Some τ ->
                     Γ |- (djs_prop ε x) ∷ τ

 | typing_CAI : forall Γ ε m (η : nat) τ, 
                Γ |- ε ∷ (τα τ m) -> 
                η < m ->
                Γ |- (djs_cai ε η) ∷ τ

 | typing_II : forall Γ ε ε' τ m (η : nat), 
                 Γ |- ε  ∷ (τα τ m) ->
                 Γ |- ε' ∷ τη -> η < m -> (m <= 1073741824)%Z ->
                 Γ |- (djs_ii ε ε' η) ∷ τ

 | typing_BAI : forall Γ (ε ε' : djs_ε) τ m, 
                  Γ |- ε  ∷ (τα τ m) ->
                  Γ |- ε' ∷ τη -> 
                  Γ |- (djs_bai ε ε') ∷ τ

 (* Literals as expressions *)
 | typing_Literal : forall Γ (l : djs_λ) τ, 
                      Γ |- l ∷ τ -> 
                      Γ |- (djs_ε_l l) ∷ τ

 (* LHS-expressions as expressions *)
 | typing_LHS : forall Γ (λε : djs_λε) τ, 
                  Γ |- λε ∷ τ -> 
                  Γ |- (djs_ε_λε λε) ∷ τ

 (* Casts to number from string, string from number, and anything to bool *)
 | typing_NumCast  : forall Γ ε  , Γ |- ε ∷ τσ -> Γ |- (djs_ε_unop djs_unop_add ε) ∷ τη
 | typing_BoolCast : forall Γ ε τ, Γ |- ε ∷ τ  -> Γ |- (djs_ε_unop djs_unop_not ε) ∷ τβ

 (* Concatenation of strings *)
 | typing_Concat : forall Γ ε1 ε2, 
     Γ |- ε1 ∷ τσ -> Γ |- ε2 ∷ τσ -> 
     Γ |- (djs_ε_binop djs_binop_add ε1 ε2) ∷ τσ

 (* Unary minus and bit-by-bit negation *)
 | typing_Unary_min :     forall Γ ε, Γ |- ε ∷ τη -> Γ |- (djs_ε_unop djs_unop_neg         ε) ∷ τη
 | typing_Unary_bin_neg : forall Γ ε, Γ |- ε ∷ τη -> Γ |- (djs_ε_unop djs_unop_bitwise_neg ε) ∷ τη

 (* Arithmetic operators +, -, *, /, % *)
 | typing_Arith_add : forall Γ ε1 ε2, 
                        Γ |- ε1 ∷ τη -> Γ |- ε2 ∷ τη ->
                         Γ |- (djs_ε_binop djs_binop_add ε1 ε2) ∷ τη
 | typing_Arith_sub : forall Γ ε1 ε2, 
                        Γ |- ε1 ∷ τη -> Γ |- ε2 ∷ τη ->
                        Γ |- (djs_ε_binop djs_binop_sub ε1 ε2) ∷ τη
 | typing_Arith_mul : forall Γ ε1 ε2, 
                        Γ |- ε1 ∷ τη -> Γ |- ε2 ∷ τη ->
                        Γ |- (djs_ε_binop djs_binop_mul ε1 ε2) ∷ τη
 | typing_Arith_div : forall Γ ε1 ε2, 
                        Γ |- ε1 ∷ τη -> Γ |- ε2 ∷ τη ->
                        Γ |- (djs_ε_binop djs_binop_div ε1 ε2) ∷ τη
 | typing_Arith_mod : forall Γ ε1 ε2, 
                        Γ |- ε1 ∷ τη -> Γ |- ε2 ∷ τη ->
                        Γ |- (djs_ε_binop djs_binop_mod ε1 ε2) ∷ τη
 | typing_Arith_str : forall Γ ε1, 
                        Γ |- ε1 ∷ τη -> 
                        Γ |- (djs_ε_binop djs_binop_add ε1 (djs_ε_l (djs_σ ""))) ∷ τσ

 (* Arithmetic bit-operators |, &, ^ *)
 | typing_Arith_bit_or  : forall Γ ε1 ε2, 
     Γ |- ε1 ∷ τη -> Γ |- ε2 ∷ τη ->
     Γ |- (djs_ε_binop djs_binop_bor  ε1 ε2) ∷ τη
 | typing_Arith_bit_and : forall Γ ε1 ε2, 
     Γ |- ε1 ∷ τη -> Γ |- ε2 ∷ τη ->
     Γ |- (djs_ε_binop djs_binop_band ε1 ε2) ∷ τη
 | typing_Arith_bit_xor : forall Γ ε1 ε2, 
     Γ |- ε1 ∷ τη -> Γ |- ε2 ∷ τη ->
     Γ |- (djs_ε_binop djs_binop_bxor ε1 ε2) ∷ τη

 (* Arithmetic shift-operators <<, >>, >>> *)
 | typing_Arith_lsh  : forall Γ ε1 ε2, 
                         Γ |- ε1 ∷ τη -> Γ |- ε2 ∷ τη ->
                         Γ |- (djs_ε_binop djs_binop_lsh ε1 ε2) ∷ τη
 | typing_Arith_rsh  : forall Γ ε1 ε2, 
                         Γ |- ε1 ∷ τη -> Γ |- ε2 ∷ τη ->
                         Γ |- (djs_ε_binop djs_binop_rsh ε1 ε2) ∷ τη
 | typing_Arith_ursh : forall Γ ε1 ε2,
                         Γ |- ε1 ∷ τη -> Γ |- ε2 ∷ τη ->
                         Γ |- (djs_ε_binop djs_binop_ursh ε1 ε2) ∷ τη

 (* Comparisons for numbers: >=, <=, >, <, ==, != *)
 | typing_Comp_ν_gt  : forall Γ ε1 ε2, 
                         Γ |- ε1 ∷ τη -> Γ |- ε2 ∷ τη ->
                         Γ |- (djs_ε_binop djs_binop_gt ε1 ε2) ∷ τη
 | typing_Comp_ν_lt  : forall Γ ε1 ε2, 
                         Γ |- ε1 ∷ τη -> Γ |- ε2 ∷ τη ->
                         Γ |- (djs_ε_binop djs_binop_lt ε1 ε2) ∷ τη
 | typing_Comp_ν_ge  : forall Γ ε1 ε2, 
                         Γ |- ε1 ∷ τη -> Γ |- ε2 ∷ τη ->
                         Γ |- (djs_ε_binop djs_binop_ge ε1 ε2) ∷ τη
 | typing_Comp_ν_le  : forall Γ ε1 ε2, 
                         Γ |- ε1 ∷ τη -> Γ |- ε2 ∷ τη ->
                         Γ |- (djs_ε_binop djs_binop_le ε1 ε2) ∷ τη
 | typing_Comp_ν_eq  : forall Γ ε1 ε2, 
                         Γ |- ε1 ∷ τη -> Γ |- ε2 ∷ τη ->
                         Γ |- (djs_ε_binop djs_binop_eq ε1 ε2) ∷ τη
 | typing_Comp_ν_neq : forall Γ ε1 ε2, 
                         Γ |- ε1 ∷ τη -> Γ |- ε2 ∷ τη ->
                         Γ |- (djs_ε_binop djs_binop_neq ε1 ε2) ∷ τη

 (* Comparisons for strings: >=, <=, >, <, ==, != *)
 | typing_Comp_σ_gt  : forall Γ ε1 ε2, 
                         Γ |- ε1 ∷ τσ -> Γ |- ε2 ∷ τσ ->
                         Γ |- (djs_ε_binop djs_binop_gt ε1 ε2) ∷ τσ
 | typing_Comp_σ_lt  : forall Γ ε1 ε2, 
                         Γ |- ε1 ∷ τσ -> Γ |- ε2 ∷ τσ ->
                         Γ |- (djs_ε_binop djs_binop_lt ε1 ε2) ∷ τσ
 | typing_Comp_σ_ge  : forall Γ ε1 ε2, 
                         Γ |- ε1 ∷ τσ -> Γ |- ε2 ∷ τσ ->
                         Γ |- (djs_ε_binop djs_binop_ge ε1 ε2) ∷ τσ
 | typing_Comp_σ_le  : forall Γ ε1 ε2, 
                         Γ |- ε1 ∷ τσ -> Γ |- ε2 ∷ τσ ->
                         Γ |- (djs_ε_binop djs_binop_le ε1 ε2) ∷ τσ
 | typing_Comp_σ_eq  : forall Γ ε1 ε2, 
                         Γ |- ε1 ∷ τσ -> Γ |- ε2 ∷ τσ ->
                         Γ |- (djs_ε_binop djs_binop_eq ε1 ε2) ∷ τσ
 | typing_Comp_σ_neq : forall Γ ε1 ε2, 
                         Γ |- ε1 ∷ τσ -> Γ |- ε2 ∷ τσ ->
                         Γ |- (djs_ε_binop djs_binop_neq ε1 ε2) ∷ τσ

 (* Comparisons for booleans: ==, != *)
 | typing_Comp_β_eq  : forall Γ ε1 ε2, 
                         Γ |- ε1 ∷ τβ -> Γ |- ε2 ∷ τβ ->
                         Γ |- (djs_ε_binop djs_binop_eq ε1 ε2) ∷ τβ
 | typing_Comp_β_neq : forall Γ ε1 ε2, 
                         Γ |- ε1 ∷ τβ -> Γ |- ε2 ∷ τβ ->
                         Γ |- (djs_ε_binop djs_binop_neq ε1 ε2) ∷ τβ

 (* Operators for booleans: ||, && *)
 | typing_Bool_or  : forall Γ ε1 ε2, 
                       Γ |- ε1 ∷ τβ -> Γ |- ε2 ∷ τβ ->
                       Γ |- (djs_ε_binop djs_binop_or  ε1 ε2) ∷ τβ
 | typing_Bool_and : forall Γ ε1 ε2, 
                       Γ |- ε1 ∷ τβ -> Γ |- ε2 ∷ τβ ->
                       Γ |- (djs_ε_binop djs_binop_and ε1 ε2) ∷ τβ

 (* Assignment *)
 | typing_Assign : forall Γ λε ε τ, 
                     Γ |- λε ∷ τ -> Γ |- ε ∷ τ ->
                     Γ |- (djs_ε_ass λε ε) ∷ τ

 (* Function expressions *)
 | typing_FunctionCall : forall Γ ϕ lε lτ τ,
                           Γ |- ϕ ∷ τϕ lτ τ ->
                           length lε = length lτ ->
                           Γ |- djs_εϕ_aux (combine lε lτ) ∷ τξ ->
                           Γ |- (djs_ε_func ϕ lε) ∷ τ

 
 | typing_FunctionCall_aux_nil : forall Γ, 
                                   Γ |- djs_εϕ_aux nil ∷ τξ

 | typing_FunctionCall_aux_cons : forall Γ ε τ lετ,
                                    Γ |- ε ∷ τ ->
                                    Γ |- djs_εϕ_aux lετ ∷ τξ ->
                                    Γ |- djs_εϕ_aux ((ε, τ) :: lετ) ∷ τξ

 (* Conditional string index *)
 | typing_CSI : forall Γ (ε ε' : djs_ε) σ, 
                  Γ |- ε  ∷ τσ -> 
                  Γ |- ε' ∷ τη ->
                  Γ |- (djs_csi ε ε' σ) ∷ τσ

 (* Expressions are statements *)
 | typing_Expression : forall Γ ε τ, 
                         Γ |- ε ∷ τ -> Γ |- (djs_stat_expr ε) ∷ τυ

 (* With statement *)
 | typing_With : forall Γ ε s τρ, 
                   Γ |- ε ∷ (το τρ) -> ((τρ, κω) :: Γ) |- s ∷ τυ ->
                   Γ |- (djs_stat_with ε s) ∷ τυ

 (* If-then-else statement *)
 | typing_If : forall Γ ε s1 s2, 
                 Γ |- ε ∷ τβ -> Γ |- s1 ∷ τυ -> Γ |- s2 ∷ τυ ->
                 Γ |- (djs_stat_if ε s1 s2) ∷ τυ

 (* While statement *)
 | typing_While : forall Γ ε s,
                    Γ |- ε ∷ τβ -> Γ |- s ∷ τυ ->
                    Γ |- (djs_stat_while ε s) ∷ τυ

 (* A sequence of statements *)
 | typing_Sequence_nil : forall Γ, Γ |- djs_stat_seq nil ∷ τυ

 | typing_Sequence_cons : forall Γ s ls, 
                            Γ |- s ∷ τυ -> 
                            Γ |- (djs_stat_seq ls) ∷ τυ -> 
                            Γ |- (djs_stat_seq (s :: ls)) ∷ τυ

 (* 
    Function definition

    IMPORTANT: Currently, types for x_i variables must be provided.
    TODO: Can/should we infer the types for x_i somehow?

    Strict mode requirement : x_i variables cannot contain duplicates
    Requirement : no x_i except the first can be equal to "this"
    Requirement : no y_i can be equal to "this"

    Choice : y_i variables cannot contain duplicates
    Choice : x_i and y_i must be disjoint

    There may be no free occurrences of 'this' in the body
 *)
 | typing_FunctionDef_main : forall Γ τρx (τρy : list (var * djs_δε)) ls ε τr, 
     let lx := fst (split τρx) in
     let lτ := snd (split τρx) in
     let ly := fst (split τρy) in
     let lδε := snd (split τρy) in
     noDup lx -> noDup ly ->
     Forall (fun x => x <> "this") lx ->
     Forall (fun y => y <> "this") ly ->
     disjoint (from_list lx) (from_list ly) ->
     Γ |- (djs_ϕ_aux τρx τρy (djs_stat_seq ls) ε nil τr) ∷ τξ ->
     Γ |- (djs_ϕ_main τρx τρy (djs_stat_seq ls) ε) ∷ 〈 lτ → τr 〉

 (* Base case *)
 | typing_FunctionDef_nil : forall Γ τρx ε ls τρ τ,
     (((τρx ++ τρ)%list, κϕ) :: Γ) |- (djs_stat_seq ls) ∷ τυ ->
     (((τρx ++ τρ)%list, κϕ) :: Γ) |- ε ∷ τ ->
     Γ  |- (djs_ϕ_aux τρx nil (djs_stat_seq ls) ε τρ τ) ∷ τξ

 (* Recursive call *)
 | typing_FunctionDef_cons : forall Γ τρx τρy ε τ y δε ls τρ τ',
     (((τρx ++ τρ)%list, κϕ) :: Γ) |- δε ∷ τ ->
     Γ |- djs_ϕ_aux τρx τρy (djs_stat_seq ls) ε (τρ & (y, τ)) τ' ∷ τξ ->
     Γ |- djs_ϕ_aux τρx ((y, δε) :: τρy) (djs_stat_seq ls) ε τρ τ' ∷ τξ

(* 
    Method definition

    Strict mode requirement : x_i variables cannot contain duplicates
    Requirement : no x_i except the first can be equal to "this"

    Choice : y_i variables cannot contain duplicates
    Choice : x_i and y_i must be disjoint

    There need to be free occurrences of 'this' in the body
 *)
 | typing_MethodDef : forall Γ τρx τρy ls ε τρ τr,
     let lx  := fst (split τρx) in
     let lτ  := snd (split τρx) in
     let ly  := fst (split τρy) in
     let lδε := snd (split τρy) in
     noDup lx -> noDup ly ->
     Forall (fun x => x <> "this") lx ->
     Forall (fun y => y <> "this") ly ->
     disjoint (from_list lx) (from_list ly) ->
     Γ |- (djs_ϕ_aux (("this", {{ τρ }}) :: τρx) τρy (djs_stat_seq ls) ε nil τr) ∷ τξ ->
     Γ |- (djs_ϕ_main τρx τρy (djs_stat_seq ls) ε) ∷ 《 lτ [τρ] → τr 》

 (* Defined expressions *)
 | typing_DefExprExpr : forall Γ ε τ, Γ |- ε ∷ τ -> Γ |- (djs_δε_expr ε) ∷ τ
 | typing_DefExprFunc : forall Γ ϕ τ, Γ |- ϕ ∷ τ -> Γ |- (djs_δε_func ϕ) ∷ τ

 (* Programs *)
 | typing_Prog : forall Γ ϕ, Γ |- ϕ ∷ 〈 (τσ :: nil) → τσ 〉 ->
                             Γ |- (djs_π_main ϕ) ∷ 〈 (τσ :: nil) → τσ 〉

where "Γ |- T ∷ τ" := (types Γ T τ).

(* ********************************************************** *)
(** * Auxiliary inversion lemmas *)

(* Weakening only from the left *)
Lemma weakening_from_left : forall T (τ : type) Γ, 
  (Γ |- T ∷ τ -> forall Γ', (Γ ++ Γ')%list |- T ∷ τ).
Proof.
  induction T using (measure_induction djs_size_term); introv HD;
  destruct T as [λ | λε | ε | s | ϕ | δε | π | ι]; destruct τ; introv; inversion HD; substs*;
  try solve [constructor; try applys* H; simpls; nat_math];
  try solve [econstructor; try eassumption; try applys* H; simpls; nat_math].

  + constructor~; applys* H;
    lets Hsize : djs_size_term_positive ε1;
    simpls; nat_math.

  + constructor~; applys* H;
    lets Hsize : djs_size_term_positive ε;
    simpls; nat_math.
  
  + rewrite app_cons. applys~ typing_VarFS.
    clear - H4. inductions Γ0. inverts H4.
    destruct a. inversion H4; substs; rewrite app_cons.
    constructor~. applys~ typing_VarFS.

  + apply typing_Arith_str. applys* H.
    simpls; nat_math.

  + econstructor; try eassumption; applys* H; [simpls; nat_math | ].
    clear - H4. inductions lε; lets Hsize : djs_size_term_positive ϕ.
    - simpls; nat_math.
    - simpls. destruct lτ; [false* | ].
      assert (length lε = length lτ) by (rew_length in *; nat_math).
      specializes IHlε H; nat_math.

  + econstructor; try eassumption. applys* H. simpls; nat_math.
    specializes H H4. simpls; nat_math. eapply H.

  + econstructor; try eassumption; applys* H; [simpls; nat_math | ].
    lets Hsize : djs_size_term_positive s0. 
    simpls; nat_math.

  + econstructor; applys* H; [simpls; nat_math | ].
    lets Hsize : djs_size_term_positive ε. 
    simpls; nat_math.

  + constructor; rewrite <- app_cons; applys* H; simpls; nat_math.

  + econstructor; [ | applys* H]. 
    - rewrite <- app_cons; applys* H. simpls; nat_math.
    - lets Hsize : djs_size_term_positive δε. 
      simpls; nat_math.
Qed.

(* Weakening from empty context *)
Lemma weakening_empty : forall T (τ : type), 
  ∅ |- T ∷ τ -> forall Γ, Γ |- T ∷ τ.
Proof.
  introv HD; introv.
  apply weakening_from_left with (Γ' := Γ) in HD; auto.
Qed.

(* Strengthening *)
Lemma strengthening : forall T (τ : type) Γ τρ Γ',
  ((Γ & (τρ, κω)) ++ Γ')%list |- T ∷ τ -> (Γ & (τρ, κω)) |- T ∷ τ.
Proof.
  induction T using (measure_induction djs_size_term); introv HD;
  destruct T as [λ | λε | ε | s | ϕ | δε | π | ι]; destruct τ; introv; inversion HD; substs*;
  try solve [constructor; try applys* H; simpls; nat_math];
  try solve [econstructor; try eassumption; try applys* H; simpls; nat_math].

  + constructor~; applys* H;
    lets Hsize : djs_size_term_positive ε1;
    simpls; nat_math.

  + constructor~; applys* H;
    lets Hsize : djs_size_term_positive ε;
    simpls; nat_math.
  
  + destruct Γ.
    - rewrite app_last_sym in *. rewrite app_nil_l in *. 
      inverts H0. applys~ typing_VarLoc.
    - rewrite app_last_sym in *. rewrite app_cons in *.
      inverts H0. applys~ typing_VarLoc.

  + destruct Γ; rewrite app_last_sym in *. 
    - rewrite app_nil_l in *. inverts H0. 
    - rewrite app_cons in *. inverts H0. 
      rewrite <- app_last_sym in H4. 
      applys~ typing_VarFS.

      clear - H4. gen τ; inductions Γ; introv Hyp; rewrite app_last_sym in *.
      * rewrite app_nil_l in *. inverts Hyp. constructor~.
      * destruct a as (τρa & κa). rewrite app_cons in *. inversion Hyp; substs.
        constructor~. rewrite <- app_last_sym in H5. applys~ typing_VarFS. applys* IHΓ.

  + apply typing_Arith_str. applys* H.
    simpls; nat_math.

  + econstructor; try eassumption; applys* H; [simpls; nat_math | ].
    clear - H4. inductions lε; lets Hsize : djs_size_term_positive ϕ.
    - simpls; nat_math.
    - simpls. destruct lτ; [false* | ].
      assert (length lε = length lτ) by (rew_length in *; nat_math).
      specializes IHlε H; nat_math.

  + econstructor; try eassumption. applys* H. simpls; nat_math.
    repeat rewrite <- app_cons in H4. 
    specializes H H4. simpls; nat_math. eapply H.

  + econstructor; try eassumption; applys* H; [simpls; nat_math | ].
    lets Hsize : djs_size_term_positive s0. 
    simpls; nat_math.

  + econstructor; applys* H; [simpls; nat_math | ].
    lets Hsize : djs_size_term_positive ε. 
    simpls; nat_math.

  + constructor; repeat rewrite <- app_cons in *; applys* H; simpls; nat_math.

  + econstructor; [ | applys* H]. 
    - rewrite <- app_cons in *; applys* H; simpls; nat_math.
    - lets Hsize : djs_size_term_positive δε. 
      simpls; nat_math.
Qed.

(* Array length correctness *)
Lemma array_length : forall Γ lε τ n, Γ |- djs_α lε ∷ [[τ, n]] -> n = length lε.
Proof.
  introv Hr. inductions Hr; 
  [ | specializes IHHr2 (ε2 :: lε0) τ n0 (@eq_refl djs_term) (@eq_refl type)];
  rew_length in *; nat_math.
Qed.

(* All elements of an array are of the same type *)
Lemma array_same_type : forall Γ lε τ n, Γ |- djs_α lε ∷ [[τ, n]] -> Forall (fun ε => Γ |- ε ∷ τ) lε.
Proof with (repeat constructor*).
  inductions lε; introv HD; inverts HD; repeat constructor*.
Qed.

(* All statements are of type 'undefined' *)
Lemma statement_undefined : forall Γ s τ, Γ |- s ∷ τ -> τ = τυ.
Proof.
  introv HD; inverts~ HD.
Qed.

Lemma same_variables_in_objects : forall ρ τρ Γ,
  Γ |- djs_ο ρ ∷ {{τρ}} -> fst (split ρ) = fst (split τρ).
Proof.
  inductions ρ; introv HD; simpls; [inverts~ HD | ].
  destruct τρ; [inverts~ HD | ].
  inverts HD. specializes IHρ H6.
  rewrite (split_combine_fs ρ). rewrite combine_split; 
  [ | rewrite split_length_l; rewrite~ split_length_r].
  rewrite (split_combine_fs τρ); simpls; rewrite combine_split;
  [ | rewrite split_length_l; rewrite~ split_length_r]; simpls*.
  rewrite~ IHρ.
Qed.
    
(****************************************************************)
(** ** Translation to JSCert                                    *)

Definition toJSC_unop (u : djs_unop) :=
match u with
 | djs_unop_add => unary_op_add (* Conversion to number *)
 | djs_unop_not => unary_op_not (* Conversion to boolean AND negation *) 
 | djs_unop_neg => unary_op_neg (* Unary minus *)
 | djs_unop_bitwise_neg => unary_op_bitwise_not (* Bitwise negation *)
end.

Definition toJSC_binop (b : djs_binop) :=
match b with
  | djs_binop_add => binary_op_add  (* + Addition       *)
  | djs_binop_sub => binary_op_sub  (* - Subtraction    *)
  | djs_binop_mul => binary_op_mult (* * Multiplication *)
  | djs_binop_div => binary_op_div  (* / Division       *)
  | djs_binop_mod => binary_op_mod  (* % Modulus        *)

  | djs_binop_band => binary_op_bitwise_and          (* &   Bitwise and          *)
  | djs_binop_bor  => binary_op_bitwise_or           (* |   Bitwise or           *)
  | djs_binop_bxor => binary_op_bitwise_xor          (* ^   Bitwise xor          *)
  | djs_binop_lsh  => binary_op_left_shift           (* <<  Shift left           *)
  | djs_binop_rsh  => binary_op_right_shift          (* >>  Shift right          *)
  | djs_binop_ursh => binary_op_unsigned_right_shift (* >>> Unsigned shift right *)

  | djs_binop_and => binary_op_and (* && Boolean and *)
  | djs_binop_or  => binary_op_or  (* || Boolean or  *)

  | djs_binop_eq  => binary_op_equal    (* == Equality   *)
  | djs_binop_neq => binary_op_disequal (* != Inequality *)
  | djs_binop_gt  => binary_op_gt       (* >  *)
  | djs_binop_lt  => binary_op_lt       (* <  *)
  | djs_binop_ge  => binary_op_ge       (* >= *)
  | djs_binop_le  => binary_op_le       (* <= *)
end.

Fixpoint toJSC_λ (λ : djs_λ) :=
match λ with
 | djs_η n  => expr_literal (literal_number n) 
 | djs_σ s  => expr_literal (literal_string s) 
 | djs_β b  => expr_literal (literal_bool   b)
 | djs_α lε => expr_array   ((fix toJSC_lε (lε : list djs_ε) :=
                               match lε with 
                                | nil => nil
                                | ε :: lε => (Some (toJSC_ε ε)) :: toJSC_lε lε
                               end) lε)   
 | djs_ο ρ  => expr_object  ((fix toJSC_ρ (ρ : djs_obj) :=
                                match ρ with
                                  | nil => nil
                                  | (x, ε) :: ρ => (propname_identifier x, propbody_val (toJSC_ε ε)) :: toJSC_ρ ρ
                                end) ρ)     
end

with toJSC_λε λε := 
match λε with
 | djs_var  x => expr_identifier x                  
 | djs_prop ε x => expr_member (toJSC_ε ε) x           

 | djs_cai  ε n => expr_access (toJSC_ε ε) 
                               (expr_literal (literal_number (JsNumber.of_int n)))

 | djs_ii   ε1 ε2 n => expr_access (toJSC_ε ε1)
                                   (expr_binary_op
                                      (toJSC_ε ε2)
                                      binary_op_bitwise_and
                                      (expr_literal (literal_number (JsNumber.of_int n))))

 | djs_bai  ε1 ε2 => let JSCε1 := toJSC_ε ε1 in
                     let JSCε2 := toJSC_ε ε2 in
                       expr_access JSCε1 
                                   (expr_binary_op 
                                      (expr_binary_op
                                         JSCε2
                                         binary_op_unsigned_right_shift
                                         (expr_literal (literal_number JsNumber.zero)))
                                       binary_op_mod
                                       (expr_member JSCε1 "length"))
end

with toJSC_ε ε := 
match ε with 
 | djs_ε_l     λ => toJSC_λ λ
 | djs_ε_λε    λε => toJSC_λε λε
 | djs_ε_ass   λε ε => expr_assign (toJSC_λε λε) None (toJSC_ε ε)
 | djs_ε_unop  unop ε => expr_unary_op (toJSC_unop unop) (toJSC_ε ε)
 | djs_ε_binop binop ε1 ε2 => expr_binary_op (toJSC_ε ε1) (toJSC_binop binop) (toJSC_ε ε2)

 | djs_csi     ε1 ε2 σ => let JSCε1 := toJSC_ε ε1 in
                          let JSCε2rsh0 := (expr_binary_op 
                                              (toJSC_ε ε2)
                                              binary_op_unsigned_right_shift
                                              (expr_literal (literal_number JsNumber.zero))) in
                            expr_conditional 
                              (expr_binary_op 
                                 JSCε2rsh0
                                 binary_op_lt
                                 (expr_member JSCε1 "length"))
                              (expr_access JSCε1 JSCε2rsh0)
                              (expr_literal (literal_string σ))

 | djs_ε_func ϕ lε => expr_call 
                        (toJSC_ϕ ϕ)
                        ((fix toJSC_lε lε :=
                            match lε with
                             | nil => nil
                             | ε :: lε => (toJSC_ε ε) :: toJSC_lε lε
                            end
                         ) lε)
end

with toJSC_stat s := 
match s with
 | djs_stat_expr  ε        => stat_expr (toJSC_ε ε)
 | djs_stat_with  ε  s     => stat_with (toJSC_ε ε) (toJSC_stat s)
 | djs_stat_if    ε  s1 s2 => stat_if (toJSC_ε ε) (toJSC_stat s1) (Some (toJSC_stat s2))
 | djs_stat_while ε  s     => stat_while nil (toJSC_ε ε) (toJSC_stat s)
 | djs_stat_seq   ls       => stat_block ((fix toJSC_lstat ls := 
                                            match ls with
                                             | nil => nil
                                             | s :: ls => (toJSC_stat s) :: (toJSC_lstat ls)
                                            end) ls)
end

(* Functions *)
with toJSC_ϕ ϕ := 
match ϕ with
 | djs_ϕ_main τρx τρy s ε => 
     let lx := fst (split τρx) in
       expr_function 
         None (* Functions have no names *)
         lx   (* List of variables       *)
         (* Function body *)
         (funcbody_intro 
            (prog_intro 
               true (* Body is always strict *)
               (
                 (* Variables *) element_stat (stat_var_decl 
                                                 ((fix var_decl τρy :=
                                                     match τρy with
                                                       | nil => nil
                                                       | (y, δε) :: τρy => (y, Some (toJSC_δε δε)) :: var_decl τρy
                                                     end) τρy)) ::
                 (* Statement *) element_stat (toJSC_stat s) :: 
                 (* Return    *) element_stat (stat_return (Some (toJSC_ε ε))) :: nil
               )
            )
            "function() {}"
         )                                                                                         
end

(* Defined expressions *)
with toJSC_δε δε :=
match δε with
 | djs_δε_expr ε => toJSC_ε ε
 | djs_δε_func ϕ => toJSC_ϕ ϕ
end

(* Programs *)
with toJSC_π π :=
match π with
 | djs_π_main ϕ => let JSCϕ := (toJSC_ϕ ϕ) in
                   prog_intro 
                     true
                     (
                       element_stat (stat_var_decl (("_", Some JSCϕ) :: nil)) ::
                       element_stat (stat_return 
                                       (Some (expr_function None ("x" :: nil)
                                               (funcbody_intro
                                                  (prog_intro 
                                                     true
                                                     (
                                                       element_stat (stat_if (expr_binary_op
                                                                                (expr_unary_op
                                                                                   unary_op_typeof
                                                                                   (expr_identifier "x")
                                                                                )
                                                                                binary_op_equal 
                                                                                (expr_literal (literal_string "string"))
                                                                             ) 
                                                                             (stat_return (Some (expr_call 
                                                                                                   JSCϕ
                                                                                                   (expr_identifier "x" :: nil))))
                                                                             None)
                                                       :: nil
                                                     )                                                     
                                                  ) 
                                                  "function() {}"
                                               )
                                             )
                                       )
                                    )
                       :: nil
                     )
end.

(*
Lemma djs_unicity_of_types_λε : 
  forall λε Γ τm1 τm2 
         (IH : forall T : djs_term,
                 lt (djs_size_term T) (djs_size_term λε) ->
                  forall Γ (τm1 τm2 : type), Γ |- T ∷ τm1 -> Γ |- T ∷ τm2 -> τm1 = τm2),
    Γ |- λε ∷ τm1 -> Γ |- λε ∷ τm2 -> τm1 = τm2.
Proof.
  introv IH HD1 HD2; destruct λε; try solve [inverts HD1; inverts~ HD2].

  + induction Γ; [inverts HD1 | ].
    destruct a. destruct κ0; inverts HD1; inverts* HD2.    
    rewrite H6 in H4. inverts~ H4.

  + inverts HD1; inverts HD2.
    lets Hτ : IH H3 H2. simpls; nat_math. inverts Hτ.
    lets Hnd : no_duplicates_in_objects H3.
    clear -H4 H6 Hnd. gen τ τ0 v. 
    inductions τρ; intros; [inverts H4 | ]. destruct a. 
    rewrite (split_combine_fs τρ) in *. repeat (rewrite combine_split in *; 
    [ | rewrite split_length_l; rewrite~ split_length_r]; simpls).
    inverts* H4. inverts~ H6. 
    eapply mem_comb in H0; [ | rewrite split_length_l; rewrite~ split_length_r]; false*.
    inverts* H6. eapply mem_comb in H0; [ | rewrite split_length_l; rewrite~ split_length_r]; false*.

  + inverts HD1; inverts HD2.
    lets Hτ : IH H2 H3. simpls; nat_math. inverts~ Hτ.

  + inverts HD1; inverts HD2.
    lets Hτ : IH H2 H3. simpls; nat_math. inverts~ Hτ.

  + inverts HD1; inverts HD2.
    lets Hτ : IH H2 H3. simpls; nat_math. inverts~ Hτ.
Qed.

Lemma djs_unicity_of_types : forall T Γ τm1 τm2,
  Γ |- T ∷ τm1 -> Γ |- T ∷ τm2 -> τm1 = τm2.
Proof.
  induction T using (measure_induction djs_size_term).
  destruct T as [λ | λε | ε | s | ϕ | δε | π | ι]; introv HD1 HD2.

  + eapply djs_unicity_of_types_λ; jauto. 
  + eapply djs_unicity_of_types_λε; jauto. 
  + admit.
  + inverts HD1; inverts~ HD2.
  + inversion HD1; inversion HD2; substs; inverts H9;
    subst lx ly lx0 ly0 lτ lτ0 lδε lδε0; substs; tryfalse.
    
    - cut (τr = τr0); [intro Hyp; substs~ | ]. 
      cut (exists Γ, Γ |- ε ∷ τr /\ Γ |- ε ∷ τr0).
      * introv (Γ0 & (HD1' & HD2')). 
        specializes H HD1' HD2'; [ | inverts~ H].
        lets Hsize : djs_size_term_positive ε; simpls; rew_length; nat_math.
      * {
          cut (Forall (fun δε => forall Γ τm1 τm2, Γ |- δε ∷ τm1 -> Γ |- δε ∷ τm2 -> τm1 = τm2) (snd (split τρy))). 
          + clear - H7 H16.
            remember nil as τρ. clear Heqτρ.
            gen Γ τρ τr τr0. inductions τρy; intros.
            - inverts H7. inverts H16. eexists; jauto.
            - destruct a. inverts H7. inverts H16.
              rewrite (split_combine_fs _) in H. rewrite combine_split in *; 
              [ | rewrite split_length_l; rewrite~ split_length_r]; simpls.
              rewrite (split_combine_fs _) in H. rewrite combine_split in *; 
              [ | rewrite split_length_l; rewrite~ split_length_r]; simpls.
              inverts H. specializes H2 H3 H4. inverts H2.              
              eapply IHτρy; eassumption.
          + rewrite <- Forall_Mem; introv Hm.
            apply H. clear - Hm.
            gen ls ε. inductions τρy; intros. inverts Hm.
            destruct a. rewrite (split_combine_fs _) in Hm. rewrite combine_split in *; 
            [ | rewrite split_length_l; rewrite~ split_length_r]; simpls.
            rewrite (split_combine_fs _) in Hm. rewrite combine_split in *; 
            [ | rewrite split_length_l; rewrite~ split_length_r]; simpls.
            inverts Hm as Hm. nat_math. specializes IHτρy Hm ls ε. nat_math.         
        }

    - cut (τr = τr0 /\ τρ = τρ0); [intros (Hyp1 & Hyp2); substs~ | ]. 
      clear H2 H3 H4 H5 HD1 H13 H10 H11 H12 HD2 H14.

      cut (exists Γ, Γ |- ε ∷ τr /\ Γ |- ε ∷ τr0).
      * introv (Γ0 & (HD1' & HD2')). 
        specializes H HD1' HD2'; [ | inverts~ H].
        lets Hsize : djs_size_term_positive ε; simpls; rew_length; nat_math.
      * {
          cut (Forall (fun δε => forall Γ τm1 τm2, Γ |- δε ∷ τm1 -> Γ |- δε ∷ τm2 -> τm1 = τm2) (snd (split τρy))). 
          + clear - H7 H16.
            remember nil as τρ. clear Heqτρ.
            gen Γ τρ τr τr0. inductions τρy; intros.
            - inverts H7. inverts H16. eexists; jauto.
            - destruct a. inverts H7. inverts H16.
              rewrite (split_combine_fs _) in H. rewrite combine_split in *; 
              [ | rewrite split_length_l; rewrite~ split_length_r]; simpls.
              rewrite (split_combine_fs _) in H. rewrite combine_split in *; 
              [ | rewrite split_length_l; rewrite~ split_length_r]; simpls.
              inverts H. specializes H2 H3 H4. inverts H2.              
              eapply IHτρy; eassumption.
          + rewrite <- Forall_Mem; introv Hm.
            apply H. clear - Hm.
            gen ls ε. inductions τρy; intros. inverts Hm.
            destruct a. rewrite (split_combine_fs _) in Hm. rewrite combine_split in *; 
            [ | rewrite split_length_l; rewrite~ split_length_r]; simpls.
            rewrite (split_combine_fs _) in Hm. rewrite combine_split in *; 
            [ | rewrite split_length_l; rewrite~ split_length_r]; simpls.
            inverts Hm as Hm. nat_math. specializes IHτρy Hm ls ε. nat_math.         
        }

        admit.

    - subst lx lτ ly lτ0. inverts H8.
      

  + inverts HD1; inverts~ HD2; eapply H; try eassumption;
    simpls; nat_math.
  + inverts HD1; inverts~ HD2.
  + inverts HD1; inverts~ HD2.
Qed. 

Lemma djs_type_inference_λ : 
  forall λ Γ (IH : forall T, djs_size_term T < djs_size_λ λ ->
    { τm | Γ |- T ∷ τm } + {forall (τm : type), ~ Γ |- T ∷ τm }), 
    { τm | Γ |- λ ∷ τm } + {forall (τm : type), ~ Γ |- λ ∷ τm }.
Proof with (try solve [right; introv NoNo; inverts* NoNo]).
  intros; destruct λ as [η | σ | β | lε | ρ]; destruct Γ...

  + left; exists τη. constructor.
  + left; exists τσ. constructor.
  + left; exists τβ. constructor.

  + destruct lε as [ | ε1 lε]...
    destruct lε as [ | ε2 lε].

    - destruct (IH ε1) as [(τm & Hε1) | ]... simpls; nat_math.
      destruct τm as [τ | ]; [ | false; inverts Hε1]... 
      left; eexists. constructor*.

    - destruct (IH ε1) as [(τm & Hε1) | ]... simpls; nat_math.
      destruct τm as [τ | ]; [ | false; inverts Hε1]... 
      
      destruct (IH (djs_α (ε2 :: lε))) as [(τm & Hε2) | ]...
      lets Hsize : djs_size_term_positive ε1; simpls; rew_length; nat_math.
      destruct τm as [τ' | ]; [ | false; inverts Hε2]...       
      destruct (IH ε2) as [(τm & Hε2') | ]... simpls; nat_math.
      destruct τm as [τ'' | ]; [ | false; inverts Hε2']...
      destruct (djs_type_eq_dec τ'' τ).
      * inverts e... destruct τ'; try solve [false; inverts Hε2].
        lets Heq : array_length Hε2; subst.
        destruct (djs_type_eq_dec τ' τ).
          inverts e. left; eexists; constructor; eassumption.
          false. inverts Hε2. simpls.
Qed.

Lemma DJS_Type_Inference : forall T Γ (τm : type), 
  {exists (τm : type), Γ |- T ∷ τm} + {~ exists (τm : type), Γ |- T ∷ τm}.
Proof.
  induction T using (measure_induction_type djs_size_term).

  destruct T as [λ | λε | ε | s | ϕ | δε | π | ι]; simpls.

  
  
  + intros; destruct λ as [η | σ | β | lε | ρ].
Qed. 

Lemma DJS_Typing_Decidable : forall T Γ (τm : type), {Γ |- T ∷ τm} + {~ Γ |- T ∷ τm}.
Proof with false_right.
  intro T. induction T using (measure_induction_type djs_size_term).

  destruct T as [λ | λε | ε | s | ϕ | δε | π | ι]; simpls.

Lemma aux_typ_dec_λ : 
  forall λ Γ (τm : type) 
         (IH : forall T, djs_size_term T < djs_size_λ λ ->
                 forall Γ (τm : type), {Γ |- T ∷ τm} + {~ Γ |- T ∷ τm}), 
    {Γ |- λ ∷ τm} + {~ Γ |- λ ∷ τm}.
Proof with false_right.
  intros; destruct λ as [η | σ | β | lε | ρ]; 
  destruct Γ; false_right; destruct τm; try destruct τ; false_right;
  try solve [left; constructor].

  + destruct lε as [ | ε1 lε]...
    destruct lε as [ | ε2 lε]. 

    - lets Hε : IH ε1 (∅) τ. simpls; nat_math.      
      inverts Hε as Hε... 
      lets Hn : eq_nat_dec n 1. inverts Hn as Hn;
      [ | right; introv Hyp; apply array_length in Hyp; rew_length in *; nat_math].
      left; constructor~.

    - lets Hn : eq_nat_dec n (length (ε1 :: ε2 :: lε)). inverts Hn as Hn;
      [ | right; introv Hyp; apply array_length in Hyp; rew_length in *; nat_math].
      lets Hε : IH ε1 (∅) τ. simpls; nat_math.
      inverts Hε as Hε...
      replace (length (ε1 :: ε2 :: lε)) with (S (length (ε2 :: lε))) by (rew_length; nat_math).
      lets Hlε : IH (djs_α (ε2 :: lε)) (∅) ([[τ, length (ε2 :: lε)]]). 
      lets Hsize : djs_size_term_positive ε1. simpls; rew_length; nat_math.
      inverts Hlε as Hlε... left; constructor~.

  + destruct ρ as [ | xε ρ]; destruct l...

    - left; constructor~. 

    - destruct xε as (x & ε). destruct p as (x' & τε).
      lets Hx : string_dec x' x. inverts Hx as Hx... 
      lets Hρl : IH (djs_ο ρ) (∅) ({{l}}). 
      lets Hsize : djs_size_term_positive ε. simpls; rew_length; nat_math. 
      inverts Hρl as Hρl...
      lets Hε : IH ε (∅) τε. simpls; nat_math. 
      inverts Hε as Hε...
      lets Hx : string_dec x "this". inverts Hx as Hx... 
      lets HD : (@noDup_decidable _ (x :: fst (split ρ)) string_dec).
      inverts HD as HD. left; constructor~.
      right; introv Hyp; inversion Hyp; substs; subst lx; auto.
Qed.

Lemma aux_typ_dec_λε : 
  forall λε Γ (τm : type) 
         (IH : forall T, djs_size_term T < djs_size_λε λε ->
                 forall Γ (τm : type), {Γ |- T ∷ τm} + {~ Γ |- T ∷ τm}), 
    {Γ |- λε ∷ τm} + {~ Γ |- λε ∷ τm}.
Proof with false_right.
  intros; destruct λε as [x | ε x | ε η | ε1 ε2 η | ε1 ε2];
  try destruct τ...

  + admit.

  + admit.

  + destruct Γ; [ | right; introv Hyp; inverts Hyp as Hyp; inverts Hyp]; 
    try destruct τm... 

Lemma aux_typ_dec_ε_α : forall ε τ (τm : type) 
         (IH : forall T, djs_size_term T < djs_size_ε ε ->
                 forall Γ (τm : type), {Γ |- T ∷ τm} + {~ Γ |- T ∷ τm}), 
    {exists m, ∅ |- ε ∷ [[τ, m]]} + {~ exists m, ∅ |- ε ∷ [[τ, m]]}.
Proof with (try solve [right; introv (m & Hyp); inverts Hyp as Hyp; inverts* Hyp]).
  destruct ε as [λ | λε | | | | |].

  + destruct λ as [ | | | lε |]...
    destruct lε as [ | ε1 lε]...
    destruct lε as [ | ε2 lε].
    
    - lets Hε : IH ε1 (∅) τ. simpls; nat_math.      
      inverts Hε as Hε... 
      left. exists 1. repeat constructor~. 

    - 
Qed.

  + admit.

  + admit.
Qed.

| typing_Prop : forall Γ ε τρ, 
                   Γ |- ε ∷ (το τρ) -> 
                   forall x τ, 
                     Mem (x, τ) τρ ->
                     Γ |- (djs_prop ε x) ∷ τ

 | typing_CAI : forall Γ ε m (η : nat) τ, 
                Γ |- ε ∷ (τα τ m) -> 
                η < m ->
                Γ |- (djs_cai ε η) ∷ τ

 | typing_II : forall Γ ε ε' τ m (η : nat), 
                 Γ |- ε  ∷ (τα τ m) ->
                 Γ |- ε' ∷ τη -> η < m -> (m <= 1073741824)%Z ->
                 Γ |- (djs_ii ε ε' η) ∷ τ

 | typing_BAI : forall Γ (ε ε' : djs_ε) τ m, 
                  Γ |- ε  ∷ (τα τ m) ->
                  Γ |- ε' ∷ τη -> 
                  Γ |- (djs_bai ε ε') ∷ τ


(* PROOOOOF *)

  (* Literals *)
  + intros; applys~ aux_typ_dec_λ.

  + .

  + destruct .

  + admit.

  + admit.

  + destruct δε as [ε | ϕ]; apply X; simpls. rew_length. nat_math.

(**************************************************************)
(** ** Lemmas for arrays                                      *)

(* Empty arrays are not allowed *)
Lemma no_empty_array : forall Γ lε τ n, Γ |- djs_α lε ∷ [[τ, n]] -> n > 0.
Proof.
  introv Hr. inverts Hr; nat_math. 
Qed.



(**************************************************************)
(** ** Lemmas for statements                                  *)



(**************************************************************)
(** ** Lemmas for functions                                   *)

(* y-variables length correctness for auxiliary *)
Lemma function_length_y_aux : forall Γ lxτ ly lδε os ε (τ : type) ρ, 
  Γ |- djs_ϕ_aux lxτ (ly, lδε) os ε ρ ∷ τ -> length ly = length lδε.
Proof.
  introv HD. inductions HD; rew_length; jauto.
Qed.

(* y-variables length correctness *)
Lemma function_length_y : forall Γ lxτ ly lδε os ε τ, 
  Γ |- djs_ϕ_main lxτ (ly, lδε) os ε ∷ τ -> length ly = length lδε.
Proof.
  introv HD. inductions HD; rew_length; jauto.
  apply function_length_y_aux in HD; auto.
Qed.

Lemma τξ_interm : forall Γ T, Γ |- T ∷ τξ ->
  exists ει, T = djs_interm ει.
Proof.
  introv HD. inductions HD; jauto.
Qed.

Lemma interm_τξ : forall Γ ει (τ : type), 
  Γ |- djs_interm ει ∷ τ -> τ = τξ.
Proof.
  introv HD. inductions HD; auto.
Qed.

(**************************************************************)
(** ** Interesting stuff                                      *)

(* { f : function() {return this} } does not type in DJS *)
Lemma untypable_object : forall Γ τ, 
  Γ |- djs_ο ("f" :: nil, 
              (djs_ε_func (djs_ϕ_main nil 
                                      (nil, nil) 
                                      (djs_stat_seq nil) 
                                      (djs_ε_λε (djs_var "this"))) nil) :: nil) ∷ τ 
  -> False. 
Proof.
  introv HD. 
    inverts HD. clear H5 H6. inverts H8. 
    inverts H7 as HD. clear H6. destruct lτ. clear H5.
    inverts HD. clear H6 H7 H8 H9. 
    inversion H10. simpls. substs. subst lx0 lτ.
    repeat rewrite app_nil_l in *.
    inverts H6. inverts H1. inverts H3.
    rew_length in H5; nat_math.
Qed.     

(* Typing objects *)
Lemma objects_typable_only_from_empty : 
  forall Γ lπ τ, Γ |- djs_ο lπ ∷ τ -> Γ = ∅.
Proof.
  introv HD. inverts~ HD. 
Qed.

(* No typable object contains a "this" variable *)
Lemma objects_no_this : 
  forall Γ lπ τ, Γ |- djs_ο lπ ∷ τ -> ~ Mem "this" (fst lπ). 
Proof.
  introv HD. inductions HD; introv Hm; inverts* Hm. 
Qed.




















(**************************************************************)
(** ** Detecting unbound this's                               

Section has_this.

(*
   Numbers, strings, and booleans do not have a 'this'.

   An array has a 'this' if any of its elements has a 'this'

   An object has a this if there exists a 'this' in one of the expressions
*)
Fixpoint has_this_λ λ :=
match λ with 
 | djs_η _ | djs_σ _ | djs_β _ => False
 | djs_α lε => ((fix has_this_lε (lε : list djs_ε) : Prop :=
                   match lε with 
                     | nil => False
                     | ε :: lε => has_this_ε ε \/ has_this_lε lε
                   end) lε)
 | djs_ο ρ => ((fix has_this_ρ ρ : Prop :=
                  match ρ with 
                    | nil => False
                    | (_, ε) :: ρ => has_this_ε ε \/ has_this_ρ ρ
                  end) ρ)
end

(*
   'this' in expressions is fully recursive
*)
with has_this_ε ε := 
match ε with 
 | djs_ε_l     λ        => has_this_λ  λ
 | djs_ε_λε    λε       => has_this_λε λε
 | djs_ε_ass   λε ε     => has_this_λε λε \/ has_this_ε ε
 | djs_ε_unop  _  ε     => has_this_ε ε
 | djs_ε_binop _  ε1 ε2 => has_this_ε ε1 \/ has_this_ε ε2
 | djs_ε_func  ϕ  lε    => has_this_ϕ ϕ \/ 
                           ((fix has_this_lε (lε : list djs_ε) : Prop :=
                               match lε with 
                                 | nil => False
                                 | ε :: lε => has_this_ε ε \/ has_this_lε lε
                               end) lε)
 | djs_csi     ε1 ε2 _  => has_this_ε ε1 \/ has_this_ε ε2
end

(*
   For lhs-expressions:

   A variable has a 'this' if it is 'this'

   'this' can never occur as a property in a typable lhs-expression
*)
with has_this_λε λε := 
match λε with
 | djs_var  x       => (x = "this")
 | djs_prop ε  _    => has_this_ε ε
 | djs_cai  ε  _    => has_this_ε ε
 | djs_ii   ε1 ε2 _ => has_this_ε ε1 \/ has_this_ε ε2
 | djs_bai  ε1 ε2   => has_this_ε ε1 \/ has_this_ε ε2
end

(*
   'this' in statements is fully recursive
*)
with has_this_stat s :=
match s with
 | djs_stat_expr  ε         => has_this_ε ε
 | djs_stat_with  ε  s      => has_this_ε ε \/ has_this_stat s
 | djs_stat_if    ε  s1 s2  => has_this_ε ε \/ has_this_stat s1 \/ has_this_stat s2
 | djs_stat_while ε  s1     => has_this_ε ε \/ has_this_stat s1
 | djs_stat_seq   ls        => ((fix has_this_ls (ls : list djs_stat) : Prop :=
                                   match ls with 
                                     | nil => False
                                     | s :: ls => has_this_stat s \/ has_this_ls ls
                                   end) ls)
end

(*
   'this' in defined expressions is fully recursive
*)
with has_this_δε δε :=
match δε with 
 | djs_δε_expr ε => has_this_ε ε
 | djs_δε_func ϕ => has_this_ϕ ϕ
end

(*
   Functions have a 'this' if 
     the first parameter is not 'this' and
     the body has a 'this'
*)
with has_this_ϕ ϕ := 
match ϕ with 
 | djs_ϕ_main τρ lvδε s ε => match τρ with
                               | (x, _) :: _ => ifb (x = "this") then False
                                                else (((fix has_this_lvδε lvδε :=
                                                          match lvδε with 
                                                            | nil => False
                                                            | (_, δε) :: lvδε => has_this_δε δε \/ has_this_lvδε lvδε
                                                          end) lvδε)
                                                      \/ has_this_stat s \/ has_this_ε ε)   
                               | _ => (((fix has_this_lvδε lvδε :=
                                           match lvδε with 
                                             | nil => False
                                             | (_, δε) :: lvδε => has_this_δε δε \/ has_this_lvδε lvδε
                                           end) lvδε)
                                       \/ has_this_stat s \/ has_this_ε ε)
                             end
end.

(*
   'this' in programs is fully recursive
*)
Definition has_this_π π := 
match π with
 | djs_π_main ϕ => has_this_ϕ ϕ
end.

(*
   Detecting unbound this's in terms
*)
Definition has_this T :=
match T with
 | djs_term_λ  λ  => has_this_λ λ
 | djs_term_λε λε => has_this_λε λε
 | djs_term_ε  ε  => has_this_ε  ε
 | djs_term_s  s  => has_this_stat s
 | djs_term_ϕ  ϕ  => has_this_ϕ ϕ
 | djs_term_δε δε => has_this_δε δε
 | djs_term_π  π  => has_this_π π
 | djs_interm  ι   => False
end.

(*
   Detecting unbound this's in lists of terms 
*)
Definition has_this_list lT :=
  ((fix has_this_lT lT : Prop :=
      match lT with 
        | nil => False
        | T :: lT => has_this T \/ has_this_lT lT
      end) lT).

(* 
   The procedure to detect this in a term is decidable 
*)
Lemma has_this_dec : forall T, {has_this T} + {~ has_this T}.
Proof.
  assert (Gλ : forall λ, (forall y, djs_size_term y < djs_size_term λ -> 
                 {has_this y} + {~ has_this y}) -> {has_this λ} + {~ has_this λ}).
  {
    introv IH; destruct λ as [η | σ | β | lε | ρ]; try solve [simpls*].
    + destruct lε as [ | ε lε]; jauto.
      lets Hsize : djs_size_term_positive ε. 
      destruct (IH ε) as [Hε | Hε]; try solve [simpls*; rew_length; nat_math].       
      destruct (IH (djs_α lε)) as [Hlε | Hlε]; simpls; intuition.
      
    + destruct ρ as [ | (x & ε) ρ]; jauto.
      lets Hsize : djs_size_term_positive ε. 
      destruct (IH ε) as [Hε | Hε]; try solve [simpls*; rew_length; nat_math].       
      destruct (IH (djs_ο ρ)) as [Hρ | Hρ]; simpls; intuition.
  }

   assert (Gλε : forall λε, (forall y, djs_size_term y < djs_size_term λε -> 
                   {has_this y} + {~ has_this y}) -> {has_this λε} + {~ has_this λε}).
  {
    introv IH; destruct λε as [x | ε x | ε n | ε1 ε2 n | ε1 ε2 ].
    + simpls; apply string_dec.
    + apply (IH ε). simpls; nat_math.
    + apply (IH ε). simpls; nat_math.
    + destruct (IH ε1); simpls; [nat_math | intuition | ].
      destruct (IH ε2); simpls; [nat_math | intuition | intuition ].
    + destruct (IH ε1); simpls; [nat_math | intuition | ].
      destruct (IH ε2); simpls; [nat_math | intuition | intuition ].
  }

   assert (Gε : forall ε, (forall y, djs_size_term y < djs_size_term ε -> 
                 {has_this y} + {~ has_this y}) -> {has_this ε} + {~ has_this ε}).
  {
    introv IH; destruct ε as [ | | λε ε | unop ε | binop ε1 ε2 | ϕ lε | ε1 ε2 ]; try solve [simpls*; intuition]. 
    + destruct (IH λε); simpls; [nat_math | intuition | ]. 
      destruct (IH ε); simpls; [nat_math | intuition | intuition ].
    + apply (IH ε). simpls; nat_math.
    + destruct (IH ε1); simpls; [nat_math | intuition | ].
      destruct (IH ε2); simpls; [nat_math | intuition | intuition ].
    + destruct (IH ϕ) as [Hϕ | Hϕ]; [simpls; nat_math | simpls; intuition | ].
      destruct lε as [ | ε lε]; [simpls* | ].
      destruct (IH ε) as [Hε | Hε]; [ simpls; nat_math |  simpls; intuition | ].
      lets Hsize : djs_size_term_positive ε.
      destruct (IH (djs_ε_func ϕ lε)) as [Hlε | ]; simpls; [nat_math | intuition | intuition].
    + destruct (IH ε1); simpls; [nat_math | intuition | ].
      destruct (IH ε2); simpls; [nat_math | intuition | intuition ].
  }

  assert (Gs : forall s, (forall y, djs_size_term y < djs_size_term s -> 
                 {has_this y} + {~ has_this y}) -> {has_this s} + {~ has_this s}).
  {
    introv IH; destruct s as [ | ε s | ε s1 s2 | ε s | ls ]; try solve [simpls*; intuition]. 
    + destruct (IH ε); simpls; [nat_math | intuition | ]. 
      destruct (IH s); simpls; [nat_math | |]; intuition.
    + destruct (IH ε); simpls; [nat_math | intuition | ]. 
      destruct (IH s1); simpls; [nat_math | intuition | ].
      destruct (IH s2); simpls; [nat_math | |]; intuition.
    + destruct (IH ε); simpls; [nat_math | intuition | ]. 
      destruct (IH s); simpls; [nat_math | |]; intuition.
    + destruct ls as [ | s ls]; simpls*.
      lets Hsize : djs_size_term_positive s.
      destruct (IH s); simpls; [nat_math | intuition | ]. 
      destruct (IH (djs_stat_seq ls)); [simpls; nat_math | left | right];      
      simpls; intuition.
  }

  assert (Gϕ : forall ϕ, (forall y, djs_size_term y < djs_size_term ϕ -> 
                 {has_this y} + {~ has_this y}) -> {has_this ϕ} + {~ has_this ϕ}).
  {
    introv IH; destruct ϕ as [lx lyδε s ε].
    lets Hs : (IH s). lets Hε : (IH ε).
    destruct lx. simpls.
    destruct Hs; destruct Hε; try solve [simpls; nat_math]; try solve [intuition].

    cut ({(fix has_this_lvδε (lvδε : list (var * djs_δε)) : Prop :=
             match lvδε with
               | nil => False
               | (_, δε) :: lvδε0 => has_this_δε δε \/ has_this_lvδε lvδε0
             end) lyδε} + 
         {~ (fix has_this_lvδε (lvδε : list (var * djs_δε)) : Prop :=
               match lvδε with
                 | nil => False
                 | (_, δε) :: lvδε0 => has_this_δε δε \/ has_this_lvδε lvδε0
               end) lyδε}).
    introv Hyp; destruct (rm Hyp); intuition.
    {
      assert (Hm : forall x δε, Mem (x, δε) lyδε -> {has_this δε} + {~ has_this δε}).
      {
        introv Hm. apply IH.
        cut (djs_size_term δε < S ((fix djs_size_lvδε (lvδε : list (var * djs_δε)) : nat :=
                                      match lvδε with
                                        | nil => 1
                                        | (_, δε0) :: lvδε0 => (djs_size_δε δε0 + djs_size_lvδε lvδε0)%nat
                                      end) lyδε)); [nat_math | ].


        clear - Hm. gen x δε. inductions lyδε; introv Hm; inverts Hm as Hm. 
        simpls; nat_math. specializes IHlyδε Hm. destruct a; nat_math.
      }

      clear - Hm. gen Hm. inductions lyδε; intros; [intuition | ].
      destruct a as (xa & δεa).

      destruct (Hm xa δεa); auto. constructor.
      destruct IHlyδε; try solve [intuition]. 
      introv Hm'; eapply Hm. constructor*. 
    }
    
    destruct p as (x & τ).
    simpls; cases_if*.
    destruct Hs; destruct Hε; try solve [simpls; nat_math]; try solve [intuition].
    destruct lyδε as [ | (y & δε) lyδε]. intuition.
    destruct (IH δε). simpls; nat_math. intuition.
    destruct (IH (djs_ϕ_main ((x, τ) :: lx) lyδε s ε)); [ | left | right].
    lets Hsize : djs_size_term_positive δε. simpls; nat_math.
      left. right. simpl in h; cases_if*.
      rew_logic. repeat splits*. simpl in n2. cases_if*.
      rewrite decide_spec in H. apply isTrue_true in e. unfolds var; false*. 
  }

  induction T using (measure_induction_type djs_size_term).
  destruct T as [λ | λε | ε | s | ϕ | δε | π | ι]; jauto.
  destruct δε as [ε | ϕ]; simpls; intuition.
  destruct π as [ϕ]; simpls; intuition.
 Qed.

(* 
   The procedure to detect this in a list of terms is decidable 
*)
Lemma has_this_list_dec : forall lT, {has_this_list lT} + {~ has_this_list lT}.
Proof.
  inductions lT; simpls*.
  destruct (has_this_dec a) as [Ha | Ha]; intuition.
Qed.

End has_this. *)

(* ********************************************************** *)
(** * Unicity of types 

Lemma djs_unicity_of_types_λ : 
  forall λ Γ τm1 τm2 
         (IH : forall T : djs_term,
                 lt (djs_size_term T) (djs_size_term λ) ->
                  forall Γ (τm1 τm2 : type), Γ |- T ∷ τm1 -> Γ |- T ∷ τm2 -> τm1 = τm2),
    Γ |- λ ∷ τm1 -> Γ |- λ ∷ τm2 -> τm1 = τm2.
Proof.
  introv IH HD1 HD2; destruct λ; inverts HD1; inverts~ HD2.
  
  + lets Hτ : IH H0 H1. simpls; nat_math. inverts~ Hτ.
  + lets Hτ : IH H0 H4. simpls; nat_math. inverts~ Hτ.
    lets Hτ : IH H2 H6. lets Hsize : djs_size_term_positive ε1. 
    simpls; rew_length; nat_math. inverts~ Hτ.
  + lets Hτ : IH H1 H6. simpls; nat_math. inverts~ Hτ.
    lets Hτ : IH H3 H8. lets Hsize : djs_size_term_positive ε. 
    simpls; rew_length; nat_math. inverts~ Hτ.
Qed.

Lemma djs_unicity_of_types_λε : 
  forall λε Γ τm1 τm2 
         (IH : forall T : djs_term,
                 lt (djs_size_term T) (djs_size_term λε) ->
                  forall Γ (τm1 τm2 : type), Γ |- T ∷ τm1 -> Γ |- T ∷ τm2 -> τm1 = τm2),
    Γ |- λε ∷ τm1 -> Γ |- λε ∷ τm2 -> τm1 = τm2.
Proof.
  introv IH HD1 HD2; destruct λε. 

  + clear IH. inductions Γ. inverts HD1.
    inversion HD1; inversion HD2; substs*.
    - inverts H4. rewrite H3 in H8. inverts~ H8.
    - inverts H4. false. apply H7. clear - H3.
      gen v τ. inductions τρ0; introv HΦ; simpls; tryfalse.
      destruct a. cases_if*; subst lx; rewrite (split_combine_fs τρ0).
      * rewrite combine_split; [ | rewrite split_length_l; rewrite~ split_length_r]. 
        simpls. inverts e. constructor.
      * rewrite combine_split; [ | rewrite split_length_l; rewrite~ split_length_r]. 
        simpls. constructor. jauto.
    - inverts H5. false. apply H2. clear - H9.
      gen v τ0. inductions τρ; introv HΦ; simpls.
      * inverts HΦ.
      * destruct a. cases_if*; subst lx; rewrite (split_combine_fs τρ).
          rewrite combine_split; [ | rewrite split_length_l; rewrite~ split_length_r]. 
          simpls. inverts e. constructor.
          rewrite combine_split; [ | rewrite split_length_l; rewrite~ split_length_r]. 
          simpls. constructor. jauto.

  + inversion HD1; inversion HD2; substs.
    specializes IH H2 H8. simpls; nat_math.
    inverts IH. rewrite H10 in H4. inverts~ H4.

  + inversion HD1; inversion HD2; substs.
    specializes IH H2 H8. simpls; nat_math.
    inverts~ IH. 

  + inversion HD1; inversion HD2; substs.
    specializes IH H2 H11. simpls; nat_math.
    inverts~ IH. 

  + inversion HD1; inversion HD2; substs.
    specializes IH H2 H8. simpls; nat_math.
    inverts~ IH. 
Qed.

Lemma djs_unicity_of_types_ε : 
  forall ε Γ τm1 τm2 
         (IH : forall T : djs_term,
                 lt (djs_size_term T) (djs_size_term ε) ->
                  forall Γ (τm1 τm2 : type), Γ |- T ∷ τm1 -> Γ |- T ∷ τm2 -> τm1 = τm2),
    Γ |- ε ∷ τm1 -> Γ |- ε ∷ τm2 -> τm1 = τm2.
Proof.
  introv IH HD1 HD2; destruct ε; inversion HD1; inversion HD2; substs*;
  try solve [tryfalse; clear HD1 HD2; eapply IH; try eassumption; simpls; nat_math].

  + inverts H5. inverts H2.
  + inverts H11. inverts H2.
  + specializes IH H1 H8. simpls; nat_math. inverts~ IH.
Qed.  

Lemma djs_unicity_of_types_ϕ : 
  forall ϕ Γ τm1 τm2 
         (IH : forall T : djs_term,
                 lt (djs_size_term T) (djs_size_term ϕ) ->
                  forall Γ (τm1 τm2 : type), Γ |- T ∷ τm1 -> Γ |- T ∷ τm2 -> τm1 = τm2),
    Γ |- ϕ ∷ τm1 -> Γ |- ϕ ∷ τm2 -> τm1 = τm2.
Proof.
  introv IH HD1 HD2; inversion HD1; inversion HD2; substs.

  + symmetry in H6; inverts H6.
    subst lx ly lτ lδε lx0 ly0 lτ0 lδε0. subst τρx0 τρy0.
    clear - IH H4 H11; rename ls0 into ls; rename ε0 into ε.

    remember nil as τρ. clear Heqτρ.
    gen Γ τρx. inductions τρy; introv HD1 IH HD2.

    - inverts HD1; inverts HD2.
      cut (τr = τr0); try congruence.
      specializes IH H6 H8; [simpls; nat_math | inverts~ IH].

    - destruct a as (y & δε). inverts HD1; inverts* HD2.
      eapply IHτρy; try eassumption. 
      introv Hs HD1 HD2. eapply IH; try eassumption.
      simpls; nat_math.
      cut (τ = τ0); try congruence.
      specializes IH H2 H3. simpls; nat_math. inverts~ IH.

  + symmetry in H6; inverts H6.
    subst lx ly lτ lδε lx0 ly0 lτ0 lδε0. subst τρx0 τρy0.
    false*.

  + symmetry in H8; inverts H8.
    subst lx ly lτ lδε lx0 ly0 lτ0 lδε0. subst τρx0 τρy0.
    false*.

  + symmetry in H8; inverts H8.
    subst lx ly lτ lδε lx0 ly0 lτ0 lδε0. subst τρx0 τρy0.
    clear - IH H6 H15. admit.
Qed.

Theorem djs_unicity_of_types : 
  forall T Γ τm1 τm2, 
    Γ |- T ∷ τm1 -> Γ |- T ∷ τm2 -> τm1 = τm2.
Proof.
  induction T using (measure_induction djs_size_term).
  destruct T as [λ | λε | ε | s | ϕ | δε | π | ι]; introv HD1 HD2.

  + eapply djs_unicity_of_types_λ; eassumption.
  + eapply djs_unicity_of_types_λε; eassumption.
  + eapply djs_unicity_of_types_ε; eassumption.
  + inverts HD1; inverts* HD2.
  + eapply djs_unicity_of_types_ϕ; eassumption.
  + inverts HD1; inverts* HD2; eapply H; try eassumption; simpls; nat_math.
  + inverts HD1; inverts* HD2; eapply H; try eassumption; simpls; nat_math.
  + inverts HD1; inverts* HD2. 
Qed. *) *)