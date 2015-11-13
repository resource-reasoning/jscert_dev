Set Implicit Arguments.
Require Import Shared.
Require Import JsNumber JsSyntax JsSyntaxAux JsCommon JsCommonAux JsPreliminary.

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

Instance inhab_τ_main : Inhab τ_main.
Proof. 
  constructor. exists~ τη.
Qed.

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

(* Typing Environments *)
Definition typ_env := list djs_obj_type.  

Notation "∅" := (@nil djs_obj_type) (at level 60).

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
 | typing_VarLoc : forall Γ τρ x τ, 
                     Φ τρ x = Some τ ->
                     (τρ :: Γ) |- djs_term_λε (djs_var x) ∷ τ

 | typing_VarFS  : forall Γ τρ x τ,
                     let lx := fst (split τρ) in
                     ~ Mem x lx -> Γ |- (djs_var x) ∷ τ -> 
                       (τρ :: Γ) |- (djs_var x) ∷ τ

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
     ((τρx ++ τρ)%list :: Γ) |- (djs_stat_seq ls) ∷ τυ ->
     ((τρx ++ τρ)%list :: Γ) |- ε ∷ τ ->
     Γ  |- (djs_ϕ_aux τρx nil (djs_stat_seq ls) ε τρ τ) ∷ τξ

 (* Recursive call *)
 | typing_FunctionDef_cons : forall Γ τρx τρy ε τ y δε ls τρ τ',
     ((τρx ++ τρ)%list :: Γ) |- δε ∷ τ ->
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
    inversion H4; substs; rewrite app_cons.
    constructor~. applys~ typing_VarFS.

  + apply typing_Arith_str. applys* H.
    simpls; nat_math.

  + econstructor; try eassumption; applys* H; [simpls; nat_math | ].
    clear - H4. inductions lε; lets Hsize : djs_size_term_positive ϕ.
    - simpls; nat_math.
    - simpls. destruct lτ; [false* | ].
      assert (length lε = length lτ) by (rew_length in *; nat_math).
      specializes IHlε H; nat_math.

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

Section DJS_to_JSCert.

Inductive jscert_term :=
 | jscert_expr : expr -> jscert_term
 | jscert_stat : stat -> jscert_term
 | jscert_prog : prog -> jscert_term
.

Definition toJSC_unop (u : djs_unop) :=
match u with
 | djs_unop_add => unary_op_add                 (* Conversion to number *)
 | djs_unop_not => unary_op_not                 (* Conversion to boolean AND negation *) 
 | djs_unop_neg => unary_op_neg                 (* Unary minus *)
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
 | djs_var  x => ifb (x = "this") then expr_this 
                                  else expr_identifier x

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
                   prog_intro true (
                   element_stat (stat_expr (expr_call (expr_function
                       None nil (funcbody_intro (prog_intro true (
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
                       :: nil)) "function() {}"
                     )) nil)) :: nil)
end

with toJSC T :=
match T with
 | djs_term_λ  λ  => Some (jscert_expr (toJSC_λ    λ))
 | djs_term_λε λε => Some (jscert_expr (toJSC_λε   λε))
 | djs_term_ε  ε  => Some (jscert_expr (toJSC_ε    ε))
 | djs_term_s  s  => Some (jscert_stat (toJSC_stat s))
 | djs_term_ϕ  ϕ  => Some (jscert_expr (toJSC_ϕ    ϕ))
 | djs_term_δε δε => Some (jscert_expr (toJSC_δε   δε))
 | djs_term_π  π  => Some (jscert_prog (toJSC_π    π))
 | _              => None
end.

End DJS_to_JSCert.

Section JSCert_to_DJS.

Definition not_a_function je :=
match je with
 | expr_function _ _ _ => False
 | _ => True
end.

Lemma not_a_function_ε : forall (ε : djs_ε), not_a_function (toJSC_ε ε).
Proof.
  destruct ε; simpls~; destruct d; simpls~; cases_if; simpls~.
Qed.

Lemma not_a_function_λε : forall λε, not_a_function (toJSC_λε λε).
Proof.
  destruct λε; simpls~; cases_if*; simpls~. 
Qed.

Definition is_lhs je :=
match je with
  | expr_this 
  | expr_identifier _
  | expr_access _ _
  | expr_member _ _ => True
  | _ => False
end.

Lemma is_lhs_λε : forall λε, is_lhs (toJSC_λε λε).
Proof.
  destruct λε; simpls*; cases_if; simpls*.
Qed.

Fixpoint DJS_allowed_expr (je : expr) := 
match je with
  | expr_this => True 
  | expr_identifier s => ifb (s = "this") then false else true

  | expr_literal l => match l with
                        | literal_null => False
                        | _ => True
                      end

  | expr_array lje => ((fix DJS_allowed_lexpr lje :=
                          match lje with
                            | nil => True
                            | (Some je) :: lje => not_a_function je /\ DJS_allowed_expr je /\ DJS_allowed_lexpr lje
                            | _ => False
                          end) lje)

  | expr_object lpp => ((fix DJS_allowed_lpp lpp := 
                           match lpp with
                             | nil => True
                             | (propname_identifier _, propbody_val je) :: lpp => not_a_function je /\ DJS_allowed_expr je /\ DJS_allowed_lpp lpp
                             | _ => False
                           end) lpp)

  | expr_member je _ => not_a_function je /\ DJS_allowed_expr je 

  | expr_call je lje => match je with
                         | expr_function os ls fb => DJS_allowed_expr je /\ 
                                                     ((fix DJS_allowed_lexpr lje :=
                                                         match lje with
                                                           | nil => True
                                                           | je :: lje => DJS_allowed_expr je /\ not_a_function je /\ DJS_allowed_lexpr lje
                                                         end) lje)
                         | _ => False
                        end

  | expr_assign je1 None je2 => DJS_allowed_expr je1 /\ is_lhs je1 /\ DJS_allowed_expr je2 /\ not_a_function je2

  (* functions do not have names, programs always in strict mode *)
  | expr_function None lx (funcbody_intro (prog_intro true lel) msg) =>
    msg = "function() {}" /\
    match lel with
     (* first statement is a variable declaration *)
     | element_stat (stat_var_decl τρy) :: lel =>
       ((fix DJS_allowed_lje τρy :=
           match τρy with
             | nil => True
             | (_, Some je) :: τρy => DJS_allowed_expr je /\ DJS_allowed_lje τρy
             | _ => False
           end) τρy) /\
       match lel with
         (* functions = statement, then return *)
         | element_stat s :: element_stat (stat_return (Some je)) :: nil =>
             DJS_allowed_stat s /\ DJS_allowed_expr je /\ not_a_function je
         | _ => False
       end
     | _ => False
    end
                    
  | expr_unary_op unop je => match unop with
                              | unary_op_add
                              | unary_op_not
                              | unary_op_neg 
                              | unary_op_bitwise_not => True
                              | _ => False
                             end /\ DJS_allowed_expr je /\ not_a_function je

  | expr_binary_op je1 binop je2 => match binop with
                                      | binary_op_instanceof
                                      | binary_op_in
                                      | binary_op_strict_equal
                                      | binary_op_strict_disequal
                                      | binary_op_coma => False
                                      | _ => True
                                    end /\ DJS_allowed_expr je1 /\ not_a_function je1 /\ DJS_allowed_expr je2 /\ not_a_function je2
                        
  | expr_access je1 je2 => match je2 with
                            | expr_literal (literal_number num) => exists (n : nat), num = JsNumber.of_int n
                            | expr_binary_op je1' binop je2' => 
                              match binop with
                                | binary_op_bitwise_and => not_a_function je1' /\ DJS_allowed_expr je1' /\ 
                                                           match je2' with 
                                                             | (expr_literal (literal_number num)) => exists (n : nat), num = JsNumber.of_int n 
                                                             | _ => False
                                                           end
                                | binary_op_mod => match je2' with
                                                     | (expr_member je1'' s) => je1'' = je1 /\ 
                                                                                s = "length" /\
                                                                                match je1' with
                                                                                  | expr_binary_op 
                                                                                      je1'''
                                                                                      binary_op_unsigned_right_shift
                                                                                      (expr_literal (literal_number num)) =>  not_a_function je1''' /\ DJS_allowed_expr je1''' /\ num = JsNumber.zero
                                                                                  | _ => False
                                                                                end
                                                     | _ => False
                                                   end
                                | _ => False
                              end
                            | _ => False
                            end /\ not_a_function je1 /\ DJS_allowed_expr je1
                                 
  | expr_conditional e1 e2 e3 => match e1, e2, e3 with
                                   | expr_binary_op
                                       (expr_binary_op
                                          je2
                                          binary_op_unsigned_right_shift 
                                          (expr_literal (literal_number num)))
                                       binary_op_lt
                                       (expr_member je1 s),
                                     expr_access je1' (expr_binary_op
                                                         je2'
                                                         binary_op_unsigned_right_shift 
                                                         (expr_literal (literal_number num'))),
                                     expr_literal (literal_string _) => 
                                       DJS_allowed_expr je1' /\ not_a_function je1' /\
                                       DJS_allowed_expr je2' /\ not_a_function je2' /\ 
                                       s = "length" /\ 
                                       je1 = je1' /\ je2 = je2' /\ 
                                       num = JsNumber.zero /\ num' = JsNumber.zero
                                   | _, _, _ => False
                                 end

  | _ => False

end

with DJS_allowed_stat (js : stat) := 
match js with
 | stat_expr je => DJS_allowed_expr je /\ not_a_function je
 | stat_block ljs => ((fix DJS_allowed_lstat ljs :=
                         match ljs with
                           | nil => True
                           | js :: ljs => DJS_allowed_stat js /\ DJS_allowed_lstat ljs
                         end) ljs)
 | stat_if je jst (Some jse) => DJS_allowed_expr je /\ not_a_function je /\ DJS_allowed_stat jst /\ DJS_allowed_stat jse
 | stat_while nil je js => DJS_allowed_expr je /\ not_a_function je /\ DJS_allowed_stat js
 | _ => False
end

with DJS_allowed_prog (jp : prog) :=
match jp with
 | prog_intro true (element_stat (stat_expr (expr_call (expr_function None nil (funcbody_intro (prog_intro true lel) msg)) nil)) :: nil) => 
   msg = "function() {}" /\
   match lel with
     | element_stat (stat_var_decl τρy) :: element_stat (stat_return (Some je)) :: nil =>
       ((fix DJS_allowed_lje τρy :=
           match τρy with
             | nil => True
             | (_, Some je) :: τρy => DJS_allowed_expr je /\ DJS_allowed_lje τρy
             | _ => False
           end) τρy) /\
       exists JSCϕ, τρy = ("_", Some JSCϕ) :: nil /\ ~ not_a_function JSCϕ /\ 
                    je = (expr_function None ("x" :: nil)
                           (funcbody_intro (prog_intro true
                              (element_stat (stat_if (expr_binary_op
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
                                                     None) :: nil)) "function() {}"))
     | _ => False
   end
 | _ => False
end. 

Definition DJS_allowed_term jT :=
match jT with
 | jscert_expr je => DJS_allowed_expr je
 | jscert_stat js => DJS_allowed_stat js
 | jscert_prog jp => DJS_allowed_prog jp
end.

End JSCert_to_DJS.

Lemma mapping_correct : forall T t, toJSC T = Some t -> DJS_allowed_term t.
Proof with (try apply not_a_function_ε; try apply not_a_function_λε; try apply is_lhs_λε).
  
  Ltac solve_IH H x := specializes H x; specializes H (@eq_refl); auto; simpls; nat_math.

  induction T using (measure_induction djs_size_term).
  destruct T as [λ | λε | ε | s | ϕ | δε | π | ι]; introv HSome; simpls; inverts HSome.

  + destruct λ as [η | σ | β | α | ρ]; try solve [simpls~]. 
    - destruct α as [ | a α]; [simpls~ | ].
      lets Ha : H a. specializes Ha (@eq_refl). simpls; nat_math. 
      lets Hα : H (djs_α α). specializes Hα (@eq_refl). 
      lets Hs : djs_size_term_positive a. simpls; nat_math.
      simpls; splits~. clear. 
      destruct a; simpls~; destruct d; simpls~; cases_if*; simpls~.

    - destruct ρ as [ | (x & ε) ρ]; [simpls~ | ]. 
      lets Hr : H ε. specializes Hr (@eq_refl). simpls; nat_math. 
      lets Hα : H (djs_ο ρ). specializes Hα (@eq_refl). 
      lets Hs : djs_size_term_positive ε. simpls; nat_math.
      simpls; splits~. clear Hα Hr. 
      destruct ε; simpls~; destruct d; simpls~; cases_if*; simpls~.

  + destruct λε as [v | ε x | ε η | ε1 ε2 η | ε1 ε2].
    - simpls; cases_if*; simpls~; cases_if*.
    - simpls; splits*... solve_IH H ε.

    - specializes H ε. specializes H (@eq_refl). simpls; nat_math. 
      destruct ε; simpls*; splits*; clear H; destruct d; simpls*; cases_if; simpls~.

    - simpls; repeat splits~... 
      specializes H ε2. specializes H (@eq_refl). simpls; nat_math. 
      destruct ε2; simpls*. 
      eexists; reflexivity.
      specializes H ε1. specializes H (@eq_refl). simpls; nat_math. 
      destruct ε1; simpls*. 

    - simpls; repeat splits*...
      specializes H ε2. specializes H (@eq_refl). simpls; nat_math. 
      destruct ε2; simpls*.      
      specializes H ε1. specializes H (@eq_refl). simpls; nat_math. 
      destruct ε1; simpls*.

  + destruct ε as [λ | λε | λε ε | op ε1 | op ε1 ε2 | ϕ lε | ε1 ε2 σ ].
    - solve_IH H λ. 
    - solve_IH H λε. 
    - simpls; splits; [solve_IH H λε | | solve_IH H ε | ]... 
    - destruct op; simpls; splits~; try solve_IH H ε1... 
    - destruct op; simpls; splits~; try solve_IH H ε1; try solve_IH H ε2...
    - destruct ϕ as [τρx τρy s ε]. 
      lets Hϕ : H (djs_ϕ_main τρx τρy s ε). 
      specializes Hϕ (@eq_refl). simpls; nat_math.
      simpls; splits~. clear Hϕ.
      assert (Hyp : forall ε, Mem ε lε -> exists t, toJSC ε = Some t /\ DJS_allowed_term t).
      {
        inductions lε; introv Hm; inverts~ Hm.
        + eexists. splits. reflexivity. 
          apply H with (y := a); auto. simpls; nat_math. 
        + applys~ IHlε. introv Hs. applys~ H. simpls; nat_math.
      } clear H ε s τρx τρy.
      inductions lε; auto; splits~...
      * lets (t & (Heq & Ht)) : Hyp a. constructor. inverts~ Heq.
      * apply IHlε. introv Hm. apply Hyp. constructor~.
    - simpls; splits*... solve_IH H ε1. solve_IH H ε2.

  + destruct s as [ε | ε s1 s2 | ε s | ls ].
    - simpls; splits... solve_IH H ε.
    - simpls; splits; [solve_IH H ε | | solve_IH H s1 | solve_IH H s2]...
    - simpls; splits; [solve_IH H ε | | solve_IH H s]...
    - destruct ls as [ | s ls]; [simpls~ | ].
      lets Hr : H s. specializes Hr (@eq_refl). simpls; nat_math. 
      lets Hls : H (djs_stat_seq ls). specializes Hls (@eq_refl). 
      lets Hs : djs_size_term_positive s. simpls; nat_math.
      simpls~.

  + destruct ϕ as [τρx τρy s ε]. simpls; splits~.
    - inductions τρy; auto.
      destruct a as (y & δε); splits.
      * specializes H (djs_term_δε δε). specializes H (@eq_refl).
        simpls; nat_math. simpls*.
      * apply IHτρy with (s := s) (ε := ε).
        introv Hsize Heq. apply H with (y := y0); auto.
        simpls; nat_math.
    - solve_IH H s. 
    - solve_IH H ε.
    - apply not_a_function_ε.

  + destruct δε as [ε | ϕ]; [solve_IH H ε | solve_IH H ϕ].

  + destruct π as (ϕ). specializes H ϕ. 
    specializes H (@eq_refl). simpls; nat_math.
    destruct ϕ; simpls*.
Admitted. (* FASTER *)

(**************************************************************)
(** ** JSCert Term size                                       *)

Section JSC_Sizes.

Open Local Scope nat_scope.

Fixpoint jscert_size_stat js := 
match js with
  | stat_expr je => S (jscert_size_expr je) 
  | stat_label _ js => S (jscert_size_stat js)
  | stat_block ls => S ((fix size_ls ls :=
                           match ls with
                             | nil => 0
                             | s :: ls => jscert_size_stat s + size_ls ls
                           end) ls)
  | stat_var_decl lxoe => S ((fix size_lxoe lxoe :=
                                match lxoe with
                                  | nil => 0
                                  | (_, oe) :: lxoe => match oe with
                                                         | None => 0
                                                         | Some e => jscert_size_expr e
                                                       end + size_lxoe lxoe
                                end) lxoe)

  | stat_if e s os => S (jscert_size_expr e + jscert_size_stat s + match os with
                                                                     | None => 0
                                                                     | Some s => jscert_size_stat s
                                                                   end)
  | stat_do_while _ s e => S (jscert_size_stat s + jscert_size_expr e)
  | stat_while _ e s => S (jscert_size_expr e + jscert_size_stat s)
  | stat_with e s => S (jscert_size_expr e + jscert_size_stat s) 
  | stat_throw e => S (jscert_size_expr e)
  | stat_return oe => match oe with 
                        | None => 1
                        | Some e => S (jscert_size_expr e)
                      end
  | stat_break _ => 1
  | stat_continue _ => 1
  | stat_try s oxs os => S (jscert_size_stat s + match oxs with
                                                   | None => 0 
                                                   | Some (_, s) => jscert_size_stat s
                                                 end + match os with
                                                         | None => 0
                                                         | Some s => jscert_size_stat s
                                                       end)
  | stat_for _ oe1 oe2 oe3 s => S (match oe1 with
                                     | None => 0
                                     | Some e => jscert_size_expr e
                                   end + 
                                   match oe2 with
                                     | None => 0
                                     | Some e => jscert_size_expr e
                                   end + 
                                   match oe3 with
                                     | None => 0
                                     | Some e => jscert_size_expr e
                                   end + jscert_size_stat s
                                  )

  | stat_for_var _ lsoe oe1 oe2 s => S (((fix size_lsoe lsoe :=
                                           match lsoe with
                                             | nil => 0
                                             | (_, oe) :: lsoe => match oe with
                                                                    | None => 0
                                                                    | Some je => jscert_size_expr je
                                                                  end
                                           end) lsoe) +
                                        match oe1 with
                                          | None => 0
                                          | Some e => jscert_size_expr e
                                        end + 
                                        match oe2 with
                                          | None => 0
                                          | Some e => jscert_size_expr e
                                        end + jscert_size_stat s)

  | stat_for_in _ e1 e2 s => S (jscert_size_expr e1 + jscert_size_expr e2 + jscert_size_stat s)

  | stat_for_in_var _ _ oe e s => S (match oe with
                                       | None => 0
                                       | Some e => jscert_size_expr e
                                     end + jscert_size_expr e + jscert_size_stat s)

  

  | stat_debugger => 1

  | stat_switch _ e sb => S (jscert_size_expr e + jscert_size_switch sb)
end

with jscert_size_expr je := 
match je with
  | expr_this 
  | expr_identifier _ 
  | expr_literal _ => 1

  | expr_object lpp => S ((fix size_lpp lpp :=
                             match lpp with
                               | nil => 0
                               | (_, pb) :: lpp => jscert_size_propbody pb + size_lpp lpp
                             end) lpp)

  | expr_array loje => S (((fix size_lje loje :=
                              match loje with 
                                | nil => 0
                                | oje :: loje => match oje with
                                                   | None => 0
                                                   | Some je => jscert_size_expr je 
                                                 end  + size_lje loje
                              end) loje))  

  | expr_function _ _ fb => S (jscert_size_func fb)

  | expr_access je1 je2 => S (jscert_size_expr je1 + jscert_size_expr je2)
  | expr_member je1 _ => S (jscert_size_expr je1) 


  | expr_new je lje => S (jscert_size_expr je + ((fix size_lje lje :=
                                                    match lje with 
                                                      | nil => 0
                                                      | je :: lje => jscert_size_expr je + size_lje lje
                                                    end) lje))
  | expr_call je lje =>  S (jscert_size_expr je + ((fix size_lje lje :=
                                                    match lje with 
                                                      | nil => 0
                                                      | je :: lje => jscert_size_expr je + size_lje lje
                                                    end) lje))  

  | expr_unary_op _ je => S (jscert_size_expr je)
  | expr_binary_op je1 _ je2 => S (jscert_size_expr je1 + jscert_size_expr je2)
  | expr_conditional je1 je2 je3 => S (jscert_size_expr je1 + jscert_size_expr je2 + jscert_size_expr je3)
  | expr_assign je1 _ je2 => S (jscert_size_expr je1 + jscert_size_expr je2)
end

with jscert_size_prog jp :=
match jp with
 | prog_intro _ le => S ((fix size_le le :=
                            match le with
                              | nil => 0
                              | element_stat s :: le => jscert_size_stat s + size_le le
                              | element_func_decl _ _ fb :: le => jscert_size_func fb + size_le le
                            end) le)
end

with jscert_size_switch sb := 0

with jscert_size_func fb := 
match fb with
 | funcbody_intro jp _ => S (jscert_size_prog jp) 
end

with jscert_size_propbody pb := 
match pb with
  | propbody_val je => S (jscert_size_expr je) 
  | propbody_get fb => S (jscert_size_func fb)
  | propbody_set _ fb => S (jscert_size_func fb)
end.

Definition jscert_size_term jT :=
match jT with
 | jscert_expr je => jscert_size_expr je
 | jscert_stat js => jscert_size_stat js
 | jscert_prog jp => jscert_size_prog jp
end.

Lemma jscert_size_term_positive : forall jT, jscert_size_term jT > 0.
Proof.
  destruct jT; [destruct e | destruct s | destruct p]; simpls; try nat_math.
  destruct o; nat_math.
Qed.

End JSC_Sizes.

Lemma DJS_allowed_object : forall o, 
  DJS_allowed_term (jscert_expr (expr_object o)) ->
  forall pp, Mem pp o -> exists id v, pp = (propname_identifier id, propbody_val v) /\ DJS_allowed_term (jscert_expr v) /\ not_a_function v.
Proof.
  inductions o; introv Hyp Hm; inverts Hm.
  destruct a as (pp & pb); destruct pp; try solve [inverts Hyp]; destruct pb; try solve [inverts Hyp].
  + exists s e; splits~. simpls*. destruct e; simpl; try solve [clear Hyp; auto]. 
    remember (expr_function o0 l f) as e. simpls. destruct Hyp as (Hyp & _ & _). substs~. 
  + applys~ IHo. destruct a as (pp' & pb'); destruct pp'; try solve [inverts Hyp]; destruct pb'; try solve [inverts Hyp]; simpls*.
Admitted. (* FASTER *)

Lemma DJS_allowed_call : forall je lje, DJS_allowed_term (jscert_expr (expr_call je lje)) -> 
  DJS_allowed_term (jscert_expr je) /\ (Forall (fun je => DJS_allowed_expr je /\ not_a_function je) lje) /\ exists os ls fb, je = expr_function os ls fb.
Proof.
  introv HD; destruct je; try solve [false*]. splits.
  + simpls*.
  + rewrite <- Forall_Mem. introv Hm. inductions lje; inverts Hm.
    - simpls*.
    - applys~ IHlje. simpls*.
  + repeat eexists.
Admitted. (* FASTER *)

Lemma DJS_allowed_array : forall α, 
  DJS_allowed_term (jscert_expr (expr_array α)) ->
  forall a, Mem a α -> exists v, a = Some v /\ DJS_allowed_term (jscert_expr v) /\ not_a_function v.
Proof.
  inductions α; introv Hd Hm; inverts Hm; 
  destruct a; simpl in Hd; inverts* Hd.
Qed.

Lemma toJSC_is_expression : forall T v, toJSC T = Some (jscert_expr v) -> 
  (exists λ, T = djs_term_λ λ) \/
  (exists λε, T = djs_term_λε λε) \/
  (exists ε, T = djs_term_ε ε) \/
  (exists ϕ, T = djs_term_ϕ ϕ) \/
  (exists δε, T = djs_term_δε δε).
Proof.
  induction T using (measure_induction djs_size_term); introv.
  destruct T as [λ | λε | ε | s' | ϕ | δε | π | ι]; introv Hyp; 
  simpls*; inverts* Hyp.
Qed. 

Lemma toJSC_is_expression_not_function : forall T v, toJSC T = Some (jscert_expr v) ->
  not_a_function v -> exists (ε : djs_ε), toJSC T = toJSC ε.
Proof.
  introv Hjsc Hnf. lets Hyp : toJSC_is_expression Hjsc.
  inverts Hyp as Hyp.
    destruct Hyp as (λ & Heq); subst.
    exists~ (djs_ε_l λ). 
    inverts Hyp as Hyp.
      destruct Hyp as (λε & Heq); subst.
      exists~ (djs_ε_λε λε).
      inverts Hyp as Hyp.
        inverts Hyp. exists~ x.
        inverts Hyp as Hyp.
          destruct Hyp as (ϕ & Heq); subst.
          destruct ϕ. false Hnf. simpls; inverts~ Hjsc.  
          destruct Hyp as (δε & Heq); subst; destruct δε as [ε | ϕ].
          inverts Hjsc. exists~ ε.
          destruct ϕ. false Hnf. simpls; inverts~ Hjsc.
Qed.

Lemma toJSC_is_expression_function : forall T v, toJSC T = Some (jscert_expr v) ->
  ~ not_a_function v -> exists (ϕ : djs_ϕ), toJSC T = toJSC ϕ.
Proof.
  induction T using (measure_induction djs_size_term).
  destruct T; introv HT HnfT.
  + false HnfT. destruct d; inverts HT; simpls*.
  + false HnfT. destruct d; inverts HT; simpls*; cases_if; simpls~.
  + false HnfT. destruct d; inverts HT; simpls*; destruct d; simpls*; cases_if; simpls*.
  + false HnfT. destruct d; inverts HT; simpls*.
  + exists~ d.
  + destruct d.
    - false HnfT. destruct d; inverts HT; simpls*; destruct d; simpls*; cases_if; simpls*.
    - exists~ d.
  + destruct d as [ϕ]; false*.
  + inverts HT.
Qed.

Lemma toJSC_is_expression_as_δε : forall T je, toJSC T = Some (jscert_expr je) -> exists (δε : djs_δε), toJSC δε = toJSC T.
Proof.
  introv Ht. lets Hyp : toJSC_is_expression Ht. repeat (inverts Hyp as Hyp; jauto).
  + exists~ (djs_δε_expr (djs_ε_l x)).
  + exists~ (djs_δε_expr (djs_ε_λε x)).
  + exists~ (djs_δε_expr x).
  + exists~ (djs_δε_func x).
Qed.

Lemma toJSC_is_lhs_expression : forall T v, toJSC T = Some (jscert_expr v) ->
  is_lhs v -> exists (λε : djs_λε), toJSC T = toJSC λε.
Proof.
  induction T using (measure_induction djs_size_term).
  destruct T; introv HT Hlhs.
  + false. destruct d; inverts HT; simpls*.
  
  + destruct d; simpls.
    - exists (djs_var v0); cases_if*; subst; simpl; cases_if*.
    - inverts HT. exists~ (djs_prop d v0). 
    - inverts HT. exists~ (djs_cai d n).
    - inverts HT. exists~ (djs_ii d d0 n).
    - inverts HT. exists~ (djs_bai d d0).
 
  + destruct d; try solve [false; inverts HT; simpls*; destruct d; simpls*; cases_if; simpls*].
    - destruct d; simpls.
      * exists (djs_var v0); cases_if*; subst; simpl; cases_if*.
      * inverts HT. exists~ (djs_prop d v0). 
      * inverts HT. exists~ (djs_cai d n).
      * inverts HT. exists~ (djs_ii d d0 n).
      * inverts HT. exists~ (djs_bai d d0).

  + false.
  + false; destruct d; inverts HT; simpls*.
  + destruct d.
    - destruct d; try solve [false; inverts HT; simpls*; destruct d; simpls*; cases_if; simpls*].
      destruct d; simpls.
      * exists (djs_var v0); cases_if*; subst; simpl; cases_if*.
      * inverts HT. exists~ (djs_prop d v0). 
      * inverts HT. exists~ (djs_cai d n).
      * inverts HT. exists~ (djs_ii d d0 n).
      * inverts HT. exists~ (djs_bai d d0).

    - false; destruct d; inverts HT; simpls*.
  + destruct d as [ϕ]; false*.
  + inverts HT.
Qed.

Lemma toJSC_is_statement : forall T (s : stat), toJSC T = Some (jscert_stat s) -> 
  exists s, T = djs_term_s s.
Proof.
  induction T using (measure_induction djs_size_term); introv Hyp.
  destruct T; simpls*; inverts* Hyp.
Qed.  

Lemma toJSC_is_object : forall obj l, toJSC obj = Some (jscert_expr (expr_object l)) ->
 exists o, obj = djs_ο o \/ obj = djs_ε_l (djs_ο o) \/ obj = djs_δε_expr (djs_ε_l (djs_ο o)).
Proof.
  introv Hyp; destruct obj as [o | o | o | o | o | o | o | o]; 
  try destruct o; simpls; inverts~ Hyp; try (destruct d; inverts* H0); try (cases_if*).
  + eexists. left; reflexivity.
  + destruct d; inverts* H1. 
  + destruct d; inverts* H1. cases_if*.
Qed.

Lemma toJSC_is_array : forall arr l, toJSC arr = Some (jscert_expr (expr_array l)) ->
 exists a, arr = djs_α a \/ arr = djs_ε_l (djs_α a) \/ arr = djs_δε_expr (djs_ε_l (djs_α a)).
Proof.
  introv Hyp; destruct arr as [o | o | o | o | o | o | o | o]; 
  try destruct o; simpls; inverts~ Hyp; try (destruct d; inverts* H0); try (cases_if*).
  + eexists. left; reflexivity.
  + destruct d; inverts* H1. 
  + destruct d; inverts* H1. cases_if*.
Qed.

Lemma toJSC_is_function : forall T os ls fb, 
  toJSC T = Some (jscert_expr (expr_function os ls fb)) -> 
  (exists ϕ, T = djs_term_ϕ ϕ) \/ (exists ϕ, T = djs_term_δε (djs_δε_func ϕ)).
Proof.
  induction T using (measure_induction djs_size_term); introv Hyp.
  destruct T; repeat (destruct d; simpls*; inverts Hyp as Hyp; try cases_if*).
Qed.

Lemma mapping_complete : forall t, (exists T, toJSC T = Some t) <-> DJS_allowed_term t.
Proof with (try solve [inverts* Hyp]).
  introv; splits; [introv (T & Heq); applys~ mapping_correct; eassumption | gen t].
  
  induction t using (measure_induction jscert_size_term).

  destruct t as [e | s | p]; introv Hyp; [destruct e | destruct s; try solve [false*] | ].

  (* expr_this *)
  + exists (djs_var "this"); simpls; cases_if*.

  (* expr_identifier *)
  + simpls; cases_if*. exists (djs_var s). simpls; cases_if*.

  (* expr_literal *)
  + destruct l.
    - inverts Hyp.
    - exists~ (djs_β b).
    - exists~ (djs_η n).
    - exists~ (djs_σ s).

  (* expr_object *)
  + lets Ho : DJS_allowed_object Hyp.
    
    inductions l.
    - exists (djs_ο nil); simpls~.
    - destruct a as (pp & pb). 
      destruct pp; destruct pb; try solve [inverts Hyp].
      lets (Tl & Htl) : (rm IHl).
      * introv Hsize Hdjs. applys~ H.
        simpls; nat_math.
      * simpls*. 
      * introv Hm. apply Ho. constructor~.

      (* main part *)
      * lets (id & v & (Hpp & Hdv & Hnfv)) : Ho (propname_identifier s, propbody_val e). 
          constructor~. 
        inverts Hpp. lets~ (Tv & HTv) : H (jscert_expr v). 
          simpls; nat_math.
 
      lets (id' & v' & Hpp' & Hd' & Hv') : (rm Ho) (propname_identifier id, propbody_val v).
        constructor. inverts~ Hpp'.
      lets~ (ε & Hε) : toJSC_is_expression_not_function HTv.
      rewrite Hε in *; clear dependent Tv.
      lets (o' & Ho') : toJSC_is_object Htl.
      exists (djs_term_ε (djs_ε_l (djs_ο ((id', ε) :: o')))). 
      clear - Ho' HTv Htl; simpls; repeat fequals.
      inverts Ho' as Ho'. inverts~ Htl.
      inverts Ho' as Ho'; inverts~ Htl.

  (* expr_array *)
  + lets Hd : DJS_allowed_array (rm Hyp). inductions l.
    - exists* (djs_term_λ (djs_α nil)). 
    - lets (va & Heqva & Hdva & Hnfva) : Hd a. constructor. subst.
      lets~ (Tva & HTva) : H (jscert_expr va). simpls; nat_math.
      lets~ (a & Ha) : toJSC_is_expression_not_function HTva.
      rewrite Ha in *; clear dependent Tva.
      lets (Tl & Htl) : (rm IHl). 
        introv Hs Hdy. applys~ H. simpls; nat_math. 
        introv Hm. apply Hd. constructor~.
      clear H Hd. lets (αl & Hαl) : toJSC_is_array Htl.
      exists (djs_term_λ (djs_α (a :: αl))). 
      inverts Hαl as Hαl; [ | inverts Hαl as Hαl]; simpls*; repeat fequals.

  (* expr_function *)
  + destruct o; [inverts Hyp | ].
    destruct f as (p & msg). 
    destruct p as (str & le).
    destruct str... destruct le...
    destruct e... destruct s...
    destruct le... destruct e...
    destruct Hyp as (Hmsg & Hτρy & Hyp). subst.
    destruct le... destruct e...
    destruct s0... destruct o...
    destruct le...
    destruct Hyp as (Hs & He).
    
    assert (Hl0 : forall x je, Mem (x, Some je) l0 -> DJS_allowed_term (jscert_expr je) /\ exists (δε : djs_δε), toJSC δε = Some (jscert_expr je)).
    {
      inductions l0; introv Hm; inverts Hm.
      + splits*. lets* (Te & HTe) : H (jscert_expr je). simpls; nat_math.
        lets (δε & Hδε) : toJSC_is_expression_as_δε HTe.
        exists δε. rewrite~ Hδε.
      + destruct a as (x' & je'). destruct je'; [ | false].
        apply IHl0 with (s := s) (e := e) (x := x); jauto.
        introv Hsize Hd. applys~ H. simpls; nat_math.
    } 

    lets* (Tσ & Hσ) : H (jscert_stat s). simpls; nat_math.
    lets* (σ & HTσ) : toJSC_is_statement Hσ.
    rewrite HTσ in Hσ; clear dependent Tσ.
   
    lets* (Tε & Hε) : H (jscert_expr e). simpls; nat_math. clear H.
    lets* (ε & HTε) : toJSC_is_expression_not_function Hε.
    rewrite HTε in Hε; clear dependent Tε.

    inductions l0.
    - exists (djs_term_ϕ (djs_ϕ_main (combine l ((fix larbitrary l :=
                                                    match l with
                                                      | nil => nil
                                                      | _ :: l => arbitrary :: larbitrary l
                                                    end) l)) nil σ ε)). 
      simpls; repeat fequals. clear. 
      rewrite~ combine_split. inductions l; rew_length in *; nat_math.
    - destruct a as (x, o). destruct o; [ | false*].
      specializes IHl0 Hs He; jauto. 
      specializes IHl0 Hσ Hε. 
        introv Hm. apply Hl0 with (x0 := x0). constructor~.
      destruct IHl0 as (Τϕ & Hϕ).
      lets Hϕ' : toJSC_is_function Hϕ.
      inverts Hϕ' as Hϕ'; destruct Hϕ' as (ϕ & Heq); subst.

      * destruct ϕ as [τρx' τρy' s' ε']. inverts Hϕ.
        lets (Hde0 & (δε & Hδε)) : Hl0 x e0. constructor.
        exists (djs_term_ϕ (djs_ϕ_main τρx' ((x, δε) :: τρy') s' ε')). 
        simpls. repeat fequals.

      * destruct ϕ as [τρx' τρy' s' ε']. inverts Hϕ.
        lets (Hde0 & (δε & Hδε)) : Hl0 x e0. constructor.
        exists (djs_term_ϕ (djs_ϕ_main τρx' ((x, δε) :: τρy') s' ε')). 
        simpls. repeat fequals.

  (* expr_access *)
  + destruct e2; try solve [simpls; inverts Hyp; tryfalse]. 
    - destruct l; try solve [simpls; inverts Hyp; tryfalse].
      destruct Hyp as ((n' & Heq) & Hnfe1 & Hde1). subst.
      lets~ (Tε & HTε) : H (jscert_expr e1). 
        simpls; nat_math.
      lets (ε & Hε) : toJSC_is_expression_not_function HTε Hnfe1.
      rewrite Hε in *; clear dependent Tε.
      exists (djs_term_ε (djs_ε_λε (djs_cai ε n'))). 
      simpls; repeat fequals.
    - destruct b; simpl in Hyp; try solve [false*].
      * destruct e2_2; try solve [false*].
        lets Hs : string_dec s "length". 
        inverts Hs as Hs; [ | false*]. 
        destruct e2_1; try solve [false*].
        destruct b; try solve [false*].
        destruct e2_1_2; try solve [false*].
        destruct l; try solve [false*].
        destruct Hyp as ((Heq1 & _ & Hnf2 & Hd2 & Heq2) & Hnf & Hde); subst.        
        lets~ (Te1 & HTe1) : H (jscert_expr e1). simpls; nat_math.
        lets~ (Te2 & HTe2) : H (jscert_expr e2_1_1). simpls; nat_math.
        lets~ (ε1 & Hε1) : toJSC_is_expression_not_function HTe1 Hnf.
        lets~ (ε2 & Hε2) : toJSC_is_expression_not_function HTe2 Hnf2.
        rewrite Hε1 in *; rewrite Hε2 in *; clear dependent Te1; clear dependent Te2.
        exists (djs_term_λε (djs_bai ε1 ε2)).
        simpls; repeat fequals.
      * destruct e2_2; try solve [false*].
        destruct l; try solve [false*].
        destruct Hyp as ((Hnf2 & Hd2 & He1) & Hnf1 & Hd1); subst.  
        lets~ (Te1 & HTe1) : H (jscert_expr e1). simpls; nat_math.
        lets~ (Te2 & HTe2) : H (jscert_expr e2_1). simpls; nat_math.
        lets~ (ε1 & Hε1) : toJSC_is_expression_not_function HTe1 Hnf1.
        lets~ (ε2 & Hε2) : toJSC_is_expression_not_function HTe2 Hnf2.
        rewrite Hε1 in *; rewrite Hε2 in *; clear dependent Te1; clear dependent Te2.
        destruct He1 as (n' & Heq); subst.
        exists (djs_term_λε (djs_ii ε1 ε2 n')).
        simpls; repeat fequals.

  (* expr_member *) 
  + destruct Hyp as (Hnf & Hd).
    lets~ (Te & HTe) : H (jscert_expr e). simpls; nat_math.
    lets~ (ε & Hε) : toJSC_is_expression_not_function HTe Hnf.
    rewrite Hε in *; inverts HTe; clear dependent Te. exists~ (djs_term_λε (djs_prop ε s)).

  (* expr_new *)
  + false*.

  (* expr_call *)
  + cut (exists ϕ lε, toJSC (djs_δε_expr (djs_ε_func ϕ lε)) = Some (jscert_expr (expr_call e l))).
    - introv (ϕ & lε & Heq). eexists; jauto.
    - inductions l. 
      * apply DJS_allowed_call in Hyp. 
        destruct Hyp as (Hde & Hdl & (os & ls & fb & Heq)). 
        rewrite <- Forall_Mem in Hdl.

        lets~ (Te & HTe) : H (jscert_expr e). simpls; nat_math.
        rewrite Heq in HTe. lets Hyp : toJSC_is_function HTe. rewrite <- Heq in HTe.
        inverts Hyp as Hyp; destruct Hyp as (ϕ & Hϕ); exists ϕ (@nil djs_ε); 
        simpls; repeat fequals; substs~; inverts~ HTe.

      * lets Hyp' : DJS_allowed_call Hyp. 
        destruct Hyp' as (Hde & Hdl & (os & ls & fb & Heq)). 
        rewrite <- Forall_Mem in Hdl.

        lets (Hda & Hnfa) : Hdl a. constructor.
        lets (ϕ & lε & Hlε) : IHl. introv Hs Hd. applys~ H. simpls; nat_math.
        subst e; simpls; splits*. 

        lets~ (Te & Hε) : H (jscert_expr a). simpls; nat_math. 
        lets~ (ε & HTe) : toJSC_is_expression_not_function Hε.
        rewrite HTe in Hε; clear dependent Te.
       
        exists ϕ (ε :: lε). simpls; repeat fequals.
    
  (* expr_unary_op *)
  + destruct Hyp as (Hop & Hde & Hnfe). 
    lets~ (Te & Hε) : H (jscert_expr e). simpl; nat_math.
    lets~ (ε & HTe) : toJSC_is_expression_not_function Hε.
    rewrite HTe in Hε; clear dependent Te.

    destruct u; tryfalse.
      exists (djs_term_ε (djs_ε_unop djs_unop_add ε)); simpls; repeat fequals.
      exists (djs_term_ε (djs_ε_unop djs_unop_neg ε)); simpls; repeat fequals.
      exists (djs_term_ε (djs_ε_unop djs_unop_bitwise_neg ε)); simpls; repeat fequals.
      exists (djs_term_ε (djs_ε_unop djs_unop_not ε)); simpls; repeat fequals.

  (* expr_binary_op *)
  + destruct Hyp as (Hop & Hde1 & Hnfe1 & Hde2 & Hnfe2). 
    lets~ (Te1 & Hε1) : H (jscert_expr e1). simpl; nat_math.
    lets~ (ε1 & HTe1) : toJSC_is_expression_not_function Hε1.
    rewrite HTe1 in Hε1; clear dependent Te1.
    lets~ (Te2 & Hε2) : H (jscert_expr e2). simpl; nat_math.
    lets~ (ε2 & HTe2) : toJSC_is_expression_not_function Hε2.
    rewrite HTe2 in Hε2; clear dependent Te2.

    destruct b; tryfalse.
      exists (djs_term_ε (djs_ε_binop djs_binop_mul ε1 ε2)); simpls; repeat fequals.
      exists (djs_term_ε (djs_ε_binop djs_binop_div ε1 ε2)); simpls; repeat fequals.
      exists (djs_term_ε (djs_ε_binop djs_binop_mod ε1 ε2)); simpls; repeat fequals.
      exists (djs_term_ε (djs_ε_binop djs_binop_add ε1 ε2)); simpls; repeat fequals.
      exists (djs_term_ε (djs_ε_binop djs_binop_sub ε1 ε2)); simpls; repeat fequals.
      exists (djs_term_ε (djs_ε_binop djs_binop_lsh ε1 ε2)); simpls; repeat fequals.
      exists (djs_term_ε (djs_ε_binop djs_binop_rsh ε1 ε2)); simpls; repeat fequals.
      exists (djs_term_ε (djs_ε_binop djs_binop_ursh ε1 ε2)); simpls; repeat fequals.
      exists (djs_term_ε (djs_ε_binop djs_binop_lt ε1 ε2)); simpls; repeat fequals.
      exists (djs_term_ε (djs_ε_binop djs_binop_gt ε1 ε2)); simpls; repeat fequals.
      exists (djs_term_ε (djs_ε_binop djs_binop_le ε1 ε2)); simpls; repeat fequals.
      exists (djs_term_ε (djs_ε_binop djs_binop_ge ε1 ε2)); simpls; repeat fequals.
      exists (djs_term_ε (djs_ε_binop djs_binop_eq ε1 ε2)); simpls; repeat fequals.
      exists (djs_term_ε (djs_ε_binop djs_binop_neq ε1 ε2)); simpls; repeat fequals.
      exists (djs_term_ε (djs_ε_binop djs_binop_band ε1 ε2)); simpls; repeat fequals.
      exists (djs_term_ε (djs_ε_binop djs_binop_bor ε1 ε2)); simpls; repeat fequals.
      exists (djs_term_ε (djs_ε_binop djs_binop_bxor ε1 ε2)); simpls; repeat fequals.
      exists (djs_term_ε (djs_ε_binop djs_binop_and ε1 ε2)); simpls; repeat fequals.
      exists (djs_term_ε (djs_ε_binop djs_binop_or ε1 ε2)); simpls; repeat fequals.

  (* expr_conditional *)
  + destruct e1... destruct e1_1... destruct b0...
    destruct e1_1_2... destruct l... destruct b...
    destruct e1_2... destruct e2... destruct e2_2...
    destruct b... destruct e2_2_2... destruct l...
    destruct e3... destruct l... 
    destruct Hyp as (Hd1 & Hnf1 & Hd2 & Hnf2 & Heq1 & Heq2 & Heq3 & Heq4 & Heq5); subst. 
    
    lets~ (Te1 & Hε1) : H (jscert_expr e2_1). simpl; nat_math.
    lets~ (ε1 & HTe1) : toJSC_is_expression_not_function Hε1.
    rewrite HTe1 in Hε1; clear dependent Te1.
    lets~ (Te2 & Hε2) : H (jscert_expr e2_2_1). simpl; nat_math.
    lets~ (ε2 & HTe2) : toJSC_is_expression_not_function Hε2.
    rewrite HTe2 in Hε2; clear dependent Te2.

    exists (djs_term_ε (djs_csi ε1 ε2 s0)). 
    simpls; inverts Hε1; inverts~ Hε2.

  (* expr_assign *)
  + destruct o...
    destruct Hyp as (Hde1 & Hnfe1 & Hde2 & Hnfe2). 
    lets~ (Te1 & Hε1) : H (jscert_expr e1). simpl; nat_math.
    lets~ (ε1 & HTe1) : toJSC_is_lhs_expression Hε1.
    rewrite HTe1 in Hε1; clear dependent Te1.
    lets~ (Te2 & Hε2) : H (jscert_expr e2). simpl; nat_math.
    lets~ (ε2 & HTe2) : toJSC_is_expression_not_function Hε2.
    rewrite HTe2 in Hε2; clear dependent Te2.
   
    exists (djs_term_ε (djs_ε_ass ε1 ε2)); simpls*; inverts Hε1; inverts~ Hε2.

  (* stat_expr *)
  + lets (Te & HTe) : H (jscert_expr e); simpls*; try nat_math.
    lets* (ε & Hε) : toJSC_is_expression_not_function e. 
    rewrite Hε in *; clear dependent Te. 
    exists* (djs_stat_expr ε). 
    simpls; repeat fequals.

  (* stat_block *)
  + induction l as [ | s ls].
    - exists (djs_stat_seq nil); simpls~.
    - lets (Tls & HTls) : IHls; [ | simpls* | ].
      introv Hs. apply H. simpls; nat_math.
      lets~ (Ts & HTs') : H (jscert_stat s). 
      simpls; nat_math. simpls*.
      lets* (s' & Hs') : toJSC_is_statement HTs'; subst.
      lets* (s'' & Hls'') : toJSC_is_statement HTls; subst.
      clear H Hyp IHls.
      assert (exists ls', s'' = djs_stat_seq ls').
      { 
        destruct s''; simpls; inverts HTls.
        eexists; reflexivity.
      } lets (ls' & Heq) : H; subst.
      exists (djs_stat_seq (s' :: ls')). 
      simpls; repeat fequals.      

  (* stat_if *)
  + destruct o; [ | false*].
    destruct Hyp as (Hde & Hnfe & Hds & Hds0).
    lets~ (Te & HTe) : H (jscert_expr e). simpls*; try nat_math.
    lets* (ε & Hε) : toJSC_is_expression_not_function e. 
    rewrite Hε in *; clear dependent Te.
    lets~ (Ts & HTs') : H (jscert_stat s). simpls; try nat_math.
    lets~ (Ts0 & HTs'') : H (jscert_stat s0). simpls; try nat_math.
    lets* (s' & Hs') : toJSC_is_statement HTs'; subst.
    lets* (s'' & Hs'') : toJSC_is_statement HTs''; subst.
    exists~ (djs_term_s (djs_stat_if ε s' s'')). 
    simpls; repeat fequals.
   
  (* stat_while *)
  + destruct l; [ | inverts Hyp].
    destruct Hyp as (Hde & Hnfe & Hds).
    lets~ (Te & HTe) : H (jscert_expr e). simpls*; try nat_math.
    lets* (ε & Hε) : toJSC_is_expression_not_function e. 
    rewrite Hε in *; clear dependent Te.
    lets~ (Ts & HTs') : H (jscert_stat s). simpls; try nat_math.
    lets* (s' & Hs') : toJSC_is_statement HTs'; subst.
    exists~ (djs_term_s (djs_stat_while ε s')). 
    simpls; repeat fequals.

  (* prog *)
  + destruct p as [s el].
    destruct s...  destruct el... destruct e...
    destruct s...  destruct e... destruct e...
    destruct o...  destruct f... destruct p...
    destruct l0... destruct s0... destruct l...
    destruct el... destruct l1... destruct e...
    destruct s0... destruct l1... destruct e...
    destruct s0... destruct o... destruct l1...
    destruct Hyp as (Hs & Hτρy & (JSCϕ & Hl & Hnfϕ & Heq)).    
    subst; destruct Hτρy as (Hdϕ & _).

    lets~ (Tϕ & Hϕ) : H (jscert_expr JSCϕ). simpls; nat_math.
    lets~ (ϕ & HTϕ) : toJSC_is_expression_function Hϕ.
    rewrite HTϕ in Hϕ; clear dependent Tϕ.

    exists (djs_term_π (djs_π_main ϕ)).
    simpls; repeat fequals.
Admitted. (* FASTER *)