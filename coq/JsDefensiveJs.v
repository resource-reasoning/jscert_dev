Set Implicit Arguments.
Require Import Shared.
Require Import JsSyntax JsSyntaxAux JsCommon JsCommonAux JsPreliminary.

(**************************************************************)
(** ** Types and Environments for DefensiveJS                 *)

Definition var := string.

(* Types *)
Inductive τ_main : Type :=
 | τη : τ_main (* numbers   *)
 | τβ : τ_main (* booleans  *)
 | τσ : τ_main (* strings   *)
 | τυ : τ_main (* undefined *)
 | το : (list var * list τ_main) -> τ_main                        (* object   *)
 | τα : τ_main -> nat -> τ_main                                   (* array    *)
 | τϕ : list τ_main -> τ_main -> τ_main                           (* function *)
 | τμ : list τ_main -> list var * list τ_main -> τ_main -> τ_main (* method *)
.

Notation "{{ ρ }}"         := (το ρ) (at level 59).
Notation "[[ τ , n ]]"     := (τα τ n) (at level 59).
Notation "〈 lτ → τ 〉"     := (τϕ lτ τ) (at level 59).
Notation "《 lτ [ ρ ] → τ 》" := (τμ lτ ρ τ) (at level 59).

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

(* Objects *)
Definition djs_obj := (list var * list τ_main)%type.

(* Retrieving type of identifier from object *)
Fixpoint Φ (lx : list var) (lτ : list τ_main) (idx : string) : option τ_main :=
match lx, lτ with
 | nil, _ => None
 | _, nil => None
 | (id :: lx), (τ :: lτ) => ifb (id = idx) then Some τ
                                           else Φ lx lτ idx
end.

(* Scope frame kinds *)
Inductive κ := | κϕ : κ | κω : κ.

(* Typing Environments *)
Definition typ_env := list (djs_obj * κ).

(**************************************************************)
(** ** Syntactic categories                                   *)

(* Literals *)
Inductive djs_λ := 
 | djs_η : number -> djs_λ                (* Number  literals *)
 | djs_σ : string -> djs_λ                (* String  literals *)
 | djs_β : bool -> djs_λ                  (* Boolean literals *)
 | djs_α : list djs_ε -> djs_λ            (* Array   literals *)
 | djs_ο : list var * list djs_ε -> djs_λ (* Object  literals *)

with djs_unop := 
 | djs_unop_to_num  (* Conversion string -> number  *)
 | djs_unop_to_str  (* Conversion number -> string  *)
 | djs_unop_to_bool (* Conversion ______ -> boolean *)
 | djs_unop_min     (* Unary minus *)
 | djs_unop_bin_neg (* Unary binary negation *)

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
 | djs_ϕ_main : list (var * τ_main) -> (list var * list djs_δε) -> djs_stat -> djs_ε -> djs_ϕ

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
 | djs_ϕ_aux  : list (var * τ_main) -> (list var * list djs_δε) -> djs_stat ->  djs_ε -> djs_obj -> djs_iterm

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

Implicit Type τ  : τ_main.
Implicit Type λ  : djs_λ.
Implicit Type ε  : djs_ε.
Implicit Type λε : djs_λε.
Implicit Type s  : djs_stat.
Implicit Type ϕ  : djs_ϕ.
Implicit Type δε : djs_δε.
Implicit Type π  : djs_π.

Implicit Type ρ  : djs_obj.

Implicit Type η : number.
Implicit Type σ : string.
Implicit Type β : bool.

Implicit Type Γ : typ_env.

(**************************************************************)
(** ** Typing                                                 *)

Notation "∅" := (@nil (djs_obj * κ)) (at level 60).

Reserved Notation "Γ |- Τ ∷ τ" (at level 60).

Inductive types : typ_env -> djs_term -> type -> Prop := 

 (* Literals *)
 | typing_Num    : forall η, ∅ |- (djs_η η) ∷ τη 
 | typing_String : forall σ, ∅ |- (djs_σ σ) ∷ τσ
 | typing_Bool   : forall β, ∅ |- (djs_β β) ∷ τβ

 | typing_Array_cn : forall ε τ, 
                       ∅ |- ε ∷ τ -> 
                       ∅ |- (djs_α (ε :: nil)) ∷ [[τ, 1]]

 | typing_Array_cc : forall ε1 ε2 lε τ n,
                       ∅ |- ε1 ∷ τ -> 
                       ∅ |- djs_α (ε2 :: lε) ∷ [[τ, n]] -> 
                       ∅ |- (djs_α (ε1 :: ε2 :: lε)) ∷ [[τ, S n]]

 | typing_Object_nil : ∅ |- djs_ο (nil, nil) ∷ {{ (nil, nil) }}

 | typing_Object_cons : forall x ε τ lε lτ lx,
                          ∅ |- ε ∷ τ ->
                          ∅ |- djs_ο (lx, lε) ∷ {{ (lx, lτ) }} ->
                          ∅ |- djs_ο ((x :: lx), (ε :: lε)) ∷ {{ ((x :: lx), (τ :: lτ)) }}

 (* Left-hand-side expressions *)
 | typing_VarLoc : forall Γ lx lε x τ, 
                     Φ lx lε x = Some τ ->
                     (((lx, lε), κω) :: Γ) |- djs_term_λε (djs_var x) ∷ τ

 | typing_VarFS  : forall Γ ρ x lx lε τ, 
                     Mem x lx -> Γ |- (djs_var x) ∷ τ -> 
                     (((lx, lε), κϕ) :: Γ) |- (djs_var x) ∷ τ

 | typing_Prop : forall Γ ε lx lτ, 
                   Γ |- ε ∷ (το (lx, lτ)) -> 
                   forall x τ, 
                     Mem (x, τ) (combine lx lτ) ->
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
 | typing_NumCast  : forall Γ ε  , Γ |- ε ∷ τσ -> Γ |- (djs_ε_unop djs_unop_to_num  ε) ∷ τη
 | typing_StrCast  : forall Γ ε  , Γ |- ε ∷ τη -> Γ |- (djs_ε_unop djs_unop_to_str  ε) ∷ τσ
 | typing_BoolCast : forall Γ ε τ, Γ |- ε ∷ τ  -> Γ |- (djs_ε_unop djs_unop_to_bool ε) ∷ τβ

 (* Concatenation of strings *)
 | typing_Concat : forall Γ ε1 ε2, Γ |- ε1 ∷ τσ -> Γ |- ε2 ∷ τσ -> 
                                   Γ |- (djs_ε_binop djs_binop_add ε1 ε2) ∷ τσ

 (* Unary minus and bit-by-bit negation *)
 | typing_Unary_min :     forall Γ ε, Γ |- ε ∷ τη -> Γ |- (djs_ε_unop djs_unop_min     ε) ∷ τη
 | typing_Unary_bin_neg : forall Γ ε, Γ |- ε ∷ τη -> Γ |- (djs_ε_unop djs_unop_bin_neg ε) ∷ τη

 (* Arithmetic operators +, -, *, /, % *)
 | typing_Arith_add : forall Γ ε1 ε2, Γ |- ε1 ∷ τη -> Γ |- ε1 ∷ τη ->
                                      Γ |- (djs_ε_binop djs_binop_add ε1 ε2) ∷ τη
 | typing_Arith_sub : forall Γ ε1 ε2, Γ |- ε1 ∷ τη -> Γ |- ε1 ∷ τη ->
                                      Γ |- (djs_ε_binop djs_binop_sub ε1 ε2) ∷ τη
 | typing_Arith_mul : forall Γ ε1 ε2, Γ |- ε1 ∷ τη -> Γ |- ε1 ∷ τη ->
                                      Γ |- (djs_ε_binop djs_binop_mul ε1 ε2) ∷ τη
 | typing_Arith_div : forall Γ ε1 ε2, Γ |- ε1 ∷ τη -> Γ |- ε1 ∷ τη ->
                                      Γ |- (djs_ε_binop djs_binop_div ε1 ε2) ∷ τη
 | typing_Arith_mod : forall Γ ε1 ε2, Γ |- ε1 ∷ τη -> Γ |- ε1 ∷ τη ->
                                      Γ |- (djs_ε_binop djs_binop_mod ε1 ε2) ∷ τη

 (* Arithmetic bit-operators |, &, ^ *)
 | typing_Arith_bit_or  : forall Γ ε1 ε2, Γ |- ε1 ∷ τη -> Γ |- ε1 ∷ τη ->
                                          Γ |- (djs_ε_binop djs_binop_bor  ε1 ε2) ∷ τη
 | typing_Arith_bit_and : forall Γ ε1 ε2, Γ |- ε1 ∷ τη -> Γ |- ε1 ∷ τη ->
                                          Γ |- (djs_ε_binop djs_binop_band ε1 ε2) ∷ τη
 | typing_Arith_bit_xor : forall Γ ε1 ε2, Γ |- ε1 ∷ τη -> Γ |- ε1 ∷ τη ->
                                          Γ |- (djs_ε_binop djs_binop_bxor ε1 ε2) ∷ τη

 (* Arithmetic shift-operators <<, >>, >>> *)
 | typing_Arith_lsh  : forall Γ ε1 ε2, Γ |- ε1 ∷ τη -> Γ |- ε1 ∷ τη ->
                                       Γ |- (djs_ε_binop djs_binop_lsh ε1 ε2) ∷ τη
 | typing_Arith_rsh  : forall Γ ε1 ε2, Γ |- ε1 ∷ τη -> Γ |- ε1 ∷ τη ->
                                       Γ |- (djs_ε_binop djs_binop_rsh ε1 ε2) ∷ τη
 | typing_Arith_ursh : forall Γ ε1 ε2, Γ |- ε1 ∷ τη -> Γ |- ε1 ∷ τη ->
                                       Γ |- (djs_ε_binop djs_binop_ursh ε1 ε2) ∷ τη

 (* Comparisons for numbers: >=, <=, >, <, ==, != *)
 | typing_Comp_ν_gt  : forall Γ ε1 ε2, Γ |- ε1 ∷ τη -> Γ |- ε1 ∷ τη ->
                                       Γ |- (djs_ε_binop djs_binop_gt ε1 ε2) ∷ τη
 | typing_Comp_ν_lt  : forall Γ ε1 ε2, Γ |- ε1 ∷ τη -> Γ |- ε1 ∷ τη ->
                                       Γ |- (djs_ε_binop djs_binop_lt ε1 ε2) ∷ τη
 | typing_Comp_ν_ge  : forall Γ ε1 ε2, Γ |- ε1 ∷ τη -> Γ |- ε1 ∷ τη ->
                                       Γ |- (djs_ε_binop djs_binop_ge ε1 ε2) ∷ τη
 | typing_Comp_ν_le  : forall Γ ε1 ε2, Γ |- ε1 ∷ τη -> Γ |- ε1 ∷ τη ->
                                       Γ |- (djs_ε_binop djs_binop_le ε1 ε2) ∷ τη
 | typing_Comp_ν_eq  : forall Γ ε1 ε2, Γ |- ε1 ∷ τη -> Γ |- ε1 ∷ τη ->
                                       Γ |- (djs_ε_binop djs_binop_eq ε1 ε2) ∷ τη
 | typing_Comp_ν_neq : forall Γ ε1 ε2, Γ |- ε1 ∷ τη -> Γ |- ε1 ∷ τη ->
                                       Γ |- (djs_ε_binop djs_binop_neq ε1 ε2) ∷ τη

 (* Comparisons for strings: >=, <=, >, <, ==, != *)
 | typing_Comp_σ_gt  : forall Γ ε1 ε2, Γ |- ε1 ∷ τσ -> Γ |- ε1 ∷ τσ ->
                                       Γ |- (djs_ε_binop djs_binop_gt ε1 ε2) ∷ τσ
 | typing_Comp_σ_lt  : forall Γ ε1 ε2, Γ |- ε1 ∷ τσ -> Γ |- ε1 ∷ τσ ->
                                       Γ |- (djs_ε_binop djs_binop_lt ε1 ε2) ∷ τσ
 | typing_Comp_σ_ge  : forall Γ ε1 ε2, Γ |- ε1 ∷ τσ -> Γ |- ε1 ∷ τσ ->
                                       Γ |- (djs_ε_binop djs_binop_ge ε1 ε2) ∷ τσ
 | typing_Comp_σ_le  : forall Γ ε1 ε2, Γ |- ε1 ∷ τσ -> Γ |- ε1 ∷ τσ ->
                                       Γ |- (djs_ε_binop djs_binop_le ε1 ε2) ∷ τσ
 | typing_Comp_σ_eq  : forall Γ ε1 ε2, Γ |- ε1 ∷ τσ -> Γ |- ε1 ∷ τσ ->
                                       Γ |- (djs_ε_binop djs_binop_eq ε1 ε2) ∷ τσ
 | typing_Comp_σ_neq : forall Γ ε1 ε2, Γ |- ε1 ∷ τσ -> Γ |- ε1 ∷ τσ ->
                                       Γ |- (djs_ε_binop djs_binop_neq ε1 ε2) ∷ τσ

 (* Comparisons for numbers: ==, != *)
 | typing_Comp_β_eq  : forall Γ ε1 ε2, Γ |- ε1 ∷ τβ -> Γ |- ε1 ∷ τβ ->
                                       Γ |- (djs_ε_binop djs_binop_eq ε1 ε2) ∷ τβ
 | typing_Comp_β_neq : forall Γ ε1 ε2, Γ |- ε1 ∷ τβ -> Γ |- ε1 ∷ τβ ->
                                       Γ |- (djs_ε_binop djs_binop_neq ε1 ε2) ∷ τβ

 (* Operators for booleans: ||, && *)
 | typing_Bool_or  : forall Γ ε1 ε2, Γ |- ε1 ∷ τβ -> Γ |- ε1 ∷ τβ ->
                                     Γ |- (djs_ε_binop djs_binop_or  ε1 ε2) ∷ τβ
 | typing_Bool_and : forall Γ ε1 ε2, Γ |- ε1 ∷ τβ -> Γ |- ε1 ∷ τβ ->
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

 
 | typing_FunctionCall_aux_nil : forall Γ, Γ |- djs_εϕ_aux nil ∷ τξ

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
 | typing_Expression : forall Γ ε τ, Γ |- ε ∷ τ -> Γ |- (djs_stat_expr ε) ∷ τυ

 (* With statement *)
 | typing_With : forall Γ ε s ρ, Γ |- ε ∷ (το ρ) -> ((ρ, κω) :: Γ) |- s ∷ τυ ->
                                 Γ |- (djs_stat_with ε s) ∷ τυ

 (* If-then-else statement *)
 | typing_If : forall Γ ε s1 s2, Γ |- ε ∷ τβ -> Γ |- s1 ∷ τυ -> Γ |- s2 ∷ τυ ->
                                 Γ |- (djs_stat_if ε s1 s2) ∷ τυ
 (* While statement *)
 | typing_While : forall Γ ε s, Γ |- ε ∷ τβ -> Γ |- s ∷ τυ ->
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
 *)

 (* Base case *)
| typing_FunctionDef_main : forall Γ lxτ ly ls ε lτ τr,
    Γ |- (djs_ϕ_aux  lxτ ly (djs_stat_seq ls) ε (nil, nil)) ∷ τξ ->
    Γ |- (djs_ϕ_main lxτ ly (djs_stat_seq ls) ε)            ∷ 〈 lτ → τr 〉


 (* Base case *)
 | typing_FunctionDef_nil : forall Γ lxτ ε ls τr lx' lτ',
     let lx := fst (split lxτ) in
     let lτ := snd (split lxτ) in
     (((lx ++ lx', lτ ++ lτ')%list, κϕ) :: Γ) |- (djs_stat_seq ls) ∷ τυ ->
     (((lx ++ lx', lτ ++ lτ')%list, κϕ) :: Γ) |- ε ∷ τr ->
     Γ  |- (djs_ϕ_aux lxτ (nil, nil) (djs_stat_seq ls) ε (lx', lτ')) ∷ τξ

 (* Recursive call *)
 | typing_FunctionDef_cons : forall Γ lxτ ε τ y ly δε lδε ls lx' lτ',
     let lx := fst (split lxτ) in
     let lτ := snd (split lxτ) in
     (((lx ++ lx', lτ ++ lτ')%list, κϕ) :: Γ) |- δε ∷ τ ->
     Γ |- djs_ϕ_aux lxτ (ly, lδε) (djs_stat_seq ls) ε (lx' & y, lτ' & τ) ∷ τξ ->
     Γ |- djs_ϕ_aux lxτ (y :: ly, δε :: lδε) (djs_stat_seq ls) ε (lx', lτ') ∷ τξ

(* Method definition *)
 | typing_MethodDef : forall Γ lxτ ρy ls ε lτ ρ τ,
     Γ |- (djs_ϕ_main (("this", {{ ρ }}) :: lxτ) ρy (djs_stat_seq ls) ε) ∷ 〈 ({{ ρ }} :: lτ) → τ 〉->
     Γ |- (djs_ϕ_main lxτ ρy (djs_stat_seq ls) ε) ∷ 《 lτ [ρ] → τ 》

 (* Defined expressions *)
 | typing_DefExprExpr : forall Γ ε τ, Γ |- ε ∷ τ -> Γ |- (djs_δε_expr ε) ∷ τ
 | typing_DefExprFunc : forall Γ ϕ τ, Γ |- ϕ ∷ τ -> Γ |- (djs_δε_func ϕ) ∷ τ

 (* Programs *)
 | typing_Prog : forall Γ ϕ, Γ |- ϕ ∷ 〈 (τσ :: nil) → τσ 〉 ->
                             Γ |- (djs_π_main ϕ) ∷ 〈 (τσ :: nil) → τσ 〉

where "Γ |- T ∷ τ" := (types Γ T τ).

(**************************************************************)
(** ** Lemmas for arrays                                      *)

(* Empty arrays are not allowed *)
Lemma no_empty_array : forall Γ lε τ n, Γ |- djs_α lε ∷ [[τ, n]] -> n > 0.
Proof.
  introv Hr. inverts Hr; nat_math. 
Qed.

(* All ellements of an array are of the same type *)
Lemma array_same_type : forall Γ lε τ n, Γ |- djs_α lε ∷ [[τ, n]] -> Forall (fun ε => Γ |- ε ∷ τ) lε.
Proof with (repeat constructor*).
  inductions lε; introv HD; inverts HD; repeat constructor*.
Qed.

(* Array length correctness *)
Lemma array_length : forall Γ lε τ n, Γ |- djs_α lε ∷ [[τ, n]] -> n = length lε.
Proof.
  introv Hr. inductions Hr; 
  [ |   specializes IHHr2 (ε2 :: lε0) τ n0 (@eq_refl djs_term) (@eq_refl type)];
  rew_length in *; nat_math.
Qed.

(**************************************************************)
(** ** Lemmas for statements                                  *)

(* All statements are of type 'undefined' *)
Lemma statement_undefined : forall Γ s τ, Γ |- s ∷ τ -> τ = τυ.
Proof.
  introv HD; inverts~ HD.
Qed.

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
    inverts HD as HD. inverts H7. 
    inverts HD as HD. clear H6. destruct lτ. clear H5.
    inverts HD. inversion H1. simpls. substs. subst lx lτ.
    repeat rewrite app_nil_l in *.
    inverts H7. inverts H2. inverts H4.
    rew_length in H5; nat_math.
Qed.     