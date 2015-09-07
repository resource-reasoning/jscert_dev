Set Implicit Arguments.
Require Import Shared.
Require Import JsSyntax JsSyntaxAux JsCommon JsCommonAux JsPreliminary.
Require Import JsPrettyInterm JsPrettyRules.
Require Import JsInversionTactics.

(**************************************************************)
(** ** Implicit Types -- copied from JsPreliminary *)

Implicit Type b : bool.
Implicit Type n : number.
Implicit Type k : int.
Implicit Type s : string.
Implicit Type i : literal.
Implicit Type l : object_loc.
Implicit Type w : prim.
Implicit Type v : value.
Implicit Type r : ref.
Implicit Type ty : type.

Implicit Type rt : restype.
Implicit Type rv : resvalue.
Implicit Type lab : label.
Implicit Type labs : label_set.
Implicit Type R : res.
Implicit Type o : out.
Implicit Type ct : codetype.

Implicit Type x : prop_name.
Implicit Type str : strictness_flag.
Implicit Type m : mutability.
Implicit Type Ad : attributes_data.
Implicit Type Aa : attributes_accessor.
Implicit Type A : attributes.
Implicit Type Desc : descriptor.
Implicit Type D : full_descriptor.

Implicit Type L : env_loc.
Implicit Type E : env_record.
Implicit Type Ed : decl_env_record.
Implicit Type X : lexical_env.
Implicit Type O : object.
Implicit Type S : state.
Implicit Type C : execution_ctx.
Implicit Type P : object_properties_type.

Implicit Type e : expr.
Implicit Type p : prog.
Implicit Type t : stat.

Implicit Type T : Type.

(**************************************************************)
(** ** Toy sublanguage #1 - just numbers                      *)

Definition sub_numbers_elem (e : element) : Prop := 
match e with
  | element_stat t =>
      match t with
        | stat_expr e => 
            match e with
              | expr_literal i =>
                  match i with
                    | literal_number n => True
                    | _ => False
                  end
              | _ => False
            end
        | _ => False
      end
  | _ => False 
end.

Definition sub_numbers_prog (p : prog) : Prop :=
match p with
  | prog_intro _ le => Forall (fun (e : element) => sub_numbers_elem e) le
end.
       
Theorem sub_numbers_characterization : 
  forall p S C o, 
    red_prog S C p o -> 
    sub_numbers_prog p -> 
    exists S' n, o = (out_ter S' n).
Proof with inversion_jscert.
  destruct p as (s & le). gen s.
  induction le using list_ind_last; introv Hr Hs...

  + apply last_eq_nil_inv in H1. false~.

  + apply last_eq_last_inv in H1; destruct H1; subst.
    apply Forall_last_inv in Hs. destruct Hs as (Hs & Ha).
    specializes IHle (rm H4) (rm Hs).
    destruct a; try solve [false*].
    destruct s0; try solve [false*].
    destruct e; try solve [false*].
    destruct l; try solve [false*]...
Qed. 

(**************************************************************)
(** ** Toy sublanguage #1 - numbers and +                     *)

Fixpoint sub_numplus_expr (e : expr) : Prop :=
match e with
 | expr_literal i =>
   match i with
    | literal_number n => True
    | _ => False
   end
 | expr_binary_op e1 binop e2 => 
   sub_numplus_expr e1 /\ sub_numplus_expr e2 /\ 
   match binop with
    | binary_op_add  => True
    | _ => False
   end
 | _ => False
end.
  
Fixpoint sub_numplus_elem (e : element) : Prop := 
match e with
  | element_stat t =>
      match t with
        | stat_expr e => sub_numplus_expr e           
        | _ => False
      end
  | _ => False 
end.

Definition sub_numplus_prog (p : prog) : Prop :=
match p with
  | prog_intro _ le => Forall (fun (e : element) => sub_numplus_elem e) le
end.

Lemma red_sub_numplus_expr : forall (e : expr),
  sub_numplus_expr e -> forall S C o, 
    red_expr S C e o -> exists (n : number), o = out_ter S n.
Proof with inversion_jscert.
  induction e; introv Hsub; introv Hr; try solve [false*].

  destruct l; try solve [false*]... 
  eexists; reflexivity.

  simpls; destruct b; try solve [false*].
  destruct Hsub as (He1 & He2 & _).
  specializes IHe1 He1 S C. specializes IHe2 He2 S C... 
  lets (n1 & Heq1) : (rm IHe1) (rm H6); subst... 
  lets (n2 & Heq2) : (rm IHe2) (rm H6); subst...
Qed. (* Faster *)

Theorem sub_numplus_characterization : 
  forall p S C o, 
    red_prog S C p o -> 
    sub_numplus_prog p -> 
    exists S' n, o = (out_ter S' n).
Proof with inversion_jscert.
  destruct p as (s & le). gen s.
  induction le using list_ind_last; introv Hr Hs...

  + apply last_eq_nil_inv in H1. false~.

  + apply last_eq_last_inv in H1; destruct H1; subst.
    apply Forall_last_inv in Hs. destruct Hs as (Hs & Ha).
    specializes IHle (rm H4) (rm Hs).
    destruct IHle as (S' & n & Heq); subst.
    destruct a; try solve [false*].
    destruct s0; try solve [false*].
    destruct e; try solve [false*].

    - destruct l; try solve [false*]...

    - simpls; destruct b; try solve [false*]...
      apply red_sub_numplus_expr in H6; jauto.
      simpls; inverts H0. destruct H6 as (n1 & Heq); subst.
      destruct y1; inverts H2; subst...
      apply red_sub_numplus_expr in H6; jauto.
      destruct H6 as (n2 & Heq); subst...
Qed.