Set Implicit Arguments.
Require Import Shared.
Require Import JsSyntax JsSyntaxAux JsCommon JsCommonAux JsPreliminary.
Require Import JsPrettyInterm JsPrettyRules.

(**************************************************************)
(** ** Inversion principles as axioms                         *)

Module Type InvExpr.

Parameter inv_red_expr_this
     : forall (S : state) (C : execution_ctx) (oo : out)
         (P : state -> execution_ctx -> out -> Prop),
       (red_expr S C (expr_basic expr_this) oo ->
        forall (S0 : state) (C0 : execution_ctx) (exte : ext_expr) (o : out),
        @eq (option out) (out_of_ext_expr (expr_basic expr_this))
          (@Some out oo) ->
        abort oo ->
        not (abort_intercepted_expr (expr_basic expr_this)) ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq ext_expr exte (expr_basic expr_this) -> @eq out o oo -> P S C oo) ->
       (red_expr S C (expr_basic expr_this) oo ->
        forall (S0 : state) (C0 : execution_ctx) (v : value),
        @eq value v (execution_ctx_this_binding C) ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq out (out_ter S (res_val v)) oo -> P S C (out_ter S (res_val v))) ->
       red_expr S C (expr_basic expr_this) oo -> P S C oo.

Parameter inv_red_expr_identifier
     : forall (S : state) (C : execution_ctx) (a1 : string) 
         (oo : out) (P : state -> execution_ctx -> string -> out -> Prop),
       (red_expr S C (expr_basic (expr_identifier a1)) oo ->
        forall (S0 : state) (C0 : execution_ctx) (exte : ext_expr) (o : out),
        @eq (option out) (out_of_ext_expr (expr_basic (expr_identifier a1)))
          (@Some out oo) ->
        abort oo ->
        not (abort_intercepted_expr (expr_basic (expr_identifier a1))) ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq ext_expr exte (expr_basic (expr_identifier a1)) ->
        @eq out o oo -> P S C a1 oo) ->
       (red_expr S C (expr_basic (expr_identifier a1)) oo ->
        forall (S0 : state) (C0 : execution_ctx) (x : prop_name)
          (y1 : specret ref) (o : out),
        @red_spec ref S C (spec_identifier_resolution C a1) y1 ->
        red_expr S C (expr_identifier_1 y1) oo ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq string x a1 -> @eq out o oo -> P S C a1 oo) ->
       red_expr S C (expr_basic (expr_identifier a1)) oo -> P S C a1 oo.

Parameter inv_red_expr_literal
     : forall (S : state) (C : execution_ctx) (a1 : literal) 
         (oo : out) (P : state -> execution_ctx -> literal -> out -> Prop),
       (red_expr S C (expr_basic (expr_literal a1)) oo ->
        forall (S0 : state) (C0 : execution_ctx) (exte : ext_expr) (o : out),
        @eq (option out) (out_of_ext_expr (expr_basic (expr_literal a1)))
          (@Some out oo) ->
        abort oo ->
        not (abort_intercepted_expr (expr_basic (expr_literal a1))) ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq ext_expr exte (expr_basic (expr_literal a1)) ->
        @eq out o oo -> P S C a1 oo) ->
       (red_expr S C (expr_basic (expr_literal a1)) oo ->
        forall (S0 : state) (C0 : execution_ctx) (i : literal) (v : value),
        @eq value v (value_prim (convert_literal_to_prim a1)) ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq literal i a1 ->
        @eq out (out_ter S (res_val v)) oo ->
        P S C a1 (out_ter S (res_val v))) ->
       red_expr S C (expr_basic (expr_literal a1)) oo -> P S C a1 oo.

Parameter inv_red_expr_object
     : forall (S : state) (C : execution_ctx)
         (a1 : list (prod propname propbody)) (oo : out)
         (P : state ->
              execution_ctx -> list (prod propname propbody) -> out -> Prop),
       (red_expr S C (expr_basic (expr_object a1)) oo ->
        forall (S0 : state) (C0 : execution_ctx) (exte : ext_expr) (o : out),
        @eq (option out) (out_of_ext_expr (expr_basic (expr_object a1)))
          (@Some out oo) ->
        abort oo ->
        not (abort_intercepted_expr (expr_basic (expr_object a1))) ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq ext_expr exte (expr_basic (expr_object a1)) ->
        @eq out o oo -> P S C a1 oo) ->
       (red_expr S C (expr_basic (expr_object a1)) oo ->
        forall (S0 : state) (C0 : execution_ctx) (pds : propdefs)
          (o1 o : out),
        red_expr S C (spec_construct_prealloc prealloc_object (@nil value))
          o1 ->
        red_expr S C (expr_object_0 o1 a1) oo ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq (list (prod propname propbody)) pds a1 ->
        @eq out o oo -> P S C a1 oo) ->
       red_expr S C (expr_basic (expr_object a1)) oo -> P S C a1 oo.

Parameter inv_red_expr_array
     : forall (S : state) (C : execution_ctx) (a1 : list (option expr))
         (oo : out)
         (P : state -> execution_ctx -> list (option expr) -> out -> Prop),
       (red_expr S C (expr_basic (expr_array a1)) oo ->
        forall (S0 : state) (C0 : execution_ctx) (exte : ext_expr) (o : out),
        @eq (option out) (out_of_ext_expr (expr_basic (expr_array a1)))
          (@Some out oo) ->
        abort oo ->
        not (abort_intercepted_expr (expr_basic (expr_array a1))) ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq ext_expr exte (expr_basic (expr_array a1)) ->
        @eq out o oo -> P S C a1 oo) ->
       (red_expr S C (expr_basic (expr_array a1)) oo ->
        forall (S0 : state) (C0 : execution_ctx) (oes : list (option expr))
          (o1 o : out),
        red_expr S C (spec_construct_prealloc prealloc_array (@nil value)) o1 ->
        red_expr S C (expr_array_0 o1 a1) oo ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq (list (option expr)) oes a1 -> @eq out o oo -> P S C a1 oo) ->
       red_expr S C (expr_basic (expr_array a1)) oo -> P S C a1 oo.

Parameter inv_red_expr_function
     : forall (S : state) (C : execution_ctx) (a1 : option string)
         (a2 : list string) (a3 : funcbody) (oo : out)
         (P : state ->
              execution_ctx ->
              option string -> list string -> funcbody -> out -> Prop),
       (red_expr S C (expr_basic (expr_function a1 a2 a3)) oo ->
        forall (S0 : state) (C0 : execution_ctx) (exte : ext_expr) (o : out),
        @eq (option out)
          (out_of_ext_expr (expr_basic (expr_function a1 a2 a3)))
          (@Some out oo) ->
        abort oo ->
        not (abort_intercepted_expr (expr_basic (expr_function a1 a2 a3))) ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq ext_expr exte (expr_basic (expr_function a1 a2 a3)) ->
        @eq out o oo -> P S C a1 a2 a3 oo) ->
       (red_expr S C (expr_basic (expr_function a1 a2 a3)) oo ->
        forall (S0 : state) (C0 : execution_ctx) (args : list string)
          (bd : funcbody) (lex : lexical_env) (o : out),
        @eq lexical_env lex (execution_ctx_lexical_env C) ->
        red_expr S C
          (spec_creating_function_object a2 a3 lex (funcbody_is_strict a3))
          oo ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq (option string) (@None string) a1 ->
        @eq (list string) args a2 ->
        @eq funcbody bd a3 -> @eq out o oo -> P S C (@None string) a2 a3 oo) ->
       (red_expr S C (expr_basic (expr_function a1 a2 a3)) oo ->
        forall (lex' : list nat) (S' : state) (L : env_loc)
          (lextail : list env_loc) (E : env_record) 
          (o1 : out) (S0 : state) (C0 : execution_ctx) 
          (s : string) (args : list string) (bd : funcbody) 
          (o : out),
        @eq (prod (list nat) state) (@pair (list nat) state lex' S')
          (lexical_env_alloc_decl S (execution_ctx_lexical_env C)) ->
        @eq (list nat) lex' (@cons env_loc L lextail) ->
        env_record_binds S' L E ->
        red_expr S' C (spec_env_record_create_immutable_binding L s) o1 ->
        red_expr S' C (expr_function_1 s a2 a3 L lex' o1) oo ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq (option string) (@Some string s) a1 ->
        @eq (list string) args a2 ->
        @eq funcbody bd a3 -> @eq out o oo -> P S C (@Some string s) a2 a3 oo) ->
       red_expr S C (expr_basic (expr_function a1 a2 a3)) oo ->
       P S C a1 a2 a3 oo.

Parameter inv_red_expr_access
     : forall (S : state) (C : execution_ctx) (a1 a2 : expr) 
         (oo : out)
         (P : state -> execution_ctx -> expr -> expr -> out -> Prop),
       (red_expr S C (expr_basic (expr_access a1 a2)) oo ->
        forall (S0 : state) (C0 : execution_ctx) (exte : ext_expr) (o : out),
        @eq (option out) (out_of_ext_expr (expr_basic (expr_access a1 a2)))
          (@Some out oo) ->
        abort oo ->
        not (abort_intercepted_expr (expr_basic (expr_access a1 a2))) ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq ext_expr exte (expr_basic (expr_access a1 a2)) ->
        @eq out o oo -> P S C a1 a2 oo) ->
       (red_expr S C (expr_basic (expr_access a1 a2)) oo ->
        forall (S0 : state) (C0 : execution_ctx) (e1 e2 : expr)
          (y1 : specret value) (o : out),
        @red_spec value S C (spec_expr_get_value a1) y1 ->
        red_expr S C (expr_access_1 y1 a2) oo ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq expr e1 a1 -> @eq expr e2 a2 -> @eq out o oo -> P S C a1 a2 oo) ->
       red_expr S C (expr_basic (expr_access a1 a2)) oo -> P S C a1 a2 oo.

Parameter inv_red_expr_member
     : forall (S : state) (C : execution_ctx) (a1 : expr) 
         (a2 : string) (oo : out)
         (P : state -> execution_ctx -> expr -> string -> out -> Prop),
       (red_expr S C (expr_basic (expr_member a1 a2)) oo ->
        forall (S0 : state) (C0 : execution_ctx) (exte : ext_expr) (o : out),
        @eq (option out) (out_of_ext_expr (expr_basic (expr_member a1 a2)))
          (@Some out oo) ->
        abort oo ->
        not (abort_intercepted_expr (expr_basic (expr_member a1 a2))) ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq ext_expr exte (expr_basic (expr_member a1 a2)) ->
        @eq out o oo -> P S C a1 a2 oo) ->
       (red_expr S C (expr_basic (expr_member a1 a2)) oo ->
        forall (x : prop_name) (S0 : state) (C0 : execution_ctx) 
          (e1 : expr) (o : out),
        red_expr S C
          (expr_basic (expr_access a1 (expr_literal (literal_string a2)))) oo ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq expr e1 a1 -> @eq string x a2 -> @eq out o oo -> P S C a1 a2 oo) ->
       red_expr S C (expr_basic (expr_member a1 a2)) oo -> P S C a1 a2 oo.

Parameter inv_red_expr_new
     : forall (S : state) (C : execution_ctx) (a1 : expr) 
         (a2 : list expr) (oo : out)
         (P : state -> execution_ctx -> expr -> list expr -> out -> Prop),
       (red_expr S C (expr_basic (expr_new a1 a2)) oo ->
        forall (S0 : state) (C0 : execution_ctx) (exte : ext_expr) (o : out),
        @eq (option out) (out_of_ext_expr (expr_basic (expr_new a1 a2)))
          (@Some out oo) ->
        abort oo ->
        not (abort_intercepted_expr (expr_basic (expr_new a1 a2))) ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq ext_expr exte (expr_basic (expr_new a1 a2)) ->
        @eq out o oo -> P S C a1 a2 oo) ->
       (red_expr S C (expr_basic (expr_new a1 a2)) oo ->
        forall (S0 : state) (C0 : execution_ctx) (e1 : expr)
          (e2s : list expr) (y1 : specret value) (o : out),
        @red_spec value S C (spec_expr_get_value a1) y1 ->
        red_expr S C (expr_new_1 y1 a2) oo ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq expr e1 a1 ->
        @eq (list expr) e2s a2 -> @eq out o oo -> P S C a1 a2 oo) ->
       red_expr S C (expr_basic (expr_new a1 a2)) oo -> P S C a1 a2 oo.

Parameter inv_red_expr_call
     : forall (S : state) (C : execution_ctx) (a1 : expr) 
         (a2 : list expr) (oo : out)
         (P : state -> execution_ctx -> expr -> list expr -> out -> Prop),
       (red_expr S C (expr_basic (expr_call a1 a2)) oo ->
        forall (S0 : state) (C0 : execution_ctx) (exte : ext_expr) (o : out),
        @eq (option out) (out_of_ext_expr (expr_basic (expr_call a1 a2)))
          (@Some out oo) ->
        abort oo ->
        not (abort_intercepted_expr (expr_basic (expr_call a1 a2))) ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq ext_expr exte (expr_basic (expr_call a1 a2)) ->
        @eq out o oo -> P S C a1 a2 oo) ->
       (red_expr S C (expr_basic (expr_call a1 a2)) oo ->
        forall (S0 : state) (C0 : execution_ctx) (e1 : expr)
          (e2s : list expr) (o1 o2 : out),
        red_expr S C (expr_basic a1) o1 ->
        red_expr S C (expr_call_1 o1 (is_syntactic_eval a1) a2) oo ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq expr e1 a1 ->
        @eq (list expr) e2s a2 -> @eq out o2 oo -> P S C a1 a2 oo) ->
       red_expr S C (expr_basic (expr_call a1 a2)) oo -> P S C a1 a2 oo.

Parameter inv_red_expr_unary_op
     : forall (S : state) (C : execution_ctx) (a1 : unary_op) 
         (a2 : expr) (oo : out)
         (P : state -> execution_ctx -> unary_op -> expr -> out -> Prop),
       (red_expr S C (expr_basic (expr_unary_op a1 a2)) oo ->
        forall (S0 : state) (C0 : execution_ctx) (exte : ext_expr) (o : out),
        @eq (option out) (out_of_ext_expr (expr_basic (expr_unary_op a1 a2)))
          (@Some out oo) ->
        abort oo ->
        not (abort_intercepted_expr (expr_basic (expr_unary_op a1 a2))) ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq ext_expr exte (expr_basic (expr_unary_op a1 a2)) ->
        @eq out o oo -> P S C a1 a2 oo) ->
       (red_expr S C (expr_basic (expr_unary_op a1 a2)) oo ->
        forall (S0 : state) (C0 : execution_ctx) (op : unary_op) 
          (e : expr) (o1 o : out),
        prepost_unary_op a1 ->
        red_expr S C (expr_basic a2) o1 ->
        red_expr S C (expr_prepost_1 a1 o1) oo ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq unary_op op a1 -> @eq expr e a2 -> @eq out o oo -> P S C a1 a2 oo) ->
       (red_expr S C (expr_basic (expr_unary_op a1 a2)) oo ->
        forall (S0 : state) (C0 : execution_ctx) (op : unary_op) 
          (e : expr) (y1 : specret value) (o : out),
        regular_unary_op a1 ->
        @red_spec value S C (spec_expr_get_value a2) y1 ->
        red_expr S C (expr_unary_op_1 a1 y1) oo ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq unary_op op a1 -> @eq expr e a2 -> @eq out o oo -> P S C a1 a2 oo) ->
       (red_expr S C (expr_basic (expr_unary_op a1 a2)) oo ->
        forall (S0 : state) (C0 : execution_ctx) (e : expr) (o1 o : out),
        red_expr S C (expr_basic a2) o1 ->
        red_expr S C (expr_delete_1 o1) oo ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq unary_op unary_op_delete a1 ->
        @eq expr e a2 -> @eq out o oo -> P S C unary_op_delete a2 oo) ->
       (red_expr S C (expr_basic (expr_unary_op a1 a2)) oo ->
        forall (S0 : state) (C0 : execution_ctx) (e : expr) (o1 o : out),
        red_expr S C (expr_basic a2) o1 ->
        red_expr S C (expr_typeof_1 o1) oo ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq unary_op unary_op_typeof a1 ->
        @eq expr e a2 -> @eq out o oo -> P S C unary_op_typeof a2 oo) ->
       red_expr S C (expr_basic (expr_unary_op a1 a2)) oo -> P S C a1 a2 oo.

Parameter inv_red_expr_binary_op
     : forall (S : state) (C : execution_ctx) (a1 : expr) 
         (a2 : binary_op) (a3 : expr) (oo : out)
         (P : state ->
              execution_ctx -> expr -> binary_op -> expr -> out -> Prop),
       (red_expr S C (expr_basic (expr_binary_op a1 a2 a3)) oo ->
        forall (S0 : state) (C0 : execution_ctx) (exte : ext_expr) (o : out),
        @eq (option out)
          (out_of_ext_expr (expr_basic (expr_binary_op a1 a2 a3)))
          (@Some out oo) ->
        abort oo ->
        not (abort_intercepted_expr (expr_basic (expr_binary_op a1 a2 a3))) ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq ext_expr exte (expr_basic (expr_binary_op a1 a2 a3)) ->
        @eq out o oo -> P S C a1 a2 a3 oo) ->
       (red_expr S C (expr_basic (expr_binary_op a1 a2 a3)) oo ->
        forall (S0 : state) (C0 : execution_ctx) (op : binary_op)
          (e1 e2 : expr) (y1 : specret value) (o : out),
        regular_binary_op a2 ->
        @red_spec value S C (spec_expr_get_value a1) y1 ->
        red_expr S C (expr_binary_op_1 a2 y1 a3) oo ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq expr e1 a1 ->
        @eq binary_op op a2 ->
        @eq expr e2 a3 -> @eq out o oo -> P S C a1 a2 a3 oo) ->
       (red_expr S C (expr_basic (expr_binary_op a1 a2 a3)) oo ->
        forall (S0 : state) (C0 : execution_ctx) (op : binary_op)
          (b_ret : bool) (e1 e2 : expr) (y1 : specret value) 
          (o : out),
        lazy_op a2 b_ret ->
        @red_spec value S C (spec_expr_get_value a1) y1 ->
        red_expr S C (expr_lazy_op_1 b_ret y1 a3) oo ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq expr e1 a1 ->
        @eq binary_op op a2 ->
        @eq expr e2 a3 -> @eq out o oo -> P S C a1 a2 a3 oo) ->
       red_expr S C (expr_basic (expr_binary_op a1 a2 a3)) oo ->
       P S C a1 a2 a3 oo.

Parameter inv_red_expr_conditional
     : forall (S : state) (C : execution_ctx) (a1 a2 a3 : expr) 
         (oo : out)
         (P : state -> execution_ctx -> expr -> expr -> expr -> out -> Prop),
       (red_expr S C (expr_basic (expr_conditional a1 a2 a3)) oo ->
        forall (S0 : state) (C0 : execution_ctx) (exte : ext_expr) (o : out),
        @eq (option out)
          (out_of_ext_expr (expr_basic (expr_conditional a1 a2 a3)))
          (@Some out oo) ->
        abort oo ->
        not (abort_intercepted_expr (expr_basic (expr_conditional a1 a2 a3))) ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq ext_expr exte (expr_basic (expr_conditional a1 a2 a3)) ->
        @eq out o oo -> P S C a1 a2 a3 oo) ->
       (red_expr S C (expr_basic (expr_conditional a1 a2 a3)) oo ->
        forall (S0 : state) (C0 : execution_ctx) (e1 e2 e3 : expr)
          (y1 : specret value) (o : out),
        @red_spec value S C (spec_expr_get_value_conv spec_to_boolean a1) y1 ->
        red_expr S C (expr_conditional_1 y1 a2 a3) oo ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq expr e1 a1 ->
        @eq expr e2 a2 -> @eq expr e3 a3 -> @eq out o oo -> P S C a1 a2 a3 oo) ->
       red_expr S C (expr_basic (expr_conditional a1 a2 a3)) oo ->
       P S C a1 a2 a3 oo.

Parameter inv_red_expr_assign
     : forall (S : state) (C : execution_ctx) (a1 : expr)
         (a2 : option binary_op) (a3 : expr) (oo : out)
         (P : state ->
              execution_ctx ->
              expr -> option binary_op -> expr -> out -> Prop),
       (red_expr S C (expr_basic (expr_assign a1 a2 a3)) oo ->
        forall (S0 : state) (C0 : execution_ctx) (exte : ext_expr) (o : out),
        @eq (option out)
          (out_of_ext_expr (expr_basic (expr_assign a1 a2 a3)))
          (@Some out oo) ->
        abort oo ->
        not (abort_intercepted_expr (expr_basic (expr_assign a1 a2 a3))) ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq ext_expr exte (expr_basic (expr_assign a1 a2 a3)) ->
        @eq out o oo -> P S C a1 a2 a3 oo) ->
       (red_expr S C (expr_basic (expr_assign a1 a2 a3)) oo ->
        forall (S0 : state) (C0 : execution_ctx) (opo : option binary_op)
          (e1 e2 : expr) (o o1 : out),
        red_expr S C (expr_basic a1) o1 ->
        red_expr S C (expr_assign_1 o1 a2 a3) oo ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq expr e1 a1 ->
        @eq (option binary_op) opo a2 ->
        @eq expr e2 a3 -> @eq out o oo -> P S C a1 a2 a3 oo) ->
       red_expr S C (expr_basic (expr_assign a1 a2 a3)) oo ->
       P S C a1 a2 a3 oo.

Parameter inv_red_expr_expr_identifier_1
     : forall (S : state) (C : execution_ctx) (a1 : specret ref) 
         (oo : out)
         (P : state -> execution_ctx -> specret ref -> out -> Prop),
       (red_expr S C (expr_identifier_1 a1) oo ->
        forall (S0 : state) (C0 : execution_ctx) (exte : ext_expr) (o : out),
        @eq (option out) (out_of_ext_expr (expr_identifier_1 a1))
          (@Some out oo) ->
        abort oo ->
        not (abort_intercepted_expr (expr_identifier_1 a1)) ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq ext_expr exte (expr_identifier_1 a1) ->
        @eq out o oo -> P S C a1 oo) ->
       (red_expr S C (expr_identifier_1 a1) oo ->
        forall (S0 S1 : state) (C0 : execution_ctx) (r : ref),
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq (specret ref) (@ret ref S1 r) a1 ->
        @eq out (out_ter S1 (res_ref r)) oo ->
        P S C (@ret ref S1 r) (out_ter S1 (res_ref r))) ->
       red_expr S C (expr_identifier_1 a1) oo -> P S C a1 oo.

Parameter inv_red_expr_expr_object_0
     : forall (S : state) (C : execution_ctx) (a1 : out) 
         (a2 : propdefs) (oo : out)
         (P : state ->
              execution_ctx ->
              out -> list (prod propname propbody) -> out -> Prop),
       (red_expr S C (expr_object_0 a1 a2) oo ->
        forall (S0 : state) (C0 : execution_ctx) (exte : ext_expr) (o : out),
        @eq (option out) (out_of_ext_expr (expr_object_0 a1 a2))
          (@Some out oo) ->
        abort oo ->
        not (abort_intercepted_expr (expr_object_0 a1 a2)) ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq ext_expr exte (expr_object_0 a1 a2) ->
        @eq out o oo -> P S C a1 a2 oo) ->
       (red_expr S C (expr_object_0 a1 a2) oo ->
        forall (S0 S1 : state) (C0 : execution_ctx) 
          (l : object_loc) (pds : propdefs) (o : out),
        red_expr S1 C (expr_object_1 l a2) oo ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq out (out_ter S1 (res_val (value_object l))) a1 ->
        @eq propdefs pds a2 ->
        @eq out o oo -> P S C (out_ter S1 (res_val (value_object l))) a2 oo) ->
       red_expr S C (expr_object_0 a1 a2) oo -> P S C a1 a2 oo.

Parameter inv_red_expr_expr_object_1
     : forall (S : state) (C : execution_ctx) (a1 : object_loc)
         (a2 : propdefs) (oo : out)
         (P : state ->
              execution_ctx ->
              object_loc -> list (prod propname propbody) -> out -> Prop),
       (red_expr S C (expr_object_1 a1 a2) oo ->
        forall (S0 : state) (C0 : execution_ctx) (exte : ext_expr) (o : out),
        @eq (option out) (out_of_ext_expr (expr_object_1 a1 a2))
          (@Some out oo) ->
        abort oo ->
        not (abort_intercepted_expr (expr_object_1 a1 a2)) ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq ext_expr exte (expr_object_1 a1 a2) ->
        @eq out o oo -> P S C a1 a2 oo) ->
       (red_expr S C (expr_object_1 a1 a2) oo ->
        forall (S0 : state) (C0 : execution_ctx) (l : object_loc),
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq object_loc l a1 ->
        @eq propdefs (@nil (prod propname propbody)) a2 ->
        @eq out (out_ter S (res_val (value_object a1))) oo ->
        P S C a1 (@nil (prod propname propbody))
          (out_ter S (res_val (value_object a1)))) ->
       (red_expr S C (expr_object_1 a1 a2) oo ->
        forall (S0 : state) (C0 : execution_ctx) (x : prop_name)
          (l : object_loc) (pn : propname) (pb : propbody) 
          (pds : propdefs) (o : out),
        @eq prop_name x (string_of_propname pn) ->
        red_expr S C (expr_object_2 a1 x pb pds) oo ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq object_loc l a1 ->
        @eq propdefs
          (@cons (prod propname propbody) (@pair propname propbody pn pb) pds)
          a2 ->
        @eq out o oo ->
        P S C a1
          (@cons (prod propname propbody) (@pair propname propbody pn pb) pds)
          oo) -> red_expr S C (expr_object_1 a1 a2) oo -> P S C a1 a2 oo.

Parameter inv_red_expr_expr_object_2
     : forall (S : state) (C : execution_ctx) (a1 : object_loc) 
         (a2 : string) (a3 : propbody) (a4 : propdefs) 
         (oo : out)
         (P : state ->
              execution_ctx ->
              object_loc ->
              string ->
              propbody -> list (prod propname propbody) -> out -> Prop),
       (red_expr S C (expr_object_2 a1 a2 a3 a4) oo ->
        forall (S0 : state) (C0 : execution_ctx) (exte : ext_expr) (o : out),
        @eq (option out) (out_of_ext_expr (expr_object_2 a1 a2 a3 a4))
          (@Some out oo) ->
        abort oo ->
        not (abort_intercepted_expr (expr_object_2 a1 a2 a3 a4)) ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq ext_expr exte (expr_object_2 a1 a2 a3 a4) ->
        @eq out o oo -> P S C a1 a2 a3 a4 oo) ->
       (red_expr S C (expr_object_2 a1 a2 a3 a4) oo ->
        forall (S0 : state) (C0 : execution_ctx) (e : expr) 
          (l : object_loc) (x : prop_name) (pds : propdefs)
          (y1 : specret value) (o : out),
        @red_spec value S C (spec_expr_get_value e) y1 ->
        red_expr S C (expr_object_3_val a1 a2 y1 a4) oo ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq object_loc l a1 ->
        @eq string x a2 ->
        @eq propbody (propbody_val e) a3 ->
        @eq propdefs pds a4 ->
        @eq out o oo -> P S C a1 a2 (propbody_val e) a4 oo) ->
       (red_expr S C (expr_object_2 a1 a2 a3 a4) oo ->
        forall (S0 : state) (C0 : execution_ctx) (bd : funcbody)
          (l : object_loc) (x : prop_name) (o o1 : out) 
          (pds : propdefs),
        red_expr S C (spec_create_new_function_in C (@nil string) bd) o1 ->
        red_expr S C (expr_object_3_get a1 a2 o1 a4) oo ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq object_loc l a1 ->
        @eq string x a2 ->
        @eq propbody (propbody_get bd) a3 ->
        @eq propdefs pds a4 ->
        @eq out o oo -> P S C a1 a2 (propbody_get bd) a4 oo) ->
       (red_expr S C (expr_object_2 a1 a2 a3 a4) oo ->
        forall (S0 : state) (C0 : execution_ctx) (l : object_loc)
          (x : prop_name) (pds : propdefs) (o o1 : out) 
          (bd : funcbody) (args : list string),
        red_expr S C (spec_create_new_function_in C args bd) o1 ->
        red_expr S C (expr_object_3_set a1 a2 o1 a4) oo ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq object_loc l a1 ->
        @eq string x a2 ->
        @eq propbody (propbody_set args bd) a3 ->
        @eq propdefs pds a4 ->
        @eq out o oo -> P S C a1 a2 (propbody_set args bd) a4 oo) ->
       red_expr S C (expr_object_2 a1 a2 a3 a4) oo -> P S C a1 a2 a3 a4 oo.

Parameter inv_red_expr_expr_object_3_val
     : forall (S : state) (C : execution_ctx) (a1 : object_loc) 
         (a2 : string) (a3 : specret value) (a4 : propdefs) 
         (oo : out)
         (P : state ->
              execution_ctx ->
              object_loc ->
              string ->
              specret value -> list (prod propname propbody) -> out -> Prop),
       (red_expr S C (expr_object_3_val a1 a2 a3 a4) oo ->
        forall (S0 : state) (C0 : execution_ctx) (exte : ext_expr) (o : out),
        @eq (option out) (out_of_ext_expr (expr_object_3_val a1 a2 a3 a4))
          (@Some out oo) ->
        abort oo ->
        not (abort_intercepted_expr (expr_object_3_val a1 a2 a3 a4)) ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq ext_expr exte (expr_object_3_val a1 a2 a3 a4) ->
        @eq out o oo -> P S C a1 a2 a3 a4 oo) ->
       (red_expr S C (expr_object_3_val a1 a2 a3 a4) oo ->
        forall (S0 S1 : state) (C0 : execution_ctx) 
          (l : object_loc) (x : prop_name) (A : attributes) 
          (v : value) (o : out) (pds : propdefs),
        @eq attributes A
          (attributes_data_of (attributes_data_intro v true true true)) ->
        red_expr S0 C (expr_object_4 a1 a2 (descriptor_of_attributes A) a4)
          oo ->
        @eq state S1 S ->
        @eq execution_ctx C0 C ->
        @eq object_loc l a1 ->
        @eq string x a2 ->
        @eq (specret value) (@ret value S0 v) a3 ->
        @eq propdefs pds a4 ->
        @eq out o oo -> P S C a1 a2 (@ret value S0 v) a4 oo) ->
       red_expr S C (expr_object_3_val a1 a2 a3 a4) oo ->
       P S C a1 a2 a3 a4 oo.

Parameter inv_red_expr_expr_object_3_get
     : forall (S : state) (C : execution_ctx) (a1 : object_loc) 
         (a2 : string) (a3 : out) (a4 : propdefs) (oo : out)
         (P : state ->
              execution_ctx ->
              object_loc ->
              string -> out -> list (prod propname propbody) -> out -> Prop),
       (red_expr S C (expr_object_3_get a1 a2 a3 a4) oo ->
        forall (S0 : state) (C0 : execution_ctx) (exte : ext_expr) (o : out),
        @eq (option out) (out_of_ext_expr (expr_object_3_get a1 a2 a3 a4))
          (@Some out oo) ->
        abort oo ->
        not (abort_intercepted_expr (expr_object_3_get a1 a2 a3 a4)) ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq ext_expr exte (expr_object_3_get a1 a2 a3 a4) ->
        @eq out o oo -> P S C a1 a2 a3 a4 oo) ->
       (red_expr S C (expr_object_3_get a1 a2 a3 a4) oo ->
        forall (S0 S1 : state) (C0 : execution_ctx) 
          (Desc : descriptor) (l : object_loc) (x : prop_name) 
          (v : value) (pds : propdefs) (o : out),
        @eq descriptor Desc
          (descriptor_intro (@None value) (@None bool) 
             (@Some value v) (@None value) (@Some bool true)
             (@Some bool true)) ->
        red_expr S0 C (expr_object_4 a1 a2 Desc a4) oo ->
        @eq state S1 S ->
        @eq execution_ctx C0 C ->
        @eq object_loc l a1 ->
        @eq string x a2 ->
        @eq out (out_ter S0 (res_val v)) a3 ->
        @eq propdefs pds a4 ->
        @eq out o oo -> P S C a1 a2 (out_ter S0 (res_val v)) a4 oo) ->
       red_expr S C (expr_object_3_get a1 a2 a3 a4) oo ->
       P S C a1 a2 a3 a4 oo.

Parameter inv_red_expr_expr_object_3_set
     : forall (S : state) (C : execution_ctx) (a1 : object_loc) 
         (a2 : string) (a3 : out) (a4 : propdefs) (oo : out)
         (P : state ->
              execution_ctx ->
              object_loc ->
              string -> out -> list (prod propname propbody) -> out -> Prop),
       (red_expr S C (expr_object_3_set a1 a2 a3 a4) oo ->
        forall (S0 : state) (C0 : execution_ctx) (exte : ext_expr) (o : out),
        @eq (option out) (out_of_ext_expr (expr_object_3_set a1 a2 a3 a4))
          (@Some out oo) ->
        abort oo ->
        not (abort_intercepted_expr (expr_object_3_set a1 a2 a3 a4)) ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq ext_expr exte (expr_object_3_set a1 a2 a3 a4) ->
        @eq out o oo -> P S C a1 a2 a3 a4 oo) ->
       (red_expr S C (expr_object_3_set a1 a2 a3 a4) oo ->
        forall (S0 S1 : state) (C0 : execution_ctx) 
          (Desc : descriptor) (l : object_loc) (x : prop_name) 
          (v : value) (pds : propdefs) (o : out),
        @eq descriptor Desc
          (descriptor_intro (@None value) (@None bool) 
             (@None value) (@Some value v) (@Some bool true)
             (@Some bool true)) ->
        red_expr S0 C (expr_object_4 a1 a2 Desc a4) oo ->
        @eq state S1 S ->
        @eq execution_ctx C0 C ->
        @eq object_loc l a1 ->
        @eq string x a2 ->
        @eq out (out_ter S0 (res_val v)) a3 ->
        @eq propdefs pds a4 ->
        @eq out o oo -> P S C a1 a2 (out_ter S0 (res_val v)) a4 oo) ->
       red_expr S C (expr_object_3_set a1 a2 a3 a4) oo ->
       P S C a1 a2 a3 a4 oo.

Parameter inv_red_expr_expr_object_4
     : forall (S : state) (C : execution_ctx) (a1 : object_loc) 
         (a2 : string) (a3 : descriptor) (a4 : propdefs) 
         (oo : out)
         (P : state ->
              execution_ctx ->
              object_loc ->
              string ->
              descriptor -> list (prod propname propbody) -> out -> Prop),
       (red_expr S C (expr_object_4 a1 a2 a3 a4) oo ->
        forall (S0 : state) (C0 : execution_ctx) (exte : ext_expr) (o : out),
        @eq (option out) (out_of_ext_expr (expr_object_4 a1 a2 a3 a4))
          (@Some out oo) ->
        abort oo ->
        not (abort_intercepted_expr (expr_object_4 a1 a2 a3 a4)) ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq ext_expr exte (expr_object_4 a1 a2 a3 a4) ->
        @eq out o oo -> P S C a1 a2 a3 a4 oo) ->
       (red_expr S C (expr_object_4 a1 a2 a3 a4) oo ->
        forall (S0 : state) (C0 : execution_ctx) (Desc : descriptor)
          (l : object_loc) (x : prop_name) (pds : propdefs) 
          (o o1 : out),
        red_expr S C (spec_object_define_own_prop a1 a2 a3 false) o1 ->
        red_expr S C (expr_object_5 a1 a4 o1) oo ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq object_loc l a1 ->
        @eq string x a2 ->
        @eq descriptor Desc a3 ->
        @eq propdefs pds a4 -> @eq out o oo -> P S C a1 a2 a3 a4 oo) ->
       red_expr S C (expr_object_4 a1 a2 a3 a4) oo -> P S C a1 a2 a3 a4 oo.

Parameter inv_red_expr_expr_object_5
     : forall (S : state) (C : execution_ctx) (a1 : object_loc)
         (a2 : propdefs) (a3 oo : out)
         (P : state ->
              execution_ctx ->
              object_loc ->
              list (prod propname propbody) -> out -> out -> Prop),
       (red_expr S C (expr_object_5 a1 a2 a3) oo ->
        forall (S0 : state) (C0 : execution_ctx) (exte : ext_expr) (o : out),
        @eq (option out) (out_of_ext_expr (expr_object_5 a1 a2 a3))
          (@Some out oo) ->
        abort oo ->
        not (abort_intercepted_expr (expr_object_5 a1 a2 a3)) ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq ext_expr exte (expr_object_5 a1 a2 a3) ->
        @eq out o oo -> P S C a1 a2 a3 oo) ->
       (red_expr S C (expr_object_5 a1 a2 a3) oo ->
        forall (S0 S1 : state) (C0 : execution_ctx) 
          (rv : resvalue) (l : object_loc) (pds : propdefs) 
          (o : out),
        red_expr S0 C (expr_object_1 a1 a2) oo ->
        @eq state S1 S ->
        @eq execution_ctx C0 C ->
        @eq object_loc l a1 ->
        @eq propdefs pds a2 ->
        @eq out (out_ter S0 (res_normal rv)) a3 ->
        @eq out o oo -> P S C a1 a2 (out_ter S0 (res_normal rv)) oo) ->
       red_expr S C (expr_object_5 a1 a2 a3) oo -> P S C a1 a2 a3 oo.

Parameter inv_red_expr_expr_array_0
     : forall (S : state) (C : execution_ctx) (a1 : out)
         (a2 : list (option expr)) (oo : out)
         (P : state ->
              execution_ctx -> out -> list (option expr) -> out -> Prop),
       (red_expr S C (expr_array_0 a1 a2) oo ->
        forall (S0 : state) (C0 : execution_ctx) (exte : ext_expr) (o : out),
        @eq (option out) (out_of_ext_expr (expr_array_0 a1 a2))
          (@Some out oo) ->
        abort oo ->
        not (abort_intercepted_expr (expr_array_0 a1 a2)) ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq ext_expr exte (expr_array_0 a1 a2) ->
        @eq out o oo -> P S C a1 a2 oo) ->
       (red_expr S C (expr_array_0 a1 a2) oo ->
        forall (S' S0 : state) (C0 : execution_ctx) 
          (l : object_loc) (oes : list (option expr)) 
          (o : out),
        red_expr S0 C (expr_array_1 l a2) oo ->
        @eq state S' S ->
        @eq execution_ctx C0 C ->
        @eq out (out_ter S0 (res_val (value_object l))) a1 ->
        @eq (list (option expr)) oes a2 ->
        @eq out o oo -> P S C (out_ter S0 (res_val (value_object l))) a2 oo) ->
       red_expr S C (expr_array_0 a1 a2) oo -> P S C a1 a2 oo.

Parameter inv_red_expr_expr_array_1
     : forall (S : state) (C : execution_ctx) (a1 : object_loc)
         (a2 : list (option expr)) (oo : out)
         (P : state ->
              execution_ctx ->
              object_loc -> list (option expr) -> out -> Prop),
       (red_expr S C (expr_array_1 a1 a2) oo ->
        forall (S0 : state) (C0 : execution_ctx) (exte : ext_expr) (o : out),
        @eq (option out) (out_of_ext_expr (expr_array_1 a1 a2))
          (@Some out oo) ->
        abort oo ->
        not (abort_intercepted_expr (expr_array_1 a1 a2)) ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq ext_expr exte (expr_array_1 a1 a2) ->
        @eq out o oo -> P S C a1 a2 oo) ->
       (red_expr S C (expr_array_1 a1 a2) oo ->
        forall (S0 : state) (C0 : execution_ctx) (l : object_loc)
          (oes : list (option expr)) (o : out)
          (ElementList Elision : list (option expr)) 
          (ElisionLength : nat),
        @eq (list (option expr)) a2
          (@append (option expr) ElementList Elision) ->
        Logic.or (@eq (list (option expr)) ElementList (@nil (option expr)))
          (@ex expr
             (fun e : expr =>
              @ex (list (option expr))
                (fun oes' : list (option expr) =>
                 @eq (list (option expr)) ElementList
                   (@append (option expr) oes'
                      (@cons (option expr) (@Some expr e)
                         (@nil (option expr))))))) ->
        @Forall (option expr)
          (fun y : option expr => @eq (option expr) y (@None expr)) Elision ->
        @eq nat ElisionLength (@length (option expr) Elision) ->
        red_expr S C
          (expr_array_2 a1 ElementList (my_Z_of_nat ElisionLength)) oo ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq object_loc l a1 ->
        @eq (list (option expr)) oes a2 -> @eq out o oo -> P S C a1 a2 oo) ->
       red_expr S C (expr_array_1 a1 a2) oo -> P S C a1 a2 oo.

Parameter inv_red_expr_expr_array_2
     : forall (S : state) (C : execution_ctx) (a1 : object_loc)
         (a2 : list (option expr)) (a3 : Z) (oo : out)
         (P : state ->
              execution_ctx ->
              object_loc -> list (option expr) -> Z -> out -> Prop),
       (red_expr S C (expr_array_2 a1 a2 a3) oo ->
        forall (S0 : state) (C0 : execution_ctx) (exte : ext_expr) (o : out),
        @eq (option out) (out_of_ext_expr (expr_array_2 a1 a2 a3))
          (@Some out oo) ->
        abort oo ->
        not (abort_intercepted_expr (expr_array_2 a1 a2 a3)) ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq ext_expr exte (expr_array_2 a1 a2 a3) ->
        @eq out o oo -> P S C a1 a2 a3 oo) ->
       (red_expr S C (expr_array_2 a1 a2 a3) oo ->
        forall (S0 : state) (C0 : execution_ctx) (l : object_loc)
          (elst : list (option expr)) (elgth : Z) (o1 o : out),
        red_expr S C (expr_array_3 a1 a2 Z0) o1 ->
        red_expr S C (expr_array_add_length a1 a3 o1) oo ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq object_loc l a1 ->
        @eq (list (option expr)) elst a2 ->
        @eq Z elgth a3 -> @eq out o oo -> P S C a1 a2 a3 oo) ->
       red_expr S C (expr_array_2 a1 a2 a3) oo -> P S C a1 a2 a3 oo.

Parameter inv_red_expr_expr_array_3
     : forall (S : state) (C : execution_ctx) (a1 : object_loc)
         (a2 : list (option expr)) (a3 : Z) (oo : out)
         (P : state ->
              execution_ctx ->
              object_loc -> list (option expr) -> Z -> out -> Prop),
       (red_expr S C (expr_array_3 a1 a2 a3) oo ->
        forall (S0 : state) (C0 : execution_ctx) (exte : ext_expr) (o : out),
        @eq (option out) (out_of_ext_expr (expr_array_3 a1 a2 a3))
          (@Some out oo) ->
        abort oo ->
        not (abort_intercepted_expr (expr_array_3 a1 a2 a3)) ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq ext_expr exte (expr_array_3 a1 a2 a3) ->
        @eq out o oo -> P S C a1 a2 a3 oo) ->
       (red_expr S C (expr_array_3 a1 a2 a3) oo ->
        forall (S0 : state) (C0 : execution_ctx) (l : object_loc)
          (firstIndex : Z),
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq object_loc l a1 ->
        @eq (list (option expr)) (@nil (option expr)) a2 ->
        @eq Z firstIndex a3 ->
        @eq out (out_ter S (res_val (value_object a1))) oo ->
        P S C a1 (@nil (option expr)) a3
          (out_ter S (res_val (value_object a1)))) ->
       (red_expr S C (expr_array_3 a1 a2 a3) oo ->
        forall (S0 : state) (C0 : execution_ctx) (l : object_loc)
          (oes : list (option expr)) (o : out)
          (Elision ElementList : list (option expr)) 
          (ElisionLength : nat) (firstIndex : Z),
        @eq (list (option expr)) (@cons (option expr) (@None expr) oes)
          (@append (option expr) Elision ElementList) ->
        Logic.or (@eq (list (option expr)) ElementList (@nil (option expr)))
          (@ex expr
             (fun e : expr =>
              @ex (list (option expr))
                (fun oes' : list (option expr) =>
                 @eq (list (option expr)) ElementList
                   (@cons (option expr) (@Some expr e) oes')))) ->
        @Forall (option expr)
          (fun y : option expr => @eq (option expr) y (@None expr)) Elision ->
        @eq nat ElisionLength (@length (option expr) Elision) ->
        red_expr S C
          (expr_array_3 a1 ElementList (my_Z_of_nat ElisionLength)) oo ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq object_loc l a1 ->
        @eq (list (option expr)) (@cons (option expr) (@None expr) oes) a2 ->
        @eq Z firstIndex a3 ->
        @eq out o oo -> P S C a1 (@cons (option expr) (@None expr) oes) a3 oo) ->
       (red_expr S C (expr_array_3 a1 a2 a3) oo ->
        forall (S0 : state) (C0 : execution_ctx) (l : object_loc)
          (y : specret value) (o : out) (oes : list (option expr)) 
          (e : expr) (firstIndex : Z),
        @red_spec value S C (spec_expr_get_value e) y ->
        red_expr S C (expr_array_3_1 a1 y oes a3) oo ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq object_loc l a1 ->
        @eq (list (option expr)) (@cons (option expr) (@Some expr e) oes) a2 ->
        @eq Z firstIndex a3 ->
        @eq out o oo ->
        P S C a1 (@cons (option expr) (@Some expr e) oes) a3 oo) ->
       red_expr S C (expr_array_3 a1 a2 a3) oo -> P S C a1 a2 a3 oo.

Parameter inv_red_expr_expr_array_3_1
     : forall (S : state) (C : execution_ctx) (a1 : object_loc)
         (a2 : specret value) (a3 : list (option expr)) 
         (a4 : Z) (oo : out)
         (P : state ->
              execution_ctx ->
              object_loc ->
              specret value -> list (option expr) -> Z -> out -> Prop),
       (red_expr S C (expr_array_3_1 a1 a2 a3 a4) oo ->
        forall (S0 : state) (C0 : execution_ctx) (exte : ext_expr) (o : out),
        @eq (option out) (out_of_ext_expr (expr_array_3_1 a1 a2 a3 a4))
          (@Some out oo) ->
        abort oo ->
        not (abort_intercepted_expr (expr_array_3_1 a1 a2 a3 a4)) ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq ext_expr exte (expr_array_3_1 a1 a2 a3 a4) ->
        @eq out o oo -> P S C a1 a2 a3 a4 oo) ->
       (red_expr S C (expr_array_3_1 a1 a2 a3 a4) oo ->
        forall (S0 S' : state) (C0 : execution_ctx) 
          (l : object_loc) (v : value) (o1 o : out)
          (oes : list (option expr)) (firstIndex : Z),
        red_expr S' C
          (spec_object_get a1
             (String (Ascii false false true true false true true false)
                (String (Ascii true false true false false true true false)
                   (String (Ascii false true true true false true true false)
                      (String
                         (Ascii true true true false false true true false)
                         (String
                            (Ascii false false true false true true true
                               false)
                            (String
                               (Ascii false false false true false true true
                                  false) EmptyString))))))) o1 ->
        red_expr S' C (expr_array_3_2 a1 v o1 a3 a4) oo ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq object_loc l a1 ->
        @eq (specret value) (@ret value S' v) a2 ->
        @eq (list (option expr)) oes a3 ->
        @eq Z firstIndex a4 ->
        @eq out o oo -> P S C a1 (@ret value S' v) a3 a4 oo) ->
       red_expr S C (expr_array_3_1 a1 a2 a3 a4) oo -> P S C a1 a2 a3 a4 oo.

Parameter inv_red_expr_expr_array_3_2
     : forall (S : state) (C : execution_ctx) (a1 : object_loc) 
         (a2 : value) (a3 : out) (a4 : list (option expr)) 
         (a5 : Z) (oo : out)
         (P : state ->
              execution_ctx ->
              object_loc ->
              value -> out -> list (option expr) -> Z -> out -> Prop),
       (red_expr S C (expr_array_3_2 a1 a2 a3 a4 a5) oo ->
        forall (S0 : state) (C0 : execution_ctx) (exte : ext_expr) (o : out),
        @eq (option out) (out_of_ext_expr (expr_array_3_2 a1 a2 a3 a4 a5))
          (@Some out oo) ->
        abort oo ->
        not (abort_intercepted_expr (expr_array_3_2 a1 a2 a3 a4 a5)) ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq ext_expr exte (expr_array_3_2 a1 a2 a3 a4 a5) ->
        @eq out o oo -> P S C a1 a2 a3 a4 a5 oo) ->
       (red_expr S C (expr_array_3_2 a1 a2 a3 a4 a5) oo ->
        forall (S' S0 : state) (C0 : execution_ctx) 
          (l : object_loc) (vlen v : value) (y : specret Z)
          (oes : list (option expr)) (firstIndex : Z) 
          (o : out),
        @red_spec Z S' C (spec_to_uint32 vlen) y ->
        red_expr S' C (expr_array_3_3 a1 a2 y a4 a5) oo ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq object_loc l a1 ->
        @eq value v a2 ->
        @eq out (out_ter S' (res_val vlen)) a3 ->
        @eq (list (option expr)) oes a4 ->
        @eq Z firstIndex a5 ->
        @eq out o oo -> P S C a1 a2 (out_ter S' (res_val vlen)) a4 a5 oo) ->
       red_expr S C (expr_array_3_2 a1 a2 a3 a4 a5) oo ->
       P S C a1 a2 a3 a4 a5 oo.

Parameter inv_red_expr_expr_array_3_3
     : forall (S : state) (C : execution_ctx) (a1 : object_loc) 
         (a2 : value) (a3 : specret Z) (a4 : list (option expr)) 
         (a5 : Z) (oo : out)
         (P : state ->
              execution_ctx ->
              object_loc ->
              value -> specret Z -> list (option expr) -> Z -> out -> Prop),
       (red_expr S C (expr_array_3_3 a1 a2 a3 a4 a5) oo ->
        forall (S0 : state) (C0 : execution_ctx) (exte : ext_expr) (o : out),
        @eq (option out) (out_of_ext_expr (expr_array_3_3 a1 a2 a3 a4 a5))
          (@Some out oo) ->
        abort oo ->
        not (abort_intercepted_expr (expr_array_3_3 a1 a2 a3 a4 a5)) ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq ext_expr exte (expr_array_3_3 a1 a2 a3 a4 a5) ->
        @eq out o oo -> P S C a1 a2 a3 a4 a5 oo) ->
       (red_expr S C (expr_array_3_3 a1 a2 a3 a4 a5) oo ->
        forall (S' S0 : state) (C0 : execution_ctx) 
          (l : object_loc) (v : value) (lenuint32 : Z)
          (oes : list (option expr)) (firstIndex : Z) 
          (o1 o : out),
        red_expr S' C
          (spec_to_string
             (value_prim (prim_number (JsNumber.of_int (Z.add lenuint32 a5)))))
          o1 ->
        red_expr S' C (expr_array_3_4 a1 a2 o1 a4) oo ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq object_loc l a1 ->
        @eq value v a2 ->
        @eq (specret Z) (@ret Z S' lenuint32) a3 ->
        @eq (list (option expr)) oes a4 ->
        @eq Z firstIndex a5 ->
        @eq out o oo -> P S C a1 a2 (@ret Z S' lenuint32) a4 a5 oo) ->
       red_expr S C (expr_array_3_3 a1 a2 a3 a4 a5) oo ->
       P S C a1 a2 a3 a4 a5 oo.

Parameter inv_red_expr_expr_array_3_4
     : forall (S : state) (C : execution_ctx) (a1 : object_loc) 
         (a2 : value) (a3 : out) (a4 : list (option expr)) 
         (oo : out)
         (P : state ->
              execution_ctx ->
              object_loc -> value -> out -> list (option expr) -> out -> Prop),
       (red_expr S C (expr_array_3_4 a1 a2 a3 a4) oo ->
        forall (S0 : state) (C0 : execution_ctx) (exte : ext_expr) (o : out),
        @eq (option out) (out_of_ext_expr (expr_array_3_4 a1 a2 a3 a4))
          (@Some out oo) ->
        abort oo ->
        not (abort_intercepted_expr (expr_array_3_4 a1 a2 a3 a4)) ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq ext_expr exte (expr_array_3_4 a1 a2 a3 a4) ->
        @eq out o oo -> P S C a1 a2 a3 a4 oo) ->
       (red_expr S C (expr_array_3_4 a1 a2 a3 a4) oo ->
        forall (S0 S' : state) (C0 : execution_ctx) 
          (l : object_loc) (v : value) (s : string)
          (oes : list (option expr)) (o1 o : out) (Desc : descriptor),
        @eq descriptor Desc (descriptor_intro_data a2 true true true) ->
        red_expr S' C (spec_object_define_own_prop a1 s Desc false) o1 ->
        red_expr S' C (expr_array_3_5 a1 o1 a4) oo ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq object_loc l a1 ->
        @eq value v a2 ->
        @eq out (out_ter S' (res_val (value_prim (prim_string s)))) a3 ->
        @eq (list (option expr)) oes a4 ->
        @eq out o oo ->
        P S C a1 a2 (out_ter S' (res_val (value_prim (prim_string s)))) a4 oo) ->
       red_expr S C (expr_array_3_4 a1 a2 a3 a4) oo -> P S C a1 a2 a3 a4 oo.

Parameter inv_red_expr_expr_array_3_5
     : forall (S : state) (C : execution_ctx) (a1 : object_loc) 
         (a2 : out) (a3 : list (option expr)) (oo : out)
         (P : state ->
              execution_ctx ->
              object_loc -> out -> list (option expr) -> out -> Prop),
       (red_expr S C (expr_array_3_5 a1 a2 a3) oo ->
        forall (S0 : state) (C0 : execution_ctx) (exte : ext_expr) (o : out),
        @eq (option out) (out_of_ext_expr (expr_array_3_5 a1 a2 a3))
          (@Some out oo) ->
        abort oo ->
        not (abort_intercepted_expr (expr_array_3_5 a1 a2 a3)) ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq ext_expr exte (expr_array_3_5 a1 a2 a3) ->
        @eq out o oo -> P S C a1 a2 a3 oo) ->
       (red_expr S C (expr_array_3_5 a1 a2 a3) oo ->
        forall (S0 S' : state) (C0 : execution_ctx) 
          (l : object_loc) (oes : list (option expr)) 
          (o : out) (b : bool),
        out ->
        red_expr S' C (expr_array_3 a1 a3 Z0) oo ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq object_loc l a1 ->
        @eq out (out_ter S' (res_val (value_prim (prim_bool b)))) a2 ->
        @eq (list (option expr)) oes a3 ->
        @eq out o oo ->
        P S C a1 (out_ter S' (res_val (value_prim (prim_bool b)))) a3 oo) ->
       red_expr S C (expr_array_3_5 a1 a2 a3) oo -> P S C a1 a2 a3 oo.

Parameter inv_red_expr_expr_array_add_length
     : forall (S : state) (C : execution_ctx) (a1 : object_loc) 
         (a2 : Z) (a3 oo : out)
         (P : state -> execution_ctx -> object_loc -> Z -> out -> out -> Prop),
       (red_expr S C (expr_array_add_length a1 a2 a3) oo ->
        forall (S0 : state) (C0 : execution_ctx) (exte : ext_expr) (o : out),
        @eq (option out) (out_of_ext_expr (expr_array_add_length a1 a2 a3))
          (@Some out oo) ->
        abort oo ->
        not (abort_intercepted_expr (expr_array_add_length a1 a2 a3)) ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq ext_expr exte (expr_array_add_length a1 a2 a3) ->
        @eq out o oo -> P S C a1 a2 a3 oo) ->
       (red_expr S C (expr_array_add_length a1 a2 a3) oo ->
        forall (S0 S' : state) (C0 : execution_ctx) 
          (l : object_loc) (o : out) (elgth : Z),
        red_expr S0 C (expr_array_add_length_0 a1 a2) oo ->
        @eq state S' S ->
        @eq execution_ctx C0 C ->
        @eq object_loc l a1 ->
        @eq Z elgth a2 ->
        @eq out (out_ter S0 (res_val (value_object a1))) a3 ->
        @eq out o oo ->
        P S C a1 a2 (out_ter S0 (res_val (value_object a1))) oo) ->
       red_expr S C (expr_array_add_length a1 a2 a3) oo -> P S C a1 a2 a3 oo.

Parameter inv_red_expr_expr_array_add_length_0
     : forall (S : state) (C : execution_ctx) (a1 : object_loc) 
         (a2 : Z) (oo : out)
         (P : state -> execution_ctx -> object_loc -> Z -> out -> Prop),
       (red_expr S C (expr_array_add_length_0 a1 a2) oo ->
        forall (S0 : state) (C0 : execution_ctx) (exte : ext_expr) (o : out),
        @eq (option out) (out_of_ext_expr (expr_array_add_length_0 a1 a2))
          (@Some out oo) ->
        abort oo ->
        not (abort_intercepted_expr (expr_array_add_length_0 a1 a2)) ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq ext_expr exte (expr_array_add_length_0 a1 a2) ->
        @eq out o oo -> P S C a1 a2 oo) ->
       (red_expr S C (expr_array_add_length_0 a1 a2) oo ->
        forall (S0 : state) (C0 : execution_ctx) (l : object_loc)
          (o1 o : out) (elgth : Z),
        red_expr S C
          (spec_object_get a1
             (String (Ascii false false true true false true true false)
                (String (Ascii true false true false false true true false)
                   (String (Ascii false true true true false true true false)
                      (String
                         (Ascii true true true false false true true false)
                         (String
                            (Ascii false false true false true true true
                               false)
                            (String
                               (Ascii false false false true false true true
                                  false) EmptyString))))))) o1 ->
        red_expr S C (expr_array_add_length_1 a1 a2 o1) oo ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq object_loc l a1 ->
        @eq Z elgth a2 -> @eq out o oo -> P S C a1 a2 oo) ->
       red_expr S C (expr_array_add_length_0 a1 a2) oo -> P S C a1 a2 oo.

Parameter inv_red_expr_expr_array_add_length_1
     : forall (S : state) (C : execution_ctx) (a1 : object_loc) 
         (a2 : Z) (a3 oo : out)
         (P : state -> execution_ctx -> object_loc -> Z -> out -> out -> Prop),
       (red_expr S C (expr_array_add_length_1 a1 a2 a3) oo ->
        forall (S0 : state) (C0 : execution_ctx) (exte : ext_expr) (o : out),
        @eq (option out) (out_of_ext_expr (expr_array_add_length_1 a1 a2 a3))
          (@Some out oo) ->
        abort oo ->
        not (abort_intercepted_expr (expr_array_add_length_1 a1 a2 a3)) ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq ext_expr exte (expr_array_add_length_1 a1 a2 a3) ->
        @eq out o oo -> P S C a1 a2 a3 oo) ->
       (red_expr S C (expr_array_add_length_1 a1 a2 a3) oo ->
        forall (S' S0 : state) (C0 : execution_ctx) 
          (l : object_loc) (vlen : value) (y : specret Z) 
          (o : out) (elgth : Z),
        @red_spec Z S0 C (spec_to_uint32 vlen) y ->
        red_expr S0 C (expr_array_add_length_2 a1 y a2) oo ->
        @eq state S' S ->
        @eq execution_ctx C0 C ->
        @eq object_loc l a1 ->
        @eq Z elgth a2 ->
        @eq out (out_ter S0 (res_val vlen)) a3 ->
        @eq out o oo -> P S C a1 a2 (out_ter S0 (res_val vlen)) oo) ->
       red_expr S C (expr_array_add_length_1 a1 a2 a3) oo ->
       P S C a1 a2 a3 oo.

Parameter inv_red_expr_expr_array_add_length_2
     : forall (S : state) (C : execution_ctx) (a1 : object_loc)
         (a2 : specret Z) (a3 : Z) (oo : out)
         (P : state ->
              execution_ctx -> object_loc -> specret Z -> Z -> out -> Prop),
       (red_expr S C (expr_array_add_length_2 a1 a2 a3) oo ->
        forall (S0 : state) (C0 : execution_ctx) (exte : ext_expr) (o : out),
        @eq (option out) (out_of_ext_expr (expr_array_add_length_2 a1 a2 a3))
          (@Some out oo) ->
        abort oo ->
        not (abort_intercepted_expr (expr_array_add_length_2 a1 a2 a3)) ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq ext_expr exte (expr_array_add_length_2 a1 a2 a3) ->
        @eq out o oo -> P S C a1 a2 a3 oo) ->
       (red_expr S C (expr_array_add_length_2 a1 a2 a3) oo ->
        forall (S' S0 : state) (C0 : execution_ctx) 
          (l : object_loc) (y : specret Z) (lenuint32 : Z) 
          (o : out) (elgth : Z),
        @red_spec Z S0 C
          (spec_to_uint32
             (value_prim (prim_number (JsNumber.of_int (Z.add lenuint32 a3)))))
          y ->
        red_expr S0 C (expr_array_add_length_3 a1 y) oo ->
        @eq state S' S ->
        @eq execution_ctx C0 C ->
        @eq object_loc l a1 ->
        @eq (specret Z) (@ret Z S0 lenuint32) a2 ->
        @eq Z elgth a3 ->
        @eq out o oo -> P S C a1 (@ret Z S0 lenuint32) a3 oo) ->
       red_expr S C (expr_array_add_length_2 a1 a2 a3) oo ->
       P S C a1 a2 a3 oo.

Parameter inv_red_expr_expr_array_add_length_3
     : forall (S : state) (C : execution_ctx) (a1 : object_loc)
         (a2 : specret Z) (oo : out)
         (P : state ->
              execution_ctx -> object_loc -> specret Z -> out -> Prop),
       (red_expr S C (expr_array_add_length_3 a1 a2) oo ->
        forall (S0 : state) (C0 : execution_ctx) (exte : ext_expr) (o : out),
        @eq (option out) (out_of_ext_expr (expr_array_add_length_3 a1 a2))
          (@Some out oo) ->
        abort oo ->
        not (abort_intercepted_expr (expr_array_add_length_3 a1 a2)) ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq ext_expr exte (expr_array_add_length_3 a1 a2) ->
        @eq out o oo -> P S C a1 a2 oo) ->
       (red_expr S C (expr_array_add_length_3 a1 a2) oo ->
        forall (S0 S' : state) (C0 : execution_ctx) 
          (l : object_loc) (vlen : Z) (o o1 : out),
        red_expr S0 C
          (spec_object_put a1
             (String (Ascii false false true true false true true false)
                (String (Ascii true false true false false true true false)
                   (String (Ascii false true true true false true true false)
                      (String
                         (Ascii true true true false false true true false)
                         (String
                            (Ascii false false true false true true true
                               false)
                            (String
                               (Ascii false false false true false true true
                                  false) EmptyString))))))
             (value_prim (prim_number (JsNumber.of_int vlen))) throw_false)
          o1 ->
        red_expr S0 C (expr_array_add_length_4 a1 o1) oo ->
        @eq state S' S ->
        @eq execution_ctx C0 C ->
        @eq object_loc l a1 ->
        @eq (specret Z) (@ret Z S0 vlen) a2 ->
        @eq out o oo -> P S C a1 (@ret Z S0 vlen) oo) ->
       red_expr S C (expr_array_add_length_3 a1 a2) oo -> P S C a1 a2 oo.

Parameter inv_red_expr_expr_array_add_length_4
     : forall (S : state) (C : execution_ctx) (a1 : object_loc) 
         (a2 oo : out)
         (P : state -> execution_ctx -> object_loc -> out -> out -> Prop),
       (red_expr S C (expr_array_add_length_4 a1 a2) oo ->
        forall (S0 : state) (C0 : execution_ctx) (exte : ext_expr) (o : out),
        @eq (option out) (out_of_ext_expr (expr_array_add_length_4 a1 a2))
          (@Some out oo) ->
        abort oo ->
        not (abort_intercepted_expr (expr_array_add_length_4 a1 a2)) ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq ext_expr exte (expr_array_add_length_4 a1 a2) ->
        @eq out o oo -> P S C a1 a2 oo) ->
       (red_expr S C (expr_array_add_length_4 a1 a2) oo ->
        forall (S' S0 : state) (C0 : execution_ctx) 
          (l : object_loc) (R : res),
        @eq state S' S ->
        @eq execution_ctx C0 C ->
        @eq object_loc l a1 ->
        @eq out (out_ter S0 R) a2 ->
        @eq out (out_ter S0 (res_val (value_object a1))) oo ->
        P S C a1 (out_ter S0 R) (out_ter S0 (res_val (value_object a1)))) ->
       red_expr S C (expr_array_add_length_4 a1 a2) oo -> P S C a1 a2 oo.

Parameter inv_red_expr_expr_function_1
     : forall (S : state) (C : execution_ctx) (a1 : string)
         (a2 : list string) (a3 : funcbody) (a4 : env_loc) 
         (a5 : lexical_env) (a6 oo : out)
         (P : state ->
              execution_ctx ->
              string ->
              list string ->
              funcbody -> nat -> list nat -> out -> out -> Prop),
       (red_expr S C (expr_function_1 a1 a2 a3 a4 a5 a6) oo ->
        forall (S0 : state) (C0 : execution_ctx) (exte : ext_expr) (o : out),
        @eq (option out)
          (out_of_ext_expr (expr_function_1 a1 a2 a3 a4 a5 a6))
          (@Some out oo) ->
        abort oo ->
        not (abort_intercepted_expr (expr_function_1 a1 a2 a3 a4 a5 a6)) ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq ext_expr exte (expr_function_1 a1 a2 a3 a4 a5 a6) ->
        @eq out o oo -> P S C a1 a2 a3 a4 a5 a6 oo) ->
       (red_expr S C (expr_function_1 a1 a2 a3 a4 a5 a6) oo ->
        forall (o1 : out) (S0 S1 : state) (C0 : execution_ctx) 
          (s : string) (args : list string) (bd : funcbody) 
          (L : env_loc) (scope : lexical_env) (o : out),
        red_expr S1 C
          (spec_creating_function_object a2 a3 a5 (funcbody_is_strict a3)) o1 ->
        red_expr S1 C (expr_function_2 a1 a4 o1) oo ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq string s a1 ->
        @eq (list string) args a2 ->
        @eq funcbody bd a3 ->
        @eq env_loc L a4 ->
        @eq lexical_env scope a5 ->
        @eq out (out_void S1) a6 ->
        @eq out o oo -> P S C a1 a2 a3 a4 a5 (out_void S1) oo) ->
       red_expr S C (expr_function_1 a1 a2 a3 a4 a5 a6) oo ->
       P S C a1 a2 a3 a4 a5 a6 oo.

Parameter inv_red_expr_expr_function_2
     : forall (S : state) (C : execution_ctx) (a1 : string) 
         (a2 : env_loc) (a3 oo : out)
         (P : state -> execution_ctx -> string -> nat -> out -> out -> Prop),
       (red_expr S C (expr_function_2 a1 a2 a3) oo ->
        forall (S0 : state) (C0 : execution_ctx) (exte : ext_expr) (o : out),
        @eq (option out) (out_of_ext_expr (expr_function_2 a1 a2 a3))
          (@Some out oo) ->
        abort oo ->
        not (abort_intercepted_expr (expr_function_2 a1 a2 a3)) ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq ext_expr exte (expr_function_2 a1 a2 a3) ->
        @eq out o oo -> P S C a1 a2 a3 oo) ->
       (red_expr S C (expr_function_2 a1 a2 a3) oo ->
        forall (o1 : out) (S0 S1 : state) (C0 : execution_ctx) 
          (s : string) (L : env_loc) (l : object_loc) 
          (o : out),
        red_expr S1 C
          (spec_env_record_initialize_immutable_binding a2 a1
             (value_object l)) o1 ->
        red_expr S1 C (expr_function_3 l o1) oo ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq string s a1 ->
        @eq env_loc L a2 ->
        @eq out (out_ter S1 (res_val (value_object l))) a3 ->
        @eq out o oo ->
        P S C a1 a2 (out_ter S1 (res_val (value_object l))) oo) ->
       red_expr S C (expr_function_2 a1 a2 a3) oo -> P S C a1 a2 a3 oo.

Parameter inv_red_expr_expr_function_3
     : forall (S : state) (C : execution_ctx) (a1 : object_loc) 
         (a2 oo : out)
         (P : state -> execution_ctx -> object_loc -> out -> out -> Prop),
       (red_expr S C (expr_function_3 a1 a2) oo ->
        forall (S0 : state) (C0 : execution_ctx) (exte : ext_expr) (o : out),
        @eq (option out) (out_of_ext_expr (expr_function_3 a1 a2))
          (@Some out oo) ->
        abort oo ->
        not (abort_intercepted_expr (expr_function_3 a1 a2)) ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq ext_expr exte (expr_function_3 a1 a2) ->
        @eq out o oo -> P S C a1 a2 oo) ->
       (red_expr S C (expr_function_3 a1 a2) oo ->
        forall (S0 S1 : state) (C0 : execution_ctx) (l : object_loc),
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq object_loc l a1 ->
        @eq out (out_void S1) a2 ->
        @eq out (out_ter S1 (res_val (value_object a1))) oo ->
        P S C a1 (out_void S1) (out_ter S1 (res_val (value_object a1)))) ->
       red_expr S C (expr_function_3 a1 a2) oo -> P S C a1 a2 oo.

Parameter inv_red_expr_expr_access_1
     : forall (S : state) (C : execution_ctx) (a1 : specret value)
         (a2 : expr) (oo : out)
         (P : state -> execution_ctx -> specret value -> expr -> out -> Prop),
       (red_expr S C (expr_access_1 a1 a2) oo ->
        forall (S0 : state) (C0 : execution_ctx) (exte : ext_expr) (o : out),
        @eq (option out) (out_of_ext_expr (expr_access_1 a1 a2))
          (@Some out oo) ->
        abort oo ->
        not (abort_intercepted_expr (expr_access_1 a1 a2)) ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq ext_expr exte (expr_access_1 a1 a2) ->
        @eq out o oo -> P S C a1 a2 oo) ->
       (red_expr S C (expr_access_1 a1 a2) oo ->
        forall (S0 S1 : state) (C0 : execution_ctx) 
          (v1 : value) (e2 : expr) (y1 : specret value) 
          (o : out),
        @red_spec value S1 C (spec_expr_get_value a2) y1 ->
        red_expr S1 C (expr_access_2 v1 y1) oo ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq (specret value) (@ret value S1 v1) a1 ->
        @eq expr e2 a2 -> @eq out o oo -> P S C (@ret value S1 v1) a2 oo) ->
       red_expr S C (expr_access_1 a1 a2) oo -> P S C a1 a2 oo.

Parameter inv_red_expr_expr_access_2
     : forall (S : state) (C : execution_ctx) (a1 : value)
         (a2 : specret value) (oo : out)
         (P : state -> execution_ctx -> value -> specret value -> out -> Prop),
       (red_expr S C (expr_access_2 a1 a2) oo ->
        forall (S0 : state) (C0 : execution_ctx) (exte : ext_expr) (o : out),
        @eq (option out) (out_of_ext_expr (expr_access_2 a1 a2))
          (@Some out oo) ->
        abort oo ->
        not (abort_intercepted_expr (expr_access_2 a1 a2)) ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq ext_expr exte (expr_access_2 a1 a2) ->
        @eq out o oo -> P S C a1 a2 oo) ->
       (red_expr S C (expr_access_2 a1 a2) oo ->
        forall (S0 S1 : state) (C0 : execution_ctx) 
          (v1 v2 : value) (o1 o : out),
        red_expr S1 C (spec_check_object_coercible a1) o1 ->
        red_expr S1 C (expr_access_3 a1 o1 v2) oo ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq value v1 a1 ->
        @eq (specret value) (@ret value S1 v2) a2 ->
        @eq out o oo -> P S C a1 (@ret value S1 v2) oo) ->
       red_expr S C (expr_access_2 a1 a2) oo -> P S C a1 a2 oo.

Parameter inv_red_expr_expr_access_3
     : forall (S : state) (C : execution_ctx) (a1 : value) 
         (a2 : out) (a3 : value) (oo : out)
         (P : state -> execution_ctx -> value -> out -> value -> out -> Prop),
       (red_expr S C (expr_access_3 a1 a2 a3) oo ->
        forall (S0 : state) (C0 : execution_ctx) (exte : ext_expr) (o : out),
        @eq (option out) (out_of_ext_expr (expr_access_3 a1 a2 a3))
          (@Some out oo) ->
        abort oo ->
        not (abort_intercepted_expr (expr_access_3 a1 a2 a3)) ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq ext_expr exte (expr_access_3 a1 a2 a3) ->
        @eq out o oo -> P S C a1 a2 a3 oo) ->
       (red_expr S C (expr_access_3 a1 a2 a3) oo ->
        forall (S0 S1 : state) (C0 : execution_ctx) 
          (v1 v2 : value) (o1 o : out),
        red_expr S1 C (spec_to_string a3) o1 ->
        red_expr S1 C (expr_access_4 a1 o1) oo ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq value v1 a1 ->
        @eq out (out_void S1) a2 ->
        @eq value v2 a3 -> @eq out o oo -> P S C a1 (out_void S1) a3 oo) ->
       red_expr S C (expr_access_3 a1 a2 a3) oo -> P S C a1 a2 a3 oo.

Parameter inv_red_expr_expr_access_4
     : forall (S : state) (C : execution_ctx) (a1 : value) 
         (a2 oo : out)
         (P : state -> execution_ctx -> value -> out -> out -> Prop),
       (red_expr S C (expr_access_4 a1 a2) oo ->
        forall (S0 : state) (C0 : execution_ctx) (exte : ext_expr) (o : out),
        @eq (option out) (out_of_ext_expr (expr_access_4 a1 a2))
          (@Some out oo) ->
        abort oo ->
        not (abort_intercepted_expr (expr_access_4 a1 a2)) ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq ext_expr exte (expr_access_4 a1 a2) ->
        @eq out o oo -> P S C a1 a2 oo) ->
       (red_expr S C (expr_access_4 a1 a2) oo ->
        forall (S0 S1 : state) (C0 : execution_ctx) 
          (v1 : value) (x : prop_name) (r : ref),
        @eq ref r (ref_create_value a1 x (execution_ctx_strict C)) ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq value v1 a1 ->
        @eq out (out_ter S1 (res_val (value_prim (prim_string x)))) a2 ->
        @eq out (out_ter S1 (res_ref r)) oo ->
        P S C a1 (out_ter S1 (res_val (value_prim (prim_string x))))
          (out_ter S1 (res_ref r))) ->
       red_expr S C (expr_access_4 a1 a2) oo -> P S C a1 a2 oo.

Parameter inv_red_expr_expr_new_1
     : forall (S : state) (C : execution_ctx) (a1 : specret value)
         (a2 : list expr) (oo : out)
         (P : state ->
              execution_ctx -> specret value -> list expr -> out -> Prop),
       (red_expr S C (expr_new_1 a1 a2) oo ->
        forall (S0 : state) (C0 : execution_ctx) (exte : ext_expr) (o : out),
        @eq (option out) (out_of_ext_expr (expr_new_1 a1 a2)) (@Some out oo) ->
        abort oo ->
        not (abort_intercepted_expr (expr_new_1 a1 a2)) ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq ext_expr exte (expr_new_1 a1 a2) ->
        @eq out o oo -> P S C a1 a2 oo) ->
       (red_expr S C (expr_new_1 a1 a2) oo ->
        forall (S0 S1 : state) (C0 : execution_ctx) 
          (e2s : list expr) (v : value) (y1 : specret (list value)) 
          (o : out),
        @red_spec (list value) S1 C (spec_list_expr a2) y1 ->
        red_expr S1 C (expr_new_2 v y1) oo ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq (specret value) (@ret value S1 v) a1 ->
        @eq (list expr) e2s a2 ->
        @eq out o oo -> P S C (@ret value S1 v) a2 oo) ->
       red_expr S C (expr_new_1 a1 a2) oo -> P S C a1 a2 oo.

Parameter inv_red_expr_expr_new_2
     : forall (S : state) (C : execution_ctx) (a1 : value)
         (a2 : specret (list value)) (oo : out)
         (P : state ->
              execution_ctx -> value -> specret (list value) -> out -> Prop),
       (red_expr S C (expr_new_2 a1 a2) oo ->
        forall (S0 : state) (C0 : execution_ctx) (exte : ext_expr) (o : out),
        @eq (option out) (out_of_ext_expr (expr_new_2 a1 a2)) (@Some out oo) ->
        abort oo ->
        not (abort_intercepted_expr (expr_new_2 a1 a2)) ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq ext_expr exte (expr_new_2 a1 a2) ->
        @eq out o oo -> P S C a1 a2 oo) ->
       (red_expr S C (expr_new_2 a1 a2) oo ->
        forall (S0 S1 : state) (C0 : execution_ctx) 
          (o : out) (v : value) (vs : list value),
        not (@eq type (type_of a1) type_object) ->
        red_expr S0 C (spec_error native_error_type) oo ->
        @eq state S1 S ->
        @eq execution_ctx C0 C ->
        @eq value v a1 ->
        @eq (specret (list value)) (@ret (list value) S0 vs) a2 ->
        @eq out o oo -> P S C a1 (@ret (list value) S0 vs) oo) ->
       (red_expr S C (expr_new_2 a1 a2) oo ->
        forall (S0 S1 : state) (C0 : execution_ctx) 
          (o : out) (l : object_loc) (vs : list value),
        @object_method (option construct) object_construct_ S0 l
          (@None construct) ->
        red_expr S0 C (spec_error native_error_type) oo ->
        @eq state S1 S ->
        @eq execution_ctx C0 C ->
        @eq value (value_object l) a1 ->
        @eq (specret (list value)) (@ret (list value) S0 vs) a2 ->
        @eq out o oo -> P S C (value_object l) (@ret (list value) S0 vs) oo) ->
       (red_expr S C (expr_new_2 a1 a2) oo ->
        forall (S0 S1 : state) (C0 : execution_ctx) 
          (l : object_loc) (vs : list value) (o : out),
        red_expr S0 C (spec_construct l vs) oo ->
        @eq state S1 S ->
        @eq execution_ctx C0 C ->
        @eq value (value_object l) a1 ->
        @eq (specret (list value)) (@ret (list value) S0 vs) a2 ->
        @eq out o oo -> P S C (value_object l) (@ret (list value) S0 vs) oo) ->
       red_expr S C (expr_new_2 a1 a2) oo -> P S C a1 a2 oo.

Parameter inv_red_expr_expr_call_1
     : forall (S : state) (C : execution_ctx) (a1 : out) 
         (a2 : bool) (a3 : list expr) (oo : out)
         (P : state ->
              execution_ctx -> out -> bool -> list expr -> out -> Prop),
       (red_expr S C (expr_call_1 a1 a2 a3) oo ->
        forall (S0 : state) (C0 : execution_ctx) (exte : ext_expr) (o : out),
        @eq (option out) (out_of_ext_expr (expr_call_1 a1 a2 a3))
          (@Some out oo) ->
        abort oo ->
        not (abort_intercepted_expr (expr_call_1 a1 a2 a3)) ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq ext_expr exte (expr_call_1 a1 a2 a3) ->
        @eq out o oo -> P S C a1 a2 a3 oo) ->
       (red_expr S C (expr_call_1 a1 a2 a3) oo ->
        forall (S0 S1 : state) (C0 : execution_ctx) 
          (rv : resvalue) (is_eval_direct : bool) (e2s : list expr)
          (y1 : specret value) (o : out),
        @red_spec value S1 C (spec_get_value rv) y1 ->
        red_expr S1 C (expr_call_2 (res_normal rv) a2 a3 y1) oo ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq out (out_ter S1 (res_normal rv)) a1 ->
        @eq bool is_eval_direct a2 ->
        @eq (list expr) e2s a3 ->
        @eq out o oo -> P S C (out_ter S1 (res_normal rv)) a2 a3 oo) ->
       red_expr S C (expr_call_1 a1 a2 a3) oo -> P S C a1 a2 a3 oo.

Parameter inv_red_expr_expr_call_2
     : forall (S : state) (C : execution_ctx) (a1 : res) 
         (a2 : bool) (a3 : list expr) (a4 : specret value) 
         (oo : out)
         (P : state ->
              execution_ctx ->
              res -> bool -> list expr -> specret value -> out -> Prop),
       (red_expr S C (expr_call_2 a1 a2 a3 a4) oo ->
        forall (S0 : state) (C0 : execution_ctx) (exte : ext_expr) (o : out),
        @eq (option out) (out_of_ext_expr (expr_call_2 a1 a2 a3 a4))
          (@Some out oo) ->
        abort oo ->
        not (abort_intercepted_expr (expr_call_2 a1 a2 a3 a4)) ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq ext_expr exte (expr_call_2 a1 a2 a3 a4) ->
        @eq out o oo -> P S C a1 a2 a3 a4 oo) ->
       (red_expr S C (expr_call_2 a1 a2 a3 a4) oo ->
        forall (S0 S1 : state) (C0 : execution_ctx) 
          (rv : resvalue) (v : value) (e2s : list expr)
          (is_eval_direct : bool) (y1 : specret (list value)) 
          (o : out),
        @red_spec (list value) S1 C (spec_list_expr a3) y1 ->
        red_expr S1 C (expr_call_3 (res_normal rv) v a2 y1) oo ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq res (res_normal rv) a1 ->
        @eq bool is_eval_direct a2 ->
        @eq (list expr) e2s a3 ->
        @eq (specret value) (@ret value S1 v) a4 ->
        @eq out o oo -> P S C (res_normal rv) a2 a3 (@ret value S1 v) oo) ->
       red_expr S C (expr_call_2 a1 a2 a3 a4) oo -> P S C a1 a2 a3 a4 oo.

Parameter inv_red_expr_expr_call_3
     : forall (S : state) (C : execution_ctx) (a1 : res) 
         (a2 : value) (a3 : bool) (a4 : specret (list value)) 
         (oo : out)
         (P : state ->
              execution_ctx ->
              res -> value -> bool -> specret (list value) -> out -> Prop),
       (red_expr S C (expr_call_3 a1 a2 a3 a4) oo ->
        forall (S0 : state) (C0 : execution_ctx) (exte : ext_expr) (o : out),
        @eq (option out) (out_of_ext_expr (expr_call_3 a1 a2 a3 a4))
          (@Some out oo) ->
        abort oo ->
        not (abort_intercepted_expr (expr_call_3 a1 a2 a3 a4)) ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq ext_expr exte (expr_call_3 a1 a2 a3 a4) ->
        @eq out o oo -> P S C a1 a2 a3 a4 oo) ->
       (red_expr S C (expr_call_3 a1 a2 a3 a4) oo ->
        forall (S0 S1 : state) (C0 : execution_ctx) 
          (o : out) (rv : resvalue) (v : value) (is_eval_direct : bool)
          (vs : list value),
        Logic.or (not (@eq type (type_of a2) type_object))
          (@ex object_loc
             (fun l : object_loc =>
              Logic.and (@eq value a2 (value_object l))
                (not (is_callable S1 (value_object l))))) ->
        red_expr S1 C (spec_error native_error_type) oo ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq res (res_normal rv) a1 ->
        @eq value v a2 ->
        @eq bool is_eval_direct a3 ->
        @eq (specret (list value)) (@ret (list value) S1 vs) a4 ->
        @eq out o oo ->
        P S C (res_normal rv) a2 a3 (@ret (list value) S1 vs) oo) ->
       (red_expr S C (expr_call_3 a1 a2 a3 a4) oo ->
        forall (l : object_loc) (S0 S1 : state) (C0 : execution_ctx)
          (o : out) (rv : resvalue) (is_eval_direct : bool) 
          (vs : list value),
        is_callable S1 (value_object l) ->
        red_expr S1 C (expr_call_4 (res_normal rv) l a3 vs) oo ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq res (res_normal rv) a1 ->
        @eq value (value_object l) a2 ->
        @eq bool is_eval_direct a3 ->
        @eq (specret (list value)) (@ret (list value) S1 vs) a4 ->
        @eq out o oo ->
        P S C (res_normal rv) (value_object l) a3 (@ret (list value) S1 vs)
          oo) ->
       red_expr S C (expr_call_3 a1 a2 a3 a4) oo -> P S C a1 a2 a3 a4 oo.

Parameter inv_red_expr_expr_call_4
     : forall (S : state) (C : execution_ctx) (a1 : res) 
         (a2 : object_loc) (a3 : bool) (a4 : list value) 
         (oo : out)
         (P : state ->
              execution_ctx ->
              res -> object_loc -> bool -> list value -> out -> Prop),
       (red_expr S C (expr_call_4 a1 a2 a3 a4) oo ->
        forall (S0 : state) (C0 : execution_ctx) (exte : ext_expr) (o : out),
        @eq (option out) (out_of_ext_expr (expr_call_4 a1 a2 a3 a4))
          (@Some out oo) ->
        abort oo ->
        not (abort_intercepted_expr (expr_call_4 a1 a2 a3 a4)) ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq ext_expr exte (expr_call_4 a1 a2 a3 a4) ->
        @eq out o oo -> P S C a1 a2 a3 a4 oo) ->
       (red_expr S C (expr_call_4 a1 a2 a3 a4) oo ->
        forall (v : value) (S0 : state) (C0 : execution_ctx) 
          (o : out) (r : ref) (l : object_loc) (is_eval_direct : bool)
          (vs : list value),
        ref_is_property r ->
        ref_is_value r v ->
        red_expr S C (expr_call_5 a2 a3 a4 (out_ter S (res_val v))) oo ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq res (res_normal (resvalue_ref r)) a1 ->
        @eq object_loc l a2 ->
        @eq bool is_eval_direct a3 ->
        @eq (list value) vs a4 ->
        @eq out o oo -> P S C (res_normal (resvalue_ref r)) a2 a3 a4 oo) ->
       (red_expr S C (expr_call_4 a1 a2 a3 a4) oo ->
        forall (L : env_loc) (o1 : out) (S0 : state) 
          (C0 : execution_ctx) (o : out) (r : ref) 
          (l : object_loc) (is_eval_direct : bool) 
          (vs : list value),
        ref_is_env_record r L ->
        red_expr S C (spec_env_record_implicit_this_value L) o1 ->
        red_expr S C (expr_call_5 a2 a3 a4 o1) oo ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq res (res_normal (resvalue_ref r)) a1 ->
        @eq object_loc l a2 ->
        @eq bool is_eval_direct a3 ->
        @eq (list value) vs a4 ->
        @eq out o oo -> P S C (res_normal (resvalue_ref r)) a2 a3 a4 oo) ->
       (red_expr S C (expr_call_4 a1 a2 a3 a4) oo ->
        forall (S0 : state) (C0 : execution_ctx) (v : value) 
          (l : object_loc) (is_eval_direct : bool) 
          (vs : list value) (o : out),
        red_expr S C
          (expr_call_5 a2 a3 a4 (out_ter S (res_val (value_prim prim_undef))))
          oo ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq res (res_normal (resvalue_value v)) a1 ->
        @eq object_loc l a2 ->
        @eq bool is_eval_direct a3 ->
        @eq (list value) vs a4 ->
        @eq out o oo -> P S C (res_normal (resvalue_value v)) a2 a3 a4 oo) ->
       red_expr S C (expr_call_4 a1 a2 a3 a4) oo -> P S C a1 a2 a3 a4 oo.

Parameter inv_red_expr_expr_call_5
     : forall (S : state) (C : execution_ctx) (a1 : object_loc) 
         (a2 : bool) (a3 : list value) (a4 oo : out)
         (P : state ->
              execution_ctx ->
              object_loc -> bool -> list value -> out -> out -> Prop),
       (red_expr S C (expr_call_5 a1 a2 a3 a4) oo ->
        forall (S0 : state) (C0 : execution_ctx) (exte : ext_expr) (o : out),
        @eq (option out) (out_of_ext_expr (expr_call_5 a1 a2 a3 a4))
          (@Some out oo) ->
        abort oo ->
        not (abort_intercepted_expr (expr_call_5 a1 a2 a3 a4)) ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq ext_expr exte (expr_call_5 a1 a2 a3 a4) ->
        @eq out o oo -> P S C a1 a2 a3 a4 oo) ->
       (red_expr S C (expr_call_5 a1 a2 a3 a4) oo ->
        forall (S0 S1 : state) (C0 : execution_ctx) 
          (is_eval_direct : bool) (vs : list value) 
          (v : value) (o : out),
        red_expr S1 C (spec_call_global_eval a2 a3) oo ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq object_loc (object_loc_prealloc prealloc_global_eval) a1 ->
        @eq bool is_eval_direct a2 ->
        @eq (list value) vs a3 ->
        @eq out (out_ter S1 (res_val v)) a4 ->
        @eq out o oo ->
        P S C (object_loc_prealloc prealloc_global_eval) a2 a3
          (out_ter S1 (res_val v)) oo) ->
       (red_expr S C (expr_call_5 a1 a2 a3 a4) oo ->
        forall (S0 S1 : state) (C0 : execution_ctx) 
          (l : object_loc) (is_eval_direct : bool) 
          (vs : list value) (v : value) (o : out),
        not (@eq object_loc a1 (object_loc_prealloc prealloc_global_eval)) ->
        red_expr S1 C (spec_call a1 v a3) oo ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq object_loc l a1 ->
        @eq bool is_eval_direct a2 ->
        @eq (list value) vs a3 ->
        @eq out (out_ter S1 (res_val v)) a4 ->
        @eq out o oo -> P S C a1 a2 a3 (out_ter S1 (res_val v)) oo) ->
       red_expr S C (expr_call_5 a1 a2 a3 a4) oo -> P S C a1 a2 a3 a4 oo.

Parameter inv_red_expr_spec_eval
     : forall (S : state) (C : execution_ctx) (a1 : bool) 
         (a2 : value) (a3 : list value) (oo : out)
         (P : state ->
              execution_ctx -> bool -> value -> list value -> out -> Prop),
       (red_expr S C (spec_eval a1 a2 a3) oo ->
        forall (S0 : state) (C0 : execution_ctx) (exte : ext_expr) (o : out),
        @eq (option out) (out_of_ext_expr (spec_eval a1 a2 a3))
          (@Some out oo) ->
        abort oo ->
        not (abort_intercepted_expr (spec_eval a1 a2 a3)) ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq ext_expr exte (spec_eval a1 a2 a3) ->
        @eq out o oo -> P S C a1 a2 a3 oo) ->
       red_expr S C (spec_eval a1 a2 a3) oo -> P S C a1 a2 a3 oo.

Parameter inv_red_expr_expr_unary_op_1
     : forall (S : state) (C : execution_ctx) (a1 : unary_op)
         (a2 : specret value) (oo : out)
         (P : state ->
              execution_ctx -> unary_op -> specret value -> out -> Prop),
       (red_expr S C (expr_unary_op_1 a1 a2) oo ->
        forall (S0 : state) (C0 : execution_ctx) (exte : ext_expr) (o : out),
        @eq (option out) (out_of_ext_expr (expr_unary_op_1 a1 a2))
          (@Some out oo) ->
        abort oo ->
        not (abort_intercepted_expr (expr_unary_op_1 a1 a2)) ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq ext_expr exte (expr_unary_op_1 a1 a2) ->
        @eq out o oo -> P S C a1 a2 oo) ->
       (red_expr S C (expr_unary_op_1 a1 a2) oo ->
        forall (S0 S1 : state) (C0 : execution_ctx) 
          (op : unary_op) (v : value) (o : out),
        red_expr S1 C (expr_unary_op_2 a1 v) oo ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq unary_op op a1 ->
        @eq (specret value) (@ret value S1 v) a2 ->
        @eq out o oo -> P S C a1 (@ret value S1 v) oo) ->
       red_expr S C (expr_unary_op_1 a1 a2) oo -> P S C a1 a2 oo.

Parameter inv_red_expr_expr_unary_op_2
     : forall (S : state) (C : execution_ctx) (a1 : unary_op) 
         (a2 : value) (oo : out)
         (P : state -> execution_ctx -> unary_op -> value -> out -> Prop),
       (red_expr S C (expr_unary_op_2 a1 a2) oo ->
        forall (S0 : state) (C0 : execution_ctx) (exte : ext_expr) (o : out),
        @eq (option out) (out_of_ext_expr (expr_unary_op_2 a1 a2))
          (@Some out oo) ->
        abort oo ->
        not (abort_intercepted_expr (expr_unary_op_2 a1 a2)) ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq ext_expr exte (expr_unary_op_2 a1 a2) ->
        @eq out o oo -> P S C a1 a2 oo) ->
       (red_expr S C (expr_unary_op_2 a1 a2) oo ->
        forall (S0 : state) (C0 : execution_ctx) (v : value),
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq unary_op unary_op_void a1 ->
        @eq value v a2 ->
        @eq out (out_ter S (res_val (value_prim prim_undef))) oo ->
        P S C unary_op_void a2 (out_ter S (res_val (value_prim prim_undef)))) ->
       (red_expr S C (expr_unary_op_2 a1 a2) oo ->
        forall (S0 : state) (C0 : execution_ctx) (v : value) (o : out),
        red_expr S C (spec_to_number a2) oo ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq unary_op unary_op_add a1 ->
        @eq value v a2 -> @eq out o oo -> P S C unary_op_add a2 oo) ->
       (red_expr S C (expr_unary_op_2 a1 a2) oo ->
        forall (S0 : state) (C0 : execution_ctx) (v : value) (o1 o : out),
        red_expr S C (spec_to_number a2) o1 ->
        red_expr S C (expr_unary_op_neg_1 o1) oo ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq unary_op unary_op_neg a1 ->
        @eq value v a2 -> @eq out o oo -> P S C unary_op_neg a2 oo) ->
       (red_expr S C (expr_unary_op_2 a1 a2) oo ->
        forall (S0 : state) (C0 : execution_ctx) (v : value) 
          (y1 : specret Z) (o : out),
        @red_spec Z S C (spec_to_int32 a2) y1 ->
        red_expr S C (expr_unary_op_bitwise_not_1 y1) oo ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq unary_op unary_op_bitwise_not a1 ->
        @eq value v a2 -> @eq out o oo -> P S C unary_op_bitwise_not a2 oo) ->
       (red_expr S C (expr_unary_op_2 a1 a2) oo ->
        forall (S0 : state) (C0 : execution_ctx) (v : value) (o1 o : out),
        red_expr S C (spec_to_boolean a2) o1 ->
        red_expr S C (expr_unary_op_not_1 o1) oo ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq unary_op unary_op_not a1 ->
        @eq value v a2 -> @eq out o oo -> P S C unary_op_not a2 oo) ->
       red_expr S C (expr_unary_op_2 a1 a2) oo -> P S C a1 a2 oo.

Parameter inv_red_expr_expr_delete_1
     : forall (S : state) (C : execution_ctx) (a1 oo : out)
         (P : state -> execution_ctx -> out -> out -> Prop),
       (red_expr S C (expr_delete_1 a1) oo ->
        forall (S0 : state) (C0 : execution_ctx) (exte : ext_expr) (o : out),
        @eq (option out) (out_of_ext_expr (expr_delete_1 a1)) (@Some out oo) ->
        abort oo ->
        not (abort_intercepted_expr (expr_delete_1 a1)) ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq ext_expr exte (expr_delete_1 a1) -> @eq out o oo -> P S C a1 oo) ->
       (red_expr S C (expr_delete_1 a1) oo ->
        forall (S0 S1 : state) (C0 : execution_ctx) (rv : resvalue),
        not (resvalue_is_ref rv) ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq out (out_ter S1 (res_normal rv)) a1 ->
        @eq out (out_ter S1 (res_val (value_prim (prim_bool true)))) oo ->
        P S C (out_ter S1 (res_normal rv))
          (out_ter S1 (res_val (value_prim (prim_bool true))))) ->
       (red_expr S C (expr_delete_1 a1) oo ->
        forall (S0 S1 : state) (C0 : execution_ctx) (r : ref) (o : out),
        ref_is_unresolvable r ->
        red_expr S1 C (expr_delete_2 r) oo ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq out (out_ter S1 (res_ref r)) a1 ->
        @eq out o oo -> P S C (out_ter S1 (res_ref r)) oo) ->
       (red_expr S C (expr_delete_1 a1) oo ->
        forall (S0 S1 : state) (C0 : execution_ctx) 
          (r : ref) (v : value) (o1 o : out),
        ref_is_property r ->
        @eq ref_base_type (ref_base r) (ref_base_type_value v) ->
        red_expr S1 C (spec_to_object v) o1 ->
        red_expr S1 C (expr_delete_3 r o1) oo ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq out (out_ter S1 (res_ref r)) a1 ->
        @eq out o oo -> P S C (out_ter S1 (res_ref r)) oo) ->
       (red_expr S C (expr_delete_1 a1) oo ->
        forall (S0 S1 : state) (C0 : execution_ctx) 
          (r : ref) (L : env_loc) (o : out),
        ref_is_env_record r L ->
        red_expr S1 C (expr_delete_4 r L) oo ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq out (out_ter S1 (res_ref r)) a1 ->
        @eq out o oo -> P S C (out_ter S1 (res_ref r)) oo) ->
       red_expr S C (expr_delete_1 a1) oo -> P S C a1 oo.

Parameter inv_red_expr_expr_delete_2
     : forall (S : state) (C : execution_ctx) (a1 : ref) 
         (oo : out) (P : state -> execution_ctx -> ref -> out -> Prop),
       (red_expr S C (expr_delete_2 a1) oo ->
        forall (S0 : state) (C0 : execution_ctx) (exte : ext_expr) (o : out),
        @eq (option out) (out_of_ext_expr (expr_delete_2 a1)) (@Some out oo) ->
        abort oo ->
        not (abort_intercepted_expr (expr_delete_2 a1)) ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq ext_expr exte (expr_delete_2 a1) -> @eq out o oo -> P S C a1 oo) ->
       (red_expr S C (expr_delete_2 a1) oo ->
        forall (S0 : state) (C0 : execution_ctx) (r : ref) (o : out),
        @eq bool (ref_strict a1) true ->
        red_expr S C (spec_error native_error_syntax) oo ->
        @eq state S0 S ->
        @eq execution_ctx C0 C -> @eq ref r a1 -> @eq out o oo -> P S C a1 oo) ->
       (red_expr S C (expr_delete_2 a1) oo ->
        forall (S0 : state) (C0 : execution_ctx) (r : ref),
        @eq bool (ref_strict a1) false ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq ref r a1 ->
        @eq out (out_ter S (res_val (value_prim (prim_bool true)))) oo ->
        P S C a1 (out_ter S (res_val (value_prim (prim_bool true))))) ->
       red_expr S C (expr_delete_2 a1) oo -> P S C a1 oo.

Parameter inv_red_expr_expr_delete_3
     : forall (S : state) (C : execution_ctx) (a1 : ref) 
         (a2 oo : out)
         (P : state -> execution_ctx -> ref -> out -> out -> Prop),
       (red_expr S C (expr_delete_3 a1 a2) oo ->
        forall (S0 : state) (C0 : execution_ctx) (exte : ext_expr) (o : out),
        @eq (option out) (out_of_ext_expr (expr_delete_3 a1 a2))
          (@Some out oo) ->
        abort oo ->
        not (abort_intercepted_expr (expr_delete_3 a1 a2)) ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq ext_expr exte (expr_delete_3 a1 a2) ->
        @eq out o oo -> P S C a1 a2 oo) ->
       (red_expr S C (expr_delete_3 a1 a2) oo ->
        forall (S0 S1 : state) (C0 : execution_ctx) 
          (r : ref) (l : object_loc) (o : out),
        red_expr S1 C (spec_object_delete l (ref_name a1) (ref_strict a1)) oo ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq ref r a1 ->
        @eq out (out_ter S1 (res_val (value_object l))) a2 ->
        @eq out o oo -> P S C a1 (out_ter S1 (res_val (value_object l))) oo) ->
       red_expr S C (expr_delete_3 a1 a2) oo -> P S C a1 a2 oo.

Parameter inv_red_expr_expr_delete_4
     : forall (S : state) (C : execution_ctx) (a1 : ref) 
         (a2 : env_loc) (oo : out)
         (P : state -> execution_ctx -> ref -> nat -> out -> Prop),
       (red_expr S C (expr_delete_4 a1 a2) oo ->
        forall (S0 : state) (C0 : execution_ctx) (exte : ext_expr) (o : out),
        @eq (option out) (out_of_ext_expr (expr_delete_4 a1 a2))
          (@Some out oo) ->
        abort oo ->
        not (abort_intercepted_expr (expr_delete_4 a1 a2)) ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq ext_expr exte (expr_delete_4 a1 a2) ->
        @eq out o oo -> P S C a1 a2 oo) ->
       (red_expr S C (expr_delete_4 a1 a2) oo ->
        forall (S0 : state) (C0 : execution_ctx) (r : ref) 
          (L : env_loc) (o : out),
        @eq bool (ref_strict a1) true ->
        red_expr S C (spec_error native_error_syntax) oo ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq ref r a1 -> @eq env_loc L a2 -> @eq out o oo -> P S C a1 a2 oo) ->
       (red_expr S C (expr_delete_4 a1 a2) oo ->
        forall (S0 : state) (C0 : execution_ctx) (r : ref) 
          (L : env_loc) (o : out),
        @eq bool (ref_strict a1) false ->
        red_expr S C (spec_env_record_delete_binding a2 (ref_name a1)) oo ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq ref r a1 -> @eq env_loc L a2 -> @eq out o oo -> P S C a1 a2 oo) ->
       red_expr S C (expr_delete_4 a1 a2) oo -> P S C a1 a2 oo.

Parameter inv_red_expr_expr_typeof_1
     : forall (S : state) (C : execution_ctx) (a1 oo : out)
         (P : state -> execution_ctx -> out -> out -> Prop),
       (red_expr S C (expr_typeof_1 a1) oo ->
        forall (S0 : state) (C0 : execution_ctx) (exte : ext_expr) (o : out),
        @eq (option out) (out_of_ext_expr (expr_typeof_1 a1)) (@Some out oo) ->
        abort oo ->
        not (abort_intercepted_expr (expr_typeof_1 a1)) ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq ext_expr exte (expr_typeof_1 a1) -> @eq out o oo -> P S C a1 oo) ->
       (red_expr S C (expr_typeof_1 a1) oo ->
        forall (S0 S1 : state) (C0 : execution_ctx) (v : value) (o : out),
        red_expr S1 C (expr_typeof_2 (@ret value S1 v)) oo ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq out (out_ter S1 (res_val v)) a1 ->
        @eq out o oo -> P S C (out_ter S1 (res_val v)) oo) ->
       (red_expr S C (expr_typeof_1 a1) oo ->
        forall (S0 S1 : state) (r : ref) (C0 : execution_ctx),
        ref_is_unresolvable r ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq out (out_ter S1 (res_ref r)) a1 ->
        @eq out
          (out_ter S1
             (res_val
                (value_prim
                   (prim_string
                      (String
                         (Ascii true false true false true true true false)
                         (String
                            (Ascii false true true true false true true false)
                            (String
                               (Ascii false false true false false true true
                                  false)
                               (String
                                  (Ascii true false true false false true
                                     true false)
                                  (String
                                     (Ascii false true true false false true
                                        true false)
                                     (String
                                        (Ascii true false false true false
                                           true true false)
                                        (String
                                           (Ascii false true true true false
                                              true true false)
                                           (String
                                              (Ascii true false true false
                                                 false true true false)
                                              (String
                                                 (Ascii false false true
                                                  false false true true false)
                                                 EmptyString))))))))))))) oo ->
        P S C (out_ter S1 (res_ref r))
          (out_ter S1
             (res_val
                (value_prim
                   (prim_string
                      (String
                         (Ascii true false true false true true true false)
                         (String
                            (Ascii false true true true false true true false)
                            (String
                               (Ascii false false true false false true true
                                  false)
                               (String
                                  (Ascii true false true false false true
                                     true false)
                                  (String
                                     (Ascii false true true false false true
                                        true false)
                                     (String
                                        (Ascii true false false true false
                                           true true false)
                                        (String
                                           (Ascii false true true true false
                                              true true false)
                                           (String
                                              (Ascii true false true false
                                                 false true true false)
                                              (String
                                                 (Ascii false false true
                                                  false false true true false)
                                                 EmptyString)))))))))))))) ->
       (red_expr S C (expr_typeof_1 a1) oo ->
        forall (S0 S1 : state) (C0 : execution_ctx) 
          (r : ref) (y1 : specret value) (o : out),
        not (ref_is_unresolvable r) ->
        @red_spec value S1 C (spec_get_value (resvalue_ref r)) y1 ->
        red_expr S1 C (expr_typeof_2 y1) oo ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq out (out_ter S1 (res_ref r)) a1 ->
        @eq out o oo -> P S C (out_ter S1 (res_ref r)) oo) ->
       red_expr S C (expr_typeof_1 a1) oo -> P S C a1 oo.

Parameter inv_red_expr_expr_typeof_2
     : forall (S : state) (C : execution_ctx) (a1 : specret value) 
         (oo : out)
         (P : state -> execution_ctx -> specret value -> out -> Prop),
       (red_expr S C (expr_typeof_2 a1) oo ->
        forall (S0 : state) (C0 : execution_ctx) (exte : ext_expr) (o : out),
        @eq (option out) (out_of_ext_expr (expr_typeof_2 a1)) (@Some out oo) ->
        abort oo ->
        not (abort_intercepted_expr (expr_typeof_2 a1)) ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq ext_expr exte (expr_typeof_2 a1) -> @eq out o oo -> P S C a1 oo) ->
       (red_expr S C (expr_typeof_2 a1) oo ->
        forall (S0 S1 : state) (s : string) (C0 : execution_ctx) (v : value),
        @eq string s (typeof_value S1 v) ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq (specret value) (@ret value S1 v) a1 ->
        @eq out (out_ter S1 (res_val (value_prim (prim_string s)))) oo ->
        P S C (@ret value S1 v)
          (out_ter S1 (res_val (value_prim (prim_string s))))) ->
       red_expr S C (expr_typeof_2 a1) oo -> P S C a1 oo.

Parameter inv_red_expr_expr_prepost_1
     : forall (S : state) (C : execution_ctx) (a1 : unary_op) 
         (a2 oo : out)
         (P : state -> execution_ctx -> unary_op -> out -> out -> Prop),
       (red_expr S C (expr_prepost_1 a1 a2) oo ->
        forall (S0 : state) (C0 : execution_ctx) (exte : ext_expr) (o : out),
        @eq (option out) (out_of_ext_expr (expr_prepost_1 a1 a2))
          (@Some out oo) ->
        abort oo ->
        not (abort_intercepted_expr (expr_prepost_1 a1 a2)) ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq ext_expr exte (expr_prepost_1 a1 a2) ->
        @eq out o oo -> P S C a1 a2 oo) ->
       (red_expr S C (expr_prepost_1 a1 a2) oo ->
        forall (S0 S1 : state) (C0 : execution_ctx) 
          (rv : resvalue) (op : unary_op) (y1 : specret value) 
          (o : out),
        @red_spec value S1 C (spec_get_value rv) y1 ->
        red_expr S1 C (expr_prepost_2 a1 (res_normal rv) y1) oo ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq unary_op op a1 ->
        @eq out (out_ter S1 (res_normal rv)) a2 ->
        @eq out o oo -> P S C a1 (out_ter S1 (res_normal rv)) oo) ->
       red_expr S C (expr_prepost_1 a1 a2) oo -> P S C a1 a2 oo.

Parameter inv_red_expr_expr_prepost_2
     : forall (S : state) (C : execution_ctx) (a1 : unary_op) 
         (a2 : res) (a3 : specret value) (oo : out)
         (P : state ->
              execution_ctx ->
              unary_op -> res -> specret value -> out -> Prop),
       (red_expr S C (expr_prepost_2 a1 a2 a3) oo ->
        forall (S0 : state) (C0 : execution_ctx) (exte : ext_expr) (o : out),
        @eq (option out) (out_of_ext_expr (expr_prepost_2 a1 a2 a3))
          (@Some out oo) ->
        abort oo ->
        not (abort_intercepted_expr (expr_prepost_2 a1 a2 a3)) ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq ext_expr exte (expr_prepost_2 a1 a2 a3) ->
        @eq out o oo -> P S C a1 a2 a3 oo) ->
       (red_expr S C (expr_prepost_2 a1 a2 a3) oo ->
        forall (S0 S1 : state) (C0 : execution_ctx) 
          (rv : resvalue) (op : unary_op) (v : value) 
          (o1 o : out),
        red_expr S1 C (spec_to_number v) o1 ->
        red_expr S1 C (expr_prepost_3 a1 (res_normal rv) o1) oo ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq unary_op op a1 ->
        @eq res (res_normal rv) a2 ->
        @eq (specret value) (@ret value S1 v) a3 ->
        @eq out o oo -> P S C a1 (res_normal rv) (@ret value S1 v) oo) ->
       red_expr S C (expr_prepost_2 a1 a2 a3) oo -> P S C a1 a2 a3 oo.

Parameter inv_red_expr_expr_prepost_3
     : forall (S : state) (C : execution_ctx) (a1 : unary_op) 
         (a2 : res) (a3 oo : out)
         (P : state -> execution_ctx -> unary_op -> res -> out -> out -> Prop),
       (red_expr S C (expr_prepost_3 a1 a2 a3) oo ->
        forall (S0 : state) (C0 : execution_ctx) (exte : ext_expr) (o : out),
        @eq (option out) (out_of_ext_expr (expr_prepost_3 a1 a2 a3))
          (@Some out oo) ->
        abort oo ->
        not (abort_intercepted_expr (expr_prepost_3 a1 a2 a3)) ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq ext_expr exte (expr_prepost_3 a1 a2 a3) ->
        @eq out o oo -> P S C a1 a2 a3 oo) ->
       (red_expr S C (expr_prepost_3 a1 a2 a3) oo ->
        forall (S0 S1 : state) (C0 : execution_ctx) 
          (rv : resvalue) (op : unary_op)
          (number_op : JsNumber.number -> JsNumber.number) 
          (is_pre : bool) (v : value) (n1 n2 : JsNumber.number) 
          (o1 o : out),
        prepost_op a1 number_op is_pre ->
        @eq JsNumber.number n2 (number_op n1) ->
        @eq value v
          (value_prim
             (prim_number
                match is_pre return JsNumber.number with
                | true => n2
                | false => n1
                end)) ->
        red_expr S1 C (spec_put_value rv (value_prim (prim_number n2))) o1 ->
        red_expr S1 C (expr_prepost_4 v o1) oo ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq unary_op op a1 ->
        @eq res (res_normal rv) a2 ->
        @eq out (out_ter S1 (res_val (value_prim (prim_number n1)))) a3 ->
        @eq out o oo ->
        P S C a1 (res_normal rv)
          (out_ter S1 (res_val (value_prim (prim_number n1)))) oo) ->
       red_expr S C (expr_prepost_3 a1 a2 a3) oo -> P S C a1 a2 a3 oo.

Parameter inv_red_expr_expr_prepost_4
     : forall (S : state) (C : execution_ctx) (a1 : value) 
         (a2 oo : out)
         (P : state -> execution_ctx -> value -> out -> out -> Prop),
       (red_expr S C (expr_prepost_4 a1 a2) oo ->
        forall (S0 : state) (C0 : execution_ctx) (exte : ext_expr) (o : out),
        @eq (option out) (out_of_ext_expr (expr_prepost_4 a1 a2))
          (@Some out oo) ->
        abort oo ->
        not (abort_intercepted_expr (expr_prepost_4 a1 a2)) ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq ext_expr exte (expr_prepost_4 a1 a2) ->
        @eq out o oo -> P S C a1 a2 oo) ->
       (red_expr S C (expr_prepost_4 a1 a2) oo ->
        forall (S0 S1 : state) (C0 : execution_ctx) (v : value),
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq value v a1 ->
        @eq out (out_void S1) a2 ->
        @eq out (out_ter S1 (res_val a1)) oo ->
        P S C a1 (out_void S1) (out_ter S1 (res_val a1))) ->
       red_expr S C (expr_prepost_4 a1 a2) oo -> P S C a1 a2 oo.

Parameter inv_red_expr_expr_unary_op_neg_1
     : forall (S : state) (C : execution_ctx) (a1 oo : out)
         (P : state -> execution_ctx -> out -> out -> Prop),
       (red_expr S C (expr_unary_op_neg_1 a1) oo ->
        forall (S0 : state) (C0 : execution_ctx) (exte : ext_expr) (o : out),
        @eq (option out) (out_of_ext_expr (expr_unary_op_neg_1 a1))
          (@Some out oo) ->
        abort oo ->
        not (abort_intercepted_expr (expr_unary_op_neg_1 a1)) ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq ext_expr exte (expr_unary_op_neg_1 a1) ->
        @eq out o oo -> P S C a1 oo) ->
       (red_expr S C (expr_unary_op_neg_1 a1) oo ->
        forall (S0 S1 : state) (C0 : execution_ctx) (n : JsNumber.number),
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq out (out_ter S1 (res_val (value_prim (prim_number n)))) a1 ->
        @eq out
          (out_ter S1 (res_val (value_prim (prim_number (JsNumber.neg n)))))
          oo ->
        P S C (out_ter S1 (res_val (value_prim (prim_number n))))
          (out_ter S1 (res_val (value_prim (prim_number (JsNumber.neg n)))))) ->
       red_expr S C (expr_unary_op_neg_1 a1) oo -> P S C a1 oo.

Parameter inv_red_expr_expr_unary_op_bitwise_not_1
     : forall (S : state) (C : execution_ctx) (a1 : specret Z) 
         (oo : out) (P : state -> execution_ctx -> specret Z -> out -> Prop),
       (red_expr S C (expr_unary_op_bitwise_not_1 a1) oo ->
        forall (S0 : state) (C0 : execution_ctx) (exte : ext_expr) (o : out),
        @eq (option out) (out_of_ext_expr (expr_unary_op_bitwise_not_1 a1))
          (@Some out oo) ->
        abort oo ->
        not (abort_intercepted_expr (expr_unary_op_bitwise_not_1 a1)) ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq ext_expr exte (expr_unary_op_bitwise_not_1 a1) ->
        @eq out o oo -> P S C a1 oo) ->
       (red_expr S C (expr_unary_op_bitwise_not_1 a1) oo ->
        forall (S0 S1 : state) (C0 : execution_ctx) 
          (k : Z) (n : JsNumber.number),
        @eq JsNumber.number n
          (JsNumber.of_int (JsNumber.int32_bitwise_not k)) ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq (specret Z) (@ret Z S1 k) a1 ->
        @eq out (out_ter S1 (res_val (value_prim (prim_number n)))) oo ->
        P S C (@ret Z S1 k)
          (out_ter S1 (res_val (value_prim (prim_number n))))) ->
       red_expr S C (expr_unary_op_bitwise_not_1 a1) oo -> P S C a1 oo.

Parameter inv_red_expr_expr_unary_op_not_1
     : forall (S : state) (C : execution_ctx) (a1 oo : out)
         (P : state -> execution_ctx -> out -> out -> Prop),
       (red_expr S C (expr_unary_op_not_1 a1) oo ->
        forall (S0 : state) (C0 : execution_ctx) (exte : ext_expr) (o : out),
        @eq (option out) (out_of_ext_expr (expr_unary_op_not_1 a1))
          (@Some out oo) ->
        abort oo ->
        not (abort_intercepted_expr (expr_unary_op_not_1 a1)) ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq ext_expr exte (expr_unary_op_not_1 a1) ->
        @eq out o oo -> P S C a1 oo) ->
       (red_expr S C (expr_unary_op_not_1 a1) oo ->
        forall (S0 S1 : state) (C0 : execution_ctx) (b : bool),
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq out (out_ter S1 (res_val (value_prim (prim_bool b)))) a1 ->
        @eq out (out_ter S1 (res_val (value_prim (prim_bool (neg b))))) oo ->
        P S C (out_ter S1 (res_val (value_prim (prim_bool b))))
          (out_ter S1 (res_val (value_prim (prim_bool (neg b)))))) ->
       red_expr S C (expr_unary_op_not_1 a1) oo -> P S C a1 oo.

Parameter inv_red_expr_expr_conditional_1
     : forall (S : state) (C : execution_ctx) (a1 : specret value)
         (a2 a3 : expr) (oo : out)
         (P : state ->
              execution_ctx -> specret value -> expr -> expr -> out -> Prop),
       (red_expr S C (expr_conditional_1 a1 a2 a3) oo ->
        forall (S0 : state) (C0 : execution_ctx) (exte : ext_expr) (o : out),
        @eq (option out) (out_of_ext_expr (expr_conditional_1 a1 a2 a3))
          (@Some out oo) ->
        abort oo ->
        not (abort_intercepted_expr (expr_conditional_1 a1 a2 a3)) ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq ext_expr exte (expr_conditional_1 a1 a2 a3) ->
        @eq out o oo -> P S C a1 a2 a3 oo) ->
       (red_expr S C (expr_conditional_1 a1 a2 a3) oo ->
        forall (S0 S1 : state) (C0 : execution_ctx) 
          (e : expr) (b : bool) (e2 e3 : expr) (y1 : specret value) 
          (o : out),
        @eq expr e
          match classicT (@eq bool b true) return expr with
          | left _ => a2
          | right _ => a3
          end ->
        @red_spec value S1 C (spec_expr_get_value e) y1 ->
        red_expr S1 C (expr_conditional_2 y1) oo ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq (specret value) (vret S1 (value_prim (prim_bool b))) a1 ->
        @eq expr e2 a2 ->
        @eq expr e3 a3 ->
        @eq out o oo -> P S C (vret S1 (value_prim (prim_bool b))) a2 a3 oo) ->
       red_expr S C (expr_conditional_1 a1 a2 a3) oo -> P S C a1 a2 a3 oo.

Parameter inv_red_expr_expr_conditional_1'
     : forall (S : state) (C : execution_ctx) (a1 : out) 
         (a2 a3 : expr) (oo : out)
         (P : state -> execution_ctx -> out -> expr -> expr -> out -> Prop),
       (red_expr S C (expr_conditional_1' a1 a2 a3) oo ->
        forall (S0 : state) (C0 : execution_ctx) (exte : ext_expr) (o : out),
        @eq (option out) (out_of_ext_expr (expr_conditional_1' a1 a2 a3))
          (@Some out oo) ->
        abort oo ->
        not (abort_intercepted_expr (expr_conditional_1' a1 a2 a3)) ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq ext_expr exte (expr_conditional_1' a1 a2 a3) ->
        @eq out o oo -> P S C a1 a2 a3 oo) ->
       red_expr S C (expr_conditional_1' a1 a2 a3) oo -> P S C a1 a2 a3 oo.

Parameter inv_red_expr_expr_conditional_2
     : forall (S : state) (C : execution_ctx) (a1 : specret value) 
         (oo : out)
         (P : state -> execution_ctx -> specret value -> out -> Prop),
       (red_expr S C (expr_conditional_2 a1) oo ->
        forall (S0 : state) (C0 : execution_ctx) (exte : ext_expr) (o : out),
        @eq (option out) (out_of_ext_expr (expr_conditional_2 a1))
          (@Some out oo) ->
        abort oo ->
        not (abort_intercepted_expr (expr_conditional_2 a1)) ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq ext_expr exte (expr_conditional_2 a1) ->
        @eq out o oo -> P S C a1 oo) ->
       (red_expr S C (expr_conditional_2 a1) oo ->
        forall (S0 S1 : state) (C0 : execution_ctx) (v : value),
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq (specret value) (@ret value S1 v) a1 ->
        @eq out (out_ter S1 (res_val v)) oo ->
        P S C (@ret value S1 v) (out_ter S1 (res_val v))) ->
       red_expr S C (expr_conditional_2 a1) oo -> P S C a1 oo.

Parameter inv_red_expr_expr_binary_op_1
     : forall (S : state) (C : execution_ctx) (a1 : binary_op)
         (a2 : specret value) (a3 : expr) (oo : out)
         (P : state ->
              execution_ctx ->
              binary_op -> specret value -> expr -> out -> Prop),
       (red_expr S C (expr_binary_op_1 a1 a2 a3) oo ->
        forall (S0 : state) (C0 : execution_ctx) (exte : ext_expr) (o : out),
        @eq (option out) (out_of_ext_expr (expr_binary_op_1 a1 a2 a3))
          (@Some out oo) ->
        abort oo ->
        not (abort_intercepted_expr (expr_binary_op_1 a1 a2 a3)) ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq ext_expr exte (expr_binary_op_1 a1 a2 a3) ->
        @eq out o oo -> P S C a1 a2 a3 oo) ->
       (red_expr S C (expr_binary_op_1 a1 a2 a3) oo ->
        forall (S0 S1 : state) (C0 : execution_ctx) 
          (op : binary_op) (v1 : value) (e2 : expr) 
          (y1 : specret value) (o : out),
        @red_spec value S1 C (spec_expr_get_value a3) y1 ->
        red_expr S1 C (expr_binary_op_2 a1 v1 y1) oo ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq binary_op op a1 ->
        @eq (specret value) (@ret value S1 v1) a2 ->
        @eq expr e2 a3 -> @eq out o oo -> P S C a1 (@ret value S1 v1) a3 oo) ->
       red_expr S C (expr_binary_op_1 a1 a2 a3) oo -> P S C a1 a2 a3 oo.

Parameter inv_red_expr_expr_binary_op_2
     : forall (S : state) (C : execution_ctx) (a1 : binary_op) 
         (a2 : value) (a3 : specret value) (oo : out)
         (P : state ->
              execution_ctx ->
              binary_op -> value -> specret value -> out -> Prop),
       (red_expr S C (expr_binary_op_2 a1 a2 a3) oo ->
        forall (S0 : state) (C0 : execution_ctx) (exte : ext_expr) (o : out),
        @eq (option out) (out_of_ext_expr (expr_binary_op_2 a1 a2 a3))
          (@Some out oo) ->
        abort oo ->
        not (abort_intercepted_expr (expr_binary_op_2 a1 a2 a3)) ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq ext_expr exte (expr_binary_op_2 a1 a2 a3) ->
        @eq out o oo -> P S C a1 a2 a3 oo) ->
       (red_expr S C (expr_binary_op_2 a1 a2 a3) oo ->
        forall (S0 S1 : state) (C0 : execution_ctx) 
          (op : binary_op) (v1 v2 : value) (o : out),
        red_expr S1 C (expr_binary_op_3 a1 a2 v2) oo ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq binary_op op a1 ->
        @eq value v1 a2 ->
        @eq (specret value) (@ret value S1 v2) a3 ->
        @eq out o oo -> P S C a1 a2 (@ret value S1 v2) oo) ->
       red_expr S C (expr_binary_op_2 a1 a2 a3) oo -> P S C a1 a2 a3 oo.

Parameter inv_red_expr_expr_binary_op_3
     : forall (S : state) (C : execution_ctx) (a1 : binary_op)
         (a2 a3 : value) (oo : out)
         (P : state ->
              execution_ctx -> binary_op -> value -> value -> out -> Prop),
       (red_expr S C (expr_binary_op_3 a1 a2 a3) oo ->
        forall (S0 : state) (C0 : execution_ctx) (exte : ext_expr) (o : out),
        @eq (option out) (out_of_ext_expr (expr_binary_op_3 a1 a2 a3))
          (@Some out oo) ->
        abort oo ->
        not (abort_intercepted_expr (expr_binary_op_3 a1 a2 a3)) ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq ext_expr exte (expr_binary_op_3 a1 a2 a3) ->
        @eq out o oo -> P S C a1 a2 a3 oo) ->
       (red_expr S C (expr_binary_op_3 a1 a2 a3) oo ->
        forall (S0 : state) (C0 : execution_ctx) (v1 v2 : value)
          (y1 : specret (prod value value)) (o : out),
        @red_spec (prod value value) S C
          (spec_convert_twice (spec_to_primitive_auto a2)
             (spec_to_primitive_auto a3)) y1 ->
        red_expr S C (expr_binary_op_add_1 y1) oo ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq binary_op binary_op_add a1 ->
        @eq value v1 a2 ->
        @eq value v2 a3 -> @eq out o oo -> P S C binary_op_add a2 a3 oo) ->
       (red_expr S C (expr_binary_op_3 a1 a2 a3) oo ->
        forall (S0 : state) (C0 : execution_ctx) (op : binary_op)
          (F : JsNumber.number -> JsNumber.number -> JsNumber.number)
          (v1 v2 : value) (y1 : specret (prod value value)) 
          (o : out),
        puremath_op a1 F ->
        @red_spec (prod value value) S C
          (spec_convert_twice (spec_to_number a2) (spec_to_number a3)) y1 ->
        red_expr S C (expr_puremath_op_1 F y1) oo ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq binary_op op a1 ->
        @eq value v1 a2 ->
        @eq value v2 a3 -> @eq out o oo -> P S C a1 a2 a3 oo) ->
       (red_expr S C (expr_binary_op_3 a1 a2 a3) oo ->
        forall (b_unsigned : bool) (S0 : state) (C0 : execution_ctx)
          (op : binary_op) (F : Z -> Z -> Z) (ext : value -> ext_spec)
          (v1 v2 : value) (y1 : specret Z) (o : out),
        shift_op a1 b_unsigned F ->
        @eq (value -> ext_spec) ext
          match b_unsigned return (value -> ext_spec) with
          | true => spec_to_uint32
          | false => spec_to_int32
          end ->
        @red_spec Z S C (ext a2) y1 ->
        red_expr S C (expr_shift_op_1 F y1 a3) oo ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq binary_op op a1 ->
        @eq value v1 a2 ->
        @eq value v2 a3 -> @eq out o oo -> P S C a1 a2 a3 oo) ->
       (red_expr S C (expr_binary_op_3 a1 a2 a3) oo ->
        forall (S0 : state) (C0 : execution_ctx) (v1 v2 : value)
          (op : binary_op) (b_swap b_neg : bool) (o : out),
        inequality_op a1 b_swap b_neg ->
        red_expr S C (expr_inequality_op_1 b_swap b_neg a2 a3) oo ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq binary_op op a1 ->
        @eq value v1 a2 ->
        @eq value v2 a3 -> @eq out o oo -> P S C a1 a2 a3 oo) ->
       (red_expr S C (expr_binary_op_3 a1 a2 a3) oo ->
        forall (S0 : state) (C0 : execution_ctx) (v1 v2 : value) (o : out),
        not (@eq type (type_of a3) type_object) ->
        red_expr S C (spec_error native_error_type) oo ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq binary_op binary_op_instanceof a1 ->
        @eq value v1 a2 ->
        @eq value v2 a3 ->
        @eq out o oo -> P S C binary_op_instanceof a2 a3 oo) ->
       (red_expr S C (expr_binary_op_3 a1 a2 a3) oo ->
        forall (S0 : state) (C0 : execution_ctx) (v1 : value)
          (l : object_loc) (o : out),
        @object_method (option builtin_has_instance) object_has_instance_ S l
          (@None builtin_has_instance) ->
        red_expr S C (spec_error native_error_type) oo ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq binary_op binary_op_instanceof a1 ->
        @eq value v1 a2 ->
        @eq value (value_object l) a3 ->
        @eq out o oo -> P S C binary_op_instanceof a2 (value_object l) oo) ->
       (red_expr S C (expr_binary_op_3 a1 a2 a3) oo ->
        forall (S0 : state) (C0 : execution_ctx) (v1 : value)
          (l : object_loc) (o : out),
        red_expr S C (spec_object_has_instance l a2) oo ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq binary_op binary_op_instanceof a1 ->
        @eq value v1 a2 ->
        @eq value (value_object l) a3 ->
        @eq out o oo -> P S C binary_op_instanceof a2 (value_object l) oo) ->
       (red_expr S C (expr_binary_op_3 a1 a2 a3) oo ->
        forall (S0 : state) (C0 : execution_ctx) (v1 v2 : value) (o : out),
        not (@eq type (type_of a3) type_object) ->
        red_expr S C (spec_error native_error_type) oo ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq binary_op binary_op_in a1 ->
        @eq value v1 a2 ->
        @eq value v2 a3 -> @eq out o oo -> P S C binary_op_in a2 a3 oo) ->
       (red_expr S C (expr_binary_op_3 a1 a2 a3) oo ->
        forall (S0 : state) (C0 : execution_ctx) (v1 : value)
          (l : object_loc) (o1 o : out),
        red_expr S C (spec_to_string a2) o1 ->
        red_expr S C (expr_binary_op_in_1 l o1) oo ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq binary_op binary_op_in a1 ->
        @eq value v1 a2 ->
        @eq value (value_object l) a3 ->
        @eq out o oo -> P S C binary_op_in a2 (value_object l) oo) ->
       (red_expr S C (expr_binary_op_3 a1 a2 a3) oo ->
        forall (S0 : state) (C0 : execution_ctx) (v1 v2 : value) (o : out),
        red_expr S C (spec_equal a2 a3) oo ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq binary_op binary_op_equal a1 ->
        @eq value v1 a2 ->
        @eq value v2 a3 -> @eq out o oo -> P S C binary_op_equal a2 a3 oo) ->
       (red_expr S C (expr_binary_op_3 a1 a2 a3) oo ->
        forall (S0 : state) (C0 : execution_ctx) (v1 v2 : value) (o1 o : out),
        red_expr S C (spec_equal a2 a3) o1 ->
        red_expr S C (expr_binary_op_disequal_1 o1) oo ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq binary_op binary_op_disequal a1 ->
        @eq value v1 a2 ->
        @eq value v2 a3 -> @eq out o oo -> P S C binary_op_disequal a2 a3 oo) ->
       (red_expr S C (expr_binary_op_3 a1 a2 a3) oo ->
        forall (S0 : state) (C0 : execution_ctx) (v1 v2 : value) (b : bool),
        @eq bool b (strict_equality_test a2 a3) ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq binary_op binary_op_strict_equal a1 ->
        @eq value v1 a2 ->
        @eq value v2 a3 ->
        @eq out (out_ter S (res_val (value_prim (prim_bool b)))) oo ->
        P S C binary_op_strict_equal a2 a3
          (out_ter S (res_val (value_prim (prim_bool b))))) ->
       (red_expr S C (expr_binary_op_3 a1 a2 a3) oo ->
        forall (S0 : state) (C0 : execution_ctx) (v1 v2 : value) (b : bool),
        @eq bool b (negb (strict_equality_test a2 a3)) ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq binary_op binary_op_strict_disequal a1 ->
        @eq value v1 a2 ->
        @eq value v2 a3 ->
        @eq out (out_ter S (res_val (value_prim (prim_bool b)))) oo ->
        P S C binary_op_strict_disequal a2 a3
          (out_ter S (res_val (value_prim (prim_bool b))))) ->
       (red_expr S C (expr_binary_op_3 a1 a2 a3) oo ->
        forall (S0 : state) (C0 : execution_ctx) (op : binary_op)
          (F : Z -> Z -> Z) (v1 v2 : value) (y1 : specret Z) 
          (o : out),
        bitwise_op a1 F ->
        @red_spec Z S C (spec_to_int32 a2) y1 ->
        red_expr S C (expr_bitwise_op_1 F y1 a3) oo ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq binary_op op a1 ->
        @eq value v1 a2 ->
        @eq value v2 a3 -> @eq out o oo -> P S C a1 a2 a3 oo) ->
       (red_expr S C (expr_binary_op_3 a1 a2 a3) oo ->
        forall (S0 : state) (C0 : execution_ctx) (v1 v2 : value),
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq binary_op binary_op_coma a1 ->
        @eq value v1 a2 ->
        @eq value v2 a3 ->
        @eq out (out_ter S (res_val a3)) oo ->
        P S C binary_op_coma a2 a3 (out_ter S (res_val a3))) ->
       red_expr S C (expr_binary_op_3 a1 a2 a3) oo -> P S C a1 a2 a3 oo.

Parameter inv_red_expr_expr_binary_op_add_1
     : forall (S : state) (C : execution_ctx)
         (a1 : specret (prod value value)) (oo : out)
         (P : state ->
              execution_ctx -> specret (prod value value) -> out -> Prop),
       (red_expr S C (expr_binary_op_add_1 a1) oo ->
        forall (S0 : state) (C0 : execution_ctx) (exte : ext_expr) (o : out),
        @eq (option out) (out_of_ext_expr (expr_binary_op_add_1 a1))
          (@Some out oo) ->
        abort oo ->
        not (abort_intercepted_expr (expr_binary_op_add_1 a1)) ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq ext_expr exte (expr_binary_op_add_1 a1) ->
        @eq out o oo -> P S C a1 oo) ->
       (red_expr S C (expr_binary_op_add_1 a1) oo ->
        forall (S0 S1 : state) (C0 : execution_ctx) 
          (v1 v2 : value) (y1 : specret (prod value value)) 
          (o : out),
        Logic.or (@eq type (type_of v1) type_string)
          (@eq type (type_of v2) type_string) ->
        @red_spec (prod value value) S1 C
          (spec_convert_twice (spec_to_string v1) (spec_to_string v2)) y1 ->
        red_expr S1 C (expr_binary_op_add_string_1 y1) oo ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq (specret (prod value value))
          (@ret (prod value value) S1 (@pair value value v1 v2)) a1 ->
        @eq out o oo ->
        P S C (@ret (prod value value) S1 (@pair value value v1 v2)) oo) ->
       (red_expr S C (expr_binary_op_add_1 a1) oo ->
        forall (S0 S1 : state) (C0 : execution_ctx) 
          (v1 v2 : value) (y1 : specret (prod value value)) 
          (o : out),
        not
          (Logic.or (@eq type (type_of v1) type_string)
             (@eq type (type_of v2) type_string)) ->
        @red_spec (prod value value) S1 C
          (spec_convert_twice (spec_to_number v1) (spec_to_number v2)) y1 ->
        red_expr S1 C (expr_puremath_op_1 JsNumber.add y1) oo ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq (specret (prod value value))
          (@ret (prod value value) S1 (@pair value value v1 v2)) a1 ->
        @eq out o oo ->
        P S C (@ret (prod value value) S1 (@pair value value v1 v2)) oo) ->
       red_expr S C (expr_binary_op_add_1 a1) oo -> P S C a1 oo.

Parameter inv_red_expr_expr_binary_op_add_string_1
     : forall (S : state) (C : execution_ctx)
         (a1 : specret (prod value value)) (oo : out)
         (P : state ->
              execution_ctx -> specret (prod value value) -> out -> Prop),
       (red_expr S C (expr_binary_op_add_string_1 a1) oo ->
        forall (S0 : state) (C0 : execution_ctx) (exte : ext_expr) (o : out),
        @eq (option out) (out_of_ext_expr (expr_binary_op_add_string_1 a1))
          (@Some out oo) ->
        abort oo ->
        not (abort_intercepted_expr (expr_binary_op_add_string_1 a1)) ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq ext_expr exte (expr_binary_op_add_string_1 a1) ->
        @eq out o oo -> P S C a1 oo) ->
       (red_expr S C (expr_binary_op_add_string_1 a1) oo ->
        forall (S0 S1 : state) (C0 : execution_ctx) (s1 s2 s : string),
        @eq string s (String.append s1 s2) ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq (specret (prod value value))
          (@ret (prod value value) S1
             (@pair value value (value_prim (prim_string s1))
                (value_prim (prim_string s2)))) a1 ->
        @eq out (out_ter S1 (res_val (value_prim (prim_string s)))) oo ->
        P S C
          (@ret (prod value value) S1
             (@pair value value (value_prim (prim_string s1))
                (value_prim (prim_string s2))))
          (out_ter S1 (res_val (value_prim (prim_string s))))) ->
       red_expr S C (expr_binary_op_add_string_1 a1) oo -> P S C a1 oo.

Parameter inv_red_expr_expr_puremath_op_1
     : forall (S : state) (C : execution_ctx)
         (a1 : JsNumber.number -> JsNumber.number -> JsNumber.number)
         (a2 : specret (prod value value)) (oo : out)
         (P : state ->
              execution_ctx ->
              (Fappli_IEEE.binary_float (Zpos (xI (xO (xI (xO (xI xH))))))
                 (Zpos (xO (xO (xO (xO (xO (xO (xO (xO (xO (xO xH))))))))))) ->
               Fappli_IEEE.binary_float (Zpos (xI (xO (xI (xO (xI xH))))))
                 (Zpos (xO (xO (xO (xO (xO (xO (xO (xO (xO (xO xH))))))))))) ->
               Fappli_IEEE.binary_float (Zpos (xI (xO (xI (xO (xI xH))))))
                 (Zpos (xO (xO (xO (xO (xO (xO (xO (xO (xO (xO xH)))))))))))) ->
              specret (prod value value) -> out -> Prop),
       (red_expr S C (expr_puremath_op_1 a1 a2) oo ->
        forall (S0 : state) (C0 : execution_ctx) (exte : ext_expr) (o : out),
        @eq (option out) (out_of_ext_expr (expr_puremath_op_1 a1 a2))
          (@Some out oo) ->
        abort oo ->
        not (abort_intercepted_expr (expr_puremath_op_1 a1 a2)) ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq ext_expr exte (expr_puremath_op_1 a1 a2) ->
        @eq out o oo -> P S C a1 a2 oo) ->
       (red_expr S C (expr_puremath_op_1 a1 a2) oo ->
        forall (S0 S1 : state) (C0 : execution_ctx)
          (F : JsNumber.number -> JsNumber.number -> JsNumber.number)
          (n n1 n2 : JsNumber.number),
        @eq JsNumber.number n (a1 n1 n2) ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq (JsNumber.number -> JsNumber.number -> JsNumber.number) F a1 ->
        @eq (specret (prod value value))
          (@ret (prod value value) S1
             (@pair value value (value_prim (prim_number n1))
                (value_prim (prim_number n2)))) a2 ->
        @eq out (out_ter S1 (res_val (value_prim (prim_number n)))) oo ->
        P S C a1
          (@ret (prod value value) S1
             (@pair value value (value_prim (prim_number n1))
                (value_prim (prim_number n2))))
          (out_ter S1 (res_val (value_prim (prim_number n))))) ->
       red_expr S C (expr_puremath_op_1 a1 a2) oo -> P S C a1 a2 oo.

Parameter inv_red_expr_expr_shift_op_1
     : forall (S : state) (C : execution_ctx) (a1 : Z -> Z -> Z)
         (a2 : specret Z) (a3 : value) (oo : out)
         (P : state ->
              execution_ctx ->
              (Z -> Z -> Z) -> specret Z -> value -> out -> Prop),
       (red_expr S C (expr_shift_op_1 a1 a2 a3) oo ->
        forall (S0 : state) (C0 : execution_ctx) (exte : ext_expr) (o : out),
        @eq (option out) (out_of_ext_expr (expr_shift_op_1 a1 a2 a3))
          (@Some out oo) ->
        abort oo ->
        not (abort_intercepted_expr (expr_shift_op_1 a1 a2 a3)) ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq ext_expr exte (expr_shift_op_1 a1 a2 a3) ->
        @eq out o oo -> P S C a1 a2 a3 oo) ->
       (red_expr S C (expr_shift_op_1 a1 a2 a3) oo ->
        forall (S0 S1 : state) (C0 : execution_ctx) 
          (F : Z -> Z -> Z) (k1 : Z) (v2 : value) (y1 : specret Z) 
          (o : out),
        @red_spec Z S1 C (spec_to_uint32 a3) y1 ->
        red_expr S1 C (expr_shift_op_2 a1 k1 y1) oo ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq (Z -> Z -> Z) F a1 ->
        @eq (specret Z) (@ret Z S1 k1) a2 ->
        @eq value v2 a3 -> @eq out o oo -> P S C a1 (@ret Z S1 k1) a3 oo) ->
       red_expr S C (expr_shift_op_1 a1 a2 a3) oo -> P S C a1 a2 a3 oo.

Parameter inv_red_expr_expr_shift_op_2
     : forall (S : state) (C : execution_ctx) (a1 : Z -> Z -> Z) 
         (a2 : Z) (a3 : specret Z) (oo : out)
         (P : state ->
              execution_ctx -> (Z -> Z -> Z) -> Z -> specret Z -> out -> Prop),
       (red_expr S C (expr_shift_op_2 a1 a2 a3) oo ->
        forall (S0 : state) (C0 : execution_ctx) (exte : ext_expr) (o : out),
        @eq (option out) (out_of_ext_expr (expr_shift_op_2 a1 a2 a3))
          (@Some out oo) ->
        abort oo ->
        not (abort_intercepted_expr (expr_shift_op_2 a1 a2 a3)) ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq ext_expr exte (expr_shift_op_2 a1 a2 a3) ->
        @eq out o oo -> P S C a1 a2 a3 oo) ->
       (red_expr S C (expr_shift_op_2 a1 a2 a3) oo ->
        forall (S0 S1 : state) (C0 : execution_ctx) 
          (k1 k2 : Z) (F : Z -> Z -> Z) (n : JsNumber.number),
        @eq JsNumber.number n
          (JsNumber.of_int (a1 a2 (JsNumber.modulo_32 k2))) ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq (Z -> Z -> Z) F a1 ->
        @eq Z k1 a2 ->
        @eq (specret Z) (@ret Z S1 k2) a3 ->
        @eq out (out_ter S1 (res_val (value_prim (prim_number n)))) oo ->
        P S C a1 a2 (@ret Z S1 k2)
          (out_ter S1 (res_val (value_prim (prim_number n))))) ->
       red_expr S C (expr_shift_op_2 a1 a2 a3) oo -> P S C a1 a2 a3 oo.

Parameter inv_red_expr_expr_inequality_op_1
     : forall (S : state) (C : execution_ctx) (a1 a2 : bool) 
         (a3 a4 : value) (oo : out)
         (P : state ->
              execution_ctx -> bool -> bool -> value -> value -> out -> Prop),
       (red_expr S C (expr_inequality_op_1 a1 a2 a3 a4) oo ->
        forall (S0 : state) (C0 : execution_ctx) (exte : ext_expr) (o : out),
        @eq (option out) (out_of_ext_expr (expr_inequality_op_1 a1 a2 a3 a4))
          (@Some out oo) ->
        abort oo ->
        not (abort_intercepted_expr (expr_inequality_op_1 a1 a2 a3 a4)) ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq ext_expr exte (expr_inequality_op_1 a1 a2 a3 a4) ->
        @eq out o oo -> P S C a1 a2 a3 a4 oo) ->
       (red_expr S C (expr_inequality_op_1 a1 a2 a3 a4) oo ->
        forall (S0 : state) (C0 : execution_ctx) (v1 v2 : value)
          (b_swap b_neg : bool) (y1 : specret (prod value value)) 
          (o : out),
        @red_spec (prod value value) S C
          (spec_convert_twice (spec_to_primitive_auto a3)
             (spec_to_primitive_auto a4)) y1 ->
        red_expr S C (expr_inequality_op_2 a1 a2 y1) oo ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq bool b_swap a1 ->
        @eq bool b_neg a2 ->
        @eq value v1 a3 ->
        @eq value v2 a4 -> @eq out o oo -> P S C a1 a2 a3 a4 oo) ->
       red_expr S C (expr_inequality_op_1 a1 a2 a3 a4) oo ->
       P S C a1 a2 a3 a4 oo.

Parameter inv_red_expr_expr_inequality_op_2
     : forall (S : state) (C : execution_ctx) (a1 a2 : bool)
         (a3 : specret (prod value value)) (oo : out)
         (P : state ->
              execution_ctx ->
              bool -> bool -> specret (prod value value) -> out -> Prop),
       (red_expr S C (expr_inequality_op_2 a1 a2 a3) oo ->
        forall (S0 : state) (C0 : execution_ctx) (exte : ext_expr) (o : out),
        @eq (option out) (out_of_ext_expr (expr_inequality_op_2 a1 a2 a3))
          (@Some out oo) ->
        abort oo ->
        not (abort_intercepted_expr (expr_inequality_op_2 a1 a2 a3)) ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq ext_expr exte (expr_inequality_op_2 a1 a2 a3) ->
        @eq out o oo -> P S C a1 a2 a3 oo) ->
       (red_expr S C (expr_inequality_op_2 a1 a2 a3) oo ->
        forall (S0 S1 : state) (C0 : execution_ctx)
          (w1 w2 wa wb wr wr' : prim) (b_swap b_neg : bool),
        @eq (prod prim prim) (@pair prim prim wa wb)
          match a1 return (prod prim prim) with
          | true => @pair prim prim w2 w1
          | false => @pair prim prim w1 w2
          end ->
        @eq prim wr (inequality_test_primitive wa wb) ->
        @eq prim wr'
          match classicT (@eq prim wr prim_undef) return prim with
          | left _ => prim_bool false
          | right _ =>
              match
                classicT
                  (Logic.and (@eq bool a2 true)
                     (@eq prim wr (prim_bool true))) 
                return prim
              with
              | left _ => prim_bool false
              | right _ =>
                  match
                    classicT
                      (Logic.and (@eq bool a2 true)
                         (@eq prim wr (prim_bool false))) 
                    return prim
                  with
                  | left _ => prim_bool true
                  | right _ => wr
                  end
              end
          end ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq bool b_swap a1 ->
        @eq bool b_neg a2 ->
        @eq (specret (prod value value))
          (@ret (prod value value) S1
             (@pair value value (value_prim w1) (value_prim w2))) a3 ->
        @eq out (out_ter S1 (res_val (value_prim wr'))) oo ->
        P S C a1 a2
          (@ret (prod value value) S1
             (@pair value value (value_prim w1) (value_prim w2)))
          (out_ter S1 (res_val (value_prim wr')))) ->
       red_expr S C (expr_inequality_op_2 a1 a2 a3) oo -> P S C a1 a2 a3 oo.

Parameter inv_red_expr_expr_binary_op_in_1
     : forall (S : state) (C : execution_ctx) (a1 : object_loc) 
         (a2 oo : out)
         (P : state -> execution_ctx -> object_loc -> out -> out -> Prop),
       (red_expr S C (expr_binary_op_in_1 a1 a2) oo ->
        forall (S0 : state) (C0 : execution_ctx) (exte : ext_expr) (o : out),
        @eq (option out) (out_of_ext_expr (expr_binary_op_in_1 a1 a2))
          (@Some out oo) ->
        abort oo ->
        not (abort_intercepted_expr (expr_binary_op_in_1 a1 a2)) ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq ext_expr exte (expr_binary_op_in_1 a1 a2) ->
        @eq out o oo -> P S C a1 a2 oo) ->
       (red_expr S C (expr_binary_op_in_1 a1 a2) oo ->
        forall (S0 S1 : state) (C0 : execution_ctx) 
          (l : object_loc) (x : prop_name) (o : out),
        red_expr S1 C (spec_object_has_prop a1 x) oo ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq object_loc l a1 ->
        @eq out (out_ter S1 (res_val (value_prim (prim_string x)))) a2 ->
        @eq out o oo ->
        P S C a1 (out_ter S1 (res_val (value_prim (prim_string x)))) oo) ->
       red_expr S C (expr_binary_op_in_1 a1 a2) oo -> P S C a1 a2 oo.

Parameter inv_red_expr_expr_binary_op_disequal_1
     : forall (S : state) (C : execution_ctx) (a1 oo : out)
         (P : state -> execution_ctx -> out -> out -> Prop),
       (red_expr S C (expr_binary_op_disequal_1 a1) oo ->
        forall (S0 : state) (C0 : execution_ctx) (exte : ext_expr) (o : out),
        @eq (option out) (out_of_ext_expr (expr_binary_op_disequal_1 a1))
          (@Some out oo) ->
        abort oo ->
        not (abort_intercepted_expr (expr_binary_op_disequal_1 a1)) ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq ext_expr exte (expr_binary_op_disequal_1 a1) ->
        @eq out o oo -> P S C a1 oo) ->
       (red_expr S C (expr_binary_op_disequal_1 a1) oo ->
        forall (S0 S1 : state) (C0 : execution_ctx) (b : bool),
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq out (out_ter S1 (res_val (value_prim (prim_bool b)))) a1 ->
        @eq out (out_ter S1 (res_val (value_prim (prim_bool (negb b))))) oo ->
        P S C (out_ter S1 (res_val (value_prim (prim_bool b))))
          (out_ter S1 (res_val (value_prim (prim_bool (negb b)))))) ->
       red_expr S C (expr_binary_op_disequal_1 a1) oo -> P S C a1 oo.

Parameter inv_red_expr_spec_equal
     : forall (S : state) (C : execution_ctx) (a1 a2 : value) 
         (oo : out)
         (P : state -> execution_ctx -> value -> value -> out -> Prop),
       (red_expr S C (spec_equal a1 a2) oo ->
        forall (S0 : state) (C0 : execution_ctx) (exte : ext_expr) (o : out),
        @eq (option out) (out_of_ext_expr (spec_equal a1 a2)) (@Some out oo) ->
        abort oo ->
        not (abort_intercepted_expr (spec_equal a1 a2)) ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq ext_expr exte (spec_equal a1 a2) ->
        @eq out o oo -> P S C a1 a2 oo) ->
       (red_expr S C (spec_equal a1 a2) oo ->
        forall (S0 : state) (C0 : execution_ctx) (v1 v2 : value)
          (ty1 ty2 : type) (o : out),
        @eq type ty1 (type_of a1) ->
        @eq type ty2 (type_of a2) ->
        red_expr S C (spec_equal_1 ty1 ty2 a1 a2) oo ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq value v1 a1 -> @eq value v2 a2 -> @eq out o oo -> P S C a1 a2 oo) ->
       red_expr S C (spec_equal a1 a2) oo -> P S C a1 a2 oo.

Parameter inv_red_expr_spec_equal_1
     : forall (S : state) (C : execution_ctx) (a1 a2 : type) 
         (a3 a4 : value) (oo : out)
         (P : state ->
              execution_ctx -> type -> type -> value -> value -> out -> Prop),
       (red_expr S C (spec_equal_1 a1 a2 a3 a4) oo ->
        forall (S0 : state) (C0 : execution_ctx) (exte : ext_expr) (o : out),
        @eq (option out) (out_of_ext_expr (spec_equal_1 a1 a2 a3 a4))
          (@Some out oo) ->
        abort oo ->
        not (abort_intercepted_expr (spec_equal_1 a1 a2 a3 a4)) ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq ext_expr exte (spec_equal_1 a1 a2 a3 a4) ->
        @eq out o oo -> P S C a1 a2 a3 a4 oo) ->
       (red_expr S C (spec_equal_1 a1 a2 a3 a4) oo ->
        forall (S0 : state) (C0 : execution_ctx) (v1 v2 : value) 
          (ty : type) (b : bool),
        @eq bool b (equality_test_for_same_type a2 a3 a4) ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq type ty a1 ->
        @eq type a1 a2 ->
        @eq value v1 a3 ->
        @eq value v2 a4 ->
        @eq out (out_ter S (res_val (value_prim (prim_bool b)))) oo ->
        P S C a2 a2 a3 a4 (out_ter S (res_val (value_prim (prim_bool b))))) ->
       (red_expr S C (spec_equal_1 a1 a2 a3 a4) oo ->
        forall (S0 : state) (C0 : execution_ctx) (v1 v2 : value)
          (ty1 ty2 : type) (ext : ext_expr) (o : out),
        @eq ext_expr ext
          match
            classicT
              (Logic.and (@eq type a1 type_null) (@eq type a2 type_undef))
            return ext_expr
          with
          | left _ => spec_equal_2 true
          | right _ =>
              match
                classicT
                  (Logic.and (@eq type a1 type_undef) (@eq type a2 type_null))
                return ext_expr
              with
              | left _ => spec_equal_2 true
              | right _ =>
                  match
                    classicT
                      (Logic.and (@eq type a1 type_number)
                         (@eq type a2 type_string)) 
                    return ext_expr
                  with
                  | left _ => spec_equal_3 a3 spec_to_number a4
                  | right _ =>
                      match
                        classicT
                          (Logic.and (@eq type a1 type_string)
                             (@eq type a2 type_number)) 
                        return ext_expr
                      with
                      | left _ => spec_equal_3 a4 spec_to_number a3
                      | right _ =>
                          match
                            classicT (@eq type a1 type_bool) return ext_expr
                          with
                          | left _ => spec_equal_3 a4 spec_to_number a3
                          | right _ =>
                              match
                                classicT (@eq type a2 type_bool)
                                return ext_expr
                              with
                              | left _ => spec_equal_3 a3 spec_to_number a4
                              | right _ =>
                                  match
                                    classicT
                                      (Logic.and
                                         (Logic.or 
                                            (@eq type a1 type_string)
                                            (@eq type a1 type_number))
                                         (@eq type a2 type_object))
                                    return ext_expr
                                  with
                                  | left _ =>
                                      spec_equal_3 a3 spec_to_primitive_auto
                                        a4
                                  | right _ =>
                                      match
                                        classicT
                                          (Logic.and
                                             (@eq type a1 type_object)
                                             (Logic.or
                                                (@eq type a2 type_string)
                                                (@eq type a2 type_number)))
                                        return ext_expr
                                      with
                                      | left _ =>
                                          spec_equal_3 a4
                                            spec_to_primitive_auto a3
                                      | right _ => spec_equal_2 false
                                      end
                                  end
                              end
                          end
                      end
                  end
              end
          end ->
        red_expr S C ext oo ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq type ty1 a1 ->
        @eq type ty2 a2 ->
        @eq value v1 a3 ->
        @eq value v2 a4 -> @eq out o oo -> P S C a1 a2 a3 a4 oo) ->
       red_expr S C (spec_equal_1 a1 a2 a3 a4) oo -> P S C a1 a2 a3 a4 oo.

Parameter inv_red_expr_spec_equal_2
     : forall (S : state) (C : execution_ctx) (a1 : bool) 
         (oo : out) (P : state -> execution_ctx -> bool -> out -> Prop),
       (red_expr S C (spec_equal_2 a1) oo ->
        forall (S0 : state) (C0 : execution_ctx) (exte : ext_expr) (o : out),
        @eq (option out) (out_of_ext_expr (spec_equal_2 a1)) (@Some out oo) ->
        abort oo ->
        not (abort_intercepted_expr (spec_equal_2 a1)) ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq ext_expr exte (spec_equal_2 a1) -> @eq out o oo -> P S C a1 oo) ->
       (red_expr S C (spec_equal_2 a1) oo ->
        forall (S0 : state) (C0 : execution_ctx) (b : bool),
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq bool b a1 ->
        @eq out (out_ter S (res_val (value_prim (prim_bool a1)))) oo ->
        P S C a1 (out_ter S (res_val (value_prim (prim_bool a1))))) ->
       red_expr S C (spec_equal_2 a1) oo -> P S C a1 oo.

Parameter inv_red_expr_spec_equal_3
     : forall (S : state) (C : execution_ctx) (a1 : value)
         (a2 : value -> ext_expr) (a3 : value) (oo : out)
         (P : state ->
              execution_ctx ->
              value -> (value -> ext_expr) -> value -> out -> Prop),
       (red_expr S C (spec_equal_3 a1 a2 a3) oo ->
        forall (S0 : state) (C0 : execution_ctx) (exte : ext_expr) (o : out),
        @eq (option out) (out_of_ext_expr (spec_equal_3 a1 a2 a3))
          (@Some out oo) ->
        abort oo ->
        not (abort_intercepted_expr (spec_equal_3 a1 a2 a3)) ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq ext_expr exte (spec_equal_3 a1 a2 a3) ->
        @eq out o oo -> P S C a1 a2 a3 oo) ->
       (red_expr S C (spec_equal_3 a1 a2 a3) oo ->
        forall (S0 : state) (C0 : execution_ctx) (v1 v2 : value)
          (K : value -> ext_expr) (o2 o : out),
        red_expr S C (a2 a3) o2 ->
        red_expr S C (spec_equal_4 a1 o2) oo ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq value v1 a1 ->
        @eq (value -> ext_expr) K a2 ->
        @eq value v2 a3 -> @eq out o oo -> P S C a1 a2 a3 oo) ->
       red_expr S C (spec_equal_3 a1 a2 a3) oo -> P S C a1 a2 a3 oo.

Parameter inv_red_expr_spec_equal_4
     : forall (S : state) (C : execution_ctx) (a1 : value) 
         (a2 oo : out)
         (P : state -> execution_ctx -> value -> out -> out -> Prop),
       (red_expr S C (spec_equal_4 a1 a2) oo ->
        forall (S0 : state) (C0 : execution_ctx) (exte : ext_expr) (o : out),
        @eq (option out) (out_of_ext_expr (spec_equal_4 a1 a2))
          (@Some out oo) ->
        abort oo ->
        not (abort_intercepted_expr (spec_equal_4 a1 a2)) ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq ext_expr exte (spec_equal_4 a1 a2) ->
        @eq out o oo -> P S C a1 a2 oo) ->
       (red_expr S C (spec_equal_4 a1 a2) oo ->
        forall (S0 S1 : state) (C0 : execution_ctx) (v1 v2 : value) (o : out),
        red_expr S1 C (spec_equal a1 v2) oo ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq value v1 a1 ->
        @eq out (out_ter S1 (res_val v2)) a2 ->
        @eq out o oo -> P S C a1 (out_ter S1 (res_val v2)) oo) ->
       red_expr S C (spec_equal_4 a1 a2) oo -> P S C a1 a2 oo.

Parameter inv_red_expr_expr_bitwise_op_1
     : forall (S : state) (C : execution_ctx) (a1 : Z -> Z -> Z)
         (a2 : specret Z) (a3 : value) (oo : out)
         (P : state ->
              execution_ctx ->
              (Z -> Z -> Z) -> specret Z -> value -> out -> Prop),
       (red_expr S C (expr_bitwise_op_1 a1 a2 a3) oo ->
        forall (S0 : state) (C0 : execution_ctx) (exte : ext_expr) (o : out),
        @eq (option out) (out_of_ext_expr (expr_bitwise_op_1 a1 a2 a3))
          (@Some out oo) ->
        abort oo ->
        not (abort_intercepted_expr (expr_bitwise_op_1 a1 a2 a3)) ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq ext_expr exte (expr_bitwise_op_1 a1 a2 a3) ->
        @eq out o oo -> P S C a1 a2 a3 oo) ->
       (red_expr S C (expr_bitwise_op_1 a1 a2 a3) oo ->
        forall (S0 S1 : state) (C0 : execution_ctx) 
          (F : Z -> Z -> Z) (k1 : Z) (v2 : value) (y1 : specret Z) 
          (o : out),
        @red_spec Z S1 C (spec_to_int32 a3) y1 ->
        red_expr S1 C (expr_bitwise_op_2 a1 k1 y1) oo ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq (Z -> Z -> Z) F a1 ->
        @eq (specret Z) (@ret Z S1 k1) a2 ->
        @eq value v2 a3 -> @eq out o oo -> P S C a1 (@ret Z S1 k1) a3 oo) ->
       red_expr S C (expr_bitwise_op_1 a1 a2 a3) oo -> P S C a1 a2 a3 oo.

Parameter inv_red_expr_expr_bitwise_op_2
     : forall (S : state) (C : execution_ctx) (a1 : Z -> Z -> Z) 
         (a2 : Z) (a3 : specret Z) (oo : out)
         (P : state ->
              execution_ctx -> (Z -> Z -> Z) -> Z -> specret Z -> out -> Prop),
       (red_expr S C (expr_bitwise_op_2 a1 a2 a3) oo ->
        forall (S0 : state) (C0 : execution_ctx) (exte : ext_expr) (o : out),
        @eq (option out) (out_of_ext_expr (expr_bitwise_op_2 a1 a2 a3))
          (@Some out oo) ->
        abort oo ->
        not (abort_intercepted_expr (expr_bitwise_op_2 a1 a2 a3)) ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq ext_expr exte (expr_bitwise_op_2 a1 a2 a3) ->
        @eq out o oo -> P S C a1 a2 a3 oo) ->
       (red_expr S C (expr_bitwise_op_2 a1 a2 a3) oo ->
        forall (S0 S1 : state) (C0 : execution_ctx) 
          (F : Z -> Z -> Z) (k1 k2 : Z) (n : JsNumber.number),
        @eq JsNumber.number n (JsNumber.of_int (a1 a2 k2)) ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq (Z -> Z -> Z) F a1 ->
        @eq Z k1 a2 ->
        @eq (specret Z) (@ret Z S1 k2) a3 ->
        @eq out (out_ter S1 (res_val (value_prim (prim_number n)))) oo ->
        P S C a1 a2 (@ret Z S1 k2)
          (out_ter S1 (res_val (value_prim (prim_number n))))) ->
       red_expr S C (expr_bitwise_op_2 a1 a2 a3) oo -> P S C a1 a2 a3 oo.

Parameter inv_red_expr_expr_lazy_op_1
     : forall (S : state) (C : execution_ctx) (a1 : bool)
         (a2 : specret value) (a3 : expr) (oo : out)
         (P : state ->
              execution_ctx -> bool -> specret value -> expr -> out -> Prop),
       (red_expr S C (expr_lazy_op_1 a1 a2 a3) oo ->
        forall (S0 : state) (C0 : execution_ctx) (exte : ext_expr) (o : out),
        @eq (option out) (out_of_ext_expr (expr_lazy_op_1 a1 a2 a3))
          (@Some out oo) ->
        abort oo ->
        not (abort_intercepted_expr (expr_lazy_op_1 a1 a2 a3)) ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq ext_expr exte (expr_lazy_op_1 a1 a2 a3) ->
        @eq out o oo -> P S C a1 a2 a3 oo) ->
       (red_expr S C (expr_lazy_op_1 a1 a2 a3) oo ->
        forall (S0 S1 : state) (C0 : execution_ctx) 
          (b_ret : bool) (e2 : expr) (v1 : value) (o1 o : out),
        red_expr S1 C (spec_to_boolean v1) o1 ->
        red_expr S1 C (expr_lazy_op_2 a1 v1 o1 a3) oo ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq bool b_ret a1 ->
        @eq (specret value) (@ret value S1 v1) a2 ->
        @eq expr e2 a3 -> @eq out o oo -> P S C a1 (@ret value S1 v1) a3 oo) ->
       red_expr S C (expr_lazy_op_1 a1 a2 a3) oo -> P S C a1 a2 a3 oo.

Parameter inv_red_expr_expr_lazy_op_2
     : forall (S : state) (C : execution_ctx) (a1 : bool) 
         (a2 : value) (a3 : out) (a4 : expr) (oo : out)
         (P : state ->
              execution_ctx -> bool -> value -> out -> expr -> out -> Prop),
       (red_expr S C (expr_lazy_op_2 a1 a2 a3 a4) oo ->
        forall (S0 : state) (C0 : execution_ctx) (exte : ext_expr) (o : out),
        @eq (option out) (out_of_ext_expr (expr_lazy_op_2 a1 a2 a3 a4))
          (@Some out oo) ->
        abort oo ->
        not (abort_intercepted_expr (expr_lazy_op_2 a1 a2 a3 a4)) ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq ext_expr exte (expr_lazy_op_2 a1 a2 a3 a4) ->
        @eq out o oo -> P S C a1 a2 a3 a4 oo) ->
       (red_expr S C (expr_lazy_op_2 a1 a2 a3 a4) oo ->
        forall (S0 S1 : state) (C0 : execution_ctx) 
          (b_ret b1 : bool) (e2 : expr) (v1 : value),
        @eq bool b1 a1 ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq bool b_ret a1 ->
        @eq value v1 a2 ->
        @eq out (out_ter S1 (res_val (value_prim (prim_bool b1)))) a3 ->
        @eq expr e2 a4 ->
        @eq out (out_ter S1 (res_val a2)) oo ->
        P S C a1 a2 (out_ter S1 (res_val (value_prim (prim_bool b1)))) a4
          (out_ter S1 (res_val a2))) ->
       (red_expr S C (expr_lazy_op_2 a1 a2 a3 a4) oo ->
        forall (S0 S1 : state) (C0 : execution_ctx) 
          (v1 : value) (b_ret b1 : bool) (e2 : expr) 
          (y1 : specret value) (o : out),
        not (@eq bool b1 a1) ->
        @red_spec value S1 C (spec_expr_get_value a4) y1 ->
        red_expr S1 C (expr_lazy_op_2_1 y1) oo ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq bool b_ret a1 ->
        @eq value v1 a2 ->
        @eq out (out_ter S1 (res_val (value_prim (prim_bool b1)))) a3 ->
        @eq expr e2 a4 ->
        @eq out o oo ->
        P S C a1 a2 (out_ter S1 (res_val (value_prim (prim_bool b1)))) a4 oo) ->
       red_expr S C (expr_lazy_op_2 a1 a2 a3 a4) oo -> P S C a1 a2 a3 a4 oo.

Parameter inv_red_expr_expr_lazy_op_2_1
     : forall (S : state) (C : execution_ctx) (a1 : specret value) 
         (oo : out)
         (P : state -> execution_ctx -> specret value -> out -> Prop),
       (red_expr S C (expr_lazy_op_2_1 a1) oo ->
        forall (S0 : state) (C0 : execution_ctx) (exte : ext_expr) (o : out),
        @eq (option out) (out_of_ext_expr (expr_lazy_op_2_1 a1))
          (@Some out oo) ->
        abort oo ->
        not (abort_intercepted_expr (expr_lazy_op_2_1 a1)) ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq ext_expr exte (expr_lazy_op_2_1 a1) ->
        @eq out o oo -> P S C a1 oo) ->
       (red_expr S C (expr_lazy_op_2_1 a1) oo ->
        forall (S0 S1 : state) (C0 : execution_ctx) (v : value),
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq (specret value) (@ret value S1 v) a1 ->
        @eq out (out_ter S1 (res_val v)) oo ->
        P S C (@ret value S1 v) (out_ter S1 (res_val v))) ->
       red_expr S C (expr_lazy_op_2_1 a1) oo -> P S C a1 oo.

Parameter inv_red_expr_expr_assign_1
     : forall (S : state) (C : execution_ctx) (a1 : out)
         (a2 : option binary_op) (a3 : expr) (oo : out)
         (P : state ->
              execution_ctx -> out -> option binary_op -> expr -> out -> Prop),
       (red_expr S C (expr_assign_1 a1 a2 a3) oo ->
        forall (S0 : state) (C0 : execution_ctx) (exte : ext_expr) (o : out),
        @eq (option out) (out_of_ext_expr (expr_assign_1 a1 a2 a3))
          (@Some out oo) ->
        abort oo ->
        not (abort_intercepted_expr (expr_assign_1 a1 a2 a3)) ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq ext_expr exte (expr_assign_1 a1 a2 a3) ->
        @eq out o oo -> P S C a1 a2 a3 oo) ->
       (red_expr S C (expr_assign_1 a1 a2 a3) oo ->
        forall (S0 S1 : state) (C0 : execution_ctx) 
          (rv : resvalue) (e2 : expr) (y1 : specret value) 
          (o : out),
        @red_spec value S1 C (spec_expr_get_value a3) y1 ->
        red_expr S1 C (expr_assign_4 (res_normal rv) y1) oo ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq out (out_ter S1 (res_normal rv)) a1 ->
        @eq (option binary_op) (@None binary_op) a2 ->
        @eq expr e2 a3 ->
        @eq out o oo ->
        P S C (out_ter S1 (res_normal rv)) (@None binary_op) a3 oo) ->
       (red_expr S C (expr_assign_1 a1 a2 a3) oo ->
        forall (S0 S1 : state) (C0 : execution_ctx) 
          (rv : resvalue) (op : binary_op) (e2 : expr) 
          (y1 : specret value) (o : out),
        @red_spec value S1 C (spec_get_value rv) y1 ->
        red_expr S1 C (expr_assign_2 (res_normal rv) y1 op a3) oo ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq out (out_ter S1 (res_normal rv)) a1 ->
        @eq (option binary_op) (@Some binary_op op) a2 ->
        @eq expr e2 a3 ->
        @eq out o oo ->
        P S C (out_ter S1 (res_normal rv)) (@Some binary_op op) a3 oo) ->
       red_expr S C (expr_assign_1 a1 a2 a3) oo -> P S C a1 a2 a3 oo.

Parameter inv_red_expr_expr_assign_2
     : forall (S : state) (C : execution_ctx) (a1 : res) 
         (a2 : specret value) (a3 : binary_op) (a4 : expr) 
         (oo : out)
         (P : state ->
              execution_ctx ->
              res -> specret value -> binary_op -> expr -> out -> Prop),
       (red_expr S C (expr_assign_2 a1 a2 a3 a4) oo ->
        forall (S0 : state) (C0 : execution_ctx) (exte : ext_expr) (o : out),
        @eq (option out) (out_of_ext_expr (expr_assign_2 a1 a2 a3 a4))
          (@Some out oo) ->
        abort oo ->
        not (abort_intercepted_expr (expr_assign_2 a1 a2 a3 a4)) ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq ext_expr exte (expr_assign_2 a1 a2 a3 a4) ->
        @eq out o oo -> P S C a1 a2 a3 a4 oo) ->
       (red_expr S C (expr_assign_2 a1 a2 a3 a4) oo ->
        forall (S0 S1 : state) (C0 : execution_ctx) 
          (rv : resvalue) (op : binary_op) (v1 : value) 
          (e2 : expr) (y1 : specret value) (o : out),
        @red_spec value S1 C (spec_expr_get_value a4) y1 ->
        red_expr S1 C (expr_assign_3 (res_normal rv) v1 a3 y1) oo ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq res (res_normal rv) a1 ->
        @eq (specret value) (@ret value S1 v1) a2 ->
        @eq binary_op op a3 ->
        @eq expr e2 a4 ->
        @eq out o oo -> P S C (res_normal rv) (@ret value S1 v1) a3 a4 oo) ->
       red_expr S C (expr_assign_2 a1 a2 a3 a4) oo -> P S C a1 a2 a3 a4 oo.

Parameter inv_red_expr_expr_assign_3
     : forall (S : state) (C : execution_ctx) (a1 : res) 
         (a2 : value) (a3 : binary_op) (a4 : specret value) 
         (oo : out)
         (P : state ->
              execution_ctx ->
              res -> value -> binary_op -> specret value -> out -> Prop),
       (red_expr S C (expr_assign_3 a1 a2 a3 a4) oo ->
        forall (S0 : state) (C0 : execution_ctx) (exte : ext_expr) (o : out),
        @eq (option out) (out_of_ext_expr (expr_assign_3 a1 a2 a3 a4))
          (@Some out oo) ->
        abort oo ->
        not (abort_intercepted_expr (expr_assign_3 a1 a2 a3 a4)) ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq ext_expr exte (expr_assign_3 a1 a2 a3 a4) ->
        @eq out o oo -> P S C a1 a2 a3 a4 oo) ->
       (red_expr S C (expr_assign_3 a1 a2 a3 a4) oo ->
        forall (S0 S1 : state) (C0 : execution_ctx) 
          (rv : resvalue) (op : binary_op) (v1 v2 : value) 
          (o1 o : out),
        red_expr S1 C (expr_binary_op_3 a3 a2 v2) o1 ->
        red_expr S1 C (expr_assign_3' (res_normal rv) o1) oo ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq res (res_normal rv) a1 ->
        @eq value v1 a2 ->
        @eq binary_op op a3 ->
        @eq (specret value) (@ret value S1 v2) a4 ->
        @eq out o oo -> P S C (res_normal rv) a2 a3 (@ret value S1 v2) oo) ->
       red_expr S C (expr_assign_3 a1 a2 a3 a4) oo -> P S C a1 a2 a3 a4 oo.

Parameter inv_red_expr_expr_assign_3'
     : forall (S : state) (C : execution_ctx) (a1 : res) 
         (a2 oo : out)
         (P : state -> execution_ctx -> res -> out -> out -> Prop),
       (red_expr S C (expr_assign_3' a1 a2) oo ->
        forall (S0 : state) (C0 : execution_ctx) (exte : ext_expr) (o : out),
        @eq (option out) (out_of_ext_expr (expr_assign_3' a1 a2))
          (@Some out oo) ->
        abort oo ->
        not (abort_intercepted_expr (expr_assign_3' a1 a2)) ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq ext_expr exte (expr_assign_3' a1 a2) ->
        @eq out o oo -> P S C a1 a2 oo) ->
       (red_expr S C (expr_assign_3' a1 a2) oo ->
        forall (S0 S1 : state) (C0 : execution_ctx) 
          (v : value) (rv : resvalue) (o : out),
        red_expr S1 C (expr_assign_4 (res_normal rv) (@ret value S1 v)) oo ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq res (res_normal rv) a1 ->
        @eq out (out_ter S1 (res_val v)) a2 ->
        @eq out o oo -> P S C (res_normal rv) (out_ter S1 (res_val v)) oo) ->
       red_expr S C (expr_assign_3' a1 a2) oo -> P S C a1 a2 oo.

Parameter inv_red_expr_expr_assign_4
     : forall (S : state) (C : execution_ctx) (a1 : res) 
         (a2 : specret value) (oo : out)
         (P : state -> execution_ctx -> res -> specret value -> out -> Prop),
       (red_expr S C (expr_assign_4 a1 a2) oo ->
        forall (S0 : state) (C0 : execution_ctx) (exte : ext_expr) (o : out),
        @eq (option out) (out_of_ext_expr (expr_assign_4 a1 a2))
          (@Some out oo) ->
        abort oo ->
        not (abort_intercepted_expr (expr_assign_4 a1 a2)) ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq ext_expr exte (expr_assign_4 a1 a2) ->
        @eq out o oo -> P S C a1 a2 oo) ->
       (red_expr S C (expr_assign_4 a1 a2) oo ->
        forall (S0 S1 : state) (C0 : execution_ctx) 
          (rv : resvalue) (v : value) (o1 o : out),
        red_expr S1 C (spec_put_value rv v) o1 ->
        red_expr S1 C (expr_assign_5 v o1) oo ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq res (res_normal rv) a1 ->
        @eq (specret value) (@ret value S1 v) a2 ->
        @eq out o oo -> P S C (res_normal rv) (@ret value S1 v) oo) ->
       red_expr S C (expr_assign_4 a1 a2) oo -> P S C a1 a2 oo.

Parameter inv_red_expr_expr_assign_5
     : forall (S : state) (C : execution_ctx) (a1 : value) 
         (a2 oo : out)
         (P : state -> execution_ctx -> value -> out -> out -> Prop),
       (red_expr S C (expr_assign_5 a1 a2) oo ->
        forall (S0 : state) (C0 : execution_ctx) (exte : ext_expr) (o : out),
        @eq (option out) (out_of_ext_expr (expr_assign_5 a1 a2))
          (@Some out oo) ->
        abort oo ->
        not (abort_intercepted_expr (expr_assign_5 a1 a2)) ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq ext_expr exte (expr_assign_5 a1 a2) ->
        @eq out o oo -> P S C a1 a2 oo) ->
       (red_expr S C (expr_assign_5 a1 a2) oo ->
        forall (S0 S1 : state) (C0 : execution_ctx) 
          (rv' : resvalue) (v : value),
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq value v a1 ->
        @eq out (out_ter S1 (res_normal rv')) a2 ->
        @eq out (out_ter S1 (res_val a1)) oo ->
        P S C a1 (out_ter S1 (res_normal rv')) (out_ter S1 (res_val a1))) ->
       red_expr S C (expr_assign_5 a1 a2) oo -> P S C a1 a2 oo.

Parameter inv_red_expr_spec_to_primitive
     : forall (S : state) (C : execution_ctx) (a1 : value)
         (a2 : option preftype) (oo : out)
         (P : state ->
              execution_ctx -> value -> option preftype -> out -> Prop),
       (red_expr S C (spec_to_primitive a1 a2) oo ->
        forall (S0 : state) (C0 : execution_ctx) (exte : ext_expr) (o : out),
        @eq (option out) (out_of_ext_expr (spec_to_primitive a1 a2))
          (@Some out oo) ->
        abort oo ->
        not (abort_intercepted_expr (spec_to_primitive a1 a2)) ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq ext_expr exte (spec_to_primitive a1 a2) ->
        @eq out o oo -> P S C a1 a2 oo) ->
       (red_expr S C (spec_to_primitive a1 a2) oo ->
        forall (S0 : state) (C0 : execution_ctx) (w : prim)
          (prefo : option preftype),
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq value (value_prim w) a1 ->
        @eq (option preftype) prefo a2 ->
        @eq out (out_ter S (res_val (value_prim w))) oo ->
        P S C (value_prim w) a2 (out_ter S (res_val (value_prim w)))) ->
       (red_expr S C (spec_to_primitive a1 a2) oo ->
        forall (S0 : state) (C0 : execution_ctx) (l : object_loc)
          (prefo : option preftype) (o : out),
        red_expr S C (spec_object_default_value l a2) oo ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq value (value_object l) a1 ->
        @eq (option preftype) prefo a2 ->
        @eq out o oo -> P S C (value_object l) a2 oo) ->
       red_expr S C (spec_to_primitive a1 a2) oo -> P S C a1 a2 oo.

Parameter inv_red_expr_spec_to_boolean
     : forall (S : state) (C : execution_ctx) (a1 : value) 
         (oo : out) (P : state -> execution_ctx -> value -> out -> Prop),
       (red_expr S C (spec_to_boolean a1) oo ->
        forall (S0 : state) (C0 : execution_ctx) (exte : ext_expr) (o : out),
        @eq (option out) (out_of_ext_expr (spec_to_boolean a1))
          (@Some out oo) ->
        abort oo ->
        not (abort_intercepted_expr (spec_to_boolean a1)) ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq ext_expr exte (spec_to_boolean a1) -> @eq out o oo -> P S C a1 oo) ->
       (red_expr S C (spec_to_boolean a1) oo ->
        forall (S0 : state) (C0 : execution_ctx) (v : value) (b : bool),
        @eq bool b (convert_value_to_boolean a1) ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq value v a1 ->
        @eq out (out_ter S (res_val (value_prim (prim_bool b)))) oo ->
        P S C a1 (out_ter S (res_val (value_prim (prim_bool b))))) ->
       red_expr S C (spec_to_boolean a1) oo -> P S C a1 oo.

Parameter inv_red_expr_spec_to_number
     : forall (S : state) (C : execution_ctx) (a1 : value) 
         (oo : out) (P : state -> execution_ctx -> value -> out -> Prop),
       (red_expr S C (spec_to_number a1) oo ->
        forall (S0 : state) (C0 : execution_ctx) (exte : ext_expr) (o : out),
        @eq (option out) (out_of_ext_expr (spec_to_number a1)) (@Some out oo) ->
        abort oo ->
        not (abort_intercepted_expr (spec_to_number a1)) ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq ext_expr exte (spec_to_number a1) -> @eq out o oo -> P S C a1 oo) ->
       (red_expr S C (spec_to_number a1) oo ->
        forall (S0 : state) (C0 : execution_ctx) (w : prim)
          (n : JsNumber.number),
        @eq JsNumber.number n (convert_prim_to_number w) ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq value (value_prim w) a1 ->
        @eq out (out_ter S (res_val (value_prim (prim_number n)))) oo ->
        P S C (value_prim w)
          (out_ter S (res_val (value_prim (prim_number n))))) ->
       (red_expr S C (spec_to_number a1) oo ->
        forall (S0 : state) (C0 : execution_ctx) (l : object_loc)
          (o1 o : out),
        red_expr S C
          (spec_to_primitive (value_object l)
             (@Some preftype preftype_number)) o1 ->
        red_expr S C (spec_to_number_1 o1) oo ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq value (value_object l) a1 ->
        @eq out o oo -> P S C (value_object l) oo) ->
       red_expr S C (spec_to_number a1) oo -> P S C a1 oo.

Parameter inv_red_expr_spec_to_number_1
     : forall (S : state) (C : execution_ctx) (a1 oo : out)
         (P : state -> execution_ctx -> out -> out -> Prop),
       (red_expr S C (spec_to_number_1 a1) oo ->
        forall (S0 : state) (C0 : execution_ctx) (exte : ext_expr) (o : out),
        @eq (option out) (out_of_ext_expr (spec_to_number_1 a1))
          (@Some out oo) ->
        abort oo ->
        not (abort_intercepted_expr (spec_to_number_1 a1)) ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq ext_expr exte (spec_to_number_1 a1) ->
        @eq out o oo -> P S C a1 oo) ->
       (red_expr S C (spec_to_number_1 a1) oo ->
        forall (S0 S1 : state) (C0 : execution_ctx) 
          (w : prim) (n : JsNumber.number),
        @eq JsNumber.number n (convert_prim_to_number w) ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq out (out_ter S1 (res_val (value_prim w))) a1 ->
        @eq out (out_ter S1 (res_val (value_prim (prim_number n)))) oo ->
        P S C (out_ter S1 (res_val (value_prim w)))
          (out_ter S1 (res_val (value_prim (prim_number n))))) ->
       red_expr S C (spec_to_number_1 a1) oo -> P S C a1 oo.

Parameter inv_red_expr_spec_to_integer
     : forall (S : state) (C : execution_ctx) (a1 : value) 
         (oo : out) (P : state -> execution_ctx -> value -> out -> Prop),
       (red_expr S C (spec_to_integer a1) oo ->
        forall (S0 : state) (C0 : execution_ctx) (exte : ext_expr) (o : out),
        @eq (option out) (out_of_ext_expr (spec_to_integer a1))
          (@Some out oo) ->
        abort oo ->
        not (abort_intercepted_expr (spec_to_integer a1)) ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq ext_expr exte (spec_to_integer a1) -> @eq out o oo -> P S C a1 oo) ->
       (red_expr S C (spec_to_integer a1) oo ->
        forall (S0 : state) (C0 : execution_ctx) (v : value) (o1 o : out),
        red_expr S C (spec_to_number a1) o1 ->
        red_expr S C (spec_to_integer_1 o1) oo ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq value v a1 -> @eq out o oo -> P S C a1 oo) ->
       red_expr S C (spec_to_integer a1) oo -> P S C a1 oo.

Parameter inv_red_expr_spec_to_integer_1
     : forall (S : state) (C : execution_ctx) (a1 oo : out)
         (P : state -> execution_ctx -> out -> out -> Prop),
       (red_expr S C (spec_to_integer_1 a1) oo ->
        forall (S0 : state) (C0 : execution_ctx) (exte : ext_expr) (o : out),
        @eq (option out) (out_of_ext_expr (spec_to_integer_1 a1))
          (@Some out oo) ->
        abort oo ->
        not (abort_intercepted_expr (spec_to_integer_1 a1)) ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq ext_expr exte (spec_to_integer_1 a1) ->
        @eq out o oo -> P S C a1 oo) ->
       (red_expr S C (spec_to_integer_1 a1) oo ->
        forall (S0 S1 : state) (C0 : execution_ctx) (n n' : JsNumber.number),
        @eq JsNumber.number n' (convert_number_to_integer n) ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq out (out_ter S1 (res_val (value_prim (prim_number n)))) a1 ->
        @eq out (out_ter S1 (res_val (value_prim (prim_number n')))) oo ->
        P S C (out_ter S1 (res_val (value_prim (prim_number n))))
          (out_ter S1 (res_val (value_prim (prim_number n'))))) ->
       red_expr S C (spec_to_integer_1 a1) oo -> P S C a1 oo.

Parameter inv_red_expr_spec_to_string
     : forall (S : state) (C : execution_ctx) (a1 : value) 
         (oo : out) (P : state -> execution_ctx -> value -> out -> Prop),
       (red_expr S C (spec_to_string a1) oo ->
        forall (S0 : state) (C0 : execution_ctx) (exte : ext_expr) (o : out),
        @eq (option out) (out_of_ext_expr (spec_to_string a1)) (@Some out oo) ->
        abort oo ->
        not (abort_intercepted_expr (spec_to_string a1)) ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq ext_expr exte (spec_to_string a1) -> @eq out o oo -> P S C a1 oo) ->
       (red_expr S C (spec_to_string a1) oo ->
        forall (S0 : state) (C0 : execution_ctx) (w : prim) (s : string),
        @eq string s (convert_prim_to_string w) ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq value (value_prim w) a1 ->
        @eq out (out_ter S (res_val (value_prim (prim_string s)))) oo ->
        P S C (value_prim w)
          (out_ter S (res_val (value_prim (prim_string s))))) ->
       (red_expr S C (spec_to_string a1) oo ->
        forall (S0 : state) (C0 : execution_ctx) (l : object_loc)
          (o1 o : out),
        red_expr S C
          (spec_to_primitive (value_object l)
             (@Some preftype preftype_string)) o1 ->
        red_expr S C (spec_to_string_1 o1) oo ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq value (value_object l) a1 ->
        @eq out o oo -> P S C (value_object l) oo) ->
       red_expr S C (spec_to_string a1) oo -> P S C a1 oo.

Parameter inv_red_expr_spec_to_string_1
     : forall (S : state) (C : execution_ctx) (a1 oo : out)
         (P : state -> execution_ctx -> out -> out -> Prop),
       (red_expr S C (spec_to_string_1 a1) oo ->
        forall (S0 : state) (C0 : execution_ctx) (exte : ext_expr) (o : out),
        @eq (option out) (out_of_ext_expr (spec_to_string_1 a1))
          (@Some out oo) ->
        abort oo ->
        not (abort_intercepted_expr (spec_to_string_1 a1)) ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq ext_expr exte (spec_to_string_1 a1) ->
        @eq out o oo -> P S C a1 oo) ->
       (red_expr S C (spec_to_string_1 a1) oo ->
        forall (S0 S1 : state) (C0 : execution_ctx) (w : prim) (s : string),
        @eq string s (convert_prim_to_string w) ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq out (out_ter S1 (res_val (value_prim w))) a1 ->
        @eq out (out_ter S1 (res_val (value_prim (prim_string s)))) oo ->
        P S C (out_ter S1 (res_val (value_prim w)))
          (out_ter S1 (res_val (value_prim (prim_string s))))) ->
       red_expr S C (spec_to_string_1 a1) oo -> P S C a1 oo.

Parameter inv_red_expr_spec_to_object
     : forall (S : state) (C : execution_ctx) (a1 : value) 
         (oo : out) (P : state -> execution_ctx -> value -> out -> Prop),
       (red_expr S C (spec_to_object a1) oo ->
        forall (S0 : state) (C0 : execution_ctx) (exte : ext_expr) (o : out),
        @eq (option out) (out_of_ext_expr (spec_to_object a1)) (@Some out oo) ->
        abort oo ->
        not (abort_intercepted_expr (spec_to_object a1)) ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq ext_expr exte (spec_to_object a1) -> @eq out o oo -> P S C a1 oo) ->
       (red_expr S C (spec_to_object a1) oo ->
        forall (S0 : state) (C0 : execution_ctx) (v : value) (o : out),
        Logic.or (@eq value a1 (value_prim prim_undef))
          (@eq value a1 (value_prim prim_null)) ->
        red_expr S C (spec_error native_error_type) oo ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq value v a1 -> @eq out o oo -> P S C a1 oo) ->
       (red_expr S C (spec_to_object a1) oo ->
        forall (S0 : state) (C0 : execution_ctx) (w : prim) (o : out),
        not (Logic.or (@eq prim w prim_undef) (@eq prim w prim_null)) ->
        red_expr S C (spec_prim_new_object w) oo ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq value (value_prim w) a1 ->
        @eq out o oo -> P S C (value_prim w) oo) ->
       (red_expr S C (spec_to_object a1) oo ->
        forall (S0 : state) (C0 : execution_ctx) (l : object_loc),
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq value (value_object l) a1 ->
        @eq out (out_ter S (res_val (value_object l))) oo ->
        P S C (value_object l) (out_ter S (res_val (value_object l)))) ->
       red_expr S C (spec_to_object a1) oo -> P S C a1 oo.

Parameter inv_red_expr_spec_check_object_coercible
     : forall (S : state) (C : execution_ctx) (a1 : value) 
         (oo : out) (P : state -> execution_ctx -> value -> out -> Prop),
       (red_expr S C (spec_check_object_coercible a1) oo ->
        forall (S0 : state) (C0 : execution_ctx) (exte : ext_expr) (o : out),
        @eq (option out) (out_of_ext_expr (spec_check_object_coercible a1))
          (@Some out oo) ->
        abort oo ->
        not (abort_intercepted_expr (spec_check_object_coercible a1)) ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq ext_expr exte (spec_check_object_coercible a1) ->
        @eq out o oo -> P S C a1 oo) ->
       (red_expr S C (spec_check_object_coercible a1) oo ->
        forall (S0 : state) (C0 : execution_ctx) (v : value) (o : out),
        Logic.or (@eq value a1 (value_prim prim_undef))
          (@eq value a1 (value_prim prim_null)) ->
        red_expr S C (spec_error native_error_type) oo ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq value v a1 -> @eq out o oo -> P S C a1 oo) ->
       (red_expr S C (spec_check_object_coercible a1) oo ->
        forall (S0 : state) (C0 : execution_ctx) (v : value),
        not
          (Logic.or (@eq value a1 (value_prim prim_undef))
             (@eq value a1 (value_prim prim_null))) ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq value v a1 -> @eq out (out_void S) oo -> P S C a1 (out_void S)) ->
       red_expr S C (spec_check_object_coercible a1) oo -> P S C a1 oo.

Parameter inv_red_expr_spec_eq
     : forall (S : state) (C : execution_ctx) (a1 a2 : value) 
         (oo : out)
         (P : state -> execution_ctx -> value -> value -> out -> Prop),
       (red_expr S C (spec_eq a1 a2) oo ->
        forall (S0 : state) (C0 : execution_ctx) (exte : ext_expr) (o : out),
        @eq (option out) (out_of_ext_expr (spec_eq a1 a2)) (@Some out oo) ->
        abort oo ->
        not (abort_intercepted_expr (spec_eq a1 a2)) ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq ext_expr exte (spec_eq a1 a2) -> @eq out o oo -> P S C a1 a2 oo) ->
       red_expr S C (spec_eq a1 a2) oo -> P S C a1 a2 oo.

Parameter inv_red_expr_spec_eq0
     : forall (S : state) (C : execution_ctx) (a1 a2 : value) 
         (oo : out)
         (P : state -> execution_ctx -> value -> value -> out -> Prop),
       (red_expr S C (spec_eq0 a1 a2) oo ->
        forall (S0 : state) (C0 : execution_ctx) (exte : ext_expr) (o : out),
        @eq (option out) (out_of_ext_expr (spec_eq0 a1 a2)) (@Some out oo) ->
        abort oo ->
        not (abort_intercepted_expr (spec_eq0 a1 a2)) ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq ext_expr exte (spec_eq0 a1 a2) -> @eq out o oo -> P S C a1 a2 oo) ->
       red_expr S C (spec_eq0 a1 a2) oo -> P S C a1 a2 oo.

Parameter inv_red_expr_spec_eq1
     : forall (S : state) (C : execution_ctx) (a1 a2 : value) 
         (oo : out)
         (P : state -> execution_ctx -> value -> value -> out -> Prop),
       (red_expr S C (spec_eq1 a1 a2) oo ->
        forall (S0 : state) (C0 : execution_ctx) (exte : ext_expr) (o : out),
        @eq (option out) (out_of_ext_expr (spec_eq1 a1 a2)) (@Some out oo) ->
        abort oo ->
        not (abort_intercepted_expr (spec_eq1 a1 a2)) ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq ext_expr exte (spec_eq1 a1 a2) -> @eq out o oo -> P S C a1 a2 oo) ->
       red_expr S C (spec_eq1 a1 a2) oo -> P S C a1 a2 oo.

Parameter inv_red_expr_spec_eq2
     : forall (S : state) (C : execution_ctx) (a1 : ext_expr) 
         (a2 a3 : value) (oo : out)
         (P : state ->
              execution_ctx -> ext_expr -> value -> value -> out -> Prop),
       (red_expr S C (spec_eq2 a1 a2 a3) oo ->
        forall (S0 : state) (C0 : execution_ctx) (exte : ext_expr) (o : out),
        @eq (option out) (out_of_ext_expr (spec_eq2 a1 a2 a3)) (@Some out oo) ->
        abort oo ->
        not (abort_intercepted_expr (spec_eq2 a1 a2 a3)) ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq ext_expr exte (spec_eq2 a1 a2 a3) ->
        @eq out o oo -> P S C a1 a2 a3 oo) ->
       red_expr S C (spec_eq2 a1 a2 a3) oo -> P S C a1 a2 a3 oo.

Parameter inv_red_expr_spec_object_get
     : forall (S : state) (C : execution_ctx) (a1 : object_loc)
         (a2 : prop_name) (oo : out)
         (P : state -> execution_ctx -> object_loc -> string -> out -> Prop),
       (red_expr S C (spec_object_get a1 a2) oo ->
        forall (S0 : state) (C0 : execution_ctx) (exte : ext_expr) (o : out),
        @eq (option out) (out_of_ext_expr (spec_object_get a1 a2))
          (@Some out oo) ->
        abort oo ->
        not (abort_intercepted_expr (spec_object_get a1 a2)) ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq ext_expr exte (spec_object_get a1 a2) ->
        @eq out o oo -> P S C a1 a2 oo) ->
       (red_expr S C (spec_object_get a1 a2) oo ->
        forall (S0 : state) (C0 : execution_ctx) (l : object_loc)
          (x : prop_name) (B : builtin_get) (o : out),
        @object_method builtin_get object_get_ S a1 B ->
        red_expr S C (spec_object_get_1 B (value_object a1) a1 a2) oo ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq object_loc l a1 ->
        @eq prop_name x a2 -> @eq out o oo -> P S C a1 a2 oo) ->
       red_expr S C (spec_object_get a1 a2) oo -> P S C a1 a2 oo.

Parameter inv_red_expr_spec_object_get_1
     : forall (S : state) (C : execution_ctx) (a1 : builtin_get) 
         (a2 : value) (a3 : object_loc) (a4 : prop_name) 
         (oo : out)
         (P : state ->
              execution_ctx ->
              builtin_get -> value -> object_loc -> string -> out -> Prop),
       (red_expr S C (spec_object_get_1 a1 a2 a3 a4) oo ->
        forall (S0 : state) (C0 : execution_ctx) (exte : ext_expr) (o : out),
        @eq (option out) (out_of_ext_expr (spec_object_get_1 a1 a2 a3 a4))
          (@Some out oo) ->
        abort oo ->
        not (abort_intercepted_expr (spec_object_get_1 a1 a2 a3 a4)) ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq ext_expr exte (spec_object_get_1 a1 a2 a3 a4) ->
        @eq out o oo -> P S C a1 a2 a3 a4 oo) ->
       (red_expr S C (spec_object_get_1 a1 a2 a3 a4) oo ->
        forall (S0 : state) (C0 : execution_ctx) (vthis : value)
          (l : object_loc) (x : prop_name) (y1 : specret full_descriptor)
          (o : out),
        @red_spec full_descriptor S C (spec_object_get_prop a3 a4) y1 ->
        red_expr S C (spec_object_get_2 a2 y1) oo ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq builtin_get builtin_get_default a1 ->
        @eq value vthis a2 ->
        @eq object_loc l a3 ->
        @eq prop_name x a4 ->
        @eq out o oo -> P S C builtin_get_default a2 a3 a4 oo) ->
       (red_expr S C (spec_object_get_1 a1 a2 a3 a4) oo ->
        forall (lmap : object_loc) (S0 : state) (C0 : execution_ctx)
          (vthis : value) (l : object_loc) (x : prop_name) 
          (o : out) (y : specret full_descriptor),
        @object_method (option object_loc) object_parameter_map_ S a3
          (@Some object_loc lmap) ->
        @red_spec full_descriptor S C (spec_object_get_own_prop lmap a4) y ->
        red_expr S C (spec_args_obj_get_1 a2 a3 a4 lmap y) oo ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq builtin_get builtin_get_args_obj a1 ->
        @eq value vthis a2 ->
        @eq object_loc l a3 ->
        @eq prop_name x a4 ->
        @eq out o oo -> P S C builtin_get_args_obj a2 a3 a4 oo) ->
       (red_expr S C (spec_object_get_1 a1 a2 a3 a4) oo ->
        forall (S0 : state) (C0 : execution_ctx) (vthis : value)
          (l : object_loc) (x : prop_name) (o1 o : out),
        red_expr S C (spec_object_get_1 builtin_get_default a2 a3 a4) o1 ->
        red_expr S C (spec_function_get_1 a3 a4 o1) oo ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq builtin_get builtin_get_function a1 ->
        @eq value vthis a2 ->
        @eq object_loc l a3 ->
        @eq prop_name x a4 ->
        @eq out o oo -> P S C builtin_get_function a2 a3 a4 oo) ->
       red_expr S C (spec_object_get_1 a1 a2 a3 a4) oo ->
       P S C a1 a2 a3 a4 oo.

Parameter inv_red_expr_spec_object_get_2
     : forall (S : state) (C : execution_ctx) (a1 : value)
         (a2 : specret full_descriptor) (oo : out)
         (P : state ->
              execution_ctx ->
              value -> specret full_descriptor -> out -> Prop),
       (red_expr S C (spec_object_get_2 a1 a2) oo ->
        forall (S0 : state) (C0 : execution_ctx) (exte : ext_expr) (o : out),
        @eq (option out) (out_of_ext_expr (spec_object_get_2 a1 a2))
          (@Some out oo) ->
        abort oo ->
        not (abort_intercepted_expr (spec_object_get_2 a1 a2)) ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq ext_expr exte (spec_object_get_2 a1 a2) ->
        @eq out o oo -> P S C a1 a2 oo) ->
       (red_expr S C (spec_object_get_2 a1 a2) oo ->
        forall (S0 S1 : state) (C0 : execution_ctx) (vthis : value),
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq value vthis a1 ->
        @eq (specret full_descriptor) (dret S1 full_descriptor_undef) a2 ->
        @eq out (out_ter S1 (res_val (value_prim prim_undef))) oo ->
        P S C a1 (dret S1 full_descriptor_undef)
          (out_ter S1 (res_val (value_prim prim_undef)))) ->
       (red_expr S C (spec_object_get_2 a1 a2) oo ->
        forall (S0 S1 : state) (C0 : execution_ctx) 
          (vthis : value) (Ad : attributes_data) (v : value),
        @eq value v (attributes_data_value Ad) ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq value vthis a1 ->
        @eq (specret full_descriptor)
          (dret S1 (full_descriptor_some (attributes_data_of Ad))) a2 ->
        @eq out (out_ter S1 (res_val v)) oo ->
        P S C a1 (dret S1 (full_descriptor_some (attributes_data_of Ad)))
          (out_ter S1 (res_val v))) ->
       (red_expr S C (spec_object_get_2 a1 a2) oo ->
        forall (S0 S1 : state) (C0 : execution_ctx) 
          (vthis : value) (Aa : attributes_accessor) 
          (o : out),
        red_expr S1 C (spec_object_get_3 a1 (attributes_accessor_get Aa)) oo ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq value vthis a1 ->
        @eq (specret full_descriptor)
          (dret S1 (full_descriptor_some (attributes_accessor_of Aa))) a2 ->
        @eq out o oo ->
        P S C a1 (dret S1 (full_descriptor_some (attributes_accessor_of Aa)))
          oo) -> red_expr S C (spec_object_get_2 a1 a2) oo -> P S C a1 a2 oo.

Parameter inv_red_expr_spec_object_get_3
     : forall (S : state) (C : execution_ctx) (a1 a2 : value) 
         (oo : out)
         (P : state -> execution_ctx -> value -> value -> out -> Prop),
       (red_expr S C (spec_object_get_3 a1 a2) oo ->
        forall (S0 : state) (C0 : execution_ctx) (exte : ext_expr) (o : out),
        @eq (option out) (out_of_ext_expr (spec_object_get_3 a1 a2))
          (@Some out oo) ->
        abort oo ->
        not (abort_intercepted_expr (spec_object_get_3 a1 a2)) ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq ext_expr exte (spec_object_get_3 a1 a2) ->
        @eq out o oo -> P S C a1 a2 oo) ->
       (red_expr S C (spec_object_get_3 a1 a2) oo ->
        forall (S0 : state) (C0 : execution_ctx) (vthis : value),
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq value vthis a1 ->
        @eq value (value_prim prim_undef) a2 ->
        @eq out (out_ter S (res_val (value_prim prim_undef))) oo ->
        P S C a1 (value_prim prim_undef)
          (out_ter S (res_val (value_prim prim_undef)))) ->
       (red_expr S C (spec_object_get_3 a1 a2) oo ->
        forall (S0 : state) (C0 : execution_ctx) (vthis : value)
          (lf : object_loc) (o : out),
        red_expr S C (spec_call lf a1 (@nil value)) oo ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq value vthis a1 ->
        @eq value (value_object lf) a2 ->
        @eq out o oo -> P S C a1 (value_object lf) oo) ->
       red_expr S C (spec_object_get_3 a1 a2) oo -> P S C a1 a2 oo.

Parameter inv_red_expr_spec_object_can_put
     : forall (S : state) (C : execution_ctx) (a1 : object_loc)
         (a2 : prop_name) (oo : out)
         (P : state -> execution_ctx -> object_loc -> string -> out -> Prop),
       (red_expr S C (spec_object_can_put a1 a2) oo ->
        forall (S0 : state) (C0 : execution_ctx) (exte : ext_expr) (o : out),
        @eq (option out) (out_of_ext_expr (spec_object_can_put a1 a2))
          (@Some out oo) ->
        abort oo ->
        not (abort_intercepted_expr (spec_object_can_put a1 a2)) ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq ext_expr exte (spec_object_can_put a1 a2) ->
        @eq out o oo -> P S C a1 a2 oo) ->
       (red_expr S C (spec_object_can_put a1 a2) oo ->
        forall (S0 : state) (C0 : execution_ctx) (l : object_loc)
          (x : prop_name) (B : builtin_can_put) (o : out),
        @object_method builtin_can_put object_can_put_ S a1 B ->
        red_expr S C (spec_object_can_put_1 B a1 a2) oo ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq object_loc l a1 ->
        @eq prop_name x a2 -> @eq out o oo -> P S C a1 a2 oo) ->
       red_expr S C (spec_object_can_put a1 a2) oo -> P S C a1 a2 oo.

Parameter inv_red_expr_spec_object_can_put_1
     : forall (S : state) (C : execution_ctx) (a1 : builtin_can_put)
         (a2 : object_loc) (a3 : prop_name) (oo : out)
         (P : state ->
              execution_ctx ->
              builtin_can_put -> object_loc -> string -> out -> Prop),
       (red_expr S C (spec_object_can_put_1 a1 a2 a3) oo ->
        forall (S0 : state) (C0 : execution_ctx) (exte : ext_expr) (o : out),
        @eq (option out) (out_of_ext_expr (spec_object_can_put_1 a1 a2 a3))
          (@Some out oo) ->
        abort oo ->
        not (abort_intercepted_expr (spec_object_can_put_1 a1 a2 a3)) ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq ext_expr exte (spec_object_can_put_1 a1 a2 a3) ->
        @eq out o oo -> P S C a1 a2 a3 oo) ->
       (red_expr S C (spec_object_can_put_1 a1 a2 a3) oo ->
        forall (S0 : state) (C0 : execution_ctx) (l : object_loc)
          (x : prop_name) (o : out) (y : specret full_descriptor),
        @red_spec full_descriptor S C (spec_object_get_own_prop a2 a3) y ->
        red_expr S C (spec_object_can_put_2 a2 a3 y) oo ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq object_loc l a2 ->
        @eq prop_name x a3 -> @eq out o oo -> P S C a1 a2 a3 oo) ->
       red_expr S C (spec_object_can_put_1 a1 a2 a3) oo -> P S C a1 a2 a3 oo.

Parameter inv_red_expr_spec_object_can_put_2
     : forall (S : state) (C : execution_ctx) (a1 : object_loc)
         (a2 : prop_name) (a3 : specret full_descriptor) 
         (oo : out)
         (P : state ->
              execution_ctx ->
              object_loc -> string -> specret full_descriptor -> out -> Prop),
       (red_expr S C (spec_object_can_put_2 a1 a2 a3) oo ->
        forall (S0 : state) (C0 : execution_ctx) (exte : ext_expr) (o : out),
        @eq (option out) (out_of_ext_expr (spec_object_can_put_2 a1 a2 a3))
          (@Some out oo) ->
        abort oo ->
        not (abort_intercepted_expr (spec_object_can_put_2 a1 a2 a3)) ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq ext_expr exte (spec_object_can_put_2 a1 a2 a3) ->
        @eq out o oo -> P S C a1 a2 a3 oo) ->
       (red_expr S C (spec_object_can_put_2 a1 a2 a3) oo ->
        forall (S0 S1 : state) (C0 : execution_ctx) 
          (l : object_loc) (x : prop_name) (Aa : attributes_accessor)
          (b : bool),
        @eq bool b
          match
            classicT
              (@eq value (attributes_accessor_set Aa) (value_prim prim_undef))
            return bool
          with
          | left _ => false
          | right _ => true
          end ->
        @eq state S1 S ->
        @eq execution_ctx C0 C ->
        @eq object_loc l a1 ->
        @eq prop_name x a2 ->
        @eq (specret full_descriptor)
          (dret S0 (full_descriptor_some (attributes_accessor_of Aa))) a3 ->
        @eq out (out_ter S0 (res_val (value_prim (prim_bool b)))) oo ->
        P S C a1 a2
          (dret S0 (full_descriptor_some (attributes_accessor_of Aa)))
          (out_ter S0 (res_val (value_prim (prim_bool b))))) ->
       (red_expr S C (spec_object_can_put_2 a1 a2 a3) oo ->
        forall (S0 S1 : state) (C0 : execution_ctx) 
          (l : object_loc) (x : prop_name) (Ad : attributes_data) 
          (b : bool),
        @eq bool b (attributes_data_writable Ad) ->
        @eq state S1 S ->
        @eq execution_ctx C0 C ->
        @eq object_loc l a1 ->
        @eq prop_name x a2 ->
        @eq (specret full_descriptor)
          (dret S0 (full_descriptor_some (attributes_data_of Ad))) a3 ->
        @eq out (out_ter S0 (res_val (value_prim (prim_bool b)))) oo ->
        P S C a1 a2 (dret S0 (full_descriptor_some (attributes_data_of Ad)))
          (out_ter S0 (res_val (value_prim (prim_bool b))))) ->
       (red_expr S C (spec_object_can_put_2 a1 a2 a3) oo ->
        forall (S0 S1 : state) (C0 : execution_ctx) 
          (l : object_loc) (x : prop_name) (o : out) 
          (lproto : value),
        object_proto S1 a1 lproto ->
        red_expr S1 C (spec_object_can_put_4 a1 a2 lproto) oo ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq object_loc l a1 ->
        @eq prop_name x a2 ->
        @eq (specret full_descriptor)
          (@ret full_descriptor S1 full_descriptor_undef) a3 ->
        @eq out o oo ->
        P S C a1 a2 (@ret full_descriptor S1 full_descriptor_undef) oo) ->
       red_expr S C (spec_object_can_put_2 a1 a2 a3) oo -> P S C a1 a2 a3 oo.

Parameter inv_red_expr_spec_object_can_put_4
     : forall (S : state) (C : execution_ctx) (a1 : object_loc)
         (a2 : prop_name) (a3 : value) (oo : out)
         (P : state ->
              execution_ctx -> object_loc -> string -> value -> out -> Prop),
       (red_expr S C (spec_object_can_put_4 a1 a2 a3) oo ->
        forall (S0 : state) (C0 : execution_ctx) (exte : ext_expr) (o : out),
        @eq (option out) (out_of_ext_expr (spec_object_can_put_4 a1 a2 a3))
          (@Some out oo) ->
        abort oo ->
        not (abort_intercepted_expr (spec_object_can_put_4 a1 a2 a3)) ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq ext_expr exte (spec_object_can_put_4 a1 a2 a3) ->
        @eq out o oo -> P S C a1 a2 a3 oo) ->
       (red_expr S C (spec_object_can_put_4 a1 a2 a3) oo ->
        forall (S0 : state) (C0 : execution_ctx) (l : object_loc)
          (x : prop_name) (b : bool),
        object_extensible S a1 b ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq object_loc l a1 ->
        @eq prop_name x a2 ->
        @eq value (value_prim prim_null) a3 ->
        @eq out (out_ter S (res_val (value_prim (prim_bool b)))) oo ->
        P S C a1 a2 (value_prim prim_null)
          (out_ter S (res_val (value_prim (prim_bool b))))) ->
       (red_expr S C (spec_object_can_put_4 a1 a2 a3) oo ->
        forall (S0 : state) (C0 : execution_ctx) (l : object_loc)
          (x : prop_name) (lproto : object_loc)
          (y1 : specret full_descriptor) (o : out),
        @red_spec full_descriptor S C (spec_object_get_prop lproto a2) y1 ->
        red_expr S C (spec_object_can_put_5 a1 y1) oo ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq object_loc l a1 ->
        @eq prop_name x a2 ->
        @eq value (value_object lproto) a3 ->
        @eq out o oo -> P S C a1 a2 (value_object lproto) oo) ->
       red_expr S C (spec_object_can_put_4 a1 a2 a3) oo -> P S C a1 a2 a3 oo.

Parameter inv_red_expr_spec_object_can_put_5
     : forall (S : state) (C : execution_ctx) (a1 : object_loc)
         (a2 : specret full_descriptor) (oo : out)
         (P : state ->
              execution_ctx ->
              object_loc -> specret full_descriptor -> out -> Prop),
       (red_expr S C (spec_object_can_put_5 a1 a2) oo ->
        forall (S0 : state) (C0 : execution_ctx) (exte : ext_expr) (o : out),
        @eq (option out) (out_of_ext_expr (spec_object_can_put_5 a1 a2))
          (@Some out oo) ->
        abort oo ->
        not (abort_intercepted_expr (spec_object_can_put_5 a1 a2)) ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq ext_expr exte (spec_object_can_put_5 a1 a2) ->
        @eq out o oo -> P S C a1 a2 oo) ->
       (red_expr S C (spec_object_can_put_5 a1 a2) oo ->
        forall (S0 S1 : state) (C0 : execution_ctx) 
          (l : object_loc) (b : bool),
        object_extensible S1 a1 b ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq object_loc l a1 ->
        @eq (specret full_descriptor) (dret S1 full_descriptor_undef) a2 ->
        @eq out (out_ter S1 (res_val (value_prim (prim_bool b)))) oo ->
        P S C a1 (dret S1 full_descriptor_undef)
          (out_ter S1 (res_val (value_prim (prim_bool b))))) ->
       (red_expr S C (spec_object_can_put_5 a1 a2) oo ->
        forall (S0 S1 : state) (C0 : execution_ctx) 
          (l : object_loc) (Aa : attributes_accessor) 
          (b : bool),
        @eq bool b
          match
            classicT
              (@eq value (attributes_accessor_set Aa) (value_prim prim_undef))
            return bool
          with
          | left _ => false
          | right _ => true
          end ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq object_loc l a1 ->
        @eq (specret full_descriptor)
          (dret S1 (full_descriptor_some (attributes_accessor_of Aa))) a2 ->
        @eq out (out_ter S1 (res_val (value_prim (prim_bool b)))) oo ->
        P S C a1 (dret S1 (full_descriptor_some (attributes_accessor_of Aa)))
          (out_ter S1 (res_val (value_prim (prim_bool b))))) ->
       (red_expr S C (spec_object_can_put_5 a1 a2) oo ->
        forall (S0 S1 : state) (C0 : execution_ctx) 
          (l : object_loc) (Ad : attributes_data) (bext : bool) 
          (o : out),
        object_extensible S1 a1 bext ->
        red_expr S1 C (spec_object_can_put_6 Ad bext) oo ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq object_loc l a1 ->
        @eq (specret full_descriptor)
          (dret S1 (full_descriptor_some (attributes_data_of Ad))) a2 ->
        @eq out o oo ->
        P S C a1 (dret S1 (full_descriptor_some (attributes_data_of Ad))) oo) ->
       red_expr S C (spec_object_can_put_5 a1 a2) oo -> P S C a1 a2 oo.

Parameter inv_red_expr_spec_object_can_put_6
     : forall (S : state) (C : execution_ctx) (a1 : attributes_data)
         (a2 : bool) (oo : out)
         (P : state ->
              execution_ctx -> attributes_data -> bool -> out -> Prop),
       (red_expr S C (spec_object_can_put_6 a1 a2) oo ->
        forall (S0 : state) (C0 : execution_ctx) (exte : ext_expr) (o : out),
        @eq (option out) (out_of_ext_expr (spec_object_can_put_6 a1 a2))
          (@Some out oo) ->
        abort oo ->
        not (abort_intercepted_expr (spec_object_can_put_6 a1 a2)) ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq ext_expr exte (spec_object_can_put_6 a1 a2) ->
        @eq out o oo -> P S C a1 a2 oo) ->
       (red_expr S C (spec_object_can_put_6 a1 a2) oo ->
        forall (S0 : state) (C0 : execution_ctx) (Ad : attributes_data),
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq attributes_data Ad a1 ->
        @eq bool false a2 ->
        @eq out (out_ter S (res_val (value_prim (prim_bool false)))) oo ->
        P S C a1 false (out_ter S (res_val (value_prim (prim_bool false))))) ->
       (red_expr S C (spec_object_can_put_6 a1 a2) oo ->
        forall (S0 : state) (C0 : execution_ctx) (Ad : attributes_data)
          (b : bool),
        @eq bool b (attributes_data_writable a1) ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq attributes_data Ad a1 ->
        @eq bool true a2 ->
        @eq out (out_ter S (res_val (value_prim (prim_bool b)))) oo ->
        P S C a1 true (out_ter S (res_val (value_prim (prim_bool b))))) ->
       red_expr S C (spec_object_can_put_6 a1 a2) oo -> P S C a1 a2 oo.

Parameter inv_red_expr_spec_object_put
     : forall (S : state) (C : execution_ctx) (a1 : object_loc)
         (a2 : prop_name) (a3 : value) (a4 : bool) 
         (oo : out)
         (P : state ->
              execution_ctx ->
              object_loc -> string -> value -> bool -> out -> Prop),
       (red_expr S C (spec_object_put a1 a2 a3 a4) oo ->
        forall (S0 : state) (C0 : execution_ctx) (exte : ext_expr) (o : out),
        @eq (option out) (out_of_ext_expr (spec_object_put a1 a2 a3 a4))
          (@Some out oo) ->
        abort oo ->
        not (abort_intercepted_expr (spec_object_put a1 a2 a3 a4)) ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq ext_expr exte (spec_object_put a1 a2 a3 a4) ->
        @eq out o oo -> P S C a1 a2 a3 a4 oo) ->
       (red_expr S C (spec_object_put a1 a2 a3 a4) oo ->
        forall (S0 : state) (C0 : execution_ctx) (l : object_loc)
          (x : prop_name) (v : value) (throw : bool) 
          (B : builtin_put) (o : out),
        @object_method builtin_put object_put_ S a1 B ->
        red_expr S C (spec_object_put_1 B (value_object a1) a1 a2 a3 a4) oo ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq object_loc l a1 ->
        @eq prop_name x a2 ->
        @eq value v a3 ->
        @eq bool throw a4 -> @eq out o oo -> P S C a1 a2 a3 a4 oo) ->
       red_expr S C (spec_object_put a1 a2 a3 a4) oo -> P S C a1 a2 a3 a4 oo.

Parameter inv_red_expr_spec_object_put_1
     : forall (S : state) (C : execution_ctx) (a1 : builtin_put) 
         (a2 : value) (a3 : object_loc) (a4 : prop_name) 
         (a5 : value) (a6 : bool) (oo : out)
         (P : state ->
              execution_ctx ->
              builtin_put ->
              value -> object_loc -> string -> value -> bool -> out -> Prop),
       (red_expr S C (spec_object_put_1 a1 a2 a3 a4 a5 a6) oo ->
        forall (S0 : state) (C0 : execution_ctx) (exte : ext_expr) (o : out),
        @eq (option out)
          (out_of_ext_expr (spec_object_put_1 a1 a2 a3 a4 a5 a6))
          (@Some out oo) ->
        abort oo ->
        not (abort_intercepted_expr (spec_object_put_1 a1 a2 a3 a4 a5 a6)) ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq ext_expr exte (spec_object_put_1 a1 a2 a3 a4 a5 a6) ->
        @eq out o oo -> P S C a1 a2 a3 a4 a5 a6 oo) ->
       (red_expr S C (spec_object_put_1 a1 a2 a3 a4 a5 a6) oo ->
        forall (S0 : state) (C0 : execution_ctx) (vthis : value)
          (l : object_loc) (x : prop_name) (v : value) 
          (throw : bool) (o1 o : out),
        red_expr S C (spec_object_can_put a3 a4) o1 ->
        red_expr S C (spec_object_put_2 a2 a3 a4 a5 a6 o1) oo ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq value vthis a2 ->
        @eq object_loc l a3 ->
        @eq prop_name x a4 ->
        @eq value v a5 ->
        @eq bool throw a6 -> @eq out o oo -> P S C a1 a2 a3 a4 a5 a6 oo) ->
       red_expr S C (spec_object_put_1 a1 a2 a3 a4 a5 a6) oo ->
       P S C a1 a2 a3 a4 a5 a6 oo.

Parameter inv_red_expr_spec_object_put_2
     : forall (S : state) (C : execution_ctx) (a1 : value) 
         (a2 : object_loc) (a3 : prop_name) (a4 : value) 
         (a5 : bool) (a6 oo : out)
         (P : state ->
              execution_ctx ->
              value ->
              object_loc -> string -> value -> bool -> out -> out -> Prop),
       (red_expr S C (spec_object_put_2 a1 a2 a3 a4 a5 a6) oo ->
        forall (S0 : state) (C0 : execution_ctx) (exte : ext_expr) (o : out),
        @eq (option out)
          (out_of_ext_expr (spec_object_put_2 a1 a2 a3 a4 a5 a6))
          (@Some out oo) ->
        abort oo ->
        not (abort_intercepted_expr (spec_object_put_2 a1 a2 a3 a4 a5 a6)) ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq ext_expr exte (spec_object_put_2 a1 a2 a3 a4 a5 a6) ->
        @eq out o oo -> P S C a1 a2 a3 a4 a5 a6 oo) ->
       (red_expr S C (spec_object_put_2 a1 a2 a3 a4 a5 a6) oo ->
        forall (S0 S1 : state) (C0 : execution_ctx) 
          (vthis : value) (l : object_loc) (x : prop_name) 
          (v : value) (throw : bool) (o : out),
        red_expr S1 C (spec_error_or_void a5 native_error_type) oo ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq value vthis a1 ->
        @eq object_loc l a2 ->
        @eq prop_name x a3 ->
        @eq value v a4 ->
        @eq bool throw a5 ->
        @eq out (out_ter S1 (res_val (value_prim (prim_bool false)))) a6 ->
        @eq out o oo ->
        P S C a1 a2 a3 a4 a5
          (out_ter S1 (res_val (value_prim (prim_bool false)))) oo) ->
       (red_expr S C (spec_object_put_2 a1 a2 a3 a4 a5 a6) oo ->
        forall (S0 S1 : state) (C0 : execution_ctx) 
          (vthis : value) (l : object_loc) (x : prop_name) 
          (v : value) (throw : bool) (o : out) (y : specret full_descriptor),
        @red_spec full_descriptor S1 C (spec_object_get_own_prop a2 a3) y ->
        red_expr S1 C (spec_object_put_3 a1 a2 a3 a4 a5 y) oo ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq value vthis a1 ->
        @eq object_loc l a2 ->
        @eq prop_name x a3 ->
        @eq value v a4 ->
        @eq bool throw a5 ->
        @eq out (out_ter S1 (res_val (value_prim (prim_bool true)))) a6 ->
        @eq out o oo ->
        P S C a1 a2 a3 a4 a5
          (out_ter S1 (res_val (value_prim (prim_bool true)))) oo) ->
       red_expr S C (spec_object_put_2 a1 a2 a3 a4 a5 a6) oo ->
       P S C a1 a2 a3 a4 a5 a6 oo.

Parameter inv_red_expr_spec_object_put_3
     : forall (S : state) (C : execution_ctx) (a1 : value) 
         (a2 : object_loc) (a3 : prop_name) (a4 : value) 
         (a5 : bool) (a6 : specret full_descriptor) 
         (oo : out)
         (P : state ->
              execution_ctx ->
              value ->
              object_loc ->
              string ->
              value -> bool -> specret full_descriptor -> out -> Prop),
       (red_expr S C (spec_object_put_3 a1 a2 a3 a4 a5 a6) oo ->
        forall (S0 : state) (C0 : execution_ctx) (exte : ext_expr) (o : out),
        @eq (option out)
          (out_of_ext_expr (spec_object_put_3 a1 a2 a3 a4 a5 a6))
          (@Some out oo) ->
        abort oo ->
        not (abort_intercepted_expr (spec_object_put_3 a1 a2 a3 a4 a5 a6)) ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq ext_expr exte (spec_object_put_3 a1 a2 a3 a4 a5 a6) ->
        @eq out o oo -> P S C a1 a2 a3 a4 a5 a6 oo) ->
       (red_expr S C (spec_object_put_3 a1 a2 a3 a4 a5 a6) oo ->
        forall (S0 S1 : state) (C0 : execution_ctx) 
          (lthis l : object_loc) (x : prop_name) (v : value) 
          (throw : bool) (Ad : attributes_data) (Desc : descriptor)
          (o1 o : out),
        @eq descriptor Desc
          (descriptor_intro (@Some value a4) (@None bool) 
             (@None value) (@None value) (@None bool) 
             (@None bool)) ->
        red_expr S1 C (spec_object_define_own_prop a2 a3 Desc a5) o1 ->
        red_expr S1 C (spec_object_put_5 o1) oo ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq value (value_object lthis) a1 ->
        @eq object_loc l a2 ->
        @eq prop_name x a3 ->
        @eq value v a4 ->
        @eq bool throw a5 ->
        @eq (specret full_descriptor)
          (dret S1 (full_descriptor_some (attributes_data_of Ad))) a6 ->
        @eq out o oo ->
        P S C (value_object lthis) a2 a3 a4 a5
          (dret S1 (full_descriptor_some (attributes_data_of Ad))) oo) ->
       (red_expr S C (spec_object_put_3 a1 a2 a3 a4 a5 a6) oo ->
        forall (S0 S1 : state) (C0 : execution_ctx) 
          (wthis : prim) (l : object_loc) (x : prop_name) 
          (v : value) (throw : bool) (Ad : attributes_data) 
          (o : out),
        red_expr S1 C (spec_error_or_void a5 native_error_type) oo ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq value (value_prim wthis) a1 ->
        @eq object_loc l a2 ->
        @eq prop_name x a3 ->
        @eq value v a4 ->
        @eq bool throw a5 ->
        @eq (specret full_descriptor)
          (dret S1 (full_descriptor_some (attributes_data_of Ad))) a6 ->
        @eq out o oo ->
        P S C (value_prim wthis) a2 a3 a4 a5
          (dret S1 (full_descriptor_some (attributes_data_of Ad))) oo) ->
       (red_expr S C (spec_object_put_3 a1 a2 a3 a4 a5 a6) oo ->
        forall (S0 S1 : state) (C0 : execution_ctx) 
          (vthis : value) (l : object_loc) (x : prop_name) 
          (v : value) (throw : bool) (Aa : attributes_accessor)
          (y1 : specret full_descriptor) (o : out) 
          (D : full_descriptor),
        Logic.or (@eq full_descriptor D full_descriptor_undef)
          (@eq full_descriptor D
             (full_descriptor_some (attributes_accessor_of Aa))) ->
        @red_spec full_descriptor S1 C (spec_object_get_prop a2 a3) y1 ->
        red_expr S1 C (spec_object_put_4 a1 a2 a3 a4 a5 y1) oo ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq value vthis a1 ->
        @eq object_loc l a2 ->
        @eq prop_name x a3 ->
        @eq value v a4 ->
        @eq bool throw a5 ->
        @eq (specret full_descriptor) (@ret full_descriptor S1 D) a6 ->
        @eq out o oo -> P S C a1 a2 a3 a4 a5 (@ret full_descriptor S1 D) oo) ->
       red_expr S C (spec_object_put_3 a1 a2 a3 a4 a5 a6) oo ->
       P S C a1 a2 a3 a4 a5 a6 oo.

Parameter inv_red_expr_spec_object_put_4
     : forall (S : state) (C : execution_ctx) (a1 : value) 
         (a2 : object_loc) (a3 : prop_name) (a4 : value) 
         (a5 : bool) (a6 : specret full_descriptor) 
         (oo : out)
         (P : state ->
              execution_ctx ->
              value ->
              object_loc ->
              string ->
              value -> bool -> specret full_descriptor -> out -> Prop),
       (red_expr S C (spec_object_put_4 a1 a2 a3 a4 a5 a6) oo ->
        forall (S0 : state) (C0 : execution_ctx) (exte : ext_expr) (o : out),
        @eq (option out)
          (out_of_ext_expr (spec_object_put_4 a1 a2 a3 a4 a5 a6))
          (@Some out oo) ->
        abort oo ->
        not (abort_intercepted_expr (spec_object_put_4 a1 a2 a3 a4 a5 a6)) ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq ext_expr exte (spec_object_put_4 a1 a2 a3 a4 a5 a6) ->
        @eq out o oo -> P S C a1 a2 a3 a4 a5 a6 oo) ->
       (red_expr S C (spec_object_put_4 a1 a2 a3 a4 a5 a6) oo ->
        forall (S0 S1 : state) (C0 : execution_ctx) 
          (vsetter : value) (lfsetter : object_loc) 
          (vthis : value) (l : object_loc) (x : prop_name) 
          (v : value) (throw : bool) (Aa : attributes_accessor) 
          (o1 o : out),
        @eq value vsetter (attributes_accessor_set Aa) ->
        not (@eq value vsetter (value_prim prim_undef)) ->
        @eq value vsetter (value_object lfsetter) ->
        red_expr S1 C (spec_call lfsetter a1 (@cons value a4 (@nil value)))
          o1 ->
        red_expr S1 C (spec_object_put_5 o1) oo ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq value vthis a1 ->
        @eq object_loc l a2 ->
        @eq prop_name x a3 ->
        @eq value v a4 ->
        @eq bool throw a5 ->
        @eq (specret full_descriptor)
          (dret S1 (full_descriptor_some (attributes_accessor_of Aa))) a6 ->
        @eq out o oo ->
        P S C a1 a2 a3 a4 a5
          (dret S1 (full_descriptor_some (attributes_accessor_of Aa))) oo) ->
       (red_expr S C (spec_object_put_4 a1 a2 a3 a4 a5 a6) oo ->
        forall (S0 S1 : state) (C0 : execution_ctx) 
          (D : full_descriptor) (lthis l : object_loc) 
          (x : prop_name) (v : value) (throw : bool) 
          (Ad : attributes_data) (Desc : descriptor) 
          (o1 o : out),
        Logic.or (@eq full_descriptor D full_descriptor_undef)
          (@eq full_descriptor D
             (full_descriptor_some (attributes_data_of Ad))) ->
        @eq descriptor Desc (descriptor_intro_data a4 true true true) ->
        red_expr S1 C (spec_object_define_own_prop a2 a3 Desc a5) o1 ->
        red_expr S1 C (spec_object_put_5 o1) oo ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq value (value_object lthis) a1 ->
        @eq object_loc l a2 ->
        @eq prop_name x a3 ->
        @eq value v a4 ->
        @eq bool throw a5 ->
        @eq (specret full_descriptor) (dret S1 D) a6 ->
        @eq out o oo -> P S C (value_object lthis) a2 a3 a4 a5 (dret S1 D) oo) ->
       (red_expr S C (spec_object_put_4 a1 a2 a3 a4 a5 a6) oo ->
        forall (S0 S1 : state) (C0 : execution_ctx) 
          (wthis : prim) (D : full_descriptor) (l : object_loc)
          (x : prop_name) (v : value) (throw : bool) 
          (Ad : attributes_data) (o : out),
        Logic.or (@eq full_descriptor D full_descriptor_undef)
          (@eq full_descriptor D
             (full_descriptor_some (attributes_data_of Ad))) ->
        red_expr S1 C (spec_error_or_void a5 native_error_type) oo ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq value (value_prim wthis) a1 ->
        @eq object_loc l a2 ->
        @eq prop_name x a3 ->
        @eq value v a4 ->
        @eq bool throw a5 ->
        @eq (specret full_descriptor) (dret S1 D) a6 ->
        @eq out o oo -> P S C (value_prim wthis) a2 a3 a4 a5 (dret S1 D) oo) ->
       red_expr S C (spec_object_put_4 a1 a2 a3 a4 a5 a6) oo ->
       P S C a1 a2 a3 a4 a5 a6 oo.

Parameter inv_red_expr_spec_object_put_5
     : forall (S : state) (C : execution_ctx) (a1 oo : out)
         (P : state -> execution_ctx -> out -> out -> Prop),
       (red_expr S C (spec_object_put_5 a1) oo ->
        forall (S0 : state) (C0 : execution_ctx) (exte : ext_expr) (o : out),
        @eq (option out) (out_of_ext_expr (spec_object_put_5 a1))
          (@Some out oo) ->
        abort oo ->
        not (abort_intercepted_expr (spec_object_put_5 a1)) ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq ext_expr exte (spec_object_put_5 a1) ->
        @eq out o oo -> P S C a1 oo) ->
       (red_expr S C (spec_object_put_5 a1) oo ->
        forall (S0 S1 : state) (C0 : execution_ctx) (rv : resvalue),
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq out (out_ter S1 (res_normal rv)) a1 ->
        @eq out (out_void S1) oo ->
        P S C (out_ter S1 (res_normal rv)) (out_void S1)) ->
       red_expr S C (spec_object_put_5 a1) oo -> P S C a1 oo.

Parameter inv_red_expr_spec_object_has_prop
     : forall (S : state) (C : execution_ctx) (a1 : object_loc)
         (a2 : prop_name) (oo : out)
         (P : state -> execution_ctx -> object_loc -> string -> out -> Prop),
       (red_expr S C (spec_object_has_prop a1 a2) oo ->
        forall (S0 : state) (C0 : execution_ctx) (exte : ext_expr) (o : out),
        @eq (option out) (out_of_ext_expr (spec_object_has_prop a1 a2))
          (@Some out oo) ->
        abort oo ->
        not (abort_intercepted_expr (spec_object_has_prop a1 a2)) ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq ext_expr exte (spec_object_has_prop a1 a2) ->
        @eq out o oo -> P S C a1 a2 oo) ->
       (red_expr S C (spec_object_has_prop a1 a2) oo ->
        forall (S0 : state) (C0 : execution_ctx) (l : object_loc)
          (x : prop_name) (B : builtin_has_prop) (o : out),
        @object_method builtin_has_prop object_has_prop_ S a1 B ->
        red_expr S C (spec_object_has_prop_1 B a1 a2) oo ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq object_loc l a1 ->
        @eq prop_name x a2 -> @eq out o oo -> P S C a1 a2 oo) ->
       red_expr S C (spec_object_has_prop a1 a2) oo -> P S C a1 a2 oo.

Parameter inv_red_expr_spec_object_has_prop_1
     : forall (S : state) (C : execution_ctx) (a1 : builtin_has_prop)
         (a2 : object_loc) (a3 : prop_name) (oo : out)
         (P : state ->
              execution_ctx ->
              builtin_has_prop -> object_loc -> string -> out -> Prop),
       (red_expr S C (spec_object_has_prop_1 a1 a2 a3) oo ->
        forall (S0 : state) (C0 : execution_ctx) (exte : ext_expr) (o : out),
        @eq (option out) (out_of_ext_expr (spec_object_has_prop_1 a1 a2 a3))
          (@Some out oo) ->
        abort oo ->
        not (abort_intercepted_expr (spec_object_has_prop_1 a1 a2 a3)) ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq ext_expr exte (spec_object_has_prop_1 a1 a2 a3) ->
        @eq out o oo -> P S C a1 a2 a3 oo) ->
       (red_expr S C (spec_object_has_prop_1 a1 a2 a3) oo ->
        forall (S0 : state) (C0 : execution_ctx) (l : object_loc)
          (x : prop_name) (y1 : specret full_descriptor) 
          (o : out),
        @red_spec full_descriptor S C (spec_object_get_prop a2 a3) y1 ->
        red_expr S C (spec_object_has_prop_2 y1) oo ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq object_loc l a2 ->
        @eq prop_name x a3 -> @eq out o oo -> P S C a1 a2 a3 oo) ->
       red_expr S C (spec_object_has_prop_1 a1 a2 a3) oo -> P S C a1 a2 a3 oo.

Parameter inv_red_expr_spec_object_has_prop_2
     : forall (S : state) (C : execution_ctx) (a1 : specret full_descriptor)
         (oo : out)
         (P : state ->
              execution_ctx -> specret full_descriptor -> out -> Prop),
       (red_expr S C (spec_object_has_prop_2 a1) oo ->
        forall (S0 : state) (C0 : execution_ctx) (exte : ext_expr) (o : out),
        @eq (option out) (out_of_ext_expr (spec_object_has_prop_2 a1))
          (@Some out oo) ->
        abort oo ->
        not (abort_intercepted_expr (spec_object_has_prop_2 a1)) ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq ext_expr exte (spec_object_has_prop_2 a1) ->
        @eq out o oo -> P S C a1 oo) ->
       (red_expr S C (spec_object_has_prop_2 a1) oo ->
        forall (S0 S1 : state) (C0 : execution_ctx) 
          (D : full_descriptor) (b : bool),
        @eq bool b
          match
            classicT (@eq full_descriptor D full_descriptor_undef)
            return bool
          with
          | left _ => false
          | right _ => true
          end ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq (specret full_descriptor) (@ret full_descriptor S1 D) a1 ->
        @eq out (out_ter S1 (res_val (value_prim (prim_bool b)))) oo ->
        P S C (@ret full_descriptor S1 D)
          (out_ter S1 (res_val (value_prim (prim_bool b))))) ->
       red_expr S C (spec_object_has_prop_2 a1) oo -> P S C a1 oo.

Parameter inv_red_expr_spec_object_delete
     : forall (S : state) (C : execution_ctx) (a1 : object_loc)
         (a2 : prop_name) (a3 : bool) (oo : out)
         (P : state ->
              execution_ctx -> object_loc -> string -> bool -> out -> Prop),
       (red_expr S C (spec_object_delete a1 a2 a3) oo ->
        forall (S0 : state) (C0 : execution_ctx) (exte : ext_expr) (o : out),
        @eq (option out) (out_of_ext_expr (spec_object_delete a1 a2 a3))
          (@Some out oo) ->
        abort oo ->
        not (abort_intercepted_expr (spec_object_delete a1 a2 a3)) ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq ext_expr exte (spec_object_delete a1 a2 a3) ->
        @eq out o oo -> P S C a1 a2 a3 oo) ->
       (red_expr S C (spec_object_delete a1 a2 a3) oo ->
        forall (S0 : state) (C0 : execution_ctx) (l : object_loc)
          (x : prop_name) (throw : bool) (B : builtin_delete) 
          (o : out),
        @object_method builtin_delete object_delete_ S a1 B ->
        red_expr S C (spec_object_delete_1 B a1 a2 a3) oo ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq object_loc l a1 ->
        @eq prop_name x a2 ->
        @eq bool throw a3 -> @eq out o oo -> P S C a1 a2 a3 oo) ->
       red_expr S C (spec_object_delete a1 a2 a3) oo -> P S C a1 a2 a3 oo.

Parameter inv_red_expr_spec_object_delete_1
     : forall (S : state) (C : execution_ctx) (a1 : builtin_delete)
         (a2 : object_loc) (a3 : prop_name) (a4 : bool) 
         (oo : out)
         (P : state ->
              execution_ctx ->
              builtin_delete -> object_loc -> string -> bool -> out -> Prop),
       (red_expr S C (spec_object_delete_1 a1 a2 a3 a4) oo ->
        forall (S0 : state) (C0 : execution_ctx) (exte : ext_expr) (o : out),
        @eq (option out) (out_of_ext_expr (spec_object_delete_1 a1 a2 a3 a4))
          (@Some out oo) ->
        abort oo ->
        not (abort_intercepted_expr (spec_object_delete_1 a1 a2 a3 a4)) ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq ext_expr exte (spec_object_delete_1 a1 a2 a3 a4) ->
        @eq out o oo -> P S C a1 a2 a3 a4 oo) ->
       (red_expr S C (spec_object_delete_1 a1 a2 a3 a4) oo ->
        forall (S0 : state) (C0 : execution_ctx) (l : object_loc)
          (x : prop_name) (throw : bool) (o : out)
          (y : specret full_descriptor),
        @red_spec full_descriptor S C (spec_object_get_own_prop a2 a3) y ->
        red_expr S C (spec_object_delete_2 a2 a3 a4 y) oo ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq builtin_delete builtin_delete_default a1 ->
        @eq object_loc l a2 ->
        @eq prop_name x a3 ->
        @eq bool throw a4 ->
        @eq out o oo -> P S C builtin_delete_default a2 a3 a4 oo) ->
       (red_expr S C (spec_object_delete_1 a1 a2 a3 a4) oo ->
        forall (lmap : object_loc) (S0 : state) (C0 : execution_ctx)
          (l : object_loc) (x : prop_name) (throw : bool) 
          (o : out) (y : specret full_descriptor),
        @object_method (option object_loc) object_parameter_map_ S a2
          (@Some object_loc lmap) ->
        @red_spec full_descriptor S C (spec_object_get_own_prop lmap a3) y ->
        red_expr S C (spec_args_obj_delete_1 a2 a3 a4 lmap y) oo ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq builtin_delete builtin_delete_args_obj a1 ->
        @eq object_loc l a2 ->
        @eq prop_name x a3 ->
        @eq bool throw a4 ->
        @eq out o oo -> P S C builtin_delete_args_obj a2 a3 a4 oo) ->
       red_expr S C (spec_object_delete_1 a1 a2 a3 a4) oo ->
       P S C a1 a2 a3 a4 oo.

Parameter inv_red_expr_spec_object_delete_2
     : forall (S : state) (C : execution_ctx) (a1 : object_loc)
         (a2 : prop_name) (a3 : bool) (a4 : specret full_descriptor)
         (oo : out)
         (P : state ->
              execution_ctx ->
              object_loc ->
              string -> bool -> specret full_descriptor -> out -> Prop),
       (red_expr S C (spec_object_delete_2 a1 a2 a3 a4) oo ->
        forall (S0 : state) (C0 : execution_ctx) (exte : ext_expr) (o : out),
        @eq (option out) (out_of_ext_expr (spec_object_delete_2 a1 a2 a3 a4))
          (@Some out oo) ->
        abort oo ->
        not (abort_intercepted_expr (spec_object_delete_2 a1 a2 a3 a4)) ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq ext_expr exte (spec_object_delete_2 a1 a2 a3 a4) ->
        @eq out o oo -> P S C a1 a2 a3 a4 oo) ->
       (red_expr S C (spec_object_delete_2 a1 a2 a3 a4) oo ->
        forall (S0 S1 : state) (C0 : execution_ctx) 
          (l : object_loc) (x : prop_name) (throw : bool),
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq object_loc l a1 ->
        @eq prop_name x a2 ->
        @eq bool throw a3 ->
        @eq (specret full_descriptor)
          (@ret full_descriptor S1 full_descriptor_undef) a4 ->
        @eq out (out_ter S1 (res_val (value_prim (prim_bool true)))) oo ->
        P S C a1 a2 a3 (@ret full_descriptor S1 full_descriptor_undef)
          (out_ter S1 (res_val (value_prim (prim_bool true))))) ->
       (red_expr S C (spec_object_delete_2 a1 a2 a3 a4) oo ->
        forall (S0 S1 : state) (C0 : execution_ctx) 
          (l : object_loc) (x : prop_name) (throw : bool) 
          (A : attributes) (S' : state),
        @eq bool (attributes_configurable A) true ->
        object_rem_property S1 a1 a2 S' ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq object_loc l a1 ->
        @eq prop_name x a2 ->
        @eq bool throw a3 ->
        @eq (specret full_descriptor)
          (@ret full_descriptor S1 (full_descriptor_some A)) a4 ->
        @eq out (out_ter S' (res_val (value_prim (prim_bool true)))) oo ->
        P S C a1 a2 a3 (@ret full_descriptor S1 (full_descriptor_some A))
          (out_ter S' (res_val (value_prim (prim_bool true))))) ->
       (red_expr S C (spec_object_delete_2 a1 a2 a3 a4) oo ->
        forall (S0 S1 : state) (C0 : execution_ctx) 
          (l : object_loc) (x : prop_name) (throw : bool) 
          (A : attributes) (o : out),
        @eq bool (attributes_configurable A) false ->
        red_expr S1 C
          (spec_error_or_cst a3 native_error_type
             (value_prim (prim_bool false))) oo ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq object_loc l a1 ->
        @eq prop_name x a2 ->
        @eq bool throw a3 ->
        @eq (specret full_descriptor)
          (@ret full_descriptor S1 (full_descriptor_some A)) a4 ->
        @eq out o oo ->
        P S C a1 a2 a3 (@ret full_descriptor S1 (full_descriptor_some A)) oo) ->
       red_expr S C (spec_object_delete_2 a1 a2 a3 a4) oo ->
       P S C a1 a2 a3 a4 oo.

Parameter inv_red_expr_spec_object_delete_3
     : forall (S : state) (C : execution_ctx) (a1 : object_loc)
         (a2 : prop_name) (a3 a4 : bool) (oo : out)
         (P : state ->
              execution_ctx ->
              object_loc -> string -> bool -> bool -> out -> Prop),
       (red_expr S C (spec_object_delete_3 a1 a2 a3 a4) oo ->
        forall (S0 : state) (C0 : execution_ctx) (exte : ext_expr) (o : out),
        @eq (option out) (out_of_ext_expr (spec_object_delete_3 a1 a2 a3 a4))
          (@Some out oo) ->
        abort oo ->
        not (abort_intercepted_expr (spec_object_delete_3 a1 a2 a3 a4)) ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq ext_expr exte (spec_object_delete_3 a1 a2 a3 a4) ->
        @eq out o oo -> P S C a1 a2 a3 a4 oo) ->
       red_expr S C (spec_object_delete_3 a1 a2 a3 a4) oo ->
       P S C a1 a2 a3 a4 oo.

Parameter inv_red_expr_spec_object_default_value
     : forall (S : state) (C : execution_ctx) (a1 : object_loc)
         (a2 : option preftype) (oo : out)
         (P : state ->
              execution_ctx -> object_loc -> option preftype -> out -> Prop),
       (red_expr S C (spec_object_default_value a1 a2) oo ->
        forall (S0 : state) (C0 : execution_ctx) (exte : ext_expr) (o : out),
        @eq (option out) (out_of_ext_expr (spec_object_default_value a1 a2))
          (@Some out oo) ->
        abort oo ->
        not (abort_intercepted_expr (spec_object_default_value a1 a2)) ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq ext_expr exte (spec_object_default_value a1 a2) ->
        @eq out o oo -> P S C a1 a2 oo) ->
       (red_expr S C (spec_object_default_value a1 a2) oo ->
        forall (S0 : state) (C0 : execution_ctx) (l : object_loc)
          (prefo : option preftype) (B : builtin_default_value) 
          (o : out),
        @object_method builtin_default_value object_default_value_ S a1 B ->
        red_expr S C (spec_object_default_value_1 B a1 a2) oo ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq object_loc l a1 ->
        @eq (option preftype) prefo a2 -> @eq out o oo -> P S C a1 a2 oo) ->
       red_expr S C (spec_object_default_value a1 a2) oo -> P S C a1 a2 oo.

Parameter inv_red_expr_spec_object_default_value_1
     : forall (S : state) (C : execution_ctx) (a1 : builtin_default_value)
         (a2 : object_loc) (a3 : option preftype) (oo : out)
         (P : state ->
              execution_ctx ->
              builtin_default_value ->
              object_loc -> option preftype -> out -> Prop),
       (red_expr S C (spec_object_default_value_1 a1 a2 a3) oo ->
        forall (S0 : state) (C0 : execution_ctx) (exte : ext_expr) (o : out),
        @eq (option out)
          (out_of_ext_expr (spec_object_default_value_1 a1 a2 a3))
          (@Some out oo) ->
        abort oo ->
        not (abort_intercepted_expr (spec_object_default_value_1 a1 a2 a3)) ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq ext_expr exte (spec_object_default_value_1 a1 a2 a3) ->
        @eq out o oo -> P S C a1 a2 a3 oo) ->
       (red_expr S C (spec_object_default_value_1 a1 a2 a3) oo ->
        forall (S0 : state) (C0 : execution_ctx) (l : object_loc)
          (prefo : option preftype) (pref : preftype) 
          (o : out),
        @eq preftype pref (@unsome_default preftype preftype_number a3) ->
        red_expr S C
          (spec_object_default_value_2 a2 pref (other_preftypes pref)) oo ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq object_loc l a2 ->
        @eq (option preftype) prefo a3 -> @eq out o oo -> P S C a1 a2 a3 oo) ->
       red_expr S C (spec_object_default_value_1 a1 a2 a3) oo ->
       P S C a1 a2 a3 oo.

Parameter inv_red_expr_spec_object_default_value_2
     : forall (S : state) (C : execution_ctx) (a1 : object_loc)
         (a2 a3 : preftype) (oo : out)
         (P : state ->
              execution_ctx ->
              object_loc -> preftype -> preftype -> out -> Prop),
       (red_expr S C (spec_object_default_value_2 a1 a2 a3) oo ->
        forall (S0 : state) (C0 : execution_ctx) (exte : ext_expr) (o : out),
        @eq (option out)
          (out_of_ext_expr (spec_object_default_value_2 a1 a2 a3))
          (@Some out oo) ->
        abort oo ->
        not (abort_intercepted_expr (spec_object_default_value_2 a1 a2 a3)) ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq ext_expr exte (spec_object_default_value_2 a1 a2 a3) ->
        @eq out o oo -> P S C a1 a2 a3 oo) ->
       (red_expr S C (spec_object_default_value_2 a1 a2 a3) oo ->
        forall (S0 : state) (C0 : execution_ctx) (l : object_loc)
          (pref1 pref2 : preftype) (o : out),
        red_expr S C
          (spec_object_default_value_sub_1 a1 (method_of_preftype a2)
             (spec_object_default_value_3 a1 a3)) oo ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq object_loc l a1 ->
        @eq preftype pref1 a2 ->
        @eq preftype pref2 a3 -> @eq out o oo -> P S C a1 a2 a3 oo) ->
       red_expr S C (spec_object_default_value_2 a1 a2 a3) oo ->
       P S C a1 a2 a3 oo.

Parameter inv_red_expr_spec_object_default_value_3
     : forall (S : state) (C : execution_ctx) (a1 : object_loc)
         (a2 : preftype) (oo : out)
         (P : state -> execution_ctx -> object_loc -> preftype -> out -> Prop),
       (red_expr S C (spec_object_default_value_3 a1 a2) oo ->
        forall (S0 : state) (C0 : execution_ctx) (exte : ext_expr) (o : out),
        @eq (option out)
          (out_of_ext_expr (spec_object_default_value_3 a1 a2))
          (@Some out oo) ->
        abort oo ->
        not (abort_intercepted_expr (spec_object_default_value_3 a1 a2)) ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq ext_expr exte (spec_object_default_value_3 a1 a2) ->
        @eq out o oo -> P S C a1 a2 oo) ->
       (red_expr S C (spec_object_default_value_3 a1 a2) oo ->
        forall (S0 : state) (C0 : execution_ctx) (l : object_loc)
          (pref2 : preftype) (o : out),
        red_expr S C
          (spec_object_default_value_sub_1 a1 (method_of_preftype a2)
             spec_object_default_value_4) oo ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq object_loc l a1 ->
        @eq preftype pref2 a2 -> @eq out o oo -> P S C a1 a2 oo) ->
       red_expr S C (spec_object_default_value_3 a1 a2) oo -> P S C a1 a2 oo.

Parameter inv_red_expr_spec_object_default_value_4
     : forall (S : state) (C : execution_ctx) (oo : out)
         (P : state -> execution_ctx -> out -> Prop),
       (red_expr S C spec_object_default_value_4 oo ->
        forall (S0 : state) (C0 : execution_ctx) (exte : ext_expr) (o : out),
        @eq (option out) (out_of_ext_expr spec_object_default_value_4)
          (@Some out oo) ->
        abort oo ->
        not (abort_intercepted_expr spec_object_default_value_4) ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq ext_expr exte spec_object_default_value_4 ->
        @eq out o oo -> P S C oo) ->
       (red_expr S C spec_object_default_value_4 oo ->
        forall (S0 : state) (C0 : execution_ctx) (o : out),
        red_expr S C (spec_error native_error_type) oo ->
        @eq state S0 S -> @eq execution_ctx C0 C -> @eq out o oo -> P S C oo) ->
       red_expr S C spec_object_default_value_4 oo -> P S C oo.

Parameter inv_red_expr_spec_object_default_value_sub_1
     : forall (S : state) (C : execution_ctx) (a1 : object_loc) 
         (a2 : string) (a3 : ext_expr) (oo : out)
         (P : state ->
              execution_ctx ->
              object_loc -> string -> ext_expr -> out -> Prop),
       (red_expr S C (spec_object_default_value_sub_1 a1 a2 a3) oo ->
        forall (S0 : state) (C0 : execution_ctx) (exte : ext_expr) (o : out),
        @eq (option out)
          (out_of_ext_expr (spec_object_default_value_sub_1 a1 a2 a3))
          (@Some out oo) ->
        abort oo ->
        not
          (abort_intercepted_expr (spec_object_default_value_sub_1 a1 a2 a3)) ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq ext_expr exte (spec_object_default_value_sub_1 a1 a2 a3) ->
        @eq out o oo -> P S C a1 a2 a3 oo) ->
       (red_expr S C (spec_object_default_value_sub_1 a1 a2 a3) oo ->
        forall (o1 : out) (S0 : state) (C0 : execution_ctx) 
          (l : object_loc) (x : prop_name) (K : ext_expr) 
          (o : out),
        red_expr S C (spec_object_get a1 a2) o1 ->
        red_expr S C (spec_object_default_value_sub_2 a1 o1 a3) oo ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq object_loc l a1 ->
        @eq string x a2 ->
        @eq ext_expr K a3 -> @eq out o oo -> P S C a1 a2 a3 oo) ->
       red_expr S C (spec_object_default_value_sub_1 a1 a2 a3) oo ->
       P S C a1 a2 a3 oo.

Parameter inv_red_expr_spec_object_default_value_sub_2
     : forall (S : state) (C : execution_ctx) (a1 : object_loc) 
         (a2 : out) (a3 : ext_expr) (oo : out)
         (P : state ->
              execution_ctx -> object_loc -> out -> ext_expr -> out -> Prop),
       (red_expr S C (spec_object_default_value_sub_2 a1 a2 a3) oo ->
        forall (S0 : state) (C0 : execution_ctx) (exte : ext_expr) (o : out),
        @eq (option out)
          (out_of_ext_expr (spec_object_default_value_sub_2 a1 a2 a3))
          (@Some out oo) ->
        abort oo ->
        not
          (abort_intercepted_expr (spec_object_default_value_sub_2 a1 a2 a3)) ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq ext_expr exte (spec_object_default_value_sub_2 a1 a2 a3) ->
        @eq out o oo -> P S C a1 a2 a3 oo) ->
       (red_expr S C (spec_object_default_value_sub_2 a1 a2 a3) oo ->
        forall (S0 S1 : state) (C0 : execution_ctx) 
          (l : object_loc) (v : value) (K : ext_expr) 
          (o : out),
        callable S1 v (@None call) ->
        red_expr S1 C a3 oo ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq object_loc l a1 ->
        @eq out (out_ter S1 (res_val v)) a2 ->
        @eq ext_expr K a3 ->
        @eq out o oo -> P S C a1 (out_ter S1 (res_val v)) a3 oo) ->
       (red_expr S C (spec_object_default_value_sub_2 a1 a2 a3) oo ->
        forall (S0 S1 : state) (C0 : execution_ctx) 
          (lfunc l : object_loc) (v : value) (K : ext_expr) 
          (o : out) (B : call) (o1 : out),
        callable S1 v (@Some call B) ->
        @eq value v (value_object lfunc) ->
        red_expr S1 C (spec_call lfunc (value_object a1) (@nil value)) o1 ->
        red_expr S1 C (spec_object_default_value_sub_3 o1 a3) oo ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq object_loc l a1 ->
        @eq out (out_ter S1 (res_val v)) a2 ->
        @eq ext_expr K a3 ->
        @eq out o oo -> P S C a1 (out_ter S1 (res_val v)) a3 oo) ->
       red_expr S C (spec_object_default_value_sub_2 a1 a2 a3) oo ->
       P S C a1 a2 a3 oo.

Parameter inv_red_expr_spec_object_default_value_sub_3
     : forall (S : state) (C : execution_ctx) (a1 : out) 
         (a2 : ext_expr) (oo : out)
         (P : state -> execution_ctx -> out -> ext_expr -> out -> Prop),
       (red_expr S C (spec_object_default_value_sub_3 a1 a2) oo ->
        forall (S0 : state) (C0 : execution_ctx) (exte : ext_expr) (o : out),
        @eq (option out)
          (out_of_ext_expr (spec_object_default_value_sub_3 a1 a2))
          (@Some out oo) ->
        abort oo ->
        not (abort_intercepted_expr (spec_object_default_value_sub_3 a1 a2)) ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq ext_expr exte (spec_object_default_value_sub_3 a1 a2) ->
        @eq out o oo -> P S C a1 a2 oo) ->
       (red_expr S C (spec_object_default_value_sub_3 a1 a2) oo ->
        forall (S0 S1 : state) (C0 : execution_ctx) (K : ext_expr) (w : prim),
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq out (out_ter S1 (res_val (value_prim w))) a1 ->
        @eq ext_expr K a2 ->
        @eq out (out_ter S1 (res_val (value_prim w))) oo ->
        P S C (out_ter S1 (res_val (value_prim w))) a2
          (out_ter S1 (res_val (value_prim w)))) ->
       (red_expr S C (spec_object_default_value_sub_3 a1 a2) oo ->
        forall (S0 S1 : state) (C0 : execution_ctx) 
          (l : object_loc) (K : ext_expr) (o : out),
        red_expr S1 C a2 oo ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq out (out_ter S1 (res_val (value_object l))) a1 ->
        @eq ext_expr K a2 ->
        @eq out o oo -> P S C (out_ter S1 (res_val (value_object l))) a2 oo) ->
       red_expr S C (spec_object_default_value_sub_3 a1 a2) oo ->
       P S C a1 a2 oo.

Parameter inv_red_expr_spec_object_define_own_prop
     : forall (S : state) (C : execution_ctx) (a1 : object_loc)
         (a2 : prop_name) (a3 : descriptor) (a4 : bool) 
         (oo : out)
         (P : state ->
              execution_ctx ->
              object_loc -> string -> descriptor -> bool -> out -> Prop),
       (red_expr S C (spec_object_define_own_prop a1 a2 a3 a4) oo ->
        forall (S0 : state) (C0 : execution_ctx) (exte : ext_expr) (o : out),
        @eq (option out)
          (out_of_ext_expr (spec_object_define_own_prop a1 a2 a3 a4))
          (@Some out oo) ->
        abort oo ->
        not
          (abort_intercepted_expr (spec_object_define_own_prop a1 a2 a3 a4)) ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq ext_expr exte (spec_object_define_own_prop a1 a2 a3 a4) ->
        @eq out o oo -> P S C a1 a2 a3 a4 oo) ->
       (red_expr S C (spec_object_define_own_prop a1 a2 a3 a4) oo ->
        forall (S0 : state) (C0 : execution_ctx) (l : object_loc)
          (x : prop_name) (Desc : descriptor) (throw : bool)
          (B : builtin_define_own_prop) (o : out),
        @object_method builtin_define_own_prop object_define_own_prop_ S a1 B ->
        red_expr S C (spec_object_define_own_prop_1 B a1 a2 a3 a4) oo ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq object_loc l a1 ->
        @eq prop_name x a2 ->
        @eq descriptor Desc a3 ->
        @eq bool throw a4 -> @eq out o oo -> P S C a1 a2 a3 a4 oo) ->
       red_expr S C (spec_object_define_own_prop a1 a2 a3 a4) oo ->
       P S C a1 a2 a3 a4 oo.

Parameter inv_red_expr_spec_object_define_own_prop_1
     : forall (S : state) (C : execution_ctx) (a1 : builtin_define_own_prop)
         (a2 : object_loc) (a3 : prop_name) (a4 : descriptor) 
         (a5 : bool) (oo : out)
         (P : state ->
              execution_ctx ->
              builtin_define_own_prop ->
              object_loc -> string -> descriptor -> bool -> out -> Prop),
       (red_expr S C (spec_object_define_own_prop_1 a1 a2 a3 a4 a5) oo ->
        forall (S0 : state) (C0 : execution_ctx) (exte : ext_expr) (o : out),
        @eq (option out)
          (out_of_ext_expr (spec_object_define_own_prop_1 a1 a2 a3 a4 a5))
          (@Some out oo) ->
        abort oo ->
        not
          (abort_intercepted_expr
             (spec_object_define_own_prop_1 a1 a2 a3 a4 a5)) ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq ext_expr exte (spec_object_define_own_prop_1 a1 a2 a3 a4 a5) ->
        @eq out o oo -> P S C a1 a2 a3 a4 a5 oo) ->
       (red_expr S C (spec_object_define_own_prop_1 a1 a2 a3 a4 a5) oo ->
        forall (S0 : state) (C0 : execution_ctx) (l : object_loc)
          (x : prop_name) (Desc : descriptor) (throw : bool) 
          (o : out) (y : specret full_descriptor),
        @red_spec full_descriptor S C (spec_object_get_own_prop a2 a3) y ->
        red_expr S C (spec_object_define_own_prop_2 a2 a3 a4 a5 y) oo ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq builtin_define_own_prop builtin_define_own_prop_default a1 ->
        @eq object_loc l a2 ->
        @eq prop_name x a3 ->
        @eq descriptor Desc a4 ->
        @eq bool throw a5 ->
        @eq out o oo -> P S C builtin_define_own_prop_default a2 a3 a4 a5 oo) ->
       (red_expr S C (spec_object_define_own_prop_1 a1 a2 a3 a4 a5) oo ->
        forall (S0 : state) (C0 : execution_ctx) (l : object_loc)
          (Desc : descriptor) (x : prop_name) (throw : bool) 
          (o : out) (y : specret full_descriptor),
        @red_spec full_descriptor S C
          (spec_object_get_own_prop a2
             (String (Ascii false false true true false true true false)
                (String (Ascii true false true false false true true false)
                   (String (Ascii false true true true false true true false)
                      (String
                         (Ascii true true true false false true true false)
                         (String
                            (Ascii false false true false true true true
                               false)
                            (String
                               (Ascii false false false true false true true
                                  false) EmptyString))))))) y ->
        red_expr S C (spec_object_define_own_prop_array_2 a2 a3 a4 a5 y) oo ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq builtin_define_own_prop builtin_define_own_prop_array a1 ->
        @eq object_loc l a2 ->
        @eq prop_name x a3 ->
        @eq descriptor Desc a4 ->
        @eq bool throw a5 ->
        @eq out o oo -> P S C builtin_define_own_prop_array a2 a3 a4 a5 oo) ->
       (red_expr S C (spec_object_define_own_prop_1 a1 a2 a3 a4 a5) oo ->
        forall (lmap : object_loc) (S0 : state) (C0 : execution_ctx)
          (l : object_loc) (x : prop_name) (Desc : descriptor) 
          (throw : bool) (o : out) (y : specret full_descriptor),
        @object_method (option object_loc) object_parameter_map_ S a2
          (@Some object_loc lmap) ->
        @red_spec full_descriptor S C (spec_object_get_own_prop lmap a3) y ->
        red_expr S C (spec_args_obj_define_own_prop_1 a2 a3 a4 a5 lmap y) oo ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq builtin_define_own_prop builtin_define_own_prop_args_obj a1 ->
        @eq object_loc l a2 ->
        @eq prop_name x a3 ->
        @eq descriptor Desc a4 ->
        @eq bool throw a5 ->
        @eq out o oo -> P S C builtin_define_own_prop_args_obj a2 a3 a4 a5 oo) ->
       red_expr S C (spec_object_define_own_prop_1 a1 a2 a3 a4 a5) oo ->
       P S C a1 a2 a3 a4 a5 oo.

Parameter inv_red_expr_spec_object_define_own_prop_2
     : forall (S : state) (C : execution_ctx) (a1 : object_loc)
         (a2 : prop_name) (a3 : descriptor) (a4 : bool)
         (a5 : specret full_descriptor) (oo : out)
         (P : state ->
              execution_ctx ->
              object_loc ->
              string ->
              descriptor -> bool -> specret full_descriptor -> out -> Prop),
       (red_expr S C (spec_object_define_own_prop_2 a1 a2 a3 a4 a5) oo ->
        forall (S0 : state) (C0 : execution_ctx) (exte : ext_expr) (o : out),
        @eq (option out)
          (out_of_ext_expr (spec_object_define_own_prop_2 a1 a2 a3 a4 a5))
          (@Some out oo) ->
        abort oo ->
        not
          (abort_intercepted_expr
             (spec_object_define_own_prop_2 a1 a2 a3 a4 a5)) ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq ext_expr exte (spec_object_define_own_prop_2 a1 a2 a3 a4 a5) ->
        @eq out o oo -> P S C a1 a2 a3 a4 a5 oo) ->
       (red_expr S C (spec_object_define_own_prop_2 a1 a2 a3 a4 a5) oo ->
        forall (S0 S1 : state) (C0 : execution_ctx) 
          (l : object_loc) (x : prop_name) (Desc : descriptor) 
          (throw : bool) (D : full_descriptor) (bext : bool) 
          (o : out),
        object_extensible S1 a1 bext ->
        red_expr S1 C (spec_object_define_own_prop_3 a1 a2 a3 a4 D bext) oo ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq object_loc l a1 ->
        @eq prop_name x a2 ->
        @eq descriptor Desc a3 ->
        @eq bool throw a4 ->
        @eq (specret full_descriptor) (@ret full_descriptor S1 D) a5 ->
        @eq out o oo -> P S C a1 a2 a3 a4 (@ret full_descriptor S1 D) oo) ->
       red_expr S C (spec_object_define_own_prop_2 a1 a2 a3 a4 a5) oo ->
       P S C a1 a2 a3 a4 a5 oo.

Parameter inv_red_expr_spec_object_define_own_prop_3
     : forall (S : state) (C : execution_ctx) (a1 : object_loc)
         (a2 : prop_name) (a3 : descriptor) (a4 : bool)
         (a5 : full_descriptor) (a6 : bool) (oo : out)
         (P : state ->
              execution_ctx ->
              object_loc ->
              string ->
              descriptor -> bool -> full_descriptor -> bool -> out -> Prop),
       (red_expr S C (spec_object_define_own_prop_3 a1 a2 a3 a4 a5 a6) oo ->
        forall (S0 : state) (C0 : execution_ctx) (exte : ext_expr) (o : out),
        @eq (option out)
          (out_of_ext_expr (spec_object_define_own_prop_3 a1 a2 a3 a4 a5 a6))
          (@Some out oo) ->
        abort oo ->
        not
          (abort_intercepted_expr
             (spec_object_define_own_prop_3 a1 a2 a3 a4 a5 a6)) ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq ext_expr exte (spec_object_define_own_prop_3 a1 a2 a3 a4 a5 a6) ->
        @eq out o oo -> P S C a1 a2 a3 a4 a5 a6 oo) ->
       (red_expr S C (spec_object_define_own_prop_3 a1 a2 a3 a4 a5 a6) oo ->
        forall (S0 : state) (C0 : execution_ctx) (l : object_loc)
          (x : prop_name) (Desc : descriptor) (throw : bool) 
          (o : out),
        red_expr S C (spec_object_define_own_prop_reject a4) oo ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq object_loc l a1 ->
        @eq prop_name x a2 ->
        @eq descriptor Desc a3 ->
        @eq bool throw a4 ->
        @eq full_descriptor full_descriptor_undef a5 ->
        @eq bool false a6 ->
        @eq out o oo -> P S C a1 a2 a3 a4 full_descriptor_undef false oo) ->
       (red_expr S C (spec_object_define_own_prop_3 a1 a2 a3 a4 a5 a6) oo ->
        forall (S0 : state) (C0 : execution_ctx) (l : object_loc)
          (x : prop_name) (Desc : descriptor) (throw : bool) 
          (A : attributes) (S' : state),
        @eq attributes A
          match
            classicT
              (Logic.or (descriptor_is_generic a3) (descriptor_is_data a3))
            return attributes
          with
          | left _ => attributes_data_of (attributes_data_of_descriptor a3)
          | right _ =>
              attributes_accessor_of (attributes_accessor_of_descriptor a3)
          end ->
        object_set_property S a1 a2 A S' ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq object_loc l a1 ->
        @eq prop_name x a2 ->
        @eq descriptor Desc a3 ->
        @eq bool throw a4 ->
        @eq full_descriptor full_descriptor_undef a5 ->
        @eq bool true a6 ->
        @eq out (out_ter S' (res_val (value_prim (prim_bool true)))) oo ->
        P S C a1 a2 a3 a4 full_descriptor_undef true
          (out_ter S' (res_val (value_prim (prim_bool true))))) ->
       (red_expr S C (spec_object_define_own_prop_3 a1 a2 a3 a4 a5 a6) oo ->
        forall (S0 : state) (C0 : execution_ctx) (l : object_loc)
          (x : prop_name) (A : attributes) (Desc : descriptor)
          (throw bext : bool),
        descriptor_contains (descriptor_of_attributes A) a3 ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq object_loc l a1 ->
        @eq prop_name x a2 ->
        @eq descriptor Desc a3 ->
        @eq bool throw a4 ->
        @eq full_descriptor (full_descriptor_some A) a5 ->
        @eq bool bext a6 ->
        @eq out (out_ter S (res_val (value_prim (prim_bool true)))) oo ->
        P S C a1 a2 a3 a4 (full_descriptor_some A) a6
          (out_ter S (res_val (value_prim (prim_bool true))))) ->
       (red_expr S C (spec_object_define_own_prop_3 a1 a2 a3 a4 a5 a6) oo ->
        forall (S0 : state) (C0 : execution_ctx) (l : object_loc)
          (x : prop_name) (A : attributes) (Desc : descriptor) 
          (throw : bool) (o : out) (bext : bool),
        not (descriptor_contains (descriptor_of_attributes A) a3) ->
        red_expr S C (spec_object_define_own_prop_4 a1 a2 A a3 a4) oo ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq object_loc l a1 ->
        @eq prop_name x a2 ->
        @eq descriptor Desc a3 ->
        @eq bool throw a4 ->
        @eq full_descriptor (full_descriptor_some A) a5 ->
        @eq bool bext a6 ->
        @eq out o oo -> P S C a1 a2 a3 a4 (full_descriptor_some A) a6 oo) ->
       red_expr S C (spec_object_define_own_prop_3 a1 a2 a3 a4 a5 a6) oo ->
       P S C a1 a2 a3 a4 a5 a6 oo.

Parameter inv_red_expr_spec_object_define_own_prop_4
     : forall (S : state) (C : execution_ctx) (a1 : object_loc)
         (a2 : prop_name) (a3 : attributes) (a4 : descriptor) 
         (a5 : bool) (oo : out)
         (P : state ->
              execution_ctx ->
              object_loc ->
              string -> attributes -> descriptor -> bool -> out -> Prop),
       (red_expr S C (spec_object_define_own_prop_4 a1 a2 a3 a4 a5) oo ->
        forall (S0 : state) (C0 : execution_ctx) (exte : ext_expr) (o : out),
        @eq (option out)
          (out_of_ext_expr (spec_object_define_own_prop_4 a1 a2 a3 a4 a5))
          (@Some out oo) ->
        abort oo ->
        not
          (abort_intercepted_expr
             (spec_object_define_own_prop_4 a1 a2 a3 a4 a5)) ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq ext_expr exte (spec_object_define_own_prop_4 a1 a2 a3 a4 a5) ->
        @eq out o oo -> P S C a1 a2 a3 a4 a5 oo) ->
       (red_expr S C (spec_object_define_own_prop_4 a1 a2 a3 a4 a5) oo ->
        forall (S0 : state) (C0 : execution_ctx) (l : object_loc)
          (x : prop_name) (A : attributes) (Desc : descriptor) 
          (throw : bool) (o : out),
        attributes_change_enumerable_on_non_configurable a3 a4 ->
        red_expr S C (spec_object_define_own_prop_reject a5) oo ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq object_loc l a1 ->
        @eq prop_name x a2 ->
        @eq attributes A a3 ->
        @eq descriptor Desc a4 ->
        @eq bool throw a5 -> @eq out o oo -> P S C a1 a2 a3 a4 a5 oo) ->
       (red_expr S C (spec_object_define_own_prop_4 a1 a2 a3 a4 a5) oo ->
        forall (S0 : state) (C0 : execution_ctx) (l : object_loc)
          (x : prop_name) (A : attributes) (Desc : descriptor) 
          (throw : bool) (o : out),
        not (attributes_change_enumerable_on_non_configurable a3 a4) ->
        red_expr S C (spec_object_define_own_prop_5 a1 a2 a3 a4 a5) oo ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq object_loc l a1 ->
        @eq prop_name x a2 ->
        @eq attributes A a3 ->
        @eq descriptor Desc a4 ->
        @eq bool throw a5 -> @eq out o oo -> P S C a1 a2 a3 a4 a5 oo) ->
       red_expr S C (spec_object_define_own_prop_4 a1 a2 a3 a4 a5) oo ->
       P S C a1 a2 a3 a4 a5 oo.

Parameter inv_red_expr_spec_object_define_own_prop_5
     : forall (S : state) (C : execution_ctx) (a1 : object_loc)
         (a2 : prop_name) (a3 : attributes) (a4 : descriptor) 
         (a5 : bool) (oo : out)
         (P : state ->
              execution_ctx ->
              object_loc ->
              string -> attributes -> descriptor -> bool -> out -> Prop),
       (red_expr S C (spec_object_define_own_prop_5 a1 a2 a3 a4 a5) oo ->
        forall (S0 : state) (C0 : execution_ctx) (exte : ext_expr) (o : out),
        @eq (option out)
          (out_of_ext_expr (spec_object_define_own_prop_5 a1 a2 a3 a4 a5))
          (@Some out oo) ->
        abort oo ->
        not
          (abort_intercepted_expr
             (spec_object_define_own_prop_5 a1 a2 a3 a4 a5)) ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq ext_expr exte (spec_object_define_own_prop_5 a1 a2 a3 a4 a5) ->
        @eq out o oo -> P S C a1 a2 a3 a4 a5 oo) ->
       (red_expr S C (spec_object_define_own_prop_5 a1 a2 a3 a4 a5) oo ->
        forall (S0 : state) (C0 : execution_ctx) (l : object_loc)
          (x : prop_name) (A : attributes) (Desc : descriptor) 
          (throw : bool) (o : out),
        descriptor_is_generic a4 ->
        red_expr S C (spec_object_define_own_prop_write a1 a2 a3 a4 a5) oo ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq object_loc l a1 ->
        @eq prop_name x a2 ->
        @eq attributes A a3 ->
        @eq descriptor Desc a4 ->
        @eq bool throw a5 -> @eq out o oo -> P S C a1 a2 a3 a4 a5 oo) ->
       (red_expr S C (spec_object_define_own_prop_5 a1 a2 a3 a4 a5) oo ->
        forall (S0 : state) (C0 : execution_ctx) (l : object_loc)
          (x : prop_name) (A : attributes) (Desc : descriptor) 
          (throw : bool) (o : out),
        not (@eq Prop (attributes_is_data a3) (descriptor_is_data a4)) ->
        red_expr S C (spec_object_define_own_prop_6a a1 a2 a3 a4 a5) oo ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq object_loc l a1 ->
        @eq prop_name x a2 ->
        @eq attributes A a3 ->
        @eq descriptor Desc a4 ->
        @eq bool throw a5 -> @eq out o oo -> P S C a1 a2 a3 a4 a5 oo) ->
       (red_expr S C (spec_object_define_own_prop_5 a1 a2 a3 a4 a5) oo ->
        forall (S0 : state) (C0 : execution_ctx) (l : object_loc)
          (x : prop_name) (Ad : attributes_data) (Desc : descriptor)
          (throw : bool) (o : out),
        descriptor_is_data a4 ->
        red_expr S C
          (spec_object_define_own_prop_6b a1 a2 (attributes_data_of Ad) a4 a5)
          oo ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq object_loc l a1 ->
        @eq prop_name x a2 ->
        @eq attributes (attributes_data_of Ad) a3 ->
        @eq descriptor Desc a4 ->
        @eq bool throw a5 ->
        @eq out o oo -> P S C a1 a2 (attributes_data_of Ad) a4 a5 oo) ->
       (red_expr S C (spec_object_define_own_prop_5 a1 a2 a3 a4 a5) oo ->
        forall (S0 : state) (C0 : execution_ctx) (l : object_loc)
          (x : prop_name) (Aa : attributes_accessor) 
          (Desc : descriptor) (throw : bool) (o : out),
        descriptor_is_accessor a4 ->
        red_expr S C
          (spec_object_define_own_prop_6c a1 a2 (attributes_accessor_of Aa)
             a4 a5) oo ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq object_loc l a1 ->
        @eq prop_name x a2 ->
        @eq attributes (attributes_accessor_of Aa) a3 ->
        @eq descriptor Desc a4 ->
        @eq bool throw a5 ->
        @eq out o oo -> P S C a1 a2 (attributes_accessor_of Aa) a4 a5 oo) ->
       red_expr S C (spec_object_define_own_prop_5 a1 a2 a3 a4 a5) oo ->
       P S C a1 a2 a3 a4 a5 oo.

Parameter inv_red_expr_spec_object_define_own_prop_6a
     : forall (S : state) (C : execution_ctx) (a1 : object_loc)
         (a2 : prop_name) (a3 : attributes) (a4 : descriptor) 
         (a5 : bool) (oo : out)
         (P : state ->
              execution_ctx ->
              object_loc ->
              string -> attributes -> descriptor -> bool -> out -> Prop),
       (red_expr S C (spec_object_define_own_prop_6a a1 a2 a3 a4 a5) oo ->
        forall (S0 : state) (C0 : execution_ctx) (exte : ext_expr) (o : out),
        @eq (option out)
          (out_of_ext_expr (spec_object_define_own_prop_6a a1 a2 a3 a4 a5))
          (@Some out oo) ->
        abort oo ->
        not
          (abort_intercepted_expr
             (spec_object_define_own_prop_6a a1 a2 a3 a4 a5)) ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq ext_expr exte (spec_object_define_own_prop_6a a1 a2 a3 a4 a5) ->
        @eq out o oo -> P S C a1 a2 a3 a4 a5 oo) ->
       (red_expr S C (spec_object_define_own_prop_6a a1 a2 a3 a4 a5) oo ->
        forall (S0 : state) (C0 : execution_ctx) (l : object_loc)
          (x : prop_name) (A : attributes) (Desc : descriptor) 
          (throw : bool) (o : out),
        @eq bool (attributes_configurable a3) false ->
        red_expr S C (spec_object_define_own_prop_reject a5) oo ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq object_loc l a1 ->
        @eq prop_name x a2 ->
        @eq attributes A a3 ->
        @eq descriptor Desc a4 ->
        @eq bool throw a5 -> @eq out o oo -> P S C a1 a2 a3 a4 a5 oo) ->
       (red_expr S C (spec_object_define_own_prop_6a a1 a2 a3 a4 a5) oo ->
        forall (S0 S' : state) (C0 : execution_ctx) 
          (l : object_loc) (x : prop_name) (A A' : attributes)
          (Desc : descriptor) (throw : bool) (o : out),
        @eq bool (attributes_configurable a3) true ->
        @eq attributes A'
          match a3 return attributes with
          | attributes_data_of Ad =>
              attributes_accessor_of
                (attributes_accessor_of_attributes_data Ad)
          | attributes_accessor_of Aa =>
              attributes_data_of (attributes_data_of_attributes_accessor Aa)
          end ->
        object_set_property S a1 a2 A' S' ->
        red_expr S' C (spec_object_define_own_prop_write a1 a2 A' a4 a5) oo ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq object_loc l a1 ->
        @eq prop_name x a2 ->
        @eq attributes A a3 ->
        @eq descriptor Desc a4 ->
        @eq bool throw a5 -> @eq out o oo -> P S C a1 a2 a3 a4 a5 oo) ->
       red_expr S C (spec_object_define_own_prop_6a a1 a2 a3 a4 a5) oo ->
       P S C a1 a2 a3 a4 a5 oo.

Parameter inv_red_expr_spec_object_define_own_prop_6b
     : forall (S : state) (C : execution_ctx) (a1 : object_loc)
         (a2 : prop_name) (a3 : attributes) (a4 : descriptor) 
         (a5 : bool) (oo : out)
         (P : state ->
              execution_ctx ->
              object_loc ->
              string -> attributes -> descriptor -> bool -> out -> Prop),
       (red_expr S C (spec_object_define_own_prop_6b a1 a2 a3 a4 a5) oo ->
        forall (S0 : state) (C0 : execution_ctx) (exte : ext_expr) (o : out),
        @eq (option out)
          (out_of_ext_expr (spec_object_define_own_prop_6b a1 a2 a3 a4 a5))
          (@Some out oo) ->
        abort oo ->
        not
          (abort_intercepted_expr
             (spec_object_define_own_prop_6b a1 a2 a3 a4 a5)) ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq ext_expr exte (spec_object_define_own_prop_6b a1 a2 a3 a4 a5) ->
        @eq out o oo -> P S C a1 a2 a3 a4 a5 oo) ->
       (red_expr S C (spec_object_define_own_prop_6b a1 a2 a3 a4 a5) oo ->
        forall (S0 : state) (C0 : execution_ctx) (l : object_loc)
          (x : prop_name) (Ad : attributes_data) (Desc : descriptor)
          (throw : bool) (o : out),
        attributes_change_data_on_non_configurable Ad a4 ->
        red_expr S C (spec_object_define_own_prop_reject a5) oo ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq object_loc l a1 ->
        @eq prop_name x a2 ->
        @eq attributes (attributes_data_of Ad) a3 ->
        @eq descriptor Desc a4 ->
        @eq bool throw a5 ->
        @eq out o oo -> P S C a1 a2 (attributes_data_of Ad) a4 a5 oo) ->
       (red_expr S C (spec_object_define_own_prop_6b a1 a2 a3 a4 a5) oo ->
        forall (S0 : state) (C0 : execution_ctx) (l : object_loc)
          (x : prop_name) (Ad : attributes_data) (Desc : descriptor)
          (throw : bool) (o : out),
        not (attributes_change_data_on_non_configurable Ad a4) ->
        red_expr S C
          (spec_object_define_own_prop_write a1 a2 
             (attributes_data_of Ad) a4 a5) oo ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq object_loc l a1 ->
        @eq prop_name x a2 ->
        @eq attributes (attributes_data_of Ad) a3 ->
        @eq descriptor Desc a4 ->
        @eq bool throw a5 ->
        @eq out o oo -> P S C a1 a2 (attributes_data_of Ad) a4 a5 oo) ->
       red_expr S C (spec_object_define_own_prop_6b a1 a2 a3 a4 a5) oo ->
       P S C a1 a2 a3 a4 a5 oo.

Parameter inv_red_expr_spec_object_define_own_prop_6c
     : forall (S : state) (C : execution_ctx) (a1 : object_loc)
         (a2 : prop_name) (a3 : attributes) (a4 : descriptor) 
         (a5 : bool) (oo : out)
         (P : state ->
              execution_ctx ->
              object_loc ->
              string -> attributes -> descriptor -> bool -> out -> Prop),
       (red_expr S C (spec_object_define_own_prop_6c a1 a2 a3 a4 a5) oo ->
        forall (S0 : state) (C0 : execution_ctx) (exte : ext_expr) (o : out),
        @eq (option out)
          (out_of_ext_expr (spec_object_define_own_prop_6c a1 a2 a3 a4 a5))
          (@Some out oo) ->
        abort oo ->
        not
          (abort_intercepted_expr
             (spec_object_define_own_prop_6c a1 a2 a3 a4 a5)) ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq ext_expr exte (spec_object_define_own_prop_6c a1 a2 a3 a4 a5) ->
        @eq out o oo -> P S C a1 a2 a3 a4 a5 oo) ->
       (red_expr S C (spec_object_define_own_prop_6c a1 a2 a3 a4 a5) oo ->
        forall (S0 : state) (C0 : execution_ctx) (l : object_loc)
          (x : prop_name) (Aa : attributes_accessor) 
          (Desc : descriptor) (throw : bool) (o : out),
        attributes_change_accessor_on_non_configurable Aa a4 ->
        red_expr S C (spec_object_define_own_prop_reject a5) oo ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq object_loc l a1 ->
        @eq prop_name x a2 ->
        @eq attributes (attributes_accessor_of Aa) a3 ->
        @eq descriptor Desc a4 ->
        @eq bool throw a5 ->
        @eq out o oo -> P S C a1 a2 (attributes_accessor_of Aa) a4 a5 oo) ->
       (red_expr S C (spec_object_define_own_prop_6c a1 a2 a3 a4 a5) oo ->
        forall (S0 : state) (C0 : execution_ctx) (l : object_loc)
          (x : prop_name) (Aa : attributes_accessor) 
          (Desc : descriptor) (throw : bool) (o : out),
        not (attributes_change_accessor_on_non_configurable Aa a4) ->
        red_expr S C
          (spec_object_define_own_prop_write a1 a2
             (attributes_accessor_of Aa) a4 a5) oo ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq object_loc l a1 ->
        @eq prop_name x a2 ->
        @eq attributes (attributes_accessor_of Aa) a3 ->
        @eq descriptor Desc a4 ->
        @eq bool throw a5 ->
        @eq out o oo -> P S C a1 a2 (attributes_accessor_of Aa) a4 a5 oo) ->
       red_expr S C (spec_object_define_own_prop_6c a1 a2 a3 a4 a5) oo ->
       P S C a1 a2 a3 a4 a5 oo.

Parameter inv_red_expr_spec_object_define_own_prop_reject
     : forall (S : state) (C : execution_ctx) (a1 : bool) 
         (oo : out) (P : state -> execution_ctx -> bool -> out -> Prop),
       (red_expr S C (spec_object_define_own_prop_reject a1) oo ->
        forall (S0 : state) (C0 : execution_ctx) (exte : ext_expr) (o : out),
        @eq (option out)
          (out_of_ext_expr (spec_object_define_own_prop_reject a1))
          (@Some out oo) ->
        abort oo ->
        not (abort_intercepted_expr (spec_object_define_own_prop_reject a1)) ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq ext_expr exte (spec_object_define_own_prop_reject a1) ->
        @eq out o oo -> P S C a1 oo) ->
       (red_expr S C (spec_object_define_own_prop_reject a1) oo ->
        forall (S0 : state) (C0 : execution_ctx) (throw : bool) (o : out),
        red_expr S C
          (spec_error_or_cst a1 native_error_type
             (value_prim (prim_bool false))) oo ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq bool throw a1 -> @eq out o oo -> P S C a1 oo) ->
       red_expr S C (spec_object_define_own_prop_reject a1) oo -> P S C a1 oo.

Parameter inv_red_expr_spec_object_define_own_prop_write
     : forall (S : state) (C : execution_ctx) (a1 : object_loc)
         (a2 : prop_name) (a3 : attributes) (a4 : descriptor) 
         (a5 : bool) (oo : out)
         (P : state ->
              execution_ctx ->
              object_loc ->
              string -> attributes -> descriptor -> bool -> out -> Prop),
       (red_expr S C (spec_object_define_own_prop_write a1 a2 a3 a4 a5) oo ->
        forall (S0 : state) (C0 : execution_ctx) (exte : ext_expr) (o : out),
        @eq (option out)
          (out_of_ext_expr (spec_object_define_own_prop_write a1 a2 a3 a4 a5))
          (@Some out oo) ->
        abort oo ->
        not
          (abort_intercepted_expr
             (spec_object_define_own_prop_write a1 a2 a3 a4 a5)) ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq ext_expr exte (spec_object_define_own_prop_write a1 a2 a3 a4 a5) ->
        @eq out o oo -> P S C a1 a2 a3 a4 a5 oo) ->
       (red_expr S C (spec_object_define_own_prop_write a1 a2 a3 a4 a5) oo ->
        forall (S0 S' : state) (C0 : execution_ctx) 
          (l : object_loc) (x : prop_name) (A : attributes)
          (Desc : descriptor) (throw : bool) (A' : attributes),
        @eq attributes A' (attributes_update a3 a4) ->
        object_set_property S a1 a2 A' S' ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq object_loc l a1 ->
        @eq prop_name x a2 ->
        @eq attributes A a3 ->
        @eq descriptor Desc a4 ->
        @eq bool throw a5 ->
        @eq out (out_ter S' (res_val (value_prim (prim_bool true)))) oo ->
        P S C a1 a2 a3 a4 a5
          (out_ter S' (res_val (value_prim (prim_bool true))))) ->
       red_expr S C (spec_object_define_own_prop_write a1 a2 a3 a4 a5) oo ->
       P S C a1 a2 a3 a4 a5 oo.

Parameter inv_red_expr_spec_object_define_own_prop_array_2
     : forall (S : state) (C : execution_ctx) (a1 : object_loc)
         (a2 : prop_name) (a3 : descriptor) (a4 : bool)
         (a5 : specret full_descriptor) (oo : out)
         (P : state ->
              execution_ctx ->
              object_loc ->
              string ->
              descriptor -> bool -> specret full_descriptor -> out -> Prop),
       (red_expr S C (spec_object_define_own_prop_array_2 a1 a2 a3 a4 a5) oo ->
        forall (S0 : state) (C0 : execution_ctx) (exte : ext_expr) (o : out),
        @eq (option out)
          (out_of_ext_expr
             (spec_object_define_own_prop_array_2 a1 a2 a3 a4 a5))
          (@Some out oo) ->
        abort oo ->
        not
          (abort_intercepted_expr
             (spec_object_define_own_prop_array_2 a1 a2 a3 a4 a5)) ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq ext_expr exte
          (spec_object_define_own_prop_array_2 a1 a2 a3 a4 a5) ->
        @eq out o oo -> P S C a1 a2 a3 a4 a5 oo) ->
       (red_expr S C (spec_object_define_own_prop_array_2 a1 a2 a3 a4 a5) oo ->
        forall (S0 S' : state) (C0 : execution_ctx) 
          (l : object_loc) (Desc : descriptor) (x : prop_name) 
          (throw : bool) (o : out) (Ad : attributes_data) 
          (v : value),
        @eq value v (attributes_data_value Ad) ->
        red_expr S' C
          (spec_object_define_own_prop_array_2_1 a1 a2 a3 a4
             (descriptor_of_attributes (attributes_data_of Ad)) v) oo ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq object_loc l a1 ->
        @eq prop_name x a2 ->
        @eq descriptor Desc a3 ->
        @eq bool throw a4 ->
        @eq (specret full_descriptor)
          (@specret_val full_descriptor S'
             (full_descriptor_some (attributes_data_of Ad))) a5 ->
        @eq out o oo ->
        P S C a1 a2 a3 a4
          (@specret_val full_descriptor S'
             (full_descriptor_some (attributes_data_of Ad))) oo) ->
       red_expr S C (spec_object_define_own_prop_array_2 a1 a2 a3 a4 a5) oo ->
       P S C a1 a2 a3 a4 a5 oo.

Parameter inv_red_expr_spec_object_define_own_prop_array_2_1
     : forall (S : state) (C : execution_ctx) (a1 : object_loc)
         (a2 : prop_name) (a3 : descriptor) (a4 : bool) 
         (a5 : descriptor) (a6 : value) (oo : out)
         (P : state ->
              execution_ctx ->
              object_loc ->
              string ->
              descriptor -> bool -> descriptor -> value -> out -> Prop),
       (red_expr S C
          (spec_object_define_own_prop_array_2_1 a1 a2 a3 a4 a5 a6) oo ->
        forall (S0 : state) (C0 : execution_ctx) (exte : ext_expr) (o : out),
        @eq (option out)
          (out_of_ext_expr
             (spec_object_define_own_prop_array_2_1 a1 a2 a3 a4 a5 a6))
          (@Some out oo) ->
        abort oo ->
        not
          (abort_intercepted_expr
             (spec_object_define_own_prop_array_2_1 a1 a2 a3 a4 a5 a6)) ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq ext_expr exte
          (spec_object_define_own_prop_array_2_1 a1 a2 a3 a4 a5 a6) ->
        @eq out o oo -> P S C a1 a2 a3 a4 a5 a6 oo) ->
       (red_expr S C
          (spec_object_define_own_prop_array_2_1 a1 a2 a3 a4 a5 a6) oo ->
        forall (S0 : state) (C0 : execution_ctx) (l : object_loc)
          (Desc : descriptor) (x : prop_name) (throw : bool) 
          (v : value) (w : prim) (y : specret Z) (o : out)
          (Ad : attributes_data),
        @eq value a6 (value_prim w) ->
        @red_spec Z S C (spec_to_uint32 a6) y ->
        red_expr S C
          (spec_object_define_own_prop_array_branch_3_4 a1 a2 a3 a4
             (descriptor_of_attributes (attributes_data_of Ad)) y) oo ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq object_loc l a1 ->
        @eq prop_name x a2 ->
        @eq descriptor Desc a3 ->
        @eq bool throw a4 ->
        @eq descriptor
          (descriptor_intro (@Some value (attributes_data_value Ad))
             (@Some bool (attributes_data_writable Ad)) 
             (@None value) (@None value)
             (@Some bool (attributes_data_enumerable Ad))
             (@Some bool (attributes_data_configurable Ad))) a5 ->
        @eq value v a6 ->
        @eq out o oo ->
        P S C a1 a2 a3 a4
          (descriptor_intro (@Some value (attributes_data_value Ad))
             (@Some bool (attributes_data_writable Ad)) 
             (@None value) (@None value)
             (@Some bool (attributes_data_enumerable Ad))
             (@Some bool (attributes_data_configurable Ad))) a6 oo) ->
       red_expr S C (spec_object_define_own_prop_array_2_1 a1 a2 a3 a4 a5 a6)
         oo -> P S C a1 a2 a3 a4 a5 a6 oo.

Parameter inv_red_expr_spec_object_define_own_prop_array_branch_3_4
     : forall (S : state) (C : execution_ctx) (a1 : object_loc)
         (a2 : prop_name) (a3 : descriptor) (a4 : bool) 
         (a5 : descriptor) (a6 : specret Z) (oo : out)
         (P : state ->
              execution_ctx ->
              object_loc ->
              string ->
              descriptor -> bool -> descriptor -> specret Z -> out -> Prop),
       (red_expr S C
          (spec_object_define_own_prop_array_branch_3_4 a1 a2 a3 a4 a5 a6) oo ->
        forall (S0 : state) (C0 : execution_ctx) (exte : ext_expr) (o : out),
        @eq (option out)
          (out_of_ext_expr
             (spec_object_define_own_prop_array_branch_3_4 a1 a2 a3 a4 a5 a6))
          (@Some out oo) ->
        abort oo ->
        not
          (abort_intercepted_expr
             (spec_object_define_own_prop_array_branch_3_4 a1 a2 a3 a4 a5 a6)) ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq ext_expr exte
          (spec_object_define_own_prop_array_branch_3_4 a1 a2 a3 a4 a5 a6) ->
        @eq out o oo -> P S C a1 a2 a3 a4 a5 a6 oo) ->
       (red_expr S C
          (spec_object_define_own_prop_array_branch_3_4 a1 a2 a3 a4 a5 a6) oo ->
        forall (S0 : state) (C0 : execution_ctx) (l : object_loc)
          (Desc : descriptor) (throw : bool) (oldLen : Z) 
          (o : out) (Ad : attributes_data),
        red_expr S C
          (spec_object_define_own_prop_array_3 a1 a3 a4
             (descriptor_of_attributes (attributes_data_of Ad)) oldLen) oo ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq object_loc l a1 ->
        @eq prop_name
          (String (Ascii false false true true false true true false)
             (String (Ascii true false true false false true true false)
                (String (Ascii false true true true false true true false)
                   (String (Ascii true true true false false true true false)
                      (String
                         (Ascii false false true false true true true false)
                         (String
                            (Ascii false false false true false true true
                               false) EmptyString)))))) a2 ->
        @eq descriptor Desc a3 ->
        @eq bool throw a4 ->
        @eq descriptor
          (descriptor_intro (@Some value (attributes_data_value Ad))
             (@Some bool (attributes_data_writable Ad)) 
             (@None value) (@None value)
             (@Some bool (attributes_data_enumerable Ad))
             (@Some bool (attributes_data_configurable Ad))) a5 ->
        @eq (specret Z) (@ret Z S oldLen) a6 ->
        @eq out o oo ->
        P S C a1
          (String (Ascii false false true true false true true false)
             (String (Ascii true false true false false true true false)
                (String (Ascii false true true true false true true false)
                   (String (Ascii true true true false false true true false)
                      (String
                         (Ascii false false true false true true true false)
                         (String
                            (Ascii false false false true false true true
                               false) EmptyString)))))) a3 a4
          (descriptor_intro (@Some value (attributes_data_value Ad))
             (@Some bool (attributes_data_writable Ad)) 
             (@None value) (@None value)
             (@Some bool (attributes_data_enumerable Ad))
             (@Some bool (attributes_data_configurable Ad)))
          (@ret Z S oldLen) oo) ->
       (red_expr S C
          (spec_object_define_own_prop_array_branch_3_4 a1 a2 a3 a4 a5 a6) oo ->
        forall (S0 : state) (C0 : execution_ctx) (l : object_loc)
          (x : prop_name) (Desc : descriptor) (throw : bool) 
          (oldLen : Z) (o : out) (Ad : attributes_data),
        not
          (@eq prop_name a2
             (String (Ascii false false true true false true true false)
                (String (Ascii true false true false false true true false)
                   (String (Ascii false true true true false true true false)
                      (String
                         (Ascii true true true false false true true false)
                         (String
                            (Ascii false false true false true true true
                               false)
                            (String
                               (Ascii false false false true false true true
                                  false) EmptyString))))))) ->
        red_expr S C
          (spec_object_define_own_prop_array_branch_4_5 a1 a2 a3 a4
             (descriptor_of_attributes (attributes_data_of Ad)) oldLen) oo ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq object_loc l a1 ->
        @eq prop_name x a2 ->
        @eq descriptor Desc a3 ->
        @eq bool throw a4 ->
        @eq descriptor
          (descriptor_intro (@Some value (attributes_data_value Ad))
             (@Some bool (attributes_data_writable Ad)) 
             (@None value) (@None value)
             (@Some bool (attributes_data_enumerable Ad))
             (@Some bool (attributes_data_configurable Ad))) a5 ->
        @eq (specret Z) (@ret Z S oldLen) a6 ->
        @eq out o oo ->
        P S C a1 a2 a3 a4
          (descriptor_intro (@Some value (attributes_data_value Ad))
             (@Some bool (attributes_data_writable Ad)) 
             (@None value) (@None value)
             (@Some bool (attributes_data_enumerable Ad))
             (@Some bool (attributes_data_configurable Ad)))
          (@ret Z S oldLen) oo) ->
       red_expr S C
         (spec_object_define_own_prop_array_branch_3_4 a1 a2 a3 a4 a5 a6) oo ->
       P S C a1 a2 a3 a4 a5 a6 oo.

Parameter inv_red_expr_spec_object_define_own_prop_array_branch_4_5
     : forall (S : state) (C : execution_ctx) (a1 : object_loc)
         (a2 : prop_name) (a3 : descriptor) (a4 : bool) 
         (a5 : descriptor) (a6 : Z) (oo : out)
         (P : state ->
              execution_ctx ->
              object_loc ->
              string -> descriptor -> bool -> descriptor -> Z -> out -> Prop),
       (red_expr S C
          (spec_object_define_own_prop_array_branch_4_5 a1 a2 a3 a4 a5 a6) oo ->
        forall (S0 : state) (C0 : execution_ctx) (exte : ext_expr) (o : out),
        @eq (option out)
          (out_of_ext_expr
             (spec_object_define_own_prop_array_branch_4_5 a1 a2 a3 a4 a5 a6))
          (@Some out oo) ->
        abort oo ->
        not
          (abort_intercepted_expr
             (spec_object_define_own_prop_array_branch_4_5 a1 a2 a3 a4 a5 a6)) ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq ext_expr exte
          (spec_object_define_own_prop_array_branch_4_5 a1 a2 a3 a4 a5 a6) ->
        @eq out o oo -> P S C a1 a2 a3 a4 a5 a6 oo) ->
       (red_expr S C
          (spec_object_define_own_prop_array_branch_4_5 a1 a2 a3 a4 a5 a6) oo ->
        forall (S0 : state) (C0 : execution_ctx) (l : object_loc)
          (x : prop_name) (Desc : descriptor) (throw : bool) 
          (oldLen : Z) (Ad : attributes_data) (o : out) 
          (y : specret Z),
        @red_spec Z S C (spec_to_uint32 (value_prim (prim_string a2))) y ->
        red_expr S C
          (spec_object_define_own_prop_array_branch_4_5_a a1 a2 y a3 a4
             (descriptor_of_attributes (attributes_data_of Ad)) a6) oo ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq object_loc l a1 ->
        @eq prop_name x a2 ->
        @eq descriptor Desc a3 ->
        @eq bool throw a4 ->
        @eq descriptor
          (descriptor_intro (@Some value (attributes_data_value Ad))
             (@Some bool (attributes_data_writable Ad)) 
             (@None value) (@None value)
             (@Some bool (attributes_data_enumerable Ad))
             (@Some bool (attributes_data_configurable Ad))) a5 ->
        @eq Z oldLen a6 ->
        @eq out o oo ->
        P S C a1 a2 a3 a4
          (descriptor_intro (@Some value (attributes_data_value Ad))
             (@Some bool (attributes_data_writable Ad)) 
             (@None value) (@None value)
             (@Some bool (attributes_data_enumerable Ad))
             (@Some bool (attributes_data_configurable Ad))) a6 oo) ->
       red_expr S C
         (spec_object_define_own_prop_array_branch_4_5 a1 a2 a3 a4 a5 a6) oo ->
       P S C a1 a2 a3 a4 a5 a6 oo.

Parameter inv_red_expr_spec_object_define_own_prop_array_branch_4_5_a
     : forall (S : state) (C : execution_ctx) (a1 : object_loc)
         (a2 : prop_name) (a3 : specret Z) (a4 : descriptor) 
         (a5 : bool) (a6 : descriptor) (a7 : Z) (oo : out)
         (P : state ->
              execution_ctx ->
              object_loc ->
              string ->
              specret Z ->
              descriptor -> bool -> descriptor -> Z -> out -> Prop),
       (red_expr S C
          (spec_object_define_own_prop_array_branch_4_5_a a1 a2 a3 a4 a5 a6
             a7) oo ->
        forall (S0 : state) (C0 : execution_ctx) (exte : ext_expr) (o : out),
        @eq (option out)
          (out_of_ext_expr
             (spec_object_define_own_prop_array_branch_4_5_a a1 a2 a3 a4 a5
                a6 a7)) (@Some out oo) ->
        abort oo ->
        not
          (abort_intercepted_expr
             (spec_object_define_own_prop_array_branch_4_5_a a1 a2 a3 a4 a5
                a6 a7)) ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq ext_expr exte
          (spec_object_define_own_prop_array_branch_4_5_a a1 a2 a3 a4 a5 a6
             a7) -> @eq out o oo -> P S C a1 a2 a3 a4 a5 a6 a7 oo) ->
       (red_expr S C
          (spec_object_define_own_prop_array_branch_4_5_a a1 a2 a3 a4 a5 a6
             a7) oo ->
        forall (S0 S' : state) (C0 : execution_ctx) 
          (l : object_loc) (x : prop_name) (ilen : Z) 
          (o1 : out) (Desc : descriptor) (throw : bool) 
          (oldLen : Z) (Ad : attributes_data) (o : out),
        red_expr S' C
          (spec_to_string (value_prim (prim_number (JsNumber.of_int ilen))))
          o1 ->
        red_expr S' C
          (spec_object_define_own_prop_array_branch_4_5_b a1 a2 ilen o1 a4 a5
             (descriptor_of_attributes (attributes_data_of Ad)) a7) oo ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq object_loc l a1 ->
        @eq prop_name x a2 ->
        @eq (specret Z) (@ret Z S' ilen) a3 ->
        @eq descriptor Desc a4 ->
        @eq bool throw a5 ->
        @eq descriptor
          (descriptor_intro (@Some value (attributes_data_value Ad))
             (@Some bool (attributes_data_writable Ad)) 
             (@None value) (@None value)
             (@Some bool (attributes_data_enumerable Ad))
             (@Some bool (attributes_data_configurable Ad))) a6 ->
        @eq Z oldLen a7 ->
        @eq out o oo ->
        P S C a1 a2 (@ret Z S' ilen) a4 a5
          (descriptor_intro (@Some value (attributes_data_value Ad))
             (@Some bool (attributes_data_writable Ad)) 
             (@None value) (@None value)
             (@Some bool (attributes_data_enumerable Ad))
             (@Some bool (attributes_data_configurable Ad))) a7 oo) ->
       red_expr S C
         (spec_object_define_own_prop_array_branch_4_5_a a1 a2 a3 a4 a5 a6 a7)
         oo -> P S C a1 a2 a3 a4 a5 a6 a7 oo.

Parameter inv_red_expr_spec_object_define_own_prop_array_branch_4_5_b
     : forall (S : state) (C : execution_ctx) (a1 : object_loc)
         (a2 : prop_name) (a3 : Z) (a4 : out) (a5 : descriptor) 
         (a6 : bool) (a7 : descriptor) (a8 : Z) (oo : out)
         (P : state ->
              execution_ctx ->
              object_loc ->
              string ->
              Z ->
              out -> descriptor -> bool -> descriptor -> Z -> out -> Prop),
       (red_expr S C
          (spec_object_define_own_prop_array_branch_4_5_b a1 a2 a3 a4 a5 a6
             a7 a8) oo ->
        forall (S0 : state) (C0 : execution_ctx) (exte : ext_expr) (o : out),
        @eq (option out)
          (out_of_ext_expr
             (spec_object_define_own_prop_array_branch_4_5_b a1 a2 a3 a4 a5
                a6 a7 a8)) (@Some out oo) ->
        abort oo ->
        not
          (abort_intercepted_expr
             (spec_object_define_own_prop_array_branch_4_5_b a1 a2 a3 a4 a5
                a6 a7 a8)) ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq ext_expr exte
          (spec_object_define_own_prop_array_branch_4_5_b a1 a2 a3 a4 a5 a6
             a7 a8) -> @eq out o oo -> P S C a1 a2 a3 a4 a5 a6 a7 a8 oo) ->
       (red_expr S C
          (spec_object_define_own_prop_array_branch_4_5_b a1 a2 a3 a4 a5 a6
             a7 a8) oo ->
        forall (S0 S' : state) (C0 : execution_ctx) 
          (l : object_loc) (x : prop_name) (ilen : Z) 
          (slen : prop_name) (Desc : descriptor) (throw : bool)
          (Ad : attributes_data) (oldLen : Z) (o : out),
        Logic.and (@eq prop_name a2 slen)
          (not
             (@eq Z a3 4294967295%Z)) ->
        red_expr S' C
          (spec_object_define_own_prop_array_4a a1 a2 a5 a6
             (descriptor_of_attributes (attributes_data_of Ad)) a8) oo ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq object_loc l a1 ->
        @eq prop_name x a2 ->
        @eq Z ilen a3 ->
        @eq out (out_ter S' (res_val (value_prim (prim_string slen)))) a4 ->
        @eq descriptor Desc a5 ->
        @eq bool throw a6 ->
        @eq descriptor
          (descriptor_intro (@Some value (attributes_data_value Ad))
             (@Some bool (attributes_data_writable Ad)) 
             (@None value) (@None value)
             (@Some bool (attributes_data_enumerable Ad))
             (@Some bool (attributes_data_configurable Ad))) a7 ->
        @eq Z oldLen a8 ->
        @eq out o oo ->
        P S C a1 a2 a3 (out_ter S' (res_val (value_prim (prim_string slen))))
          a5 a6
          (descriptor_intro (@Some value (attributes_data_value Ad))
             (@Some bool (attributes_data_writable Ad)) 
             (@None value) (@None value)
             (@Some bool (attributes_data_enumerable Ad))
             (@Some bool (attributes_data_configurable Ad))) a8 oo) ->
       (red_expr S C
          (spec_object_define_own_prop_array_branch_4_5_b a1 a2 a3 a4 a5 a6
             a7 a8) oo ->
        forall (S0 S' : state) (C0 : execution_ctx) 
          (l : object_loc) (x : prop_name) (ilen : Z) 
          (slen : prop_name) (Desc : descriptor) (throw : bool)
          (Ad : attributes_data) (oldLen : Z) (o : out),
        not
          (Logic.and (@eq prop_name a2 slen)
             (not
                (@eq Z a3 4294967295%Z))) ->
        red_expr S' C (spec_object_define_own_prop_array_5 a1 a2 a5 a6) oo ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq object_loc l a1 ->
        @eq prop_name x a2 ->
        @eq Z ilen a3 ->
        @eq out (out_ter S' (res_val (value_prim (prim_string slen)))) a4 ->
        @eq descriptor Desc a5 ->
        @eq bool throw a6 ->
        @eq descriptor
          (descriptor_intro (@Some value (attributes_data_value Ad))
             (@Some bool (attributes_data_writable Ad)) 
             (@None value) (@None value)
             (@Some bool (attributes_data_enumerable Ad))
             (@Some bool (attributes_data_configurable Ad))) a7 ->
        @eq Z oldLen a8 ->
        @eq out o oo ->
        P S C a1 a2 a3 (out_ter S' (res_val (value_prim (prim_string slen))))
          a5 a6
          (descriptor_intro (@Some value (attributes_data_value Ad))
             (@Some bool (attributes_data_writable Ad)) 
             (@None value) (@None value)
             (@Some bool (attributes_data_enumerable Ad))
             (@Some bool (attributes_data_configurable Ad))) a8 oo) ->
       red_expr S C
         (spec_object_define_own_prop_array_branch_4_5_b a1 a2 a3 a4 a5 a6 a7
            a8) oo -> P S C a1 a2 a3 a4 a5 a6 a7 a8 oo.

Parameter inv_red_expr_spec_object_define_own_prop_array_4a
     : forall (S : state) (C : execution_ctx) (a1 : object_loc)
         (a2 : prop_name) (a3 : descriptor) (a4 : bool) 
         (a5 : descriptor) (a6 : Z) (oo : out)
         (P : state ->
              execution_ctx ->
              object_loc ->
              string -> descriptor -> bool -> descriptor -> Z -> out -> Prop),
       (red_expr S C (spec_object_define_own_prop_array_4a a1 a2 a3 a4 a5 a6)
          oo ->
        forall (S0 : state) (C0 : execution_ctx) (exte : ext_expr) (o : out),
        @eq (option out)
          (out_of_ext_expr
             (spec_object_define_own_prop_array_4a a1 a2 a3 a4 a5 a6))
          (@Some out oo) ->
        abort oo ->
        not
          (abort_intercepted_expr
             (spec_object_define_own_prop_array_4a a1 a2 a3 a4 a5 a6)) ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq ext_expr exte
          (spec_object_define_own_prop_array_4a a1 a2 a3 a4 a5 a6) ->
        @eq out o oo -> P S C a1 a2 a3 a4 a5 a6 oo) ->
       (red_expr S C (spec_object_define_own_prop_array_4a a1 a2 a3 a4 a5 a6)
          oo ->
        forall (S0 : state) (C0 : execution_ctx) (l : object_loc)
          (x : prop_name) (Desc : descriptor) (throw : bool)
          (Ad : attributes_data) (oldLen : Z) (y : specret Z) 
          (o : out),
        @red_spec Z S C (spec_to_uint32 (value_prim (prim_string a2))) y ->
        red_expr S C
          (spec_object_define_own_prop_array_4b a1 a2 y a3 a4
             (descriptor_of_attributes (attributes_data_of Ad)) a6) oo ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq object_loc l a1 ->
        @eq prop_name x a2 ->
        @eq descriptor Desc a3 ->
        @eq bool throw a4 ->
        @eq descriptor
          (descriptor_intro (@Some value (attributes_data_value Ad))
             (@Some bool (attributes_data_writable Ad)) 
             (@None value) (@None value)
             (@Some bool (attributes_data_enumerable Ad))
             (@Some bool (attributes_data_configurable Ad))) a5 ->
        @eq Z oldLen a6 ->
        @eq out o oo ->
        P S C a1 a2 a3 a4
          (descriptor_intro (@Some value (attributes_data_value Ad))
             (@Some bool (attributes_data_writable Ad)) 
             (@None value) (@None value)
             (@Some bool (attributes_data_enumerable Ad))
             (@Some bool (attributes_data_configurable Ad))) a6 oo) ->
       red_expr S C (spec_object_define_own_prop_array_4a a1 a2 a3 a4 a5 a6)
         oo -> P S C a1 a2 a3 a4 a5 a6 oo.

Parameter inv_red_expr_spec_object_define_own_prop_array_4b
     : forall (S : state) (C : execution_ctx) (a1 : object_loc)
         (a2 : prop_name) (a3 : specret Z) (a4 : descriptor) 
         (a5 : bool) (a6 : descriptor) (a7 : Z) (oo : out)
         (P : state ->
              execution_ctx ->
              object_loc ->
              string ->
              specret Z ->
              descriptor -> bool -> descriptor -> Z -> out -> Prop),
       (red_expr S C
          (spec_object_define_own_prop_array_4b a1 a2 a3 a4 a5 a6 a7) oo ->
        forall (S0 : state) (C0 : execution_ctx) (exte : ext_expr) (o : out),
        @eq (option out)
          (out_of_ext_expr
             (spec_object_define_own_prop_array_4b a1 a2 a3 a4 a5 a6 a7))
          (@Some out oo) ->
        abort oo ->
        not
          (abort_intercepted_expr
             (spec_object_define_own_prop_array_4b a1 a2 a3 a4 a5 a6 a7)) ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq ext_expr exte
          (spec_object_define_own_prop_array_4b a1 a2 a3 a4 a5 a6 a7) ->
        @eq out o oo -> P S C a1 a2 a3 a4 a5 a6 a7 oo) ->
       (red_expr S C
          (spec_object_define_own_prop_array_4b a1 a2 a3 a4 a5 a6 a7) oo ->
        forall (S0 S' : state) (C0 : execution_ctx) 
          (l : object_loc) (x : prop_name) (index : Z) 
          (Desc : descriptor) (throw : bool) (Ad : attributes_data)
          (oldLen : Z) (o : out),
        Logic.and (@le Z le_int_inst a7 index)
          (not (istrue (attributes_data_writable Ad))) ->
        red_expr S' C (spec_object_define_own_prop_reject a5) oo ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq object_loc l a1 ->
        @eq prop_name x a2 ->
        @eq (specret Z) (@ret Z S' index) a3 ->
        @eq descriptor Desc a4 ->
        @eq bool throw a5 ->
        @eq descriptor
          (descriptor_intro (@Some value (attributes_data_value Ad))
             (@Some bool (attributes_data_writable Ad)) 
             (@None value) (@None value)
             (@Some bool (attributes_data_enumerable Ad))
             (@Some bool (attributes_data_configurable Ad))) a6 ->
        @eq Z oldLen a7 ->
        @eq out o oo ->
        P S C a1 a2 (@ret Z S' index) a4 a5
          (descriptor_intro (@Some value (attributes_data_value Ad))
             (@Some bool (attributes_data_writable Ad)) 
             (@None value) (@None value)
             (@Some bool (attributes_data_enumerable Ad))
             (@Some bool (attributes_data_configurable Ad))) a7 oo) ->
       (red_expr S C
          (spec_object_define_own_prop_array_4b a1 a2 a3 a4 a5 a6 a7) oo ->
        forall (S0 S' : state) (C0 : execution_ctx) 
          (l : object_loc) (x : prop_name) (index : Z) 
          (Desc : descriptor) (throw : bool) (Ad : attributes_data)
          (oldLen : Z) (o1 o : out),
        not
          (Logic.and (@le Z le_int_inst a7 index)
             (not (istrue (attributes_data_writable Ad)))) ->
        red_expr S' C
          (spec_object_define_own_prop_1 builtin_define_own_prop_default a1
             a2 a4 false) o1 ->
        red_expr S' C
          (spec_object_define_own_prop_array_4c a1 index a4 a5 a7
             (descriptor_of_attributes (attributes_data_of Ad)) o1) oo ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq object_loc l a1 ->
        @eq prop_name x a2 ->
        @eq (specret Z) (@ret Z S' index) a3 ->
        @eq descriptor Desc a4 ->
        @eq bool throw a5 ->
        @eq descriptor
          (descriptor_intro (@Some value (attributes_data_value Ad))
             (@Some bool (attributes_data_writable Ad)) 
             (@None value) (@None value)
             (@Some bool (attributes_data_enumerable Ad))
             (@Some bool (attributes_data_configurable Ad))) a6 ->
        @eq Z oldLen a7 ->
        @eq out o oo ->
        P S C a1 a2 (@ret Z S' index) a4 a5
          (descriptor_intro (@Some value (attributes_data_value Ad))
             (@Some bool (attributes_data_writable Ad)) 
             (@None value) (@None value)
             (@Some bool (attributes_data_enumerable Ad))
             (@Some bool (attributes_data_configurable Ad))) a7 oo) ->
       red_expr S C
         (spec_object_define_own_prop_array_4b a1 a2 a3 a4 a5 a6 a7) oo ->
       P S C a1 a2 a3 a4 a5 a6 a7 oo.

Parameter inv_red_expr_spec_object_define_own_prop_array_4c
     : forall (S : state) (C : execution_ctx) (a1 : object_loc) 
         (a2 : Z) (a3 : descriptor) (a4 : bool) (a5 : Z) 
         (a6 : descriptor) (a7 oo : out)
         (P : state ->
              execution_ctx ->
              object_loc ->
              Z ->
              descriptor -> bool -> Z -> descriptor -> out -> out -> Prop),
       (red_expr S C
          (spec_object_define_own_prop_array_4c a1 a2 a3 a4 a5 a6 a7) oo ->
        forall (S0 : state) (C0 : execution_ctx) (exte : ext_expr) (o : out),
        @eq (option out)
          (out_of_ext_expr
             (spec_object_define_own_prop_array_4c a1 a2 a3 a4 a5 a6 a7))
          (@Some out oo) ->
        abort oo ->
        not
          (abort_intercepted_expr
             (spec_object_define_own_prop_array_4c a1 a2 a3 a4 a5 a6 a7)) ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq ext_expr exte
          (spec_object_define_own_prop_array_4c a1 a2 a3 a4 a5 a6 a7) ->
        @eq out o oo -> P S C a1 a2 a3 a4 a5 a6 a7 oo) ->
       (red_expr S C
          (spec_object_define_own_prop_array_4c a1 a2 a3 a4 a5 a6 a7) oo ->
        forall (S0 S' : state) (C0 : execution_ctx) 
          (l : object_loc) (index : Z) (Desc : descriptor) 
          (throw : bool) (oldLen : Z) (Ad : attributes_data) 
          (o : out),
        red_expr S' C (spec_object_define_own_prop_reject a4) oo ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq object_loc l a1 ->
        @eq Z index a2 ->
        @eq descriptor Desc a3 ->
        @eq bool throw a4 ->
        @eq Z oldLen a5 ->
        @eq descriptor
          (descriptor_intro (@Some value (attributes_data_value Ad))
             (@Some bool (attributes_data_writable Ad)) 
             (@None value) (@None value)
             (@Some bool (attributes_data_enumerable Ad))
             (@Some bool (attributes_data_configurable Ad))) a6 ->
        @eq out (out_ter S' (res_val (value_prim (prim_bool false)))) a7 ->
        @eq out o oo ->
        P S C a1 a2 a3 a4 a5
          (descriptor_intro (@Some value (attributes_data_value Ad))
             (@Some bool (attributes_data_writable Ad)) 
             (@None value) (@None value)
             (@Some bool (attributes_data_enumerable Ad))
             (@Some bool (attributes_data_configurable Ad)))
          (out_ter S' (res_val (value_prim (prim_bool false)))) oo) ->
       (red_expr S C
          (spec_object_define_own_prop_array_4c a1 a2 a3 a4 a5 a6 a7) oo ->
        forall (S0 S' : state) (C0 : execution_ctx) 
          (l : object_loc) (index : Z) (Desc Desc' : descriptor)
          (throw : bool) (oldLen : Z) (Ad : attributes_data) 
          (o : out),
        @le Z le_int_inst a5 a2 ->
        @eq descriptor Desc'
          (descriptor_with_value
             (descriptor_of_attributes (attributes_data_of Ad))
             (@Some value
                (value_prim
                   (prim_number (JsNumber.of_int (Z.add a2 (Zpos xH))))))) ->
        red_expr S' C
          (spec_object_define_own_prop_1 builtin_define_own_prop_default a1
             (String (Ascii false false true true false true true false)
                (String (Ascii true false true false false true true false)
                   (String (Ascii false true true true false true true false)
                      (String
                         (Ascii true true true false false true true false)
                         (String
                            (Ascii false false true false true true true
                               false)
                            (String
                               (Ascii false false false true false true true
                                  false) EmptyString)))))) Desc' false) oo ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq object_loc l a1 ->
        @eq Z index a2 ->
        @eq descriptor Desc a3 ->
        @eq bool throw a4 ->
        @eq Z oldLen a5 ->
        @eq descriptor
          (descriptor_intro (@Some value (attributes_data_value Ad))
             (@Some bool (attributes_data_writable Ad)) 
             (@None value) (@None value)
             (@Some bool (attributes_data_enumerable Ad))
             (@Some bool (attributes_data_configurable Ad))) a6 ->
        @eq out (out_ter S' (res_val (value_prim (prim_bool true)))) a7 ->
        @eq out o oo ->
        P S C a1 a2 a3 a4 a5
          (descriptor_intro (@Some value (attributes_data_value Ad))
             (@Some bool (attributes_data_writable Ad)) 
             (@None value) (@None value)
             (@Some bool (attributes_data_enumerable Ad))
             (@Some bool (attributes_data_configurable Ad)))
          (out_ter S' (res_val (value_prim (prim_bool true)))) oo) ->
       (red_expr S C
          (spec_object_define_own_prop_array_4c a1 a2 a3 a4 a5 a6 a7) oo ->
        forall (S0 S' : state) (C0 : execution_ctx) 
          (l : object_loc) (index : Z) (Desc : descriptor) 
          (throw : bool) (oldLen : Z) (Ad : attributes_data),
        not (@le Z le_int_inst a5 a2) ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq object_loc l a1 ->
        @eq Z index a2 ->
        @eq descriptor Desc a3 ->
        @eq bool throw a4 ->
        @eq Z oldLen a5 ->
        @eq descriptor
          (descriptor_intro (@Some value (attributes_data_value Ad))
             (@Some bool (attributes_data_writable Ad)) 
             (@None value) (@None value)
             (@Some bool (attributes_data_enumerable Ad))
             (@Some bool (attributes_data_configurable Ad))) a6 ->
        @eq out (out_ter S' (res_val (value_prim (prim_bool true)))) a7 ->
        @eq out (out_ter S' (res_val (value_prim (prim_bool true)))) oo ->
        P S C a1 a2 a3 a4 a5
          (descriptor_intro (@Some value (attributes_data_value Ad))
             (@Some bool (attributes_data_writable Ad)) 
             (@None value) (@None value)
             (@Some bool (attributes_data_enumerable Ad))
             (@Some bool (attributes_data_configurable Ad)))
          (out_ter S' (res_val (value_prim (prim_bool true))))
          (out_ter S' (res_val (value_prim (prim_bool true))))) ->
       red_expr S C
         (spec_object_define_own_prop_array_4c a1 a2 a3 a4 a5 a6 a7) oo ->
       P S C a1 a2 a3 a4 a5 a6 a7 oo.

Parameter inv_red_expr_spec_object_define_own_prop_array_5
     : forall (S : state) (C : execution_ctx) (a1 : object_loc)
         (a2 : prop_name) (a3 : descriptor) (a4 : bool) 
         (oo : out)
         (P : state ->
              execution_ctx ->
              object_loc -> string -> descriptor -> bool -> out -> Prop),
       (red_expr S C (spec_object_define_own_prop_array_5 a1 a2 a3 a4) oo ->
        forall (S0 : state) (C0 : execution_ctx) (exte : ext_expr) (o : out),
        @eq (option out)
          (out_of_ext_expr (spec_object_define_own_prop_array_5 a1 a2 a3 a4))
          (@Some out oo) ->
        abort oo ->
        not
          (abort_intercepted_expr
             (spec_object_define_own_prop_array_5 a1 a2 a3 a4)) ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq ext_expr exte (spec_object_define_own_prop_array_5 a1 a2 a3 a4) ->
        @eq out o oo -> P S C a1 a2 a3 a4 oo) ->
       (red_expr S C (spec_object_define_own_prop_array_5 a1 a2 a3 a4) oo ->
        forall (S0 : state) (C0 : execution_ctx) (l : object_loc)
          (x : prop_name) (Desc : descriptor) (throw : bool) 
          (o : out),
        red_expr S C
          (spec_object_define_own_prop_1 builtin_define_own_prop_default a1
             a2 a3 a4) oo ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq object_loc l a1 ->
        @eq prop_name x a2 ->
        @eq descriptor Desc a3 ->
        @eq bool throw a4 -> @eq out o oo -> P S C a1 a2 a3 a4 oo) ->
       red_expr S C (spec_object_define_own_prop_array_5 a1 a2 a3 a4) oo ->
       P S C a1 a2 a3 a4 oo.

Parameter inv_red_expr_spec_object_define_own_prop_array_3
     : forall (S : state) (C : execution_ctx) (a1 : object_loc)
         (a2 : descriptor) (a3 : bool) (a4 : descriptor) 
         (a5 : Z) (oo : out)
         (P : state ->
              execution_ctx ->
              object_loc ->
              descriptor -> bool -> descriptor -> Z -> out -> Prop),
       (red_expr S C (spec_object_define_own_prop_array_3 a1 a2 a3 a4 a5) oo ->
        forall (S0 : state) (C0 : execution_ctx) (exte : ext_expr) (o : out),
        @eq (option out)
          (out_of_ext_expr
             (spec_object_define_own_prop_array_3 a1 a2 a3 a4 a5))
          (@Some out oo) ->
        abort oo ->
        not
          (abort_intercepted_expr
             (spec_object_define_own_prop_array_3 a1 a2 a3 a4 a5)) ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq ext_expr exte
          (spec_object_define_own_prop_array_3 a1 a2 a3 a4 a5) ->
        @eq out o oo -> P S C a1 a2 a3 a4 a5 oo) ->
       (red_expr S C (spec_object_define_own_prop_array_3 a1 a2 a3 a4 a5) oo ->
        forall (S0 : state) (C0 : execution_ctx) (l : object_loc)
          (Desc : descriptor) (throw : bool) (oldLen : Z)
          (Ad : attributes_data) (o0 : out),
        out ->
        @eq (option value) (descriptor_value a2) (@None value) ->
        red_expr S C
          (spec_object_define_own_prop_1 builtin_define_own_prop_default a1
             (String (Ascii false false true true false true true false)
                (String (Ascii true false true false false true true false)
                   (String (Ascii false true true true false true true false)
                      (String
                         (Ascii true true true false false true true false)
                         (String
                            (Ascii false false true false true true true
                               false)
                            (String
                               (Ascii false false false true false true true
                                  false) EmptyString)))))) a2 a3) oo ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq object_loc l a1 ->
        @eq descriptor Desc a2 ->
        @eq bool throw a3 ->
        @eq descriptor
          (descriptor_intro (@Some value (attributes_data_value Ad))
             (@Some bool (attributes_data_writable Ad)) 
             (@None value) (@None value)
             (@Some bool (attributes_data_enumerable Ad))
             (@Some bool (attributes_data_configurable Ad))) a4 ->
        @eq Z oldLen a5 ->
        @eq out o0 oo ->
        P S C a1 a2 a3
          (descriptor_intro (@Some value (attributes_data_value Ad))
             (@Some bool (attributes_data_writable Ad)) 
             (@None value) (@None value)
             (@Some bool (attributes_data_enumerable Ad))
             (@Some bool (attributes_data_configurable Ad))) a5 oo) ->
       (red_expr S C (spec_object_define_own_prop_array_3 a1 a2 a3 a4 a5) oo ->
        forall (S0 : state) (C0 : execution_ctx) (l : object_loc) 
          (v : value) (y : specret Z) (Desc : descriptor) 
          (throw : bool) (Ad : attributes_data) (oldLen : Z) 
          (o : out),
        @eq (option value) (descriptor_value a2) (@Some value v) ->
        @red_spec Z S C (spec_to_uint32 v) y ->
        red_expr S C
          (spec_object_define_own_prop_array_3c a1 v y a2 a3
             (descriptor_of_attributes (attributes_data_of Ad)) a5) oo ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq object_loc l a1 ->
        @eq descriptor Desc a2 ->
        @eq bool throw a3 ->
        @eq descriptor
          (descriptor_intro (@Some value (attributes_data_value Ad))
             (@Some bool (attributes_data_writable Ad)) 
             (@None value) (@None value)
             (@Some bool (attributes_data_enumerable Ad))
             (@Some bool (attributes_data_configurable Ad))) a4 ->
        @eq Z oldLen a5 ->
        @eq out o oo ->
        P S C a1 a2 a3
          (descriptor_intro (@Some value (attributes_data_value Ad))
             (@Some bool (attributes_data_writable Ad)) 
             (@None value) (@None value)
             (@Some bool (attributes_data_enumerable Ad))
             (@Some bool (attributes_data_configurable Ad))) a5 oo) ->
       red_expr S C (spec_object_define_own_prop_array_3 a1 a2 a3 a4 a5) oo ->
       P S C a1 a2 a3 a4 a5 oo.

Parameter inv_red_expr_spec_object_define_own_prop_array_3c
     : forall (S : state) (C : execution_ctx) (a1 : object_loc) 
         (a2 : value) (a3 : specret Z) (a4 : descriptor) 
         (a5 : bool) (a6 : descriptor) (a7 : Z) (oo : out)
         (P : state ->
              execution_ctx ->
              object_loc ->
              value ->
              specret Z ->
              descriptor -> bool -> descriptor -> Z -> out -> Prop),
       (red_expr S C
          (spec_object_define_own_prop_array_3c a1 a2 a3 a4 a5 a6 a7) oo ->
        forall (S0 : state) (C0 : execution_ctx) (exte : ext_expr) (o : out),
        @eq (option out)
          (out_of_ext_expr
             (spec_object_define_own_prop_array_3c a1 a2 a3 a4 a5 a6 a7))
          (@Some out oo) ->
        abort oo ->
        not
          (abort_intercepted_expr
             (spec_object_define_own_prop_array_3c a1 a2 a3 a4 a5 a6 a7)) ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq ext_expr exte
          (spec_object_define_own_prop_array_3c a1 a2 a3 a4 a5 a6 a7) ->
        @eq out o oo -> P S C a1 a2 a3 a4 a5 a6 a7 oo) ->
       (red_expr S C
          (spec_object_define_own_prop_array_3c a1 a2 a3 a4 a5 a6 a7) oo ->
        forall (S0 S' : state) (C0 : execution_ctx) 
          (l : object_loc) (v : value) (ilen : Z) (Desc : descriptor)
          (throw : bool) (Ad : attributes_data) (oldLen : Z) 
          (o o1 : out),
        red_expr S' C (spec_to_number a2) o1 ->
        red_expr S' C
          (spec_object_define_own_prop_array_3d_e a1 o1 ilen a4 a5
             (descriptor_of_attributes (attributes_data_of Ad)) a7) oo ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq object_loc l a1 ->
        @eq value v a2 ->
        @eq (specret Z) (@ret Z S' ilen) a3 ->
        @eq descriptor Desc a4 ->
        @eq bool throw a5 ->
        @eq descriptor
          (descriptor_intro (@Some value (attributes_data_value Ad))
             (@Some bool (attributes_data_writable Ad)) 
             (@None value) (@None value)
             (@Some bool (attributes_data_enumerable Ad))
             (@Some bool (attributes_data_configurable Ad))) a6 ->
        @eq Z oldLen a7 ->
        @eq out o oo ->
        P S C a1 a2 (@ret Z S' ilen) a4 a5
          (descriptor_intro (@Some value (attributes_data_value Ad))
             (@Some bool (attributes_data_writable Ad)) 
             (@None value) (@None value)
             (@Some bool (attributes_data_enumerable Ad))
             (@Some bool (attributes_data_configurable Ad))) a7 oo) ->
       red_expr S C
         (spec_object_define_own_prop_array_3c a1 a2 a3 a4 a5 a6 a7) oo ->
       P S C a1 a2 a3 a4 a5 a6 a7 oo.

Parameter inv_red_expr_spec_object_define_own_prop_array_3d_e
     : forall (S : state) (C : execution_ctx) (a1 : object_loc) 
         (a2 : out) (a3 : Z) (a4 : descriptor) (a5 : bool) 
         (a6 : descriptor) (a7 : Z) (oo : out)
         (P : state ->
              execution_ctx ->
              object_loc ->
              out ->
              Z -> descriptor -> bool -> descriptor -> Z -> out -> Prop),
       (red_expr S C
          (spec_object_define_own_prop_array_3d_e a1 a2 a3 a4 a5 a6 a7) oo ->
        forall (S0 : state) (C0 : execution_ctx) (exte : ext_expr) (o : out),
        @eq (option out)
          (out_of_ext_expr
             (spec_object_define_own_prop_array_3d_e a1 a2 a3 a4 a5 a6 a7))
          (@Some out oo) ->
        abort oo ->
        not
          (abort_intercepted_expr
             (spec_object_define_own_prop_array_3d_e a1 a2 a3 a4 a5 a6 a7)) ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq ext_expr exte
          (spec_object_define_own_prop_array_3d_e a1 a2 a3 a4 a5 a6 a7) ->
        @eq out o oo -> P S C a1 a2 a3 a4 a5 a6 a7 oo) ->
       (red_expr S C
          (spec_object_define_own_prop_array_3d_e a1 a2 a3 a4 a5 a6 a7) oo ->
        forall (S0 S' : state) (C0 : execution_ctx) 
          (l : object_loc) (ilen : Z) (nlen : JsNumber.number)
          (Desc : descriptor) (throw : bool) (Ad : attributes_data)
          (oldLen : Z) (o : out),
        not (@eq JsNumber.number (JsNumber.of_int a3) nlen) ->
        red_expr S' C (spec_error native_error_range) oo ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq object_loc l a1 ->
        @eq out (out_ter S' (res_val (value_prim (prim_number nlen)))) a2 ->
        @eq Z ilen a3 ->
        @eq descriptor Desc a4 ->
        @eq bool throw a5 ->
        @eq descriptor
          (descriptor_intro (@Some value (attributes_data_value Ad))
             (@Some bool (attributes_data_writable Ad)) 
             (@None value) (@None value)
             (@Some bool (attributes_data_enumerable Ad))
             (@Some bool (attributes_data_configurable Ad))) a6 ->
        @eq Z oldLen a7 ->
        @eq out o oo ->
        P S C a1 (out_ter S' (res_val (value_prim (prim_number nlen)))) a3 a4
          a5
          (descriptor_intro (@Some value (attributes_data_value Ad))
             (@Some bool (attributes_data_writable Ad)) 
             (@None value) (@None value)
             (@Some bool (attributes_data_enumerable Ad))
             (@Some bool (attributes_data_configurable Ad))) a7 oo) ->
       (red_expr S C
          (spec_object_define_own_prop_array_3d_e a1 a2 a3 a4 a5 a6 a7) oo ->
        forall (S0 S' : state) (C0 : execution_ctx) 
          (l : object_loc) (ilen : Z) (nlen : JsNumber.number)
          (newLenDesc : descriptor) (throw : bool) 
          (Ad : attributes_data) (oldLen : Z) (Desc : descriptor) 
          (o : out),
        @eq JsNumber.number (JsNumber.of_int a3) nlen ->
        @eq descriptor newLenDesc
          (descriptor_with_value a4
             (@Some value (value_prim (prim_number (JsNumber.of_int a3))))) ->
        red_expr S' C
          (spec_object_define_own_prop_array_3f_g a1 a3 a7 newLenDesc a5
             (descriptor_of_attributes (attributes_data_of Ad))) oo ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq object_loc l a1 ->
        @eq out (out_ter S' (res_val (value_prim (prim_number nlen)))) a2 ->
        @eq Z ilen a3 ->
        @eq descriptor Desc a4 ->
        @eq bool throw a5 ->
        @eq descriptor
          (descriptor_intro (@Some value (attributes_data_value Ad))
             (@Some bool (attributes_data_writable Ad)) 
             (@None value) (@None value)
             (@Some bool (attributes_data_enumerable Ad))
             (@Some bool (attributes_data_configurable Ad))) a6 ->
        @eq Z oldLen a7 ->
        @eq out o oo ->
        P S C a1 (out_ter S' (res_val (value_prim (prim_number nlen)))) a3 a4
          a5
          (descriptor_intro (@Some value (attributes_data_value Ad))
             (@Some bool (attributes_data_writable Ad)) 
             (@None value) (@None value)
             (@Some bool (attributes_data_enumerable Ad))
             (@Some bool (attributes_data_configurable Ad))) a7 oo) ->
       red_expr S C
         (spec_object_define_own_prop_array_3d_e a1 a2 a3 a4 a5 a6 a7) oo ->
       P S C a1 a2 a3 a4 a5 a6 a7 oo.

Parameter inv_red_expr_spec_object_define_own_prop_array_3f_g
     : forall (S : state) (C : execution_ctx) (a1 : object_loc) 
         (a2 a3 : Z) (a4 : descriptor) (a5 : bool) 
         (a6 : descriptor) (oo : out)
         (P : state ->
              execution_ctx ->
              object_loc ->
              Z -> Z -> descriptor -> bool -> descriptor -> out -> Prop),
       (red_expr S C
          (spec_object_define_own_prop_array_3f_g a1 a2 a3 a4 a5 a6) oo ->
        forall (S0 : state) (C0 : execution_ctx) (exte : ext_expr) (o : out),
        @eq (option out)
          (out_of_ext_expr
             (spec_object_define_own_prop_array_3f_g a1 a2 a3 a4 a5 a6))
          (@Some out oo) ->
        abort oo ->
        not
          (abort_intercepted_expr
             (spec_object_define_own_prop_array_3f_g a1 a2 a3 a4 a5 a6)) ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq ext_expr exte
          (spec_object_define_own_prop_array_3f_g a1 a2 a3 a4 a5 a6) ->
        @eq out o oo -> P S C a1 a2 a3 a4 a5 a6 oo) ->
       (red_expr S C
          (spec_object_define_own_prop_array_3f_g a1 a2 a3 a4 a5 a6) oo ->
        forall (S0 : state) (C0 : execution_ctx) (l : object_loc)
          (oldLen newLen : Z) (newLenDesc : descriptor) 
          (throw : bool) (Ad : attributes_data) (o : out),
        @le Z le_int_inst a3 a2 ->
        red_expr S C
          (spec_object_define_own_prop_1 builtin_define_own_prop_default a1
             (String (Ascii false false true true false true true false)
                (String (Ascii true false true false false true true false)
                   (String (Ascii false true true true false true true false)
                      (String
                         (Ascii true true true false false true true false)
                         (String
                            (Ascii false false true false true true true
                               false)
                            (String
                               (Ascii false false false true false true true
                                  false) EmptyString)))))) a4 a5) oo ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq object_loc l a1 ->
        @eq Z newLen a2 ->
        @eq Z oldLen a3 ->
        @eq descriptor newLenDesc a4 ->
        @eq bool throw a5 ->
        @eq descriptor
          (descriptor_intro (@Some value (attributes_data_value Ad))
             (@Some bool (attributes_data_writable Ad)) 
             (@None value) (@None value)
             (@Some bool (attributes_data_enumerable Ad))
             (@Some bool (attributes_data_configurable Ad))) a6 ->
        @eq out o oo ->
        P S C a1 a2 a3 a4 a5
          (descriptor_intro (@Some value (attributes_data_value Ad))
             (@Some bool (attributes_data_writable Ad)) 
             (@None value) (@None value)
             (@Some bool (attributes_data_enumerable Ad))
             (@Some bool (attributes_data_configurable Ad))) oo) ->
       (red_expr S C
          (spec_object_define_own_prop_array_3f_g a1 a2 a3 a4 a5 a6) oo ->
        forall (S0 : state) (C0 : execution_ctx) (l : object_loc)
          (newLen oldLen : Z) (newLenDesc : descriptor) 
          (throw : bool) (Ad : attributes_data) (o : out),
        not (istrue (attributes_data_writable Ad)) ->
        red_expr S C (spec_object_define_own_prop_reject a5) oo ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq object_loc l a1 ->
        @eq Z newLen a2 ->
        @eq Z oldLen a3 ->
        @eq descriptor newLenDesc a4 ->
        @eq bool throw a5 ->
        @eq descriptor
          (descriptor_intro (@Some value (attributes_data_value Ad))
             (@Some bool (attributes_data_writable Ad)) 
             (@None value) (@None value)
             (@Some bool (attributes_data_enumerable Ad))
             (@Some bool (attributes_data_configurable Ad))) a6 ->
        @eq out o oo ->
        P S C a1 a2 a3 a4 a5
          (descriptor_intro (@Some value (attributes_data_value Ad))
             (@Some bool (attributes_data_writable Ad)) 
             (@None value) (@None value)
             (@Some bool (attributes_data_enumerable Ad))
             (@Some bool (attributes_data_configurable Ad))) oo) ->
       (red_expr S C
          (spec_object_define_own_prop_array_3f_g a1 a2 a3 a4 a5 a6) oo ->
        forall (S0 : state) (C0 : execution_ctx) (l : object_loc)
          (newLen oldLen : Z) (newLenDesc : descriptor) 
          (throw : bool) (Ad : attributes_data) (o : out),
        istrue (attributes_data_writable Ad) ->
        red_expr S C
          (spec_object_define_own_prop_array_3h_i a1 a2 a3 a4 a5
             (descriptor_of_attributes (attributes_data_of Ad))) oo ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq object_loc l a1 ->
        @eq Z newLen a2 ->
        @eq Z oldLen a3 ->
        @eq descriptor newLenDesc a4 ->
        @eq bool throw a5 ->
        @eq descriptor
          (descriptor_intro (@Some value (attributes_data_value Ad))
             (@Some bool (attributes_data_writable Ad)) 
             (@None value) (@None value)
             (@Some bool (attributes_data_enumerable Ad))
             (@Some bool (attributes_data_configurable Ad))) a6 ->
        @eq out o oo ->
        P S C a1 a2 a3 a4 a5
          (descriptor_intro (@Some value (attributes_data_value Ad))
             (@Some bool (attributes_data_writable Ad)) 
             (@None value) (@None value)
             (@Some bool (attributes_data_enumerable Ad))
             (@Some bool (attributes_data_configurable Ad))) oo) ->
       red_expr S C
         (spec_object_define_own_prop_array_3f_g a1 a2 a3 a4 a5 a6) oo ->
       P S C a1 a2 a3 a4 a5 a6 oo.

Parameter inv_red_expr_spec_object_define_own_prop_array_3h_i
     : forall (S : state) (C : execution_ctx) (a1 : object_loc) 
         (a2 a3 : Z) (a4 : descriptor) (a5 : bool) 
         (a6 : descriptor) (oo : out)
         (P : state ->
              execution_ctx ->
              object_loc ->
              Z -> Z -> descriptor -> bool -> descriptor -> out -> Prop),
       (red_expr S C
          (spec_object_define_own_prop_array_3h_i a1 a2 a3 a4 a5 a6) oo ->
        forall (S0 : state) (C0 : execution_ctx) (exte : ext_expr) (o : out),
        @eq (option out)
          (out_of_ext_expr
             (spec_object_define_own_prop_array_3h_i a1 a2 a3 a4 a5 a6))
          (@Some out oo) ->
        abort oo ->
        not
          (abort_intercepted_expr
             (spec_object_define_own_prop_array_3h_i a1 a2 a3 a4 a5 a6)) ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq ext_expr exte
          (spec_object_define_own_prop_array_3h_i a1 a2 a3 a4 a5 a6) ->
        @eq out o oo -> P S C a1 a2 a3 a4 a5 a6 oo) ->
       (red_expr S C
          (spec_object_define_own_prop_array_3h_i a1 a2 a3 a4 a5 a6) oo ->
        forall (S0 : state) (C0 : execution_ctx) (l : object_loc)
          (newLen oldLen : Z) (newLenDesc : descriptor) 
          (throw : bool) (Ad : attributes_data) (o : out),
        Logic.or (@eq (option bool) (descriptor_writable a4) (@None bool))
          (@eq (option bool) (descriptor_writable a4) (@Some bool true)) ->
        red_expr S C
          (spec_object_define_own_prop_array_3j a1 a2 a3 a4 true a5
             (descriptor_of_attributes (attributes_data_of Ad))) oo ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq object_loc l a1 ->
        @eq Z newLen a2 ->
        @eq Z oldLen a3 ->
        @eq descriptor newLenDesc a4 ->
        @eq bool throw a5 ->
        @eq descriptor
          (descriptor_intro (@Some value (attributes_data_value Ad))
             (@Some bool (attributes_data_writable Ad)) 
             (@None value) (@None value)
             (@Some bool (attributes_data_enumerable Ad))
             (@Some bool (attributes_data_configurable Ad))) a6 ->
        @eq out o oo ->
        P S C a1 a2 a3 a4 a5
          (descriptor_intro (@Some value (attributes_data_value Ad))
             (@Some bool (attributes_data_writable Ad)) 
             (@None value) (@None value)
             (@Some bool (attributes_data_enumerable Ad))
             (@Some bool (attributes_data_configurable Ad))) oo) ->
       (red_expr S C
          (spec_object_define_own_prop_array_3h_i a1 a2 a3 a4 a5 a6) oo ->
        forall (S0 : state) (C0 : execution_ctx) (l : object_loc)
          (newLen oldLen : Z) (newLenDesc : descriptor) 
          (throw : bool) (Ad : attributes_data) (o : out),
        @eq (option bool) (descriptor_writable a4) (@Some bool false) ->
        red_expr S C
          (spec_object_define_own_prop_array_3j a1 a2 a3
             (descriptor_with_writable a4 (@Some bool true)) false a5
             (descriptor_of_attributes (attributes_data_of Ad))) oo ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq object_loc l a1 ->
        @eq Z newLen a2 ->
        @eq Z oldLen a3 ->
        @eq descriptor newLenDesc a4 ->
        @eq bool throw a5 ->
        @eq descriptor
          (descriptor_intro (@Some value (attributes_data_value Ad))
             (@Some bool (attributes_data_writable Ad)) 
             (@None value) (@None value)
             (@Some bool (attributes_data_enumerable Ad))
             (@Some bool (attributes_data_configurable Ad))) a6 ->
        @eq out o oo ->
        P S C a1 a2 a3 a4 a5
          (descriptor_intro (@Some value (attributes_data_value Ad))
             (@Some bool (attributes_data_writable Ad)) 
             (@None value) (@None value)
             (@Some bool (attributes_data_enumerable Ad))
             (@Some bool (attributes_data_configurable Ad))) oo) ->
       red_expr S C
         (spec_object_define_own_prop_array_3h_i a1 a2 a3 a4 a5 a6) oo ->
       P S C a1 a2 a3 a4 a5 a6 oo.

Parameter inv_red_expr_spec_object_define_own_prop_array_3j
     : forall (S : state) (C : execution_ctx) (a1 : object_loc) 
         (a2 a3 : Z) (a4 : descriptor) (a5 a6 : bool) 
         (a7 : descriptor) (oo : out)
         (P : state ->
              execution_ctx ->
              object_loc ->
              Z ->
              Z -> descriptor -> bool -> bool -> descriptor -> out -> Prop),
       (red_expr S C
          (spec_object_define_own_prop_array_3j a1 a2 a3 a4 a5 a6 a7) oo ->
        forall (S0 : state) (C0 : execution_ctx) (exte : ext_expr) (o : out),
        @eq (option out)
          (out_of_ext_expr
             (spec_object_define_own_prop_array_3j a1 a2 a3 a4 a5 a6 a7))
          (@Some out oo) ->
        abort oo ->
        not
          (abort_intercepted_expr
             (spec_object_define_own_prop_array_3j a1 a2 a3 a4 a5 a6 a7)) ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq ext_expr exte
          (spec_object_define_own_prop_array_3j a1 a2 a3 a4 a5 a6 a7) ->
        @eq out o oo -> P S C a1 a2 a3 a4 a5 a6 a7 oo) ->
       (red_expr S C
          (spec_object_define_own_prop_array_3j a1 a2 a3 a4 a5 a6 a7) oo ->
        forall (S0 : state) (C0 : execution_ctx) (l : object_loc)
          (newLen oldLen : Z) (newLenDesc : descriptor)
          (newWritable throw : bool) (Ad : attributes_data) 
          (o1 o : out),
        red_expr S C
          (spec_object_define_own_prop_1 builtin_define_own_prop_default a1
             (String (Ascii false false true true false true true false)
                (String (Ascii true false true false false true true false)
                   (String (Ascii false true true true false true true false)
                      (String
                         (Ascii true true true false false true true false)
                         (String
                            (Ascii false false true false true true true
                               false)
                            (String
                               (Ascii false false false true false true true
                                  false) EmptyString)))))) a4 a6) o1 ->
        red_expr S C
          (spec_object_define_own_prop_array_3k_l a1 o1 a2 a3 a4 a5 a6
             (descriptor_of_attributes (attributes_data_of Ad))) oo ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq object_loc l a1 ->
        @eq Z newLen a2 ->
        @eq Z oldLen a3 ->
        @eq descriptor newLenDesc a4 ->
        @eq bool newWritable a5 ->
        @eq bool throw a6 ->
        @eq descriptor
          (descriptor_intro (@Some value (attributes_data_value Ad))
             (@Some bool (attributes_data_writable Ad)) 
             (@None value) (@None value)
             (@Some bool (attributes_data_enumerable Ad))
             (@Some bool (attributes_data_configurable Ad))) a7 ->
        @eq out o oo ->
        P S C a1 a2 a3 a4 a5 a6
          (descriptor_intro (@Some value (attributes_data_value Ad))
             (@Some bool (attributes_data_writable Ad)) 
             (@None value) (@None value)
             (@Some bool (attributes_data_enumerable Ad))
             (@Some bool (attributes_data_configurable Ad))) oo) ->
       red_expr S C
         (spec_object_define_own_prop_array_3j a1 a2 a3 a4 a5 a6 a7) oo ->
       P S C a1 a2 a3 a4 a5 a6 a7 oo.

Parameter inv_red_expr_spec_object_define_own_prop_array_3k_l
     : forall (S : state) (C : execution_ctx) (a1 : object_loc) 
         (a2 : out) (a3 a4 : Z) (a5 : descriptor) (a6 a7 : bool)
         (a8 : descriptor) (oo : out)
         (P : state ->
              execution_ctx ->
              object_loc ->
              out ->
              Z ->
              Z -> descriptor -> bool -> bool -> descriptor -> out -> Prop),
       (red_expr S C
          (spec_object_define_own_prop_array_3k_l a1 a2 a3 a4 a5 a6 a7 a8) oo ->
        forall (S0 : state) (C0 : execution_ctx) (exte : ext_expr) (o : out),
        @eq (option out)
          (out_of_ext_expr
             (spec_object_define_own_prop_array_3k_l a1 a2 a3 a4 a5 a6 a7 a8))
          (@Some out oo) ->
        abort oo ->
        not
          (abort_intercepted_expr
             (spec_object_define_own_prop_array_3k_l a1 a2 a3 a4 a5 a6 a7 a8)) ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq ext_expr exte
          (spec_object_define_own_prop_array_3k_l a1 a2 a3 a4 a5 a6 a7 a8) ->
        @eq out o oo -> P S C a1 a2 a3 a4 a5 a6 a7 a8 oo) ->
       (red_expr S C
          (spec_object_define_own_prop_array_3k_l a1 a2 a3 a4 a5 a6 a7 a8) oo ->
        forall (S0 S' : state) (C0 : execution_ctx) 
          (l : object_loc) (newLen oldLen : Z) (newLenDesc : descriptor)
          (newWritable throw : bool) (Ad : attributes_data),
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq object_loc l a1 ->
        @eq out (out_ter S' (res_val (value_prim (prim_bool false)))) a2 ->
        @eq Z newLen a3 ->
        @eq Z oldLen a4 ->
        @eq descriptor newLenDesc a5 ->
        @eq bool newWritable a6 ->
        @eq bool throw a7 ->
        @eq descriptor
          (descriptor_intro (@Some value (attributes_data_value Ad))
             (@Some bool (attributes_data_writable Ad)) 
             (@None value) (@None value)
             (@Some bool (attributes_data_enumerable Ad))
             (@Some bool (attributes_data_configurable Ad))) a8 ->
        @eq out (out_ter S' (res_val (value_prim (prim_bool false)))) oo ->
        P S C a1 (out_ter S' (res_val (value_prim (prim_bool false)))) a3 a4
          a5 a6 a7
          (descriptor_intro (@Some value (attributes_data_value Ad))
             (@Some bool (attributes_data_writable Ad)) 
             (@None value) (@None value)
             (@Some bool (attributes_data_enumerable Ad))
             (@Some bool (attributes_data_configurable Ad)))
          (out_ter S' (res_val (value_prim (prim_bool false))))) ->
       (red_expr S C
          (spec_object_define_own_prop_array_3k_l a1 a2 a3 a4 a5 a6 a7 a8) oo ->
        forall (S0 S' : state) (C0 : execution_ctx) 
          (l : object_loc) (newLen oldLen : Z) (newLenDesc : descriptor)
          (newWritable throw : bool) (Ad : attributes_data) 
          (o : out),
        red_expr S' C
          (spec_object_define_own_prop_array_3l a1 a3 a4 a5 a6 a7) oo ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq object_loc l a1 ->
        @eq out (out_ter S' (res_val (value_prim (prim_bool true)))) a2 ->
        @eq Z newLen a3 ->
        @eq Z oldLen a4 ->
        @eq descriptor newLenDesc a5 ->
        @eq bool newWritable a6 ->
        @eq bool throw a7 ->
        @eq descriptor
          (descriptor_intro (@Some value (attributes_data_value Ad))
             (@Some bool (attributes_data_writable Ad)) 
             (@None value) (@None value)
             (@Some bool (attributes_data_enumerable Ad))
             (@Some bool (attributes_data_configurable Ad))) a8 ->
        @eq out o oo ->
        P S C a1 (out_ter S' (res_val (value_prim (prim_bool true)))) a3 a4
          a5 a6 a7
          (descriptor_intro (@Some value (attributes_data_value Ad))
             (@Some bool (attributes_data_writable Ad)) 
             (@None value) (@None value)
             (@Some bool (attributes_data_enumerable Ad))
             (@Some bool (attributes_data_configurable Ad))) oo) ->
       red_expr S C
         (spec_object_define_own_prop_array_3k_l a1 a2 a3 a4 a5 a6 a7 a8) oo ->
       P S C a1 a2 a3 a4 a5 a6 a7 a8 oo.

Parameter inv_red_expr_spec_object_define_own_prop_array_3l
     : forall (S : state) (C : execution_ctx) (a1 : object_loc) 
         (a2 a3 : Z) (a4 : descriptor) (a5 a6 : bool) 
         (oo : out)
         (P : state ->
              execution_ctx ->
              object_loc ->
              Z -> Z -> descriptor -> bool -> bool -> out -> Prop),
       (red_expr S C (spec_object_define_own_prop_array_3l a1 a2 a3 a4 a5 a6)
          oo ->
        forall (S0 : state) (C0 : execution_ctx) (exte : ext_expr) (o : out),
        @eq (option out)
          (out_of_ext_expr
             (spec_object_define_own_prop_array_3l a1 a2 a3 a4 a5 a6))
          (@Some out oo) ->
        abort oo ->
        not
          (abort_intercepted_expr
             (spec_object_define_own_prop_array_3l a1 a2 a3 a4 a5 a6)) ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq ext_expr exte
          (spec_object_define_own_prop_array_3l a1 a2 a3 a4 a5 a6) ->
        @eq out o oo -> P S C a1 a2 a3 a4 a5 a6 oo) ->
       (red_expr S C (spec_object_define_own_prop_array_3l a1 a2 a3 a4 a5 a6)
          oo ->
        forall (S0 : state) (C0 : execution_ctx) (l : object_loc)
          (newLen oldLen : Z) (newLenDesc : descriptor)
          (newWritable throw : bool) (o : out),
        @lt Z (@lt_from_le Z le_int_inst) a2 a3 ->
        red_expr S C
          (spec_object_define_own_prop_array_3l_ii a1 a2 
             (Z.sub a3 (Zpos xH)) a4 a5 a6) oo ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq object_loc l a1 ->
        @eq Z newLen a2 ->
        @eq Z oldLen a3 ->
        @eq descriptor newLenDesc a4 ->
        @eq bool newWritable a5 ->
        @eq bool throw a6 -> @eq out o oo -> P S C a1 a2 a3 a4 a5 a6 oo) ->
       (red_expr S C (spec_object_define_own_prop_array_3l a1 a2 a3 a4 a5 a6)
          oo ->
        forall (S0 : state) (C0 : execution_ctx) (l : object_loc)
          (newLen oldLen : Z) (newLenDesc : descriptor)
          (newWritable throw : bool) (o : out),
        not (@lt Z (@lt_from_le Z le_int_inst) a2 a3) ->
        red_expr S C (spec_object_define_own_prop_array_3m_n a1 a5) oo ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq object_loc l a1 ->
        @eq Z newLen a2 ->
        @eq Z oldLen a3 ->
        @eq descriptor newLenDesc a4 ->
        @eq bool newWritable a5 ->
        @eq bool throw a6 -> @eq out o oo -> P S C a1 a2 a3 a4 a5 a6 oo) ->
       red_expr S C (spec_object_define_own_prop_array_3l a1 a2 a3 a4 a5 a6)
         oo -> P S C a1 a2 a3 a4 a5 a6 oo.

Parameter inv_red_expr_spec_object_define_own_prop_array_3l_ii
     : forall (S : state) (C : execution_ctx) (a1 : object_loc) 
         (a2 a3 : Z) (a4 : descriptor) (a5 a6 : bool) 
         (oo : out)
         (P : state ->
              execution_ctx ->
              object_loc ->
              Z -> Z -> descriptor -> bool -> bool -> out -> Prop),
       (red_expr S C
          (spec_object_define_own_prop_array_3l_ii a1 a2 a3 a4 a5 a6) oo ->
        forall (S0 : state) (C0 : execution_ctx) (exte : ext_expr) (o : out),
        @eq (option out)
          (out_of_ext_expr
             (spec_object_define_own_prop_array_3l_ii a1 a2 a3 a4 a5 a6))
          (@Some out oo) ->
        abort oo ->
        not
          (abort_intercepted_expr
             (spec_object_define_own_prop_array_3l_ii a1 a2 a3 a4 a5 a6)) ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq ext_expr exte
          (spec_object_define_own_prop_array_3l_ii a1 a2 a3 a4 a5 a6) ->
        @eq out o oo -> P S C a1 a2 a3 a4 a5 a6 oo) ->
       (red_expr S C
          (spec_object_define_own_prop_array_3l_ii a1 a2 a3 a4 a5 a6) oo ->
        forall (S0 : state) (C0 : execution_ctx) (l : object_loc)
          (newLen oldLen : Z) (newLenDesc : descriptor)
          (newWritable throw : bool) (o1 o : out),
        red_expr S C
          (spec_to_string (value_prim (prim_number (JsNumber.of_int a3)))) o1 ->
        red_expr S C
          (spec_object_define_own_prop_array_3l_ii_1 a1 a2 a3 a4 a5 a6 o1) oo ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq object_loc l a1 ->
        @eq Z newLen a2 ->
        @eq Z oldLen a3 ->
        @eq descriptor newLenDesc a4 ->
        @eq bool newWritable a5 ->
        @eq bool throw a6 -> @eq out o oo -> P S C a1 a2 a3 a4 a5 a6 oo) ->
       red_expr S C
         (spec_object_define_own_prop_array_3l_ii a1 a2 a3 a4 a5 a6) oo ->
       P S C a1 a2 a3 a4 a5 a6 oo.

Parameter inv_red_expr_spec_object_define_own_prop_array_3l_ii_1
     : forall (S : state) (C : execution_ctx) (a1 : object_loc) 
         (a2 a3 : Z) (a4 : descriptor) (a5 a6 : bool) 
         (a7 oo : out)
         (P : state ->
              execution_ctx ->
              object_loc ->
              Z -> Z -> descriptor -> bool -> bool -> out -> out -> Prop),
       (red_expr S C
          (spec_object_define_own_prop_array_3l_ii_1 a1 a2 a3 a4 a5 a6 a7) oo ->
        forall (S0 : state) (C0 : execution_ctx) (exte : ext_expr) (o : out),
        @eq (option out)
          (out_of_ext_expr
             (spec_object_define_own_prop_array_3l_ii_1 a1 a2 a3 a4 a5 a6 a7))
          (@Some out oo) ->
        abort oo ->
        not
          (abort_intercepted_expr
             (spec_object_define_own_prop_array_3l_ii_1 a1 a2 a3 a4 a5 a6 a7)) ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq ext_expr exte
          (spec_object_define_own_prop_array_3l_ii_1 a1 a2 a3 a4 a5 a6 a7) ->
        @eq out o oo -> P S C a1 a2 a3 a4 a5 a6 a7 oo) ->
       (red_expr S C
          (spec_object_define_own_prop_array_3l_ii_1 a1 a2 a3 a4 a5 a6 a7) oo ->
        forall (S0 S' : state) (C0 : execution_ctx) 
          (l : object_loc) (x : prop_name) (newLen oldLen : Z)
          (newLenDesc : descriptor) (newWritable throw : bool) 
          (o1 o : out),
        red_expr S' C (spec_object_delete a1 x false) o1 ->
        red_expr S' C
          (spec_object_define_own_prop_array_3l_ii_2 a1 a2 a3 a4 a5 a6 o1) oo ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq object_loc l a1 ->
        @eq Z newLen a2 ->
        @eq Z oldLen a3 ->
        @eq descriptor newLenDesc a4 ->
        @eq bool newWritable a5 ->
        @eq bool throw a6 ->
        @eq out (out_ter S' (res_val (value_prim (prim_string x)))) a7 ->
        @eq out o oo ->
        P S C a1 a2 a3 a4 a5 a6
          (out_ter S' (res_val (value_prim (prim_string x)))) oo) ->
       red_expr S C
         (spec_object_define_own_prop_array_3l_ii_1 a1 a2 a3 a4 a5 a6 a7) oo ->
       P S C a1 a2 a3 a4 a5 a6 a7 oo.

Parameter inv_red_expr_spec_object_define_own_prop_array_3l_ii_2
     : forall (S : state) (C : execution_ctx) (a1 : object_loc) 
         (a2 a3 : Z) (a4 : descriptor) (a5 a6 : bool) 
         (a7 oo : out)
         (P : state ->
              execution_ctx ->
              object_loc ->
              Z -> Z -> descriptor -> bool -> bool -> out -> out -> Prop),
       (red_expr S C
          (spec_object_define_own_prop_array_3l_ii_2 a1 a2 a3 a4 a5 a6 a7) oo ->
        forall (S0 : state) (C0 : execution_ctx) (exte : ext_expr) (o : out),
        @eq (option out)
          (out_of_ext_expr
             (spec_object_define_own_prop_array_3l_ii_2 a1 a2 a3 a4 a5 a6 a7))
          (@Some out oo) ->
        abort oo ->
        not
          (abort_intercepted_expr
             (spec_object_define_own_prop_array_3l_ii_2 a1 a2 a3 a4 a5 a6 a7)) ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq ext_expr exte
          (spec_object_define_own_prop_array_3l_ii_2 a1 a2 a3 a4 a5 a6 a7) ->
        @eq out o oo -> P S C a1 a2 a3 a4 a5 a6 a7 oo) ->
       (red_expr S C
          (spec_object_define_own_prop_array_3l_ii_2 a1 a2 a3 a4 a5 a6 a7) oo ->
        forall (S0 S' : state) (C0 : execution_ctx) 
          (l : object_loc) (newLen oldLen : Z) (newLenDesc : descriptor)
          (newWritable throw : bool) (o : out),
        red_expr S' C
          (spec_object_define_own_prop_array_3l a1 a2 a3 a4 a5 a6) oo ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq object_loc l a1 ->
        @eq Z newLen a2 ->
        @eq Z oldLen a3 ->
        @eq descriptor newLenDesc a4 ->
        @eq bool newWritable a5 ->
        @eq bool throw a6 ->
        @eq out (out_ter S' (res_val (value_prim (prim_bool true)))) a7 ->
        @eq out o oo ->
        P S C a1 a2 a3 a4 a5 a6
          (out_ter S' (res_val (value_prim (prim_bool true)))) oo) ->
       (red_expr S C
          (spec_object_define_own_prop_array_3l_ii_2 a1 a2 a3 a4 a5 a6 a7) oo ->
        forall (S0 S' : state) (C0 : execution_ctx) 
          (l : object_loc) (newLen oldLen : Z) (newLenDesc : descriptor)
          (newWritable throw : bool) (o : out),
        red_expr S' C
          (spec_object_define_own_prop_array_3l_iii_1 a1 a3 a4 a5 a6) oo ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq object_loc l a1 ->
        @eq Z newLen a2 ->
        @eq Z oldLen a3 ->
        @eq descriptor newLenDesc a4 ->
        @eq bool newWritable a5 ->
        @eq bool throw a6 ->
        @eq out (out_ter S' (res_val (value_prim (prim_bool false)))) a7 ->
        @eq out o oo ->
        P S C a1 a2 a3 a4 a5 a6
          (out_ter S' (res_val (value_prim (prim_bool false)))) oo) ->
       red_expr S C
         (spec_object_define_own_prop_array_3l_ii_2 a1 a2 a3 a4 a5 a6 a7) oo ->
       P S C a1 a2 a3 a4 a5 a6 a7 oo.

Parameter inv_red_expr_spec_object_define_own_prop_array_3l_iii_1
     : forall (S : state) (C : execution_ctx) (a1 : object_loc) 
         (a2 : Z) (a3 : descriptor) (a4 a5 : bool) 
         (oo : out)
         (P : state ->
              execution_ctx ->
              object_loc -> Z -> descriptor -> bool -> bool -> out -> Prop),
       (red_expr S C
          (spec_object_define_own_prop_array_3l_iii_1 a1 a2 a3 a4 a5) oo ->
        forall (S0 : state) (C0 : execution_ctx) (exte : ext_expr) (o : out),
        @eq (option out)
          (out_of_ext_expr
             (spec_object_define_own_prop_array_3l_iii_1 a1 a2 a3 a4 a5))
          (@Some out oo) ->
        abort oo ->
        not
          (abort_intercepted_expr
             (spec_object_define_own_prop_array_3l_iii_1 a1 a2 a3 a4 a5)) ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq ext_expr exte
          (spec_object_define_own_prop_array_3l_iii_1 a1 a2 a3 a4 a5) ->
        @eq out o oo -> P S C a1 a2 a3 a4 a5 oo) ->
       (red_expr S C
          (spec_object_define_own_prop_array_3l_iii_1 a1 a2 a3 a4 a5) oo ->
        forall (S0 : state) (C0 : execution_ctx) (l : object_loc)
          (oldLen : Z) (newLenDesc newLenDesc' : descriptor)
          (newWritable throw : bool) (o : out),
        @eq descriptor newLenDesc'
          (descriptor_with_value a3
             (@Some value
                (value_prim
                   (prim_number (JsNumber.of_int (Z.add a2 (Zpos xH))))))) ->
        red_expr S C
          (spec_object_define_own_prop_array_3l_iii_2 a1 newLenDesc' a4 a5)
          oo ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq object_loc l a1 ->
        @eq Z oldLen a2 ->
        @eq descriptor newLenDesc a3 ->
        @eq bool newWritable a4 ->
        @eq bool throw a5 -> @eq out o oo -> P S C a1 a2 a3 a4 a5 oo) ->
       red_expr S C
         (spec_object_define_own_prop_array_3l_iii_1 a1 a2 a3 a4 a5) oo ->
       P S C a1 a2 a3 a4 a5 oo.

Parameter inv_red_expr_spec_object_define_own_prop_array_3l_iii_2
     : forall (S : state) (C : execution_ctx) (a1 : object_loc)
         (a2 : descriptor) (a3 a4 : bool) (oo : out)
         (P : state ->
              execution_ctx ->
              object_loc -> descriptor -> bool -> bool -> out -> Prop),
       (red_expr S C (spec_object_define_own_prop_array_3l_iii_2 a1 a2 a3 a4)
          oo ->
        forall (S0 : state) (C0 : execution_ctx) (exte : ext_expr) (o : out),
        @eq (option out)
          (out_of_ext_expr
             (spec_object_define_own_prop_array_3l_iii_2 a1 a2 a3 a4))
          (@Some out oo) ->
        abort oo ->
        not
          (abort_intercepted_expr
             (spec_object_define_own_prop_array_3l_iii_2 a1 a2 a3 a4)) ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq ext_expr exte
          (spec_object_define_own_prop_array_3l_iii_2 a1 a2 a3 a4) ->
        @eq out o oo -> P S C a1 a2 a3 a4 oo) ->
       (red_expr S C (spec_object_define_own_prop_array_3l_iii_2 a1 a2 a3 a4)
          oo ->
        forall (S0 : state) (C0 : execution_ctx) (l : object_loc)
          (newLenDesc : descriptor) (o : out) (throw : bool),
        red_expr S C
          (spec_object_define_own_prop_array_3l_iii_3 a1
             (descriptor_with_writable a2 (@Some bool false)) a4) oo ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq object_loc l a1 ->
        @eq descriptor newLenDesc a2 ->
        @eq bool false a3 ->
        @eq bool throw a4 -> @eq out o oo -> P S C a1 a2 false a4 oo) ->
       (red_expr S C (spec_object_define_own_prop_array_3l_iii_2 a1 a2 a3 a4)
          oo ->
        forall (S0 : state) (C0 : execution_ctx) (l : object_loc)
          (newLenDesc : descriptor) (o : out) (throw : bool),
        red_expr S C (spec_object_define_own_prop_array_3l_iii_3 a1 a2 a4) oo ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq object_loc l a1 ->
        @eq descriptor newLenDesc a2 ->
        @eq bool true a3 ->
        @eq bool throw a4 -> @eq out o oo -> P S C a1 a2 true a4 oo) ->
       red_expr S C (spec_object_define_own_prop_array_3l_iii_2 a1 a2 a3 a4)
         oo -> P S C a1 a2 a3 a4 oo.

Parameter inv_red_expr_spec_object_define_own_prop_array_3l_iii_3
     : forall (S : state) (C : execution_ctx) (a1 : object_loc)
         (a2 : descriptor) (a3 : bool) (oo : out)
         (P : state ->
              execution_ctx ->
              object_loc -> descriptor -> bool -> out -> Prop),
       (red_expr S C (spec_object_define_own_prop_array_3l_iii_3 a1 a2 a3) oo ->
        forall (S0 : state) (C0 : execution_ctx) (exte : ext_expr) (o : out),
        @eq (option out)
          (out_of_ext_expr
             (spec_object_define_own_prop_array_3l_iii_3 a1 a2 a3))
          (@Some out oo) ->
        abort oo ->
        not
          (abort_intercepted_expr
             (spec_object_define_own_prop_array_3l_iii_3 a1 a2 a3)) ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq ext_expr exte
          (spec_object_define_own_prop_array_3l_iii_3 a1 a2 a3) ->
        @eq out o oo -> P S C a1 a2 a3 oo) ->
       (red_expr S C (spec_object_define_own_prop_array_3l_iii_3 a1 a2 a3) oo ->
        forall (S0 : state) (C0 : execution_ctx) (l : object_loc)
          (newLenDesc : descriptor) (o1 o : out) (throw : bool),
        red_expr S C
          (spec_object_define_own_prop_1 builtin_define_own_prop_default a1
             (String (Ascii false false true true false true true false)
                (String (Ascii true false true false false true true false)
                   (String (Ascii false true true true false true true false)
                      (String
                         (Ascii true true true false false true true false)
                         (String
                            (Ascii false false true false true true true
                               false)
                            (String
                               (Ascii false false false true false true true
                                  false) EmptyString)))))) a2 false) o1 ->
        red_expr S C (spec_object_define_own_prop_array_3l_iii_4 a1 a3 o1) oo ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq object_loc l a1 ->
        @eq descriptor newLenDesc a2 ->
        @eq bool throw a3 -> @eq out o oo -> P S C a1 a2 a3 oo) ->
       red_expr S C (spec_object_define_own_prop_array_3l_iii_3 a1 a2 a3) oo ->
       P S C a1 a2 a3 oo.

Parameter inv_red_expr_spec_object_define_own_prop_array_3l_iii_4
     : forall (S : state) (C : execution_ctx) (a1 : object_loc) 
         (a2 : bool) (a3 oo : out)
         (P : state ->
              execution_ctx -> object_loc -> bool -> out -> out -> Prop),
       (red_expr S C (spec_object_define_own_prop_array_3l_iii_4 a1 a2 a3) oo ->
        forall (S0 : state) (C0 : execution_ctx) (exte : ext_expr) (o : out),
        @eq (option out)
          (out_of_ext_expr
             (spec_object_define_own_prop_array_3l_iii_4 a1 a2 a3))
          (@Some out oo) ->
        abort oo ->
        not
          (abort_intercepted_expr
             (spec_object_define_own_prop_array_3l_iii_4 a1 a2 a3)) ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq ext_expr exte
          (spec_object_define_own_prop_array_3l_iii_4 a1 a2 a3) ->
        @eq out o oo -> P S C a1 a2 a3 oo) ->
       (red_expr S C (spec_object_define_own_prop_array_3l_iii_4 a1 a2 a3) oo ->
        forall (S0 S' : state) (C0 : execution_ctx) 
          (l : object_loc) (b throw : bool) (o : out),
        out ->
        red_expr S' C (spec_object_define_own_prop_reject a2) oo ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq object_loc l a1 ->
        @eq bool throw a2 ->
        @eq out (out_ter S' (res_val (value_prim (prim_bool b)))) a3 ->
        @eq out o oo ->
        P S C a1 a2 (out_ter S' (res_val (value_prim (prim_bool b)))) oo) ->
       red_expr S C (spec_object_define_own_prop_array_3l_iii_4 a1 a2 a3) oo ->
       P S C a1 a2 a3 oo.

Parameter inv_red_expr_spec_object_define_own_prop_array_3m_n
     : forall (S : state) (C : execution_ctx) (a1 : object_loc) 
         (a2 : bool) (oo : out)
         (P : state -> execution_ctx -> object_loc -> bool -> out -> Prop),
       (red_expr S C (spec_object_define_own_prop_array_3m_n a1 a2) oo ->
        forall (S0 : state) (C0 : execution_ctx) (exte : ext_expr) (o : out),
        @eq (option out)
          (out_of_ext_expr (spec_object_define_own_prop_array_3m_n a1 a2))
          (@Some out oo) ->
        abort oo ->
        not
          (abort_intercepted_expr
             (spec_object_define_own_prop_array_3m_n a1 a2)) ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq ext_expr exte (spec_object_define_own_prop_array_3m_n a1 a2) ->
        @eq out o oo -> P S C a1 a2 oo) ->
       (red_expr S C (spec_object_define_own_prop_array_3m_n a1 a2) oo ->
        forall (S0 : state) (C0 : execution_ctx) (l : object_loc) (o : out),
        red_expr S C
          (spec_object_define_own_prop_1 builtin_define_own_prop_default a1
             (String (Ascii false false true true false true true false)
                (String (Ascii true false true false false true true false)
                   (String (Ascii false true true true false true true false)
                      (String
                         (Ascii true true true false false true true false)
                         (String
                            (Ascii false false true false true true true
                               false)
                            (String
                               (Ascii false false false true false true true
                                  false) EmptyString))))))
             (descriptor_intro (@None value) (@Some bool false) 
                (@None value) (@None value) (@None bool) 
                (@None bool)) false) oo ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq object_loc l a1 ->
        @eq bool false a2 -> @eq out o oo -> P S C a1 false oo) ->
       (red_expr S C (spec_object_define_own_prop_array_3m_n a1 a2) oo ->
        forall (S0 : state) (C0 : execution_ctx) (l : object_loc),
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq object_loc l a1 ->
        @eq bool true a2 ->
        @eq out (out_ter S (res_val (value_prim (prim_bool true)))) oo ->
        P S C a1 true (out_ter S (res_val (value_prim (prim_bool true))))) ->
       red_expr S C (spec_object_define_own_prop_array_3m_n a1 a2) oo ->
       P S C a1 a2 oo.

Parameter inv_red_expr_spec_prim_value_get
     : forall (S : state) (C : execution_ctx) (a1 : value) 
         (a2 : prop_name) (oo : out)
         (P : state -> execution_ctx -> value -> string -> out -> Prop),
       (red_expr S C (spec_prim_value_get a1 a2) oo ->
        forall (S0 : state) (C0 : execution_ctx) (exte : ext_expr) (o : out),
        @eq (option out) (out_of_ext_expr (spec_prim_value_get a1 a2))
          (@Some out oo) ->
        abort oo ->
        not (abort_intercepted_expr (spec_prim_value_get a1 a2)) ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq ext_expr exte (spec_prim_value_get a1 a2) ->
        @eq out o oo -> P S C a1 a2 oo) ->
       (red_expr S C (spec_prim_value_get a1 a2) oo ->
        forall (S0 : state) (C0 : execution_ctx) (v : value) 
          (x : prop_name) (o1 o : out),
        red_expr S C (spec_to_object a1) o1 ->
        red_expr S C (spec_prim_value_get_1 a1 a2 o1) oo ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq value v a1 ->
        @eq prop_name x a2 -> @eq out o oo -> P S C a1 a2 oo) ->
       red_expr S C (spec_prim_value_get a1 a2) oo -> P S C a1 a2 oo.

Parameter inv_red_expr_spec_prim_value_get_1
     : forall (S : state) (C : execution_ctx) (a1 : value) 
         (a2 : prop_name) (a3 oo : out)
         (P : state -> execution_ctx -> value -> string -> out -> out -> Prop),
       (red_expr S C (spec_prim_value_get_1 a1 a2 a3) oo ->
        forall (S0 : state) (C0 : execution_ctx) (exte : ext_expr) (o : out),
        @eq (option out) (out_of_ext_expr (spec_prim_value_get_1 a1 a2 a3))
          (@Some out oo) ->
        abort oo ->
        not (abort_intercepted_expr (spec_prim_value_get_1 a1 a2 a3)) ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq ext_expr exte (spec_prim_value_get_1 a1 a2 a3) ->
        @eq out o oo -> P S C a1 a2 a3 oo) ->
       (red_expr S C (spec_prim_value_get_1 a1 a2 a3) oo ->
        forall (S0 S1 : state) (C0 : execution_ctx) 
          (v : value) (x : prop_name) (l : object_loc) 
          (o : out),
        red_expr S1 C (spec_object_get_1 builtin_get_default a1 l a2) oo ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq value v a1 ->
        @eq prop_name x a2 ->
        @eq out (out_ter S1 (res_val (value_object l))) a3 ->
        @eq out o oo ->
        P S C a1 a2 (out_ter S1 (res_val (value_object l))) oo) ->
       red_expr S C (spec_prim_value_get_1 a1 a2 a3) oo -> P S C a1 a2 a3 oo.

Parameter inv_red_expr_spec_prim_value_put
     : forall (S : state) (C : execution_ctx) (a1 : value) 
         (a2 : prop_name) (a3 : value) (a4 : bool) 
         (oo : out)
         (P : state ->
              execution_ctx ->
              value -> string -> value -> bool -> out -> Prop),
       (red_expr S C (spec_prim_value_put a1 a2 a3 a4) oo ->
        forall (S0 : state) (C0 : execution_ctx) (exte : ext_expr) (o : out),
        @eq (option out) (out_of_ext_expr (spec_prim_value_put a1 a2 a3 a4))
          (@Some out oo) ->
        abort oo ->
        not (abort_intercepted_expr (spec_prim_value_put a1 a2 a3 a4)) ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq ext_expr exte (spec_prim_value_put a1 a2 a3 a4) ->
        @eq out o oo -> P S C a1 a2 a3 a4 oo) ->
       (red_expr S C (spec_prim_value_put a1 a2 a3 a4) oo ->
        forall (S0 : state) (C0 : execution_ctx) (w : prim) 
          (x : prop_name) (v : value) (throw : bool) 
          (o1 o : out),
        red_expr S C (spec_to_object (value_prim w)) o1 ->
        red_expr S C (spec_prim_value_put_1 w a2 a3 a4 o1) oo ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq value (value_prim w) a1 ->
        @eq prop_name x a2 ->
        @eq value v a3 ->
        @eq bool throw a4 -> @eq out o oo -> P S C (value_prim w) a2 a3 a4 oo) ->
       red_expr S C (spec_prim_value_put a1 a2 a3 a4) oo ->
       P S C a1 a2 a3 a4 oo.

Parameter inv_red_expr_spec_prim_value_put_1
     : forall (S : state) (C : execution_ctx) (a1 : prim) 
         (a2 : prop_name) (a3 : value) (a4 : bool) 
         (a5 oo : out)
         (P : state ->
              execution_ctx ->
              prim -> string -> value -> bool -> out -> out -> Prop),
       (red_expr S C (spec_prim_value_put_1 a1 a2 a3 a4 a5) oo ->
        forall (S0 : state) (C0 : execution_ctx) (exte : ext_expr) (o : out),
        @eq (option out)
          (out_of_ext_expr (spec_prim_value_put_1 a1 a2 a3 a4 a5))
          (@Some out oo) ->
        abort oo ->
        not (abort_intercepted_expr (spec_prim_value_put_1 a1 a2 a3 a4 a5)) ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq ext_expr exte (spec_prim_value_put_1 a1 a2 a3 a4 a5) ->
        @eq out o oo -> P S C a1 a2 a3 a4 a5 oo) ->
       (red_expr S C (spec_prim_value_put_1 a1 a2 a3 a4 a5) oo ->
        forall (S0 S1 : state) (C0 : execution_ctx) 
          (w : prim) (x : prop_name) (v : value) (throw : bool)
          (l : object_loc) (o : out),
        red_expr S1 C
          (spec_object_put_1 builtin_put_default (value_prim a1) l a2 a3 a4)
          oo ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq prim w a1 ->
        @eq prop_name x a2 ->
        @eq value v a3 ->
        @eq bool throw a4 ->
        @eq out (out_ter S1 (res_val (value_object l))) a5 ->
        @eq out o oo ->
        P S C a1 a2 a3 a4 (out_ter S1 (res_val (value_object l))) oo) ->
       red_expr S C (spec_prim_value_put_1 a1 a2 a3 a4 a5) oo ->
       P S C a1 a2 a3 a4 a5 oo.

Parameter inv_red_expr_spec_put_value
     : forall (S : state) (C : execution_ctx) (a1 : resvalue) 
         (a2 : value) (oo : out)
         (P : state -> execution_ctx -> resvalue -> value -> out -> Prop),
       (red_expr S C (spec_put_value a1 a2) oo ->
        forall (S0 : state) (C0 : execution_ctx) (exte : ext_expr) (o : out),
        @eq (option out) (out_of_ext_expr (spec_put_value a1 a2))
          (@Some out oo) ->
        abort oo ->
        not (abort_intercepted_expr (spec_put_value a1 a2)) ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq ext_expr exte (spec_put_value a1 a2) ->
        @eq out o oo -> P S C a1 a2 oo) ->
       (red_expr S C (spec_put_value a1 a2) oo ->
        forall (S0 : state) (C0 : execution_ctx) (v vnew : value) (o : out),
        red_expr S C (spec_error native_error_ref) oo ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq resvalue (resvalue_value v) a1 ->
        @eq value vnew a2 -> @eq out o oo -> P S C (resvalue_value v) a2 oo) ->
       (red_expr S C (spec_put_value a1 a2) oo ->
        forall (S0 : state) (C0 : execution_ctx) (r : ref) 
          (vnew : value) (o : out),
        ref_is_unresolvable r ->
        @eq bool (ref_strict r) true ->
        red_expr S C (spec_error native_error_ref) oo ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq resvalue (resvalue_ref r) a1 ->
        @eq value vnew a2 -> @eq out o oo -> P S C (resvalue_ref r) a2 oo) ->
       (red_expr S C (spec_put_value a1 a2) oo ->
        forall (o : out) (S0 : state) (C0 : execution_ctx) 
          (r : ref) (vnew : value),
        ref_is_unresolvable r ->
        @eq bool (ref_strict r) false ->
        red_expr S C
          (spec_object_put (object_loc_prealloc prealloc_global) 
             (ref_name r) a2 throw_false) oo ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq resvalue (resvalue_ref r) a1 ->
        @eq value vnew a2 -> @eq out o oo -> P S C (resvalue_ref r) a2 oo) ->
       (red_expr S C (spec_put_value a1 a2) oo ->
        forall (v : value) (S0 : state) (C0 : execution_ctx) 
          (r : ref) (vnew : value) (o : out),
        ref_is_property r ->
        @eq ref_base_type (ref_base r) (ref_base_type_value v) ->
        ref_has_primitive_base r ->
        red_expr S C (spec_prim_value_put v (ref_name r) a2 (ref_strict r))
          oo ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq resvalue (resvalue_ref r) a1 ->
        @eq value vnew a2 -> @eq out o oo -> P S C (resvalue_ref r) a2 oo) ->
       (red_expr S C (spec_put_value a1 a2) oo ->
        forall (l : object_loc) (S0 : state) (C0 : execution_ctx) 
          (r : ref) (vnew : value) (o : out),
        ref_is_property r ->
        @eq ref_base_type (ref_base r) (ref_base_type_value (value_object l)) ->
        not (ref_has_primitive_base r) ->
        red_expr S C (spec_object_put l (ref_name r) a2 (ref_strict r)) oo ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq resvalue (resvalue_ref r) a1 ->
        @eq value vnew a2 -> @eq out o oo -> P S C (resvalue_ref r) a2 oo) ->
       (red_expr S C (spec_put_value a1 a2) oo ->
        forall (L : env_loc) (S0 : state) (C0 : execution_ctx) 
          (r : ref) (vnew : value) (o : out),
        @eq ref_base_type (ref_base r) (ref_base_type_env_loc L) ->
        red_expr S C
          (spec_env_record_set_mutable_binding L (ref_name r) a2
             (ref_strict r)) oo ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq resvalue (resvalue_ref r) a1 ->
        @eq value vnew a2 -> @eq out o oo -> P S C (resvalue_ref r) a2 oo) ->
       red_expr S C (spec_put_value a1 a2) oo -> P S C a1 a2 oo.

Parameter inv_red_expr_spec_env_record_has_binding
     : forall (S : state) (C : execution_ctx) (a1 : env_loc) 
         (a2 : prop_name) (oo : out)
         (P : state -> execution_ctx -> nat -> string -> out -> Prop),
       (red_expr S C (spec_env_record_has_binding a1 a2) oo ->
        forall (S0 : state) (C0 : execution_ctx) (exte : ext_expr) (o : out),
        @eq (option out)
          (out_of_ext_expr (spec_env_record_has_binding a1 a2))
          (@Some out oo) ->
        abort oo ->
        not (abort_intercepted_expr (spec_env_record_has_binding a1 a2)) ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq ext_expr exte (spec_env_record_has_binding a1 a2) ->
        @eq out o oo -> P S C a1 a2 oo) ->
       (red_expr S C (spec_env_record_has_binding a1 a2) oo ->
        forall (S0 : state) (C0 : execution_ctx) (L : env_loc)
          (x : prop_name) (o : out) (E : env_record),
        env_record_binds S a1 E ->
        red_expr S C (spec_env_record_has_binding_1 a1 a2 E) oo ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq env_loc L a1 ->
        @eq prop_name x a2 -> @eq out o oo -> P S C a1 a2 oo) ->
       red_expr S C (spec_env_record_has_binding a1 a2) oo -> P S C a1 a2 oo.

Parameter inv_red_expr_spec_env_record_has_binding_1
     : forall (S : state) (C : execution_ctx) (a1 : env_loc) 
         (a2 : prop_name) (a3 : env_record) (oo : out)
         (P : state ->
              execution_ctx -> nat -> string -> env_record -> out -> Prop),
       (red_expr S C (spec_env_record_has_binding_1 a1 a2 a3) oo ->
        forall (S0 : state) (C0 : execution_ctx) (exte : ext_expr) (o : out),
        @eq (option out)
          (out_of_ext_expr (spec_env_record_has_binding_1 a1 a2 a3))
          (@Some out oo) ->
        abort oo ->
        not (abort_intercepted_expr (spec_env_record_has_binding_1 a1 a2 a3)) ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq ext_expr exte (spec_env_record_has_binding_1 a1 a2 a3) ->
        @eq out o oo -> P S C a1 a2 a3 oo) ->
       (red_expr S C (spec_env_record_has_binding_1 a1 a2 a3) oo ->
        forall (S0 : state) (C0 : execution_ctx) (L : env_loc)
          (x : prop_name) (Ed : decl_env_record) (b : bool),
        @eq bool b
          match classicT (decl_env_record_indom Ed a2) return bool with
          | left _ => true
          | right _ => false
          end ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq env_loc L a1 ->
        @eq prop_name x a2 ->
        @eq env_record (env_record_decl Ed) a3 ->
        @eq out (out_ter S (res_val (value_prim (prim_bool b)))) oo ->
        P S C a1 a2 (env_record_decl Ed)
          (out_ter S (res_val (value_prim (prim_bool b))))) ->
       (red_expr S C (spec_env_record_has_binding_1 a1 a2 a3) oo ->
        forall (S0 : state) (C0 : execution_ctx) (L : env_loc)
          (x : prop_name) (l : object_loc) (pt : provide_this_flag) 
          (o : out),
        red_expr S C (spec_object_has_prop l a2) oo ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq env_loc L a1 ->
        @eq prop_name x a2 ->
        @eq env_record (env_record_object l pt) a3 ->
        @eq out o oo -> P S C a1 a2 (env_record_object l pt) oo) ->
       red_expr S C (spec_env_record_has_binding_1 a1 a2 a3) oo ->
       P S C a1 a2 a3 oo.

Parameter inv_red_expr_spec_env_record_get_binding_value
     : forall (S : state) (C : execution_ctx) (a1 : env_loc) 
         (a2 : prop_name) (a3 : bool) (oo : out)
         (P : state -> execution_ctx -> nat -> string -> bool -> out -> Prop),
       (red_expr S C (spec_env_record_get_binding_value a1 a2 a3) oo ->
        forall (S0 : state) (C0 : execution_ctx) (exte : ext_expr) (o : out),
        @eq (option out)
          (out_of_ext_expr (spec_env_record_get_binding_value a1 a2 a3))
          (@Some out oo) ->
        abort oo ->
        not
          (abort_intercepted_expr
             (spec_env_record_get_binding_value a1 a2 a3)) ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq ext_expr exte (spec_env_record_get_binding_value a1 a2 a3) ->
        @eq out o oo -> P S C a1 a2 a3 oo) ->
       (red_expr S C (spec_env_record_get_binding_value a1 a2 a3) oo ->
        forall (E : env_record) (S0 : state) (C0 : execution_ctx)
          (L : env_loc) (x : prop_name) (str : strictness_flag) 
          (o : out),
        env_record_binds S a1 E ->
        red_expr S C (spec_env_record_get_binding_value_1 a1 a2 a3 E) oo ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq env_loc L a1 ->
        @eq prop_name x a2 ->
        @eq bool str a3 -> @eq out o oo -> P S C a1 a2 a3 oo) ->
       red_expr S C (spec_env_record_get_binding_value a1 a2 a3) oo ->
       P S C a1 a2 a3 oo.

Parameter inv_red_expr_spec_env_record_get_binding_value_1
     : forall (S : state) (C : execution_ctx) (a1 : env_loc) 
         (a2 : prop_name) (a3 : bool) (a4 : env_record) 
         (oo : out)
         (P : state ->
              execution_ctx ->
              nat -> string -> bool -> env_record -> out -> Prop),
       (red_expr S C (spec_env_record_get_binding_value_1 a1 a2 a3 a4) oo ->
        forall (S0 : state) (C0 : execution_ctx) (exte : ext_expr) (o : out),
        @eq (option out)
          (out_of_ext_expr (spec_env_record_get_binding_value_1 a1 a2 a3 a4))
          (@Some out oo) ->
        abort oo ->
        not
          (abort_intercepted_expr
             (spec_env_record_get_binding_value_1 a1 a2 a3 a4)) ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq ext_expr exte (spec_env_record_get_binding_value_1 a1 a2 a3 a4) ->
        @eq out o oo -> P S C a1 a2 a3 a4 oo) ->
       (red_expr S C (spec_env_record_get_binding_value_1 a1 a2 a3 a4) oo ->
        forall (mu : mutability) (v : value) (S0 : state)
          (C0 : execution_ctx) (L : env_loc) (x : prop_name)
          (str : strictness_flag) (Ed : decl_env_record) 
          (o : out),
        decl_env_record_binds Ed a2 mu v ->
        @eq mutability mu mutability_uninitialized_immutable ->
        red_expr S C
          (spec_error_or_cst a3 native_error_ref (value_prim prim_undef)) oo ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq env_loc L a1 ->
        @eq prop_name x a2 ->
        @eq bool str a3 ->
        @eq env_record (env_record_decl Ed) a4 ->
        @eq out o oo -> P S C a1 a2 a3 (env_record_decl Ed) oo) ->
       (red_expr S C (spec_env_record_get_binding_value_1 a1 a2 a3 a4) oo ->
        forall (mu : mutability) (v : value) (S0 : state)
          (C0 : execution_ctx) (L : env_loc) (x : prop_name)
          (str : strictness_flag) (Ed : decl_env_record) 
          (o : out),
        decl_env_record_binds Ed a2 mu v ->
        not (@eq mutability mu mutability_uninitialized_immutable) ->
        red_expr S C (spec_returns (out_ter S (res_val v))) oo ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq env_loc L a1 ->
        @eq prop_name x a2 ->
        @eq bool str a3 ->
        @eq env_record (env_record_decl Ed) a4 ->
        @eq out o oo -> P S C a1 a2 a3 (env_record_decl Ed) oo) ->
       (red_expr S C (spec_env_record_get_binding_value_1 a1 a2 a3 a4) oo ->
        forall (o1 : out) (S0 : state) (C0 : execution_ctx) 
          (L : env_loc) (x : prop_name) (str : strictness_flag)
          (l : object_loc) (pt : provide_this_flag) 
          (o : out),
        red_expr S C (spec_object_has_prop l a2) o1 ->
        red_expr S C (spec_env_record_get_binding_value_2 a2 a3 l o1) oo ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq env_loc L a1 ->
        @eq prop_name x a2 ->
        @eq bool str a3 ->
        @eq env_record (env_record_object l pt) a4 ->
        @eq out o oo -> P S C a1 a2 a3 (env_record_object l pt) oo) ->
       red_expr S C (spec_env_record_get_binding_value_1 a1 a2 a3 a4) oo ->
       P S C a1 a2 a3 a4 oo.

Parameter inv_red_expr_spec_env_record_get_binding_value_2
     : forall (S : state) (C : execution_ctx) (a1 : prop_name) 
         (a2 : bool) (a3 : object_loc) (a4 oo : out)
         (P : state ->
              execution_ctx ->
              string -> bool -> object_loc -> out -> out -> Prop),
       (red_expr S C (spec_env_record_get_binding_value_2 a1 a2 a3 a4) oo ->
        forall (S0 : state) (C0 : execution_ctx) (exte : ext_expr) (o : out),
        @eq (option out)
          (out_of_ext_expr (spec_env_record_get_binding_value_2 a1 a2 a3 a4))
          (@Some out oo) ->
        abort oo ->
        not
          (abort_intercepted_expr
             (spec_env_record_get_binding_value_2 a1 a2 a3 a4)) ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq ext_expr exte (spec_env_record_get_binding_value_2 a1 a2 a3 a4) ->
        @eq out o oo -> P S C a1 a2 a3 a4 oo) ->
       (red_expr S C (spec_env_record_get_binding_value_2 a1 a2 a3 a4) oo ->
        forall (S0 : state) (C0 : execution_ctx) (x : prop_name)
          (str : strictness_flag) (l : object_loc) 
          (S1 : state) (o : out),
        red_expr S1 C
          (spec_error_or_cst a2 native_error_ref (value_prim prim_undef)) oo ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq prop_name x a1 ->
        @eq bool str a2 ->
        @eq object_loc l a3 ->
        @eq out (out_ter S1 (res_val (value_prim (prim_bool false)))) a4 ->
        @eq out o oo ->
        P S C a1 a2 a3 (out_ter S1 (res_val (value_prim (prim_bool false))))
          oo) ->
       (red_expr S C (spec_env_record_get_binding_value_2 a1 a2 a3 a4) oo ->
        forall (S0 : state) (C0 : execution_ctx) (x : prop_name)
          (str : strictness_flag) (l : object_loc) 
          (S1 : state) (o : out),
        red_expr S1 C (spec_object_get a3 a1) oo ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq prop_name x a1 ->
        @eq bool str a2 ->
        @eq object_loc l a3 ->
        @eq out (out_ter S1 (res_val (value_prim (prim_bool true)))) a4 ->
        @eq out o oo ->
        P S C a1 a2 a3 (out_ter S1 (res_val (value_prim (prim_bool true))))
          oo) ->
       red_expr S C (spec_env_record_get_binding_value_2 a1 a2 a3 a4) oo ->
       P S C a1 a2 a3 a4 oo.

Parameter inv_red_expr_spec_env_record_create_immutable_binding
     : forall (S : state) (C : execution_ctx) (a1 : env_loc) 
         (a2 : prop_name) (oo : out)
         (P : state -> execution_ctx -> nat -> string -> out -> Prop),
       (red_expr S C (spec_env_record_create_immutable_binding a1 a2) oo ->
        forall (S0 : state) (C0 : execution_ctx) (exte : ext_expr) (o : out),
        @eq (option out)
          (out_of_ext_expr (spec_env_record_create_immutable_binding a1 a2))
          (@Some out oo) ->
        abort oo ->
        not
          (abort_intercepted_expr
             (spec_env_record_create_immutable_binding a1 a2)) ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq ext_expr exte (spec_env_record_create_immutable_binding a1 a2) ->
        @eq out o oo -> P S C a1 a2 oo) ->
       (red_expr S C (spec_env_record_create_immutable_binding a1 a2) oo ->
        forall (Ed : decl_env_record) (S0 : state) 
          (C0 : execution_ctx) (L : env_loc) (x : prop_name) 
          (S' : state),
        env_record_binds S a1 (env_record_decl Ed) ->
        not (decl_env_record_indom Ed a2) ->
        @eq state S'
          (env_record_write_decl_env S a1 a2
             mutability_uninitialized_immutable (value_prim prim_undef)) ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq env_loc L a1 ->
        @eq prop_name x a2 ->
        @eq out (out_void S') oo -> P S C a1 a2 (out_void S')) ->
       red_expr S C (spec_env_record_create_immutable_binding a1 a2) oo ->
       P S C a1 a2 oo.

Parameter inv_red_expr_spec_env_record_initialize_immutable_binding
     : forall (S : state) (C : execution_ctx) (a1 : env_loc) 
         (a2 : prop_name) (a3 : value) (oo : out)
         (P : state -> execution_ctx -> nat -> string -> value -> out -> Prop),
       (red_expr S C (spec_env_record_initialize_immutable_binding a1 a2 a3)
          oo ->
        forall (S0 : state) (C0 : execution_ctx) (exte : ext_expr) (o : out),
        @eq (option out)
          (out_of_ext_expr
             (spec_env_record_initialize_immutable_binding a1 a2 a3))
          (@Some out oo) ->
        abort oo ->
        not
          (abort_intercepted_expr
             (spec_env_record_initialize_immutable_binding a1 a2 a3)) ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq ext_expr exte
          (spec_env_record_initialize_immutable_binding a1 a2 a3) ->
        @eq out o oo -> P S C a1 a2 a3 oo) ->
       (red_expr S C (spec_env_record_initialize_immutable_binding a1 a2 a3)
          oo ->
        forall (Ed : decl_env_record) (v_old : value) 
          (S0 : state) (C0 : execution_ctx) (L : env_loc) 
          (x : prop_name) (v : value) (S' : state),
        env_record_binds S a1 (env_record_decl Ed) ->
        decl_env_record_binds Ed a2 mutability_uninitialized_immutable v_old ->
        @eq state S'
          (env_record_write_decl_env S a1 a2 mutability_immutable a3) ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq env_loc L a1 ->
        @eq prop_name x a2 ->
        @eq value v a3 ->
        @eq out (out_void S') oo -> P S C a1 a2 a3 (out_void S')) ->
       red_expr S C (spec_env_record_initialize_immutable_binding a1 a2 a3)
         oo -> P S C a1 a2 a3 oo.

Parameter inv_red_expr_spec_env_record_create_mutable_binding
     : forall (S : state) (C : execution_ctx) (a1 : env_loc) 
         (a2 : prop_name) (a3 : option bool) (oo : out)
         (P : state ->
              execution_ctx -> nat -> string -> option bool -> out -> Prop),
       (red_expr S C (spec_env_record_create_mutable_binding a1 a2 a3) oo ->
        forall (S0 : state) (C0 : execution_ctx) (exte : ext_expr) (o : out),
        @eq (option out)
          (out_of_ext_expr (spec_env_record_create_mutable_binding a1 a2 a3))
          (@Some out oo) ->
        abort oo ->
        not
          (abort_intercepted_expr
             (spec_env_record_create_mutable_binding a1 a2 a3)) ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq ext_expr exte (spec_env_record_create_mutable_binding a1 a2 a3) ->
        @eq out o oo -> P S C a1 a2 a3 oo) ->
       (red_expr S C (spec_env_record_create_mutable_binding a1 a2 a3) oo ->
        forall (S0 : state) (C0 : execution_ctx) (L : env_loc)
          (x : prop_name) (deletable_opt : option bool) 
          (deletable : bool) (o : out) (E : env_record),
        @eq bool deletable (@unsome_default bool false a3) ->
        env_record_binds S a1 E ->
        red_expr S C
          (spec_env_record_create_mutable_binding_1 a1 a2 deletable E) oo ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq env_loc L a1 ->
        @eq prop_name x a2 ->
        @eq (option bool) deletable_opt a3 ->
        @eq out o oo -> P S C a1 a2 a3 oo) ->
       red_expr S C (spec_env_record_create_mutable_binding a1 a2 a3) oo ->
       P S C a1 a2 a3 oo.

Parameter inv_red_expr_spec_env_record_create_mutable_binding_1
     : forall (S : state) (C : execution_ctx) (a1 : env_loc) 
         (a2 : prop_name) (a3 : bool) (a4 : env_record) 
         (oo : out)
         (P : state ->
              execution_ctx ->
              nat -> string -> bool -> env_record -> out -> Prop),
       (red_expr S C (spec_env_record_create_mutable_binding_1 a1 a2 a3 a4)
          oo ->
        forall (S0 : state) (C0 : execution_ctx) (exte : ext_expr) (o : out),
        @eq (option out)
          (out_of_ext_expr
             (spec_env_record_create_mutable_binding_1 a1 a2 a3 a4))
          (@Some out oo) ->
        abort oo ->
        not
          (abort_intercepted_expr
             (spec_env_record_create_mutable_binding_1 a1 a2 a3 a4)) ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq ext_expr exte
          (spec_env_record_create_mutable_binding_1 a1 a2 a3 a4) ->
        @eq out o oo -> P S C a1 a2 a3 a4 oo) ->
       (red_expr S C (spec_env_record_create_mutable_binding_1 a1 a2 a3 a4)
          oo ->
        forall (S0 : state) (C0 : execution_ctx) (L : env_loc)
          (x : prop_name) (deletable : bool) (Ed : decl_env_record)
          (S' : state),
        not (decl_env_record_indom Ed a2) ->
        @eq state S'
          (env_record_write_decl_env S a1 a2 (mutability_of_bool a3)
             (value_prim prim_undef)) ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq env_loc L a1 ->
        @eq prop_name x a2 ->
        @eq bool deletable a3 ->
        @eq env_record (env_record_decl Ed) a4 ->
        @eq out (out_void S') oo ->
        P S C a1 a2 a3 (env_record_decl Ed) (out_void S')) ->
       (red_expr S C (spec_env_record_create_mutable_binding_1 a1 a2 a3 a4)
          oo ->
        forall (o1 : out) (S0 : state) (C0 : execution_ctx) 
          (L : env_loc) (x : prop_name) (deletable : bool) 
          (l : object_loc) (pt : provide_this_flag) 
          (o : out),
        red_expr S C (spec_object_has_prop l a2) o1 ->
        red_expr S C (spec_env_record_create_mutable_binding_2 a1 a2 a3 l o1)
          oo ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq env_loc L a1 ->
        @eq prop_name x a2 ->
        @eq bool deletable a3 ->
        @eq env_record (env_record_object l pt) a4 ->
        @eq out o oo -> P S C a1 a2 a3 (env_record_object l pt) oo) ->
       red_expr S C (spec_env_record_create_mutable_binding_1 a1 a2 a3 a4) oo ->
       P S C a1 a2 a3 a4 oo.

Parameter inv_red_expr_spec_env_record_create_mutable_binding_2
     : forall (S : state) (C : execution_ctx) (a1 : env_loc) 
         (a2 : prop_name) (a3 : bool) (a4 : object_loc) 
         (a5 oo : out)
         (P : state ->
              execution_ctx ->
              nat -> string -> bool -> object_loc -> out -> out -> Prop),
       (red_expr S C
          (spec_env_record_create_mutable_binding_2 a1 a2 a3 a4 a5) oo ->
        forall (S0 : state) (C0 : execution_ctx) (exte : ext_expr) (o : out),
        @eq (option out)
          (out_of_ext_expr
             (spec_env_record_create_mutable_binding_2 a1 a2 a3 a4 a5))
          (@Some out oo) ->
        abort oo ->
        not
          (abort_intercepted_expr
             (spec_env_record_create_mutable_binding_2 a1 a2 a3 a4 a5)) ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq ext_expr exte
          (spec_env_record_create_mutable_binding_2 a1 a2 a3 a4 a5) ->
        @eq out o oo -> P S C a1 a2 a3 a4 a5 oo) ->
       (red_expr S C
          (spec_env_record_create_mutable_binding_2 a1 a2 a3 a4 a5) oo ->
        forall (A : attributes) (S0 : state) (C0 : execution_ctx)
          (L : env_loc) (x : prop_name) (deletable : bool) 
          (l : object_loc) (S1 : state) (o1 o : out),
        @eq attributes A
          (attributes_data_of
             (attributes_data_intro (value_prim prim_undef) true true a3)) ->
        red_expr S1 C
          (spec_object_define_own_prop a4 a2 (descriptor_of_attributes A)
             throw_true) o1 ->
        red_expr S1 C (spec_env_record_create_mutable_binding_3 o1) oo ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq env_loc L a1 ->
        @eq prop_name x a2 ->
        @eq bool deletable a3 ->
        @eq object_loc l a4 ->
        @eq out (out_ter S1 (res_val (value_prim (prim_bool false)))) a5 ->
        @eq out o oo ->
        P S C a1 a2 a3 a4
          (out_ter S1 (res_val (value_prim (prim_bool false)))) oo) ->
       red_expr S C (spec_env_record_create_mutable_binding_2 a1 a2 a3 a4 a5)
         oo -> P S C a1 a2 a3 a4 a5 oo.

Parameter inv_red_expr_spec_env_record_create_mutable_binding_3
     : forall (S : state) (C : execution_ctx) (a1 oo : out)
         (P : state -> execution_ctx -> out -> out -> Prop),
       (red_expr S C (spec_env_record_create_mutable_binding_3 a1) oo ->
        forall (S0 : state) (C0 : execution_ctx) (exte : ext_expr) (o : out),
        @eq (option out)
          (out_of_ext_expr (spec_env_record_create_mutable_binding_3 a1))
          (@Some out oo) ->
        abort oo ->
        not
          (abort_intercepted_expr
             (spec_env_record_create_mutable_binding_3 a1)) ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq ext_expr exte (spec_env_record_create_mutable_binding_3 a1) ->
        @eq out o oo -> P S C a1 oo) ->
       (red_expr S C (spec_env_record_create_mutable_binding_3 a1) oo ->
        forall (S0 S1 : state) (C0 : execution_ctx) (rv : resvalue),
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq out (out_ter S1 (res_normal rv)) a1 ->
        @eq out (out_void S1) oo ->
        P S C (out_ter S1 (res_normal rv)) (out_void S1)) ->
       red_expr S C (spec_env_record_create_mutable_binding_3 a1) oo ->
       P S C a1 oo.

Parameter inv_red_expr_spec_env_record_set_mutable_binding
     : forall (S : state) (C : execution_ctx) (a1 : env_loc) 
         (a2 : prop_name) (a3 : value) (a4 : bool) 
         (oo : out)
         (P : state ->
              execution_ctx -> nat -> string -> value -> bool -> out -> Prop),
       (red_expr S C (spec_env_record_set_mutable_binding a1 a2 a3 a4) oo ->
        forall (S0 : state) (C0 : execution_ctx) (exte : ext_expr) (o : out),
        @eq (option out)
          (out_of_ext_expr (spec_env_record_set_mutable_binding a1 a2 a3 a4))
          (@Some out oo) ->
        abort oo ->
        not
          (abort_intercepted_expr
             (spec_env_record_set_mutable_binding a1 a2 a3 a4)) ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq ext_expr exte (spec_env_record_set_mutable_binding a1 a2 a3 a4) ->
        @eq out o oo -> P S C a1 a2 a3 a4 oo) ->
       (red_expr S C (spec_env_record_set_mutable_binding a1 a2 a3 a4) oo ->
        forall (S0 : state) (C0 : execution_ctx) (L : env_loc)
          (x : prop_name) (v : value) (str : strictness_flag) 
          (o : out) (E : env_record),
        env_record_binds S a1 E ->
        red_expr S C (spec_env_record_set_mutable_binding_1 a1 a2 a3 a4 E) oo ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq env_loc L a1 ->
        @eq prop_name x a2 ->
        @eq value v a3 ->
        @eq bool str a4 -> @eq out o oo -> P S C a1 a2 a3 a4 oo) ->
       red_expr S C (spec_env_record_set_mutable_binding a1 a2 a3 a4) oo ->
       P S C a1 a2 a3 a4 oo.

Parameter inv_red_expr_spec_env_record_set_mutable_binding_1
     : forall (S : state) (C : execution_ctx) (a1 : env_loc) 
         (a2 : prop_name) (a3 : value) (a4 : bool) 
         (a5 : env_record) (oo : out)
         (P : state ->
              execution_ctx ->
              nat -> string -> value -> bool -> env_record -> out -> Prop),
       (red_expr S C (spec_env_record_set_mutable_binding_1 a1 a2 a3 a4 a5)
          oo ->
        forall (S0 : state) (C0 : execution_ctx) (exte : ext_expr) (o : out),
        @eq (option out)
          (out_of_ext_expr
             (spec_env_record_set_mutable_binding_1 a1 a2 a3 a4 a5))
          (@Some out oo) ->
        abort oo ->
        not
          (abort_intercepted_expr
             (spec_env_record_set_mutable_binding_1 a1 a2 a3 a4 a5)) ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq ext_expr exte
          (spec_env_record_set_mutable_binding_1 a1 a2 a3 a4 a5) ->
        @eq out o oo -> P S C a1 a2 a3 a4 a5 oo) ->
       (red_expr S C (spec_env_record_set_mutable_binding_1 a1 a2 a3 a4 a5)
          oo ->
        forall (v_old : value) (mu : mutability) (S0 : state)
          (C0 : execution_ctx) (L : env_loc) (x : prop_name) 
          (v : value) (str : strictness_flag) (Ed : decl_env_record)
          (o : out),
        decl_env_record_binds Ed a2 mu v_old ->
        mutability_is_mutable mu ->
        red_expr S C
          (spec_returns (out_void (env_record_write_decl_env S a1 a2 mu a3)))
          oo ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq env_loc L a1 ->
        @eq prop_name x a2 ->
        @eq value v a3 ->
        @eq bool str a4 ->
        @eq env_record (env_record_decl Ed) a5 ->
        @eq out o oo -> P S C a1 a2 a3 a4 (env_record_decl Ed) oo) ->
       (red_expr S C (spec_env_record_set_mutable_binding_1 a1 a2 a3 a4 a5)
          oo ->
        forall (v_old : value) (mu : mutability) (S0 : state)
          (C0 : execution_ctx) (L : env_loc) (x : prop_name) 
          (v : value) (str : strictness_flag) (Ed : decl_env_record)
          (o : out),
        decl_env_record_binds Ed a2 mu v_old ->
        not (mutability_is_mutable mu) ->
        red_expr S C (spec_error_or_void a4 native_error_type) oo ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq env_loc L a1 ->
        @eq prop_name x a2 ->
        @eq value v a3 ->
        @eq bool str a4 ->
        @eq env_record (env_record_decl Ed) a5 ->
        @eq out o oo -> P S C a1 a2 a3 a4 (env_record_decl Ed) oo) ->
       (red_expr S C (spec_env_record_set_mutable_binding_1 a1 a2 a3 a4 a5)
          oo ->
        forall (S0 : state) (C0 : execution_ctx) (L : env_loc)
          (x : prop_name) (v : value) (str : strictness_flag)
          (l : object_loc) (pt : provide_this_flag) 
          (o : out),
        red_expr S C (spec_object_put l a2 a3 a4) oo ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq env_loc L a1 ->
        @eq prop_name x a2 ->
        @eq value v a3 ->
        @eq bool str a4 ->
        @eq env_record (env_record_object l pt) a5 ->
        @eq out o oo -> P S C a1 a2 a3 a4 (env_record_object l pt) oo) ->
       red_expr S C (spec_env_record_set_mutable_binding_1 a1 a2 a3 a4 a5) oo ->
       P S C a1 a2 a3 a4 a5 oo.

Parameter inv_red_expr_spec_env_record_delete_binding
     : forall (S : state) (C : execution_ctx) (a1 : env_loc) 
         (a2 : prop_name) (oo : out)
         (P : state -> execution_ctx -> nat -> string -> out -> Prop),
       (red_expr S C (spec_env_record_delete_binding a1 a2) oo ->
        forall (S0 : state) (C0 : execution_ctx) (exte : ext_expr) (o : out),
        @eq (option out)
          (out_of_ext_expr (spec_env_record_delete_binding a1 a2))
          (@Some out oo) ->
        abort oo ->
        not (abort_intercepted_expr (spec_env_record_delete_binding a1 a2)) ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq ext_expr exte (spec_env_record_delete_binding a1 a2) ->
        @eq out o oo -> P S C a1 a2 oo) ->
       (red_expr S C (spec_env_record_delete_binding a1 a2) oo ->
        forall (S0 : state) (C0 : execution_ctx) (L : env_loc)
          (x : prop_name) (o : out) (E : env_record),
        env_record_binds S a1 E ->
        red_expr S C (spec_env_record_delete_binding_1 a1 a2 E) oo ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq env_loc L a1 ->
        @eq prop_name x a2 -> @eq out o oo -> P S C a1 a2 oo) ->
       red_expr S C (spec_env_record_delete_binding a1 a2) oo ->
       P S C a1 a2 oo.

Parameter inv_red_expr_spec_env_record_delete_binding_1
     : forall (S : state) (C : execution_ctx) (a1 : env_loc) 
         (a2 : prop_name) (a3 : env_record) (oo : out)
         (P : state ->
              execution_ctx -> nat -> string -> env_record -> out -> Prop),
       (red_expr S C (spec_env_record_delete_binding_1 a1 a2 a3) oo ->
        forall (S0 : state) (C0 : execution_ctx) (exte : ext_expr) (o : out),
        @eq (option out)
          (out_of_ext_expr (spec_env_record_delete_binding_1 a1 a2 a3))
          (@Some out oo) ->
        abort oo ->
        not
          (abort_intercepted_expr (spec_env_record_delete_binding_1 a1 a2 a3)) ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq ext_expr exte (spec_env_record_delete_binding_1 a1 a2 a3) ->
        @eq out o oo -> P S C a1 a2 a3 oo) ->
       (red_expr S C (spec_env_record_delete_binding_1 a1 a2 a3) oo ->
        forall (mu : mutability) (v : value) (S0 : state)
          (C0 : execution_ctx) (L : env_loc) (x : prop_name)
          (Ed : decl_env_record) (S' : state) (b : bool),
        decl_env_record_binds Ed a2 mu v ->
        match
          classicT (@eq mutability mu mutability_deletable) return Prop
        with
        | left _ =>
            Logic.and
              (@eq state S'
                 (env_record_write S a1
                    (env_record_decl (decl_env_record_rem Ed a2))))
              (@eq bool b true)
        | right _ => Logic.and (@eq state S' S) (@eq bool b false)
        end ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq env_loc L a1 ->
        @eq prop_name x a2 ->
        @eq env_record (env_record_decl Ed) a3 ->
        @eq out (out_ter S' (res_val (value_prim (prim_bool b)))) oo ->
        P S C a1 a2 (env_record_decl Ed)
          (out_ter S' (res_val (value_prim (prim_bool b))))) ->
       (red_expr S C (spec_env_record_delete_binding_1 a1 a2 a3) oo ->
        forall (S0 : state) (C0 : execution_ctx) (L : env_loc)
          (x : prop_name) (Ed : decl_env_record),
        not (decl_env_record_indom Ed a2) ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq env_loc L a1 ->
        @eq prop_name x a2 ->
        @eq env_record (env_record_decl Ed) a3 ->
        @eq out (out_ter S (res_val (value_prim (prim_bool true)))) oo ->
        P S C a1 a2 (env_record_decl Ed)
          (out_ter S (res_val (value_prim (prim_bool true))))) ->
       (red_expr S C (spec_env_record_delete_binding_1 a1 a2 a3) oo ->
        forall (S0 : state) (C0 : execution_ctx) (L : env_loc)
          (x : prop_name) (l : object_loc) (pt : provide_this_flag) 
          (o : out),
        red_expr S C (spec_object_delete l a2 throw_false) oo ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq env_loc L a1 ->
        @eq prop_name x a2 ->
        @eq env_record (env_record_object l pt) a3 ->
        @eq out o oo -> P S C a1 a2 (env_record_object l pt) oo) ->
       red_expr S C (spec_env_record_delete_binding_1 a1 a2 a3) oo ->
       P S C a1 a2 a3 oo.

Parameter inv_red_expr_spec_env_record_create_set_mutable_binding
     : forall (S : state) (C : execution_ctx) (a1 : env_loc) 
         (a2 : prop_name) (a3 : option bool) (a4 : value) 
         (a5 : bool) (oo : out)
         (P : state ->
              execution_ctx ->
              nat -> string -> option bool -> value -> bool -> out -> Prop),
       (red_expr S C
          (spec_env_record_create_set_mutable_binding a1 a2 a3 a4 a5) oo ->
        forall (S0 : state) (C0 : execution_ctx) (exte : ext_expr) (o : out),
        @eq (option out)
          (out_of_ext_expr
             (spec_env_record_create_set_mutable_binding a1 a2 a3 a4 a5))
          (@Some out oo) ->
        abort oo ->
        not
          (abort_intercepted_expr
             (spec_env_record_create_set_mutable_binding a1 a2 a3 a4 a5)) ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq ext_expr exte
          (spec_env_record_create_set_mutable_binding a1 a2 a3 a4 a5) ->
        @eq out o oo -> P S C a1 a2 a3 a4 a5 oo) ->
       (red_expr S C
          (spec_env_record_create_set_mutable_binding a1 a2 a3 a4 a5) oo ->
        forall (S0 : state) (C0 : execution_ctx) (L : env_loc)
          (x : prop_name) (deletable_opt : option bool) 
          (v : value) (str : strictness_flag) (o o1 : out),
        red_expr S C (spec_env_record_create_mutable_binding a1 a2 a3) o1 ->
        red_expr S C
          (spec_env_record_create_set_mutable_binding_1 o1 a1 a2 a4 a5) oo ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq env_loc L a1 ->
        @eq prop_name x a2 ->
        @eq (option bool) deletable_opt a3 ->
        @eq value v a4 ->
        @eq bool str a5 -> @eq out o oo -> P S C a1 a2 a3 a4 a5 oo) ->
       red_expr S C
         (spec_env_record_create_set_mutable_binding a1 a2 a3 a4 a5) oo ->
       P S C a1 a2 a3 a4 a5 oo.

Parameter inv_red_expr_spec_env_record_create_set_mutable_binding_1
     : forall (S : state) (C : execution_ctx) (a1 : out) 
         (a2 : env_loc) (a3 : prop_name) (a4 : value) 
         (a5 : bool) (oo : out)
         (P : state ->
              execution_ctx ->
              out -> nat -> string -> value -> bool -> out -> Prop),
       (red_expr S C
          (spec_env_record_create_set_mutable_binding_1 a1 a2 a3 a4 a5) oo ->
        forall (S0 : state) (C0 : execution_ctx) (exte : ext_expr) (o : out),
        @eq (option out)
          (out_of_ext_expr
             (spec_env_record_create_set_mutable_binding_1 a1 a2 a3 a4 a5))
          (@Some out oo) ->
        abort oo ->
        not
          (abort_intercepted_expr
             (spec_env_record_create_set_mutable_binding_1 a1 a2 a3 a4 a5)) ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq ext_expr exte
          (spec_env_record_create_set_mutable_binding_1 a1 a2 a3 a4 a5) ->
        @eq out o oo -> P S C a1 a2 a3 a4 a5 oo) ->
       (red_expr S C
          (spec_env_record_create_set_mutable_binding_1 a1 a2 a3 a4 a5) oo ->
        forall (S0 S1 : state) (C0 : execution_ctx) 
          (L : env_loc) (x : prop_name) (v : value) 
          (str : strictness_flag) (o : out),
        red_expr S0 C (spec_env_record_set_mutable_binding a2 a3 a4 a5) oo ->
        @eq state S1 S ->
        @eq execution_ctx C0 C ->
        @eq out (out_void S0) a1 ->
        @eq env_loc L a2 ->
        @eq prop_name x a3 ->
        @eq value v a4 ->
        @eq bool str a5 -> @eq out o oo -> P S C (out_void S0) a2 a3 a4 a5 oo) ->
       red_expr S C
         (spec_env_record_create_set_mutable_binding_1 a1 a2 a3 a4 a5) oo ->
       P S C a1 a2 a3 a4 a5 oo.

Parameter inv_red_expr_spec_env_record_implicit_this_value
     : forall (S : state) (C : execution_ctx) (a1 : env_loc) 
         (oo : out) (P : state -> execution_ctx -> nat -> out -> Prop),
       (red_expr S C (spec_env_record_implicit_this_value a1) oo ->
        forall (S0 : state) (C0 : execution_ctx) (exte : ext_expr) (o : out),
        @eq (option out)
          (out_of_ext_expr (spec_env_record_implicit_this_value a1))
          (@Some out oo) ->
        abort oo ->
        not (abort_intercepted_expr (spec_env_record_implicit_this_value a1)) ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq ext_expr exte (spec_env_record_implicit_this_value a1) ->
        @eq out o oo -> P S C a1 oo) ->
       (red_expr S C (spec_env_record_implicit_this_value a1) oo ->
        forall (S0 : state) (C0 : execution_ctx) (L : env_loc) 
          (o : out) (E : env_record),
        env_record_binds S a1 E ->
        red_expr S C (spec_env_record_implicit_this_value_1 a1 E) oo ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq env_loc L a1 -> @eq out o oo -> P S C a1 oo) ->
       red_expr S C (spec_env_record_implicit_this_value a1) oo ->
       P S C a1 oo.

Parameter inv_red_expr_spec_env_record_implicit_this_value_1
     : forall (S : state) (C : execution_ctx) (a1 : env_loc)
         (a2 : env_record) (oo : out)
         (P : state -> execution_ctx -> nat -> env_record -> out -> Prop),
       (red_expr S C (spec_env_record_implicit_this_value_1 a1 a2) oo ->
        forall (S0 : state) (C0 : execution_ctx) (exte : ext_expr) (o : out),
        @eq (option out)
          (out_of_ext_expr (spec_env_record_implicit_this_value_1 a1 a2))
          (@Some out oo) ->
        abort oo ->
        not
          (abort_intercepted_expr
             (spec_env_record_implicit_this_value_1 a1 a2)) ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq ext_expr exte (spec_env_record_implicit_this_value_1 a1 a2) ->
        @eq out o oo -> P S C a1 a2 oo) ->
       (red_expr S C (spec_env_record_implicit_this_value_1 a1 a2) oo ->
        forall (S0 : state) (C0 : execution_ctx) (L : env_loc)
          (Ed : decl_env_record),
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq env_loc L a1 ->
        @eq env_record (env_record_decl Ed) a2 ->
        @eq out (out_ter S (res_val (value_prim prim_undef))) oo ->
        P S C a1 (env_record_decl Ed)
          (out_ter S (res_val (value_prim prim_undef)))) ->
       (red_expr S C (spec_env_record_implicit_this_value_1 a1 a2) oo ->
        forall (S0 : state) (C0 : execution_ctx) (L : env_loc)
          (l : object_loc) (pt : bool) (v : value),
        @eq value v
          match pt return value with
          | true => value_object l
          | false => value_prim prim_undef
          end ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq env_loc L a1 ->
        @eq env_record (env_record_object l pt) a2 ->
        @eq out (out_ter S (res_val v)) oo ->
        P S C a1 (env_record_object l pt) (out_ter S (res_val v))) ->
       red_expr S C (spec_env_record_implicit_this_value_1 a1 a2) oo ->
       P S C a1 a2 oo.

Parameter inv_red_expr_spec_from_descriptor
     : forall (S : state) (C : execution_ctx) (a1 : specret full_descriptor)
         (oo : out)
         (P : state ->
              execution_ctx -> specret full_descriptor -> out -> Prop),
       (red_expr S C (spec_from_descriptor a1) oo ->
        forall (S0 : state) (C0 : execution_ctx) (exte : ext_expr) (o : out),
        @eq (option out) (out_of_ext_expr (spec_from_descriptor a1))
          (@Some out oo) ->
        abort oo ->
        not (abort_intercepted_expr (spec_from_descriptor a1)) ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq ext_expr exte (spec_from_descriptor a1) ->
        @eq out o oo -> P S C a1 oo) ->
       (red_expr S C (spec_from_descriptor a1) oo ->
        forall (S0 S1 : state) (C0 : execution_ctx),
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq (specret full_descriptor)
          (@ret full_descriptor S1 full_descriptor_undef) a1 ->
        @eq out (out_ter S1 (res_val (value_prim prim_undef))) oo ->
        P S C (@ret full_descriptor S1 full_descriptor_undef)
          (out_ter S1 (res_val (value_prim prim_undef)))) ->
       (red_expr S C (spec_from_descriptor a1) oo ->
        forall (S0 S1 : state) (C0 : execution_ctx) 
          (A : attributes) (o o1 : out),
        red_expr S1 C (spec_construct_prealloc prealloc_object (@nil value))
          o1 ->
        red_expr S1 C (spec_from_descriptor_1 A o1) oo ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq (specret full_descriptor)
          (@ret full_descriptor S1 (full_descriptor_some A)) a1 ->
        @eq out o oo ->
        P S C (@ret full_descriptor S1 (full_descriptor_some A)) oo) ->
       red_expr S C (spec_from_descriptor a1) oo -> P S C a1 oo.

Parameter inv_red_expr_spec_from_descriptor_1
     : forall (S : state) (C : execution_ctx) (a1 : attributes) 
         (a2 oo : out)
         (P : state -> execution_ctx -> attributes -> out -> out -> Prop),
       (red_expr S C (spec_from_descriptor_1 a1 a2) oo ->
        forall (S0 : state) (C0 : execution_ctx) (exte : ext_expr) (o : out),
        @eq (option out) (out_of_ext_expr (spec_from_descriptor_1 a1 a2))
          (@Some out oo) ->
        abort oo ->
        not (abort_intercepted_expr (spec_from_descriptor_1 a1 a2)) ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq ext_expr exte (spec_from_descriptor_1 a1 a2) ->
        @eq out o oo -> P S C a1 a2 oo) ->
       (red_expr S C (spec_from_descriptor_1 a1 a2) oo ->
        forall (S0 S1 : state) (C0 : execution_ctx) 
          (Ad : attributes_data) (A' : attributes) 
          (l : object_loc) (o o1 : out),
        @eq attributes A'
          (attributes_data_of
             (attributes_data_intro_all_true (attributes_data_value Ad))) ->
        red_expr S1 C
          (spec_object_define_own_prop l
             (String (Ascii false true true false true true true false)
                (String (Ascii true false false false false true true false)
                   (String
                      (Ascii false false true true false true true false)
                      (String
                         (Ascii true false true false true true true false)
                         (String
                            (Ascii true false true false false true true
                               false) EmptyString)))))
             (descriptor_of_attributes A') throw_false) o1 ->
        red_expr S1 C (spec_from_descriptor_2 l Ad o1) oo ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq attributes (attributes_data_of Ad) a1 ->
        @eq out (out_ter S1 (res_val (value_object l))) a2 ->
        @eq out o oo ->
        P S C (attributes_data_of Ad) (out_ter S1 (res_val (value_object l)))
          oo) ->
       (red_expr S C (spec_from_descriptor_1 a1 a2) oo ->
        forall (S0 S1 : state) (C0 : execution_ctx)
          (Aa : attributes_accessor) (A' : attributes) 
          (l : object_loc) (o o1 : out),
        @eq attributes A'
          (attributes_data_of
             (attributes_data_intro_all_true (attributes_accessor_get Aa))) ->
        red_expr S1 C
          (spec_object_define_own_prop l
             (String (Ascii true true true false false true true false)
                (String (Ascii true false true false false true true false)
                   (String
                      (Ascii false false true false true true true false)
                      EmptyString))) (descriptor_of_attributes A')
             throw_false) o1 ->
        red_expr S1 C (spec_from_descriptor_3 l Aa o1) oo ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq attributes (attributes_accessor_of Aa) a1 ->
        @eq out (out_ter S1 (res_val (value_object l))) a2 ->
        @eq out o oo ->
        P S C (attributes_accessor_of Aa)
          (out_ter S1 (res_val (value_object l))) oo) ->
       red_expr S C (spec_from_descriptor_1 a1 a2) oo -> P S C a1 a2 oo.

Parameter inv_red_expr_spec_from_descriptor_2
     : forall (S : state) (C : execution_ctx) (a1 : object_loc)
         (a2 : attributes_data) (a3 oo : out)
         (P : state ->
              execution_ctx ->
              object_loc -> attributes_data -> out -> out -> Prop),
       (red_expr S C (spec_from_descriptor_2 a1 a2 a3) oo ->
        forall (S0 : state) (C0 : execution_ctx) (exte : ext_expr) (o : out),
        @eq (option out) (out_of_ext_expr (spec_from_descriptor_2 a1 a2 a3))
          (@Some out oo) ->
        abort oo ->
        not (abort_intercepted_expr (spec_from_descriptor_2 a1 a2 a3)) ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq ext_expr exte (spec_from_descriptor_2 a1 a2 a3) ->
        @eq out o oo -> P S C a1 a2 a3 oo) ->
       (red_expr S C (spec_from_descriptor_2 a1 a2 a3) oo ->
        forall (S0 S1 : state) (C0 : execution_ctx) 
          (Ad : attributes_data) (A' : attributes) 
          (l : object_loc) (b : bool) (o o1 : out),
        @eq attributes A'
          (attributes_data_of
             (attributes_data_intro_all_true
                (value_prim (prim_bool (attributes_data_writable a2))))) ->
        red_expr S1 C
          (spec_object_define_own_prop a1
             (String (Ascii true true true false true true true false)
                (String (Ascii false true false false true true true false)
                   (String
                      (Ascii true false false true false true true false)
                      (String
                         (Ascii false false true false true true true false)
                         (String
                            (Ascii true false false false false true true
                               false)
                            (String
                               (Ascii false true false false false true true
                                  false)
                               (String
                                  (Ascii false false true true false true
                                     true false)
                                  (String
                                     (Ascii true false true false false true
                                        true false) EmptyString))))))))
             (descriptor_of_attributes A') throw_false) o1 ->
        red_expr S1 C (spec_from_descriptor_4 a1 (attributes_data_of a2) o1)
          oo ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq object_loc l a1 ->
        @eq attributes_data Ad a2 ->
        @eq out (out_ter S1 (res_val (value_prim (prim_bool b)))) a3 ->
        @eq out o oo ->
        P S C a1 a2 (out_ter S1 (res_val (value_prim (prim_bool b)))) oo) ->
       red_expr S C (spec_from_descriptor_2 a1 a2 a3) oo -> P S C a1 a2 a3 oo.

Parameter inv_red_expr_spec_from_descriptor_3
     : forall (S : state) (C : execution_ctx) (a1 : object_loc)
         (a2 : attributes_accessor) (a3 oo : out)
         (P : state ->
              execution_ctx ->
              object_loc -> attributes_accessor -> out -> out -> Prop),
       (red_expr S C (spec_from_descriptor_3 a1 a2 a3) oo ->
        forall (S0 : state) (C0 : execution_ctx) (exte : ext_expr) (o : out),
        @eq (option out) (out_of_ext_expr (spec_from_descriptor_3 a1 a2 a3))
          (@Some out oo) ->
        abort oo ->
        not (abort_intercepted_expr (spec_from_descriptor_3 a1 a2 a3)) ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq ext_expr exte (spec_from_descriptor_3 a1 a2 a3) ->
        @eq out o oo -> P S C a1 a2 a3 oo) ->
       (red_expr S C (spec_from_descriptor_3 a1 a2 a3) oo ->
        forall (S0 S1 : state) (C0 : execution_ctx)
          (Aa : attributes_accessor) (A' : attributes) 
          (l : object_loc) (b : bool) (o o1 : out),
        @eq attributes A'
          (attributes_data_of
             (attributes_data_intro_all_true (attributes_accessor_set a2))) ->
        red_expr S1 C
          (spec_object_define_own_prop a1
             (String (Ascii true true false false true true true false)
                (String (Ascii true false true false false true true false)
                   (String
                      (Ascii false false true false true true true false)
                      EmptyString))) (descriptor_of_attributes A')
             throw_false) o1 ->
        red_expr S1 C
          (spec_from_descriptor_4 a1 (attributes_accessor_of a2) o1) oo ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq object_loc l a1 ->
        @eq attributes_accessor Aa a2 ->
        @eq out (out_ter S1 (res_val (value_prim (prim_bool b)))) a3 ->
        @eq out o oo ->
        P S C a1 a2 (out_ter S1 (res_val (value_prim (prim_bool b)))) oo) ->
       red_expr S C (spec_from_descriptor_3 a1 a2 a3) oo -> P S C a1 a2 a3 oo.

Parameter inv_red_expr_spec_from_descriptor_4
     : forall (S : state) (C : execution_ctx) (a1 : object_loc)
         (a2 : attributes) (a3 oo : out)
         (P : state ->
              execution_ctx -> object_loc -> attributes -> out -> out -> Prop),
       (red_expr S C (spec_from_descriptor_4 a1 a2 a3) oo ->
        forall (S0 : state) (C0 : execution_ctx) (exte : ext_expr) (o : out),
        @eq (option out) (out_of_ext_expr (spec_from_descriptor_4 a1 a2 a3))
          (@Some out oo) ->
        abort oo ->
        not (abort_intercepted_expr (spec_from_descriptor_4 a1 a2 a3)) ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq ext_expr exte (spec_from_descriptor_4 a1 a2 a3) ->
        @eq out o oo -> P S C a1 a2 a3 oo) ->
       (red_expr S C (spec_from_descriptor_4 a1 a2 a3) oo ->
        forall (S0 S1 : state) (C0 : execution_ctx) 
          (A A' : attributes) (l : object_loc) (b : bool) 
          (o o1 : out),
        @eq attributes A'
          (attributes_data_of
             (attributes_data_intro_all_true
                (value_prim (prim_bool (attributes_enumerable a2))))) ->
        red_expr S1 C
          (spec_object_define_own_prop a1
             (String (Ascii true false true false false true true false)
                (String (Ascii false true true true false true true false)
                   (String (Ascii true false true false true true true false)
                      (String
                         (Ascii true false true true false true true false)
                         (String
                            (Ascii true false true false false true true
                               false)
                            (String
                               (Ascii false true false false true true true
                                  false)
                               (String
                                  (Ascii true false false false false true
                                     true false)
                                  (String
                                     (Ascii false true false false false true
                                        true false)
                                     (String
                                        (Ascii false false true true false
                                           true true false)
                                        (String
                                           (Ascii true false true false false
                                              true true false) EmptyString))))))))))
             (descriptor_of_attributes A') throw_false) o1 ->
        red_expr S1 C (spec_from_descriptor_5 a1 a2 o1) oo ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq object_loc l a1 ->
        @eq attributes A a2 ->
        @eq out (out_ter S1 (res_val (value_prim (prim_bool b)))) a3 ->
        @eq out o oo ->
        P S C a1 a2 (out_ter S1 (res_val (value_prim (prim_bool b)))) oo) ->
       red_expr S C (spec_from_descriptor_4 a1 a2 a3) oo -> P S C a1 a2 a3 oo.

Parameter inv_red_expr_spec_from_descriptor_5
     : forall (S : state) (C : execution_ctx) (a1 : object_loc)
         (a2 : attributes) (a3 oo : out)
         (P : state ->
              execution_ctx -> object_loc -> attributes -> out -> out -> Prop),
       (red_expr S C (spec_from_descriptor_5 a1 a2 a3) oo ->
        forall (S0 : state) (C0 : execution_ctx) (exte : ext_expr) (o : out),
        @eq (option out) (out_of_ext_expr (spec_from_descriptor_5 a1 a2 a3))
          (@Some out oo) ->
        abort oo ->
        not (abort_intercepted_expr (spec_from_descriptor_5 a1 a2 a3)) ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq ext_expr exte (spec_from_descriptor_5 a1 a2 a3) ->
        @eq out o oo -> P S C a1 a2 a3 oo) ->
       (red_expr S C (spec_from_descriptor_5 a1 a2 a3) oo ->
        forall (S0 S1 : state) (C0 : execution_ctx) 
          (A A' : attributes) (l : object_loc) (b : bool) 
          (o o1 : out),
        @eq attributes A'
          (attributes_data_of
             (attributes_data_intro_all_true
                (value_prim (prim_bool (attributes_configurable a2))))) ->
        red_expr S1 C
          (spec_object_define_own_prop a1
             (String (Ascii true true false false false true true false)
                (String (Ascii true true true true false true true false)
                   (String (Ascii false true true true false true true false)
                      (String
                         (Ascii false true true false false true true false)
                         (String
                            (Ascii true false false true false true true
                               false)
                            (String
                               (Ascii true true true false false true true
                                  false)
                               (String
                                  (Ascii true false true false true true true
                                     false)
                                  (String
                                     (Ascii false true false false true true
                                        true false)
                                     (String
                                        (Ascii true false false false false
                                           true true false)
                                        (String
                                           (Ascii false true false false
                                              false true true false)
                                           (String
                                              (Ascii false false true true
                                                 false true true false)
                                              (String
                                                 (Ascii true false true false
                                                  false true true false)
                                                 EmptyString))))))))))))
             (descriptor_of_attributes A') throw_false) o1 ->
        red_expr S1 C (spec_from_descriptor_6 a1 o1) oo ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq object_loc l a1 ->
        @eq attributes A a2 ->
        @eq out (out_ter S1 (res_val (value_prim (prim_bool b)))) a3 ->
        @eq out o oo ->
        P S C a1 a2 (out_ter S1 (res_val (value_prim (prim_bool b)))) oo) ->
       red_expr S C (spec_from_descriptor_5 a1 a2 a3) oo -> P S C a1 a2 a3 oo.

Parameter inv_red_expr_spec_from_descriptor_6
     : forall (S : state) (C : execution_ctx) (a1 : object_loc) 
         (a2 oo : out)
         (P : state -> execution_ctx -> object_loc -> out -> out -> Prop),
       (red_expr S C (spec_from_descriptor_6 a1 a2) oo ->
        forall (S0 : state) (C0 : execution_ctx) (exte : ext_expr) (o : out),
        @eq (option out) (out_of_ext_expr (spec_from_descriptor_6 a1 a2))
          (@Some out oo) ->
        abort oo ->
        not (abort_intercepted_expr (spec_from_descriptor_6 a1 a2)) ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq ext_expr exte (spec_from_descriptor_6 a1 a2) ->
        @eq out o oo -> P S C a1 a2 oo) ->
       (red_expr S C (spec_from_descriptor_6 a1 a2) oo ->
        forall (S0 S1 : state) (C0 : execution_ctx) 
          (l : object_loc) (b : bool),
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq object_loc l a1 ->
        @eq out (out_ter S1 (res_val (value_prim (prim_bool b)))) a2 ->
        @eq out (out_ter S1 (res_val (value_object a1))) oo ->
        P S C a1 (out_ter S1 (res_val (value_prim (prim_bool b))))
          (out_ter S1 (res_val (value_object a1)))) ->
       red_expr S C (spec_from_descriptor_6 a1 a2) oo -> P S C a1 a2 oo.

Parameter inv_red_expr_spec_entering_eval_code
     : forall (S : state) (C : execution_ctx) (a1 : bool) 
         (a2 : funcbody) (a3 : ext_expr) (oo : out)
         (P : state ->
              execution_ctx -> bool -> funcbody -> ext_expr -> out -> Prop),
       (red_expr S C (spec_entering_eval_code a1 a2 a3) oo ->
        forall (S0 : state) (C0 : execution_ctx) (exte : ext_expr) (o : out),
        @eq (option out) (out_of_ext_expr (spec_entering_eval_code a1 a2 a3))
          (@Some out oo) ->
        abort oo ->
        not (abort_intercepted_expr (spec_entering_eval_code a1 a2 a3)) ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq ext_expr exte (spec_entering_eval_code a1 a2 a3) ->
        @eq out o oo -> P S C a1 a2 a3 oo) ->
       (red_expr S C (spec_entering_eval_code a1 a2 a3) oo ->
        forall (str : bool) (C' : execution_ctx) (S0 : state)
          (C0 : execution_ctx) (bdirect : bool) (bd : funcbody)
          (K : ext_expr) (o : out),
        @eq bool str
          (or (funcbody_is_strict a2) (andb a1 (execution_ctx_strict C))) ->
        @eq execution_ctx C'
          match classicT (istrue a1) return execution_ctx with
          | left _ => C
          | right _ => execution_ctx_initial str
          end ->
        red_expr S C' (spec_entering_eval_code_1 a2 a3 str) oo ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq bool bdirect a1 ->
        @eq funcbody bd a2 ->
        @eq ext_expr K a3 -> @eq out o oo -> P S C a1 a2 a3 oo) ->
       red_expr S C (spec_entering_eval_code a1 a2 a3) oo ->
       P S C a1 a2 a3 oo.

Parameter inv_red_expr_spec_entering_eval_code_1
     : forall (S : state) (C : execution_ctx) (a1 : funcbody) 
         (a2 : ext_expr) (a3 : bool) (oo : out)
         (P : state ->
              execution_ctx -> funcbody -> ext_expr -> bool -> out -> Prop),
       (red_expr S C (spec_entering_eval_code_1 a1 a2 a3) oo ->
        forall (S0 : state) (C0 : execution_ctx) (exte : ext_expr) (o : out),
        @eq (option out)
          (out_of_ext_expr (spec_entering_eval_code_1 a1 a2 a3))
          (@Some out oo) ->
        abort oo ->
        not (abort_intercepted_expr (spec_entering_eval_code_1 a1 a2 a3)) ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq ext_expr exte (spec_entering_eval_code_1 a1 a2 a3) ->
        @eq out o oo -> P S C a1 a2 a3 oo) ->
       (red_expr S C (spec_entering_eval_code_1 a1 a2 a3) oo ->
        forall (str : bool) (lex : list nat) (S' : state)
          (C' : execution_ctx) (o1 : out) (S0 : state) 
          (C0 : execution_ctx) (bd : funcbody) (K : ext_expr) 
          (o : out),
        @eq (prod (list nat) state) (@pair (list nat) state lex S')
          match classicT (istrue a3) return (prod (list nat) state) with
          | left _ => lexical_env_alloc_decl S (execution_ctx_lexical_env C)
          | right _ =>
              @pair lexical_env state (execution_ctx_lexical_env C) S
          end ->
        @eq execution_ctx C'
          match classicT (istrue a3) return execution_ctx with
          | left _ => execution_ctx_with_lex_same C lex
          | right _ => C
          end ->
        red_expr S' C'
          (spec_binding_inst codetype_eval (@None object_loc)
             (funcbody_prog a1) (@nil value)) o1 ->
        red_expr S' C' (spec_entering_eval_code_2 o1 a2) oo ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq funcbody bd a1 ->
        @eq ext_expr K a2 ->
        @eq bool str a3 -> @eq out o oo -> P S C a1 a2 a3 oo) ->
       red_expr S C (spec_entering_eval_code_1 a1 a2 a3) oo ->
       P S C a1 a2 a3 oo.

Parameter inv_red_expr_spec_entering_eval_code_2
     : forall (S : state) (C : execution_ctx) (a1 : out) 
         (a2 : ext_expr) (oo : out)
         (P : state -> execution_ctx -> out -> ext_expr -> out -> Prop),
       (red_expr S C (spec_entering_eval_code_2 a1 a2) oo ->
        forall (S0 : state) (C0 : execution_ctx) (exte : ext_expr) (o : out),
        @eq (option out) (out_of_ext_expr (spec_entering_eval_code_2 a1 a2))
          (@Some out oo) ->
        abort oo ->
        not (abort_intercepted_expr (spec_entering_eval_code_2 a1 a2)) ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq ext_expr exte (spec_entering_eval_code_2 a1 a2) ->
        @eq out o oo -> P S C a1 a2 oo) ->
       (red_expr S C (spec_entering_eval_code_2 a1 a2) oo ->
        forall (S0 : state) (C0 : execution_ctx) (S1 : state) 
          (K : ext_expr) (o : out),
        red_expr S1 C a2 oo ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq out (out_void S1) a1 ->
        @eq ext_expr K a2 -> @eq out o oo -> P S C (out_void S1) a2 oo) ->
       red_expr S C (spec_entering_eval_code_2 a1 a2) oo -> P S C a1 a2 oo.

Parameter inv_red_expr_spec_call_global_eval
     : forall (S : state) (C : execution_ctx) (a1 : bool) 
         (a2 : list value) (oo : out)
         (P : state -> execution_ctx -> bool -> list value -> out -> Prop),
       (red_expr S C (spec_call_global_eval a1 a2) oo ->
        forall (S0 : state) (C0 : execution_ctx) (exte : ext_expr) (o : out),
        @eq (option out) (out_of_ext_expr (spec_call_global_eval a1 a2))
          (@Some out oo) ->
        abort oo ->
        not (abort_intercepted_expr (spec_call_global_eval a1 a2)) ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq ext_expr exte (spec_call_global_eval a1 a2) ->
        @eq out o oo -> P S C a1 a2 oo) ->
       (red_expr S C (spec_call_global_eval a1 a2) oo ->
        forall (S0 : state) (C0 : execution_ctx) (bdirect : bool)
          (args : list value) (v : value) (o : out),
        arguments_from a2 (@cons value v (@nil value)) ->
        red_expr S C (spec_call_global_eval_1 a1 v) oo ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq bool bdirect a1 ->
        @eq (list value) args a2 -> @eq out o oo -> P S C a1 a2 oo) ->
       red_expr S C (spec_call_global_eval a1 a2) oo -> P S C a1 a2 oo.

Parameter inv_red_expr_spec_call_global_eval_1
     : forall (S : state) (C : execution_ctx) (a1 : bool) 
         (a2 : value) (oo : out)
         (P : state -> execution_ctx -> bool -> value -> out -> Prop),
       (red_expr S C (spec_call_global_eval_1 a1 a2) oo ->
        forall (S0 : state) (C0 : execution_ctx) (exte : ext_expr) (o : out),
        @eq (option out) (out_of_ext_expr (spec_call_global_eval_1 a1 a2))
          (@Some out oo) ->
        abort oo ->
        not (abort_intercepted_expr (spec_call_global_eval_1 a1 a2)) ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq ext_expr exte (spec_call_global_eval_1 a1 a2) ->
        @eq out o oo -> P S C a1 a2 oo) ->
       (red_expr S C (spec_call_global_eval_1 a1 a2) oo ->
        forall (S0 : state) (C0 : execution_ctx) (bdirect : bool) (v : value),
        not (@eq type (type_of a2) type_string) ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq bool bdirect a1 ->
        @eq value v a2 ->
        @eq out (out_ter S (res_val a2)) oo ->
        P S C a1 a2 (out_ter S (res_val a2))) ->
       (red_expr S C (spec_call_global_eval_1 a1 a2) oo ->
        forall (s : string) (b : bool) (S0 : state) 
          (C0 : execution_ctx) (bdirect : bool) (o : out),
        (forall p : prog, not (parse s b p)) ->
        red_expr S C (spec_error native_error_syntax) oo ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq bool bdirect a1 ->
        @eq value (value_prim (prim_string s)) a2 ->
        @eq out o oo -> P S C a1 (value_prim (prim_string s)) oo) ->
       (red_expr S C (spec_call_global_eval_1 a1 a2) oo ->
        forall (s : string) (b : bool) (p : prog) (S0 : state)
          (C0 : execution_ctx) (bdirect : bool) (o : out),
        parse s b p ->
        red_expr S C
          (spec_entering_eval_code a1 (funcbody_intro p s)
             (spec_call_global_eval_2 p)) oo ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq bool bdirect a1 ->
        @eq value (value_prim (prim_string s)) a2 ->
        @eq out o oo -> P S C a1 (value_prim (prim_string s)) oo) ->
       red_expr S C (spec_call_global_eval_1 a1 a2) oo -> P S C a1 a2 oo.

Parameter inv_red_expr_spec_call_global_eval_2
     : forall (S : state) (C : execution_ctx) (a1 : prog) 
         (oo : out) (P : state -> execution_ctx -> prog -> out -> Prop),
       (red_expr S C (spec_call_global_eval_2 a1) oo ->
        forall (S0 : state) (C0 : execution_ctx) (exte : ext_expr) (o : out),
        @eq (option out) (out_of_ext_expr (spec_call_global_eval_2 a1))
          (@Some out oo) ->
        abort oo ->
        not (abort_intercepted_expr (spec_call_global_eval_2 a1)) ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq ext_expr exte (spec_call_global_eval_2 a1) ->
        @eq out o oo -> P S C a1 oo) ->
       (red_expr S C (spec_call_global_eval_2 a1) oo ->
        forall (o1 : out) (S0 : state) (C0 : execution_ctx) 
          (p : prog) (o : out),
        red_prog S C (prog_basic a1) o1 ->
        red_expr S C (spec_call_global_eval_3 o1) oo ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq prog p a1 -> @eq out o oo -> P S C a1 oo) ->
       red_expr S C (spec_call_global_eval_2 a1) oo -> P S C a1 oo.

Parameter inv_red_expr_spec_call_global_eval_3
     : forall (S : state) (C : execution_ctx) (a1 oo : out)
         (P : state -> execution_ctx -> out -> out -> Prop),
       (red_expr S C (spec_call_global_eval_3 a1) oo ->
        forall (S0 : state) (C0 : execution_ctx) (exte : ext_expr) (o : out),
        @eq (option out) (out_of_ext_expr (spec_call_global_eval_3 a1))
          (@Some out oo) ->
        abort oo ->
        not (abort_intercepted_expr (spec_call_global_eval_3 a1)) ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq ext_expr exte (spec_call_global_eval_3 a1) ->
        @eq out o oo -> P S C a1 oo) ->
       (red_expr S C (spec_call_global_eval_3 a1) oo ->
        forall (S0 S1 : state) (C0 : execution_ctx) (v : value),
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq out (out_ter S1 (res_val v)) a1 ->
        @eq out (out_ter S1 (res_val v)) oo ->
        P S C (out_ter S1 (res_val v)) (out_ter S1 (res_val v))) ->
       (red_expr S C (spec_call_global_eval_3 a1) oo ->
        forall (S0 S1 : state) (C0 : execution_ctx) (R : res),
        @eq restype (res_type R) restype_normal ->
        @eq resvalue (res_value R) resvalue_empty ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq out (out_ter S1 R) a1 ->
        @eq out (out_ter S1 (res_val (value_prim prim_undef))) oo ->
        P S C (out_ter S1 R) (out_ter S1 (res_val (value_prim prim_undef)))) ->
       (red_expr S C (spec_call_global_eval_3 a1) oo ->
        forall (S0 S1 : state) (C0 : execution_ctx) (R : res),
        @eq restype (res_type R) restype_throw ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq out (out_ter S1 R) a1 ->
        @eq out (out_ter S1 (res_throw (res_value R))) oo ->
        P S C (out_ter S1 R) (out_ter S1 (res_throw (res_value R)))) ->
       red_expr S C (spec_call_global_eval_3 a1) oo -> P S C a1 oo.

Parameter inv_red_expr_spec_entering_func_code
     : forall (S : state) (C : execution_ctx) (a1 : object_loc) 
         (a2 : value) (a3 : list value) (a4 : ext_expr) 
         (oo : out)
         (P : state ->
              execution_ctx ->
              object_loc -> value -> list value -> ext_expr -> out -> Prop),
       (red_expr S C (spec_entering_func_code a1 a2 a3 a4) oo ->
        forall (S0 : state) (C0 : execution_ctx) (exte : ext_expr) (o : out),
        @eq (option out)
          (out_of_ext_expr (spec_entering_func_code a1 a2 a3 a4))
          (@Some out oo) ->
        abort oo ->
        not (abort_intercepted_expr (spec_entering_func_code a1 a2 a3 a4)) ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq ext_expr exte (spec_entering_func_code a1 a2 a3 a4) ->
        @eq out o oo -> P S C a1 a2 a3 a4 oo) ->
       (red_expr S C (spec_entering_func_code a1 a2 a3 a4) oo ->
        forall (S0 : state) (C0 : execution_ctx) (lf : object_loc)
          (vthis : value) (args : list value) (bd : funcbody)
          (str : strictness_flag) (K : ext_expr) (o : out),
        @object_method (option funcbody) object_code_ S a1
          (@Some funcbody bd) ->
        @eq strictness_flag str (funcbody_is_strict bd) ->
        red_expr S C (spec_entering_func_code_1 a1 a3 bd a2 str a4) oo ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq object_loc lf a1 ->
        @eq value vthis a2 ->
        @eq (list value) args a3 ->
        @eq ext_expr K a4 -> @eq out o oo -> P S C a1 a2 a3 a4 oo) ->
       red_expr S C (spec_entering_func_code a1 a2 a3 a4) oo ->
       P S C a1 a2 a3 a4 oo.

Parameter inv_red_expr_spec_entering_func_code_1
     : forall (S : state) (C : execution_ctx) (a1 : object_loc)
         (a2 : list value) (a3 : funcbody) (a4 : value)
         (a5 : strictness_flag) (a6 : ext_expr) (oo : out)
         (P : state ->
              execution_ctx ->
              object_loc ->
              list value ->
              funcbody -> value -> bool -> ext_expr -> out -> Prop),
       (red_expr S C (spec_entering_func_code_1 a1 a2 a3 a4 a5 a6) oo ->
        forall (S0 : state) (C0 : execution_ctx) (exte : ext_expr) (o : out),
        @eq (option out)
          (out_of_ext_expr (spec_entering_func_code_1 a1 a2 a3 a4 a5 a6))
          (@Some out oo) ->
        abort oo ->
        not
          (abort_intercepted_expr
             (spec_entering_func_code_1 a1 a2 a3 a4 a5 a6)) ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq ext_expr exte (spec_entering_func_code_1 a1 a2 a3 a4 a5 a6) ->
        @eq out o oo -> P S C a1 a2 a3 a4 a5 a6 oo) ->
       (red_expr S C (spec_entering_func_code_1 a1 a2 a3 a4 a5 a6) oo ->
        forall (S0 : state) (C0 : execution_ctx) (lf : object_loc)
          (args : list value) (bd : funcbody) (vthis : value) 
          (K : ext_expr) (o : out),
        red_expr S C (spec_entering_func_code_3 a1 a2 true a3 a4 a6) oo ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq object_loc lf a1 ->
        @eq (list value) args a2 ->
        @eq funcbody bd a3 ->
        @eq value vthis a4 ->
        @eq strictness_flag strictness_true a5 ->
        @eq ext_expr K a6 ->
        @eq out o oo -> P S C a1 a2 a3 a4 strictness_true a6 oo) ->
       (red_expr S C (spec_entering_func_code_1 a1 a2 a3 a4 a5 a6) oo ->
        forall (S0 : state) (C0 : execution_ctx) (lf : object_loc)
          (args : list value) (bd : funcbody) (vthis : value) 
          (K : ext_expr) (o : out),
        Logic.or (@eq value a4 (value_prim prim_null))
          (@eq value a4 (value_prim prim_undef)) ->
        red_expr S C
          (spec_entering_func_code_3 a1 a2 false a3
             (value_object (object_loc_prealloc prealloc_global)) a6) oo ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq object_loc lf a1 ->
        @eq (list value) args a2 ->
        @eq funcbody bd a3 ->
        @eq value vthis a4 ->
        @eq strictness_flag strictness_false a5 ->
        @eq ext_expr K a6 ->
        @eq out o oo -> P S C a1 a2 a3 a4 strictness_false a6 oo) ->
       (red_expr S C (spec_entering_func_code_1 a1 a2 a3 a4 a5 a6) oo ->
        forall (S0 : state) (C0 : execution_ctx) (lf : object_loc)
          (args : list value) (bd : funcbody) (vthis : value) 
          (o1 : out) (K : ext_expr) (o : out),
        Logic.and (not (@eq value a4 (value_prim prim_null)))
          (Logic.and (not (@eq value a4 (value_prim prim_undef)))
             (not (@eq type (type_of a4) type_object))) ->
        red_expr S C (spec_to_object a4) o1 ->
        red_expr S C (spec_entering_func_code_2 a1 a2 a3 o1 a6) oo ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq object_loc lf a1 ->
        @eq (list value) args a2 ->
        @eq funcbody bd a3 ->
        @eq value vthis a4 ->
        @eq strictness_flag strictness_false a5 ->
        @eq ext_expr K a6 ->
        @eq out o oo -> P S C a1 a2 a3 a4 strictness_false a6 oo) ->
       (red_expr S C (spec_entering_func_code_1 a1 a2 a3 a4 a5 a6) oo ->
        forall (S0 : state) (C0 : execution_ctx) (lf : object_loc)
          (args : list value) (bd : funcbody) (lthis : object_loc)
          (K : ext_expr) (o : out),
        red_expr S C
          (spec_entering_func_code_3 a1 a2 strictness_false a3
             (value_object lthis) a6) oo ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq object_loc lf a1 ->
        @eq (list value) args a2 ->
        @eq funcbody bd a3 ->
        @eq value (value_object lthis) a4 ->
        @eq strictness_flag strictness_false a5 ->
        @eq ext_expr K a6 ->
        @eq out o oo ->
        P S C a1 a2 a3 (value_object lthis) strictness_false a6 oo) ->
       red_expr S C (spec_entering_func_code_1 a1 a2 a3 a4 a5 a6) oo ->
       P S C a1 a2 a3 a4 a5 a6 oo.

Parameter inv_red_expr_spec_entering_func_code_2
     : forall (S : state) (C : execution_ctx) (a1 : object_loc)
         (a2 : list value) (a3 : funcbody) (a4 : out) 
         (a5 : ext_expr) (oo : out)
         (P : state ->
              execution_ctx ->
              object_loc ->
              list value -> funcbody -> out -> ext_expr -> out -> Prop),
       (red_expr S C (spec_entering_func_code_2 a1 a2 a3 a4 a5) oo ->
        forall (S0 : state) (C0 : execution_ctx) (exte : ext_expr) (o : out),
        @eq (option out)
          (out_of_ext_expr (spec_entering_func_code_2 a1 a2 a3 a4 a5))
          (@Some out oo) ->
        abort oo ->
        not
          (abort_intercepted_expr (spec_entering_func_code_2 a1 a2 a3 a4 a5)) ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq ext_expr exte (spec_entering_func_code_2 a1 a2 a3 a4 a5) ->
        @eq out o oo -> P S C a1 a2 a3 a4 a5 oo) ->
       (red_expr S C (spec_entering_func_code_2 a1 a2 a3 a4 a5) oo ->
        forall (S0 S1 : state) (C0 : execution_ctx) 
          (lf : object_loc) (args : list value) (bd : funcbody)
          (vthis : value) (K : ext_expr) (o : out),
        red_expr S0 C
          (spec_entering_func_code_3 a1 a2 strictness_false a3 vthis a5) oo ->
        @eq state S1 S ->
        @eq execution_ctx C0 C ->
        @eq object_loc lf a1 ->
        @eq (list value) args a2 ->
        @eq funcbody bd a3 ->
        @eq out (out_ter S0 (res_val vthis)) a4 ->
        @eq ext_expr K a5 ->
        @eq out o oo -> P S C a1 a2 a3 (out_ter S0 (res_val vthis)) a5 oo) ->
       red_expr S C (spec_entering_func_code_2 a1 a2 a3 a4 a5) oo ->
       P S C a1 a2 a3 a4 a5 oo.

Parameter inv_red_expr_spec_entering_func_code_3
     : forall (S : state) (C : execution_ctx) (a1 : object_loc)
         (a2 : list value) (a3 : strictness_flag) (a4 : funcbody)
         (a5 : value) (a6 : ext_expr) (oo : out)
         (P : state ->
              execution_ctx ->
              object_loc ->
              list value ->
              bool -> funcbody -> value -> ext_expr -> out -> Prop),
       (red_expr S C (spec_entering_func_code_3 a1 a2 a3 a4 a5 a6) oo ->
        forall (S0 : state) (C0 : execution_ctx) (exte : ext_expr) (o : out),
        @eq (option out)
          (out_of_ext_expr (spec_entering_func_code_3 a1 a2 a3 a4 a5 a6))
          (@Some out oo) ->
        abort oo ->
        not
          (abort_intercepted_expr
             (spec_entering_func_code_3 a1 a2 a3 a4 a5 a6)) ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq ext_expr exte (spec_entering_func_code_3 a1 a2 a3 a4 a5 a6) ->
        @eq out o oo -> P S C a1 a2 a3 a4 a5 a6 oo) ->
       (red_expr S C (spec_entering_func_code_3 a1 a2 a3 a4 a5 a6) oo ->
        forall (lex' : list nat) (S' : state) (C' : execution_ctx) 
          (o1 : out) (S0 : state) (C0 : execution_ctx) 
          (lf : object_loc) (args : list value) (str : strictness_flag)
          (bd : funcbody) (vthis : value) (lex : lexical_env) 
          (K : ext_expr) (o : out),
        @object_method (option lexical_env) object_scope_ S a1
          (@Some lexical_env lex) ->
        @eq (prod (list nat) state) (@pair (list nat) state lex' S')
          (lexical_env_alloc_decl S lex) ->
        @eq execution_ctx C' (execution_ctx_intro_same lex' a5 a3) ->
        red_expr S' C'
          (spec_binding_inst codetype_func (@Some object_loc a1)
             (funcbody_prog a4) a2) o1 ->
        red_expr S' C' (spec_entering_func_code_4 o1 a6) oo ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq object_loc lf a1 ->
        @eq (list value) args a2 ->
        @eq strictness_flag str a3 ->
        @eq funcbody bd a4 ->
        @eq value vthis a5 ->
        @eq ext_expr K a6 -> @eq out o oo -> P S C a1 a2 a3 a4 a5 a6 oo) ->
       red_expr S C (spec_entering_func_code_3 a1 a2 a3 a4 a5 a6) oo ->
       P S C a1 a2 a3 a4 a5 a6 oo.

Parameter inv_red_expr_spec_entering_func_code_4
     : forall (S : state) (C : execution_ctx) (a1 : out) 
         (a2 : ext_expr) (oo : out)
         (P : state -> execution_ctx -> out -> ext_expr -> out -> Prop),
       (red_expr S C (spec_entering_func_code_4 a1 a2) oo ->
        forall (S0 : state) (C0 : execution_ctx) (exte : ext_expr) (o : out),
        @eq (option out) (out_of_ext_expr (spec_entering_func_code_4 a1 a2))
          (@Some out oo) ->
        abort oo ->
        not (abort_intercepted_expr (spec_entering_func_code_4 a1 a2)) ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq ext_expr exte (spec_entering_func_code_4 a1 a2) ->
        @eq out o oo -> P S C a1 a2 oo) ->
       (red_expr S C (spec_entering_func_code_4 a1 a2) oo ->
        forall (S0 S1 : state) (C0 : execution_ctx) (K : ext_expr) (o : out),
        red_expr S1 C a2 oo ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq out (out_void S1) a1 ->
        @eq ext_expr K a2 -> @eq out o oo -> P S C (out_void S1) a2 oo) ->
       red_expr S C (spec_entering_func_code_4 a1 a2) oo -> P S C a1 a2 oo.

Parameter inv_red_expr_spec_binding_inst_formal_params
     : forall (S : state) (C : execution_ctx) (a1 : list value)
         (a2 : env_loc) (a3 : list string) (a4 : strictness_flag) 
         (oo : out)
         (P : state ->
              execution_ctx ->
              list value -> nat -> list string -> bool -> out -> Prop),
       (red_expr S C (spec_binding_inst_formal_params a1 a2 a3 a4) oo ->
        forall (S0 : state) (C0 : execution_ctx) (exte : ext_expr) (o : out),
        @eq (option out)
          (out_of_ext_expr (spec_binding_inst_formal_params a1 a2 a3 a4))
          (@Some out oo) ->
        abort oo ->
        not
          (abort_intercepted_expr
             (spec_binding_inst_formal_params a1 a2 a3 a4)) ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq ext_expr exte (spec_binding_inst_formal_params a1 a2 a3 a4) ->
        @eq out o oo -> P S C a1 a2 a3 a4 oo) ->
       (red_expr S C (spec_binding_inst_formal_params a1 a2 a3 a4) oo ->
        forall (S0 : state) (C0 : execution_ctx) (args : list value)
          (L : env_loc) (str : strictness_flag),
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq (list value) args a1 ->
        @eq env_loc L a2 ->
        @eq (list string) (@nil string) a3 ->
        @eq strictness_flag str a4 ->
        @eq out (out_void S) oo -> P S C a1 a2 (@nil string) a4 (out_void S)) ->
       (red_expr S C (spec_binding_inst_formal_params a1 a2 a3 a4) oo ->
        forall (v : value) (args' : list value) (S0 : state)
          (C0 : execution_ctx) (args : list value) 
          (L : env_loc) (x : prop_name) (xs : list prop_name)
          (str : strictness_flag) (o1 o : out),
        @eq (prod value (list value)) (@pair value (list value) v args')
          match a1 return (prod value (list value)) with
          | nil =>
              @pair value (list value) (value_prim prim_undef) (@nil value)
          | cons v0 args'0 => @pair value (list value) v0 args'0
          end ->
        red_expr S C (spec_env_record_has_binding a2 x) o1 ->
        red_expr S C
          (spec_binding_inst_formal_params_1 args' a2 x xs a4 v o1) oo ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq (list value) args a1 ->
        @eq env_loc L a2 ->
        @eq (list string) (@cons prop_name x xs) a3 ->
        @eq strictness_flag str a4 ->
        @eq out o oo -> P S C a1 a2 (@cons prop_name x xs) a4 oo) ->
       red_expr S C (spec_binding_inst_formal_params a1 a2 a3 a4) oo ->
       P S C a1 a2 a3 a4 oo.

Parameter inv_red_expr_spec_binding_inst_formal_params_1
     : forall (S : state) (C : execution_ctx) (a1 : list value)
         (a2 : env_loc) (a3 : string) (a4 : list string)
         (a5 : strictness_flag) (a6 : value) (a7 oo : out)
         (P : state ->
              execution_ctx ->
              list value ->
              nat ->
              string -> list string -> bool -> value -> out -> out -> Prop),
       (red_expr S C (spec_binding_inst_formal_params_1 a1 a2 a3 a4 a5 a6 a7)
          oo ->
        forall (S0 : state) (C0 : execution_ctx) (exte : ext_expr) (o : out),
        @eq (option out)
          (out_of_ext_expr
             (spec_binding_inst_formal_params_1 a1 a2 a3 a4 a5 a6 a7))
          (@Some out oo) ->
        abort oo ->
        not
          (abort_intercepted_expr
             (spec_binding_inst_formal_params_1 a1 a2 a3 a4 a5 a6 a7)) ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq ext_expr exte
          (spec_binding_inst_formal_params_1 a1 a2 a3 a4 a5 a6 a7) ->
        @eq out o oo -> P S C a1 a2 a3 a4 a5 a6 a7 oo) ->
       (red_expr S C (spec_binding_inst_formal_params_1 a1 a2 a3 a4 a5 a6 a7)
          oo ->
        forall (S0 S1 : state) (C0 : execution_ctx) 
          (args : list value) (L : env_loc) (x : prop_name)
          (xs : list prop_name) (str : strictness_flag) 
          (v : value) (o o1 : out),
        red_expr S1 C
          (spec_env_record_create_mutable_binding a2 a3 (@None bool)) o1 ->
        red_expr S1 C
          (spec_binding_inst_formal_params_2 a1 a2 a3 a4 a5 a6 o1) oo ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq (list value) args a1 ->
        @eq env_loc L a2 ->
        @eq string x a3 ->
        @eq (list string) xs a4 ->
        @eq strictness_flag str a5 ->
        @eq value v a6 ->
        @eq out (out_ter S1 (res_val (value_prim (prim_bool false)))) a7 ->
        @eq out o oo ->
        P S C a1 a2 a3 a4 a5 a6
          (out_ter S1 (res_val (value_prim (prim_bool false)))) oo) ->
       (red_expr S C (spec_binding_inst_formal_params_1 a1 a2 a3 a4 a5 a6 a7)
          oo ->
        forall (S0 S1 : state) (C0 : execution_ctx) 
          (args : list value) (L : env_loc) (x : prop_name)
          (xs : list prop_name) (str : strictness_flag) 
          (v : value) (o : out),
        red_expr S1 C (spec_binding_inst_formal_params_3 a1 a2 a3 a4 a5 a6)
          oo ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq (list value) args a1 ->
        @eq env_loc L a2 ->
        @eq string x a3 ->
        @eq (list string) xs a4 ->
        @eq strictness_flag str a5 ->
        @eq value v a6 ->
        @eq out (out_ter S1 (res_val (value_prim (prim_bool true)))) a7 ->
        @eq out o oo ->
        P S C a1 a2 a3 a4 a5 a6
          (out_ter S1 (res_val (value_prim (prim_bool true)))) oo) ->
       red_expr S C (spec_binding_inst_formal_params_1 a1 a2 a3 a4 a5 a6 a7)
         oo -> P S C a1 a2 a3 a4 a5 a6 a7 oo.

Parameter inv_red_expr_spec_binding_inst_formal_params_2
     : forall (S : state) (C : execution_ctx) (a1 : list value)
         (a2 : env_loc) (a3 : string) (a4 : list string)
         (a5 : strictness_flag) (a6 : value) (a7 oo : out)
         (P : state ->
              execution_ctx ->
              list value ->
              nat ->
              string -> list string -> bool -> value -> out -> out -> Prop),
       (red_expr S C (spec_binding_inst_formal_params_2 a1 a2 a3 a4 a5 a6 a7)
          oo ->
        forall (S0 : state) (C0 : execution_ctx) (exte : ext_expr) (o : out),
        @eq (option out)
          (out_of_ext_expr
             (spec_binding_inst_formal_params_2 a1 a2 a3 a4 a5 a6 a7))
          (@Some out oo) ->
        abort oo ->
        not
          (abort_intercepted_expr
             (spec_binding_inst_formal_params_2 a1 a2 a3 a4 a5 a6 a7)) ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq ext_expr exte
          (spec_binding_inst_formal_params_2 a1 a2 a3 a4 a5 a6 a7) ->
        @eq out o oo -> P S C a1 a2 a3 a4 a5 a6 a7 oo) ->
       (red_expr S C (spec_binding_inst_formal_params_2 a1 a2 a3 a4 a5 a6 a7)
          oo ->
        forall (S0 S1 : state) (C0 : execution_ctx) 
          (args : list value) (L : env_loc) (x : prop_name)
          (xs : list prop_name) (str : strictness_flag) 
          (v : value) (o : out),
        red_expr S1 C (spec_binding_inst_formal_params_3 a1 a2 a3 a4 a5 a6)
          oo ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq (list value) args a1 ->
        @eq env_loc L a2 ->
        @eq string x a3 ->
        @eq (list string) xs a4 ->
        @eq strictness_flag str a5 ->
        @eq value v a6 ->
        @eq out (out_void S1) a7 ->
        @eq out o oo -> P S C a1 a2 a3 a4 a5 a6 (out_void S1) oo) ->
       red_expr S C (spec_binding_inst_formal_params_2 a1 a2 a3 a4 a5 a6 a7)
         oo -> P S C a1 a2 a3 a4 a5 a6 a7 oo.

Parameter inv_red_expr_spec_binding_inst_formal_params_3
     : forall (S : state) (C : execution_ctx) (a1 : list value)
         (a2 : env_loc) (a3 : string) (a4 : list string)
         (a5 : strictness_flag) (a6 : value) (oo : out)
         (P : state ->
              execution_ctx ->
              list value ->
              nat -> string -> list string -> bool -> value -> out -> Prop),
       (red_expr S C (spec_binding_inst_formal_params_3 a1 a2 a3 a4 a5 a6) oo ->
        forall (S0 : state) (C0 : execution_ctx) (exte : ext_expr) (o : out),
        @eq (option out)
          (out_of_ext_expr
             (spec_binding_inst_formal_params_3 a1 a2 a3 a4 a5 a6))
          (@Some out oo) ->
        abort oo ->
        not
          (abort_intercepted_expr
             (spec_binding_inst_formal_params_3 a1 a2 a3 a4 a5 a6)) ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq ext_expr exte
          (spec_binding_inst_formal_params_3 a1 a2 a3 a4 a5 a6) ->
        @eq out o oo -> P S C a1 a2 a3 a4 a5 a6 oo) ->
       (red_expr S C (spec_binding_inst_formal_params_3 a1 a2 a3 a4 a5 a6) oo ->
        forall (o1 : out) (S0 : state) (C0 : execution_ctx)
          (args : list value) (L : env_loc) (x : prop_name)
          (xs : list prop_name) (str : strictness_flag) 
          (v : value) (o : out),
        red_expr S C (spec_env_record_set_mutable_binding a2 a3 a6 a5) o1 ->
        red_expr S C (spec_binding_inst_formal_params_4 a1 a2 a4 a5 o1) oo ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq (list value) args a1 ->
        @eq env_loc L a2 ->
        @eq string x a3 ->
        @eq (list string) xs a4 ->
        @eq strictness_flag str a5 ->
        @eq value v a6 -> @eq out o oo -> P S C a1 a2 a3 a4 a5 a6 oo) ->
       red_expr S C (spec_binding_inst_formal_params_3 a1 a2 a3 a4 a5 a6) oo ->
       P S C a1 a2 a3 a4 a5 a6 oo.

Parameter inv_red_expr_spec_binding_inst_formal_params_4
     : forall (S : state) (C : execution_ctx) (a1 : list value)
         (a2 : env_loc) (a3 : list string) (a4 : strictness_flag)
         (a5 oo : out)
         (P : state ->
              execution_ctx ->
              list value -> nat -> list string -> bool -> out -> out -> Prop),
       (red_expr S C (spec_binding_inst_formal_params_4 a1 a2 a3 a4 a5) oo ->
        forall (S0 : state) (C0 : execution_ctx) (exte : ext_expr) (o : out),
        @eq (option out)
          (out_of_ext_expr (spec_binding_inst_formal_params_4 a1 a2 a3 a4 a5))
          (@Some out oo) ->
        abort oo ->
        not
          (abort_intercepted_expr
             (spec_binding_inst_formal_params_4 a1 a2 a3 a4 a5)) ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq ext_expr exte (spec_binding_inst_formal_params_4 a1 a2 a3 a4 a5) ->
        @eq out o oo -> P S C a1 a2 a3 a4 a5 oo) ->
       (red_expr S C (spec_binding_inst_formal_params_4 a1 a2 a3 a4 a5) oo ->
        forall (S0 S1 : state) (C0 : execution_ctx) 
          (args : list value) (L : env_loc) (xs : list prop_name)
          (str : strictness_flag) (o : out),
        red_expr S1 C (spec_binding_inst_formal_params a1 a2 a3 a4) oo ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq (list value) args a1 ->
        @eq env_loc L a2 ->
        @eq (list string) xs a3 ->
        @eq strictness_flag str a4 ->
        @eq out (out_void S1) a5 ->
        @eq out o oo -> P S C a1 a2 a3 a4 (out_void S1) oo) ->
       red_expr S C (spec_binding_inst_formal_params_4 a1 a2 a3 a4 a5) oo ->
       P S C a1 a2 a3 a4 a5 oo.

Parameter inv_red_expr_spec_binding_inst_function_decls
     : forall (S : state) (C : execution_ctx) (a1 : env_loc)
         (a2 : list funcdecl) (a3 : strictness_flag) 
         (a4 : bool) (oo : out)
         (P : state ->
              execution_ctx ->
              nat -> list funcdecl -> bool -> bool -> out -> Prop),
       (red_expr S C (spec_binding_inst_function_decls a1 a2 a3 a4) oo ->
        forall (S0 : state) (C0 : execution_ctx) (exte : ext_expr) (o : out),
        @eq (option out)
          (out_of_ext_expr (spec_binding_inst_function_decls a1 a2 a3 a4))
          (@Some out oo) ->
        abort oo ->
        not
          (abort_intercepted_expr
             (spec_binding_inst_function_decls a1 a2 a3 a4)) ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq ext_expr exte (spec_binding_inst_function_decls a1 a2 a3 a4) ->
        @eq out o oo -> P S C a1 a2 a3 a4 oo) ->
       (red_expr S C (spec_binding_inst_function_decls a1 a2 a3 a4) oo ->
        forall (L : env_loc) (S0 : state) (C0 : execution_ctx)
          (str : strictness_flag) (bconfig : bool),
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq env_loc L a1 ->
        @eq (list funcdecl) (@nil funcdecl) a2 ->
        @eq strictness_flag str a3 ->
        @eq bool bconfig a4 ->
        @eq out (out_void S) oo ->
        P S C a1 (@nil funcdecl) a3 a4 (out_void S)) ->
       (red_expr S C (spec_binding_inst_function_decls a1 a2 a3 a4) oo ->
        forall (str_fd : strictness_flag) (S0 : state) 
          (C0 : execution_ctx) (L : env_loc) (fd : funcdecl)
          (fds : list funcdecl) (str : strictness_flag) 
          (bconfig : bool) (o1 o : out),
        @eq strictness_flag str_fd (funcbody_is_strict (funcdecl_body fd)) ->
        red_expr S C
          (spec_creating_function_object (funcdecl_parameters fd)
             (funcdecl_body fd) (execution_ctx_variable_env C) str_fd) o1 ->
        red_expr S C (spec_binding_inst_function_decls_1 a1 fd fds a3 a4 o1)
          oo ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq env_loc L a1 ->
        @eq (list funcdecl) (@cons funcdecl fd fds) a2 ->
        @eq strictness_flag str a3 ->
        @eq bool bconfig a4 ->
        @eq out o oo -> P S C a1 (@cons funcdecl fd fds) a3 a4 oo) ->
       red_expr S C (spec_binding_inst_function_decls a1 a2 a3 a4) oo ->
       P S C a1 a2 a3 a4 oo.

Parameter inv_red_expr_spec_binding_inst_function_decls_1
     : forall (S : state) (C : execution_ctx) (a1 : env_loc) 
         (a2 : funcdecl) (a3 : list funcdecl) (a4 : strictness_flag)
         (a5 : bool) (a6 oo : out)
         (P : state ->
              execution_ctx ->
              nat ->
              funcdecl -> list funcdecl -> bool -> bool -> out -> out -> Prop),
       (red_expr S C (spec_binding_inst_function_decls_1 a1 a2 a3 a4 a5 a6)
          oo ->
        forall (S0 : state) (C0 : execution_ctx) (exte : ext_expr) (o : out),
        @eq (option out)
          (out_of_ext_expr
             (spec_binding_inst_function_decls_1 a1 a2 a3 a4 a5 a6))
          (@Some out oo) ->
        abort oo ->
        not
          (abort_intercepted_expr
             (spec_binding_inst_function_decls_1 a1 a2 a3 a4 a5 a6)) ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq ext_expr exte
          (spec_binding_inst_function_decls_1 a1 a2 a3 a4 a5 a6) ->
        @eq out o oo -> P S C a1 a2 a3 a4 a5 a6 oo) ->
       (red_expr S C (spec_binding_inst_function_decls_1 a1 a2 a3 a4 a5 a6)
          oo ->
        forall (o1 : out) (L : env_loc) (S0 S1 : state) 
          (C0 : execution_ctx) (fd : funcdecl) (fds : list funcdecl)
          (str : strictness_flag) (fo : object_loc) 
          (bconfig : bool) (o : out),
        red_expr S1 C (spec_env_record_has_binding a1 (funcdecl_name a2)) o1 ->
        red_expr S1 C
          (spec_binding_inst_function_decls_2 a1 a2 a3 a4 fo a5 o1) oo ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq env_loc L a1 ->
        @eq funcdecl fd a2 ->
        @eq (list funcdecl) fds a3 ->
        @eq strictness_flag str a4 ->
        @eq bool bconfig a5 ->
        @eq out (out_ter S1 (res_val (value_object fo))) a6 ->
        @eq out o oo ->
        P S C a1 a2 a3 a4 a5 (out_ter S1 (res_val (value_object fo))) oo) ->
       red_expr S C (spec_binding_inst_function_decls_1 a1 a2 a3 a4 a5 a6) oo ->
       P S C a1 a2 a3 a4 a5 a6 oo.

Parameter inv_red_expr_spec_binding_inst_function_decls_2
     : forall (S : state) (C : execution_ctx) (a1 : env_loc) 
         (a2 : funcdecl) (a3 : list funcdecl) (a4 : strictness_flag)
         (a5 : object_loc) (a6 : bool) (a7 oo : out)
         (P : state ->
              execution_ctx ->
              nat ->
              funcdecl ->
              list funcdecl ->
              bool -> object_loc -> bool -> out -> out -> Prop),
       (red_expr S C
          (spec_binding_inst_function_decls_2 a1 a2 a3 a4 a5 a6 a7) oo ->
        forall (S0 : state) (C0 : execution_ctx) (exte : ext_expr) (o : out),
        @eq (option out)
          (out_of_ext_expr
             (spec_binding_inst_function_decls_2 a1 a2 a3 a4 a5 a6 a7))
          (@Some out oo) ->
        abort oo ->
        not
          (abort_intercepted_expr
             (spec_binding_inst_function_decls_2 a1 a2 a3 a4 a5 a6 a7)) ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq ext_expr exte
          (spec_binding_inst_function_decls_2 a1 a2 a3 a4 a5 a6 a7) ->
        @eq out o oo -> P S C a1 a2 a3 a4 a5 a6 a7 oo) ->
       (red_expr S C
          (spec_binding_inst_function_decls_2 a1 a2 a3 a4 a5 a6 a7) oo ->
        forall (o1 : out) (L : env_loc) (S0 S1 : state) 
          (C0 : execution_ctx) (fd : funcdecl) (fds : list funcdecl)
          (str : strictness_flag) (fo : object_loc) 
          (bconfig : bool) (o : out),
        red_expr S1 C
          (spec_env_record_create_mutable_binding a1 
             (funcdecl_name a2) (@Some bool a6)) o1 ->
        red_expr S1 C
          (spec_binding_inst_function_decls_4 a1 a2 a3 a4 a5 a6 o1) oo ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq env_loc L a1 ->
        @eq funcdecl fd a2 ->
        @eq (list funcdecl) fds a3 ->
        @eq strictness_flag str a4 ->
        @eq object_loc fo a5 ->
        @eq bool bconfig a6 ->
        @eq out (out_ter S1 (res_val (value_prim (prim_bool false)))) a7 ->
        @eq out o oo ->
        P S C a1 a2 a3 a4 a5 a6
          (out_ter S1 (res_val (value_prim (prim_bool false)))) oo) ->
       (red_expr S C
          (spec_binding_inst_function_decls_2 a1 a2 a3 a4 a5 a6 a7) oo ->
        forall (S0 S1 : state) (C0 : execution_ctx) 
          (fd : funcdecl) (fds : list funcdecl) (str : strictness_flag)
          (fo : object_loc) (bconfig : bool) (y1 : specret full_descriptor)
          (o : out),
        @red_spec full_descriptor S1 C
          (spec_object_get_prop (object_loc_prealloc prealloc_global)
             (funcdecl_name a2)) y1 ->
        red_expr S1 C (spec_binding_inst_function_decls_3 a2 a3 a4 a5 a6 y1)
          oo ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq env_loc env_loc_global_env_record a1 ->
        @eq funcdecl fd a2 ->
        @eq (list funcdecl) fds a3 ->
        @eq strictness_flag str a4 ->
        @eq object_loc fo a5 ->
        @eq bool bconfig a6 ->
        @eq out (out_ter S1 (res_val (value_prim (prim_bool true)))) a7 ->
        @eq out o oo ->
        P S C env_loc_global_env_record a2 a3 a4 a5 a6
          (out_ter S1 (res_val (value_prim (prim_bool true)))) oo) ->
       (red_expr S C
          (spec_binding_inst_function_decls_2 a1 a2 a3 a4 a5 a6 a7) oo ->
        forall (L : env_loc) (S0 S1 : state) (C0 : execution_ctx)
          (fd : funcdecl) (fds : list funcdecl) (str : strictness_flag)
          (fo : object_loc) (bconfig : bool) (o : out),
        not (@eq env_loc a1 env_loc_global_env_record) ->
        red_expr S1 C (spec_binding_inst_function_decls_5 a1 a2 a3 a4 a5 a6)
          oo ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq env_loc L a1 ->
        @eq funcdecl fd a2 ->
        @eq (list funcdecl) fds a3 ->
        @eq strictness_flag str a4 ->
        @eq object_loc fo a5 ->
        @eq bool bconfig a6 ->
        @eq out (out_ter S1 (res_val (value_prim (prim_bool true)))) a7 ->
        @eq out o oo ->
        P S C a1 a2 a3 a4 a5 a6
          (out_ter S1 (res_val (value_prim (prim_bool true)))) oo) ->
       red_expr S C (spec_binding_inst_function_decls_2 a1 a2 a3 a4 a5 a6 a7)
         oo -> P S C a1 a2 a3 a4 a5 a6 a7 oo.

Parameter inv_red_expr_spec_binding_inst_function_decls_3
     : forall (S : state) (C : execution_ctx) (a1 : funcdecl)
         (a2 : list funcdecl) (a3 : strictness_flag) 
         (a4 : object_loc) (a5 : bool) (a6 : specret full_descriptor)
         (oo : out)
         (P : state ->
              execution_ctx ->
              funcdecl ->
              list funcdecl ->
              bool ->
              object_loc -> bool -> specret full_descriptor -> out -> Prop),
       (red_expr S C (spec_binding_inst_function_decls_3 a1 a2 a3 a4 a5 a6)
          oo ->
        forall (S0 : state) (C0 : execution_ctx) (exte : ext_expr) (o : out),
        @eq (option out)
          (out_of_ext_expr
             (spec_binding_inst_function_decls_3 a1 a2 a3 a4 a5 a6))
          (@Some out oo) ->
        abort oo ->
        not
          (abort_intercepted_expr
             (spec_binding_inst_function_decls_3 a1 a2 a3 a4 a5 a6)) ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq ext_expr exte
          (spec_binding_inst_function_decls_3 a1 a2 a3 a4 a5 a6) ->
        @eq out o oo -> P S C a1 a2 a3 a4 a5 a6 oo) ->
       (red_expr S C (spec_binding_inst_function_decls_3 a1 a2 a3 a4 a5 a6)
          oo ->
        forall (S0 S1 : state) (C0 : execution_ctx) 
          (fd : funcdecl) (fds : list funcdecl) (str : strictness_flag)
          (fo : object_loc) (bconfig : bool) (A : attributes)
          (Anew : attributes_data) (o1 o : out),
        @eq bool (attributes_configurable A) true ->
        @eq attributes_data Anew
          (attributes_data_intro (value_prim prim_undef) true true a5) ->
        red_expr S1 C
          (spec_object_define_own_prop (object_loc_prealloc prealloc_global)
             (funcdecl_name a1)
             (descriptor_of_attributes (attributes_data_of Anew)) true) o1 ->
        red_expr S1 C
          (spec_binding_inst_function_decls_4 env_loc_global_env_record a1 a2
             a3 a4 a5 o1) oo ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq funcdecl fd a1 ->
        @eq (list funcdecl) fds a2 ->
        @eq strictness_flag str a3 ->
        @eq object_loc fo a4 ->
        @eq bool bconfig a5 ->
        @eq (specret full_descriptor)
          (@ret full_descriptor S1 (full_descriptor_some A)) a6 ->
        @eq out o oo ->
        P S C a1 a2 a3 a4 a5
          (@ret full_descriptor S1 (full_descriptor_some A)) oo) ->
       (red_expr S C (spec_binding_inst_function_decls_3 a1 a2 a3 a4 a5 a6)
          oo ->
        forall (S0 S1 : state) (C0 : execution_ctx) 
          (fd : funcdecl) (fds : list funcdecl) (str : strictness_flag)
          (fo : object_loc) (A : attributes) (bconfig : bool) 
          (o : out),
        @eq bool (attributes_configurable A) false ->
        red_expr S1 C
          (spec_binding_inst_function_decls_3a a1 a2 a3 a4 a5
             (full_descriptor_some A)) oo ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq funcdecl fd a1 ->
        @eq (list funcdecl) fds a2 ->
        @eq strictness_flag str a3 ->
        @eq object_loc fo a4 ->
        @eq bool bconfig a5 ->
        @eq (specret full_descriptor)
          (@ret full_descriptor S1 (full_descriptor_some A)) a6 ->
        @eq out o oo ->
        P S C a1 a2 a3 a4 a5
          (@ret full_descriptor S1 (full_descriptor_some A)) oo) ->
       red_expr S C (spec_binding_inst_function_decls_3 a1 a2 a3 a4 a5 a6) oo ->
       P S C a1 a2 a3 a4 a5 a6 oo.

Parameter inv_red_expr_spec_binding_inst_function_decls_3a
     : forall (S : state) (C : execution_ctx) (a1 : funcdecl)
         (a2 : list funcdecl) (a3 : strictness_flag) 
         (a4 : object_loc) (a5 : bool) (a6 : full_descriptor) 
         (oo : out)
         (P : state ->
              execution_ctx ->
              funcdecl ->
              list funcdecl ->
              bool -> object_loc -> bool -> full_descriptor -> out -> Prop),
       (red_expr S C (spec_binding_inst_function_decls_3a a1 a2 a3 a4 a5 a6)
          oo ->
        forall (S0 : state) (C0 : execution_ctx) (exte : ext_expr) (o : out),
        @eq (option out)
          (out_of_ext_expr
             (spec_binding_inst_function_decls_3a a1 a2 a3 a4 a5 a6))
          (@Some out oo) ->
        abort oo ->
        not
          (abort_intercepted_expr
             (spec_binding_inst_function_decls_3a a1 a2 a3 a4 a5 a6)) ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq ext_expr exte
          (spec_binding_inst_function_decls_3a a1 a2 a3 a4 a5 a6) ->
        @eq out o oo -> P S C a1 a2 a3 a4 a5 a6 oo) ->
       (red_expr S C (spec_binding_inst_function_decls_3a a1 a2 a3 a4 a5 a6)
          oo ->
        forall (S0 : state) (C0 : execution_ctx) (fd : funcdecl)
          (fds : list funcdecl) (str : strictness_flag) 
          (fo : object_loc) (A : attributes) (bconfig : bool) 
          (o : out),
        Logic.or (descriptor_is_accessor (descriptor_of_attributes A))
          (Logic.or (@eq bool (attributes_writable A) false)
             (@eq bool (attributes_enumerable A) false)) ->
        red_expr S C (spec_error native_error_type) oo ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq funcdecl fd a1 ->
        @eq (list funcdecl) fds a2 ->
        @eq strictness_flag str a3 ->
        @eq object_loc fo a4 ->
        @eq bool bconfig a5 ->
        @eq full_descriptor (full_descriptor_some A) a6 ->
        @eq out o oo -> P S C a1 a2 a3 a4 a5 (full_descriptor_some A) oo) ->
       (red_expr S C (spec_binding_inst_function_decls_3a a1 a2 a3 a4 a5 a6)
          oo ->
        forall (S0 : state) (C0 : execution_ctx) (fd : funcdecl)
          (fds : list funcdecl) (str : strictness_flag) 
          (fo : object_loc) (A : attributes) (bconfig : bool) 
          (o : out),
        not
          (Logic.or (descriptor_is_accessor (descriptor_of_attributes A))
             (Logic.or (@eq bool (attributes_writable A) false)
                (@eq bool (attributes_enumerable A) false))) ->
        red_expr S C
          (spec_binding_inst_function_decls_5 env_loc_global_env_record a1 a2
             a3 a4 a5) oo ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq funcdecl fd a1 ->
        @eq (list funcdecl) fds a2 ->
        @eq strictness_flag str a3 ->
        @eq object_loc fo a4 ->
        @eq bool bconfig a5 ->
        @eq full_descriptor (full_descriptor_some A) a6 ->
        @eq out o oo -> P S C a1 a2 a3 a4 a5 (full_descriptor_some A) oo) ->
       red_expr S C (spec_binding_inst_function_decls_3a a1 a2 a3 a4 a5 a6)
         oo -> P S C a1 a2 a3 a4 a5 a6 oo.

Parameter inv_red_expr_spec_binding_inst_function_decls_4
     : forall (S : state) (C : execution_ctx) (a1 : env_loc) 
         (a2 : funcdecl) (a3 : list funcdecl) (a4 : strictness_flag)
         (a5 : object_loc) (a6 : bool) (a7 oo : out)
         (P : state ->
              execution_ctx ->
              nat ->
              funcdecl ->
              list funcdecl ->
              bool -> object_loc -> bool -> out -> out -> Prop),
       (red_expr S C
          (spec_binding_inst_function_decls_4 a1 a2 a3 a4 a5 a6 a7) oo ->
        forall (S0 : state) (C0 : execution_ctx) (exte : ext_expr) (o : out),
        @eq (option out)
          (out_of_ext_expr
             (spec_binding_inst_function_decls_4 a1 a2 a3 a4 a5 a6 a7))
          (@Some out oo) ->
        abort oo ->
        not
          (abort_intercepted_expr
             (spec_binding_inst_function_decls_4 a1 a2 a3 a4 a5 a6 a7)) ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq ext_expr exte
          (spec_binding_inst_function_decls_4 a1 a2 a3 a4 a5 a6 a7) ->
        @eq out o oo -> P S C a1 a2 a3 a4 a5 a6 a7 oo) ->
       (red_expr S C
          (spec_binding_inst_function_decls_4 a1 a2 a3 a4 a5 a6 a7) oo ->
        forall (S0 S1 : state) (C0 : execution_ctx) 
          (L : env_loc) (fd : funcdecl) (fds : list funcdecl)
          (str : strictness_flag) (fo : object_loc) 
          (bconfig : bool) (rv : resvalue) (o : out),
        red_expr S1 C (spec_binding_inst_function_decls_5 a1 a2 a3 a4 a5 a6)
          oo ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq env_loc L a1 ->
        @eq funcdecl fd a2 ->
        @eq (list funcdecl) fds a3 ->
        @eq strictness_flag str a4 ->
        @eq object_loc fo a5 ->
        @eq bool bconfig a6 ->
        @eq out (out_ter S1 (res_normal rv)) a7 ->
        @eq out o oo ->
        P S C a1 a2 a3 a4 a5 a6 (out_ter S1 (res_normal rv)) oo) ->
       red_expr S C (spec_binding_inst_function_decls_4 a1 a2 a3 a4 a5 a6 a7)
         oo -> P S C a1 a2 a3 a4 a5 a6 a7 oo.

Parameter inv_red_expr_spec_binding_inst_function_decls_5
     : forall (S : state) (C : execution_ctx) (a1 : env_loc) 
         (a2 : funcdecl) (a3 : list funcdecl) (a4 : strictness_flag)
         (a5 : object_loc) (a6 : bool) (oo : out)
         (P : state ->
              execution_ctx ->
              nat ->
              funcdecl ->
              list funcdecl -> bool -> object_loc -> bool -> out -> Prop),
       (red_expr S C (spec_binding_inst_function_decls_5 a1 a2 a3 a4 a5 a6)
          oo ->
        forall (S0 : state) (C0 : execution_ctx) (exte : ext_expr) (o : out),
        @eq (option out)
          (out_of_ext_expr
             (spec_binding_inst_function_decls_5 a1 a2 a3 a4 a5 a6))
          (@Some out oo) ->
        abort oo ->
        not
          (abort_intercepted_expr
             (spec_binding_inst_function_decls_5 a1 a2 a3 a4 a5 a6)) ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq ext_expr exte
          (spec_binding_inst_function_decls_5 a1 a2 a3 a4 a5 a6) ->
        @eq out o oo -> P S C a1 a2 a3 a4 a5 a6 oo) ->
       (red_expr S C (spec_binding_inst_function_decls_5 a1 a2 a3 a4 a5 a6)
          oo ->
        forall (o1 : out) (L : env_loc) (S0 : state) 
          (C0 : execution_ctx) (fd : funcdecl) (fds : list funcdecl)
          (str : strictness_flag) (fo : object_loc) 
          (bconfig : bool) (o : out),
        red_expr S C
          (spec_env_record_set_mutable_binding a1 (funcdecl_name a2)
             (value_object a5) a4) o1 ->
        red_expr S C (spec_binding_inst_function_decls_6 a1 a3 a4 a6 o1) oo ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq env_loc L a1 ->
        @eq funcdecl fd a2 ->
        @eq (list funcdecl) fds a3 ->
        @eq strictness_flag str a4 ->
        @eq object_loc fo a5 ->
        @eq bool bconfig a6 -> @eq out o oo -> P S C a1 a2 a3 a4 a5 a6 oo) ->
       red_expr S C (spec_binding_inst_function_decls_5 a1 a2 a3 a4 a5 a6) oo ->
       P S C a1 a2 a3 a4 a5 a6 oo.

Parameter inv_red_expr_spec_binding_inst_function_decls_6
     : forall (S : state) (C : execution_ctx) (a1 : env_loc)
         (a2 : list funcdecl) (a3 : strictness_flag) 
         (a4 : bool) (a5 oo : out)
         (P : state ->
              execution_ctx ->
              nat -> list funcdecl -> bool -> bool -> out -> out -> Prop),
       (red_expr S C (spec_binding_inst_function_decls_6 a1 a2 a3 a4 a5) oo ->
        forall (S0 : state) (C0 : execution_ctx) (exte : ext_expr) (o : out),
        @eq (option out)
          (out_of_ext_expr
             (spec_binding_inst_function_decls_6 a1 a2 a3 a4 a5))
          (@Some out oo) ->
        abort oo ->
        not
          (abort_intercepted_expr
             (spec_binding_inst_function_decls_6 a1 a2 a3 a4 a5)) ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq ext_expr exte (spec_binding_inst_function_decls_6 a1 a2 a3 a4 a5) ->
        @eq out o oo -> P S C a1 a2 a3 a4 a5 oo) ->
       (red_expr S C (spec_binding_inst_function_decls_6 a1 a2 a3 a4 a5) oo ->
        forall (L : env_loc) (S0 S1 : state) (C0 : execution_ctx)
          (fds : list funcdecl) (str : strictness_flag) 
          (bconfig : bool) (o : out),
        red_expr S1 C (spec_binding_inst_function_decls a1 a2 a3 a4) oo ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq env_loc L a1 ->
        @eq (list funcdecl) fds a2 ->
        @eq strictness_flag str a3 ->
        @eq bool bconfig a4 ->
        @eq out (out_void S1) a5 ->
        @eq out o oo -> P S C a1 a2 a3 a4 (out_void S1) oo) ->
       red_expr S C (spec_binding_inst_function_decls_6 a1 a2 a3 a4 a5) oo ->
       P S C a1 a2 a3 a4 a5 oo.

Parameter inv_red_expr_spec_binding_inst_arg_obj
     : forall (S : state) (C : execution_ctx) (a1 : object_loc)
         (a2 : list string) (a3 : list value) (a4 : env_loc)
         (a5 : strictness_flag) (oo : out)
         (P : state ->
              execution_ctx ->
              object_loc ->
              list string -> list value -> nat -> bool -> out -> Prop),
       (red_expr S C (spec_binding_inst_arg_obj a1 a2 a3 a4 a5) oo ->
        forall (S0 : state) (C0 : execution_ctx) (exte : ext_expr) (o : out),
        @eq (option out)
          (out_of_ext_expr (spec_binding_inst_arg_obj a1 a2 a3 a4 a5))
          (@Some out oo) ->
        abort oo ->
        not
          (abort_intercepted_expr (spec_binding_inst_arg_obj a1 a2 a3 a4 a5)) ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq ext_expr exte (spec_binding_inst_arg_obj a1 a2 a3 a4 a5) ->
        @eq out o oo -> P S C a1 a2 a3 a4 a5 oo) ->
       (red_expr S C (spec_binding_inst_arg_obj a1 a2 a3 a4 a5) oo ->
        forall (str : strictness_flag) (o1 : out) (L : env_loc) 
          (S0 : state) (C0 : execution_ctx) (lf : object_loc)
          (xs : list prop_name) (args : list value) 
          (o : out),
        red_expr S C
          (spec_create_arguments_object a1 a2 a3
             (execution_ctx_variable_env C) a5) o1 ->
        red_expr S C (spec_binding_inst_arg_obj_1 a4 a5 o1) oo ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq object_loc lf a1 ->
        @eq (list string) xs a2 ->
        @eq (list value) args a3 ->
        @eq env_loc L a4 ->
        @eq strictness_flag str a5 -> @eq out o oo -> P S C a1 a2 a3 a4 a5 oo) ->
       red_expr S C (spec_binding_inst_arg_obj a1 a2 a3 a4 a5) oo ->
       P S C a1 a2 a3 a4 a5 oo.

Parameter inv_red_expr_spec_binding_inst_arg_obj_1
     : forall (S : state) (C : execution_ctx) (a1 : env_loc)
         (a2 : strictness_flag) (a3 oo : out)
         (P : state -> execution_ctx -> nat -> bool -> out -> out -> Prop),
       (red_expr S C (spec_binding_inst_arg_obj_1 a1 a2 a3) oo ->
        forall (S0 : state) (C0 : execution_ctx) (exte : ext_expr) (o : out),
        @eq (option out)
          (out_of_ext_expr (spec_binding_inst_arg_obj_1 a1 a2 a3))
          (@Some out oo) ->
        abort oo ->
        not (abort_intercepted_expr (spec_binding_inst_arg_obj_1 a1 a2 a3)) ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq ext_expr exte (spec_binding_inst_arg_obj_1 a1 a2 a3) ->
        @eq out o oo -> P S C a1 a2 a3 oo) ->
       (red_expr S C (spec_binding_inst_arg_obj_1 a1 a2 a3) oo ->
        forall (o1 : out) (L : env_loc) (S0 S1 : state) 
          (C0 : execution_ctx) (largs : object_loc) 
          (o : out),
        red_expr S1 C
          (spec_env_record_create_immutable_binding a1
             (String (Ascii true false false false false true true false)
                (String (Ascii false true false false true true true false)
                   (String (Ascii true true true false false true true false)
                      (String
                         (Ascii true false true false true true true false)
                         (String
                            (Ascii true false true true false true true false)
                            (String
                               (Ascii true false true false false true true
                                  false)
                               (String
                                  (Ascii false true true true false true true
                                     false)
                                  (String
                                     (Ascii false false true false true true
                                        true false)
                                     (String
                                        (Ascii true true false false true
                                           true true false) EmptyString))))))))))
          o1 ->
        red_expr S1 C (spec_binding_inst_arg_obj_2 a1 largs o1) oo ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq env_loc L a1 ->
        @eq strictness_flag true a2 ->
        @eq out (out_ter S1 (res_val (value_object largs))) a3 ->
        @eq out o oo ->
        P S C a1 true (out_ter S1 (res_val (value_object largs))) oo) ->
       (red_expr S C (spec_binding_inst_arg_obj_1 a1 a2 a3) oo ->
        forall (L : env_loc) (S0 S1 : state) (C0 : execution_ctx)
          (largs : value) (o : out),
        red_expr S1 C
          (spec_env_record_create_set_mutable_binding a1
             (String (Ascii true false false false false true true false)
                (String (Ascii false true false false true true true false)
                   (String (Ascii true true true false false true true false)
                      (String
                         (Ascii true false true false true true true false)
                         (String
                            (Ascii true false true true false true true false)
                            (String
                               (Ascii true false true false false true true
                                  false)
                               (String
                                  (Ascii false true true true false true true
                                     false)
                                  (String
                                     (Ascii false false true false true true
                                        true false)
                                     (String
                                        (Ascii true true false false true
                                           true true false) EmptyString)))))))))
             (@None bool) largs false) oo ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq env_loc L a1 ->
        @eq strictness_flag false a2 ->
        @eq out (out_ter S1 (res_val largs)) a3 ->
        @eq out o oo -> P S C a1 false (out_ter S1 (res_val largs)) oo) ->
       red_expr S C (spec_binding_inst_arg_obj_1 a1 a2 a3) oo ->
       P S C a1 a2 a3 oo.

Parameter inv_red_expr_spec_binding_inst_arg_obj_2
     : forall (S : state) (C : execution_ctx) (a1 : env_loc)
         (a2 : object_loc) (a3 oo : out)
         (P : state ->
              execution_ctx -> nat -> object_loc -> out -> out -> Prop),
       (red_expr S C (spec_binding_inst_arg_obj_2 a1 a2 a3) oo ->
        forall (S0 : state) (C0 : execution_ctx) (exte : ext_expr) (o : out),
        @eq (option out)
          (out_of_ext_expr (spec_binding_inst_arg_obj_2 a1 a2 a3))
          (@Some out oo) ->
        abort oo ->
        not (abort_intercepted_expr (spec_binding_inst_arg_obj_2 a1 a2 a3)) ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq ext_expr exte (spec_binding_inst_arg_obj_2 a1 a2 a3) ->
        @eq out o oo -> P S C a1 a2 a3 oo) ->
       (red_expr S C (spec_binding_inst_arg_obj_2 a1 a2 a3) oo ->
        forall (L : env_loc) (S0 S1 : state) (C0 : execution_ctx)
          (largs : object_loc) (o : out),
        red_expr S1 C
          (spec_env_record_initialize_immutable_binding a1
             (String (Ascii true false false false false true true false)
                (String (Ascii false true false false true true true false)
                   (String (Ascii true true true false false true true false)
                      (String
                         (Ascii true false true false true true true false)
                         (String
                            (Ascii true false true true false true true false)
                            (String
                               (Ascii true false true false false true true
                                  false)
                               (String
                                  (Ascii false true true true false true true
                                     false)
                                  (String
                                     (Ascii false false true false true true
                                        true false)
                                     (String
                                        (Ascii true true false false true
                                           true true false) EmptyString)))))))))
             (value_object a2)) oo ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq env_loc L a1 ->
        @eq object_loc largs a2 ->
        @eq out (out_void S1) a3 ->
        @eq out o oo -> P S C a1 a2 (out_void S1) oo) ->
       red_expr S C (spec_binding_inst_arg_obj_2 a1 a2 a3) oo ->
       P S C a1 a2 a3 oo.

Parameter inv_red_expr_spec_binding_inst_var_decls
     : forall (S : state) (C : execution_ctx) (a1 : env_loc)
         (a2 : list string) (a3 : bool) (a4 : strictness_flag) 
         (oo : out)
         (P : state ->
              execution_ctx ->
              nat -> list string -> bool -> bool -> out -> Prop),
       (red_expr S C (spec_binding_inst_var_decls a1 a2 a3 a4) oo ->
        forall (S0 : state) (C0 : execution_ctx) (exte : ext_expr) (o : out),
        @eq (option out)
          (out_of_ext_expr (spec_binding_inst_var_decls a1 a2 a3 a4))
          (@Some out oo) ->
        abort oo ->
        not
          (abort_intercepted_expr (spec_binding_inst_var_decls a1 a2 a3 a4)) ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq ext_expr exte (spec_binding_inst_var_decls a1 a2 a3 a4) ->
        @eq out o oo -> P S C a1 a2 a3 a4 oo) ->
       (red_expr S C (spec_binding_inst_var_decls a1 a2 a3 a4) oo ->
        forall (L : env_loc) (S0 : state) (C0 : execution_ctx)
          (bconfig : bool) (str : strictness_flag),
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq env_loc L a1 ->
        @eq (list string) (@nil string) a2 ->
        @eq bool bconfig a3 ->
        @eq strictness_flag str a4 ->
        @eq out (out_void S) oo -> P S C a1 (@nil string) a3 a4 (out_void S)) ->
       (red_expr S C (spec_binding_inst_var_decls a1 a2 a3 a4) oo ->
        forall (o1 : out) (L : env_loc) (S0 : state) 
          (C0 : execution_ctx) (vd : prop_name) (vds : list string)
          (bconfig : bool) (str : strictness_flag) 
          (o : out),
        red_expr S C (spec_env_record_has_binding a1 vd) o1 ->
        red_expr S C (spec_binding_inst_var_decls_1 a1 vd vds a3 a4 o1) oo ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq env_loc L a1 ->
        @eq (list string) (@cons prop_name vd vds) a2 ->
        @eq bool bconfig a3 ->
        @eq strictness_flag str a4 ->
        @eq out o oo -> P S C a1 (@cons prop_name vd vds) a3 a4 oo) ->
       red_expr S C (spec_binding_inst_var_decls a1 a2 a3 a4) oo ->
       P S C a1 a2 a3 a4 oo.

Parameter inv_red_expr_spec_binding_inst_var_decls_1
     : forall (S : state) (C : execution_ctx) (a1 : env_loc) 
         (a2 : string) (a3 : list string) (a4 : bool) 
         (a5 : strictness_flag) (a6 oo : out)
         (P : state ->
              execution_ctx ->
              nat ->
              string -> list string -> bool -> bool -> out -> out -> Prop),
       (red_expr S C (spec_binding_inst_var_decls_1 a1 a2 a3 a4 a5 a6) oo ->
        forall (S0 : state) (C0 : execution_ctx) (exte : ext_expr) (o : out),
        @eq (option out)
          (out_of_ext_expr (spec_binding_inst_var_decls_1 a1 a2 a3 a4 a5 a6))
          (@Some out oo) ->
        abort oo ->
        not
          (abort_intercepted_expr
             (spec_binding_inst_var_decls_1 a1 a2 a3 a4 a5 a6)) ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq ext_expr exte (spec_binding_inst_var_decls_1 a1 a2 a3 a4 a5 a6) ->
        @eq out o oo -> P S C a1 a2 a3 a4 a5 a6 oo) ->
       (red_expr S C (spec_binding_inst_var_decls_1 a1 a2 a3 a4 a5 a6) oo ->
        forall (L : env_loc) (S0 S1 : state) (C0 : execution_ctx)
          (vd : string) (vds : list string) (bconfig : bool)
          (str : strictness_flag) (o : out),
        red_expr S1 C (spec_binding_inst_var_decls a1 a3 a4 a5) oo ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq env_loc L a1 ->
        @eq string vd a2 ->
        @eq (list string) vds a3 ->
        @eq bool bconfig a4 ->
        @eq strictness_flag str a5 ->
        @eq out (out_ter S1 (res_val (value_prim (prim_bool true)))) a6 ->
        @eq out o oo ->
        P S C a1 a2 a3 a4 a5
          (out_ter S1 (res_val (value_prim (prim_bool true)))) oo) ->
       (red_expr S C (spec_binding_inst_var_decls_1 a1 a2 a3 a4 a5 a6) oo ->
        forall (o1 : out) (L : env_loc) (S0 S1 : state) 
          (C0 : execution_ctx) (vd : prop_name) (vds : list string)
          (bconfig : bool) (str : strictness_flag) 
          (o : out),
        red_expr S1 C
          (spec_env_record_create_set_mutable_binding a1 a2 
             (@Some bool a4) (value_prim prim_undef) a5) o1 ->
        red_expr S1 C (spec_binding_inst_var_decls_2 a1 a3 a4 a5 o1) oo ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq env_loc L a1 ->
        @eq string vd a2 ->
        @eq (list string) vds a3 ->
        @eq bool bconfig a4 ->
        @eq strictness_flag str a5 ->
        @eq out (out_ter S1 (res_val (value_prim (prim_bool false)))) a6 ->
        @eq out o oo ->
        P S C a1 a2 a3 a4 a5
          (out_ter S1 (res_val (value_prim (prim_bool false)))) oo) ->
       red_expr S C (spec_binding_inst_var_decls_1 a1 a2 a3 a4 a5 a6) oo ->
       P S C a1 a2 a3 a4 a5 a6 oo.

Parameter inv_red_expr_spec_binding_inst_var_decls_2
     : forall (S : state) (C : execution_ctx) (a1 : env_loc)
         (a2 : list string) (a3 : bool) (a4 : strictness_flag) 
         (a5 oo : out)
         (P : state ->
              execution_ctx ->
              nat -> list string -> bool -> bool -> out -> out -> Prop),
       (red_expr S C (spec_binding_inst_var_decls_2 a1 a2 a3 a4 a5) oo ->
        forall (S0 : state) (C0 : execution_ctx) (exte : ext_expr) (o : out),
        @eq (option out)
          (out_of_ext_expr (spec_binding_inst_var_decls_2 a1 a2 a3 a4 a5))
          (@Some out oo) ->
        abort oo ->
        not
          (abort_intercepted_expr
             (spec_binding_inst_var_decls_2 a1 a2 a3 a4 a5)) ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq ext_expr exte (spec_binding_inst_var_decls_2 a1 a2 a3 a4 a5) ->
        @eq out o oo -> P S C a1 a2 a3 a4 a5 oo) ->
       (red_expr S C (spec_binding_inst_var_decls_2 a1 a2 a3 a4 a5) oo ->
        forall (L : env_loc) (S0 S1 : state) (C0 : execution_ctx)
          (vds : list string) (bconfig : bool) (str : strictness_flag)
          (o : out),
        red_expr S1 C (spec_binding_inst_var_decls a1 a2 a3 a4) oo ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq env_loc L a1 ->
        @eq (list string) vds a2 ->
        @eq bool bconfig a3 ->
        @eq strictness_flag str a4 ->
        @eq out (out_void S1) a5 ->
        @eq out o oo -> P S C a1 a2 a3 a4 (out_void S1) oo) ->
       red_expr S C (spec_binding_inst_var_decls_2 a1 a2 a3 a4 a5) oo ->
       P S C a1 a2 a3 a4 a5 oo.

Parameter inv_red_expr_spec_binding_inst
     : forall (S : state) (C : execution_ctx) (a1 : codetype)
         (a2 : option object_loc) (a3 : prog) (a4 : list value) 
         (oo : out)
         (P : state ->
              execution_ctx ->
              codetype ->
              option object_loc -> prog -> list value -> out -> Prop),
       (red_expr S C (spec_binding_inst a1 a2 a3 a4) oo ->
        forall (S0 : state) (C0 : execution_ctx) (exte : ext_expr) (o : out),
        @eq (option out) (out_of_ext_expr (spec_binding_inst a1 a2 a3 a4))
          (@Some out oo) ->
        abort oo ->
        not (abort_intercepted_expr (spec_binding_inst a1 a2 a3 a4)) ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq ext_expr exte (spec_binding_inst a1 a2 a3 a4) ->
        @eq out o oo -> P S C a1 a2 a3 a4 oo) ->
       (red_expr S C (spec_binding_inst a1 a2 a3 a4) oo ->
        forall (L : env_loc) (Ls : list env_loc) (S0 : state)
          (C0 : execution_ctx) (ct : codetype) (olf : option object_loc)
          (code : prog) (args : list value) (o : out),
        @eq lexical_env (execution_ctx_variable_env C) (@cons env_loc L Ls) ->
        red_expr S C (spec_binding_inst_1 a1 a2 a3 a4 L) oo ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq codetype ct a1 ->
        @eq (option object_loc) olf a2 ->
        @eq prog code a3 ->
        @eq (list value) args a4 -> @eq out o oo -> P S C a1 a2 a3 a4 oo) ->
       red_expr S C (spec_binding_inst a1 a2 a3 a4) oo ->
       P S C a1 a2 a3 a4 oo.

Parameter inv_red_expr_spec_binding_inst_1
     : forall (S : state) (C : execution_ctx) (a1 : codetype)
         (a2 : option object_loc) (a3 : prog) (a4 : list value)
         (a5 : env_loc) (oo : out)
         (P : state ->
              execution_ctx ->
              codetype ->
              option object_loc -> prog -> list value -> nat -> out -> Prop),
       (red_expr S C (spec_binding_inst_1 a1 a2 a3 a4 a5) oo ->
        forall (S0 : state) (C0 : execution_ctx) (exte : ext_expr) (o : out),
        @eq (option out)
          (out_of_ext_expr (spec_binding_inst_1 a1 a2 a3 a4 a5))
          (@Some out oo) ->
        abort oo ->
        not (abort_intercepted_expr (spec_binding_inst_1 a1 a2 a3 a4 a5)) ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq ext_expr exte (spec_binding_inst_1 a1 a2 a3 a4 a5) ->
        @eq out o oo -> P S C a1 a2 a3 a4 a5 oo) ->
       (red_expr S C (spec_binding_inst_1 a1 a2 a3 a4 a5) oo ->
        forall (o1 : out) (xs : list prop_name) (S0 : state)
          (C0 : execution_ctx) (lf : object_loc) (code : prog)
          (args : list value) (L : env_loc) (o : out),
        @object_method (option (list string)) object_formal_parameters_ S lf
          (@Some (list prop_name) xs) ->
        red_expr S C
          (spec_binding_inst_formal_params a4 a5 xs
             (prog_intro_strictness a3)) o1 ->
        red_expr S C (spec_binding_inst_2 codetype_func lf a3 xs a4 a5 o1) oo ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq codetype codetype_func a1 ->
        @eq (option object_loc) (@Some object_loc lf) a2 ->
        @eq prog code a3 ->
        @eq (list value) args a4 ->
        @eq env_loc L a5 ->
        @eq out o oo -> P S C codetype_func (@Some object_loc lf) a3 a4 a5 oo) ->
       (red_expr S C (spec_binding_inst_1 a1 a2 a3 a4 a5) oo ->
        forall (L : env_loc) (S0 : state) (C0 : execution_ctx)
          (ct : codetype) (code : prog) (args : list value) 
          (o : out),
        not (@eq codetype a1 codetype_func) ->
        red_expr S C
          (spec_binding_inst_3 a1 (@None object_loc) a3 (@nil string) a4 a5)
          oo ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq codetype ct a1 ->
        @eq (option object_loc) (@None object_loc) a2 ->
        @eq prog code a3 ->
        @eq (list value) args a4 ->
        @eq env_loc L a5 ->
        @eq out o oo -> P S C a1 (@None object_loc) a3 a4 a5 oo) ->
       red_expr S C (spec_binding_inst_1 a1 a2 a3 a4 a5) oo ->
       P S C a1 a2 a3 a4 a5 oo.

Parameter inv_red_expr_spec_binding_inst_2
     : forall (S : state) (C : execution_ctx) (a1 : codetype)
         (a2 : object_loc) (a3 : prog) (a4 : list string) 
         (a5 : list value) (a6 : env_loc) (a7 oo : out)
         (P : state ->
              execution_ctx ->
              codetype ->
              object_loc ->
              prog -> list string -> list value -> nat -> out -> out -> Prop),
       (red_expr S C (spec_binding_inst_2 a1 a2 a3 a4 a5 a6 a7) oo ->
        forall (S0 : state) (C0 : execution_ctx) (exte : ext_expr) (o : out),
        @eq (option out)
          (out_of_ext_expr (spec_binding_inst_2 a1 a2 a3 a4 a5 a6 a7))
          (@Some out oo) ->
        abort oo ->
        not
          (abort_intercepted_expr (spec_binding_inst_2 a1 a2 a3 a4 a5 a6 a7)) ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq ext_expr exte (spec_binding_inst_2 a1 a2 a3 a4 a5 a6 a7) ->
        @eq out o oo -> P S C a1 a2 a3 a4 a5 a6 a7 oo) ->
       (red_expr S C (spec_binding_inst_2 a1 a2 a3 a4 a5 a6 a7) oo ->
        forall (S0 : state) (xs : list prop_name) (S1 : state)
          (C0 : execution_ctx) (lf : object_loc) (code : prog)
          (args : list value) (L : env_loc) (o : out),
        red_expr S1 C
          (spec_binding_inst_3 codetype_func (@Some object_loc a2) a3 a4 a5
             a6) oo ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq codetype codetype_func a1 ->
        @eq object_loc lf a2 ->
        @eq prog code a3 ->
        @eq (list string) xs a4 ->
        @eq (list value) args a5 ->
        @eq env_loc L a6 ->
        @eq out (out_void S1) a7 ->
        @eq out o oo -> P S C codetype_func a2 a3 a4 a5 a6 (out_void S1) oo) ->
       red_expr S C (spec_binding_inst_2 a1 a2 a3 a4 a5 a6 a7) oo ->
       P S C a1 a2 a3 a4 a5 a6 a7 oo.

Parameter inv_red_expr_spec_binding_inst_3
     : forall (S : state) (C : execution_ctx) (a1 : codetype)
         (a2 : option object_loc) (a3 : prog) (a4 : list string)
         (a5 : list value) (a6 : env_loc) (oo : out)
         (P : state ->
              execution_ctx ->
              codetype ->
              option object_loc ->
              prog -> list string -> list value -> nat -> out -> Prop),
       (red_expr S C (spec_binding_inst_3 a1 a2 a3 a4 a5 a6) oo ->
        forall (S0 : state) (C0 : execution_ctx) (exte : ext_expr) (o : out),
        @eq (option out)
          (out_of_ext_expr (spec_binding_inst_3 a1 a2 a3 a4 a5 a6))
          (@Some out oo) ->
        abort oo ->
        not (abort_intercepted_expr (spec_binding_inst_3 a1 a2 a3 a4 a5 a6)) ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq ext_expr exte (spec_binding_inst_3 a1 a2 a3 a4 a5 a6) ->
        @eq out o oo -> P S C a1 a2 a3 a4 a5 a6 oo) ->
       (red_expr S C (spec_binding_inst_3 a1 a2 a3 a4 a5 a6) oo ->
        forall (bconfig : bool) (L : env_loc) (S0 : state)
          (C0 : execution_ctx) (ct : codetype) (olf : option object_loc)
          (code : prog) (fds : list funcdecl) (xs : list prop_name)
          (args : list value) (o1 o : out),
        @eq bool bconfig
          match classicT (@eq codetype a1 codetype_eval) return bool with
          | left _ => true
          | right _ => false
          end ->
        @eq (list funcdecl) fds (prog_funcdecl a3) ->
        red_expr S C
          (spec_binding_inst_function_decls a6 fds 
             (prog_intro_strictness a3) bconfig) o1 ->
        red_expr S C (spec_binding_inst_4 a1 a2 a3 a4 a5 bconfig a6 o1) oo ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq codetype ct a1 ->
        @eq (option object_loc) olf a2 ->
        @eq prog code a3 ->
        @eq (list string) xs a4 ->
        @eq (list value) args a5 ->
        @eq env_loc L a6 -> @eq out o oo -> P S C a1 a2 a3 a4 a5 a6 oo) ->
       red_expr S C (spec_binding_inst_3 a1 a2 a3 a4 a5 a6) oo ->
       P S C a1 a2 a3 a4 a5 a6 oo.

Parameter inv_red_expr_spec_binding_inst_4
     : forall (S : state) (C : execution_ctx) (a1 : codetype)
         (a2 : option object_loc) (a3 : prog) (a4 : list string)
         (a5 : list value) (a6 : bool) (a7 : env_loc) 
         (a8 oo : out)
         (P : state ->
              execution_ctx ->
              codetype ->
              option object_loc ->
              prog ->
              list string -> list value -> bool -> nat -> out -> out -> Prop),
       (red_expr S C (spec_binding_inst_4 a1 a2 a3 a4 a5 a6 a7 a8) oo ->
        forall (S0 : state) (C0 : execution_ctx) (exte : ext_expr) (o : out),
        @eq (option out)
          (out_of_ext_expr (spec_binding_inst_4 a1 a2 a3 a4 a5 a6 a7 a8))
          (@Some out oo) ->
        abort oo ->
        not
          (abort_intercepted_expr
             (spec_binding_inst_4 a1 a2 a3 a4 a5 a6 a7 a8)) ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq ext_expr exte (spec_binding_inst_4 a1 a2 a3 a4 a5 a6 a7 a8) ->
        @eq out o oo -> P S C a1 a2 a3 a4 a5 a6 a7 a8 oo) ->
       (red_expr S C (spec_binding_inst_4 a1 a2 a3 a4 a5 a6 a7 a8) oo ->
        forall (bconfig : bool) (L : env_loc) (S0 S1 : state)
          (C0 : execution_ctx) (ct : codetype) (olf : option object_loc)
          (code : prog) (xs : list prop_name) (args : list value) 
          (o : out),
        red_expr S1 C (spec_binding_inst_5 a1 a2 a3 a4 a5 a6 a7) oo ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq codetype ct a1 ->
        @eq (option object_loc) olf a2 ->
        @eq prog code a3 ->
        @eq (list string) xs a4 ->
        @eq (list value) args a5 ->
        @eq bool bconfig a6 ->
        @eq env_loc L a7 ->
        @eq out (out_void S1) a8 ->
        @eq out o oo -> P S C a1 a2 a3 a4 a5 a6 a7 (out_void S1) oo) ->
       red_expr S C (spec_binding_inst_4 a1 a2 a3 a4 a5 a6 a7 a8) oo ->
       P S C a1 a2 a3 a4 a5 a6 a7 a8 oo.

Parameter inv_red_expr_spec_binding_inst_5
     : forall (S : state) (C : execution_ctx) (a1 : codetype)
         (a2 : option object_loc) (a3 : prog) (a4 : list string)
         (a5 : list value) (a6 : bool) (a7 : env_loc) 
         (oo : out)
         (P : state ->
              execution_ctx ->
              codetype ->
              option object_loc ->
              prog -> list string -> list value -> bool -> nat -> out -> Prop),
       (red_expr S C (spec_binding_inst_5 a1 a2 a3 a4 a5 a6 a7) oo ->
        forall (S0 : state) (C0 : execution_ctx) (exte : ext_expr) (o : out),
        @eq (option out)
          (out_of_ext_expr (spec_binding_inst_5 a1 a2 a3 a4 a5 a6 a7))
          (@Some out oo) ->
        abort oo ->
        not
          (abort_intercepted_expr (spec_binding_inst_5 a1 a2 a3 a4 a5 a6 a7)) ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq ext_expr exte (spec_binding_inst_5 a1 a2 a3 a4 a5 a6 a7) ->
        @eq out o oo -> P S C a1 a2 a3 a4 a5 a6 a7 oo) ->
       (red_expr S C (spec_binding_inst_5 a1 a2 a3 a4 a5 a6 a7) oo ->
        forall (o1 : out) (L : env_loc) (S0 : state) 
          (C0 : execution_ctx) (ct : codetype) (olf : option object_loc)
          (code : prog) (xs : list prop_name) (args : list value)
          (bconfig : bool) (o : out),
        red_expr S C
          (spec_env_record_has_binding a7
             (String (Ascii true false false false false true true false)
                (String (Ascii false true false false true true true false)
                   (String (Ascii true true true false false true true false)
                      (String
                         (Ascii true false true false true true true false)
                         (String
                            (Ascii true false true true false true true false)
                            (String
                               (Ascii true false true false false true true
                                  false)
                               (String
                                  (Ascii false true true true false true true
                                     false)
                                  (String
                                     (Ascii false false true false true true
                                        true false)
                                     (String
                                        (Ascii true true false false true
                                           true true false) EmptyString))))))))))
          o1 ->
        red_expr S C (spec_binding_inst_6 a1 a2 a3 a4 a5 a6 a7 o1) oo ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq codetype ct a1 ->
        @eq (option object_loc) olf a2 ->
        @eq prog code a3 ->
        @eq (list string) xs a4 ->
        @eq (list value) args a5 ->
        @eq bool bconfig a6 ->
        @eq env_loc L a7 -> @eq out o oo -> P S C a1 a2 a3 a4 a5 a6 a7 oo) ->
       red_expr S C (spec_binding_inst_5 a1 a2 a3 a4 a5 a6 a7) oo ->
       P S C a1 a2 a3 a4 a5 a6 a7 oo.

Parameter inv_red_expr_spec_binding_inst_6
     : forall (S : state) (C : execution_ctx) (a1 : codetype)
         (a2 : option object_loc) (a3 : prog) (a4 : list string)
         (a5 : list value) (a6 : bool) (a7 : env_loc) 
         (a8 oo : out)
         (P : state ->
              execution_ctx ->
              codetype ->
              option object_loc ->
              prog ->
              list string -> list value -> bool -> nat -> out -> out -> Prop),
       (red_expr S C (spec_binding_inst_6 a1 a2 a3 a4 a5 a6 a7 a8) oo ->
        forall (S0 : state) (C0 : execution_ctx) (exte : ext_expr) (o : out),
        @eq (option out)
          (out_of_ext_expr (spec_binding_inst_6 a1 a2 a3 a4 a5 a6 a7 a8))
          (@Some out oo) ->
        abort oo ->
        not
          (abort_intercepted_expr
             (spec_binding_inst_6 a1 a2 a3 a4 a5 a6 a7 a8)) ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq ext_expr exte (spec_binding_inst_6 a1 a2 a3 a4 a5 a6 a7 a8) ->
        @eq out o oo -> P S C a1 a2 a3 a4 a5 a6 a7 a8 oo) ->
       (red_expr S C (spec_binding_inst_6 a1 a2 a3 a4 a5 a6 a7 a8) oo ->
        forall (o1 : out) (L : env_loc) (S0 S1 : state) 
          (C0 : execution_ctx) (lf : object_loc) (code : prog)
          (xs : list prop_name) (args : list value) 
          (bconfig : bool) (o : out),
        red_expr S1 C
          (spec_binding_inst_arg_obj lf a4 a5 a7 (prog_intro_strictness a3))
          o1 ->
        red_expr S1 C (spec_binding_inst_7 a3 a6 a7 o1) oo ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq codetype codetype_func a1 ->
        @eq (option object_loc) (@Some object_loc lf) a2 ->
        @eq prog code a3 ->
        @eq (list string) xs a4 ->
        @eq (list value) args a5 ->
        @eq bool bconfig a6 ->
        @eq env_loc L a7 ->
        @eq out (out_ter S1 (res_val (value_prim (prim_bool false)))) a8 ->
        @eq out o oo ->
        P S C codetype_func (@Some object_loc lf) a3 a4 a5 a6 a7
          (out_ter S1 (res_val (value_prim (prim_bool false)))) oo) ->
       (red_expr S C (spec_binding_inst_6 a1 a2 a3 a4 a5 a6 a7 a8) oo ->
        forall (L : env_loc) (S0 S1 : state) (C0 : execution_ctx)
          (ct : codetype) (olf : option object_loc) 
          (code : prog) (xs : list prop_name) (args : list value)
          (bconfig bdefined : bool) (o : out),
        not
          (Logic.and (@eq codetype a1 codetype_func)
             (@eq bool bdefined false)) ->
        red_expr S1 C (spec_binding_inst_8 a3 a6 a7) oo ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq codetype ct a1 ->
        @eq (option object_loc) olf a2 ->
        @eq prog code a3 ->
        @eq (list string) xs a4 ->
        @eq (list value) args a5 ->
        @eq bool bconfig a6 ->
        @eq env_loc L a7 ->
        @eq out (out_ter S1 (res_val (value_prim (prim_bool bdefined)))) a8 ->
        @eq out o oo ->
        P S C a1 a2 a3 a4 a5 a6 a7
          (out_ter S1 (res_val (value_prim (prim_bool bdefined)))) oo) ->
       red_expr S C (spec_binding_inst_6 a1 a2 a3 a4 a5 a6 a7 a8) oo ->
       P S C a1 a2 a3 a4 a5 a6 a7 a8 oo.

Parameter inv_red_expr_spec_binding_inst_7
     : forall (S : state) (C : execution_ctx) (a1 : prog) 
         (a2 : bool) (a3 : env_loc) (a4 oo : out)
         (P : state ->
              execution_ctx -> prog -> bool -> nat -> out -> out -> Prop),
       (red_expr S C (spec_binding_inst_7 a1 a2 a3 a4) oo ->
        forall (S0 : state) (C0 : execution_ctx) (exte : ext_expr) (o : out),
        @eq (option out) (out_of_ext_expr (spec_binding_inst_7 a1 a2 a3 a4))
          (@Some out oo) ->
        abort oo ->
        not (abort_intercepted_expr (spec_binding_inst_7 a1 a2 a3 a4)) ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq ext_expr exte (spec_binding_inst_7 a1 a2 a3 a4) ->
        @eq out o oo -> P S C a1 a2 a3 a4 oo) ->
       (red_expr S C (spec_binding_inst_7 a1 a2 a3 a4) oo ->
        forall (S0 S1 : state) (C0 : execution_ctx) 
          (code : prog) (bconfig : bool) (L : env_loc) 
          (o : out),
        red_expr S1 C (spec_binding_inst_8 a1 a2 a3) oo ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq prog code a1 ->
        @eq bool bconfig a2 ->
        @eq env_loc L a3 ->
        @eq out (out_void S1) a4 ->
        @eq out o oo -> P S C a1 a2 a3 (out_void S1) oo) ->
       red_expr S C (spec_binding_inst_7 a1 a2 a3 a4) oo ->
       P S C a1 a2 a3 a4 oo.

Parameter inv_red_expr_spec_binding_inst_8
     : forall (S : state) (C : execution_ctx) (a1 : prog) 
         (a2 : bool) (a3 : env_loc) (oo : out)
         (P : state -> execution_ctx -> prog -> bool -> nat -> out -> Prop),
       (red_expr S C (spec_binding_inst_8 a1 a2 a3) oo ->
        forall (S0 : state) (C0 : execution_ctx) (exte : ext_expr) (o : out),
        @eq (option out) (out_of_ext_expr (spec_binding_inst_8 a1 a2 a3))
          (@Some out oo) ->
        abort oo ->
        not (abort_intercepted_expr (spec_binding_inst_8 a1 a2 a3)) ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq ext_expr exte (spec_binding_inst_8 a1 a2 a3) ->
        @eq out o oo -> P S C a1 a2 a3 oo) ->
       (red_expr S C (spec_binding_inst_8 a1 a2 a3) oo ->
        forall (S0 : state) (L : env_loc) (S1 : state) 
          (C0 : execution_ctx) (code : prog) (bconfig : bool) 
          (o : out),
        red_expr S1 C
          (spec_binding_inst_var_decls a3 (prog_vardecl a1) a2
             (prog_intro_strictness a1)) oo ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq prog code a1 ->
        @eq bool bconfig a2 ->
        @eq env_loc L a3 -> @eq out o oo -> P S C a1 a2 a3 oo) ->
       red_expr S C (spec_binding_inst_8 a1 a2 a3) oo -> P S C a1 a2 a3 oo.

Parameter inv_red_expr_spec_make_arg_getter
     : forall (S : state) (C : execution_ctx) (a1 : string)
         (a2 : lexical_env) (oo : out)
         (P : state -> execution_ctx -> string -> list nat -> out -> Prop),
       (red_expr S C (spec_make_arg_getter a1 a2) oo ->
        forall (S0 : state) (C0 : execution_ctx) (exte : ext_expr) (o : out),
        @eq (option out) (out_of_ext_expr (spec_make_arg_getter a1 a2))
          (@Some out oo) ->
        abort oo ->
        not (abort_intercepted_expr (spec_make_arg_getter a1 a2)) ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq ext_expr exte (spec_make_arg_getter a1 a2) ->
        @eq out o oo -> P S C a1 a2 oo) ->
       (red_expr S C (spec_make_arg_getter a1 a2) oo ->
        forall (xbd : string) (bd : funcbody) (S0 : state)
          (C0 : execution_ctx) (x : prop_name) (X : lexical_env) 
          (o : out),
        @eq string xbd
          (String.append
             (String (Ascii false true false false true true true false)
                (String (Ascii true false true false false true true false)
                   (String
                      (Ascii false false true false true true true false)
                      (String
                         (Ascii true false true false true true true false)
                         (String
                            (Ascii false true false false true true true
                               false)
                            (String
                               (Ascii false true true true false true true
                                  false)
                               (String
                                  (Ascii false false false false false true
                                     false false) EmptyString)))))))
             (String.append a1
                (String (Ascii true true false true true true false false)
                   EmptyString))) ->
        @eq funcbody bd
          (funcbody_intro
             (prog_intro true
                (@cons element
                   (element_stat
                      (stat_return (@Some expr (expr_identifier a1))))
                   (@nil element))) xbd) ->
        red_expr S C (spec_creating_function_object (@nil string) bd a2 true)
          oo ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq string x a1 ->
        @eq lexical_env X a2 -> @eq out o oo -> P S C a1 a2 oo) ->
       red_expr S C (spec_make_arg_getter a1 a2) oo -> P S C a1 a2 oo.

Parameter inv_red_expr_spec_make_arg_setter
     : forall (S : state) (C : execution_ctx) (a1 : string)
         (a2 : lexical_env) (oo : out)
         (P : state -> execution_ctx -> string -> list nat -> out -> Prop),
       (red_expr S C (spec_make_arg_setter a1 a2) oo ->
        forall (S0 : state) (C0 : execution_ctx) (exte : ext_expr) (o : out),
        @eq (option out) (out_of_ext_expr (spec_make_arg_setter a1 a2))
          (@Some out oo) ->
        abort oo ->
        not (abort_intercepted_expr (spec_make_arg_setter a1 a2)) ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq ext_expr exte (spec_make_arg_setter a1 a2) ->
        @eq out o oo -> P S C a1 a2 oo) ->
       (red_expr S C (spec_make_arg_setter a1 a2) oo ->
        forall (xparam xbd : string) (bd : funcbody) 
          (S0 : state) (C0 : execution_ctx) (x : prop_name) 
          (X : lexical_env) (o : out),
        @eq string xparam
          (String.append a1
             (String (Ascii true true true true true false true false)
                (String (Ascii true false false false false true true false)
                   (String
                      (Ascii false true false false true true true false)
                      (String
                         (Ascii true true true false false true true false)
                         EmptyString))))) ->
        @eq string xbd
          (String.append a1
             (String.append
                (String
                   (Ascii false false false false false true false false)
                   (String (Ascii true false true true true true false false)
                      (String
                         (Ascii false false false false false true false
                            false) EmptyString)))
                (String.append xparam
                   (String (Ascii true true false true true true false false)
                      EmptyString)))) ->
        @eq funcbody bd
          (funcbody_intro
             (prog_intro true
                (@cons element
                   (element_stat
                      (stat_expr
                         (expr_assign (expr_identifier a1) 
                            (@None binary_op) (expr_identifier xparam))))
                   (@nil element))) xbd) ->
        red_expr S C
          (spec_creating_function_object (@cons string xparam (@nil string))
             bd a2 true) oo ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq string x a1 ->
        @eq lexical_env X a2 -> @eq out o oo -> P S C a1 a2 oo) ->
       red_expr S C (spec_make_arg_setter a1 a2) oo -> P S C a1 a2 oo.

Parameter inv_red_expr_spec_args_obj_get_1
     : forall (S : state) (C : execution_ctx) (a1 : value) 
         (a2 : object_loc) (a3 : prop_name) (a4 : object_loc)
         (a5 : specret full_descriptor) (oo : out)
         (P : state ->
              execution_ctx ->
              value ->
              object_loc ->
              string -> object_loc -> specret full_descriptor -> out -> Prop),
       (red_expr S C (spec_args_obj_get_1 a1 a2 a3 a4 a5) oo ->
        forall (S0 : state) (C0 : execution_ctx) (exte : ext_expr) (o : out),
        @eq (option out)
          (out_of_ext_expr (spec_args_obj_get_1 a1 a2 a3 a4 a5))
          (@Some out oo) ->
        abort oo ->
        not (abort_intercepted_expr (spec_args_obj_get_1 a1 a2 a3 a4 a5)) ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq ext_expr exte (spec_args_obj_get_1 a1 a2 a3 a4 a5) ->
        @eq out o oo -> P S C a1 a2 a3 a4 a5 oo) ->
       (red_expr S C (spec_args_obj_get_1 a1 a2 a3 a4 a5) oo ->
        forall (S0 S1 : state) (C0 : execution_ctx) 
          (vthis : value) (l : object_loc) (x : prop_name)
          (lmap : object_loc) (o : out),
        red_expr S0 C (spec_object_get_1 builtin_get_function a1 a2 a3) oo ->
        @eq state S1 S ->
        @eq execution_ctx C0 C ->
        @eq value vthis a1 ->
        @eq object_loc l a2 ->
        @eq prop_name x a3 ->
        @eq object_loc lmap a4 ->
        @eq (specret full_descriptor)
          (@ret full_descriptor S0 full_descriptor_undef) a5 ->
        @eq out o oo ->
        P S C a1 a2 a3 a4 (@ret full_descriptor S0 full_descriptor_undef) oo) ->
       (red_expr S C (spec_args_obj_get_1 a1 a2 a3 a4 a5) oo ->
        forall (S0 S1 : state) (C0 : execution_ctx) 
          (vthis : value) (l : object_loc) (x : prop_name)
          (lmap : object_loc) (A : attributes) (o : out),
        red_expr S0 C (spec_object_get a4 a3) oo ->
        @eq state S1 S ->
        @eq execution_ctx C0 C ->
        @eq value vthis a1 ->
        @eq object_loc l a2 ->
        @eq prop_name x a3 ->
        @eq object_loc lmap a4 ->
        @eq (specret full_descriptor)
          (@ret full_descriptor S0 (full_descriptor_some A)) a5 ->
        @eq out o oo ->
        P S C a1 a2 a3 a4 (@ret full_descriptor S0 (full_descriptor_some A))
          oo) ->
       red_expr S C (spec_args_obj_get_1 a1 a2 a3 a4 a5) oo ->
       P S C a1 a2 a3 a4 a5 oo.

Parameter inv_red_expr_spec_args_obj_define_own_prop_1
     : forall (S : state) (C : execution_ctx) (a1 : object_loc)
         (a2 : prop_name) (a3 : descriptor) (a4 : bool) 
         (a5 : object_loc) (a6 : specret full_descriptor) 
         (oo : out)
         (P : state ->
              execution_ctx ->
              object_loc ->
              string ->
              descriptor ->
              bool -> object_loc -> specret full_descriptor -> out -> Prop),
       (red_expr S C (spec_args_obj_define_own_prop_1 a1 a2 a3 a4 a5 a6) oo ->
        forall (S0 : state) (C0 : execution_ctx) (exte : ext_expr) (o : out),
        @eq (option out)
          (out_of_ext_expr
             (spec_args_obj_define_own_prop_1 a1 a2 a3 a4 a5 a6))
          (@Some out oo) ->
        abort oo ->
        not
          (abort_intercepted_expr
             (spec_args_obj_define_own_prop_1 a1 a2 a3 a4 a5 a6)) ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq ext_expr exte (spec_args_obj_define_own_prop_1 a1 a2 a3 a4 a5 a6) ->
        @eq out o oo -> P S C a1 a2 a3 a4 a5 a6 oo) ->
       (red_expr S C (spec_args_obj_define_own_prop_1 a1 a2 a3 a4 a5 a6) oo ->
        forall (o1 : out) (S0 S1 : state) (C0 : execution_ctx)
          (l : object_loc) (x : prop_name) (Desc : descriptor) 
          (throw : bool) (lmap : object_loc) (Dmap : full_descriptor)
          (o : out),
        red_expr S0 C
          (spec_object_define_own_prop_1 builtin_define_own_prop_default a1
             a2 a3 false) o1 ->
        red_expr S0 C
          (spec_args_obj_define_own_prop_2 a1 a2 a3 a4 a5 Dmap o1) oo ->
        @eq state S1 S ->
        @eq execution_ctx C0 C ->
        @eq object_loc l a1 ->
        @eq prop_name x a2 ->
        @eq descriptor Desc a3 ->
        @eq bool throw a4 ->
        @eq object_loc lmap a5 ->
        @eq (specret full_descriptor) (@ret full_descriptor S0 Dmap) a6 ->
        @eq out o oo ->
        P S C a1 a2 a3 a4 a5 (@ret full_descriptor S0 Dmap) oo) ->
       red_expr S C (spec_args_obj_define_own_prop_1 a1 a2 a3 a4 a5 a6) oo ->
       P S C a1 a2 a3 a4 a5 a6 oo.

Parameter inv_red_expr_spec_args_obj_define_own_prop_2
     : forall (S : state) (C : execution_ctx) (a1 : object_loc)
         (a2 : prop_name) (a3 : descriptor) (a4 : bool) 
         (a5 : object_loc) (a6 : full_descriptor) (a7 oo : out)
         (P : state ->
              execution_ctx ->
              object_loc ->
              string ->
              descriptor ->
              bool -> object_loc -> full_descriptor -> out -> out -> Prop),
       (red_expr S C (spec_args_obj_define_own_prop_2 a1 a2 a3 a4 a5 a6 a7)
          oo ->
        forall (S0 : state) (C0 : execution_ctx) (exte : ext_expr) (o : out),
        @eq (option out)
          (out_of_ext_expr
             (spec_args_obj_define_own_prop_2 a1 a2 a3 a4 a5 a6 a7))
          (@Some out oo) ->
        abort oo ->
        not
          (abort_intercepted_expr
             (spec_args_obj_define_own_prop_2 a1 a2 a3 a4 a5 a6 a7)) ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq ext_expr exte
          (spec_args_obj_define_own_prop_2 a1 a2 a3 a4 a5 a6 a7) ->
        @eq out o oo -> P S C a1 a2 a3 a4 a5 a6 a7 oo) ->
       (red_expr S C (spec_args_obj_define_own_prop_2 a1 a2 a3 a4 a5 a6 a7)
          oo ->
        forall (S0 : state) (C0 : execution_ctx) (l : object_loc)
          (x : prop_name) (Desc : descriptor) (throw : bool)
          (lmap : object_loc) (Dmap : full_descriptor) 
          (S' : state) (o : out),
        red_expr S' C (spec_object_define_own_prop_reject a4) oo ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq object_loc l a1 ->
        @eq prop_name x a2 ->
        @eq descriptor Desc a3 ->
        @eq bool throw a4 ->
        @eq object_loc lmap a5 ->
        @eq full_descriptor Dmap a6 ->
        @eq out (out_ter S' (res_val (value_prim (prim_bool false)))) a7 ->
        @eq out o oo ->
        P S C a1 a2 a3 a4 a5 a6
          (out_ter S' (res_val (value_prim (prim_bool false)))) oo) ->
       (red_expr S C (spec_args_obj_define_own_prop_2 a1 a2 a3 a4 a5 a6 a7)
          oo ->
        forall (o1 : out) (S0 : state) (C0 : execution_ctx) 
          (l : object_loc) (x : prop_name) (Desc : descriptor) 
          (throw : bool) (lmap : object_loc) (A : attributes) 
          (S' : state) (o : out),
        descriptor_is_accessor a3 ->
        red_expr S' C (spec_object_delete a5 a2 false) o1 ->
        red_expr S' C (spec_args_obj_define_own_prop_5 o1) oo ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq object_loc l a1 ->
        @eq prop_name x a2 ->
        @eq descriptor Desc a3 ->
        @eq bool throw a4 ->
        @eq object_loc lmap a5 ->
        @eq full_descriptor (full_descriptor_some A) a6 ->
        @eq out (out_ter S' (res_val (value_prim (prim_bool true)))) a7 ->
        @eq out o oo ->
        P S C a1 a2 a3 a4 a5 (full_descriptor_some A)
          (out_ter S' (res_val (value_prim (prim_bool true)))) oo) ->
       (red_expr S C (spec_args_obj_define_own_prop_2 a1 a2 a3 a4 a5 a6 a7)
          oo ->
        forall (v : value) (o1 : out) (S0 : state) 
          (C0 : execution_ctx) (l : object_loc) (x : prop_name)
          (Desc : descriptor) (throw : bool) (lmap : object_loc)
          (A : attributes) (S' : state) (o : out),
        not (descriptor_is_accessor a3) ->
        @eq (option value) (descriptor_value a3) (@Some value v) ->
        red_expr S' C (spec_object_put a5 a2 v a4) o1 ->
        red_expr S' C (spec_args_obj_define_own_prop_3 a1 a2 a3 a4 a5 o1) oo ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq object_loc l a1 ->
        @eq prop_name x a2 ->
        @eq descriptor Desc a3 ->
        @eq bool throw a4 ->
        @eq object_loc lmap a5 ->
        @eq full_descriptor (full_descriptor_some A) a6 ->
        @eq out (out_ter S' (res_val (value_prim (prim_bool true)))) a7 ->
        @eq out o oo ->
        P S C a1 a2 a3 a4 a5 (full_descriptor_some A)
          (out_ter S' (res_val (value_prim (prim_bool true)))) oo) ->
       (red_expr S C (spec_args_obj_define_own_prop_2 a1 a2 a3 a4 a5 a6 a7)
          oo ->
        forall (S0 : state) (C0 : execution_ctx) (l : object_loc)
          (x : prop_name) (Desc : descriptor) (throw : bool)
          (lmap : object_loc) (A : attributes) (S' : state) 
          (o : out),
        not (descriptor_is_accessor a3) ->
        @eq (option value) (descriptor_value a3) (@None value) ->
        red_expr S' C (spec_args_obj_define_own_prop_4 a1 a2 a3 a4 a5) oo ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq object_loc l a1 ->
        @eq prop_name x a2 ->
        @eq descriptor Desc a3 ->
        @eq bool throw a4 ->
        @eq object_loc lmap a5 ->
        @eq full_descriptor (full_descriptor_some A) a6 ->
        @eq out (out_ter S' (res_val (value_prim (prim_bool true)))) a7 ->
        @eq out o oo ->
        P S C a1 a2 a3 a4 a5 (full_descriptor_some A)
          (out_ter S' (res_val (value_prim (prim_bool true)))) oo) ->
       (red_expr S C (spec_args_obj_define_own_prop_2 a1 a2 a3 a4 a5 a6 a7)
          oo ->
        forall (S0 : state) (C0 : execution_ctx) (l : object_loc)
          (x : prop_name) (Desc : descriptor) (throw : bool)
          (lmap : object_loc) (S' : state) (o : out),
        red_expr S' C spec_args_obj_define_own_prop_6 oo ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq object_loc l a1 ->
        @eq prop_name x a2 ->
        @eq descriptor Desc a3 ->
        @eq bool throw a4 ->
        @eq object_loc lmap a5 ->
        @eq full_descriptor full_descriptor_undef a6 ->
        @eq out (out_ter S' (res_val (value_prim (prim_bool true)))) a7 ->
        @eq out o oo ->
        P S C a1 a2 a3 a4 a5 full_descriptor_undef
          (out_ter S' (res_val (value_prim (prim_bool true)))) oo) ->
       red_expr S C (spec_args_obj_define_own_prop_2 a1 a2 a3 a4 a5 a6 a7) oo ->
       P S C a1 a2 a3 a4 a5 a6 a7 oo.

Parameter inv_red_expr_spec_args_obj_define_own_prop_3
     : forall (S : state) (C : execution_ctx) (a1 : object_loc)
         (a2 : prop_name) (a3 : descriptor) (a4 : bool) 
         (a5 : object_loc) (a6 oo : out)
         (P : state ->
              execution_ctx ->
              object_loc ->
              string ->
              descriptor -> bool -> object_loc -> out -> out -> Prop),
       (red_expr S C (spec_args_obj_define_own_prop_3 a1 a2 a3 a4 a5 a6) oo ->
        forall (S0 : state) (C0 : execution_ctx) (exte : ext_expr) (o : out),
        @eq (option out)
          (out_of_ext_expr
             (spec_args_obj_define_own_prop_3 a1 a2 a3 a4 a5 a6))
          (@Some out oo) ->
        abort oo ->
        not
          (abort_intercepted_expr
             (spec_args_obj_define_own_prop_3 a1 a2 a3 a4 a5 a6)) ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq ext_expr exte (spec_args_obj_define_own_prop_3 a1 a2 a3 a4 a5 a6) ->
        @eq out o oo -> P S C a1 a2 a3 a4 a5 a6 oo) ->
       (red_expr S C (spec_args_obj_define_own_prop_3 a1 a2 a3 a4 a5 a6) oo ->
        forall (S0 : state) (C0 : execution_ctx) (l : object_loc)
          (x : prop_name) (Desc : descriptor) (throw : bool)
          (lmap : object_loc) (S' : state) (o : out),
        red_expr S' C (spec_args_obj_define_own_prop_4 a1 a2 a3 a4 a5) oo ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq object_loc l a1 ->
        @eq prop_name x a2 ->
        @eq descriptor Desc a3 ->
        @eq bool throw a4 ->
        @eq object_loc lmap a5 ->
        @eq out (out_void S') a6 ->
        @eq out o oo -> P S C a1 a2 a3 a4 a5 (out_void S') oo) ->
       red_expr S C (spec_args_obj_define_own_prop_3 a1 a2 a3 a4 a5 a6) oo ->
       P S C a1 a2 a3 a4 a5 a6 oo.

Parameter inv_red_expr_spec_args_obj_define_own_prop_4
     : forall (S : state) (C : execution_ctx) (a1 : object_loc)
         (a2 : prop_name) (a3 : descriptor) (a4 : bool) 
         (a5 : object_loc) (oo : out)
         (P : state ->
              execution_ctx ->
              object_loc ->
              string -> descriptor -> bool -> object_loc -> out -> Prop),
       (red_expr S C (spec_args_obj_define_own_prop_4 a1 a2 a3 a4 a5) oo ->
        forall (S0 : state) (C0 : execution_ctx) (exte : ext_expr) (o : out),
        @eq (option out)
          (out_of_ext_expr (spec_args_obj_define_own_prop_4 a1 a2 a3 a4 a5))
          (@Some out oo) ->
        abort oo ->
        not
          (abort_intercepted_expr
             (spec_args_obj_define_own_prop_4 a1 a2 a3 a4 a5)) ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq ext_expr exte (spec_args_obj_define_own_prop_4 a1 a2 a3 a4 a5) ->
        @eq out o oo -> P S C a1 a2 a3 a4 a5 oo) ->
       (red_expr S C (spec_args_obj_define_own_prop_4 a1 a2 a3 a4 a5) oo ->
        forall (o1 : out) (S0 : state) (C0 : execution_ctx) 
          (l : object_loc) (x : prop_name) (Desc : descriptor) 
          (throw : bool) (lmap : object_loc) (o : out),
        @eq (option bool) (descriptor_writable a3) (@Some bool false) ->
        red_expr S C (spec_object_delete a5 a2 false) o1 ->
        red_expr S C (spec_args_obj_define_own_prop_5 o1) oo ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq object_loc l a1 ->
        @eq prop_name x a2 ->
        @eq descriptor Desc a3 ->
        @eq bool throw a4 ->
        @eq object_loc lmap a5 -> @eq out o oo -> P S C a1 a2 a3 a4 a5 oo) ->
       (red_expr S C (spec_args_obj_define_own_prop_4 a1 a2 a3 a4 a5) oo ->
        forall (S0 : state) (C0 : execution_ctx) (l : object_loc)
          (x : prop_name) (Desc : descriptor) (throw : bool)
          (lmap : object_loc) (o : out),
        not (@eq (option bool) (descriptor_writable a3) (@Some bool false)) ->
        red_expr S C spec_args_obj_define_own_prop_6 oo ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq object_loc l a1 ->
        @eq prop_name x a2 ->
        @eq descriptor Desc a3 ->
        @eq bool throw a4 ->
        @eq object_loc lmap a5 -> @eq out o oo -> P S C a1 a2 a3 a4 a5 oo) ->
       red_expr S C (spec_args_obj_define_own_prop_4 a1 a2 a3 a4 a5) oo ->
       P S C a1 a2 a3 a4 a5 oo.

Parameter inv_red_expr_spec_args_obj_define_own_prop_5
     : forall (S : state) (C : execution_ctx) (a1 oo : out)
         (P : state -> execution_ctx -> out -> out -> Prop),
       (red_expr S C (spec_args_obj_define_own_prop_5 a1) oo ->
        forall (S0 : state) (C0 : execution_ctx) (exte : ext_expr) (o : out),
        @eq (option out)
          (out_of_ext_expr (spec_args_obj_define_own_prop_5 a1))
          (@Some out oo) ->
        abort oo ->
        not (abort_intercepted_expr (spec_args_obj_define_own_prop_5 a1)) ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq ext_expr exte (spec_args_obj_define_own_prop_5 a1) ->
        @eq out o oo -> P S C a1 oo) ->
       (red_expr S C (spec_args_obj_define_own_prop_5 a1) oo ->
        forall (S0 : state) (C0 : execution_ctx) (S' : state) 
          (b : bool) (o : out),
        red_expr S' C spec_args_obj_define_own_prop_6 oo ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq out (out_ter S' (res_val (value_prim (prim_bool b)))) a1 ->
        @eq out o oo ->
        P S C (out_ter S' (res_val (value_prim (prim_bool b)))) oo) ->
       red_expr S C (spec_args_obj_define_own_prop_5 a1) oo -> P S C a1 oo.

Parameter inv_red_expr_spec_args_obj_define_own_prop_6
     : forall (S : state) (C : execution_ctx) (oo : out)
         (P : state -> execution_ctx -> out -> Prop),
       (red_expr S C spec_args_obj_define_own_prop_6 oo ->
        forall (S0 : state) (C0 : execution_ctx) (exte : ext_expr) (o : out),
        @eq (option out) (out_of_ext_expr spec_args_obj_define_own_prop_6)
          (@Some out oo) ->
        abort oo ->
        not (abort_intercepted_expr spec_args_obj_define_own_prop_6) ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq ext_expr exte spec_args_obj_define_own_prop_6 ->
        @eq out o oo -> P S C oo) ->
       (red_expr S C spec_args_obj_define_own_prop_6 oo ->
        forall (S0 : state) (C0 : execution_ctx),
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq out (out_ter S (res_val (value_prim (prim_bool true)))) oo ->
        P S C (out_ter S (res_val (value_prim (prim_bool true))))) ->
       red_expr S C spec_args_obj_define_own_prop_6 oo -> P S C oo.

Parameter inv_red_expr_spec_args_obj_delete_1
     : forall (S : state) (C : execution_ctx) (a1 : object_loc)
         (a2 : prop_name) (a3 : bool) (a4 : object_loc)
         (a5 : specret full_descriptor) (oo : out)
         (P : state ->
              execution_ctx ->
              object_loc ->
              string ->
              bool -> object_loc -> specret full_descriptor -> out -> Prop),
       (red_expr S C (spec_args_obj_delete_1 a1 a2 a3 a4 a5) oo ->
        forall (S0 : state) (C0 : execution_ctx) (exte : ext_expr) (o : out),
        @eq (option out)
          (out_of_ext_expr (spec_args_obj_delete_1 a1 a2 a3 a4 a5))
          (@Some out oo) ->
        abort oo ->
        not (abort_intercepted_expr (spec_args_obj_delete_1 a1 a2 a3 a4 a5)) ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq ext_expr exte (spec_args_obj_delete_1 a1 a2 a3 a4 a5) ->
        @eq out o oo -> P S C a1 a2 a3 a4 a5 oo) ->
       (red_expr S C (spec_args_obj_delete_1 a1 a2 a3 a4 a5) oo ->
        forall (o1 : out) (S0 S1 : state) (C0 : execution_ctx)
          (l : object_loc) (x : prop_name) (throw : bool) 
          (lmap : object_loc) (D : full_descriptor) 
          (o : out),
        red_expr S0 C (spec_object_delete_1 builtin_delete_default a1 a2 a3)
          o1 ->
        red_expr S0 C (spec_args_obj_delete_2 a1 a2 a3 a4 D o1) oo ->
        @eq state S1 S ->
        @eq execution_ctx C0 C ->
        @eq object_loc l a1 ->
        @eq prop_name x a2 ->
        @eq bool throw a3 ->
        @eq object_loc lmap a4 ->
        @eq (specret full_descriptor) (@ret full_descriptor S0 D) a5 ->
        @eq out o oo -> P S C a1 a2 a3 a4 (@ret full_descriptor S0 D) oo) ->
       red_expr S C (spec_args_obj_delete_1 a1 a2 a3 a4 a5) oo ->
       P S C a1 a2 a3 a4 a5 oo.

Parameter inv_red_expr_spec_args_obj_delete_2
     : forall (S : state) (C : execution_ctx) (a1 : object_loc)
         (a2 : prop_name) (a3 : bool) (a4 : object_loc)
         (a5 : full_descriptor) (a6 oo : out)
         (P : state ->
              execution_ctx ->
              object_loc ->
              string ->
              bool -> object_loc -> full_descriptor -> out -> out -> Prop),
       (red_expr S C (spec_args_obj_delete_2 a1 a2 a3 a4 a5 a6) oo ->
        forall (S0 : state) (C0 : execution_ctx) (exte : ext_expr) (o : out),
        @eq (option out)
          (out_of_ext_expr (spec_args_obj_delete_2 a1 a2 a3 a4 a5 a6))
          (@Some out oo) ->
        abort oo ->
        not
          (abort_intercepted_expr (spec_args_obj_delete_2 a1 a2 a3 a4 a5 a6)) ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq ext_expr exte (spec_args_obj_delete_2 a1 a2 a3 a4 a5 a6) ->
        @eq out o oo -> P S C a1 a2 a3 a4 a5 a6 oo) ->
       (red_expr S C (spec_args_obj_delete_2 a1 a2 a3 a4 a5 a6) oo ->
        forall (o1 : out) (S0 : state) (C0 : execution_ctx) 
          (l : object_loc) (x : prop_name) (throw : bool) 
          (lmap : object_loc) (A : attributes) (S' : state) 
          (o : out),
        red_expr S' C (spec_object_delete a4 a2 false) o1 ->
        red_expr S' C (spec_args_obj_delete_3 o1) oo ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq object_loc l a1 ->
        @eq prop_name x a2 ->
        @eq bool throw a3 ->
        @eq object_loc lmap a4 ->
        @eq full_descriptor (full_descriptor_some A) a5 ->
        @eq out (out_ter S' (res_val (value_prim (prim_bool true)))) a6 ->
        @eq out o oo ->
        P S C a1 a2 a3 a4 (full_descriptor_some A)
          (out_ter S' (res_val (value_prim (prim_bool true)))) oo) ->
       (red_expr S C (spec_args_obj_delete_2 a1 a2 a3 a4 a5 a6) oo ->
        forall (S0 : state) (C0 : execution_ctx) (l : object_loc)
          (x : prop_name) (throw : bool) (lmap : object_loc)
          (D : full_descriptor) (S' : state) (b : bool) 
          (o : out),
        Logic.or (@eq bool b false)
          (@eq full_descriptor a5 full_descriptor_undef) ->
        red_expr S' C (spec_args_obj_delete_4 b) oo ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq object_loc l a1 ->
        @eq prop_name x a2 ->
        @eq bool throw a3 ->
        @eq object_loc lmap a4 ->
        @eq full_descriptor D a5 ->
        @eq out (out_ter S' (res_val (value_prim (prim_bool b)))) a6 ->
        @eq out o oo ->
        P S C a1 a2 a3 a4 a5
          (out_ter S' (res_val (value_prim (prim_bool b)))) oo) ->
       red_expr S C (spec_args_obj_delete_2 a1 a2 a3 a4 a5 a6) oo ->
       P S C a1 a2 a3 a4 a5 a6 oo.

Parameter inv_red_expr_spec_args_obj_delete_3
     : forall (S : state) (C : execution_ctx) (a1 oo : out)
         (P : state -> execution_ctx -> out -> out -> Prop),
       (red_expr S C (spec_args_obj_delete_3 a1) oo ->
        forall (S0 : state) (C0 : execution_ctx) (exte : ext_expr) (o : out),
        @eq (option out) (out_of_ext_expr (spec_args_obj_delete_3 a1))
          (@Some out oo) ->
        abort oo ->
        not (abort_intercepted_expr (spec_args_obj_delete_3 a1)) ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq ext_expr exte (spec_args_obj_delete_3 a1) ->
        @eq out o oo -> P S C a1 oo) ->
       (red_expr S C (spec_args_obj_delete_3 a1) oo ->
        forall (S0 : state) (C0 : execution_ctx) (S' : state) 
          (b : bool) (o : out),
        red_expr S' C (spec_args_obj_delete_4 true) oo ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq out (out_ter S' (res_val (value_prim (prim_bool b)))) a1 ->
        @eq out o oo ->
        P S C (out_ter S' (res_val (value_prim (prim_bool b)))) oo) ->
       red_expr S C (spec_args_obj_delete_3 a1) oo -> P S C a1 oo.

Parameter inv_red_expr_spec_args_obj_delete_4
     : forall (S : state) (C : execution_ctx) (a1 : bool) 
         (oo : out) (P : state -> execution_ctx -> bool -> out -> Prop),
       (red_expr S C (spec_args_obj_delete_4 a1) oo ->
        forall (S0 : state) (C0 : execution_ctx) (exte : ext_expr) (o : out),
        @eq (option out) (out_of_ext_expr (spec_args_obj_delete_4 a1))
          (@Some out oo) ->
        abort oo ->
        not (abort_intercepted_expr (spec_args_obj_delete_4 a1)) ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq ext_expr exte (spec_args_obj_delete_4 a1) ->
        @eq out o oo -> P S C a1 oo) ->
       (red_expr S C (spec_args_obj_delete_4 a1) oo ->
        forall (S0 : state) (C0 : execution_ctx) (b : bool),
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq bool b a1 ->
        @eq out (out_ter S (res_val (value_prim (prim_bool a1)))) oo ->
        P S C a1 (out_ter S (res_val (value_prim (prim_bool a1))))) ->
       red_expr S C (spec_args_obj_delete_4 a1) oo -> P S C a1 oo.

Parameter inv_red_expr_spec_arguments_object_map
     : forall (S : state) (C : execution_ctx) (a1 : object_loc)
         (a2 : list string) (a3 : list value) (a4 : lexical_env)
         (a5 : strictness_flag) (oo : out)
         (P : state ->
              execution_ctx ->
              object_loc ->
              list string -> list value -> list nat -> bool -> out -> Prop),
       (red_expr S C (spec_arguments_object_map a1 a2 a3 a4 a5) oo ->
        forall (S0 : state) (C0 : execution_ctx) (exte : ext_expr) (o : out),
        @eq (option out)
          (out_of_ext_expr (spec_arguments_object_map a1 a2 a3 a4 a5))
          (@Some out oo) ->
        abort oo ->
        not
          (abort_intercepted_expr (spec_arguments_object_map a1 a2 a3 a4 a5)) ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq ext_expr exte (spec_arguments_object_map a1 a2 a3 a4 a5) ->
        @eq out o oo -> P S C a1 a2 a3 a4 a5 oo) ->
       (red_expr S C (spec_arguments_object_map a1 a2 a3 a4 a5) oo ->
        forall (o1 : out) (S0 : state) (C0 : execution_ctx) 
          (l : object_loc) (xs : list prop_name) (args : list value)
          (X : lexical_env) (str : strictness_flag) 
          (o : out),
        red_expr S C (spec_construct_prealloc prealloc_object (@nil value))
          o1 ->
        red_expr S C (spec_arguments_object_map_1 a1 a2 a3 a4 a5 o1) oo ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq object_loc l a1 ->
        @eq (list string) xs a2 ->
        @eq (list value) args a3 ->
        @eq lexical_env X a4 ->
        @eq strictness_flag str a5 -> @eq out o oo -> P S C a1 a2 a3 a4 a5 oo) ->
       red_expr S C (spec_arguments_object_map a1 a2 a3 a4 a5) oo ->
       P S C a1 a2 a3 a4 a5 oo.

Parameter inv_red_expr_spec_arguments_object_map_1
     : forall (S : state) (C : execution_ctx) (a1 : object_loc)
         (a2 : list string) (a3 : list value) (a4 : lexical_env)
         (a5 : strictness_flag) (a6 oo : out)
         (P : state ->
              execution_ctx ->
              object_loc ->
              list string ->
              list value -> list nat -> bool -> out -> out -> Prop),
       (red_expr S C (spec_arguments_object_map_1 a1 a2 a3 a4 a5 a6) oo ->
        forall (S0 : state) (C0 : execution_ctx) (exte : ext_expr) (o : out),
        @eq (option out)
          (out_of_ext_expr (spec_arguments_object_map_1 a1 a2 a3 a4 a5 a6))
          (@Some out oo) ->
        abort oo ->
        not
          (abort_intercepted_expr
             (spec_arguments_object_map_1 a1 a2 a3 a4 a5 a6)) ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq ext_expr exte (spec_arguments_object_map_1 a1 a2 a3 a4 a5 a6) ->
        @eq out o oo -> P S C a1 a2 a3 a4 a5 a6 oo) ->
       (red_expr S C (spec_arguments_object_map_1 a1 a2 a3 a4 a5 a6) oo ->
        forall (S' S0 : state) (C0 : execution_ctx) 
          (l : object_loc) (xs : list prop_name) (args : list value)
          (X : lexical_env) (str : strictness_flag) 
          (lmap : object_loc) (o : out),
        red_expr S' C
          (spec_arguments_object_map_2 a1 a2 a3 a4 a5 lmap 
             (@nil string) (Z.sub (my_Z_of_nat (@length value a3)) (Zpos xH)))
          oo ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq object_loc l a1 ->
        @eq (list string) xs a2 ->
        @eq (list value) args a3 ->
        @eq lexical_env X a4 ->
        @eq strictness_flag str a5 ->
        @eq out (out_ter S' (res_val (value_object lmap))) a6 ->
        @eq out o oo ->
        P S C a1 a2 a3 a4 a5 (out_ter S' (res_val (value_object lmap))) oo) ->
       red_expr S C (spec_arguments_object_map_1 a1 a2 a3 a4 a5 a6) oo ->
       P S C a1 a2 a3 a4 a5 a6 oo.

Parameter inv_red_expr_spec_arguments_object_map_2
     : forall (S : state) (C : execution_ctx) (a1 : object_loc)
         (a2 : list string) (a3 : list value) (a4 : lexical_env)
         (a5 : strictness_flag) (a6 : object_loc) (a7 : list string) 
         (a8 : Z) (oo : out)
         (P : state ->
              execution_ctx ->
              object_loc ->
              list string ->
              list value ->
              list nat ->
              bool -> object_loc -> list string -> Z -> out -> Prop),
       (red_expr S C (spec_arguments_object_map_2 a1 a2 a3 a4 a5 a6 a7 a8) oo ->
        forall (S0 : state) (C0 : execution_ctx) (exte : ext_expr) (o : out),
        @eq (option out)
          (out_of_ext_expr
             (spec_arguments_object_map_2 a1 a2 a3 a4 a5 a6 a7 a8))
          (@Some out oo) ->
        abort oo ->
        not
          (abort_intercepted_expr
             (spec_arguments_object_map_2 a1 a2 a3 a4 a5 a6 a7 a8)) ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq ext_expr exte
          (spec_arguments_object_map_2 a1 a2 a3 a4 a5 a6 a7 a8) ->
        @eq out o oo -> P S C a1 a2 a3 a4 a5 a6 a7 a8 oo) ->
       (red_expr S C (spec_arguments_object_map_2 a1 a2 a3 a4 a5 a6 a7 a8) oo ->
        forall (S0 : state) (C0 : execution_ctx) (l : object_loc)
          (xs : list prop_name) (args : list value) 
          (X : lexical_env) (str : strictness_flag) 
          (lmap : object_loc) (xsmap : list string) 
          (k : Z) (o : out),
        @lt Z (@lt_from_le Z le_int_inst) a8 (my_Z_of_nat O) ->
        red_expr S C (spec_arguments_object_map_8 a1 a6 a7) oo ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq object_loc l a1 ->
        @eq (list string) xs a2 ->
        @eq (list value) args a3 ->
        @eq lexical_env X a4 ->
        @eq strictness_flag str a5 ->
        @eq object_loc lmap a6 ->
        @eq (list string) xsmap a7 ->
        @eq Z k a8 -> @eq out o oo -> P S C a1 a2 a3 a4 a5 a6 a7 a8 oo) ->
       (red_expr S C (spec_arguments_object_map_2 a1 a2 a3 a4 a5 a6 a7 a8) oo ->
        forall (A : attributes) (o1 : out) (S0 : state) 
          (C0 : execution_ctx) (l : object_loc) (xs : list prop_name)
          (args : list value) (X : lexical_env) (str : strictness_flag)
          (lmap : object_loc) (xsmap : list string) 
          (k : Z) (v : value) (o : out),
        @ZNth value a8 a3 v ->
        @eq attributes A
          (attributes_data_of (attributes_data_intro_all_true v)) ->
        red_expr S C
          (spec_object_define_own_prop a1
             (convert_prim_to_string (prim_number (JsNumber.of_int a8)))
             (descriptor_of_attributes A) false) o1 ->
        red_expr S C (spec_arguments_object_map_3 a1 a2 a3 a4 a5 a6 a7 a8 o1)
          oo ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq object_loc l a1 ->
        @eq (list string) xs a2 ->
        @eq (list value) args a3 ->
        @eq lexical_env X a4 ->
        @eq strictness_flag str a5 ->
        @eq object_loc lmap a6 ->
        @eq (list string) xsmap a7 ->
        @eq Z k a8 -> @eq out o oo -> P S C a1 a2 a3 a4 a5 a6 a7 a8 oo) ->
       red_expr S C (spec_arguments_object_map_2 a1 a2 a3 a4 a5 a6 a7 a8) oo ->
       P S C a1 a2 a3 a4 a5 a6 a7 a8 oo.

Parameter inv_red_expr_spec_arguments_object_map_3
     : forall (S : state) (C : execution_ctx) (a1 : object_loc)
         (a2 : list string) (a3 : list value) (a4 : lexical_env)
         (a5 : strictness_flag) (a6 : object_loc) (a7 : list string) 
         (a8 : Z) (a9 oo : out)
         (P : state ->
              execution_ctx ->
              object_loc ->
              list string ->
              list value ->
              list nat ->
              bool -> object_loc -> list string -> Z -> out -> out -> Prop),
       (red_expr S C (spec_arguments_object_map_3 a1 a2 a3 a4 a5 a6 a7 a8 a9)
          oo ->
        forall (S0 : state) (C0 : execution_ctx) (exte : ext_expr) (o : out),
        @eq (option out)
          (out_of_ext_expr
             (spec_arguments_object_map_3 a1 a2 a3 a4 a5 a6 a7 a8 a9))
          (@Some out oo) ->
        abort oo ->
        not
          (abort_intercepted_expr
             (spec_arguments_object_map_3 a1 a2 a3 a4 a5 a6 a7 a8 a9)) ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq ext_expr exte
          (spec_arguments_object_map_3 a1 a2 a3 a4 a5 a6 a7 a8 a9) ->
        @eq out o oo -> P S C a1 a2 a3 a4 a5 a6 a7 a8 a9 oo) ->
       (red_expr S C (spec_arguments_object_map_3 a1 a2 a3 a4 a5 a6 a7 a8 a9)
          oo ->
        forall (S0 : state) (C0 : execution_ctx) (l : object_loc)
          (xs : list prop_name) (args : list value) 
          (X : lexical_env) (str : strictness_flag) 
          (lmap : object_loc) (xsmap : list string) 
          (k : Z) (S' : state) (b : bool) (o : out),
        @ge Z (@ge_from_le Z le_int_inst) a8
          (my_Z_of_nat (@length prop_name a2)) ->
        red_expr S' C
          (spec_arguments_object_map_2 a1 a2 a3 a4 a5 a6 a7
             (Z.sub a8 (Zpos xH))) oo ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq object_loc l a1 ->
        @eq (list string) xs a2 ->
        @eq (list value) args a3 ->
        @eq lexical_env X a4 ->
        @eq strictness_flag str a5 ->
        @eq object_loc lmap a6 ->
        @eq (list string) xsmap a7 ->
        @eq Z k a8 ->
        @eq out (out_ter S' (res_val (value_prim (prim_bool b)))) a9 ->
        @eq out o oo ->
        P S C a1 a2 a3 a4 a5 a6 a7 a8
          (out_ter S' (res_val (value_prim (prim_bool b)))) oo) ->
       (red_expr S C (spec_arguments_object_map_3 a1 a2 a3 a4 a5 a6 a7 a8 a9)
          oo ->
        forall (x : prop_name) (S0 : state) (C0 : execution_ctx)
          (l : object_loc) (xs : list prop_name) (args : list value)
          (X : lexical_env) (str : strictness_flag) 
          (lmap : object_loc) (xsmap : list prop_name) 
          (k : Z) (S' : state) (b : bool) (o : out),
        @ZNth prop_name a8 a2 x ->
        Logic.or (@eq strictness_flag a5 true) (@Mem prop_name x a7) ->
        red_expr S' C
          (spec_arguments_object_map_2 a1 a2 a3 a4 a5 a6 a7
             (Z.sub a8 (Zpos xH))) oo ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq object_loc l a1 ->
        @eq (list string) xs a2 ->
        @eq (list value) args a3 ->
        @eq lexical_env X a4 ->
        @eq strictness_flag str a5 ->
        @eq object_loc lmap a6 ->
        @eq (list string) xsmap a7 ->
        @eq Z k a8 ->
        @eq out (out_ter S' (res_val (value_prim (prim_bool b)))) a9 ->
        @eq out o oo ->
        P S C a1 a2 a3 a4 a5 a6 a7 a8
          (out_ter S' (res_val (value_prim (prim_bool b)))) oo) ->
       (red_expr S C (spec_arguments_object_map_3 a1 a2 a3 a4 a5 a6 a7 a8 a9)
          oo ->
        forall (x : prop_name) (S0 : state) (C0 : execution_ctx)
          (l : object_loc) (xs : list prop_name) (args : list value)
          (X : lexical_env) (str : strictness_flag) 
          (lmap : object_loc) (xsmap : list prop_name) 
          (k : Z) (S' : state) (b : bool) (o : out),
        @ZNth prop_name a8 a2 x ->
        Logic.and (@eq strictness_flag a5 false) (not (@Mem prop_name x a7)) ->
        red_expr S' C (spec_arguments_object_map_4 a1 a2 a3 a4 a5 a6 a7 a8 x)
          oo ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq object_loc l a1 ->
        @eq (list string) xs a2 ->
        @eq (list value) args a3 ->
        @eq lexical_env X a4 ->
        @eq strictness_flag str a5 ->
        @eq object_loc lmap a6 ->
        @eq (list string) xsmap a7 ->
        @eq Z k a8 ->
        @eq out (out_ter S' (res_val (value_prim (prim_bool b)))) a9 ->
        @eq out o oo ->
        P S C a1 a2 a3 a4 a5 a6 a7 a8
          (out_ter S' (res_val (value_prim (prim_bool b)))) oo) ->
       red_expr S C (spec_arguments_object_map_3 a1 a2 a3 a4 a5 a6 a7 a8 a9)
         oo -> P S C a1 a2 a3 a4 a5 a6 a7 a8 a9 oo.

Parameter inv_red_expr_spec_arguments_object_map_4
     : forall (S : state) (C : execution_ctx) (a1 : object_loc)
         (a2 : list string) (a3 : list value) (a4 : lexical_env)
         (a5 : strictness_flag) (a6 : object_loc) (a7 : list string) 
         (a8 : Z) (a9 : string) (oo : out)
         (P : state ->
              execution_ctx ->
              object_loc ->
              list string ->
              list value ->
              list nat ->
              bool -> object_loc -> list string -> Z -> string -> out -> Prop),
       (red_expr S C (spec_arguments_object_map_4 a1 a2 a3 a4 a5 a6 a7 a8 a9)
          oo ->
        forall (S0 : state) (C0 : execution_ctx) (exte : ext_expr) (o : out),
        @eq (option out)
          (out_of_ext_expr
             (spec_arguments_object_map_4 a1 a2 a3 a4 a5 a6 a7 a8 a9))
          (@Some out oo) ->
        abort oo ->
        not
          (abort_intercepted_expr
             (spec_arguments_object_map_4 a1 a2 a3 a4 a5 a6 a7 a8 a9)) ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq ext_expr exte
          (spec_arguments_object_map_4 a1 a2 a3 a4 a5 a6 a7 a8 a9) ->
        @eq out o oo -> P S C a1 a2 a3 a4 a5 a6 a7 a8 a9 oo) ->
       (red_expr S C (spec_arguments_object_map_4 a1 a2 a3 a4 a5 a6 a7 a8 a9)
          oo ->
        forall (o1 : out) (S0 : state) (C0 : execution_ctx) 
          (l : object_loc) (xs : list prop_name) (args : list value)
          (X : lexical_env) (str : strictness_flag) 
          (lmap : object_loc) (xsmap : list prop_name) 
          (k : Z) (x : prop_name) (o : out),
        red_expr S C (spec_make_arg_getter a9 a4) o1 ->
        red_expr S C
          (spec_arguments_object_map_5 a1 a2 a3 a4 a5 a6
             (@cons prop_name a9 a7) a8 a9 o1) oo ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq object_loc l a1 ->
        @eq (list string) xs a2 ->
        @eq (list value) args a3 ->
        @eq lexical_env X a4 ->
        @eq strictness_flag str a5 ->
        @eq object_loc lmap a6 ->
        @eq (list string) xsmap a7 ->
        @eq Z k a8 ->
        @eq string x a9 ->
        @eq out o oo -> P S C a1 a2 a3 a4 a5 a6 a7 a8 a9 oo) ->
       red_expr S C (spec_arguments_object_map_4 a1 a2 a3 a4 a5 a6 a7 a8 a9)
         oo -> P S C a1 a2 a3 a4 a5 a6 a7 a8 a9 oo.

Parameter inv_red_expr_spec_arguments_object_map_5
     : forall (S : state) (C : execution_ctx) (a1 : object_loc)
         (a2 : list string) (a3 : list value) (a4 : lexical_env)
         (a5 : strictness_flag) (a6 : object_loc) (a7 : list string) 
         (a8 : Z) (a9 : string) (a10 oo : out)
         (P : state ->
              execution_ctx ->
              object_loc ->
              list string ->
              list value ->
              list nat ->
              bool ->
              object_loc -> list string -> Z -> string -> out -> out -> Prop),
       (red_expr S C
          (spec_arguments_object_map_5 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10) oo ->
        forall (S0 : state) (C0 : execution_ctx) (exte : ext_expr) (o : out),
        @eq (option out)
          (out_of_ext_expr
             (spec_arguments_object_map_5 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10))
          (@Some out oo) ->
        abort oo ->
        not
          (abort_intercepted_expr
             (spec_arguments_object_map_5 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10)) ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq ext_expr exte
          (spec_arguments_object_map_5 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10) ->
        @eq out o oo -> P S C a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 oo) ->
       (red_expr S C
          (spec_arguments_object_map_5 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10) oo ->
        forall (o1 : out) (S0 : state) (C0 : execution_ctx) 
          (l : object_loc) (xs : list prop_name) (args : list value)
          (X : lexical_env) (str : strictness_flag) 
          (lmap : object_loc) (xsmap : list string) 
          (k : Z) (x : prop_name) (S' : state) (lgetter : object_loc)
          (o : out),
        red_expr S' C (spec_make_arg_setter a9 a4) o1 ->
        red_expr S' C
          (spec_arguments_object_map_6 a1 a2 a3 a4 a5 a6 a7 a8 lgetter o1) oo ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq object_loc l a1 ->
        @eq (list string) xs a2 ->
        @eq (list value) args a3 ->
        @eq lexical_env X a4 ->
        @eq strictness_flag str a5 ->
        @eq object_loc lmap a6 ->
        @eq (list string) xsmap a7 ->
        @eq Z k a8 ->
        @eq string x a9 ->
        @eq out (out_ter S' (res_val (value_object lgetter))) a10 ->
        @eq out o oo ->
        P S C a1 a2 a3 a4 a5 a6 a7 a8 a9
          (out_ter S' (res_val (value_object lgetter))) oo) ->
       red_expr S C
         (spec_arguments_object_map_5 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10) oo ->
       P S C a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 oo.

Parameter inv_red_expr_spec_arguments_object_map_6
     : forall (S : state) (C : execution_ctx) (a1 : object_loc)
         (a2 : list string) (a3 : list value) (a4 : lexical_env)
         (a5 : strictness_flag) (a6 : object_loc) (a7 : list string) 
         (a8 : Z) (a9 : object_loc) (a10 oo : out)
         (P : state ->
              execution_ctx ->
              object_loc ->
              list string ->
              list value ->
              list nat ->
              bool ->
              object_loc ->
              list string -> Z -> object_loc -> out -> out -> Prop),
       (red_expr S C
          (spec_arguments_object_map_6 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10) oo ->
        forall (S0 : state) (C0 : execution_ctx) (exte : ext_expr) (o : out),
        @eq (option out)
          (out_of_ext_expr
             (spec_arguments_object_map_6 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10))
          (@Some out oo) ->
        abort oo ->
        not
          (abort_intercepted_expr
             (spec_arguments_object_map_6 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10)) ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq ext_expr exte
          (spec_arguments_object_map_6 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10) ->
        @eq out o oo -> P S C a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 oo) ->
       (red_expr S C
          (spec_arguments_object_map_6 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10) oo ->
        forall (A : attributes) (o1 : out) (S0 : state) 
          (C0 : execution_ctx) (l : object_loc) (xs : list prop_name)
          (args : list value) (X : lexical_env) (str : strictness_flag)
          (lmap : object_loc) (xsmap : list string) 
          (k : Z) (lgetter : object_loc) (S' : state) 
          (lsetter : object_loc) (o : out),
        @eq attributes A
          (attributes_accessor_of
             (attributes_accessor_intro (value_object a9)
                (value_object lsetter) false true)) ->
        red_expr S' C
          (spec_object_define_own_prop a6
             (convert_prim_to_string (prim_number (JsNumber.of_int a8)))
             (descriptor_of_attributes A) false) o1 ->
        red_expr S' C
          (spec_arguments_object_map_7 a1 a2 a3 a4 a5 a6 a7 a8 o1) oo ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq object_loc l a1 ->
        @eq (list string) xs a2 ->
        @eq (list value) args a3 ->
        @eq lexical_env X a4 ->
        @eq strictness_flag str a5 ->
        @eq object_loc lmap a6 ->
        @eq (list string) xsmap a7 ->
        @eq Z k a8 ->
        @eq object_loc lgetter a9 ->
        @eq out (out_ter S' (res_val (value_object lsetter))) a10 ->
        @eq out o oo ->
        P S C a1 a2 a3 a4 a5 a6 a7 a8 a9
          (out_ter S' (res_val (value_object lsetter))) oo) ->
       red_expr S C
         (spec_arguments_object_map_6 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10) oo ->
       P S C a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 oo.

Parameter inv_red_expr_spec_arguments_object_map_7
     : forall (S : state) (C : execution_ctx) (a1 : object_loc)
         (a2 : list string) (a3 : list value) (a4 : lexical_env)
         (a5 : strictness_flag) (a6 : object_loc) (a7 : list string) 
         (a8 : Z) (a9 oo : out)
         (P : state ->
              execution_ctx ->
              object_loc ->
              list string ->
              list value ->
              list nat ->
              bool -> object_loc -> list string -> Z -> out -> out -> Prop),
       (red_expr S C (spec_arguments_object_map_7 a1 a2 a3 a4 a5 a6 a7 a8 a9)
          oo ->
        forall (S0 : state) (C0 : execution_ctx) (exte : ext_expr) (o : out),
        @eq (option out)
          (out_of_ext_expr
             (spec_arguments_object_map_7 a1 a2 a3 a4 a5 a6 a7 a8 a9))
          (@Some out oo) ->
        abort oo ->
        not
          (abort_intercepted_expr
             (spec_arguments_object_map_7 a1 a2 a3 a4 a5 a6 a7 a8 a9)) ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq ext_expr exte
          (spec_arguments_object_map_7 a1 a2 a3 a4 a5 a6 a7 a8 a9) ->
        @eq out o oo -> P S C a1 a2 a3 a4 a5 a6 a7 a8 a9 oo) ->
       (red_expr S C (spec_arguments_object_map_7 a1 a2 a3 a4 a5 a6 a7 a8 a9)
          oo ->
        forall (S0 : state) (C0 : execution_ctx) (l : object_loc)
          (xs : list prop_name) (args : list value) 
          (X : lexical_env) (str : strictness_flag) 
          (lmap : object_loc) (xsmap : list string) 
          (k : Z) (S' : state) (b : bool) (o : out),
        red_expr S' C
          (spec_arguments_object_map_2 a1 a2 a3 a4 a5 a6 a7
             (Z.sub a8 (Zpos xH))) oo ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq object_loc l a1 ->
        @eq (list string) xs a2 ->
        @eq (list value) args a3 ->
        @eq lexical_env X a4 ->
        @eq strictness_flag str a5 ->
        @eq object_loc lmap a6 ->
        @eq (list string) xsmap a7 ->
        @eq Z k a8 ->
        @eq out (out_ter S' (res_val (value_prim (prim_bool b)))) a9 ->
        @eq out o oo ->
        P S C a1 a2 a3 a4 a5 a6 a7 a8
          (out_ter S' (res_val (value_prim (prim_bool b)))) oo) ->
       red_expr S C (spec_arguments_object_map_7 a1 a2 a3 a4 a5 a6 a7 a8 a9)
         oo -> P S C a1 a2 a3 a4 a5 a6 a7 a8 a9 oo.

Parameter inv_red_expr_spec_arguments_object_map_8
     : forall (S : state) (C : execution_ctx) (a1 a2 : object_loc)
         (a3 : list string) (oo : out)
         (P : state ->
              execution_ctx ->
              object_loc -> object_loc -> list string -> out -> Prop),
       (red_expr S C (spec_arguments_object_map_8 a1 a2 a3) oo ->
        forall (S0 : state) (C0 : execution_ctx) (exte : ext_expr) (o : out),
        @eq (option out)
          (out_of_ext_expr (spec_arguments_object_map_8 a1 a2 a3))
          (@Some out oo) ->
        abort oo ->
        not (abort_intercepted_expr (spec_arguments_object_map_8 a1 a2 a3)) ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq ext_expr exte (spec_arguments_object_map_8 a1 a2 a3) ->
        @eq out o oo -> P S C a1 a2 a3 oo) ->
       (red_expr S C (spec_arguments_object_map_8 a1 a2 a3) oo ->
        forall (O O' : object) (S0 : state) (C0 : execution_ctx)
          (l lmap : object_loc) (xsmap : list string) 
          (S' : state),
        not (@eq (list string) a3 (@nil string)) ->
        object_binds S a1 O ->
        @eq object O'
          (object_for_args_object O a2 builtin_get_args_obj
             builtin_get_own_prop_args_obj builtin_define_own_prop_args_obj
             builtin_delete_args_obj) ->
        @eq state S' (object_write S a1 O') ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq object_loc l a1 ->
        @eq object_loc lmap a2 ->
        @eq (list string) xsmap a3 ->
        @eq out (out_void S') oo -> P S C a1 a2 a3 (out_void S')) ->
       (red_expr S C (spec_arguments_object_map_8 a1 a2 a3) oo ->
        forall (S0 : state) (C0 : execution_ctx) (l lmap : object_loc),
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq object_loc l a1 ->
        @eq object_loc lmap a2 ->
        @eq (list string) (@nil string) a3 ->
        @eq out (out_void S) oo -> P S C a1 a2 (@nil string) (out_void S)) ->
       red_expr S C (spec_arguments_object_map_8 a1 a2 a3) oo ->
       P S C a1 a2 a3 oo.

Parameter inv_red_expr_spec_create_arguments_object
     : forall (S : state) (C : execution_ctx) (a1 : object_loc)
         (a2 : list string) (a3 : list value) (a4 : lexical_env)
         (a5 : strictness_flag) (oo : out)
         (P : state ->
              execution_ctx ->
              object_loc ->
              list string -> list value -> list nat -> bool -> out -> Prop),
       (red_expr S C (spec_create_arguments_object a1 a2 a3 a4 a5) oo ->
        forall (S0 : state) (C0 : execution_ctx) (exte : ext_expr) (o : out),
        @eq (option out)
          (out_of_ext_expr (spec_create_arguments_object a1 a2 a3 a4 a5))
          (@Some out oo) ->
        abort oo ->
        not
          (abort_intercepted_expr
             (spec_create_arguments_object a1 a2 a3 a4 a5)) ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq ext_expr exte (spec_create_arguments_object a1 a2 a3 a4 a5) ->
        @eq out o oo -> P S C a1 a2 a3 a4 a5 oo) ->
       (red_expr S C (spec_create_arguments_object a1 a2 a3 a4 a5) oo ->
        forall (O : object) (l : object_loc) (S' : state) 
          (A : attributes) (o1 : out) (S0 : state) 
          (C0 : execution_ctx) (lf : object_loc) (xs : list prop_name)
          (args : list value) (X : lexical_env) (str : strictness_flag)
          (o : out),
        @eq object O
          (object_new
             (value_object (object_loc_prealloc prealloc_object_proto))
             (String (Ascii true false false false false false true false)
                (String (Ascii false true false false true true true false)
                   (String (Ascii true true true false false true true false)
                      (String
                         (Ascii true false true false true true true false)
                         (String
                            (Ascii true false true true false true true false)
                            (String
                               (Ascii true false true false false true true
                                  false)
                               (String
                                  (Ascii false true true true false true true
                                     false)
                                  (String
                                     (Ascii false false true false true true
                                        true false)
                                     (String
                                        (Ascii true true false false true
                                           true true false) EmptyString)))))))))) ->
        @eq (prod object_loc state) (@pair object_loc state l S')
          (object_alloc S O) ->
        @eq attributes A
          (attributes_data_of
             (attributes_data_intro
                (value_prim
                   (prim_number
                      (JsNumber.of_int (my_Z_of_nat (@length value a3)))))
                true false true)) ->
        red_expr S' C
          (spec_object_define_own_prop l
             (String (Ascii false false true true false true true false)
                (String (Ascii true false true false false true true false)
                   (String (Ascii false true true true false true true false)
                      (String
                         (Ascii true true true false false true true false)
                         (String
                            (Ascii false false true false true true true
                               false)
                            (String
                               (Ascii false false false true false true true
                                  false) EmptyString))))))
             (descriptor_of_attributes A) false) o1 ->
        red_expr S' C (spec_create_arguments_object_1 a1 a2 a3 a4 a5 l o1) oo ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq object_loc lf a1 ->
        @eq (list string) xs a2 ->
        @eq (list value) args a3 ->
        @eq lexical_env X a4 ->
        @eq strictness_flag str a5 -> @eq out o oo -> P S C a1 a2 a3 a4 a5 oo) ->
       red_expr S C (spec_create_arguments_object a1 a2 a3 a4 a5) oo ->
       P S C a1 a2 a3 a4 a5 oo.

Parameter inv_red_expr_spec_create_arguments_object_1
     : forall (S : state) (C : execution_ctx) (a1 : object_loc)
         (a2 : list string) (a3 : list value) (a4 : lexical_env)
         (a5 : strictness_flag) (a6 : object_loc) (a7 oo : out)
         (P : state ->
              execution_ctx ->
              object_loc ->
              list string ->
              list value ->
              list nat -> bool -> object_loc -> out -> out -> Prop),
       (red_expr S C (spec_create_arguments_object_1 a1 a2 a3 a4 a5 a6 a7) oo ->
        forall (S0 : state) (C0 : execution_ctx) (exte : ext_expr) (o : out),
        @eq (option out)
          (out_of_ext_expr
             (spec_create_arguments_object_1 a1 a2 a3 a4 a5 a6 a7))
          (@Some out oo) ->
        abort oo ->
        not
          (abort_intercepted_expr
             (spec_create_arguments_object_1 a1 a2 a3 a4 a5 a6 a7)) ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq ext_expr exte
          (spec_create_arguments_object_1 a1 a2 a3 a4 a5 a6 a7) ->
        @eq out o oo -> P S C a1 a2 a3 a4 a5 a6 a7 oo) ->
       (red_expr S C (spec_create_arguments_object_1 a1 a2 a3 a4 a5 a6 a7) oo ->
        forall (o1 : out) (S0 : state) (C0 : execution_ctx) 
          (lf : object_loc) (xs : list prop_name) (args : list value)
          (X : lexical_env) (str : strictness_flag) 
          (l : object_loc) (S' : state) (b : bool) 
          (o : out),
        red_expr S' C (spec_arguments_object_map a6 a2 a3 a4 a5) o1 ->
        red_expr S' C (spec_create_arguments_object_2 a1 a5 a6 o1) oo ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq object_loc lf a1 ->
        @eq (list string) xs a2 ->
        @eq (list value) args a3 ->
        @eq lexical_env X a4 ->
        @eq strictness_flag str a5 ->
        @eq object_loc l a6 ->
        @eq out (out_ter S' (res_val (value_prim (prim_bool b)))) a7 ->
        @eq out o oo ->
        P S C a1 a2 a3 a4 a5 a6
          (out_ter S' (res_val (value_prim (prim_bool b)))) oo) ->
       red_expr S C (spec_create_arguments_object_1 a1 a2 a3 a4 a5 a6 a7) oo ->
       P S C a1 a2 a3 a4 a5 a6 a7 oo.

Parameter inv_red_expr_spec_create_arguments_object_2
     : forall (S : state) (C : execution_ctx) (a1 : object_loc)
         (a2 : strictness_flag) (a3 : object_loc) (a4 oo : out)
         (P : state ->
              execution_ctx ->
              object_loc -> bool -> object_loc -> out -> out -> Prop),
       (red_expr S C (spec_create_arguments_object_2 a1 a2 a3 a4) oo ->
        forall (S0 : state) (C0 : execution_ctx) (exte : ext_expr) (o : out),
        @eq (option out)
          (out_of_ext_expr (spec_create_arguments_object_2 a1 a2 a3 a4))
          (@Some out oo) ->
        abort oo ->
        not
          (abort_intercepted_expr
             (spec_create_arguments_object_2 a1 a2 a3 a4)) ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq ext_expr exte (spec_create_arguments_object_2 a1 a2 a3 a4) ->
        @eq out o oo -> P S C a1 a2 a3 a4 oo) ->
       (red_expr S C (spec_create_arguments_object_2 a1 a2 a3 a4) oo ->
        forall (A : attributes) (o1 : out) (S0 : state) 
          (C0 : execution_ctx) (lf l : object_loc) 
          (S' : state) (o : out),
        @eq attributes A
          (attributes_data_of
             (attributes_data_intro (value_object a1) true false true)) ->
        red_expr S' C
          (spec_object_define_own_prop a3
             (String (Ascii true true false false false true true false)
                (String (Ascii true false false false false true true false)
                   (String
                      (Ascii false false true true false true true false)
                      (String
                         (Ascii false false true true false true true false)
                         (String
                            (Ascii true false true false false true true
                               false)
                            (String
                               (Ascii true false true false false true true
                                  false) EmptyString))))))
             (descriptor_of_attributes A) false) o1 ->
        red_expr S' C (spec_create_arguments_object_4 a3 o1) oo ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq object_loc lf a1 ->
        @eq strictness_flag false a2 ->
        @eq object_loc l a3 ->
        @eq out (out_void S') a4 ->
        @eq out o oo -> P S C a1 false a3 (out_void S') oo) ->
       (red_expr S C (spec_create_arguments_object_2 a1 a2 a3 a4) oo ->
        forall (vthrower : value) (A : attributes) 
          (o1 : out) (S0 : state) (C0 : execution_ctx) 
          (lf l : object_loc) (S' : state) (o : out),
        @eq value vthrower
          (value_object (object_loc_prealloc prealloc_throw_type_error)) ->
        @eq attributes A
          (attributes_accessor_of
             (attributes_accessor_intro vthrower vthrower false false)) ->
        red_expr S' C
          (spec_object_define_own_prop a3
             (String (Ascii true true false false false true true false)
                (String (Ascii true false false false false true true false)
                   (String
                      (Ascii false false true true false true true false)
                      (String
                         (Ascii false false true true false true true false)
                         (String
                            (Ascii true false true false false true true
                               false)
                            (String
                               (Ascii false true false false true true true
                                  false) EmptyString))))))
             (descriptor_of_attributes A) false) o1 ->
        red_expr S' C (spec_create_arguments_object_3 a3 vthrower A o1) oo ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq object_loc lf a1 ->
        @eq strictness_flag true a2 ->
        @eq object_loc l a3 ->
        @eq out (out_void S') a4 ->
        @eq out o oo -> P S C a1 true a3 (out_void S') oo) ->
       red_expr S C (spec_create_arguments_object_2 a1 a2 a3 a4) oo ->
       P S C a1 a2 a3 a4 oo.

Parameter inv_red_expr_spec_create_arguments_object_3
     : forall (S : state) (C : execution_ctx) (a1 : object_loc) 
         (a2 : value) (a3 : attributes) (a4 oo : out)
         (P : state ->
              execution_ctx ->
              object_loc -> value -> attributes -> out -> out -> Prop),
       (red_expr S C (spec_create_arguments_object_3 a1 a2 a3 a4) oo ->
        forall (S0 : state) (C0 : execution_ctx) (exte : ext_expr) (o : out),
        @eq (option out)
          (out_of_ext_expr (spec_create_arguments_object_3 a1 a2 a3 a4))
          (@Some out oo) ->
        abort oo ->
        not
          (abort_intercepted_expr
             (spec_create_arguments_object_3 a1 a2 a3 a4)) ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq ext_expr exte (spec_create_arguments_object_3 a1 a2 a3 a4) ->
        @eq out o oo -> P S C a1 a2 a3 a4 oo) ->
       (red_expr S C (spec_create_arguments_object_3 a1 a2 a3 a4) oo ->
        forall (o1 : out) (S0 : state) (C0 : execution_ctx) 
          (l : object_loc) (vthrower : value) (A : attributes) 
          (S' : state) (b : bool) (o : out),
        red_expr S' C
          (spec_object_define_own_prop a1
             (String (Ascii true true false false false true true false)
                (String (Ascii true false false false false true true false)
                   (String
                      (Ascii false false true true false true true false)
                      (String
                         (Ascii false false true true false true true false)
                         (String
                            (Ascii true false true false false true true
                               false)
                            (String
                               (Ascii true false true false false true true
                                  false) EmptyString))))))
             (descriptor_of_attributes a3) false) o1 ->
        red_expr S' C (spec_create_arguments_object_4 a1 o1) oo ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq object_loc l a1 ->
        @eq value vthrower a2 ->
        @eq attributes A a3 ->
        @eq out (out_ter S' (res_val (value_prim (prim_bool b)))) a4 ->
        @eq out o oo ->
        P S C a1 a2 a3 (out_ter S' (res_val (value_prim (prim_bool b)))) oo) ->
       red_expr S C (spec_create_arguments_object_3 a1 a2 a3 a4) oo ->
       P S C a1 a2 a3 a4 oo.

Parameter inv_red_expr_spec_create_arguments_object_4
     : forall (S : state) (C : execution_ctx) (a1 : object_loc) 
         (a2 oo : out)
         (P : state -> execution_ctx -> object_loc -> out -> out -> Prop),
       (red_expr S C (spec_create_arguments_object_4 a1 a2) oo ->
        forall (S0 : state) (C0 : execution_ctx) (exte : ext_expr) (o : out),
        @eq (option out)
          (out_of_ext_expr (spec_create_arguments_object_4 a1 a2))
          (@Some out oo) ->
        abort oo ->
        not (abort_intercepted_expr (spec_create_arguments_object_4 a1 a2)) ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq ext_expr exte (spec_create_arguments_object_4 a1 a2) ->
        @eq out o oo -> P S C a1 a2 oo) ->
       (red_expr S C (spec_create_arguments_object_4 a1 a2) oo ->
        forall (S0 : state) (C0 : execution_ctx) (l : object_loc)
          (S' : state) (b : bool),
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq object_loc l a1 ->
        @eq out (out_ter S' (res_val (value_prim (prim_bool b)))) a2 ->
        @eq out (out_ter S' (res_val (value_object a1))) oo ->
        P S C a1 (out_ter S' (res_val (value_prim (prim_bool b))))
          (out_ter S' (res_val (value_object a1)))) ->
       red_expr S C (spec_create_arguments_object_4 a1 a2) oo ->
       P S C a1 a2 oo.

Parameter inv_red_expr_spec_object_has_instance
     : forall (S : state) (C : execution_ctx) (a1 : object_loc) 
         (a2 : value) (oo : out)
         (P : state -> execution_ctx -> object_loc -> value -> out -> Prop),
       (red_expr S C (spec_object_has_instance a1 a2) oo ->
        forall (S0 : state) (C0 : execution_ctx) (exte : ext_expr) (o : out),
        @eq (option out) (out_of_ext_expr (spec_object_has_instance a1 a2))
          (@Some out oo) ->
        abort oo ->
        not (abort_intercepted_expr (spec_object_has_instance a1 a2)) ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq ext_expr exte (spec_object_has_instance a1 a2) ->
        @eq out o oo -> P S C a1 a2 oo) ->
       (red_expr S C (spec_object_has_instance a1 a2) oo ->
        forall (S0 : state) (C0 : execution_ctx) (l : object_loc) 
          (v : value) (B : builtin_has_instance) (o : out),
        @object_method (option builtin_has_instance) object_has_instance_ S
          a1 (@Some builtin_has_instance B) ->
        red_expr S C (spec_object_has_instance_1 B a1 a2) oo ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq object_loc l a1 ->
        @eq value v a2 -> @eq out o oo -> P S C a1 a2 oo) ->
       red_expr S C (spec_object_has_instance a1 a2) oo -> P S C a1 a2 oo.

Parameter inv_red_expr_spec_object_has_instance_1
     : forall (S : state) (C : execution_ctx) (a1 : builtin_has_instance)
         (a2 : object_loc) (a3 : value) (oo : out)
         (P : state ->
              execution_ctx ->
              builtin_has_instance -> object_loc -> value -> out -> Prop),
       (red_expr S C (spec_object_has_instance_1 a1 a2 a3) oo ->
        forall (S0 : state) (C0 : execution_ctx) (exte : ext_expr) (o : out),
        @eq (option out)
          (out_of_ext_expr (spec_object_has_instance_1 a1 a2 a3))
          (@Some out oo) ->
        abort oo ->
        not (abort_intercepted_expr (spec_object_has_instance_1 a1 a2 a3)) ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq ext_expr exte (spec_object_has_instance_1 a1 a2 a3) ->
        @eq out o oo -> P S C a1 a2 a3 oo) ->
       (red_expr S C (spec_object_has_instance_1 a1 a2 a3) oo ->
        forall (S0 : state) (C0 : execution_ctx) (l : object_loc) (w : prim),
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq builtin_has_instance builtin_has_instance_function a1 ->
        @eq object_loc l a2 ->
        @eq value (value_prim w) a3 ->
        @eq out (out_ter S (res_val (value_prim (prim_bool false)))) oo ->
        P S C builtin_has_instance_function a2 (value_prim w)
          (out_ter S (res_val (value_prim (prim_bool false))))) ->
       (red_expr S C (spec_object_has_instance_1 a1 a2 a3) oo ->
        forall (o1 : out) (S0 : state) (C0 : execution_ctx)
          (l lv : object_loc) (o : out),
        red_expr S C
          (spec_object_get a2
             (String (Ascii false false false false true true true false)
                (String (Ascii false true false false true true true false)
                   (String (Ascii true true true true false true true false)
                      (String
                         (Ascii false false true false true true true false)
                         (String
                            (Ascii true true true true false true true false)
                            (String
                               (Ascii false false true false true true true
                                  false)
                               (String
                                  (Ascii true false false true true true true
                                     false)
                                  (String
                                     (Ascii false false false false true true
                                        true false)
                                     (String
                                        (Ascii true false true false false
                                           true true false) EmptyString))))))))))
          o1 ->
        red_expr S C (spec_function_has_instance_1 lv o1) oo ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq builtin_has_instance builtin_has_instance_function a1 ->
        @eq object_loc l a2 ->
        @eq value (value_object lv) a3 ->
        @eq out o oo ->
        P S C builtin_has_instance_function a2 (value_object lv) oo) ->
       (red_expr S C (spec_object_has_instance_1 a1 a2 a3) oo ->
        forall (S0 : state) (C0 : execution_ctx) (l : object_loc) 
          (v : value) (o : out),
        red_expr S C (spec_function_has_instance_after_bind_1 a2 a3) oo ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq builtin_has_instance builtin_has_instance_after_bind a1 ->
        @eq object_loc l a2 ->
        @eq value v a3 ->
        @eq out o oo -> P S C builtin_has_instance_after_bind a2 a3 oo) ->
       red_expr S C (spec_object_has_instance_1 a1 a2 a3) oo ->
       P S C a1 a2 a3 oo.

Parameter inv_red_expr_spec_function_has_instance_1
     : forall (S : state) (C : execution_ctx) (a1 : object_loc) 
         (a2 oo : out)
         (P : state -> execution_ctx -> object_loc -> out -> out -> Prop),
       (red_expr S C (spec_function_has_instance_1 a1 a2) oo ->
        forall (S0 : state) (C0 : execution_ctx) (exte : ext_expr) (o : out),
        @eq (option out)
          (out_of_ext_expr (spec_function_has_instance_1 a1 a2))
          (@Some out oo) ->
        abort oo ->
        not (abort_intercepted_expr (spec_function_has_instance_1 a1 a2)) ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq ext_expr exte (spec_function_has_instance_1 a1 a2) ->
        @eq out o oo -> P S C a1 a2 oo) ->
       (red_expr S C (spec_function_has_instance_1 a1 a2) oo ->
        forall (S0 S1 : state) (C0 : execution_ctx) 
          (lv : object_loc) (v : value) (o : out),
        not (@eq type (type_of v) type_object) ->
        red_expr S1 C (spec_error native_error_type) oo ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq object_loc lv a1 ->
        @eq out (out_ter S1 (res_val v)) a2 ->
        @eq out o oo -> P S C a1 (out_ter S1 (res_val v)) oo) ->
       (red_expr S C (spec_function_has_instance_1 a1 a2) oo ->
        forall (S0 S1 : state) (C0 : execution_ctx) 
          (lv lo : object_loc) (o : out),
        red_expr S1 C (spec_function_has_instance_2 lo a1) oo ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq object_loc lv a1 ->
        @eq out (out_ter S1 (res_val (value_object lo))) a2 ->
        @eq out o oo -> P S C a1 (out_ter S1 (res_val (value_object lo))) oo) ->
       red_expr S C (spec_function_has_instance_1 a1 a2) oo -> P S C a1 a2 oo.

Parameter inv_red_expr_spec_function_has_instance_2
     : forall (S : state) (C : execution_ctx) (a1 a2 : object_loc) 
         (oo : out)
         (P : state ->
              execution_ctx -> object_loc -> object_loc -> out -> Prop),
       (red_expr S C (spec_function_has_instance_2 a1 a2) oo ->
        forall (S0 : state) (C0 : execution_ctx) (exte : ext_expr) (o : out),
        @eq (option out)
          (out_of_ext_expr (spec_function_has_instance_2 a1 a2))
          (@Some out oo) ->
        abort oo ->
        not (abort_intercepted_expr (spec_function_has_instance_2 a1 a2)) ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq ext_expr exte (spec_function_has_instance_2 a1 a2) ->
        @eq out o oo -> P S C a1 a2 oo) ->
       (red_expr S C (spec_function_has_instance_2 a1 a2) oo ->
        forall (S0 : state) (C0 : execution_ctx) (lo lv : object_loc)
          (vproto : value) (o : out),
        object_proto S a2 vproto ->
        red_expr S C (spec_function_has_instance_3 a1 vproto) oo ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq object_loc lo a1 ->
        @eq object_loc lv a2 -> @eq out o oo -> P S C a1 a2 oo) ->
       red_expr S C (spec_function_has_instance_2 a1 a2) oo -> P S C a1 a2 oo.

Parameter inv_red_expr_spec_function_has_instance_3
     : forall (S : state) (C : execution_ctx) (a1 : object_loc) 
         (a2 : value) (oo : out)
         (P : state -> execution_ctx -> object_loc -> value -> out -> Prop),
       (red_expr S C (spec_function_has_instance_3 a1 a2) oo ->
        forall (S0 : state) (C0 : execution_ctx) (exte : ext_expr) (o : out),
        @eq (option out)
          (out_of_ext_expr (spec_function_has_instance_3 a1 a2))
          (@Some out oo) ->
        abort oo ->
        not (abort_intercepted_expr (spec_function_has_instance_3 a1 a2)) ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq ext_expr exte (spec_function_has_instance_3 a1 a2) ->
        @eq out o oo -> P S C a1 a2 oo) ->
       (red_expr S C (spec_function_has_instance_3 a1 a2) oo ->
        forall (S0 : state) (C0 : execution_ctx) (lo : object_loc),
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq object_loc lo a1 ->
        @eq value (value_prim prim_null) a2 ->
        @eq out (out_ter S (res_val (value_prim (prim_bool false)))) oo ->
        P S C a1 (value_prim prim_null)
          (out_ter S (res_val (value_prim (prim_bool false))))) ->
       (red_expr S C (spec_function_has_instance_3 a1 a2) oo ->
        forall (S0 : state) (C0 : execution_ctx) (lo lv : object_loc),
        @eq object_loc lv a1 ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq object_loc lo a1 ->
        @eq value (value_object lv) a2 ->
        @eq out (out_ter S (res_val (value_prim (prim_bool true)))) oo ->
        P S C a1 (value_object lv)
          (out_ter S (res_val (value_prim (prim_bool true))))) ->
       (red_expr S C (spec_function_has_instance_3 a1 a2) oo ->
        forall (S0 : state) (C0 : execution_ctx) (lo lv : object_loc)
          (o : out),
        not (@eq object_loc lv a1) ->
        red_expr S C (spec_function_has_instance_2 a1 lv) oo ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq object_loc lo a1 ->
        @eq value (value_object lv) a2 ->
        @eq out o oo -> P S C a1 (value_object lv) oo) ->
       red_expr S C (spec_function_has_instance_3 a1 a2) oo -> P S C a1 a2 oo.

Parameter inv_red_expr_spec_function_has_instance_after_bind_1
     : forall (S : state) (C : execution_ctx) (a1 : object_loc) 
         (a2 : value) (oo : out)
         (P : state -> execution_ctx -> object_loc -> value -> out -> Prop),
       (red_expr S C (spec_function_has_instance_after_bind_1 a1 a2) oo ->
        forall (S0 : state) (C0 : execution_ctx) (exte : ext_expr) (o : out),
        @eq (option out)
          (out_of_ext_expr (spec_function_has_instance_after_bind_1 a1 a2))
          (@Some out oo) ->
        abort oo ->
        not
          (abort_intercepted_expr
             (spec_function_has_instance_after_bind_1 a1 a2)) ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq ext_expr exte (spec_function_has_instance_after_bind_1 a1 a2) ->
        @eq out o oo -> P S C a1 a2 oo) ->
       (red_expr S C (spec_function_has_instance_after_bind_1 a1 a2) oo ->
        forall (S0 : state) (C0 : execution_ctx) (l l' : object_loc)
          (v : value) (o : out),
        @object_method (option object_loc) object_target_function_ S a1
          (@Some object_loc l') ->
        red_expr S C (spec_function_has_instance_after_bind_2 l' a2) oo ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq object_loc l a1 ->
        @eq value v a2 -> @eq out o oo -> P S C a1 a2 oo) ->
       red_expr S C (spec_function_has_instance_after_bind_1 a1 a2) oo ->
       P S C a1 a2 oo.

Parameter inv_red_expr_spec_function_has_instance_after_bind_2
     : forall (S : state) (C : execution_ctx) (a1 : object_loc) 
         (a2 : value) (oo : out)
         (P : state -> execution_ctx -> object_loc -> value -> out -> Prop),
       (red_expr S C (spec_function_has_instance_after_bind_2 a1 a2) oo ->
        forall (S0 : state) (C0 : execution_ctx) (exte : ext_expr) (o : out),
        @eq (option out)
          (out_of_ext_expr (spec_function_has_instance_after_bind_2 a1 a2))
          (@Some out oo) ->
        abort oo ->
        not
          (abort_intercepted_expr
             (spec_function_has_instance_after_bind_2 a1 a2)) ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq ext_expr exte (spec_function_has_instance_after_bind_2 a1 a2) ->
        @eq out o oo -> P S C a1 a2 oo) ->
       (red_expr S C (spec_function_has_instance_after_bind_2 a1 a2) oo ->
        forall (S0 : state) (C0 : execution_ctx) (l' : object_loc)
          (v : value) (o : out),
        @object_method (option builtin_has_instance) object_has_instance_ S
          a1 (@None builtin_has_instance) ->
        red_expr S C (spec_error native_error_type) oo ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq object_loc l' a1 ->
        @eq value v a2 -> @eq out o oo -> P S C a1 a2 oo) ->
       (red_expr S C (spec_function_has_instance_after_bind_2 a1 a2) oo ->
        forall (S0 : state) (C0 : execution_ctx) (B : builtin_has_instance)
          (l' : object_loc) (v : value) (o : out),
        @object_method (option builtin_has_instance) object_has_instance_ S
          a1 (@Some builtin_has_instance B) ->
        red_expr S C (spec_object_has_instance_1 B a1 a2) oo ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq object_loc l' a1 ->
        @eq value v a2 -> @eq out o oo -> P S C a1 a2 oo) ->
       red_expr S C (spec_function_has_instance_after_bind_2 a1 a2) oo ->
       P S C a1 a2 oo.

Parameter inv_red_expr_spec_function_get_1
     : forall (S : state) (C : execution_ctx) (a1 : object_loc)
         (a2 : prop_name) (a3 oo : out)
         (P : state ->
              execution_ctx -> object_loc -> string -> out -> out -> Prop),
       (red_expr S C (spec_function_get_1 a1 a2 a3) oo ->
        forall (S0 : state) (C0 : execution_ctx) (exte : ext_expr) (o : out),
        @eq (option out) (out_of_ext_expr (spec_function_get_1 a1 a2 a3))
          (@Some out oo) ->
        abort oo ->
        not (abort_intercepted_expr (spec_function_get_1 a1 a2 a3)) ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq ext_expr exte (spec_function_get_1 a1 a2 a3) ->
        @eq out o oo -> P S C a1 a2 a3 oo) ->
       (red_expr S C (spec_function_get_1 a1 a2 a3) oo ->
        forall (S0 S1 : state) (C0 : execution_ctx) 
          (l : object_loc) (x : prop_name) (v : value) 
          (o : out),
        spec_function_get_error_case S1 a2 v ->
        red_expr S1 C (spec_error native_error_type) oo ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq object_loc l a1 ->
        @eq prop_name x a2 ->
        @eq out (out_ter S1 (res_val v)) a3 ->
        @eq out o oo -> P S C a1 a2 (out_ter S1 (res_val v)) oo) ->
       (red_expr S C (spec_function_get_1 a1 a2 a3) oo ->
        forall (S0 S1 : state) (C0 : execution_ctx) 
          (l : object_loc) (x : prop_name) (v : value),
        not (spec_function_get_error_case S1 a2 v) ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq object_loc l a1 ->
        @eq prop_name x a2 ->
        @eq out (out_ter S1 (res_val v)) a3 ->
        @eq out (out_ter S1 (res_val v)) oo ->
        P S C a1 a2 (out_ter S1 (res_val v)) (out_ter S1 (res_val v))) ->
       red_expr S C (spec_function_get_1 a1 a2 a3) oo -> P S C a1 a2 a3 oo.

Parameter inv_red_expr_spec_error
     : forall (S : state) (C : execution_ctx) (a1 : native_error) 
         (oo : out)
         (P : state -> execution_ctx -> native_error -> out -> Prop),
       (red_expr S C (spec_error a1) oo ->
        forall (S0 : state) (C0 : execution_ctx) (exte : ext_expr) (o : out),
        @eq (option out) (out_of_ext_expr (spec_error a1)) (@Some out oo) ->
        abort oo ->
        not (abort_intercepted_expr (spec_error a1)) ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq ext_expr exte (spec_error a1) -> @eq out o oo -> P S C a1 oo) ->
       (red_expr S C (spec_error a1) oo ->
        forall (S0 : state) (C0 : execution_ctx) (ne : native_error)
          (o1 o : out),
        red_expr S C
          (spec_build_error
             (value_object
                (object_loc_prealloc (prealloc_native_error_proto a1)))
             (value_prim prim_undef)) o1 ->
        red_expr S C (spec_error_1 o1) oo ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq native_error ne a1 -> @eq out o oo -> P S C a1 oo) ->
       red_expr S C (spec_error a1) oo -> P S C a1 oo.

Parameter inv_red_expr_spec_error_1
     : forall (S : state) (C : execution_ctx) (a1 oo : out)
         (P : state -> execution_ctx -> out -> out -> Prop),
       (red_expr S C (spec_error_1 a1) oo ->
        forall (S0 : state) (C0 : execution_ctx) (exte : ext_expr) (o : out),
        @eq (option out) (out_of_ext_expr (spec_error_1 a1)) (@Some out oo) ->
        abort oo ->
        not (abort_intercepted_expr (spec_error_1 a1)) ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq ext_expr exte (spec_error_1 a1) -> @eq out o oo -> P S C a1 oo) ->
       (red_expr S C (spec_error_1 a1) oo ->
        forall (S0 S1 : state) (C0 : execution_ctx) (l : object_loc),
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq out (out_ter S1 (res_val (value_object l))) a1 ->
        @eq out (out_ter S1 (res_throw (resvalue_value (value_object l)))) oo ->
        P S C (out_ter S1 (res_val (value_object l)))
          (out_ter S1 (res_throw (resvalue_value (value_object l))))) ->
       red_expr S C (spec_error_1 a1) oo -> P S C a1 oo.

Parameter inv_red_expr_spec_error_or_cst
     : forall (S : state) (C : execution_ctx) (a1 : bool) 
         (a2 : native_error) (a3 : value) (oo : out)
         (P : state ->
              execution_ctx -> bool -> native_error -> value -> out -> Prop),
       (red_expr S C (spec_error_or_cst a1 a2 a3) oo ->
        forall (S0 : state) (C0 : execution_ctx) (exte : ext_expr) (o : out),
        @eq (option out) (out_of_ext_expr (spec_error_or_cst a1 a2 a3))
          (@Some out oo) ->
        abort oo ->
        not (abort_intercepted_expr (spec_error_or_cst a1 a2 a3)) ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq ext_expr exte (spec_error_or_cst a1 a2 a3) ->
        @eq out o oo -> P S C a1 a2 a3 oo) ->
       (red_expr S C (spec_error_or_cst a1 a2 a3) oo ->
        forall (S0 : state) (C0 : execution_ctx) (ne : native_error)
          (v : value) (o : out),
        red_expr S C (spec_error a2) oo ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq bool true a1 ->
        @eq native_error ne a2 ->
        @eq value v a3 -> @eq out o oo -> P S C true a2 a3 oo) ->
       (red_expr S C (spec_error_or_cst a1 a2 a3) oo ->
        forall (S0 : state) (C0 : execution_ctx) (ne : native_error)
          (v : value),
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq bool false a1 ->
        @eq native_error ne a2 ->
        @eq value v a3 ->
        @eq out (out_ter S (res_val a3)) oo ->
        P S C false a2 a3 (out_ter S (res_val a3))) ->
       red_expr S C (spec_error_or_cst a1 a2 a3) oo -> P S C a1 a2 a3 oo.

Parameter inv_red_expr_spec_error_or_void
     : forall (S : state) (C : execution_ctx) (a1 : bool) 
         (a2 : native_error) (oo : out)
         (P : state -> execution_ctx -> bool -> native_error -> out -> Prop),
       (red_expr S C (spec_error_or_void a1 a2) oo ->
        forall (S0 : state) (C0 : execution_ctx) (exte : ext_expr) (o : out),
        @eq (option out) (out_of_ext_expr (spec_error_or_void a1 a2))
          (@Some out oo) ->
        abort oo ->
        not (abort_intercepted_expr (spec_error_or_void a1 a2)) ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq ext_expr exte (spec_error_or_void a1 a2) ->
        @eq out o oo -> P S C a1 a2 oo) ->
       (red_expr S C (spec_error_or_void a1 a2) oo ->
        forall (S0 : state) (C0 : execution_ctx) (ne : native_error)
          (o : out),
        red_expr S C (spec_error a2) oo ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq bool true a1 ->
        @eq native_error ne a2 -> @eq out o oo -> P S C true a2 oo) ->
       (red_expr S C (spec_error_or_void a1 a2) oo ->
        forall (S0 : state) (C0 : execution_ctx) (ne : native_error),
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq bool false a1 ->
        @eq native_error ne a2 ->
        @eq out (out_void S) oo -> P S C false a2 (out_void S)) ->
       red_expr S C (spec_error_or_void a1 a2) oo -> P S C a1 a2 oo.

Parameter inv_red_expr_spec_init_throw_type_error
     : forall (S : state) (C : execution_ctx) (oo : out)
         (P : state -> execution_ctx -> out -> Prop),
       (red_expr S C spec_init_throw_type_error oo ->
        forall (S0 : state) (C0 : execution_ctx) (exte : ext_expr) (o : out),
        @eq (option out) (out_of_ext_expr spec_init_throw_type_error)
          (@Some out oo) ->
        abort oo ->
        not (abort_intercepted_expr spec_init_throw_type_error) ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq ext_expr exte spec_init_throw_type_error ->
        @eq out o oo -> P S C oo) ->
       red_expr S C spec_init_throw_type_error oo -> P S C oo.

Parameter inv_red_expr_spec_init_throw_type_error_1
     : forall (S : state) (C : execution_ctx) (a1 oo : out)
         (P : state -> execution_ctx -> out -> out -> Prop),
       (red_expr S C (spec_init_throw_type_error_1 a1) oo ->
        forall (S0 : state) (C0 : execution_ctx) (exte : ext_expr) (o : out),
        @eq (option out) (out_of_ext_expr (spec_init_throw_type_error_1 a1))
          (@Some out oo) ->
        abort oo ->
        not (abort_intercepted_expr (spec_init_throw_type_error_1 a1)) ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq ext_expr exte (spec_init_throw_type_error_1 a1) ->
        @eq out o oo -> P S C a1 oo) ->
       red_expr S C (spec_init_throw_type_error_1 a1) oo -> P S C a1 oo.

Parameter inv_red_expr_spec_build_error
     : forall (S : state) (C : execution_ctx) (a1 a2 : value) 
         (oo : out)
         (P : state -> execution_ctx -> value -> value -> out -> Prop),
       (red_expr S C (spec_build_error a1 a2) oo ->
        forall (S0 : state) (C0 : execution_ctx) (exte : ext_expr) (o : out),
        @eq (option out) (out_of_ext_expr (spec_build_error a1 a2))
          (@Some out oo) ->
        abort oo ->
        not (abort_intercepted_expr (spec_build_error a1 a2)) ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq ext_expr exte (spec_build_error a1 a2) ->
        @eq out o oo -> P S C a1 a2 oo) ->
       (red_expr S C (spec_build_error a1 a2) oo ->
        forall (S0 : state) (C0 : execution_ctx) (O : object)
          (vproto vmsg : value) (l : object_loc) (S' : state) 
          (o : out),
        @eq object O
          (object_new a1
             (String (Ascii true false true false false false true false)
                (String (Ascii false true false false true true true false)
                   (String
                      (Ascii false true false false true true true false)
                      (String
                         (Ascii true true true true false true true false)
                         (String
                            (Ascii false true false false true true true
                               false) EmptyString)))))) ->
        @eq (prod object_loc state) (@pair object_loc state l S')
          (object_alloc S O) ->
        red_expr S' C (spec_build_error_1 l a2) oo ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq value vproto a1 ->
        @eq value vmsg a2 -> @eq out o oo -> P S C a1 a2 oo) ->
       red_expr S C (spec_build_error a1 a2) oo -> P S C a1 a2 oo.

Parameter inv_red_expr_spec_build_error_1
     : forall (S : state) (C : execution_ctx) (a1 : object_loc) 
         (a2 : value) (oo : out)
         (P : state -> execution_ctx -> object_loc -> value -> out -> Prop),
       (red_expr S C (spec_build_error_1 a1 a2) oo ->
        forall (S0 : state) (C0 : execution_ctx) (exte : ext_expr) (o : out),
        @eq (option out) (out_of_ext_expr (spec_build_error_1 a1 a2))
          (@Some out oo) ->
        abort oo ->
        not (abort_intercepted_expr (spec_build_error_1 a1 a2)) ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq ext_expr exte (spec_build_error_1 a1 a2) ->
        @eq out o oo -> P S C a1 a2 oo) ->
       (red_expr S C (spec_build_error_1 a1 a2) oo ->
        forall (S0 : state) (C0 : execution_ctx) (l : object_loc)
          (vmsg : value),
        @eq value a2 (value_prim prim_undef) ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq object_loc l a1 ->
        @eq value vmsg a2 ->
        @eq out (out_ter S (res_val (value_object a1))) oo ->
        P S C a1 a2 (out_ter S (res_val (value_object a1)))) ->
       (red_expr S C (spec_build_error_1 a1 a2) oo ->
        forall (S0 : state) (C0 : execution_ctx) (l : object_loc)
          (vmsg : value) (o1 o : out),
        not (@eq value a2 (value_prim prim_undef)) ->
        red_expr S C (spec_to_string a2) o1 ->
        red_expr S C (spec_build_error_2 a1 o1) oo ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq object_loc l a1 ->
        @eq value vmsg a2 -> @eq out o oo -> P S C a1 a2 oo) ->
       red_expr S C (spec_build_error_1 a1 a2) oo -> P S C a1 a2 oo.

Parameter inv_red_expr_spec_build_error_2
     : forall (S : state) (C : execution_ctx) (a1 : object_loc) 
         (a2 oo : out)
         (P : state -> execution_ctx -> object_loc -> out -> out -> Prop),
       (red_expr S C (spec_build_error_2 a1 a2) oo ->
        forall (S0 : state) (C0 : execution_ctx) (exte : ext_expr) (o : out),
        @eq (option out) (out_of_ext_expr (spec_build_error_2 a1 a2))
          (@Some out oo) ->
        abort oo ->
        not (abort_intercepted_expr (spec_build_error_2 a1 a2)) ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq ext_expr exte (spec_build_error_2 a1 a2) ->
        @eq out o oo -> P S C a1 a2 oo) ->
       (red_expr S C (spec_build_error_2 a1 a2) oo ->
        forall (S0 S1 S' : state) (C0 : execution_ctx) 
          (l : object_loc) (smsg : value),
        object_set_property S1 a1
          (String (Ascii true false true true false true true false)
             (String (Ascii true false true false false true true false)
                (String (Ascii true true false false true true true false)
                   (String (Ascii true true false false true true true false)
                      (String
                         (Ascii true false false false false true true false)
                         (String
                            (Ascii true true true false false true true false)
                            (String
                               (Ascii true false true false false true true
                                  false) EmptyString)))))))
          (attributes_data_of (attributes_data_intro smsg true false true))
          S' ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq object_loc l a1 ->
        @eq out (out_ter S1 (res_val smsg)) a2 ->
        @eq out (out_ter S' (res_val (value_object a1))) oo ->
        P S C a1 (out_ter S1 (res_val smsg))
          (out_ter S' (res_val (value_object a1)))) ->
       red_expr S C (spec_build_error_2 a1 a2) oo -> P S C a1 a2 oo.

Parameter inv_red_expr_spec_new_object
     : forall (S : state) (C : execution_ctx) (a1 : object_loc -> ext_expr)
         (oo : out)
         (P : state ->
              execution_ctx -> (object_loc -> ext_expr) -> out -> Prop),
       (red_expr S C (spec_new_object a1) oo ->
        forall (S0 : state) (C0 : execution_ctx) (exte : ext_expr) (o : out),
        @eq (option out) (out_of_ext_expr (spec_new_object a1))
          (@Some out oo) ->
        abort oo ->
        not (abort_intercepted_expr (spec_new_object a1)) ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq ext_expr exte (spec_new_object a1) -> @eq out o oo -> P S C a1 oo) ->
       red_expr S C (spec_new_object a1) oo -> P S C a1 oo.

Parameter inv_red_expr_spec_new_object_1
     : forall (S : state) (C : execution_ctx) (a1 : out)
         (a2 : object_loc -> ext_expr) (oo : out)
         (P : state ->
              execution_ctx -> out -> (object_loc -> ext_expr) -> out -> Prop),
       (red_expr S C (spec_new_object_1 a1 a2) oo ->
        forall (S0 : state) (C0 : execution_ctx) (exte : ext_expr) (o : out),
        @eq (option out) (out_of_ext_expr (spec_new_object_1 a1 a2))
          (@Some out oo) ->
        abort oo ->
        not (abort_intercepted_expr (spec_new_object_1 a1 a2)) ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq ext_expr exte (spec_new_object_1 a1 a2) ->
        @eq out o oo -> P S C a1 a2 oo) ->
       red_expr S C (spec_new_object_1 a1 a2) oo -> P S C a1 a2 oo.

Parameter inv_red_expr_spec_creating_function_object_proto
     : forall (S : state) (C : execution_ctx) (a1 : object_loc) 
         (oo : out) (P : state -> execution_ctx -> object_loc -> out -> Prop),
       (red_expr S C (spec_creating_function_object_proto a1) oo ->
        forall (S0 : state) (C0 : execution_ctx) (exte : ext_expr) (o : out),
        @eq (option out)
          (out_of_ext_expr (spec_creating_function_object_proto a1))
          (@Some out oo) ->
        abort oo ->
        not (abort_intercepted_expr (spec_creating_function_object_proto a1)) ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq ext_expr exte (spec_creating_function_object_proto a1) ->
        @eq out o oo -> P S C a1 oo) ->
       (red_expr S C (spec_creating_function_object_proto a1) oo ->
        forall (S0 : state) (C0 : execution_ctx) (l : object_loc)
          (o1 o : out),
        red_expr S C (spec_construct_prealloc prealloc_object (@nil value))
          o1 ->
        red_expr S C (spec_creating_function_object_proto_1 a1 o1) oo ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq object_loc l a1 -> @eq out o oo -> P S C a1 oo) ->
       red_expr S C (spec_creating_function_object_proto a1) oo ->
       P S C a1 oo.

Parameter inv_red_expr_spec_creating_function_object
     : forall (S : state) (C : execution_ctx) (a1 : list string)
         (a2 : funcbody) (a3 : lexical_env) (a4 : strictness_flag) 
         (oo : out)
         (P : state ->
              execution_ctx ->
              list string -> funcbody -> list nat -> bool -> out -> Prop),
       (red_expr S C (spec_creating_function_object a1 a2 a3 a4) oo ->
        forall (S0 : state) (C0 : execution_ctx) (exte : ext_expr) (o : out),
        @eq (option out)
          (out_of_ext_expr (spec_creating_function_object a1 a2 a3 a4))
          (@Some out oo) ->
        abort oo ->
        not
          (abort_intercepted_expr (spec_creating_function_object a1 a2 a3 a4)) ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq ext_expr exte (spec_creating_function_object a1 a2 a3 a4) ->
        @eq out o oo -> P S C a1 a2 a3 a4 oo) ->
       (red_expr S C (spec_creating_function_object a1 a2 a3 a4) oo ->
        forall (S0 : state) (C0 : execution_ctx) (S' : state)
          (O O1 O2 O3 : object) (A : attributes) (l : object_loc)
          (names : list string) (bd : funcbody) (X : lexical_env)
          (str : strictness_flag) (o1 o : out),
        @eq object O
          (object_new
             (value_object (object_loc_prealloc prealloc_function_proto))
             (String (Ascii false true true false false false true false)
                (String (Ascii true false true false true true true false)
                   (String (Ascii false true true true false true true false)
                      (String
                         (Ascii true true false false false true true false)
                         (String
                            (Ascii false false true false true true true
                               false)
                            (String
                               (Ascii true false false true false true true
                                  false)
                               (String
                                  (Ascii true true true true false true true
                                     false)
                                  (String
                                     (Ascii false true true true false true
                                        true false) EmptyString))))))))) ->
        @eq object O1 (object_with_get O builtin_get_function) ->
        @eq object O2
          (object_with_invokation O1 (@Some construct construct_default)
             (@Some call call_default)
             (@Some builtin_has_instance builtin_has_instance_function)) ->
        @eq object O3
          (object_with_details O2 (@Some lexical_env a3)
             (@Some (list string) a1) (@Some funcbody a2) 
             (@None object_loc) (@None value) (@None (list value))
             (@None object_loc)) ->
        @eq (prod object_loc state) (@pair object_loc state l S')
          (object_alloc S O3) ->
        @eq attributes A
          (attributes_data_of
             (attributes_data_intro
                (value_prim
                   (prim_number
                      (JsNumber.of_int (my_Z_of_nat (@length string a1)))))
                false false false)) ->
        red_expr S' C
          (spec_object_define_own_prop l
             (String (Ascii false false true true false true true false)
                (String (Ascii true false true false false true true false)
                   (String (Ascii false true true true false true true false)
                      (String
                         (Ascii true true true false false true true false)
                         (String
                            (Ascii false false true false true true true
                               false)
                            (String
                               (Ascii false false false true false true true
                                  false) EmptyString))))))
             (descriptor_of_attributes A) false) o1 ->
        red_expr S' C (spec_creating_function_object_1 a4 l o1) oo ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq (list string) names a1 ->
        @eq funcbody bd a2 ->
        @eq lexical_env X a3 ->
        @eq strictness_flag str a4 -> @eq out o oo -> P S C a1 a2 a3 a4 oo) ->
       red_expr S C (spec_creating_function_object a1 a2 a3 a4) oo ->
       P S C a1 a2 a3 a4 oo.

Parameter inv_red_expr_spec_creating_function_object_1
     : forall (S : state) (C : execution_ctx) (a1 : strictness_flag)
         (a2 : object_loc) (a3 oo : out)
         (P : state ->
              execution_ctx -> bool -> object_loc -> out -> out -> Prop),
       (red_expr S C (spec_creating_function_object_1 a1 a2 a3) oo ->
        forall (S0 : state) (C0 : execution_ctx) (exte : ext_expr) (o : out),
        @eq (option out)
          (out_of_ext_expr (spec_creating_function_object_1 a1 a2 a3))
          (@Some out oo) ->
        abort oo ->
        not
          (abort_intercepted_expr (spec_creating_function_object_1 a1 a2 a3)) ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq ext_expr exte (spec_creating_function_object_1 a1 a2 a3) ->
        @eq out o oo -> P S C a1 a2 a3 oo) ->
       (red_expr S C (spec_creating_function_object_1 a1 a2 a3) oo ->
        forall (S0 S1 : state) (C0 : execution_ctx) 
          (str : strictness_flag) (l : object_loc) 
          (b : bool) (o1 o : out),
        red_expr S1 C (spec_creating_function_object_proto a2) o1 ->
        red_expr S1 C (spec_creating_function_object_2 a1 a2 o1) oo ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq strictness_flag str a1 ->
        @eq object_loc l a2 ->
        @eq out (out_ter S1 (res_val (value_prim (prim_bool b)))) a3 ->
        @eq out o oo ->
        P S C a1 a2 (out_ter S1 (res_val (value_prim (prim_bool b)))) oo) ->
       red_expr S C (spec_creating_function_object_1 a1 a2 a3) oo ->
       P S C a1 a2 a3 oo.

Parameter inv_red_expr_spec_creating_function_object_2
     : forall (S : state) (C : execution_ctx) (a1 : strictness_flag)
         (a2 : object_loc) (a3 oo : out)
         (P : state ->
              execution_ctx -> bool -> object_loc -> out -> out -> Prop),
       (red_expr S C (spec_creating_function_object_2 a1 a2 a3) oo ->
        forall (S0 : state) (C0 : execution_ctx) (exte : ext_expr) (o : out),
        @eq (option out)
          (out_of_ext_expr (spec_creating_function_object_2 a1 a2 a3))
          (@Some out oo) ->
        abort oo ->
        not
          (abort_intercepted_expr (spec_creating_function_object_2 a1 a2 a3)) ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq ext_expr exte (spec_creating_function_object_2 a1 a2 a3) ->
        @eq out o oo -> P S C a1 a2 a3 oo) ->
       (red_expr S C (spec_creating_function_object_2 a1 a2 a3) oo ->
        forall (S0 S1 : state) (C0 : execution_ctx) 
          (l : object_loc) (b : bool),
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq strictness_flag false a1 ->
        @eq object_loc l a2 ->
        @eq out (out_ter S1 (res_val (value_prim (prim_bool b)))) a3 ->
        @eq out (out_ter S1 (res_val (value_object a2))) oo ->
        P S C false a2 (out_ter S1 (res_val (value_prim (prim_bool b))))
          (out_ter S1 (res_val (value_object a2)))) ->
       (red_expr S C (spec_creating_function_object_2 a1 a2 a3) oo ->
        forall (S0 S1 : state) (C0 : execution_ctx) 
          (vthrower : value) (A : attributes) (l : object_loc) 
          (b : bool) (o1 o : out),
        @eq value vthrower
          (value_object (object_loc_prealloc prealloc_throw_type_error)) ->
        @eq attributes A
          (attributes_accessor_of
             (attributes_accessor_intro vthrower vthrower false false)) ->
        red_expr S1 C
          (spec_object_define_own_prop a2
             (String (Ascii true true false false false true true false)
                (String (Ascii true false false false false true true false)
                   (String
                      (Ascii false false true true false true true false)
                      (String
                         (Ascii false false true true false true true false)
                         (String
                            (Ascii true false true false false true true
                               false)
                            (String
                               (Ascii false true false false true true true
                                  false) EmptyString))))))
             (descriptor_of_attributes A) false) o1 ->
        red_expr S1 C (spec_creating_function_object_3 a2 o1) oo ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq strictness_flag true a1 ->
        @eq object_loc l a2 ->
        @eq out (out_ter S1 (res_val (value_prim (prim_bool b)))) a3 ->
        @eq out o oo ->
        P S C true a2 (out_ter S1 (res_val (value_prim (prim_bool b)))) oo) ->
       red_expr S C (spec_creating_function_object_2 a1 a2 a3) oo ->
       P S C a1 a2 a3 oo.

Parameter inv_red_expr_spec_creating_function_object_3
     : forall (S : state) (C : execution_ctx) (a1 : object_loc) 
         (a2 oo : out)
         (P : state -> execution_ctx -> object_loc -> out -> out -> Prop),
       (red_expr S C (spec_creating_function_object_3 a1 a2) oo ->
        forall (S0 : state) (C0 : execution_ctx) (exte : ext_expr) (o : out),
        @eq (option out)
          (out_of_ext_expr (spec_creating_function_object_3 a1 a2))
          (@Some out oo) ->
        abort oo ->
        not (abort_intercepted_expr (spec_creating_function_object_3 a1 a2)) ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq ext_expr exte (spec_creating_function_object_3 a1 a2) ->
        @eq out o oo -> P S C a1 a2 oo) ->
       (red_expr S C (spec_creating_function_object_3 a1 a2) oo ->
        forall (S0 S1 : state) (C0 : execution_ctx) 
          (vthrower : value) (A : attributes) (l : object_loc) 
          (b : bool) (o1 o : out),
        @eq value vthrower
          (value_object (object_loc_prealloc prealloc_throw_type_error)) ->
        @eq attributes A
          (attributes_accessor_of
             (attributes_accessor_intro vthrower vthrower false false)) ->
        red_expr S1 C
          (spec_object_define_own_prop a1
             (String (Ascii true false false false false true true false)
                (String (Ascii false true false false true true true false)
                   (String (Ascii true true true false false true true false)
                      (String
                         (Ascii true false true false true true true false)
                         (String
                            (Ascii true false true true false true true false)
                            (String
                               (Ascii true false true false false true true
                                  false)
                               (String
                                  (Ascii false true true true false true true
                                     false)
                                  (String
                                     (Ascii false false true false true true
                                        true false)
                                     (String
                                        (Ascii true true false false true
                                           true true false) EmptyString)))))))))
             (descriptor_of_attributes A) false) o1 ->
        red_expr S1 C (spec_creating_function_object_4 a1 o1) oo ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq object_loc l a1 ->
        @eq out (out_ter S1 (res_val (value_prim (prim_bool b)))) a2 ->
        @eq out o oo ->
        P S C a1 (out_ter S1 (res_val (value_prim (prim_bool b)))) oo) ->
       red_expr S C (spec_creating_function_object_3 a1 a2) oo ->
       P S C a1 a2 oo.

Parameter inv_red_expr_spec_creating_function_object_4
     : forall (S : state) (C : execution_ctx) (a1 : object_loc) 
         (a2 oo : out)
         (P : state -> execution_ctx -> object_loc -> out -> out -> Prop),
       (red_expr S C (spec_creating_function_object_4 a1 a2) oo ->
        forall (S0 : state) (C0 : execution_ctx) (exte : ext_expr) (o : out),
        @eq (option out)
          (out_of_ext_expr (spec_creating_function_object_4 a1 a2))
          (@Some out oo) ->
        abort oo ->
        not (abort_intercepted_expr (spec_creating_function_object_4 a1 a2)) ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq ext_expr exte (spec_creating_function_object_4 a1 a2) ->
        @eq out o oo -> P S C a1 a2 oo) ->
       (red_expr S C (spec_creating_function_object_4 a1 a2) oo ->
        forall (S0 S1 : state) (C0 : execution_ctx) 
          (l : object_loc) (b : bool),
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq object_loc l a1 ->
        @eq out (out_ter S1 (res_val (value_prim (prim_bool b)))) a2 ->
        @eq out (out_ter S1 (res_val (value_object a1))) oo ->
        P S C a1 (out_ter S1 (res_val (value_prim (prim_bool b))))
          (out_ter S1 (res_val (value_object a1)))) ->
       red_expr S C (spec_creating_function_object_4 a1 a2) oo ->
       P S C a1 a2 oo.

Parameter inv_red_expr_spec_function_proto_apply
     : forall (S : state) (C : execution_ctx) (a1 : object_loc)
         (a2 a3 : value) (oo : out)
         (P : state ->
              execution_ctx -> object_loc -> value -> value -> out -> Prop),
       (red_expr S C (spec_function_proto_apply a1 a2 a3) oo ->
        forall (S0 : state) (C0 : execution_ctx) (exte : ext_expr) (o : out),
        @eq (option out)
          (out_of_ext_expr (spec_function_proto_apply a1 a2 a3))
          (@Some out oo) ->
        abort oo ->
        not (abort_intercepted_expr (spec_function_proto_apply a1 a2 a3)) ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq ext_expr exte (spec_function_proto_apply a1 a2 a3) ->
        @eq out o oo -> P S C a1 a2 a3 oo) ->
       (red_expr S C (spec_function_proto_apply a1 a2 a3) oo ->
        forall (S0 : state) (C0 : execution_ctx) (func : object_loc)
          (thisArg argArray : value) (o : out),
        Logic.or (@eq value a3 (value_prim prim_null))
          (@eq value a3 (value_prim prim_undef)) ->
        red_expr S C (spec_call a1 a2 (@nil value)) oo ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq object_loc func a1 ->
        @eq value thisArg a2 ->
        @eq value argArray a3 -> @eq out o oo -> P S C a1 a2 a3 oo) ->
       (red_expr S C (spec_function_proto_apply a1 a2 a3) oo ->
        forall (S0 : state) (C0 : execution_ctx) (func : object_loc)
          (thisArg argArray : value) (array : object_loc) 
          (o : out),
        Logic.and (not (@eq value a3 (value_prim prim_null)))
          (Logic.and (not (@eq value a3 (value_prim prim_undef)))
             (not (@eq value a3 (value_object array)))) ->
        red_expr S C (spec_error native_error_type) oo ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq object_loc func a1 ->
        @eq value thisArg a2 ->
        @eq value argArray a3 -> @eq out o oo -> P S C a1 a2 a3 oo) ->
       (red_expr S C (spec_function_proto_apply a1 a2 a3) oo ->
        forall (S0 : state) (C0 : execution_ctx) (func : object_loc)
          (thisArg argArray : value) (array : object_loc) 
          (o1 o : out),
        @eq value a3 (value_object array) ->
        red_expr S C
          (spec_object_get array
             (String (Ascii false false true true false true true false)
                (String (Ascii true false true false false true true false)
                   (String (Ascii false true true true false true true false)
                      (String
                         (Ascii true true true false false true true false)
                         (String
                            (Ascii false false true false true true true
                               false)
                            (String
                               (Ascii false false false true false true true
                                  false) EmptyString))))))) o1 ->
        red_expr S C (spec_function_proto_apply_1 a1 a2 array o1) oo ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq object_loc func a1 ->
        @eq value thisArg a2 ->
        @eq value argArray a3 -> @eq out o oo -> P S C a1 a2 a3 oo) ->
       red_expr S C (spec_function_proto_apply a1 a2 a3) oo ->
       P S C a1 a2 a3 oo.

Parameter inv_red_expr_spec_function_proto_apply_1
     : forall (S : state) (C : execution_ctx) (a1 : object_loc) 
         (a2 : value) (a3 : object_loc) (a4 oo : out)
         (P : state ->
              execution_ctx ->
              object_loc -> value -> object_loc -> out -> out -> Prop),
       (red_expr S C (spec_function_proto_apply_1 a1 a2 a3 a4) oo ->
        forall (S0 : state) (C0 : execution_ctx) (exte : ext_expr) (o : out),
        @eq (option out)
          (out_of_ext_expr (spec_function_proto_apply_1 a1 a2 a3 a4))
          (@Some out oo) ->
        abort oo ->
        not
          (abort_intercepted_expr (spec_function_proto_apply_1 a1 a2 a3 a4)) ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq ext_expr exte (spec_function_proto_apply_1 a1 a2 a3 a4) ->
        @eq out o oo -> P S C a1 a2 a3 a4 oo) ->
       (red_expr S C (spec_function_proto_apply_1 a1 a2 a3 a4) oo ->
        forall (S0 S' : state) (C0 : execution_ctx) 
          (func : object_loc) (thisArg : value) (array : object_loc)
          (v : value) (y : specret Z) (o : out),
        @red_spec Z S' C (spec_to_uint32 v) y ->
        red_expr S' C (spec_function_proto_apply_2 a1 a2 a3 y) oo ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq object_loc func a1 ->
        @eq value thisArg a2 ->
        @eq object_loc array a3 ->
        @eq out (out_ter S' (res_val v)) a4 ->
        @eq out o oo -> P S C a1 a2 a3 (out_ter S' (res_val v)) oo) ->
       red_expr S C (spec_function_proto_apply_1 a1 a2 a3 a4) oo ->
       P S C a1 a2 a3 a4 oo.

Parameter inv_red_expr_spec_function_proto_apply_2
     : forall (S : state) (C : execution_ctx) (a1 : object_loc) 
         (a2 : value) (a3 : object_loc) (a4 : specret Z) 
         (oo : out)
         (P : state ->
              execution_ctx ->
              object_loc -> value -> object_loc -> specret Z -> out -> Prop),
       (red_expr S C (spec_function_proto_apply_2 a1 a2 a3 a4) oo ->
        forall (S0 : state) (C0 : execution_ctx) (exte : ext_expr) (o : out),
        @eq (option out)
          (out_of_ext_expr (spec_function_proto_apply_2 a1 a2 a3 a4))
          (@Some out oo) ->
        abort oo ->
        not
          (abort_intercepted_expr (spec_function_proto_apply_2 a1 a2 a3 a4)) ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq ext_expr exte (spec_function_proto_apply_2 a1 a2 a3 a4) ->
        @eq out o oo -> P S C a1 a2 a3 a4 oo) ->
       (red_expr S C (spec_function_proto_apply_2 a1 a2 a3 a4) oo ->
        forall (S0 S' : state) (C0 : execution_ctx) 
          (func : object_loc) (thisArg : value) (array : object_loc)
          (ilen : Z) (y : specret (list value)) (o : out),
        @red_spec (list value) S' C
          (spec_function_proto_apply_get_args a3 Z0 ilen) y ->
        red_expr S' C (spec_function_proto_apply_3 a1 a2 y) oo ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq object_loc func a1 ->
        @eq value thisArg a2 ->
        @eq object_loc array a3 ->
        @eq (specret Z) (@ret Z S' ilen) a4 ->
        @eq out o oo -> P S C a1 a2 a3 (@ret Z S' ilen) oo) ->
       red_expr S C (spec_function_proto_apply_2 a1 a2 a3 a4) oo ->
       P S C a1 a2 a3 a4 oo.

Parameter inv_red_expr_spec_function_proto_apply_3
     : forall (S : state) (C : execution_ctx) (a1 : object_loc) 
         (a2 : value) (a3 : specret (list value)) (oo : out)
         (P : state ->
              execution_ctx ->
              object_loc -> value -> specret (list value) -> out -> Prop),
       (red_expr S C (spec_function_proto_apply_3 a1 a2 a3) oo ->
        forall (S0 : state) (C0 : execution_ctx) (exte : ext_expr) (o : out),
        @eq (option out)
          (out_of_ext_expr (spec_function_proto_apply_3 a1 a2 a3))
          (@Some out oo) ->
        abort oo ->
        not (abort_intercepted_expr (spec_function_proto_apply_3 a1 a2 a3)) ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq ext_expr exte (spec_function_proto_apply_3 a1 a2 a3) ->
        @eq out o oo -> P S C a1 a2 a3 oo) ->
       (red_expr S C (spec_function_proto_apply_3 a1 a2 a3) oo ->
        forall (S0 S' : state) (C0 : execution_ctx) 
          (func : object_loc) (thisArg : value) (argList : list value)
          (o : out),
        red_expr S' C (spec_call a1 a2 argList) oo ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq object_loc func a1 ->
        @eq value thisArg a2 ->
        @eq (specret (list value)) (@ret (list value) S' argList) a3 ->
        @eq out o oo -> P S C a1 a2 (@ret (list value) S' argList) oo) ->
       red_expr S C (spec_function_proto_apply_3 a1 a2 a3) oo ->
       P S C a1 a2 a3 oo.

Parameter inv_red_expr_spec_function_proto_bind_1
     : forall (S : state) (C : execution_ctx) (a1 : object_loc) 
         (a2 : value) (a3 : list value) (oo : out)
         (P : state ->
              execution_ctx ->
              object_loc -> value -> list value -> out -> Prop),
       (red_expr S C (spec_function_proto_bind_1 a1 a2 a3) oo ->
        forall (S0 : state) (C0 : execution_ctx) (exte : ext_expr) (o : out),
        @eq (option out)
          (out_of_ext_expr (spec_function_proto_bind_1 a1 a2 a3))
          (@Some out oo) ->
        abort oo ->
        not (abort_intercepted_expr (spec_function_proto_bind_1 a1 a2 a3)) ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq ext_expr exte (spec_function_proto_bind_1 a1 a2 a3) ->
        @eq out o oo -> P S C a1 a2 a3 oo) ->
       (red_expr S C (spec_function_proto_bind_1 a1 a2 a3) oo ->
        forall (S0 S' : state) (C0 : execution_ctx) 
          (l target : object_loc) (thisArg : value) 
          (A : list value) (O1 O2 O3 O4 O5 O6 O7 : object) 
          (o : out),
        @eq object O1
          (object_new
             (value_object (object_loc_prealloc prealloc_object_proto))
             (String (Ascii true true true true false false true false)
                (String (Ascii false true false false false true true false)
                   (String
                      (Ascii false true false true false true true false)
                      (String
                         (Ascii true false true false false true true false)
                         (String
                            (Ascii true true false false false true true
                               false)
                            (String
                               (Ascii false false true false true true true
                                  false) EmptyString))))))) ->
        @eq object O2 (object_with_get O1 builtin_get_function) ->
        @eq object O3
          (object_with_details O2 (@None lexical_env) 
             (@None (list string)) (@None funcbody) 
             (@Some object_loc a1) (@Some value a2) 
             (@Some (list value) a3) (@None object_loc)) ->
        @eq object O4
          (object_set_class O3
             (String (Ascii false true true false false false true false)
                (String (Ascii true false true false true true true false)
                   (String (Ascii false true true true false true true false)
                      (String
                         (Ascii true true false false false true true false)
                         (String
                            (Ascii false false true false true true true
                               false)
                            (String
                               (Ascii true false false true false true true
                                  false)
                               (String
                                  (Ascii true true true true false true true
                                     false)
                                  (String
                                     (Ascii false true true true false true
                                        true false) EmptyString))))))))) ->
        @eq object O5
          (object_set_proto O4
             (value_object (object_loc_prealloc prealloc_function_proto))) ->
        @eq object O6
          (object_with_invokation O5 (@Some construct construct_after_bind)
             (@Some call call_after_bind)
             (@Some builtin_has_instance builtin_has_instance_after_bind)) ->
        @eq object O7 (object_set_extensible O6 true) ->
        @eq (prod object_loc state) (@pair object_loc state l S')
          (object_alloc S O7) ->
        red_expr S' C (spec_function_proto_bind_2 l (value_object a1) a3) oo ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq object_loc target a1 ->
        @eq value thisArg a2 ->
        @eq (list value) A a3 -> @eq out o oo -> P S C a1 a2 a3 oo) ->
       red_expr S C (spec_function_proto_bind_1 a1 a2 a3) oo ->
       P S C a1 a2 a3 oo.

Parameter inv_red_expr_spec_function_proto_bind_2
     : forall (S : state) (C : execution_ctx) (a1 : object_loc) 
         (a2 : value) (a3 : list value) (oo : out)
         (P : state ->
              execution_ctx ->
              object_loc -> value -> list value -> out -> Prop),
       (red_expr S C (spec_function_proto_bind_2 a1 a2 a3) oo ->
        forall (S0 : state) (C0 : execution_ctx) (exte : ext_expr) (o : out),
        @eq (option out)
          (out_of_ext_expr (spec_function_proto_bind_2 a1 a2 a3))
          (@Some out oo) ->
        abort oo ->
        not (abort_intercepted_expr (spec_function_proto_bind_2 a1 a2 a3)) ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq ext_expr exte (spec_function_proto_bind_2 a1 a2 a3) ->
        @eq out o oo -> P S C a1 a2 a3 oo) ->
       (red_expr S C (spec_function_proto_bind_2 a1 a2 a3) oo ->
        forall (S0 : state) (C0 : execution_ctx) (l target : object_loc)
          (A : list value) (y : specret Z) (o : out),
        @red_spec Z S C (spec_function_proto_bind_length target a3) y ->
        red_expr S C (spec_function_proto_bind_3 a1 y) oo ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq object_loc l a1 ->
        @eq value (value_object target) a2 ->
        @eq (list value) A a3 ->
        @eq out o oo -> P S C a1 (value_object target) a3 oo) ->
       red_expr S C (spec_function_proto_bind_2 a1 a2 a3) oo ->
       P S C a1 a2 a3 oo.

Parameter inv_red_expr_spec_function_proto_bind_3
     : forall (S : state) (C : execution_ctx) (a1 : object_loc)
         (a2 : specret Z) (oo : out)
         (P : state ->
              execution_ctx -> object_loc -> specret Z -> out -> Prop),
       (red_expr S C (spec_function_proto_bind_3 a1 a2) oo ->
        forall (S0 : state) (C0 : execution_ctx) (exte : ext_expr) (o : out),
        @eq (option out) (out_of_ext_expr (spec_function_proto_bind_3 a1 a2))
          (@Some out oo) ->
        abort oo ->
        not (abort_intercepted_expr (spec_function_proto_bind_3 a1 a2)) ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq ext_expr exte (spec_function_proto_bind_3 a1 a2) ->
        @eq out o oo -> P S C a1 a2 oo) ->
       (red_expr S C (spec_function_proto_bind_3 a1 a2) oo ->
        forall (S0 S' : state) (C0 : execution_ctx) 
          (l : object_loc) (length : Z) (o : out),
        red_expr S' C (spec_function_proto_bind_4 a1 length) oo ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq object_loc l a1 ->
        @eq (specret Z) (@ret Z S' length) a2 ->
        @eq out o oo -> P S C a1 (@ret Z S' length) oo) ->
       red_expr S C (spec_function_proto_bind_3 a1 a2) oo -> P S C a1 a2 oo.

Parameter inv_red_expr_spec_function_proto_bind_4
     : forall (S : state) (C : execution_ctx) (a1 : object_loc) 
         (a2 : Z) (oo : out)
         (P : state -> execution_ctx -> object_loc -> Z -> out -> Prop),
       (red_expr S C (spec_function_proto_bind_4 a1 a2) oo ->
        forall (S0 : state) (C0 : execution_ctx) (exte : ext_expr) (o : out),
        @eq (option out) (out_of_ext_expr (spec_function_proto_bind_4 a1 a2))
          (@Some out oo) ->
        abort oo ->
        not (abort_intercepted_expr (spec_function_proto_bind_4 a1 a2)) ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq ext_expr exte (spec_function_proto_bind_4 a1 a2) ->
        @eq out o oo -> P S C a1 a2 oo) ->
       (red_expr S C (spec_function_proto_bind_4 a1 a2) oo ->
        forall (S0 S' : state) (C0 : execution_ctx) 
          (l : object_loc) (length : Z) (A : attributes) 
          (o : out),
        @eq attributes A
          (attributes_data_of
             (attributes_data_intro
                (value_prim (prim_number (JsNumber.of_int a2))) false false
                false)) ->
        object_set_property S a1
          (String (Ascii false false true true false true true false)
             (String (Ascii true false true false false true true false)
                (String (Ascii false true true true false true true false)
                   (String (Ascii true true true false false true true false)
                      (String
                         (Ascii false false true false true true true false)
                         (String
                            (Ascii false false false true false true true
                               false) EmptyString)))))) A S' ->
        red_expr S' C (spec_function_proto_bind_5 a1) oo ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq object_loc l a1 ->
        @eq Z length a2 -> @eq out o oo -> P S C a1 a2 oo) ->
       red_expr S C (spec_function_proto_bind_4 a1 a2) oo -> P S C a1 a2 oo.

Parameter inv_red_expr_spec_function_proto_bind_5
     : forall (S : state) (C : execution_ctx) (a1 : object_loc) 
         (oo : out) (P : state -> execution_ctx -> object_loc -> out -> Prop),
       (red_expr S C (spec_function_proto_bind_5 a1) oo ->
        forall (S0 : state) (C0 : execution_ctx) (exte : ext_expr) (o : out),
        @eq (option out) (out_of_ext_expr (spec_function_proto_bind_5 a1))
          (@Some out oo) ->
        abort oo ->
        not (abort_intercepted_expr (spec_function_proto_bind_5 a1)) ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq ext_expr exte (spec_function_proto_bind_5 a1) ->
        @eq out o oo -> P S C a1 oo) ->
       (red_expr S C (spec_function_proto_bind_5 a1) oo ->
        forall (S0 : state) (C0 : execution_ctx) (l : object_loc)
          (o o1 : out) (vthrower : value) (A : attributes),
        @eq value vthrower
          (value_object (object_loc_prealloc prealloc_throw_type_error)) ->
        @eq attributes A
          (attributes_accessor_of
             (attributes_accessor_intro vthrower vthrower false false)) ->
        red_expr S C
          (spec_object_define_own_prop a1
             (String (Ascii true true false false false true true false)
                (String (Ascii true false false false false true true false)
                   (String
                      (Ascii false false true true false true true false)
                      (String
                         (Ascii false false true true false true true false)
                         (String
                            (Ascii true false true false false true true
                               false)
                            (String
                               (Ascii false true false false true true true
                                  false) EmptyString))))))
             (descriptor_of_attributes A) false) o1 ->
        red_expr S C (spec_function_proto_bind_6 a1 o1) oo ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq object_loc l a1 -> @eq out o oo -> P S C a1 oo) ->
       red_expr S C (spec_function_proto_bind_5 a1) oo -> P S C a1 oo.

Parameter inv_red_expr_spec_function_proto_bind_6
     : forall (S : state) (C : execution_ctx) (a1 : object_loc) 
         (a2 oo : out)
         (P : state -> execution_ctx -> object_loc -> out -> out -> Prop),
       (red_expr S C (spec_function_proto_bind_6 a1 a2) oo ->
        forall (S0 : state) (C0 : execution_ctx) (exte : ext_expr) (o : out),
        @eq (option out) (out_of_ext_expr (spec_function_proto_bind_6 a1 a2))
          (@Some out oo) ->
        abort oo ->
        not (abort_intercepted_expr (spec_function_proto_bind_6 a1 a2)) ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq ext_expr exte (spec_function_proto_bind_6 a1 a2) ->
        @eq out o oo -> P S C a1 a2 oo) ->
       (red_expr S C (spec_function_proto_bind_6 a1 a2) oo ->
        forall (S0 S' : state) (C0 : execution_ctx) 
          (l : object_loc) (o o1 : out) (vthrower : value) 
          (A : attributes) (b : bool),
        @eq value vthrower
          (value_object (object_loc_prealloc prealloc_throw_type_error)) ->
        @eq attributes A
          (attributes_accessor_of
             (attributes_accessor_intro vthrower vthrower false false)) ->
        red_expr S' C
          (spec_object_define_own_prop a1
             (String (Ascii true false false false false true true false)
                (String (Ascii false true false false true true true false)
                   (String (Ascii true true true false false true true false)
                      (String
                         (Ascii true false true false true true true false)
                         (String
                            (Ascii true false true true false true true false)
                            (String
                               (Ascii true false true false false true true
                                  false)
                               (String
                                  (Ascii false true true true false true true
                                     false)
                                  (String
                                     (Ascii false false true false true true
                                        true false)
                                     (String
                                        (Ascii true true false false true
                                           true true false) EmptyString)))))))))
             (descriptor_of_attributes A) false) o1 ->
        red_expr S' C (spec_function_proto_bind_7 a1 o1) oo ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq object_loc l a1 ->
        @eq out (out_ter S' (res_val (value_prim (prim_bool b)))) a2 ->
        @eq out o oo ->
        P S C a1 (out_ter S' (res_val (value_prim (prim_bool b)))) oo) ->
       red_expr S C (spec_function_proto_bind_6 a1 a2) oo -> P S C a1 a2 oo.

Parameter inv_red_expr_spec_function_proto_bind_7
     : forall (S : state) (C : execution_ctx) (a1 : object_loc) 
         (a2 oo : out)
         (P : state -> execution_ctx -> object_loc -> out -> out -> Prop),
       (red_expr S C (spec_function_proto_bind_7 a1 a2) oo ->
        forall (S0 : state) (C0 : execution_ctx) (exte : ext_expr) (o : out),
        @eq (option out) (out_of_ext_expr (spec_function_proto_bind_7 a1 a2))
          (@Some out oo) ->
        abort oo ->
        not (abort_intercepted_expr (spec_function_proto_bind_7 a1 a2)) ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq ext_expr exte (spec_function_proto_bind_7 a1 a2) ->
        @eq out o oo -> P S C a1 a2 oo) ->
       (red_expr S C (spec_function_proto_bind_7 a1 a2) oo ->
        forall (S0 S' : state) (C0 : execution_ctx) 
          (l : object_loc) (b : bool),
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq object_loc l a1 ->
        @eq out (out_ter S' (res_val (value_prim (prim_bool b)))) a2 ->
        @eq out (out_ter S' (res_val (value_object a1))) oo ->
        P S C a1 (out_ter S' (res_val (value_prim (prim_bool b))))
          (out_ter S' (res_val (value_object a1)))) ->
       red_expr S C (spec_function_proto_bind_7 a1 a2) oo -> P S C a1 a2 oo.

Parameter inv_red_expr_spec_create_new_function_in
     : forall (S : state) (C a1 : execution_ctx) (a2 : list string)
         (a3 : funcbody) (oo : out)
         (P : state ->
              execution_ctx ->
              execution_ctx -> list string -> funcbody -> out -> Prop),
       (red_expr S C (spec_create_new_function_in a1 a2 a3) oo ->
        forall (S0 : state) (C0 : execution_ctx) (exte : ext_expr) (o : out),
        @eq (option out)
          (out_of_ext_expr (spec_create_new_function_in a1 a2 a3))
          (@Some out oo) ->
        abort oo ->
        not (abort_intercepted_expr (spec_create_new_function_in a1 a2 a3)) ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq ext_expr exte (spec_create_new_function_in a1 a2 a3) ->
        @eq out o oo -> P S C a1 a2 a3 oo) ->
       (red_expr S C (spec_create_new_function_in a1 a2 a3) oo ->
        forall (S0 : state) (C0 : execution_ctx) (args : list string)
          (bd : funcbody) (o : out),
        red_expr S a1
          (spec_creating_function_object a2 a3 (execution_ctx_lexical_env a1)
             (execution_ctx_strict a1)) oo ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq execution_ctx C a1 ->
        @eq (list string) args a2 ->
        @eq funcbody bd a3 -> @eq out o oo -> P S a1 a1 a2 a3 oo) ->
       red_expr S C (spec_create_new_function_in a1 a2 a3) oo ->
       P S C a1 a2 a3 oo.

Parameter inv_red_expr_spec_call
     : forall (S : state) (C : execution_ctx) (a1 : object_loc) 
         (a2 : value) (a3 : list value) (oo : out)
         (P : state ->
              execution_ctx ->
              object_loc -> value -> list value -> out -> Prop),
       (red_expr S C (spec_call a1 a2 a3) oo ->
        forall (S0 : state) (C0 : execution_ctx) (exte : ext_expr) (o : out),
        @eq (option out) (out_of_ext_expr (spec_call a1 a2 a3))
          (@Some out oo) ->
        abort oo ->
        not (abort_intercepted_expr (spec_call a1 a2 a3)) ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq ext_expr exte (spec_call a1 a2 a3) ->
        @eq out o oo -> P S C a1 a2 a3 oo) ->
       (red_expr S C (spec_call a1 a2 a3) oo ->
        forall (S0 : state) (C0 : execution_ctx) (l : object_loc) 
          (B : call) (this : value) (args : list value) 
          (o : out),
        @object_method (option call) object_call_ S a1 (@Some call B) ->
        red_expr S C (spec_call_1 B a1 a2 a3) oo ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq object_loc l a1 ->
        @eq value this a2 ->
        @eq (list value) args a3 -> @eq out o oo -> P S C a1 a2 a3 oo) ->
       red_expr S C (spec_call a1 a2 a3) oo -> P S C a1 a2 a3 oo.

Parameter inv_red_expr_spec_call_1
     : forall (S : state) (C : execution_ctx) (a1 : call) 
         (a2 : object_loc) (a3 : value) (a4 : list value) 
         (oo : out)
         (P : state ->
              execution_ctx ->
              call -> object_loc -> value -> list value -> out -> Prop),
       (red_expr S C (spec_call_1 a1 a2 a3 a4) oo ->
        forall (S0 : state) (C0 : execution_ctx) (exte : ext_expr) (o : out),
        @eq (option out) (out_of_ext_expr (spec_call_1 a1 a2 a3 a4))
          (@Some out oo) ->
        abort oo ->
        not (abort_intercepted_expr (spec_call_1 a1 a2 a3 a4)) ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq ext_expr exte (spec_call_1 a1 a2 a3 a4) ->
        @eq out o oo -> P S C a1 a2 a3 a4 oo) ->
       (red_expr S C (spec_call_1 a1 a2 a3 a4) oo ->
        forall (S0 : state) (C0 : execution_ctx) (B : prealloc)
          (lo : object_loc) (this : value) (args : list value) 
          (o : out),
        red_expr S C (spec_call_prealloc B a3 a4) oo ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq call (call_prealloc B) a1 ->
        @eq object_loc lo a2 ->
        @eq value this a3 ->
        @eq (list value) args a4 ->
        @eq out o oo -> P S C (call_prealloc B) a2 a3 a4 oo) ->
       (red_expr S C (spec_call_1 a1 a2 a3 a4) oo ->
        forall (S0 : state) (C0 : execution_ctx) (l : object_loc)
          (this : value) (args : list value) (o : out),
        red_expr S C (spec_call_default a2 a3 a4) oo ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq call call_default a1 ->
        @eq object_loc l a2 ->
        @eq value this a3 ->
        @eq (list value) args a4 ->
        @eq out o oo -> P S C call_default a2 a3 a4 oo) ->
       (red_expr S C (spec_call_1 a1 a2 a3 a4) oo ->
        forall (S0 : state) (C0 : execution_ctx) (l : object_loc)
          (this : value) (args : list value) (o : out)
          (boundArgs : list value) (boundThis : value) 
          (target : object_loc) (arguments : list value),
        @object_method (option (list value)) object_bound_args_ S a2
          (@Some (list value) boundArgs) ->
        @object_method (option value) object_bound_this_ S a2
          (@Some value boundThis) ->
        @object_method (option object_loc) object_target_function_ S a2
          (@Some object_loc target) ->
        @eq (list value) arguments (@append value boundArgs a4) ->
        red_expr S C (spec_call target boundThis arguments) oo ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq call call_after_bind a1 ->
        @eq object_loc l a2 ->
        @eq value this a3 ->
        @eq (list value) args a4 ->
        @eq out o oo -> P S C call_after_bind a2 a3 a4 oo) ->
       red_expr S C (spec_call_1 a1 a2 a3 a4) oo -> P S C a1 a2 a3 a4 oo.

Parameter inv_red_expr_spec_call_default
     : forall (S : state) (C : execution_ctx) (a1 : object_loc) 
         (a2 : value) (a3 : list value) (oo : out)
         (P : state ->
              execution_ctx ->
              object_loc -> value -> list value -> out -> Prop),
       (red_expr S C (spec_call_default a1 a2 a3) oo ->
        forall (S0 : state) (C0 : execution_ctx) (exte : ext_expr) (o : out),
        @eq (option out) (out_of_ext_expr (spec_call_default a1 a2 a3))
          (@Some out oo) ->
        abort oo ->
        not (abort_intercepted_expr (spec_call_default a1 a2 a3)) ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq ext_expr exte (spec_call_default a1 a2 a3) ->
        @eq out o oo -> P S C a1 a2 a3 oo) ->
       (red_expr S C (spec_call_default a1 a2 a3) oo ->
        forall (S0 : state) (C0 : execution_ctx) (l : object_loc)
          (this : value) (args : list value) (o : out),
        red_expr S C
          (spec_entering_func_code a1 a2 a3 (spec_call_default_1 a1)) oo ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq object_loc l a1 ->
        @eq value this a2 ->
        @eq (list value) args a3 -> @eq out o oo -> P S C a1 a2 a3 oo) ->
       red_expr S C (spec_call_default a1 a2 a3) oo -> P S C a1 a2 a3 oo.

Parameter inv_red_expr_spec_call_default_1
     : forall (S : state) (C : execution_ctx) (a1 : object_loc) 
         (oo : out) (P : state -> execution_ctx -> object_loc -> out -> Prop),
       (red_expr S C (spec_call_default_1 a1) oo ->
        forall (S0 : state) (C0 : execution_ctx) (exte : ext_expr) (o : out),
        @eq (option out) (out_of_ext_expr (spec_call_default_1 a1))
          (@Some out oo) ->
        abort oo ->
        not (abort_intercepted_expr (spec_call_default_1 a1)) ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq ext_expr exte (spec_call_default_1 a1) ->
        @eq out o oo -> P S C a1 oo) ->
       (red_expr S C (spec_call_default_1 a1) oo ->
        forall (S0 : state) (C0 : execution_ctx) (l : object_loc)
          (bdo : option funcbody) (o : out),
        @object_method (option funcbody) object_code_ S a1 bdo ->
        red_expr S C (spec_call_default_2 bdo) oo ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq object_loc l a1 -> @eq out o oo -> P S C a1 oo) ->
       red_expr S C (spec_call_default_1 a1) oo -> P S C a1 oo.

Parameter inv_red_expr_spec_call_default_2
     : forall (S : state) (C : execution_ctx) (a1 : option funcbody)
         (oo : out)
         (P : state -> execution_ctx -> option funcbody -> out -> Prop),
       (red_expr S C (spec_call_default_2 a1) oo ->
        forall (S0 : state) (C0 : execution_ctx) (exte : ext_expr) (o : out),
        @eq (option out) (out_of_ext_expr (spec_call_default_2 a1))
          (@Some out oo) ->
        abort oo ->
        not (abort_intercepted_expr (spec_call_default_2 a1)) ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq ext_expr exte (spec_call_default_2 a1) ->
        @eq out o oo -> P S C a1 oo) ->
       (red_expr S C (spec_call_default_2 a1) oo ->
        forall (S0 : state) (C0 : execution_ctx) (bd : funcbody) (o1 o : out),
        not (funcbody_empty bd) ->
        red_prog S C (prog_basic (funcbody_prog bd)) o1 ->
        red_expr S C (spec_call_default_3 o1) oo ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq (option funcbody) (@Some funcbody bd) a1 ->
        @eq out o oo -> P S C (@Some funcbody bd) oo) ->
       (red_expr S C (spec_call_default_2 a1) oo ->
        forall (S0 : state) (C0 : execution_ctx) (bdo : option funcbody)
          (o : out),
        match a1 return Prop with
        | Some bd => funcbody_empty bd
        | None => True
        end ->
        red_expr S C
          (spec_call_default_3
             (out_ter S (res_normal (resvalue_value (value_prim prim_undef)))))
          oo ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq (option funcbody) bdo a1 -> @eq out o oo -> P S C a1 oo) ->
       red_expr S C (spec_call_default_2 a1) oo -> P S C a1 oo.

Parameter inv_red_expr_spec_call_default_3
     : forall (S : state) (C : execution_ctx) (a1 oo : out)
         (P : state -> execution_ctx -> out -> out -> Prop),
       (red_expr S C (spec_call_default_3 a1) oo ->
        forall (S0 : state) (C0 : execution_ctx) (exte : ext_expr) (o : out),
        @eq (option out) (out_of_ext_expr (spec_call_default_3 a1))
          (@Some out oo) ->
        abort oo ->
        not (abort_intercepted_expr (spec_call_default_3 a1)) ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq ext_expr exte (spec_call_default_3 a1) ->
        @eq out o oo -> P S C a1 oo) ->
       (red_expr S C (spec_call_default_3 a1) oo ->
        forall (S0 S1 : state) (C0 : execution_ctx) (rv : resvalue),
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq out (out_ter S1 (res_return rv)) a1 ->
        @eq out (out_ter S1 (res_normal rv)) oo ->
        P S C (out_ter S1 (res_return rv)) (out_ter S1 (res_normal rv))) ->
       (red_expr S C (spec_call_default_3 a1) oo ->
        forall (S0 S1 : state) (C0 : execution_ctx) (rv : resvalue),
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq out (out_ter S1 (res_normal rv)) a1 ->
        @eq out (out_ter S1 (res_val (value_prim prim_undef))) oo ->
        P S C (out_ter S1 (res_normal rv))
          (out_ter S1 (res_val (value_prim prim_undef)))) ->
       red_expr S C (spec_call_default_3 a1) oo -> P S C a1 oo.

Parameter inv_red_expr_spec_construct
     : forall (S : state) (C : execution_ctx) (a1 : object_loc)
         (a2 : list value) (oo : out)
         (P : state ->
              execution_ctx -> object_loc -> list value -> out -> Prop),
       (red_expr S C (spec_construct a1 a2) oo ->
        forall (S0 : state) (C0 : execution_ctx) (exte : ext_expr) (o : out),
        @eq (option out) (out_of_ext_expr (spec_construct a1 a2))
          (@Some out oo) ->
        abort oo ->
        not (abort_intercepted_expr (spec_construct a1 a2)) ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq ext_expr exte (spec_construct a1 a2) ->
        @eq out o oo -> P S C a1 a2 oo) ->
       (red_expr S C (spec_construct a1 a2) oo ->
        forall (S0 : state) (C0 : execution_ctx) (l : object_loc)
          (B : construct) (args : list value) (o : out),
        @object_method (option construct) object_construct_ S a1
          (@Some construct B) ->
        red_expr S C (spec_construct_1 B a1 a2) oo ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq object_loc l a1 ->
        @eq (list value) args a2 -> @eq out o oo -> P S C a1 a2 oo) ->
       red_expr S C (spec_construct a1 a2) oo -> P S C a1 a2 oo.

Parameter inv_red_expr_spec_construct_1
     : forall (S : state) (C : execution_ctx) (a1 : construct)
         (a2 : object_loc) (a3 : list value) (oo : out)
         (P : state ->
              execution_ctx ->
              construct -> object_loc -> list value -> out -> Prop),
       (red_expr S C (spec_construct_1 a1 a2 a3) oo ->
        forall (S0 : state) (C0 : execution_ctx) (exte : ext_expr) (o : out),
        @eq (option out) (out_of_ext_expr (spec_construct_1 a1 a2 a3))
          (@Some out oo) ->
        abort oo ->
        not (abort_intercepted_expr (spec_construct_1 a1 a2 a3)) ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq ext_expr exte (spec_construct_1 a1 a2 a3) ->
        @eq out o oo -> P S C a1 a2 a3 oo) ->
       (red_expr S C (spec_construct_1 a1 a2 a3) oo ->
        forall (S0 : state) (C0 : execution_ctx) (B : prealloc)
          (l : object_loc) (args : list value) (o : out),
        red_expr S C (spec_construct_prealloc B a3) oo ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq construct (construct_prealloc B) a1 ->
        @eq object_loc l a2 ->
        @eq (list value) args a3 ->
        @eq out o oo -> P S C (construct_prealloc B) a2 a3 oo) ->
       (red_expr S C (spec_construct_1 a1 a2 a3) oo ->
        forall (S0 : state) (C0 : execution_ctx) (l : object_loc)
          (args : list value) (o : out),
        red_expr S C (spec_construct_default a2 a3) oo ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq construct construct_default a1 ->
        @eq object_loc l a2 ->
        @eq (list value) args a3 ->
        @eq out o oo -> P S C construct_default a2 a3 oo) ->
       (red_expr S C (spec_construct_1 a1 a2 a3) oo ->
        forall (S0 : state) (C0 : execution_ctx) (l : object_loc)
          (args : list value) (o : out) (target : object_loc),
        @object_method (option object_loc) object_target_function_ S a2
          (@Some object_loc target) ->
        red_expr S C (spec_construct_1_after_bind a2 a3 target) oo ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq construct construct_after_bind a1 ->
        @eq object_loc l a2 ->
        @eq (list value) args a3 ->
        @eq out o oo -> P S C construct_after_bind a2 a3 oo) ->
       red_expr S C (spec_construct_1 a1 a2 a3) oo -> P S C a1 a2 a3 oo.

Parameter inv_red_expr_spec_construct_prealloc
     : forall (S : state) (C : execution_ctx) (a1 : prealloc)
         (a2 : list value) (oo : out)
         (P : state -> execution_ctx -> prealloc -> list value -> out -> Prop),
       (red_expr S C (spec_construct_prealloc a1 a2) oo ->
        forall (S0 : state) (C0 : execution_ctx) (exte : ext_expr) (o : out),
        @eq (option out) (out_of_ext_expr (spec_construct_prealloc a1 a2))
          (@Some out oo) ->
        abort oo ->
        not (abort_intercepted_expr (spec_construct_prealloc a1 a2)) ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq ext_expr exte (spec_construct_prealloc a1 a2) ->
        @eq out o oo -> P S C a1 a2 oo) ->
       (red_expr S C (spec_construct_prealloc a1 a2) oo ->
        forall (S0 : state) (C0 : execution_ctx) (args : list value)
          (v : value) (o : out),
        arguments_from a2 (@cons value v (@nil value)) ->
        red_expr S C (spec_call_object_new_1 v) oo ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq prealloc prealloc_object a1 ->
        @eq (list value) args a2 ->
        @eq out o oo -> P S C prealloc_object a2 oo) ->
       (red_expr S C (spec_construct_prealloc a1 a2) oo ->
        forall (S0 : state) (C0 : execution_ctx) (args : list value)
          (o : out),
        @eq (list value) a2 (@nil value) ->
        red_expr S C (spec_call_array_new_1 a2) oo ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq prealloc prealloc_array a1 ->
        @eq (list value) args a2 ->
        @eq out o oo -> P S C prealloc_array a2 oo) ->
       (red_expr S C (spec_construct_prealloc a1 a2) oo ->
        forall (S0 : state) (C0 : execution_ctx) (args : list value)
          (v1 v2 : value) (vs : list value) (o : out),
        @eq (list value) a2 (@cons value v1 (@cons value v2 vs)) ->
        red_expr S C (spec_call_array_new_1 a2) oo ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq prealloc prealloc_array a1 ->
        @eq (list value) args a2 ->
        @eq out o oo -> P S C prealloc_array a2 oo) ->
       (red_expr S C (spec_construct_prealloc a1 a2) oo ->
        forall (S0 : state) (C0 : execution_ctx) (args : list value)
          (v : value) (o : out),
        @eq (list value) a2 (@cons value v (@nil value)) ->
        red_expr S C (spec_call_array_new_single_1 v) oo ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq prealloc prealloc_array a1 ->
        @eq (list value) args a2 ->
        @eq out o oo -> P S C prealloc_array a2 oo) ->
       (red_expr S C (spec_construct_prealloc a1 a2) oo ->
        forall (S0 : state) (C0 : execution_ctx) (v : value)
          (args : list value) (o : out),
        not (@eq (list value) a2 (@nil value)) ->
        arguments_from a2 (@cons value v (@nil value)) ->
        red_expr S C (spec_construct_string_1 v) oo ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq prealloc prealloc_string a1 ->
        @eq (list value) args a2 ->
        @eq out o oo -> P S C prealloc_string a2 oo) ->
       (red_expr S C (spec_construct_prealloc a1 a2) oo ->
        forall (S0 : state) (C0 : execution_ctx) (o : out),
        red_expr S C
          (spec_construct_string_2
             (out_ter S (res_val (value_prim (prim_string EmptyString))))) oo ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq prealloc prealloc_string a1 ->
        @eq (list value) (@nil value) a2 ->
        @eq out o oo -> P S C prealloc_string (@nil value) oo) ->
       (red_expr S C (spec_construct_prealloc a1 a2) oo ->
        forall (S0 : state) (C0 : execution_ctx) (v : value) 
          (o o1 : out) (args : list value),
        arguments_from a2 (@cons value v (@nil value)) ->
        red_expr S C (spec_to_boolean v) o1 ->
        red_expr S C (spec_construct_bool_1 o1) oo ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq prealloc prealloc_bool a1 ->
        @eq (list value) args a2 -> @eq out o oo -> P S C prealloc_bool a2 oo) ->
       (red_expr S C (spec_construct_prealloc a1 a2) oo ->
        forall (S0 : state) (C0 : execution_ctx) (o : out),
        red_expr S C
          (spec_construct_number_1
             (out_ter S (res_val (value_prim (prim_number JsNumber.zero)))))
          oo ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq prealloc prealloc_number a1 ->
        @eq (list value) (@nil value) a2 ->
        @eq out o oo -> P S C prealloc_number (@nil value) oo) ->
       (red_expr S C (spec_construct_prealloc a1 a2) oo ->
        forall (S0 : state) (C0 : execution_ctx) (v : value) 
          (o o1 : out) (args : list value),
        not (@eq (list value) a2 (@nil value)) ->
        arguments_from a2 (@cons value v (@nil value)) ->
        red_expr S C (spec_to_number v) o1 ->
        red_expr S C (spec_construct_number_1 o1) oo ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq prealloc prealloc_number a1 ->
        @eq (list value) args a2 ->
        @eq out o oo -> P S C prealloc_number a2 oo) ->
       (red_expr S C (spec_construct_prealloc a1 a2) oo ->
        forall (S0 : state) (C0 : execution_ctx) (v : value) 
          (o : out) (args : list value),
        arguments_from a2 (@cons value v (@nil value)) ->
        red_expr S C
          (spec_build_error
             (value_object (object_loc_prealloc prealloc_error_proto)) v) oo ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq prealloc prealloc_error a1 ->
        @eq (list value) args a2 ->
        @eq out o oo -> P S C prealloc_error a2 oo) ->
       (red_expr S C (spec_construct_prealloc a1 a2) oo ->
        forall (S0 : state) (C0 : execution_ctx) (v : value) 
          (o : out) (ne : native_error) (args : list value),
        arguments_from a2 (@cons value v (@nil value)) ->
        red_expr S C
          (spec_build_error
             (value_object
                (object_loc_prealloc (prealloc_native_error_proto ne))) v) oo ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq prealloc (prealloc_native_error ne) a1 ->
        @eq (list value) args a2 ->
        @eq out o oo -> P S C (prealloc_native_error ne) a2 oo) ->
       (red_expr S C (spec_construct_prealloc a1 a2) oo ->
        forall (S0 : state) (C0 : execution_ctx) (B : prealloc)
          (args : list value) (o : out),
        implementation_prealloc a1 ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq prealloc B a1 ->
        @eq (list value) args a2 -> @eq out o oo -> P S C a1 a2 oo) ->
       red_expr S C (spec_construct_prealloc a1 a2) oo -> P S C a1 a2 oo.

Parameter inv_red_expr_spec_construct_default
     : forall (S : state) (C : execution_ctx) (a1 : object_loc)
         (a2 : list value) (oo : out)
         (P : state ->
              execution_ctx -> object_loc -> list value -> out -> Prop),
       (red_expr S C (spec_construct_default a1 a2) oo ->
        forall (S0 : state) (C0 : execution_ctx) (exte : ext_expr) (o : out),
        @eq (option out) (out_of_ext_expr (spec_construct_default a1 a2))
          (@Some out oo) ->
        abort oo ->
        not (abort_intercepted_expr (spec_construct_default a1 a2)) ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq ext_expr exte (spec_construct_default a1 a2) ->
        @eq out o oo -> P S C a1 a2 oo) ->
       (red_expr S C (spec_construct_default a1 a2) oo ->
        forall (S0 : state) (C0 : execution_ctx) (l : object_loc)
          (args : list value) (o1 o : out),
        red_expr S C
          (spec_object_get a1
             (String (Ascii false false false false true true true false)
                (String (Ascii false true false false true true true false)
                   (String (Ascii true true true true false true true false)
                      (String
                         (Ascii false false true false true true true false)
                         (String
                            (Ascii true true true true false true true false)
                            (String
                               (Ascii false false true false true true true
                                  false)
                               (String
                                  (Ascii true false false true true true true
                                     false)
                                  (String
                                     (Ascii false false false false true true
                                        true false)
                                     (String
                                        (Ascii true false true false false
                                           true true false) EmptyString))))))))))
          o1 ->
        red_expr S C (spec_construct_default_1 a1 a2 o1) oo ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq object_loc l a1 ->
        @eq (list value) args a2 -> @eq out o oo -> P S C a1 a2 oo) ->
       red_expr S C (spec_construct_default a1 a2) oo -> P S C a1 a2 oo.

Parameter inv_red_expr_spec_construct_default_1
     : forall (S : state) (C : execution_ctx) (a1 : object_loc)
         (a2 : list value) (a3 oo : out)
         (P : state ->
              execution_ctx -> object_loc -> list value -> out -> out -> Prop),
       (red_expr S C (spec_construct_default_1 a1 a2 a3) oo ->
        forall (S0 : state) (C0 : execution_ctx) (exte : ext_expr) (o : out),
        @eq (option out)
          (out_of_ext_expr (spec_construct_default_1 a1 a2 a3))
          (@Some out oo) ->
        abort oo ->
        not (abort_intercepted_expr (spec_construct_default_1 a1 a2 a3)) ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq ext_expr exte (spec_construct_default_1 a1 a2 a3) ->
        @eq out o oo -> P S C a1 a2 a3 oo) ->
       (red_expr S C (spec_construct_default_1 a1 a2 a3) oo ->
        forall (S0 S1 S' : state) (C0 : execution_ctx) 
          (l' : object_loc) (vproto : value) (O : object) 
          (l : object_loc) (args : list value) (v : value) 
          (o1 o : out),
        @eq value vproto
          match classicT (@eq type (type_of v) type_object) return value with
          | left _ => v
          | right _ =>
              value_object (object_loc_prealloc prealloc_object_proto)
          end ->
        @eq object O
          (object_new vproto
             (String (Ascii true true true true false false true false)
                (String (Ascii false true false false false true true false)
                   (String
                      (Ascii false true false true false true true false)
                      (String
                         (Ascii true false true false false true true false)
                         (String
                            (Ascii true true false false false true true
                               false)
                            (String
                               (Ascii false false true false true true true
                                  false) EmptyString))))))) ->
        @eq (prod object_loc state) (@pair object_loc state l' S')
          (object_alloc S1 O) ->
        red_expr S' C (spec_call a1 (value_object l') a2) o1 ->
        red_expr S' C (spec_construct_default_2 l' o1) oo ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq object_loc l a1 ->
        @eq (list value) args a2 ->
        @eq out (out_ter S1 (res_val v)) a3 ->
        @eq out o oo -> P S C a1 a2 (out_ter S1 (res_val v)) oo) ->
       red_expr S C (spec_construct_default_1 a1 a2 a3) oo ->
       P S C a1 a2 a3 oo.

Parameter inv_red_expr_spec_construct_default_2
     : forall (S : state) (C : execution_ctx) (a1 : object_loc) 
         (a2 oo : out)
         (P : state -> execution_ctx -> object_loc -> out -> out -> Prop),
       (red_expr S C (spec_construct_default_2 a1 a2) oo ->
        forall (S0 : state) (C0 : execution_ctx) (exte : ext_expr) (o : out),
        @eq (option out) (out_of_ext_expr (spec_construct_default_2 a1 a2))
          (@Some out oo) ->
        abort oo ->
        not (abort_intercepted_expr (spec_construct_default_2 a1 a2)) ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq ext_expr exte (spec_construct_default_2 a1 a2) ->
        @eq out o oo -> P S C a1 a2 oo) ->
       (red_expr S C (spec_construct_default_2 a1 a2) oo ->
        forall (S0 S1 : state) (C0 : execution_ctx) 
          (l' : object_loc) (v v' : value),
        @eq value v'
          match classicT (@eq type (type_of v) type_object) return value with
          | left _ => v
          | right _ => value_object a1
          end ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq object_loc l' a1 ->
        @eq out (out_ter S1 (res_val v)) a2 ->
        @eq out (out_ter S1 (res_val v')) oo ->
        P S C a1 (out_ter S1 (res_val v)) (out_ter S1 (res_val v'))) ->
       red_expr S C (spec_construct_default_2 a1 a2) oo -> P S C a1 a2 oo.

Parameter inv_red_expr_spec_construct_1_after_bind
     : forall (S : state) (C : execution_ctx) (a1 : object_loc)
         (a2 : list value) (a3 : object_loc) (oo : out)
         (P : state ->
              execution_ctx ->
              object_loc -> list value -> object_loc -> out -> Prop),
       (red_expr S C (spec_construct_1_after_bind a1 a2 a3) oo ->
        forall (S0 : state) (C0 : execution_ctx) (exte : ext_expr) (o : out),
        @eq (option out)
          (out_of_ext_expr (spec_construct_1_after_bind a1 a2 a3))
          (@Some out oo) ->
        abort oo ->
        not (abort_intercepted_expr (spec_construct_1_after_bind a1 a2 a3)) ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq ext_expr exte (spec_construct_1_after_bind a1 a2 a3) ->
        @eq out o oo -> P S C a1 a2 a3 oo) ->
       (red_expr S C (spec_construct_1_after_bind a1 a2 a3) oo ->
        forall (S0 : state) (C0 : execution_ctx) (l : object_loc)
          (args : list value) (co : construct) (o : out)
          (target : object_loc) (boundArgs arguments : list value),
        @object_method (option construct) object_construct_ S a3
          (@Some construct co) ->
        @object_method (option (list value)) object_bound_args_ S a1
          (@Some (list value) boundArgs) ->
        @eq (list value) arguments (@append value boundArgs a2) ->
        red_expr S C (spec_construct_1 co a3 arguments) oo ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq object_loc l a1 ->
        @eq (list value) args a2 ->
        @eq object_loc target a3 -> @eq out o oo -> P S C a1 a2 a3 oo) ->
       (red_expr S C (spec_construct_1_after_bind a1 a2 a3) oo ->
        forall (S0 : state) (C0 : execution_ctx) (l : object_loc)
          (args : list value) (target : object_loc) 
          (o : out),
        @object_method (option construct) object_construct_ S a3
          (@None construct) ->
        red_expr S C (spec_error native_error_type) oo ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq object_loc l a1 ->
        @eq (list value) args a2 ->
        @eq object_loc target a3 -> @eq out o oo -> P S C a1 a2 a3 oo) ->
       red_expr S C (spec_construct_1_after_bind a1 a2 a3) oo ->
       P S C a1 a2 a3 oo.

Parameter inv_red_expr_spec_call_global_is_nan_1
     : forall (S : state) (C : execution_ctx) (a1 oo : out)
         (P : state -> execution_ctx -> out -> out -> Prop),
       (red_expr S C (spec_call_global_is_nan_1 a1) oo ->
        forall (S0 : state) (C0 : execution_ctx) (exte : ext_expr) (o : out),
        @eq (option out) (out_of_ext_expr (spec_call_global_is_nan_1 a1))
          (@Some out oo) ->
        abort oo ->
        not (abort_intercepted_expr (spec_call_global_is_nan_1 a1)) ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq ext_expr exte (spec_call_global_is_nan_1 a1) ->
        @eq out o oo -> P S C a1 oo) ->
       (red_expr S C (spec_call_global_is_nan_1 a1) oo ->
        forall (S0 S1 : state) (C0 : execution_ctx) 
          (b : bool) (n : JsNumber.number),
        @eq bool b
          match
            classicT (@eq JsNumber.number n JsNumber.nan) return bool
          with
          | left _ => true
          | right _ => false
          end ->
        @eq state S1 S ->
        @eq execution_ctx C0 C ->
        @eq out (out_ter S0 (res_val (value_prim (prim_number n)))) a1 ->
        @eq out (out_ter S0 (res_val (value_prim (prim_bool b)))) oo ->
        P S C (out_ter S0 (res_val (value_prim (prim_number n))))
          (out_ter S0 (res_val (value_prim (prim_bool b))))) ->
       red_expr S C (spec_call_global_is_nan_1 a1) oo -> P S C a1 oo.

Parameter inv_red_expr_spec_call_global_is_finite_1
     : forall (S : state) (C : execution_ctx) (a1 oo : out)
         (P : state -> execution_ctx -> out -> out -> Prop),
       (red_expr S C (spec_call_global_is_finite_1 a1) oo ->
        forall (S0 : state) (C0 : execution_ctx) (exte : ext_expr) (o : out),
        @eq (option out) (out_of_ext_expr (spec_call_global_is_finite_1 a1))
          (@Some out oo) ->
        abort oo ->
        not (abort_intercepted_expr (spec_call_global_is_finite_1 a1)) ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq ext_expr exte (spec_call_global_is_finite_1 a1) ->
        @eq out o oo -> P S C a1 oo) ->
       (red_expr S C (spec_call_global_is_finite_1 a1) oo ->
        forall (S0 S1 : state) (C0 : execution_ctx) 
          (b : bool) (n : JsNumber.number),
        @eq bool b
          match
            classicT
              (Logic.or (@eq JsNumber.number n JsNumber.nan)
                 (Logic.or (@eq JsNumber.number n JsNumber.infinity)
                    (@eq JsNumber.number n JsNumber.neg_infinity)))
            return bool
          with
          | left _ => false
          | right _ => true
          end ->
        @eq state S1 S ->
        @eq execution_ctx C0 C ->
        @eq out (out_ter S0 (res_val (value_prim (prim_number n)))) a1 ->
        @eq out (out_ter S0 (res_val (value_prim (prim_bool b)))) oo ->
        P S C (out_ter S0 (res_val (value_prim (prim_number n))))
          (out_ter S0 (res_val (value_prim (prim_bool b))))) ->
       red_expr S C (spec_call_global_is_finite_1 a1) oo -> P S C a1 oo.

Parameter inv_red_expr_spec_call_object_call_1
     : forall (S : state) (C : execution_ctx) (a1 : value) 
         (a2 : list value) (oo : out)
         (P : state -> execution_ctx -> value -> list value -> out -> Prop),
       (red_expr S C (spec_call_object_call_1 a1 a2) oo ->
        forall (S0 : state) (C0 : execution_ctx) (exte : ext_expr) (o : out),
        @eq (option out) (out_of_ext_expr (spec_call_object_call_1 a1 a2))
          (@Some out oo) ->
        abort oo ->
        not (abort_intercepted_expr (spec_call_object_call_1 a1 a2)) ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq ext_expr exte (spec_call_object_call_1 a1 a2) ->
        @eq out o oo -> P S C a1 a2 oo) ->
       (red_expr S C (spec_call_object_call_1 a1 a2) oo ->
        forall (S0 : state) (C0 : execution_ctx) (v : value) 
          (o : out) (args : list value),
        Logic.or (@eq value a1 (value_prim prim_null))
          (@eq value a1 (value_prim prim_undef)) ->
        red_expr S C (spec_construct_prealloc prealloc_object a2) oo ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq value v a1 ->
        @eq (list value) args a2 -> @eq out o oo -> P S C a1 a2 oo) ->
       (red_expr S C (spec_call_object_call_1 a1 a2) oo ->
        forall (S0 : state) (C0 : execution_ctx) (v : value) 
          (o : out) (args : list value),
        Logic.and (not (@eq value a1 (value_prim prim_null)))
          (not (@eq value a1 (value_prim prim_undef))) ->
        red_expr S C (spec_to_object a1) oo ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq value v a1 ->
        @eq (list value) args a2 -> @eq out o oo -> P S C a1 a2 oo) ->
       red_expr S C (spec_call_object_call_1 a1 a2) oo -> P S C a1 a2 oo.

Parameter inv_red_expr_spec_call_object_new_1
     : forall (S : state) (C : execution_ctx) (a1 : value) 
         (oo : out) (P : state -> execution_ctx -> value -> out -> Prop),
       (red_expr S C (spec_call_object_new_1 a1) oo ->
        forall (S0 : state) (C0 : execution_ctx) (exte : ext_expr) (o : out),
        @eq (option out) (out_of_ext_expr (spec_call_object_new_1 a1))
          (@Some out oo) ->
        abort oo ->
        not (abort_intercepted_expr (spec_call_object_new_1 a1)) ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq ext_expr exte (spec_call_object_new_1 a1) ->
        @eq out o oo -> P S C a1 oo) ->
       (red_expr S C (spec_call_object_new_1 a1) oo ->
        forall (S0 : state) (C0 : execution_ctx) (v : value),
        @eq type (type_of a1) type_object ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq value v a1 ->
        @eq out (out_ter S (res_val a1)) oo ->
        P S C a1 (out_ter S (res_val a1))) ->
       (red_expr S C (spec_call_object_new_1 a1) oo ->
        forall (S0 : state) (C0 : execution_ctx) (v : value) 
          (ty : type) (o : out),
        @eq type ty (type_of a1) ->
        Logic.or (@eq type ty type_string)
          (Logic.or (@eq type ty type_bool) (@eq type ty type_number)) ->
        red_expr S C (spec_to_object a1) oo ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq value v a1 -> @eq out o oo -> P S C a1 oo) ->
       (red_expr S C (spec_call_object_new_1 a1) oo ->
        forall (S0 : state) (C0 : execution_ctx) (v : value) 
          (O : object) (l : object_loc) (S' : state),
        Logic.or (@eq value a1 (value_prim prim_null))
          (@eq value a1 (value_prim prim_undef)) ->
        @eq object O
          (object_new
             (value_object (object_loc_prealloc prealloc_object_proto))
             (String (Ascii true true true true false false true false)
                (String (Ascii false true false false false true true false)
                   (String
                      (Ascii false true false true false true true false)
                      (String
                         (Ascii true false true false false true true false)
                         (String
                            (Ascii true true false false false true true
                               false)
                            (String
                               (Ascii false false true false true true true
                                  false) EmptyString))))))) ->
        @eq (prod object_loc state) (@pair object_loc state l S')
          (object_alloc S O) ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq value v a1 ->
        @eq out (out_ter S' (res_val (value_object l))) oo ->
        P S C a1 (out_ter S' (res_val (value_object l)))) ->
       red_expr S C (spec_call_object_new_1 a1) oo -> P S C a1 oo.

Parameter inv_red_expr_spec_call_object_get_proto_of_1
     : forall (S : state) (C : execution_ctx) (a1 : value) 
         (oo : out) (P : state -> execution_ctx -> value -> out -> Prop),
       (red_expr S C (spec_call_object_get_proto_of_1 a1) oo ->
        forall (S0 : state) (C0 : execution_ctx) (exte : ext_expr) (o : out),
        @eq (option out)
          (out_of_ext_expr (spec_call_object_get_proto_of_1 a1))
          (@Some out oo) ->
        abort oo ->
        not (abort_intercepted_expr (spec_call_object_get_proto_of_1 a1)) ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq ext_expr exte (spec_call_object_get_proto_of_1 a1) ->
        @eq out o oo -> P S C a1 oo) ->
       (red_expr S C (spec_call_object_get_proto_of_1 a1) oo ->
        forall (S0 : state) (C0 : execution_ctx) (w : prim) (o : out),
        red_expr S C (spec_error native_error_type) oo ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq value (value_prim w) a1 ->
        @eq out o oo -> P S C (value_prim w) oo) ->
       (red_expr S C (spec_call_object_get_proto_of_1 a1) oo ->
        forall (S0 : state) (C0 : execution_ctx) (l : object_loc) (v : value),
        object_proto S l v ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq value (value_object l) a1 ->
        @eq out (out_ter S (res_val v)) oo ->
        P S C (value_object l) (out_ter S (res_val v))) ->
       red_expr S C (spec_call_object_get_proto_of_1 a1) oo -> P S C a1 oo.

Parameter inv_red_expr_spec_call_object_is_extensible_1
     : forall (S : state) (C : execution_ctx) (a1 : value) 
         (oo : out) (P : state -> execution_ctx -> value -> out -> Prop),
       (red_expr S C (spec_call_object_is_extensible_1 a1) oo ->
        forall (S0 : state) (C0 : execution_ctx) (exte : ext_expr) (o : out),
        @eq (option out)
          (out_of_ext_expr (spec_call_object_is_extensible_1 a1))
          (@Some out oo) ->
        abort oo ->
        not (abort_intercepted_expr (spec_call_object_is_extensible_1 a1)) ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq ext_expr exte (spec_call_object_is_extensible_1 a1) ->
        @eq out o oo -> P S C a1 oo) ->
       (red_expr S C (spec_call_object_is_extensible_1 a1) oo ->
        forall (S0 : state) (C0 : execution_ctx) (v : value) (o : out),
        not (@eq type (type_of a1) type_object) ->
        red_expr S C (spec_error native_error_type) oo ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq value v a1 -> @eq out o oo -> P S C a1 oo) ->
       (red_expr S C (spec_call_object_is_extensible_1 a1) oo ->
        forall (S0 : state) (C0 : execution_ctx) (l : object_loc) (b : bool),
        object_extensible S l b ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq value (value_object l) a1 ->
        @eq out (out_ter S (res_val (value_prim (prim_bool b)))) oo ->
        P S C (value_object l)
          (out_ter S (res_val (value_prim (prim_bool b))))) ->
       red_expr S C (spec_call_object_is_extensible_1 a1) oo -> P S C a1 oo.

Parameter inv_red_expr_spec_call_object_define_props_1
     : forall (S : state) (C : execution_ctx) (a1 a2 : value) 
         (oo : out)
         (P : state -> execution_ctx -> value -> value -> out -> Prop),
       (red_expr S C (spec_call_object_define_props_1 a1 a2) oo ->
        forall (S0 : state) (C0 : execution_ctx) (exte : ext_expr) (o : out),
        @eq (option out)
          (out_of_ext_expr (spec_call_object_define_props_1 a1 a2))
          (@Some out oo) ->
        abort oo ->
        not (abort_intercepted_expr (spec_call_object_define_props_1 a1 a2)) ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq ext_expr exte (spec_call_object_define_props_1 a1 a2) ->
        @eq out o oo -> P S C a1 a2 oo) ->
       (red_expr S C (spec_call_object_define_props_1 a1 a2) oo ->
        forall (S0 : state) (C0 : execution_ctx) (vo vp : value) (o : out),
        not (@eq type (type_of a1) type_object) ->
        red_expr S C (spec_error native_error_type) oo ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq value vo a1 -> @eq value vp a2 -> @eq out o oo -> P S C a1 a2 oo) ->
       (red_expr S C (spec_call_object_define_props_1 a1 a2) oo ->
        forall (S0 : state) (C0 : execution_ctx) (l : object_loc)
          (vp : value) (o o1 : out),
        red_expr S C (spec_to_object a2) o1 ->
        red_expr S C (spec_call_object_define_props_2 o1 l) oo ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq value (value_object l) a1 ->
        @eq value vp a2 -> @eq out o oo -> P S C (value_object l) a2 oo) ->
       red_expr S C (spec_call_object_define_props_1 a1 a2) oo ->
       P S C a1 a2 oo.

Parameter inv_red_expr_spec_call_object_define_props_2
     : forall (S : state) (C : execution_ctx) (a1 : out) 
         (a2 : object_loc) (oo : out)
         (P : state -> execution_ctx -> out -> object_loc -> out -> Prop),
       (red_expr S C (spec_call_object_define_props_2 a1 a2) oo ->
        forall (S0 : state) (C0 : execution_ctx) (exte : ext_expr) (o : out),
        @eq (option out)
          (out_of_ext_expr (spec_call_object_define_props_2 a1 a2))
          (@Some out oo) ->
        abort oo ->
        not (abort_intercepted_expr (spec_call_object_define_props_2 a1 a2)) ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq ext_expr exte (spec_call_object_define_props_2 a1 a2) ->
        @eq out o oo -> P S C a1 a2 oo) ->
       (red_expr S C (spec_call_object_define_props_2 a1 a2) oo ->
        forall (S0 S1 : state) (C0 : execution_ctx) 
          (l lp : object_loc) (xs : list prop_name) 
          (o : out),
        object_properties_enumerable_keys_as_list S1 lp xs ->
        red_expr S1 C
          (spec_call_object_define_props_3 a2 lp xs
             (@nil (prod prop_name attributes))) oo ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq out (out_ter S1 (res_val (value_object lp))) a1 ->
        @eq object_loc l a2 ->
        @eq out o oo -> P S C (out_ter S1 (res_val (value_object lp))) a2 oo) ->
       red_expr S C (spec_call_object_define_props_2 a1 a2) oo ->
       P S C a1 a2 oo.

Parameter inv_red_expr_spec_call_object_define_props_3
     : forall (S : state) (C : execution_ctx) (a1 a2 : object_loc)
         (a3 : list prop_name) (a4 : list (prod prop_name attributes))
         (oo : out)
         (P : state ->
              execution_ctx ->
              object_loc ->
              object_loc ->
              list string -> list (prod string attributes) -> out -> Prop),
       (red_expr S C (spec_call_object_define_props_3 a1 a2 a3 a4) oo ->
        forall (S0 : state) (C0 : execution_ctx) (exte : ext_expr) (o : out),
        @eq (option out)
          (out_of_ext_expr (spec_call_object_define_props_3 a1 a2 a3 a4))
          (@Some out oo) ->
        abort oo ->
        not
          (abort_intercepted_expr
             (spec_call_object_define_props_3 a1 a2 a3 a4)) ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq ext_expr exte (spec_call_object_define_props_3 a1 a2 a3 a4) ->
        @eq out o oo -> P S C a1 a2 a3 a4 oo) ->
       (red_expr S C (spec_call_object_define_props_3 a1 a2 a3 a4) oo ->
        forall (S0 : state) (C0 : execution_ctx) (l lp : object_loc)
          (Descs : list (prod prop_name attributes)) 
          (o : out),
        red_expr S C (spec_call_object_define_props_6 a1 a4) oo ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq object_loc l a1 ->
        @eq object_loc lp a2 ->
        @eq (list prop_name) (@nil prop_name) a3 ->
        @eq (list (prod prop_name attributes)) Descs a4 ->
        @eq out o oo -> P S C a1 a2 (@nil prop_name) a4 oo) ->
       (red_expr S C (spec_call_object_define_props_3 a1 a2 a3 a4) oo ->
        forall (S0 : state) (C0 : execution_ctx) (l lp : object_loc)
          (x : prop_name) (xs : list prop_name)
          (Descs : list (prod prop_name attributes)) 
          (o o1 : out),
        red_expr S C (spec_object_get a2 x) o1 ->
        red_expr S C (spec_call_object_define_props_4 o1 a1 a2 x xs a4) oo ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq object_loc l a1 ->
        @eq object_loc lp a2 ->
        @eq (list prop_name) (@cons prop_name x xs) a3 ->
        @eq (list (prod prop_name attributes)) Descs a4 ->
        @eq out o oo -> P S C a1 a2 (@cons prop_name x xs) a4 oo) ->
       red_expr S C (spec_call_object_define_props_3 a1 a2 a3 a4) oo ->
       P S C a1 a2 a3 a4 oo.

Parameter inv_red_expr_spec_call_object_define_props_4
     : forall (S : state) (C : execution_ctx) (a1 : out) 
         (a2 a3 : object_loc) (a4 : prop_name) (a5 : list prop_name)
         (a6 : list (prod prop_name attributes)) (oo : out)
         (P : state ->
              execution_ctx ->
              out ->
              object_loc ->
              object_loc ->
              string ->
              list string -> list (prod string attributes) -> out -> Prop),
       (red_expr S C (spec_call_object_define_props_4 a1 a2 a3 a4 a5 a6) oo ->
        forall (S0 : state) (C0 : execution_ctx) (exte : ext_expr) (o : out),
        @eq (option out)
          (out_of_ext_expr
             (spec_call_object_define_props_4 a1 a2 a3 a4 a5 a6))
          (@Some out oo) ->
        abort oo ->
        not
          (abort_intercepted_expr
             (spec_call_object_define_props_4 a1 a2 a3 a4 a5 a6)) ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq ext_expr exte (spec_call_object_define_props_4 a1 a2 a3 a4 a5 a6) ->
        @eq out o oo -> P S C a1 a2 a3 a4 a5 a6 oo) ->
       (red_expr S C (spec_call_object_define_props_4 a1 a2 a3 a4 a5 a6) oo ->
        forall (S0 S1 : state) (C0 : execution_ctx) 
          (v : value) (l lp : object_loc) (o o1 : out) 
          (x : prop_name) (xs : list prop_name)
          (Descs : list (prod prop_name attributes)) 
          (y : specret attributes),
        @red_spec attributes S1 C (spec_to_descriptor v) y ->
        red_expr S1 C (spec_call_object_define_props_5 a2 a3 a4 a5 a6 y) o1 ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq out (out_ter S1 (res_val v)) a1 ->
        @eq object_loc l a2 ->
        @eq object_loc lp a3 ->
        @eq prop_name x a4 ->
        @eq (list prop_name) xs a5 ->
        @eq (list (prod prop_name attributes)) Descs a6 ->
        @eq out o oo -> P S C (out_ter S1 (res_val v)) a2 a3 a4 a5 a6 oo) ->
       red_expr S C (spec_call_object_define_props_4 a1 a2 a3 a4 a5 a6) oo ->
       P S C a1 a2 a3 a4 a5 a6 oo.

Parameter inv_red_expr_spec_call_object_define_props_5
     : forall (S : state) (C : execution_ctx) (a1 a2 : object_loc)
         (a3 : prop_name) (a4 : list prop_name)
         (a5 : list (prod prop_name attributes)) (a6 : specret attributes)
         (oo : out)
         (P : state ->
              execution_ctx ->
              object_loc ->
              object_loc ->
              string ->
              list string ->
              list (prod string attributes) ->
              specret attributes -> out -> Prop),
       (red_expr S C (spec_call_object_define_props_5 a1 a2 a3 a4 a5 a6) oo ->
        forall (S0 : state) (C0 : execution_ctx) (exte : ext_expr) (o : out),
        @eq (option out)
          (out_of_ext_expr
             (spec_call_object_define_props_5 a1 a2 a3 a4 a5 a6))
          (@Some out oo) ->
        abort oo ->
        not
          (abort_intercepted_expr
             (spec_call_object_define_props_5 a1 a2 a3 a4 a5 a6)) ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq ext_expr exte (spec_call_object_define_props_5 a1 a2 a3 a4 a5 a6) ->
        @eq out o oo -> P S C a1 a2 a3 a4 a5 a6 oo) ->
       (red_expr S C (spec_call_object_define_props_5 a1 a2 a3 a4 a5 a6) oo ->
        forall (S0 S1 : state) (C0 : execution_ctx) 
          (A : attributes) (l lp : object_loc) (o : out) 
          (x : prop_name) (xs : list prop_name)
          (xAs : list (prod prop_name attributes)),
        red_expr S0 C
          (spec_call_object_define_props_3 a1 a2 a4
             (@append (prod prop_name attributes) a5
                (@cons (prod prop_name attributes)
                   (@pair prop_name attributes a3 A)
                   (@nil (prod prop_name attributes))))) oo ->
        @eq state S1 S ->
        @eq execution_ctx C0 C ->
        @eq object_loc l a1 ->
        @eq object_loc lp a2 ->
        @eq prop_name x a3 ->
        @eq (list prop_name) xs a4 ->
        @eq (list (prod prop_name attributes)) xAs a5 ->
        @eq (specret attributes) (@ret attributes S0 A) a6 ->
        @eq out o oo -> P S C a1 a2 a3 a4 a5 (@ret attributes S0 A) oo) ->
       red_expr S C (spec_call_object_define_props_5 a1 a2 a3 a4 a5 a6) oo ->
       P S C a1 a2 a3 a4 a5 a6 oo.

Parameter inv_red_expr_spec_call_object_define_props_6
     : forall (S : state) (C : execution_ctx) (a1 : object_loc)
         (a2 : list (prod prop_name attributes)) (oo : out)
         (P : state ->
              execution_ctx ->
              object_loc -> list (prod string attributes) -> out -> Prop),
       (red_expr S C (spec_call_object_define_props_6 a1 a2) oo ->
        forall (S0 : state) (C0 : execution_ctx) (exte : ext_expr) (o : out),
        @eq (option out)
          (out_of_ext_expr (spec_call_object_define_props_6 a1 a2))
          (@Some out oo) ->
        abort oo ->
        not (abort_intercepted_expr (spec_call_object_define_props_6 a1 a2)) ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq ext_expr exte (spec_call_object_define_props_6 a1 a2) ->
        @eq out o oo -> P S C a1 a2 oo) ->
       (red_expr S C (spec_call_object_define_props_6 a1 a2) oo ->
        forall (S0 : state) (C0 : execution_ctx) (l : object_loc)
          (x : prop_name) (A : attributes)
          (xAs : list (prod prop_name attributes)) 
          (o1 o : out),
        red_expr S C
          (spec_object_define_own_prop a1 x (descriptor_of_attributes A)
             throw_true) o1 ->
        red_expr S C (spec_call_object_define_props_7 o1 a1 xAs) oo ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq object_loc l a1 ->
        @eq (list (prod prop_name attributes))
          (@cons (prod prop_name attributes) (@pair prop_name attributes x A)
             xAs) a2 ->
        @eq out o oo ->
        P S C a1
          (@cons (prod prop_name attributes) (@pair prop_name attributes x A)
             xAs) oo) ->
       (red_expr S C (spec_call_object_define_props_6 a1 a2) oo ->
        forall (S0 : state) (C0 : execution_ctx) (l : object_loc),
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq object_loc l a1 ->
        @eq (list (prod prop_name attributes))
          (@nil (prod prop_name attributes)) a2 ->
        @eq out (out_ter S (res_val (value_object a1))) oo ->
        P S C a1 (@nil (prod prop_name attributes))
          (out_ter S (res_val (value_object a1)))) ->
       red_expr S C (spec_call_object_define_props_6 a1 a2) oo ->
       P S C a1 a2 oo.

Parameter inv_red_expr_spec_call_object_define_props_7
     : forall (S : state) (C : execution_ctx) (a1 : out) 
         (a2 : object_loc) (a3 : list (prod prop_name attributes)) 
         (oo : out)
         (P : state ->
              execution_ctx ->
              out ->
              object_loc -> list (prod string attributes) -> out -> Prop),
       (red_expr S C (spec_call_object_define_props_7 a1 a2 a3) oo ->
        forall (S0 : state) (C0 : execution_ctx) (exte : ext_expr) (o : out),
        @eq (option out)
          (out_of_ext_expr (spec_call_object_define_props_7 a1 a2 a3))
          (@Some out oo) ->
        abort oo ->
        not
          (abort_intercepted_expr (spec_call_object_define_props_7 a1 a2 a3)) ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq ext_expr exte (spec_call_object_define_props_7 a1 a2 a3) ->
        @eq out o oo -> P S C a1 a2 a3 oo) ->
       (red_expr S C (spec_call_object_define_props_7 a1 a2 a3) oo ->
        forall (S0 S1 : state) (C0 : execution_ctx) 
          (l : object_loc) (xAs : list (prod prop_name attributes))
          (b : bool) (o : out),
        red_expr S1 C (spec_call_object_define_props_6 a2 a3) oo ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq out (out_ter S1 (res_val (value_prim (prim_bool b)))) a1 ->
        @eq object_loc l a2 ->
        @eq (list (prod prop_name attributes)) xAs a3 ->
        @eq out o oo ->
        P S C (out_ter S1 (res_val (value_prim (prim_bool b)))) a2 a3 oo) ->
       red_expr S C (spec_call_object_define_props_7 a1 a2 a3) oo ->
       P S C a1 a2 a3 oo.

Parameter inv_red_expr_spec_call_object_create_1
     : forall (S : state) (C : execution_ctx) (a1 a2 : value) 
         (oo : out)
         (P : state -> execution_ctx -> value -> value -> out -> Prop),
       (red_expr S C (spec_call_object_create_1 a1 a2) oo ->
        forall (S0 : state) (C0 : execution_ctx) (exte : ext_expr) (o : out),
        @eq (option out) (out_of_ext_expr (spec_call_object_create_1 a1 a2))
          (@Some out oo) ->
        abort oo ->
        not (abort_intercepted_expr (spec_call_object_create_1 a1 a2)) ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq ext_expr exte (spec_call_object_create_1 a1 a2) ->
        @eq out o oo -> P S C a1 a2 oo) ->
       (red_expr S C (spec_call_object_create_1 a1 a2) oo ->
        forall (S0 : state) (C0 : execution_ctx) (vo vp : value) (o : out),
        not (@eq type (type_of a1) type_object) ->
        not (@eq type (type_of a1) type_null) ->
        red_expr S C (spec_error native_error_type) oo ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq value vo a1 -> @eq value vp a2 -> @eq out o oo -> P S C a1 a2 oo) ->
       (red_expr S C (spec_call_object_create_1 a1 a2) oo ->
        forall (S0 : state) (C0 : execution_ctx) (vo vp : value) (o o1 : out),
        red_expr S C (spec_construct_prealloc prealloc_object (@nil value))
          o1 ->
        red_expr S C (spec_call_object_create_2 o1 a1 a2) oo ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq value vo a1 -> @eq value vp a2 -> @eq out o oo -> P S C a1 a2 oo) ->
       red_expr S C (spec_call_object_create_1 a1 a2) oo -> P S C a1 a2 oo.

Parameter inv_red_expr_spec_call_object_create_2
     : forall (S : state) (C : execution_ctx) (a1 : out) 
         (a2 a3 : value) (oo : out)
         (P : state -> execution_ctx -> out -> value -> value -> out -> Prop),
       (red_expr S C (spec_call_object_create_2 a1 a2 a3) oo ->
        forall (S0 : state) (C0 : execution_ctx) (exte : ext_expr) (o : out),
        @eq (option out)
          (out_of_ext_expr (spec_call_object_create_2 a1 a2 a3))
          (@Some out oo) ->
        abort oo ->
        not (abort_intercepted_expr (spec_call_object_create_2 a1 a2 a3)) ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq ext_expr exte (spec_call_object_create_2 a1 a2 a3) ->
        @eq out o oo -> P S C a1 a2 a3 oo) ->
       (red_expr S C (spec_call_object_create_2 a1 a2 a3) oo ->
        forall (S0 S1 : state) (C0 : execution_ctx) 
          (l : object_loc) (O O' : object) (S' : state) 
          (vo vp : value) (o : out),
        object_binds S0 l O ->
        @eq object O' (object_set_proto O a2) ->
        @eq state S' (object_write S0 l O') ->
        red_expr S' C (spec_call_object_create_3 l a3) oo ->
        @eq state S1 S ->
        @eq execution_ctx C0 C ->
        @eq out (out_ter S0 (res_val (value_object l))) a1 ->
        @eq value vo a2 ->
        @eq value vp a3 ->
        @eq out o oo ->
        P S C (out_ter S0 (res_val (value_object l))) a2 a3 oo) ->
       red_expr S C (spec_call_object_create_2 a1 a2 a3) oo ->
       P S C a1 a2 a3 oo.

Parameter inv_red_expr_spec_call_object_create_3
     : forall (S : state) (C : execution_ctx) (a1 : object_loc) 
         (a2 : value) (oo : out)
         (P : state -> execution_ctx -> object_loc -> value -> out -> Prop),
       (red_expr S C (spec_call_object_create_3 a1 a2) oo ->
        forall (S0 : state) (C0 : execution_ctx) (exte : ext_expr) (o : out),
        @eq (option out) (out_of_ext_expr (spec_call_object_create_3 a1 a2))
          (@Some out oo) ->
        abort oo ->
        not (abort_intercepted_expr (spec_call_object_create_3 a1 a2)) ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq ext_expr exte (spec_call_object_create_3 a1 a2) ->
        @eq out o oo -> P S C a1 a2 oo) ->
       (red_expr S C (spec_call_object_create_3 a1 a2) oo ->
        forall (S0 : state) (C0 : execution_ctx) (l : object_loc)
          (vp : value) (o : out),
        not (@eq value a2 (value_prim prim_undef)) ->
        red_expr S C (spec_call_object_define_props_1 (value_object a1) a2)
          oo ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq object_loc l a1 ->
        @eq value vp a2 -> @eq out o oo -> P S C a1 a2 oo) ->
       (red_expr S C (spec_call_object_create_3 a1 a2) oo ->
        forall (S0 : state) (C0 : execution_ctx) (l : object_loc),
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq object_loc l a1 ->
        @eq value (value_prim prim_undef) a2 ->
        @eq out (out_ter S (res_val (value_object a1))) oo ->
        P S C a1 (value_prim prim_undef)
          (out_ter S (res_val (value_object a1)))) ->
       red_expr S C (spec_call_object_create_3 a1 a2) oo -> P S C a1 a2 oo.

Parameter inv_red_expr_spec_call_object_seal_1
     : forall (S : state) (C : execution_ctx) (a1 : value) 
         (oo : out) (P : state -> execution_ctx -> value -> out -> Prop),
       (red_expr S C (spec_call_object_seal_1 a1) oo ->
        forall (S0 : state) (C0 : execution_ctx) (exte : ext_expr) (o : out),
        @eq (option out) (out_of_ext_expr (spec_call_object_seal_1 a1))
          (@Some out oo) ->
        abort oo ->
        not (abort_intercepted_expr (spec_call_object_seal_1 a1)) ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq ext_expr exte (spec_call_object_seal_1 a1) ->
        @eq out o oo -> P S C a1 oo) ->
       (red_expr S C (spec_call_object_seal_1 a1) oo ->
        forall (S0 : state) (C0 : execution_ctx) (v : value) (o : out),
        not (@eq type (type_of a1) type_object) ->
        red_expr S C (spec_error native_error_type) oo ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq value v a1 -> @eq out o oo -> P S C a1 oo) ->
       (red_expr S C (spec_call_object_seal_1 a1) oo ->
        forall (S0 : state) (C0 : execution_ctx) (l : object_loc)
          (xs : list prop_name) (o : out),
        object_properties_keys_as_list S l xs ->
        red_expr S C (spec_call_object_seal_2 l xs) oo ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq value (value_object l) a1 ->
        @eq out o oo -> P S C (value_object l) oo) ->
       red_expr S C (spec_call_object_seal_1 a1) oo -> P S C a1 oo.

Parameter inv_red_expr_spec_call_object_seal_2
     : forall (S : state) (C : execution_ctx) (a1 : object_loc)
         (a2 : list prop_name) (oo : out)
         (P : state ->
              execution_ctx -> object_loc -> list string -> out -> Prop),
       (red_expr S C (spec_call_object_seal_2 a1 a2) oo ->
        forall (S0 : state) (C0 : execution_ctx) (exte : ext_expr) (o : out),
        @eq (option out) (out_of_ext_expr (spec_call_object_seal_2 a1 a2))
          (@Some out oo) ->
        abort oo ->
        not (abort_intercepted_expr (spec_call_object_seal_2 a1 a2)) ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq ext_expr exte (spec_call_object_seal_2 a1 a2) ->
        @eq out o oo -> P S C a1 a2 oo) ->
       (red_expr S C (spec_call_object_seal_2 a1 a2) oo ->
        forall (S0 : state) (C0 : execution_ctx) (l : object_loc)
          (xs : list prop_name) (x : prop_name) (o : out)
          (y : specret full_descriptor),
        @red_spec full_descriptor S C (spec_object_get_own_prop a1 x) y ->
        red_expr S C (spec_call_object_seal_3 a1 x xs y) oo ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq object_loc l a1 ->
        @eq (list prop_name) (@cons prop_name x xs) a2 ->
        @eq out o oo -> P S C a1 (@cons prop_name x xs) oo) ->
       (red_expr S C (spec_call_object_seal_2 a1 a2) oo ->
        forall (S0 S' : state) (C0 : execution_ctx) (l : object_loc),
        object_heap_set_extensible false S a1 S' ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq object_loc l a1 ->
        @eq (list prop_name) (@nil prop_name) a2 ->
        @eq out (out_ter S' (res_val (value_object a1))) oo ->
        P S C a1 (@nil prop_name) (out_ter S' (res_val (value_object a1)))) ->
       red_expr S C (spec_call_object_seal_2 a1 a2) oo -> P S C a1 a2 oo.

Parameter inv_red_expr_spec_call_object_seal_3
     : forall (S : state) (C : execution_ctx) (a1 : object_loc)
         (a2 : prop_name) (a3 : list prop_name)
         (a4 : specret full_descriptor) (oo : out)
         (P : state ->
              execution_ctx ->
              object_loc ->
              string -> list string -> specret full_descriptor -> out -> Prop),
       (red_expr S C (spec_call_object_seal_3 a1 a2 a3 a4) oo ->
        forall (S0 : state) (C0 : execution_ctx) (exte : ext_expr) (o : out),
        @eq (option out)
          (out_of_ext_expr (spec_call_object_seal_3 a1 a2 a3 a4))
          (@Some out oo) ->
        abort oo ->
        not (abort_intercepted_expr (spec_call_object_seal_3 a1 a2 a3 a4)) ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq ext_expr exte (spec_call_object_seal_3 a1 a2 a3 a4) ->
        @eq out o oo -> P S C a1 a2 a3 a4 oo) ->
       (red_expr S C (spec_call_object_seal_3 a1 a2 a3 a4) oo ->
        forall (S0 S1 : state) (C0 : execution_ctx) 
          (l : object_loc) (xs : list prop_name) (x : prop_name)
          (A A' : attributes) (o1 o : out),
        @eq attributes A'
          match
            classicT (istrue (attributes_configurable A)) return attributes
          with
          | left _ => attributes_with_configurable A false
          | right _ => A
          end ->
        red_expr S1 C
          (spec_object_define_own_prop a1 a2 (descriptor_of_attributes A')
             throw_true) o1 ->
        red_expr S1 C (spec_call_object_seal_4 a1 a3 o1) oo ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq object_loc l a1 ->
        @eq prop_name x a2 ->
        @eq (list prop_name) xs a3 ->
        @eq (specret full_descriptor) (dret S1 (full_descriptor_some A)) a4 ->
        @eq out o oo -> P S C a1 a2 a3 (dret S1 (full_descriptor_some A)) oo) ->
       red_expr S C (spec_call_object_seal_3 a1 a2 a3 a4) oo ->
       P S C a1 a2 a3 a4 oo.

Parameter inv_red_expr_spec_call_object_seal_4
     : forall (S : state) (C : execution_ctx) (a1 : object_loc)
         (a2 : list prop_name) (a3 oo : out)
         (P : state ->
              execution_ctx ->
              object_loc -> list string -> out -> out -> Prop),
       (red_expr S C (spec_call_object_seal_4 a1 a2 a3) oo ->
        forall (S0 : state) (C0 : execution_ctx) (exte : ext_expr) (o : out),
        @eq (option out) (out_of_ext_expr (spec_call_object_seal_4 a1 a2 a3))
          (@Some out oo) ->
        abort oo ->
        not (abort_intercepted_expr (spec_call_object_seal_4 a1 a2 a3)) ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq ext_expr exte (spec_call_object_seal_4 a1 a2 a3) ->
        @eq out o oo -> P S C a1 a2 a3 oo) ->
       (red_expr S C (spec_call_object_seal_4 a1 a2 a3) oo ->
        forall (S0 S1 : state) (C0 : execution_ctx) 
          (l : object_loc) (xs : list prop_name) (b : bool) 
          (o : out),
        red_expr S1 C (spec_call_object_seal_2 a1 a2) oo ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq object_loc l a1 ->
        @eq (list prop_name) xs a2 ->
        @eq out (out_ter S1 (res_val (value_prim (prim_bool b)))) a3 ->
        @eq out o oo ->
        P S C a1 a2 (out_ter S1 (res_val (value_prim (prim_bool b)))) oo) ->
       red_expr S C (spec_call_object_seal_4 a1 a2 a3) oo ->
       P S C a1 a2 a3 oo.

Parameter inv_red_expr_spec_call_object_is_sealed_1
     : forall (S : state) (C : execution_ctx) (a1 : value) 
         (oo : out) (P : state -> execution_ctx -> value -> out -> Prop),
       (red_expr S C (spec_call_object_is_sealed_1 a1) oo ->
        forall (S0 : state) (C0 : execution_ctx) (exte : ext_expr) (o : out),
        @eq (option out) (out_of_ext_expr (spec_call_object_is_sealed_1 a1))
          (@Some out oo) ->
        abort oo ->
        not (abort_intercepted_expr (spec_call_object_is_sealed_1 a1)) ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq ext_expr exte (spec_call_object_is_sealed_1 a1) ->
        @eq out o oo -> P S C a1 oo) ->
       (red_expr S C (spec_call_object_is_sealed_1 a1) oo ->
        forall (S0 : state) (C0 : execution_ctx) (v : value) (o : out),
        not (@eq type (type_of a1) type_object) ->
        red_expr S C (spec_error native_error_type) oo ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq value v a1 -> @eq out o oo -> P S C a1 oo) ->
       (red_expr S C (spec_call_object_is_sealed_1 a1) oo ->
        forall (S0 : state) (C0 : execution_ctx) (l : object_loc)
          (xs : list prop_name) (o : out),
        object_properties_keys_as_list S l xs ->
        red_expr S C (spec_call_object_is_sealed_2 l xs) oo ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq value (value_object l) a1 ->
        @eq out o oo -> P S C (value_object l) oo) ->
       red_expr S C (spec_call_object_is_sealed_1 a1) oo -> P S C a1 oo.

Parameter inv_red_expr_spec_call_object_is_sealed_2
     : forall (S : state) (C : execution_ctx) (a1 : object_loc)
         (a2 : list prop_name) (oo : out)
         (P : state ->
              execution_ctx -> object_loc -> list string -> out -> Prop),
       (red_expr S C (spec_call_object_is_sealed_2 a1 a2) oo ->
        forall (S0 : state) (C0 : execution_ctx) (exte : ext_expr) (o : out),
        @eq (option out)
          (out_of_ext_expr (spec_call_object_is_sealed_2 a1 a2))
          (@Some out oo) ->
        abort oo ->
        not (abort_intercepted_expr (spec_call_object_is_sealed_2 a1 a2)) ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq ext_expr exte (spec_call_object_is_sealed_2 a1 a2) ->
        @eq out o oo -> P S C a1 a2 oo) ->
       (red_expr S C (spec_call_object_is_sealed_2 a1 a2) oo ->
        forall (S0 : state) (C0 : execution_ctx) (l : object_loc)
          (xs : list prop_name) (x : prop_name) (o : out)
          (y : specret full_descriptor),
        @red_spec full_descriptor S C (spec_object_get_own_prop a1 x) y ->
        red_expr S C (spec_call_object_is_sealed_3 a1 xs y) oo ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq object_loc l a1 ->
        @eq (list prop_name) (@cons prop_name x xs) a2 ->
        @eq out o oo -> P S C a1 (@cons prop_name x xs) oo) ->
       (red_expr S C (spec_call_object_is_sealed_2 a1 a2) oo ->
        forall (S0 : state) (C0 : execution_ctx) (l : object_loc) (b : bool),
        object_extensible S a1 b ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq object_loc l a1 ->
        @eq (list prop_name) (@nil prop_name) a2 ->
        @eq out (out_ter S (res_val (value_prim (prim_bool (negb b))))) oo ->
        P S C a1 (@nil prop_name)
          (out_ter S (res_val (value_prim (prim_bool (negb b)))))) ->
       red_expr S C (spec_call_object_is_sealed_2 a1 a2) oo -> P S C a1 a2 oo.

Parameter inv_red_expr_spec_call_object_is_sealed_3
     : forall (S : state) (C : execution_ctx) (a1 : object_loc)
         (a2 : list prop_name) (a3 : specret full_descriptor) 
         (oo : out)
         (P : state ->
              execution_ctx ->
              object_loc ->
              list string -> specret full_descriptor -> out -> Prop),
       (red_expr S C (spec_call_object_is_sealed_3 a1 a2 a3) oo ->
        forall (S0 : state) (C0 : execution_ctx) (exte : ext_expr) (o : out),
        @eq (option out)
          (out_of_ext_expr (spec_call_object_is_sealed_3 a1 a2 a3))
          (@Some out oo) ->
        abort oo ->
        not (abort_intercepted_expr (spec_call_object_is_sealed_3 a1 a2 a3)) ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq ext_expr exte (spec_call_object_is_sealed_3 a1 a2 a3) ->
        @eq out o oo -> P S C a1 a2 a3 oo) ->
       (red_expr S C (spec_call_object_is_sealed_3 a1 a2 a3) oo ->
        forall (S0 S1 : state) (C0 : execution_ctx) 
          (A : attributes) (xs : list prop_name) (l : object_loc),
        @eq bool (attributes_configurable A) true ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq object_loc l a1 ->
        @eq (list prop_name) xs a2 ->
        @eq (specret full_descriptor) (dret S1 (full_descriptor_some A)) a3 ->
        @eq out (out_ter S1 (res_val (value_prim (prim_bool false)))) oo ->
        P S C a1 a2 (dret S1 (full_descriptor_some A))
          (out_ter S1 (res_val (value_prim (prim_bool false))))) ->
       (red_expr S C (spec_call_object_is_sealed_3 a1 a2 a3) oo ->
        forall (S0 S1 : state) (C0 : execution_ctx) 
          (A : attributes) (xs : list prop_name) (l : object_loc) 
          (o : out),
        @eq bool (attributes_configurable A) false ->
        red_expr S1 C (spec_call_object_is_sealed_2 a1 a2) oo ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq object_loc l a1 ->
        @eq (list prop_name) xs a2 ->
        @eq (specret full_descriptor) (dret S1 (full_descriptor_some A)) a3 ->
        @eq out o oo -> P S C a1 a2 (dret S1 (full_descriptor_some A)) oo) ->
       red_expr S C (spec_call_object_is_sealed_3 a1 a2 a3) oo ->
       P S C a1 a2 a3 oo.

Parameter inv_red_expr_spec_call_object_freeze_1
     : forall (S : state) (C : execution_ctx) (a1 : value) 
         (oo : out) (P : state -> execution_ctx -> value -> out -> Prop),
       (red_expr S C (spec_call_object_freeze_1 a1) oo ->
        forall (S0 : state) (C0 : execution_ctx) (exte : ext_expr) (o : out),
        @eq (option out) (out_of_ext_expr (spec_call_object_freeze_1 a1))
          (@Some out oo) ->
        abort oo ->
        not (abort_intercepted_expr (spec_call_object_freeze_1 a1)) ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq ext_expr exte (spec_call_object_freeze_1 a1) ->
        @eq out o oo -> P S C a1 oo) ->
       (red_expr S C (spec_call_object_freeze_1 a1) oo ->
        forall (S0 : state) (C0 : execution_ctx) (v : value) (o : out),
        not (@eq type (type_of a1) type_object) ->
        red_expr S C (spec_error native_error_type) oo ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq value v a1 -> @eq out o oo -> P S C a1 oo) ->
       (red_expr S C (spec_call_object_freeze_1 a1) oo ->
        forall (S0 : state) (C0 : execution_ctx) (l : object_loc)
          (xs : list prop_name) (o : out),
        object_properties_keys_as_list S l xs ->
        red_expr S C (spec_call_object_freeze_2 l xs) oo ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq value (value_object l) a1 ->
        @eq out o oo -> P S C (value_object l) oo) ->
       red_expr S C (spec_call_object_freeze_1 a1) oo -> P S C a1 oo.

Parameter inv_red_expr_spec_call_object_freeze_2
     : forall (S : state) (C : execution_ctx) (a1 : object_loc)
         (a2 : list prop_name) (oo : out)
         (P : state ->
              execution_ctx -> object_loc -> list string -> out -> Prop),
       (red_expr S C (spec_call_object_freeze_2 a1 a2) oo ->
        forall (S0 : state) (C0 : execution_ctx) (exte : ext_expr) (o : out),
        @eq (option out) (out_of_ext_expr (spec_call_object_freeze_2 a1 a2))
          (@Some out oo) ->
        abort oo ->
        not (abort_intercepted_expr (spec_call_object_freeze_2 a1 a2)) ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq ext_expr exte (spec_call_object_freeze_2 a1 a2) ->
        @eq out o oo -> P S C a1 a2 oo) ->
       (red_expr S C (spec_call_object_freeze_2 a1 a2) oo ->
        forall (S0 : state) (C0 : execution_ctx) (l : object_loc)
          (xs : list prop_name) (x : prop_name) (o : out)
          (y : specret full_descriptor),
        @red_spec full_descriptor S C (spec_object_get_own_prop a1 x) y ->
        red_expr S C (spec_call_object_freeze_3 a1 x xs y) oo ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq object_loc l a1 ->
        @eq (list prop_name) (@cons prop_name x xs) a2 ->
        @eq out o oo -> P S C a1 (@cons prop_name x xs) oo) ->
       (red_expr S C (spec_call_object_freeze_2 a1 a2) oo ->
        forall (S0 S' : state) (C0 : execution_ctx) (l : object_loc),
        object_heap_set_extensible false S a1 S' ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq object_loc l a1 ->
        @eq (list prop_name) (@nil prop_name) a2 ->
        @eq out (out_ter S' (res_val (value_object a1))) oo ->
        P S C a1 (@nil prop_name) (out_ter S' (res_val (value_object a1)))) ->
       red_expr S C (spec_call_object_freeze_2 a1 a2) oo -> P S C a1 a2 oo.

Parameter inv_red_expr_spec_call_object_freeze_3
     : forall (S : state) (C : execution_ctx) (a1 : object_loc)
         (a2 : prop_name) (a3 : list prop_name)
         (a4 : specret full_descriptor) (oo : out)
         (P : state ->
              execution_ctx ->
              object_loc ->
              string -> list string -> specret full_descriptor -> out -> Prop),
       (red_expr S C (spec_call_object_freeze_3 a1 a2 a3 a4) oo ->
        forall (S0 : state) (C0 : execution_ctx) (exte : ext_expr) (o : out),
        @eq (option out)
          (out_of_ext_expr (spec_call_object_freeze_3 a1 a2 a3 a4))
          (@Some out oo) ->
        abort oo ->
        not (abort_intercepted_expr (spec_call_object_freeze_3 a1 a2 a3 a4)) ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq ext_expr exte (spec_call_object_freeze_3 a1 a2 a3 a4) ->
        @eq out o oo -> P S C a1 a2 a3 a4 oo) ->
       (red_expr S C (spec_call_object_freeze_3 a1 a2 a3 a4) oo ->
        forall (S0 S1 : state) (C0 : execution_ctx) 
          (A A' : attributes) (xs : list prop_name) 
          (l : object_loc) (x : prop_name) (o : out),
        @eq attributes A'
          match A return attributes with
          | attributes_data_of Ad =>
              attributes_data_of
                match
                  classicT (istrue (attributes_data_writable Ad))
                  return attributes_data
                with
                | left _ => attributes_data_with_writable Ad false
                | right _ => Ad
                end
          | attributes_accessor_of Aa => attributes_accessor_of Aa
          end ->
        red_expr S1 C
          (spec_call_object_freeze_4 a1 a2 a3 (full_descriptor_some A')) oo ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq object_loc l a1 ->
        @eq prop_name x a2 ->
        @eq (list prop_name) xs a3 ->
        @eq (specret full_descriptor) (dret S1 (full_descriptor_some A)) a4 ->
        @eq out o oo -> P S C a1 a2 a3 (dret S1 (full_descriptor_some A)) oo) ->
       red_expr S C (spec_call_object_freeze_3 a1 a2 a3 a4) oo ->
       P S C a1 a2 a3 a4 oo.

Parameter inv_red_expr_spec_call_object_freeze_4
     : forall (S : state) (C : execution_ctx) (a1 : object_loc)
         (a2 : prop_name) (a3 : list prop_name) (a4 : full_descriptor)
         (oo : out)
         (P : state ->
              execution_ctx ->
              object_loc ->
              string -> list string -> full_descriptor -> out -> Prop),
       (red_expr S C (spec_call_object_freeze_4 a1 a2 a3 a4) oo ->
        forall (S0 : state) (C0 : execution_ctx) (exte : ext_expr) (o : out),
        @eq (option out)
          (out_of_ext_expr (spec_call_object_freeze_4 a1 a2 a3 a4))
          (@Some out oo) ->
        abort oo ->
        not (abort_intercepted_expr (spec_call_object_freeze_4 a1 a2 a3 a4)) ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq ext_expr exte (spec_call_object_freeze_4 a1 a2 a3 a4) ->
        @eq out o oo -> P S C a1 a2 a3 a4 oo) ->
       (red_expr S C (spec_call_object_freeze_4 a1 a2 a3 a4) oo ->
        forall (S0 : state) (C0 : execution_ctx) (A A' : attributes)
          (xs : list prop_name) (l : object_loc) (x : prop_name) 
          (o1 o : out),
        @eq attributes A'
          match
            classicT (istrue (attributes_configurable A)) return attributes
          with
          | left _ => attributes_with_configurable A false
          | right _ => A
          end ->
        red_expr S C
          (spec_object_define_own_prop a1 a2 (descriptor_of_attributes A')
             throw_true) o1 ->
        red_expr S C (spec_call_object_freeze_5 a1 a3 o1) oo ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq object_loc l a1 ->
        @eq prop_name x a2 ->
        @eq (list prop_name) xs a3 ->
        @eq full_descriptor (full_descriptor_some A) a4 ->
        @eq out o oo -> P S C a1 a2 a3 (full_descriptor_some A) oo) ->
       red_expr S C (spec_call_object_freeze_4 a1 a2 a3 a4) oo ->
       P S C a1 a2 a3 a4 oo.

Parameter inv_red_expr_spec_call_object_freeze_5
     : forall (S : state) (C : execution_ctx) (a1 : object_loc)
         (a2 : list prop_name) (a3 oo : out)
         (P : state ->
              execution_ctx ->
              object_loc -> list string -> out -> out -> Prop),
       (red_expr S C (spec_call_object_freeze_5 a1 a2 a3) oo ->
        forall (S0 : state) (C0 : execution_ctx) (exte : ext_expr) (o : out),
        @eq (option out)
          (out_of_ext_expr (spec_call_object_freeze_5 a1 a2 a3))
          (@Some out oo) ->
        abort oo ->
        not (abort_intercepted_expr (spec_call_object_freeze_5 a1 a2 a3)) ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq ext_expr exte (spec_call_object_freeze_5 a1 a2 a3) ->
        @eq out o oo -> P S C a1 a2 a3 oo) ->
       (red_expr S C (spec_call_object_freeze_5 a1 a2 a3) oo ->
        forall (S0 S1 : state) (C0 : execution_ctx) 
          (xs : list prop_name) (l : object_loc) (b : bool) 
          (o : out),
        red_expr S1 C (spec_call_object_freeze_2 a1 a2) oo ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq object_loc l a1 ->
        @eq (list prop_name) xs a2 ->
        @eq out (out_ter S1 (res_val (value_prim (prim_bool b)))) a3 ->
        @eq out o oo ->
        P S C a1 a2 (out_ter S1 (res_val (value_prim (prim_bool b)))) oo) ->
       red_expr S C (spec_call_object_freeze_5 a1 a2 a3) oo ->
       P S C a1 a2 a3 oo.

Parameter inv_red_expr_spec_call_object_is_frozen_1
     : forall (S : state) (C : execution_ctx) (a1 : value) 
         (oo : out) (P : state -> execution_ctx -> value -> out -> Prop),
       (red_expr S C (spec_call_object_is_frozen_1 a1) oo ->
        forall (S0 : state) (C0 : execution_ctx) (exte : ext_expr) (o : out),
        @eq (option out) (out_of_ext_expr (spec_call_object_is_frozen_1 a1))
          (@Some out oo) ->
        abort oo ->
        not (abort_intercepted_expr (spec_call_object_is_frozen_1 a1)) ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq ext_expr exte (spec_call_object_is_frozen_1 a1) ->
        @eq out o oo -> P S C a1 oo) ->
       (red_expr S C (spec_call_object_is_frozen_1 a1) oo ->
        forall (S0 : state) (C0 : execution_ctx) (v : value) (o : out),
        not (@eq type (type_of a1) type_object) ->
        red_expr S C (spec_error native_error_type) oo ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq value v a1 -> @eq out o oo -> P S C a1 oo) ->
       (red_expr S C (spec_call_object_is_frozen_1 a1) oo ->
        forall (S0 : state) (C0 : execution_ctx) (l : object_loc)
          (xs : list prop_name) (o : out),
        object_properties_keys_as_list S l xs ->
        red_expr S C (spec_call_object_is_frozen_2 l xs) oo ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq value (value_object l) a1 ->
        @eq out o oo -> P S C (value_object l) oo) ->
       red_expr S C (spec_call_object_is_frozen_1 a1) oo -> P S C a1 oo.

Parameter inv_red_expr_spec_call_object_is_frozen_2
     : forall (S : state) (C : execution_ctx) (a1 : object_loc)
         (a2 : list prop_name) (oo : out)
         (P : state ->
              execution_ctx -> object_loc -> list string -> out -> Prop),
       (red_expr S C (spec_call_object_is_frozen_2 a1 a2) oo ->
        forall (S0 : state) (C0 : execution_ctx) (exte : ext_expr) (o : out),
        @eq (option out)
          (out_of_ext_expr (spec_call_object_is_frozen_2 a1 a2))
          (@Some out oo) ->
        abort oo ->
        not (abort_intercepted_expr (spec_call_object_is_frozen_2 a1 a2)) ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq ext_expr exte (spec_call_object_is_frozen_2 a1 a2) ->
        @eq out o oo -> P S C a1 a2 oo) ->
       (red_expr S C (spec_call_object_is_frozen_2 a1 a2) oo ->
        forall (S0 : state) (C0 : execution_ctx) (l : object_loc)
          (xs : list prop_name) (x : prop_name) (o : out)
          (y : specret full_descriptor),
        @red_spec full_descriptor S C (spec_object_get_own_prop a1 x) y ->
        red_expr S C (spec_call_object_is_frozen_3 a1 xs y) oo ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq object_loc l a1 ->
        @eq (list prop_name) (@cons prop_name x xs) a2 ->
        @eq out o oo -> P S C a1 (@cons prop_name x xs) oo) ->
       (red_expr S C (spec_call_object_is_frozen_2 a1 a2) oo ->
        forall (S0 : state) (C0 : execution_ctx) (l : object_loc) (b : bool),
        object_extensible S a1 b ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq object_loc l a1 ->
        @eq (list prop_name) (@nil prop_name) a2 ->
        @eq out (out_ter S (res_val (value_prim (prim_bool (negb b))))) oo ->
        P S C a1 (@nil prop_name)
          (out_ter S (res_val (value_prim (prim_bool (negb b)))))) ->
       red_expr S C (spec_call_object_is_frozen_2 a1 a2) oo -> P S C a1 a2 oo.

Parameter inv_red_expr_spec_call_object_is_frozen_3
     : forall (S : state) (C : execution_ctx) (a1 : object_loc)
         (a2 : list prop_name) (a3 : specret full_descriptor) 
         (oo : out)
         (P : state ->
              execution_ctx ->
              object_loc ->
              list string -> specret full_descriptor -> out -> Prop),
       (red_expr S C (spec_call_object_is_frozen_3 a1 a2 a3) oo ->
        forall (S0 : state) (C0 : execution_ctx) (exte : ext_expr) (o : out),
        @eq (option out)
          (out_of_ext_expr (spec_call_object_is_frozen_3 a1 a2 a3))
          (@Some out oo) ->
        abort oo ->
        not (abort_intercepted_expr (spec_call_object_is_frozen_3 a1 a2 a3)) ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq ext_expr exte (spec_call_object_is_frozen_3 a1 a2 a3) ->
        @eq out o oo -> P S C a1 a2 a3 oo) ->
       (red_expr S C (spec_call_object_is_frozen_3 a1 a2 a3) oo ->
        forall (S0 S1 : state) (C0 : execution_ctx) 
          (A : attributes) (xs : list prop_name) (l : object_loc) 
          (o : out),
        attributes_is_data A ->
        red_expr S1 C
          (spec_call_object_is_frozen_4 a1 a2 (full_descriptor_some A)) oo ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq object_loc l a1 ->
        @eq (list prop_name) xs a2 ->
        @eq (specret full_descriptor) (dret S1 (full_descriptor_some A)) a3 ->
        @eq out o oo -> P S C a1 a2 (dret S1 (full_descriptor_some A)) oo) ->
       (red_expr S C (spec_call_object_is_frozen_3 a1 a2 a3) oo ->
        forall (S0 S1 : state) (C0 : execution_ctx) 
          (A : attributes) (xs : list prop_name) (l : object_loc) 
          (o : out),
        not (attributes_is_data A) ->
        red_expr S1 C
          (spec_call_object_is_frozen_5 a1 a2 (full_descriptor_some A)) oo ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq object_loc l a1 ->
        @eq (list prop_name) xs a2 ->
        @eq (specret full_descriptor) (dret S1 (full_descriptor_some A)) a3 ->
        @eq out o oo -> P S C a1 a2 (dret S1 (full_descriptor_some A)) oo) ->
       red_expr S C (spec_call_object_is_frozen_3 a1 a2 a3) oo ->
       P S C a1 a2 a3 oo.

Parameter inv_red_expr_spec_call_object_is_frozen_4
     : forall (S : state) (C : execution_ctx) (a1 : object_loc)
         (a2 : list prop_name) (a3 : full_descriptor) 
         (oo : out)
         (P : state ->
              execution_ctx ->
              object_loc -> list string -> full_descriptor -> out -> Prop),
       (red_expr S C (spec_call_object_is_frozen_4 a1 a2 a3) oo ->
        forall (S0 : state) (C0 : execution_ctx) (exte : ext_expr) (o : out),
        @eq (option out)
          (out_of_ext_expr (spec_call_object_is_frozen_4 a1 a2 a3))
          (@Some out oo) ->
        abort oo ->
        not (abort_intercepted_expr (spec_call_object_is_frozen_4 a1 a2 a3)) ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq ext_expr exte (spec_call_object_is_frozen_4 a1 a2 a3) ->
        @eq out o oo -> P S C a1 a2 a3 oo) ->
       (red_expr S C (spec_call_object_is_frozen_4 a1 a2 a3) oo ->
        forall (S0 : state) (C0 : execution_ctx) (A : attributes)
          (xs : list prop_name) (l : object_loc),
        @eq bool (attributes_writable A) true ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq object_loc l a1 ->
        @eq (list prop_name) xs a2 ->
        @eq full_descriptor (full_descriptor_some A) a3 ->
        @eq out (out_ter S (res_val (value_prim (prim_bool false)))) oo ->
        P S C a1 a2 (full_descriptor_some A)
          (out_ter S (res_val (value_prim (prim_bool false))))) ->
       (red_expr S C (spec_call_object_is_frozen_4 a1 a2 a3) oo ->
        forall (S0 : state) (C0 : execution_ctx) (A : attributes)
          (xs : list prop_name) (l : object_loc) (o : out),
        @eq bool (attributes_writable A) false ->
        red_expr S C
          (spec_call_object_is_frozen_5 a1 a2 (full_descriptor_some A)) oo ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq object_loc l a1 ->
        @eq (list prop_name) xs a2 ->
        @eq full_descriptor (full_descriptor_some A) a3 ->
        @eq out o oo -> P S C a1 a2 (full_descriptor_some A) oo) ->
       red_expr S C (spec_call_object_is_frozen_4 a1 a2 a3) oo ->
       P S C a1 a2 a3 oo.

Parameter inv_red_expr_spec_call_object_is_frozen_5
     : forall (S : state) (C : execution_ctx) (a1 : object_loc)
         (a2 : list prop_name) (a3 : full_descriptor) 
         (oo : out)
         (P : state ->
              execution_ctx ->
              object_loc -> list string -> full_descriptor -> out -> Prop),
       (red_expr S C (spec_call_object_is_frozen_5 a1 a2 a3) oo ->
        forall (S0 : state) (C0 : execution_ctx) (exte : ext_expr) (o : out),
        @eq (option out)
          (out_of_ext_expr (spec_call_object_is_frozen_5 a1 a2 a3))
          (@Some out oo) ->
        abort oo ->
        not (abort_intercepted_expr (spec_call_object_is_frozen_5 a1 a2 a3)) ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq ext_expr exte (spec_call_object_is_frozen_5 a1 a2 a3) ->
        @eq out o oo -> P S C a1 a2 a3 oo) ->
       (red_expr S C (spec_call_object_is_frozen_5 a1 a2 a3) oo ->
        forall (S0 : state) (C0 : execution_ctx) (A : attributes)
          (xs : list prop_name) (l : object_loc),
        @eq bool (attributes_configurable A) true ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq object_loc l a1 ->
        @eq (list prop_name) xs a2 ->
        @eq full_descriptor (full_descriptor_some A) a3 ->
        @eq out (out_ter S (res_val (value_prim (prim_bool false)))) oo ->
        P S C a1 a2 (full_descriptor_some A)
          (out_ter S (res_val (value_prim (prim_bool false))))) ->
       (red_expr S C (spec_call_object_is_frozen_5 a1 a2 a3) oo ->
        forall (S0 : state) (C0 : execution_ctx) (A : attributes)
          (xs : list prop_name) (l : object_loc) (o : out),
        @eq bool (attributes_configurable A) false ->
        red_expr S C (spec_call_object_is_frozen_2 a1 a2) oo ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq object_loc l a1 ->
        @eq (list prop_name) xs a2 ->
        @eq full_descriptor (full_descriptor_some A) a3 ->
        @eq out o oo -> P S C a1 a2 (full_descriptor_some A) oo) ->
       red_expr S C (spec_call_object_is_frozen_5 a1 a2 a3) oo ->
       P S C a1 a2 a3 oo.

Parameter inv_red_expr_spec_call_object_prevent_extensions_1
     : forall (S : state) (C : execution_ctx) (a1 : value) 
         (oo : out) (P : state -> execution_ctx -> value -> out -> Prop),
       (red_expr S C (spec_call_object_prevent_extensions_1 a1) oo ->
        forall (S0 : state) (C0 : execution_ctx) (exte : ext_expr) (o : out),
        @eq (option out)
          (out_of_ext_expr (spec_call_object_prevent_extensions_1 a1))
          (@Some out oo) ->
        abort oo ->
        not
          (abort_intercepted_expr (spec_call_object_prevent_extensions_1 a1)) ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq ext_expr exte (spec_call_object_prevent_extensions_1 a1) ->
        @eq out o oo -> P S C a1 oo) ->
       (red_expr S C (spec_call_object_prevent_extensions_1 a1) oo ->
        forall (S0 : state) (C0 : execution_ctx) (v : value) (o : out),
        not (@eq type (type_of a1) type_object) ->
        red_expr S C (spec_error native_error_type) oo ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq value v a1 -> @eq out o oo -> P S C a1 oo) ->
       (red_expr S C (spec_call_object_prevent_extensions_1 a1) oo ->
        forall (S0 S' : state) (C0 : execution_ctx) 
          (O O' : object) (l : object_loc),
        object_binds S l O ->
        @eq object O' (object_with_extension O false) ->
        @eq state S' (object_write S l O') ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq value (value_object l) a1 ->
        @eq out (out_ter S' (res_val (value_object l))) oo ->
        P S C (value_object l) (out_ter S' (res_val (value_object l)))) ->
       red_expr S C (spec_call_object_prevent_extensions_1 a1) oo ->
       P S C a1 oo.

Parameter inv_red_expr_spec_call_object_define_prop_1
     : forall (S : state) (C : execution_ctx) (a1 a2 a3 : value) 
         (oo : out)
         (P : state ->
              execution_ctx -> value -> value -> value -> out -> Prop),
       (red_expr S C (spec_call_object_define_prop_1 a1 a2 a3) oo ->
        forall (S0 : state) (C0 : execution_ctx) (exte : ext_expr) (o : out),
        @eq (option out)
          (out_of_ext_expr (spec_call_object_define_prop_1 a1 a2 a3))
          (@Some out oo) ->
        abort oo ->
        not
          (abort_intercepted_expr (spec_call_object_define_prop_1 a1 a2 a3)) ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq ext_expr exte (spec_call_object_define_prop_1 a1 a2 a3) ->
        @eq out o oo -> P S C a1 a2 a3 oo) ->
       (red_expr S C (spec_call_object_define_prop_1 a1 a2 a3) oo ->
        forall (S0 : state) (C0 : execution_ctx) (vo vx va : value) (o : out),
        not (@eq type (type_of a1) type_object) ->
        red_expr S C (spec_error native_error_type) oo ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq value vo a1 ->
        @eq value vx a2 ->
        @eq value va a3 -> @eq out o oo -> P S C a1 a2 a3 oo) ->
       (red_expr S C (spec_call_object_define_prop_1 a1 a2 a3) oo ->
        forall (S0 : state) (C0 : execution_ctx) (l : object_loc)
          (vx va : value) (o1 o : out),
        red_expr S C (spec_to_string a2) o1 ->
        red_expr S C (spec_call_object_define_prop_2 l o1 a3) oo ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq value (value_object l) a1 ->
        @eq value vx a2 ->
        @eq value va a3 -> @eq out o oo -> P S C (value_object l) a2 a3 oo) ->
       red_expr S C (spec_call_object_define_prop_1 a1 a2 a3) oo ->
       P S C a1 a2 a3 oo.

Parameter inv_red_expr_spec_call_object_define_prop_2
     : forall (S : state) (C : execution_ctx) (a1 : object_loc) 
         (a2 : out) (a3 : value) (oo : out)
         (P : state ->
              execution_ctx -> object_loc -> out -> value -> out -> Prop),
       (red_expr S C (spec_call_object_define_prop_2 a1 a2 a3) oo ->
        forall (S0 : state) (C0 : execution_ctx) (exte : ext_expr) (o : out),
        @eq (option out)
          (out_of_ext_expr (spec_call_object_define_prop_2 a1 a2 a3))
          (@Some out oo) ->
        abort oo ->
        not
          (abort_intercepted_expr (spec_call_object_define_prop_2 a1 a2 a3)) ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq ext_expr exte (spec_call_object_define_prop_2 a1 a2 a3) ->
        @eq out o oo -> P S C a1 a2 a3 oo) ->
       (red_expr S C (spec_call_object_define_prop_2 a1 a2 a3) oo ->
        forall (S0 S1 : state) (C0 : execution_ctx) 
          (l : object_loc) (x : prop_name) (va : value) 
          (o : out) (y : specret descriptor),
        @red_spec descriptor S0 C (spec_to_descriptor a3) y ->
        red_expr S0 C (spec_call_object_define_prop_3 a1 x y) oo ->
        @eq state S1 S ->
        @eq execution_ctx C0 C ->
        @eq object_loc l a1 ->
        @eq out (out_ter S0 (res_val (value_prim (prim_string x)))) a2 ->
        @eq value va a3 ->
        @eq out o oo ->
        P S C a1 (out_ter S0 (res_val (value_prim (prim_string x)))) a3 oo) ->
       red_expr S C (spec_call_object_define_prop_2 a1 a2 a3) oo ->
       P S C a1 a2 a3 oo.

Parameter inv_red_expr_spec_call_object_define_prop_3
     : forall (S : state) (C : execution_ctx) (a1 : object_loc) 
         (a2 : string) (a3 : specret descriptor) (oo : out)
         (P : state ->
              execution_ctx ->
              object_loc -> string -> specret descriptor -> out -> Prop),
       (red_expr S C (spec_call_object_define_prop_3 a1 a2 a3) oo ->
        forall (S0 : state) (C0 : execution_ctx) (exte : ext_expr) (o : out),
        @eq (option out)
          (out_of_ext_expr (spec_call_object_define_prop_3 a1 a2 a3))
          (@Some out oo) ->
        abort oo ->
        not
          (abort_intercepted_expr (spec_call_object_define_prop_3 a1 a2 a3)) ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq ext_expr exte (spec_call_object_define_prop_3 a1 a2 a3) ->
        @eq out o oo -> P S C a1 a2 a3 oo) ->
       (red_expr S C (spec_call_object_define_prop_3 a1 a2 a3) oo ->
        forall (S0 S1 : state) (C0 : execution_ctx) 
          (l : object_loc) (s : string) (Desc : descriptor) 
          (o1 o : out),
        red_expr S0 C (spec_object_define_own_prop a1 a2 Desc throw_true) o1 ->
        red_expr S0 C (spec_call_object_define_prop_4 a1 o1) oo ->
        @eq state S1 S ->
        @eq execution_ctx C0 C ->
        @eq object_loc l a1 ->
        @eq string s a2 ->
        @eq (specret descriptor) (@ret descriptor S0 Desc) a3 ->
        @eq out o oo -> P S C a1 a2 (@ret descriptor S0 Desc) oo) ->
       red_expr S C (spec_call_object_define_prop_3 a1 a2 a3) oo ->
       P S C a1 a2 a3 oo.

Parameter inv_red_expr_spec_call_object_define_prop_4
     : forall (S : state) (C : execution_ctx) (a1 : object_loc) 
         (a2 oo : out)
         (P : state -> execution_ctx -> object_loc -> out -> out -> Prop),
       (red_expr S C (spec_call_object_define_prop_4 a1 a2) oo ->
        forall (S0 : state) (C0 : execution_ctx) (exte : ext_expr) (o : out),
        @eq (option out)
          (out_of_ext_expr (spec_call_object_define_prop_4 a1 a2))
          (@Some out oo) ->
        abort oo ->
        not (abort_intercepted_expr (spec_call_object_define_prop_4 a1 a2)) ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq ext_expr exte (spec_call_object_define_prop_4 a1 a2) ->
        @eq out o oo -> P S C a1 a2 oo) ->
       (red_expr S C (spec_call_object_define_prop_4 a1 a2) oo ->
        forall (S0 S1 : state) (C0 : execution_ctx) 
          (l : object_loc) (b : bool),
        @eq state S1 S ->
        @eq execution_ctx C0 C ->
        @eq object_loc l a1 ->
        @eq out (out_ter S0 (res_val (value_prim (prim_bool b)))) a2 ->
        @eq out (out_ter S0 (res_val (value_object a1))) oo ->
        P S C a1 (out_ter S0 (res_val (value_prim (prim_bool b))))
          (out_ter S0 (res_val (value_object a1)))) ->
       red_expr S C (spec_call_object_define_prop_4 a1 a2) oo ->
       P S C a1 a2 oo.

Parameter inv_red_expr_spec_call_object_get_own_prop_descriptor_1
     : forall (S : state) (C : execution_ctx) (a1 a2 : value) 
         (oo : out)
         (P : state -> execution_ctx -> value -> value -> out -> Prop),
       (red_expr S C (spec_call_object_get_own_prop_descriptor_1 a1 a2) oo ->
        forall (S0 : state) (C0 : execution_ctx) (exte : ext_expr) (o : out),
        @eq (option out)
          (out_of_ext_expr (spec_call_object_get_own_prop_descriptor_1 a1 a2))
          (@Some out oo) ->
        abort oo ->
        not
          (abort_intercepted_expr
             (spec_call_object_get_own_prop_descriptor_1 a1 a2)) ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq ext_expr exte (spec_call_object_get_own_prop_descriptor_1 a1 a2) ->
        @eq out o oo -> P S C a1 a2 oo) ->
       (red_expr S C (spec_call_object_get_own_prop_descriptor_1 a1 a2) oo ->
        forall (S0 : state) (C0 : execution_ctx) (vo vx : value) (o : out),
        not (@eq type (type_of a1) type_object) ->
        red_expr S C (spec_error native_error_type) oo ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq value vo a1 -> @eq value vx a2 -> @eq out o oo -> P S C a1 a2 oo) ->
       (red_expr S C (spec_call_object_get_own_prop_descriptor_1 a1 a2) oo ->
        forall (S0 : state) (C0 : execution_ctx) (l : object_loc)
          (vx : value) (o o1 : out),
        red_expr S C (spec_to_string a2) o1 ->
        red_expr S C (spec_call_object_get_own_prop_descriptor_2 l o1) oo ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq value (value_object l) a1 ->
        @eq value vx a2 -> @eq out o oo -> P S C (value_object l) a2 oo) ->
       red_expr S C (spec_call_object_get_own_prop_descriptor_1 a1 a2) oo ->
       P S C a1 a2 oo.

Parameter inv_red_expr_spec_call_object_get_own_prop_descriptor_2
     : forall (S : state) (C : execution_ctx) (a1 : object_loc) 
         (a2 oo : out)
         (P : state -> execution_ctx -> object_loc -> out -> out -> Prop),
       (red_expr S C (spec_call_object_get_own_prop_descriptor_2 a1 a2) oo ->
        forall (S0 : state) (C0 : execution_ctx) (exte : ext_expr) (o : out),
        @eq (option out)
          (out_of_ext_expr (spec_call_object_get_own_prop_descriptor_2 a1 a2))
          (@Some out oo) ->
        abort oo ->
        not
          (abort_intercepted_expr
             (spec_call_object_get_own_prop_descriptor_2 a1 a2)) ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq ext_expr exte (spec_call_object_get_own_prop_descriptor_2 a1 a2) ->
        @eq out o oo -> P S C a1 a2 oo) ->
       (red_expr S C (spec_call_object_get_own_prop_descriptor_2 a1 a2) oo ->
        forall (S0 S1 : state) (C0 : execution_ctx) 
          (l : object_loc) (x : prop_name) (o : out)
          (y : specret full_descriptor),
        @red_spec full_descriptor S1 C (spec_object_get_own_prop a1 x) y ->
        red_expr S1 C (spec_from_descriptor y) oo ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq object_loc l a1 ->
        @eq out (out_ter S1 (res_val (value_prim (prim_string x)))) a2 ->
        @eq out o oo ->
        P S C a1 (out_ter S1 (res_val (value_prim (prim_string x)))) oo) ->
       red_expr S C (spec_call_object_get_own_prop_descriptor_2 a1 a2) oo ->
       P S C a1 a2 oo.

Parameter inv_red_expr_spec_call_object_proto_to_string_1
     : forall (S : state) (C : execution_ctx) (a1 : value) 
         (oo : out) (P : state -> execution_ctx -> value -> out -> Prop),
       (red_expr S C (spec_call_object_proto_to_string_1 a1) oo ->
        forall (S0 : state) (C0 : execution_ctx) (exte : ext_expr) (o : out),
        @eq (option out)
          (out_of_ext_expr (spec_call_object_proto_to_string_1 a1))
          (@Some out oo) ->
        abort oo ->
        not (abort_intercepted_expr (spec_call_object_proto_to_string_1 a1)) ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq ext_expr exte (spec_call_object_proto_to_string_1 a1) ->
        @eq out o oo -> P S C a1 oo) ->
       (red_expr S C (spec_call_object_proto_to_string_1 a1) oo ->
        forall (S0 : state) (C0 : execution_ctx),
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq value (value_prim prim_undef) a1 ->
        @eq out
          (out_ter S
             (res_val
                (value_prim
                   (prim_string "[object Undefined]"%string))))
          oo ->
        P S C (value_prim prim_undef)
          (out_ter S
             (res_val
                (value_prim
                   (prim_string "[object Undefined]"%string))))) ->
       (red_expr S C (spec_call_object_proto_to_string_1 a1) oo ->
        forall (S0 : state) (C0 : execution_ctx),
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq value (value_prim prim_null) a1 ->
        @eq out
          (out_ter S
             (res_val
                (value_prim
                   (prim_string "[object Null]"%string))))
          oo ->
        P S C (value_prim prim_null)
          (out_ter S
             (res_val
                (value_prim
                   (prim_string "[object Null]"%string))))) ->
       (red_expr S C (spec_call_object_proto_to_string_1 a1) oo ->
        forall (S0 : state) (C0 : execution_ctx) (v : value) (o o1 : out),
        not
          (Logic.or (@eq value a1 (value_prim prim_null))
             (@eq value a1 (value_prim prim_undef))) ->
        red_expr S C (spec_to_object a1) o1 ->
        red_expr S C (spec_call_object_proto_to_string_2 o1) oo ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq value v a1 -> @eq out o oo -> P S C a1 oo) ->
       red_expr S C (spec_call_object_proto_to_string_1 a1) oo -> P S C a1 oo.
 
Parameter inv_red_expr_spec_call_object_proto_to_string_2
     : forall (S : state) (C : execution_ctx) (a1 oo : out)
         (P : state -> execution_ctx -> out -> out -> Prop),
       (red_expr S C (spec_call_object_proto_to_string_2 a1) oo ->
        forall (S0 : state) (C0 : execution_ctx) (exte : ext_expr) (o : out),
        @eq (option out)
          (out_of_ext_expr (spec_call_object_proto_to_string_2 a1))
          (@Some out oo) ->
        abort oo ->
        not (abort_intercepted_expr (spec_call_object_proto_to_string_2 a1)) ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq ext_expr exte (spec_call_object_proto_to_string_2 a1) ->
        @eq out o oo -> P S C a1 oo) ->
       (red_expr S C (spec_call_object_proto_to_string_2 a1) oo ->
        forall (S0 S1 : state) (C0 : execution_ctx) 
          (l : object_loc) (s sclass : string),
        object_class S1 l sclass ->
        @eq string s
          (String.append
             (String (Ascii true true false true true false true false)
                (String (Ascii true true true true false true true false)
                   (String
                      (Ascii false true false false false true true false)
                      (String
                         (Ascii false true false true false true true false)
                         (String
                            (Ascii true false true false false true true
                               false)
                            (String
                               (Ascii true true false false false true true
                                  false)
                               (String
                                  (Ascii false false true false true true
                                     true false)
                                  (String
                                     (Ascii false false false false false
                                        true false false) EmptyString))))))))
             (String.append sclass
                (String (Ascii true false true true true false true false)
                   EmptyString))) ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq out (out_ter S1 (res_val (value_object l))) a1 ->
        @eq out (out_ter S1 (res_val (value_prim (prim_string s)))) oo ->
        P S C (out_ter S1 (res_val (value_object l)))
          (out_ter S1 (res_val (value_prim (prim_string s))))) ->
       red_expr S C (spec_call_object_proto_to_string_2 a1) oo -> P S C a1 oo.

Parameter inv_red_expr_spec_call_object_proto_has_own_prop_1
     : forall (S : state) (C : execution_ctx) (a1 : out) 
         (a2 : value) (oo : out)
         (P : state -> execution_ctx -> out -> value -> out -> Prop),
       (red_expr S C (spec_call_object_proto_has_own_prop_1 a1 a2) oo ->
        forall (S0 : state) (C0 : execution_ctx) (exte : ext_expr) (o : out),
        @eq (option out)
          (out_of_ext_expr (spec_call_object_proto_has_own_prop_1 a1 a2))
          (@Some out oo) ->
        abort oo ->
        not
          (abort_intercepted_expr
             (spec_call_object_proto_has_own_prop_1 a1 a2)) ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq ext_expr exte (spec_call_object_proto_has_own_prop_1 a1 a2) ->
        @eq out o oo -> P S C a1 a2 oo) ->
       (red_expr S C (spec_call_object_proto_has_own_prop_1 a1 a2) oo ->
        forall (S0 S' : state) (C0 : execution_ctx) 
          (vthis : value) (s : string) (o o1 : out),
        red_expr S' C (spec_to_object a2) o1 ->
        red_expr S' C (spec_call_object_proto_has_own_prop_2 o1 s) oo ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq out (out_ter S' (res_val (value_prim (prim_string s)))) a1 ->
        @eq value vthis a2 ->
        @eq out o oo ->
        P S C (out_ter S' (res_val (value_prim (prim_string s)))) a2 oo) ->
       red_expr S C (spec_call_object_proto_has_own_prop_1 a1 a2) oo ->
       P S C a1 a2 oo.

Parameter inv_red_expr_spec_call_object_proto_has_own_prop_2
     : forall (S : state) (C : execution_ctx) (a1 : out) 
         (a2 : prop_name) (oo : out)
         (P : state -> execution_ctx -> out -> string -> out -> Prop),
       (red_expr S C (spec_call_object_proto_has_own_prop_2 a1 a2) oo ->
        forall (S0 : state) (C0 : execution_ctx) (exte : ext_expr) (o : out),
        @eq (option out)
          (out_of_ext_expr (spec_call_object_proto_has_own_prop_2 a1 a2))
          (@Some out oo) ->
        abort oo ->
        not
          (abort_intercepted_expr
             (spec_call_object_proto_has_own_prop_2 a1 a2)) ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq ext_expr exte (spec_call_object_proto_has_own_prop_2 a1 a2) ->
        @eq out o oo -> P S C a1 a2 oo) ->
       (red_expr S C (spec_call_object_proto_has_own_prop_2 a1 a2) oo ->
        forall (S0 S' : state) (C0 : execution_ctx) 
          (l : object_loc) (s : string) (o : out)
          (y : specret full_descriptor),
        @red_spec full_descriptor S' C (spec_object_get_own_prop l a2) y ->
        red_expr S' C (spec_call_object_proto_has_own_prop_3 y) oo ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq out (out_ter S' (res_val (value_object l))) a1 ->
        @eq prop_name s a2 ->
        @eq out o oo -> P S C (out_ter S' (res_val (value_object l))) a2 oo) ->
       red_expr S C (spec_call_object_proto_has_own_prop_2 a1 a2) oo ->
       P S C a1 a2 oo.

Parameter inv_red_expr_spec_call_object_proto_has_own_prop_3
     : forall (S : state) (C : execution_ctx) (a1 : specret full_descriptor)
         (oo : out)
         (P : state ->
              execution_ctx -> specret full_descriptor -> out -> Prop),
       (red_expr S C (spec_call_object_proto_has_own_prop_3 a1) oo ->
        forall (S0 : state) (C0 : execution_ctx) (exte : ext_expr) (o : out),
        @eq (option out)
          (out_of_ext_expr (spec_call_object_proto_has_own_prop_3 a1))
          (@Some out oo) ->
        abort oo ->
        not
          (abort_intercepted_expr (spec_call_object_proto_has_own_prop_3 a1)) ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq ext_expr exte (spec_call_object_proto_has_own_prop_3 a1) ->
        @eq out o oo -> P S C a1 oo) ->
       (red_expr S C (spec_call_object_proto_has_own_prop_3 a1) oo ->
        forall (S0 S' : state) (C0 : execution_ctx),
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq (specret full_descriptor)
          (@ret full_descriptor S' full_descriptor_undef) a1 ->
        @eq out (out_ter S' (res_val (value_prim (prim_bool false)))) oo ->
        P S C (@ret full_descriptor S' full_descriptor_undef)
          (out_ter S' (res_val (value_prim (prim_bool false))))) ->
       (red_expr S C (spec_call_object_proto_has_own_prop_3 a1) oo ->
        forall (S0 S' : state) (C0 : execution_ctx) (A : attributes),
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq (specret full_descriptor) (dret S' (full_descriptor_some A)) a1 ->
        @eq out (out_ter S' (res_val (value_prim (prim_bool true)))) oo ->
        P S C (dret S' (full_descriptor_some A))
          (out_ter S' (res_val (value_prim (prim_bool true))))) ->
       red_expr S C (spec_call_object_proto_has_own_prop_3 a1) oo ->
       P S C a1 oo.

Parameter inv_red_expr_spec_call_object_proto_is_prototype_of_2_1
     : forall (S : state) (C : execution_ctx) (a1 a2 : value) 
         (oo : out)
         (P : state -> execution_ctx -> value -> value -> out -> Prop),
       (red_expr S C (spec_call_object_proto_is_prototype_of_2_1 a1 a2) oo ->
        forall (S0 : state) (C0 : execution_ctx) (exte : ext_expr) (o : out),
        @eq (option out)
          (out_of_ext_expr (spec_call_object_proto_is_prototype_of_2_1 a1 a2))
          (@Some out oo) ->
        abort oo ->
        not
          (abort_intercepted_expr
             (spec_call_object_proto_is_prototype_of_2_1 a1 a2)) ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq ext_expr exte (spec_call_object_proto_is_prototype_of_2_1 a1 a2) ->
        @eq out o oo -> P S C a1 a2 oo) ->
       (red_expr S C (spec_call_object_proto_is_prototype_of_2_1 a1 a2) oo ->
        forall (S0 : state) (C0 : execution_ctx) (v vthis : value),
        not (@eq type (type_of a1) type_object) ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq value v a1 ->
        @eq value vthis a2 ->
        @eq out (out_ter S (res_val (value_prim (prim_bool false)))) oo ->
        P S C a1 a2 (out_ter S (res_val (value_prim (prim_bool false))))) ->
       (red_expr S C (spec_call_object_proto_is_prototype_of_2_1 a1 a2) oo ->
        forall (S0 : state) (C0 : execution_ctx) (l : object_loc)
          (vthis : value) (o1 o : out),
        red_expr S C (spec_to_object a2) o1 ->
        red_expr S C (spec_call_object_proto_is_prototype_of_2_2 o1 l) oo ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq value (value_object l) a1 ->
        @eq value vthis a2 -> @eq out o oo -> P S C (value_object l) a2 oo) ->
       red_expr S C (spec_call_object_proto_is_prototype_of_2_1 a1 a2) oo ->
       P S C a1 a2 oo.

Parameter inv_red_expr_spec_call_object_proto_is_prototype_of_2_2
     : forall (S : state) (C : execution_ctx) (a1 : out) 
         (a2 : object_loc) (oo : out)
         (P : state -> execution_ctx -> out -> object_loc -> out -> Prop),
       (red_expr S C (spec_call_object_proto_is_prototype_of_2_2 a1 a2) oo ->
        forall (S0 : state) (C0 : execution_ctx) (exte : ext_expr) (o : out),
        @eq (option out)
          (out_of_ext_expr (spec_call_object_proto_is_prototype_of_2_2 a1 a2))
          (@Some out oo) ->
        abort oo ->
        not
          (abort_intercepted_expr
             (spec_call_object_proto_is_prototype_of_2_2 a1 a2)) ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq ext_expr exte (spec_call_object_proto_is_prototype_of_2_2 a1 a2) ->
        @eq out o oo -> P S C a1 a2 oo) ->
       (red_expr S C (spec_call_object_proto_is_prototype_of_2_2 a1 a2) oo ->
        forall (S0 S1 : state) (C0 : execution_ctx) 
          (l lthis : object_loc) (o : out),
        red_expr S1 C (spec_call_object_proto_is_prototype_of_2_3 lthis a2)
          oo ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq out (out_ter S1 (res_val (value_object lthis))) a1 ->
        @eq object_loc l a2 ->
        @eq out o oo ->
        P S C (out_ter S1 (res_val (value_object lthis))) a2 oo) ->
       red_expr S C (spec_call_object_proto_is_prototype_of_2_2 a1 a2) oo ->
       P S C a1 a2 oo.

Parameter inv_red_expr_spec_call_object_proto_is_prototype_of_2_3
     : forall (S : state) (C : execution_ctx) (a1 a2 : object_loc) 
         (oo : out)
         (P : state ->
              execution_ctx -> object_loc -> object_loc -> out -> Prop),
       (red_expr S C (spec_call_object_proto_is_prototype_of_2_3 a1 a2) oo ->
        forall (S0 : state) (C0 : execution_ctx) (exte : ext_expr) (o : out),
        @eq (option out)
          (out_of_ext_expr (spec_call_object_proto_is_prototype_of_2_3 a1 a2))
          (@Some out oo) ->
        abort oo ->
        not
          (abort_intercepted_expr
             (spec_call_object_proto_is_prototype_of_2_3 a1 a2)) ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq ext_expr exte (spec_call_object_proto_is_prototype_of_2_3 a1 a2) ->
        @eq out o oo -> P S C a1 a2 oo) ->
       (red_expr S C (spec_call_object_proto_is_prototype_of_2_3 a1 a2) oo ->
        forall (S0 : state) (C0 : execution_ctx) (l lthis : object_loc)
          (vproto : value) (o : out),
        object_proto S a2 vproto ->
        red_expr S C (spec_call_object_proto_is_prototype_of_2_4 a1 vproto)
          oo ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq object_loc lthis a1 ->
        @eq object_loc l a2 -> @eq out o oo -> P S C a1 a2 oo) ->
       red_expr S C (spec_call_object_proto_is_prototype_of_2_3 a1 a2) oo ->
       P S C a1 a2 oo.

Parameter inv_red_expr_spec_call_object_proto_is_prototype_of_2_4
     : forall (S : state) (C : execution_ctx) (a1 : object_loc) 
         (a2 : value) (oo : out)
         (P : state -> execution_ctx -> object_loc -> value -> out -> Prop),
       (red_expr S C (spec_call_object_proto_is_prototype_of_2_4 a1 a2) oo ->
        forall (S0 : state) (C0 : execution_ctx) (exte : ext_expr) (o : out),
        @eq (option out)
          (out_of_ext_expr (spec_call_object_proto_is_prototype_of_2_4 a1 a2))
          (@Some out oo) ->
        abort oo ->
        not
          (abort_intercepted_expr
             (spec_call_object_proto_is_prototype_of_2_4 a1 a2)) ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq ext_expr exte (spec_call_object_proto_is_prototype_of_2_4 a1 a2) ->
        @eq out o oo -> P S C a1 a2 oo) ->
       (red_expr S C (spec_call_object_proto_is_prototype_of_2_4 a1 a2) oo ->
        forall (S0 : state) (C0 : execution_ctx) (lthis : object_loc),
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq object_loc lthis a1 ->
        @eq value (value_prim prim_null) a2 ->
        @eq out (out_ter S (res_val (value_prim (prim_bool false)))) oo ->
        P S C a1 (value_prim prim_null)
          (out_ter S (res_val (value_prim (prim_bool false))))) ->
       (red_expr S C (spec_call_object_proto_is_prototype_of_2_4 a1 a2) oo ->
        forall (S0 : state) (C0 : execution_ctx) (lthis : object_loc),
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq object_loc lthis a1 ->
        @eq value (value_object a1) a2 ->
        @eq out (out_ter S (res_val (value_prim (prim_bool true)))) oo ->
        P S C a1 (value_object a1)
          (out_ter S (res_val (value_prim (prim_bool true))))) ->
       (red_expr S C (spec_call_object_proto_is_prototype_of_2_4 a1 a2) oo ->
        forall (S0 : state) (C0 : execution_ctx) (lthis lproto : object_loc)
          (o : out),
        not (@eq object_loc lproto a1) ->
        red_expr S C (spec_call_object_proto_is_prototype_of_2_3 a1 lproto)
          oo ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq object_loc lthis a1 ->
        @eq value (value_object lproto) a2 ->
        @eq out o oo -> P S C a1 (value_object lproto) oo) ->
       red_expr S C (spec_call_object_proto_is_prototype_of_2_4 a1 a2) oo ->
       P S C a1 a2 oo.

Parameter inv_red_expr_spec_call_object_proto_prop_is_enumerable_1
     : forall (S : state) (C : execution_ctx) (a1 a2 : value) 
         (oo : out)
         (P : state -> execution_ctx -> value -> value -> out -> Prop),
       (red_expr S C (spec_call_object_proto_prop_is_enumerable_1 a1 a2) oo ->
        forall (S0 : state) (C0 : execution_ctx) (exte : ext_expr) (o : out),
        @eq (option out)
          (out_of_ext_expr
             (spec_call_object_proto_prop_is_enumerable_1 a1 a2))
          (@Some out oo) ->
        abort oo ->
        not
          (abort_intercepted_expr
             (spec_call_object_proto_prop_is_enumerable_1 a1 a2)) ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq ext_expr exte (spec_call_object_proto_prop_is_enumerable_1 a1 a2) ->
        @eq out o oo -> P S C a1 a2 oo) ->
       (red_expr S C (spec_call_object_proto_prop_is_enumerable_1 a1 a2) oo ->
        forall (S0 : state) (C0 : execution_ctx) (v vthis : value)
          (o o1 : out),
        red_expr S C (spec_to_string a1) o1 ->
        red_expr S C (spec_call_object_proto_prop_is_enumerable_2 a2 o1) oo ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq value v a1 ->
        @eq value vthis a2 -> @eq out o oo -> P S C a1 a2 oo) ->
       red_expr S C (spec_call_object_proto_prop_is_enumerable_1 a1 a2) oo ->
       P S C a1 a2 oo.

Parameter inv_red_expr_spec_call_object_proto_prop_is_enumerable_2
     : forall (S : state) (C : execution_ctx) (a1 : value) 
         (a2 oo : out)
         (P : state -> execution_ctx -> value -> out -> out -> Prop),
       (red_expr S C (spec_call_object_proto_prop_is_enumerable_2 a1 a2) oo ->
        forall (S0 : state) (C0 : execution_ctx) (exte : ext_expr) (o : out),
        @eq (option out)
          (out_of_ext_expr
             (spec_call_object_proto_prop_is_enumerable_2 a1 a2))
          (@Some out oo) ->
        abort oo ->
        not
          (abort_intercepted_expr
             (spec_call_object_proto_prop_is_enumerable_2 a1 a2)) ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq ext_expr exte (spec_call_object_proto_prop_is_enumerable_2 a1 a2) ->
        @eq out o oo -> P S C a1 a2 oo) ->
       (red_expr S C (spec_call_object_proto_prop_is_enumerable_2 a1 a2) oo ->
        forall (S0 S' : state) (C0 : execution_ctx) 
          (vthis : value) (s : string) (o o1 : out),
        red_expr S' C (spec_to_object a1) o1 ->
        red_expr S' C (spec_call_object_proto_prop_is_enumerable_3 o1 s) oo ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq value vthis a1 ->
        @eq out (out_ter S' (res_val (value_prim (prim_string s)))) a2 ->
        @eq out o oo ->
        P S C a1 (out_ter S' (res_val (value_prim (prim_string s)))) oo) ->
       red_expr S C (spec_call_object_proto_prop_is_enumerable_2 a1 a2) oo ->
       P S C a1 a2 oo.

Parameter inv_red_expr_spec_call_object_proto_prop_is_enumerable_3
     : forall (S : state) (C : execution_ctx) (a1 : out) 
         (a2 : string) (oo : out)
         (P : state -> execution_ctx -> out -> string -> out -> Prop),
       (red_expr S C (spec_call_object_proto_prop_is_enumerable_3 a1 a2) oo ->
        forall (S0 : state) (C0 : execution_ctx) (exte : ext_expr) (o : out),
        @eq (option out)
          (out_of_ext_expr
             (spec_call_object_proto_prop_is_enumerable_3 a1 a2))
          (@Some out oo) ->
        abort oo ->
        not
          (abort_intercepted_expr
             (spec_call_object_proto_prop_is_enumerable_3 a1 a2)) ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq ext_expr exte (spec_call_object_proto_prop_is_enumerable_3 a1 a2) ->
        @eq out o oo -> P S C a1 a2 oo) ->
       (red_expr S C (spec_call_object_proto_prop_is_enumerable_3 a1 a2) oo ->
        forall (S0 S' : state) (C0 : execution_ctx) 
          (l : object_loc) (x : prop_name) (o : out)
          (y : specret full_descriptor),
        @red_spec full_descriptor S' C (spec_object_get_own_prop l a2) y ->
        red_expr S' C (spec_call_object_proto_prop_is_enumerable_4 y) oo ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq out (out_ter S' (res_val (value_object l))) a1 ->
        @eq string x a2 ->
        @eq out o oo -> P S C (out_ter S' (res_val (value_object l))) a2 oo) ->
       red_expr S C (spec_call_object_proto_prop_is_enumerable_3 a1 a2) oo ->
       P S C a1 a2 oo.

Parameter inv_red_expr_spec_call_object_proto_prop_is_enumerable_4
     : forall (S : state) (C : execution_ctx) (a1 : specret full_descriptor)
         (oo : out)
         (P : state ->
              execution_ctx -> specret full_descriptor -> out -> Prop),
       (red_expr S C (spec_call_object_proto_prop_is_enumerable_4 a1) oo ->
        forall (S0 : state) (C0 : execution_ctx) (exte : ext_expr) (o : out),
        @eq (option out)
          (out_of_ext_expr (spec_call_object_proto_prop_is_enumerable_4 a1))
          (@Some out oo) ->
        abort oo ->
        not
          (abort_intercepted_expr
             (spec_call_object_proto_prop_is_enumerable_4 a1)) ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq ext_expr exte (spec_call_object_proto_prop_is_enumerable_4 a1) ->
        @eq out o oo -> P S C a1 oo) ->
       (red_expr S C (spec_call_object_proto_prop_is_enumerable_4 a1) oo ->
        forall (S0 S1 : state) (C0 : execution_ctx),
        @eq state S1 S ->
        @eq execution_ctx C0 C ->
        @eq (specret full_descriptor) (dret S0 full_descriptor_undef) a1 ->
        @eq out (out_ter S0 (res_val (value_prim (prim_bool false)))) oo ->
        P S C (dret S0 full_descriptor_undef)
          (out_ter S0 (res_val (value_prim (prim_bool false))))) ->
       (red_expr S C (spec_call_object_proto_prop_is_enumerable_4 a1) oo ->
        forall (S0 S1 : state) (C0 : execution_ctx) 
          (A : attributes) (b : bool),
        @eq bool b (attributes_enumerable A) ->
        @eq state S1 S ->
        @eq execution_ctx C0 C ->
        @eq (specret full_descriptor) (dret S0 (full_descriptor_some A)) a1 ->
        @eq out (out_ter S0 (res_val (value_prim (prim_bool b)))) oo ->
        P S C (dret S0 (full_descriptor_some A))
          (out_ter S0 (res_val (value_prim (prim_bool b))))) ->
       red_expr S C (spec_call_object_proto_prop_is_enumerable_4 a1) oo ->
       P S C a1 oo.

Parameter inv_red_expr_spec_call_array_new_1
     : forall (S : state) (C : execution_ctx) (a1 : list value) 
         (oo : out) (P : state -> execution_ctx -> list value -> out -> Prop),
       (red_expr S C (spec_call_array_new_1 a1) oo ->
        forall (S0 : state) (C0 : execution_ctx) (exte : ext_expr) (o : out),
        @eq (option out) (out_of_ext_expr (spec_call_array_new_1 a1))
          (@Some out oo) ->
        abort oo ->
        not (abort_intercepted_expr (spec_call_array_new_1 a1)) ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq ext_expr exte (spec_call_array_new_1 a1) ->
        @eq out o oo -> P S C a1 oo) ->
       (red_expr S C (spec_call_array_new_1 a1) oo ->
        forall (S0 S' : state) (C0 : execution_ctx) 
          (args : list value) (O O' : object) (l : object_loc) 
          (o : out),
        @eq object O'
          (object_new
             (value_object (object_loc_prealloc prealloc_array_proto))
             (String (Ascii true false false false false false true false)
                (String (Ascii false true false false true true true false)
                   (String
                      (Ascii false true false false true true true false)
                      (String
                         (Ascii true false false false false true true false)
                         (String
                            (Ascii true false false true true true true false)
                            EmptyString)))))) ->
        @eq object O (object_for_array O' builtin_define_own_prop_array) ->
        @eq (prod object_loc state) (@pair object_loc state l S')
          (object_alloc S O) ->
        red_expr S' C (spec_call_array_new_2 l a1) oo ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq (list value) args a1 -> @eq out o oo -> P S C a1 oo) ->
       red_expr S C (spec_call_array_new_1 a1) oo -> P S C a1 oo.

Parameter inv_red_expr_spec_call_array_new_2
     : forall (S : state) (C : execution_ctx) (a1 : object_loc)
         (a2 : list value) (oo : out)
         (P : state ->
              execution_ctx -> object_loc -> list value -> out -> Prop),
       (red_expr S C (spec_call_array_new_2 a1 a2) oo ->
        forall (S0 : state) (C0 : execution_ctx) (exte : ext_expr) (o : out),
        @eq (option out) (out_of_ext_expr (spec_call_array_new_2 a1 a2))
          (@Some out oo) ->
        abort oo ->
        not (abort_intercepted_expr (spec_call_array_new_2 a1 a2)) ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq ext_expr exte (spec_call_array_new_2 a1 a2) ->
        @eq out o oo -> P S C a1 a2 oo) ->
       (red_expr S C (spec_call_array_new_2 a1 a2) oo ->
        forall (S0 S' : state) (C0 : execution_ctx) 
          (l : object_loc) (args : list value) (o : out),
        object_set_property S a1
          (String (Ascii false false true true false true true false)
             (String (Ascii true false true false false true true false)
                (String (Ascii false true true true false true true false)
                   (String (Ascii true true true false false true true false)
                      (String
                         (Ascii false false true false true true true false)
                         (String
                            (Ascii false false false true false true true
                               false) EmptyString))))))
          (attributes_data_of
             (attributes_data_intro
                (value_prim
                   (prim_number
                      (JsNumber.of_int (my_Z_of_nat (@length value a2)))))
                true false false)) S' ->
        red_expr S' C (spec_call_array_new_3 a1 a2 Z0) oo ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq object_loc l a1 ->
        @eq (list value) args a2 -> @eq out o oo -> P S C a1 a2 oo) ->
       red_expr S C (spec_call_array_new_2 a1 a2) oo -> P S C a1 a2 oo.

Parameter inv_red_expr_spec_call_array_new_3
     : forall (S : state) (C : execution_ctx) (a1 : object_loc)
         (a2 : list value) (a3 : Z) (oo : out)
         (P : state ->
              execution_ctx -> object_loc -> list value -> Z -> out -> Prop),
       (red_expr S C (spec_call_array_new_3 a1 a2 a3) oo ->
        forall (S0 : state) (C0 : execution_ctx) (exte : ext_expr) (o : out),
        @eq (option out) (out_of_ext_expr (spec_call_array_new_3 a1 a2 a3))
          (@Some out oo) ->
        abort oo ->
        not (abort_intercepted_expr (spec_call_array_new_3 a1 a2 a3)) ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq ext_expr exte (spec_call_array_new_3 a1 a2 a3) ->
        @eq out o oo -> P S C a1 a2 a3 oo) ->
       (red_expr S C (spec_call_array_new_3 a1 a2 a3) oo ->
        forall (S0 S' : state) (C0 : execution_ctx) 
          (l : object_loc) (v : value) (vs : list value) 
          (ilen : Z) (o : out),
        object_set_property S a1 (JsNumber.to_string (JsNumber.of_int a3))
          (attributes_data_of (attributes_data_intro v true true true)) S' ->
        red_expr S' C (spec_call_array_new_3 a1 vs (Z.add a3 (Zpos xH))) oo ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq object_loc l a1 ->
        @eq (list value) (@cons value v vs) a2 ->
        @eq Z ilen a3 -> @eq out o oo -> P S C a1 (@cons value v vs) a3 oo) ->
       (red_expr S C (spec_call_array_new_3 a1 a2 a3) oo ->
        forall (S0 : state) (C0 : execution_ctx) (l : object_loc) (ilen : Z),
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq object_loc l a1 ->
        @eq (list value) (@nil value) a2 ->
        @eq Z ilen a3 ->
        @eq out (out_ter S (res_val (value_object a1))) oo ->
        P S C a1 (@nil value) a3 (out_ter S (res_val (value_object a1)))) ->
       red_expr S C (spec_call_array_new_3 a1 a2 a3) oo -> P S C a1 a2 a3 oo.

Parameter inv_red_expr_spec_call_array_new_single_1
     : forall (S : state) (C : execution_ctx) (a1 : value) 
         (oo : out) (P : state -> execution_ctx -> value -> out -> Prop),
       (red_expr S C (spec_call_array_new_single_1 a1) oo ->
        forall (S0 : state) (C0 : execution_ctx) (exte : ext_expr) (o : out),
        @eq (option out) (out_of_ext_expr (spec_call_array_new_single_1 a1))
          (@Some out oo) ->
        abort oo ->
        not (abort_intercepted_expr (spec_call_array_new_single_1 a1)) ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq ext_expr exte (spec_call_array_new_single_1 a1) ->
        @eq out o oo -> P S C a1 oo) ->
       (red_expr S C (spec_call_array_new_single_1 a1) oo ->
        forall (S0 S' : state) (C0 : execution_ctx) 
          (v : value) (O O' : object) (l : object_loc) 
          (o : out),
        @eq object O'
          (object_new
             (value_object (object_loc_prealloc prealloc_array_proto))
             (String (Ascii true false false false false false true false)
                (String (Ascii false true false false true true true false)
                   (String
                      (Ascii false true false false true true true false)
                      (String
                         (Ascii true false false false false true true false)
                         (String
                            (Ascii true false false true true true true false)
                            EmptyString)))))) ->
        @eq object O (object_for_array O' builtin_define_own_prop_array) ->
        @eq (prod object_loc state) (@pair object_loc state l S')
          (object_alloc S O) ->
        red_expr S' C (spec_call_array_new_single_2 l a1) oo ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq value v a1 -> @eq out o oo -> P S C a1 oo) ->
       red_expr S C (spec_call_array_new_single_1 a1) oo -> P S C a1 oo.

Parameter inv_red_expr_spec_call_array_new_single_2
     : forall (S : state) (C : execution_ctx) (a1 : object_loc) 
         (a2 : value) (oo : out)
         (P : state -> execution_ctx -> object_loc -> value -> out -> Prop),
       (red_expr S C (spec_call_array_new_single_2 a1 a2) oo ->
        forall (S0 : state) (C0 : execution_ctx) (exte : ext_expr) (o : out),
        @eq (option out)
          (out_of_ext_expr (spec_call_array_new_single_2 a1 a2))
          (@Some out oo) ->
        abort oo ->
        not (abort_intercepted_expr (spec_call_array_new_single_2 a1 a2)) ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq ext_expr exte (spec_call_array_new_single_2 a1 a2) ->
        @eq out o oo -> P S C a1 a2 oo) ->
       (red_expr S C (spec_call_array_new_single_2 a1 a2) oo ->
        forall (S0 S' S'' : state) (C0 : execution_ctx) 
          (l : object_loc) (v : value) (n : JsNumber.number),
        not (@eq value a2 (value_prim (prim_number n))) ->
        object_set_property S a1
          (String (Ascii false false false false true true false false)
             EmptyString)
          (attributes_data_of (attributes_data_intro a2 true true true)) S' ->
        object_set_property S' a1
          (String (Ascii false false true true false true true false)
             (String (Ascii true false true false false true true false)
                (String (Ascii false true true true false true true false)
                   (String (Ascii true true true false false true true false)
                      (String
                         (Ascii false false true false true true true false)
                         (String
                            (Ascii false false false true false true true
                               false) EmptyString))))))
          (attributes_data_of
             (attributes_data_intro
                (value_prim (prim_number (JsNumber.of_int (Zpos xH)))) true
                false false)) S'' ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq object_loc l a1 ->
        @eq value v a2 ->
        @eq out (out_ter S'' (res_val (value_object a1))) oo ->
        P S C a1 a2 (out_ter S'' (res_val (value_object a1)))) ->
       (red_expr S C (spec_call_array_new_single_2 a1 a2) oo ->
        forall (S0 : state) (C0 : execution_ctx) (l : object_loc) 
          (v : value) (o : out) (n : JsNumber.number) 
          (y : specret Z),
        @eq value a2 (value_prim (prim_number n)) ->
        @red_spec Z S C (spec_to_uint32 (value_prim (prim_number n))) y ->
        red_expr S C (spec_call_array_new_single_3 a1 n y) oo ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq object_loc l a1 ->
        @eq value v a2 -> @eq out o oo -> P S C a1 a2 oo) ->
       red_expr S C (spec_call_array_new_single_2 a1 a2) oo -> P S C a1 a2 oo.

Parameter inv_red_expr_spec_call_array_new_single_3
     : forall (S : state) (C : execution_ctx) (a1 : object_loc)
         (a2 : JsNumber.number) (a3 : specret Z) (oo : out)
         (P : state ->
              execution_ctx ->
              object_loc ->
              Fappli_IEEE.binary_float (Zpos (xI (xO (xI (xO (xI xH))))))
                (Zpos (xO (xO (xO (xO (xO (xO (xO (xO (xO (xO xH))))))))))) ->
              specret Z -> out -> Prop),
       (red_expr S C (spec_call_array_new_single_3 a1 a2 a3) oo ->
        forall (S0 : state) (C0 : execution_ctx) (exte : ext_expr) (o : out),
        @eq (option out)
          (out_of_ext_expr (spec_call_array_new_single_3 a1 a2 a3))
          (@Some out oo) ->
        abort oo ->
        not (abort_intercepted_expr (spec_call_array_new_single_3 a1 a2 a3)) ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq ext_expr exte (spec_call_array_new_single_3 a1 a2 a3) ->
        @eq out o oo -> P S C a1 a2 a3 oo) ->
       (red_expr S C (spec_call_array_new_single_3 a1 a2 a3) oo ->
        forall (S0 S' : state) (C0 : execution_ctx) 
          (l : object_loc) (n : JsNumber.number) (ilen : Z) 
          (o : out),
        @eq JsNumber.number (JsNumber.of_int ilen) a2 ->
        red_expr S' C (spec_call_array_new_single_4 a1 ilen) oo ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq object_loc l a1 ->
        @eq JsNumber.number n a2 ->
        @eq (specret Z) (@ret Z S' ilen) a3 ->
        @eq out o oo -> P S C a1 a2 (@ret Z S' ilen) oo) ->
       (red_expr S C (spec_call_array_new_single_3 a1 a2 a3) oo ->
        forall (S0 S' : state) (C0 : execution_ctx) 
          (l : object_loc) (n : JsNumber.number) (ilen : Z) 
          (o : out),
        not (@eq JsNumber.number (JsNumber.of_int ilen) a2) ->
        red_expr S' C (spec_error native_error_range) oo ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq object_loc l a1 ->
        @eq JsNumber.number n a2 ->
        @eq (specret Z) (@ret Z S' ilen) a3 ->
        @eq out o oo -> P S C a1 a2 (@ret Z S' ilen) oo) ->
       red_expr S C (spec_call_array_new_single_3 a1 a2 a3) oo ->
       P S C a1 a2 a3 oo.

Parameter inv_red_expr_spec_call_array_new_single_4
     : forall (S : state) (C : execution_ctx) (a1 : object_loc) 
         (a2 : Z) (oo : out)
         (P : state -> execution_ctx -> object_loc -> Z -> out -> Prop),
       (red_expr S C (spec_call_array_new_single_4 a1 a2) oo ->
        forall (S0 : state) (C0 : execution_ctx) (exte : ext_expr) (o : out),
        @eq (option out)
          (out_of_ext_expr (spec_call_array_new_single_4 a1 a2))
          (@Some out oo) ->
        abort oo ->
        not (abort_intercepted_expr (spec_call_array_new_single_4 a1 a2)) ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq ext_expr exte (spec_call_array_new_single_4 a1 a2) ->
        @eq out o oo -> P S C a1 a2 oo) ->
       (red_expr S C (spec_call_array_new_single_4 a1 a2) oo ->
        forall (S0 S' : state) (C0 : execution_ctx) 
          (l : object_loc) (ilen : Z),
        object_set_property S a1
          (String (Ascii false false true true false true true false)
             (String (Ascii true false true false false true true false)
                (String (Ascii false true true true false true true false)
                   (String (Ascii true true true false false true true false)
                      (String
                         (Ascii false false true false true true true false)
                         (String
                            (Ascii false false false true false true true
                               false) EmptyString))))))
          (attributes_data_of
             (attributes_data_intro
                (value_prim (prim_number (JsNumber.of_int a2))) true false
                false)) S' ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq object_loc l a1 ->
        @eq Z ilen a2 ->
        @eq out (out_ter S' (res_val (value_object a1))) oo ->
        P S C a1 a2 (out_ter S' (res_val (value_object a1)))) ->
       red_expr S C (spec_call_array_new_single_4 a1 a2) oo -> P S C a1 a2 oo.

Parameter inv_red_expr_spec_call_array_is_array_1
     : forall (S : state) (C : execution_ctx) (a1 : value) 
         (oo : out) (P : state -> execution_ctx -> value -> out -> Prop),
       (red_expr S C (spec_call_array_is_array_1 a1) oo ->
        forall (S0 : state) (C0 : execution_ctx) (exte : ext_expr) (o : out),
        @eq (option out) (out_of_ext_expr (spec_call_array_is_array_1 a1))
          (@Some out oo) ->
        abort oo ->
        not (abort_intercepted_expr (spec_call_array_is_array_1 a1)) ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq ext_expr exte (spec_call_array_is_array_1 a1) ->
        @eq out o oo -> P S C a1 oo) ->
       (red_expr S C (spec_call_array_is_array_1 a1) oo ->
        forall (S0 : state) (C0 : execution_ctx) (arg : value),
        not (@eq type (type_of a1) type_object) ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq value arg a1 ->
        @eq out (out_ter S (res_val (value_prim (prim_bool false)))) oo ->
        P S C a1 (out_ter S (res_val (value_prim (prim_bool false))))) ->
       (red_expr S C (spec_call_array_is_array_1 a1) oo ->
        forall (S0 : state) (C0 : execution_ctx) (arg : value)
          (l : object_loc) (class : class_name) (o : out),
        @eq value a1 (value_object l) ->
        @object_method class_name object_class_ S l class ->
        red_expr S C (spec_call_array_is_array_2_3 class) oo ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq value arg a1 -> @eq out o oo -> P S C a1 oo) ->
       red_expr S C (spec_call_array_is_array_1 a1) oo -> P S C a1 oo.

Parameter inv_red_expr_spec_call_array_is_array_2_3
     : forall (S : state) (C : execution_ctx) (a1 : class_name) 
         (oo : out) (P : state -> execution_ctx -> string -> out -> Prop),
       (red_expr S C (spec_call_array_is_array_2_3 a1) oo ->
        forall (S0 : state) (C0 : execution_ctx) (exte : ext_expr) (o : out),
        @eq (option out) (out_of_ext_expr (spec_call_array_is_array_2_3 a1))
          (@Some out oo) ->
        abort oo ->
        not (abort_intercepted_expr (spec_call_array_is_array_2_3 a1)) ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq ext_expr exte (spec_call_array_is_array_2_3 a1) ->
        @eq out o oo -> P S C a1 oo) ->
       (red_expr S C (spec_call_array_is_array_2_3 a1) oo ->
        forall (S0 : state) (C0 : execution_ctx) (class : string),
        @eq string a1
          (String (Ascii true false false false false false true false)
             (String (Ascii false true false false true true true false)
                (String (Ascii false true false false true true true false)
                   (String
                      (Ascii true false false false false true true false)
                      (String
                         (Ascii true false false true true true true false)
                         EmptyString))))) ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq class_name class a1 ->
        @eq out (out_ter S (res_val (value_prim (prim_bool true)))) oo ->
        P S C a1 (out_ter S (res_val (value_prim (prim_bool true))))) ->
       (red_expr S C (spec_call_array_is_array_2_3 a1) oo ->
        forall (S0 : state) (C0 : execution_ctx) (class : class_name),
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq class_name class a1 ->
        @eq out (out_ter S (res_val (value_prim (prim_bool false)))) oo ->
        P S C a1 (out_ter S (res_val (value_prim (prim_bool false))))) ->
       red_expr S C (spec_call_array_is_array_2_3 a1) oo -> P S C a1 oo.

Parameter inv_red_expr_spec_call_array_proto_join
     : forall (S : state) (C : execution_ctx) (a1 : out) 
         (a2 : list value) (oo : out)
         (P : state -> execution_ctx -> out -> list value -> out -> Prop),
       (red_expr S C (spec_call_array_proto_join a1 a2) oo ->
        forall (S0 : state) (C0 : execution_ctx) (exte : ext_expr) (o : out),
        @eq (option out) (out_of_ext_expr (spec_call_array_proto_join a1 a2))
          (@Some out oo) ->
        abort oo ->
        not (abort_intercepted_expr (spec_call_array_proto_join a1 a2)) ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq ext_expr exte (spec_call_array_proto_join a1 a2) ->
        @eq out o oo -> P S C a1 a2 oo) ->
       (red_expr S C (spec_call_array_proto_join a1 a2) oo ->
        forall (S0 S' : state) (C0 : execution_ctx) 
          (l : object_loc) (o o1 : out) (args : list value),
        red_expr S' C
          (spec_object_get l
             (String (Ascii false false true true false true true false)
                (String (Ascii true false true false false true true false)
                   (String (Ascii false true true true false true true false)
                      (String
                         (Ascii true true true false false true true false)
                         (String
                            (Ascii false false true false true true true
                               false)
                            (String
                               (Ascii false false false true false true true
                                  false) EmptyString))))))) o1 ->
        red_expr S' C (spec_call_array_proto_join_1 l o1 a2) oo ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq out (out_ter S' (res_val (value_object l))) a1 ->
        @eq (list value) args a2 ->
        @eq out o oo -> P S C (out_ter S' (res_val (value_object l))) a2 oo) ->
       red_expr S C (spec_call_array_proto_join a1 a2) oo -> P S C a1 a2 oo.

Parameter inv_red_expr_spec_call_array_proto_join_1
     : forall (S : state) (C : execution_ctx) (a1 : object_loc) 
         (a2 : out) (a3 : list value) (oo : out)
         (P : state ->
              execution_ctx -> object_loc -> out -> list value -> out -> Prop),
       (red_expr S C (spec_call_array_proto_join_1 a1 a2 a3) oo ->
        forall (S0 : state) (C0 : execution_ctx) (exte : ext_expr) (o : out),
        @eq (option out)
          (out_of_ext_expr (spec_call_array_proto_join_1 a1 a2 a3))
          (@Some out oo) ->
        abort oo ->
        not (abort_intercepted_expr (spec_call_array_proto_join_1 a1 a2 a3)) ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq ext_expr exte (spec_call_array_proto_join_1 a1 a2 a3) ->
        @eq out o oo -> P S C a1 a2 a3 oo) ->
       (red_expr S C (spec_call_array_proto_join_1 a1 a2 a3) oo ->
        forall (S0 S' : state) (C0 : execution_ctx) 
          (l : object_loc) (vlen : value) (o : out) 
          (y : specret Z) (args : list value),
        @red_spec Z S' C (spec_to_uint32 vlen) y ->
        red_expr S' C (spec_call_array_proto_join_2 a1 y a3) oo ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq object_loc l a1 ->
        @eq out (out_ter S' (res_val vlen)) a2 ->
        @eq (list value) args a3 ->
        @eq out o oo -> P S C a1 (out_ter S' (res_val vlen)) a3 oo) ->
       red_expr S C (spec_call_array_proto_join_1 a1 a2 a3) oo ->
       P S C a1 a2 a3 oo.

Parameter inv_red_expr_spec_call_array_proto_join_2
     : forall (S : state) (C : execution_ctx) (a1 : object_loc)
         (a2 : specret Z) (a3 : list value) (oo : out)
         (P : state ->
              execution_ctx ->
              object_loc -> specret Z -> list value -> out -> Prop),
       (red_expr S C (spec_call_array_proto_join_2 a1 a2 a3) oo ->
        forall (S0 : state) (C0 : execution_ctx) (exte : ext_expr) (o : out),
        @eq (option out)
          (out_of_ext_expr (spec_call_array_proto_join_2 a1 a2 a3))
          (@Some out oo) ->
        abort oo ->
        not (abort_intercepted_expr (spec_call_array_proto_join_2 a1 a2 a3)) ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq ext_expr exte (spec_call_array_proto_join_2 a1 a2 a3) ->
        @eq out o oo -> P S C a1 a2 a3 oo) ->
       (red_expr S C (spec_call_array_proto_join_2 a1 a2 a3) oo ->
        forall (S0 S' : state) (C0 : execution_ctx) 
          (l : object_loc) (length : Z) (o : out) (args : list value)
          (sep : value),
        arguments_from a3 (@cons value sep (@nil value)) ->
        red_expr S' C (spec_call_array_proto_join_3 a1 length sep) oo ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq object_loc l a1 ->
        @eq (specret Z) (@ret Z S' length) a2 ->
        @eq (list value) args a3 ->
        @eq out o oo -> P S C a1 (@ret Z S' length) a3 oo) ->
       red_expr S C (spec_call_array_proto_join_2 a1 a2 a3) oo ->
       P S C a1 a2 a3 oo.

Parameter inv_red_expr_spec_call_array_proto_join_3
     : forall (S : state) (C : execution_ctx) (a1 : object_loc) 
         (a2 : Z) (a3 : value) (oo : out)
         (P : state ->
              execution_ctx -> object_loc -> Z -> value -> out -> Prop),
       (red_expr S C (spec_call_array_proto_join_3 a1 a2 a3) oo ->
        forall (S0 : state) (C0 : execution_ctx) (exte : ext_expr) (o : out),
        @eq (option out)
          (out_of_ext_expr (spec_call_array_proto_join_3 a1 a2 a3))
          (@Some out oo) ->
        abort oo ->
        not (abort_intercepted_expr (spec_call_array_proto_join_3 a1 a2 a3)) ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq ext_expr exte (spec_call_array_proto_join_3 a1 a2 a3) ->
        @eq out o oo -> P S C a1 a2 a3 oo) ->
       (red_expr S C (spec_call_array_proto_join_3 a1 a2 a3) oo ->
        forall (S0 S' : state) (C0 : execution_ctx) 
          (l : object_loc) (length : Z) (o o1 : out) 
          (sep : value),
        @eq value a3 (value_prim prim_undef) ->
        red_expr S' C
          (spec_to_string
             (value_prim
                (prim_string
                   (String
                      (Ascii false false true true false true false false)
                      EmptyString)))) o1 ->
        red_expr S' C (spec_call_array_proto_join_4 a1 a2 o1) oo ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq object_loc l a1 ->
        @eq Z length a2 ->
        @eq value sep a3 -> @eq out o oo -> P S C a1 a2 a3 oo) ->
       (red_expr S C (spec_call_array_proto_join_3 a1 a2 a3) oo ->
        forall (S0 S' : state) (C0 : execution_ctx) 
          (l : object_loc) (length : Z) (o o1 : out) 
          (sep : value),
        not (@eq value a3 (value_prim prim_undef)) ->
        red_expr S' C (spec_to_string a3) o1 ->
        red_expr S' C (spec_call_array_proto_join_4 a1 a2 o1) oo ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq object_loc l a1 ->
        @eq Z length a2 ->
        @eq value sep a3 -> @eq out o oo -> P S C a1 a2 a3 oo) ->
       red_expr S C (spec_call_array_proto_join_3 a1 a2 a3) oo ->
       P S C a1 a2 a3 oo.

Parameter inv_red_expr_spec_call_array_proto_join_4
     : forall (S : state) (C : execution_ctx) (a1 : object_loc) 
         (a2 : Z) (a3 oo : out)
         (P : state -> execution_ctx -> object_loc -> Z -> out -> out -> Prop),
       (red_expr S C (spec_call_array_proto_join_4 a1 a2 a3) oo ->
        forall (S0 : state) (C0 : execution_ctx) (exte : ext_expr) (o : out),
        @eq (option out)
          (out_of_ext_expr (spec_call_array_proto_join_4 a1 a2 a3))
          (@Some out oo) ->
        abort oo ->
        not (abort_intercepted_expr (spec_call_array_proto_join_4 a1 a2 a3)) ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq ext_expr exte (spec_call_array_proto_join_4 a1 a2 a3) ->
        @eq out o oo -> P S C a1 a2 a3 oo) ->
       (red_expr S C (spec_call_array_proto_join_4 a1 a2 a3) oo ->
        forall (S0 S' : state) (C0 : execution_ctx) 
          (l : object_loc) (length : Z) (s : string),
        @eq Z a2 Z0 ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq object_loc l a1 ->
        @eq Z length a2 ->
        @eq out (out_ter S' (res_val (value_prim (prim_string s)))) a3 ->
        @eq out (out_ter S' (res_val (value_prim (prim_string EmptyString))))
          oo ->
        P S C a1 a2 (out_ter S' (res_val (value_prim (prim_string s))))
          (out_ter S' (res_val (value_prim (prim_string EmptyString))))) ->
       (red_expr S C (spec_call_array_proto_join_4 a1 a2 a3) oo ->
        forall (S0 S' : state) (C0 : execution_ctx) 
          (l : object_loc) (length : Z) (sep : string) 
          (o : out) (y : specret string),
        not (@eq Z a2 Z0) ->
        @red_spec string S' C (spec_call_array_proto_join_vtsfj a1 Z0) y ->
        red_expr S' C (spec_call_array_proto_join_5 a1 a2 sep y) oo ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq object_loc l a1 ->
        @eq Z length a2 ->
        @eq out (out_ter S' (res_val (value_prim (prim_string sep)))) a3 ->
        @eq out o oo ->
        P S C a1 a2 (out_ter S' (res_val (value_prim (prim_string sep)))) oo) ->
       red_expr S C (spec_call_array_proto_join_4 a1 a2 a3) oo ->
       P S C a1 a2 a3 oo.

Parameter inv_red_expr_spec_call_array_proto_join_5
     : forall (S : state) (C : execution_ctx) (a1 : object_loc) 
         (a2 : Z) (a3 : string) (a4 : specret string) 
         (oo : out)
         (P : state ->
              execution_ctx ->
              object_loc -> Z -> string -> specret string -> out -> Prop),
       (red_expr S C (spec_call_array_proto_join_5 a1 a2 a3 a4) oo ->
        forall (S0 : state) (C0 : execution_ctx) (exte : ext_expr) (o : out),
        @eq (option out)
          (out_of_ext_expr (spec_call_array_proto_join_5 a1 a2 a3 a4))
          (@Some out oo) ->
        abort oo ->
        not
          (abort_intercepted_expr (spec_call_array_proto_join_5 a1 a2 a3 a4)) ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq ext_expr exte (spec_call_array_proto_join_5 a1 a2 a3 a4) ->
        @eq out o oo -> P S C a1 a2 a3 a4 oo) ->
       (red_expr S C (spec_call_array_proto_join_5 a1 a2 a3 a4) oo ->
        forall (S0 S' : state) (C0 : execution_ctx) 
          (l : object_loc) (length : Z) (sep s : string) 
          (o : out),
        red_expr S' C
          (spec_call_array_proto_join_elements a1 (Zpos xH) a2 a3 s) oo ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq object_loc l a1 ->
        @eq Z length a2 ->
        @eq string sep a3 ->
        @eq (specret string) (@ret string S' s) a4 ->
        @eq out o oo -> P S C a1 a2 a3 (@ret string S' s) oo) ->
       red_expr S C (spec_call_array_proto_join_5 a1 a2 a3 a4) oo ->
       P S C a1 a2 a3 a4 oo.

Parameter inv_red_expr_spec_call_array_proto_join_elements
     : forall (S : state) (C : execution_ctx) (a1 : object_loc) 
         (a2 a3 : Z) (a4 a5 : string) (oo : out)
         (P : state ->
              execution_ctx ->
              object_loc -> Z -> Z -> string -> string -> out -> Prop),
       (red_expr S C (spec_call_array_proto_join_elements a1 a2 a3 a4 a5) oo ->
        forall (S0 : state) (C0 : execution_ctx) (exte : ext_expr) (o : out),
        @eq (option out)
          (out_of_ext_expr
             (spec_call_array_proto_join_elements a1 a2 a3 a4 a5))
          (@Some out oo) ->
        abort oo ->
        not
          (abort_intercepted_expr
             (spec_call_array_proto_join_elements a1 a2 a3 a4 a5)) ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq ext_expr exte
          (spec_call_array_proto_join_elements a1 a2 a3 a4 a5) ->
        @eq out o oo -> P S C a1 a2 a3 a4 a5 oo) ->
       (red_expr S C (spec_call_array_proto_join_elements a1 a2 a3 a4 a5) oo ->
        forall (S0 : state) (C0 : execution_ctx) (l : object_loc)
          (k length : Z) (sep sR : string),
        not (@lt Z (@lt_from_le Z le_int_inst) a2 a3) ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq object_loc l a1 ->
        @eq Z k a2 ->
        @eq Z length a3 ->
        @eq string sep a4 ->
        @eq string sR a5 ->
        @eq out (out_ter S (res_val (value_prim (prim_string a5)))) oo ->
        P S C a1 a2 a3 a4 a5
          (out_ter S (res_val (value_prim (prim_string a5))))) ->
       (red_expr S C (spec_call_array_proto_join_elements a1 a2 a3 a4 a5) oo ->
        forall (S0 : state) (C0 : execution_ctx) (l : object_loc)
          (k length : Z) (sep sR str : string) (o : out),
        @lt Z (@lt_from_le Z le_int_inst) a2 a3 ->
        @eq string str (String.append a5 a4) ->
        red_expr S C (spec_call_array_proto_join_elements_1 a1 a2 a3 a4 str)
          oo ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq object_loc l a1 ->
        @eq Z k a2 ->
        @eq Z length a3 ->
        @eq string sep a4 ->
        @eq string sR a5 -> @eq out o oo -> P S C a1 a2 a3 a4 a5 oo) ->
       red_expr S C (spec_call_array_proto_join_elements a1 a2 a3 a4 a5) oo ->
       P S C a1 a2 a3 a4 a5 oo.

Parameter inv_red_expr_spec_call_array_proto_join_elements_1
     : forall (S : state) (C : execution_ctx) (a1 : object_loc) 
         (a2 a3 : Z) (a4 a5 : string) (oo : out)
         (P : state ->
              execution_ctx ->
              object_loc -> Z -> Z -> string -> string -> out -> Prop),
       (red_expr S C (spec_call_array_proto_join_elements_1 a1 a2 a3 a4 a5)
          oo ->
        forall (S0 : state) (C0 : execution_ctx) (exte : ext_expr) (o : out),
        @eq (option out)
          (out_of_ext_expr
             (spec_call_array_proto_join_elements_1 a1 a2 a3 a4 a5))
          (@Some out oo) ->
        abort oo ->
        not
          (abort_intercepted_expr
             (spec_call_array_proto_join_elements_1 a1 a2 a3 a4 a5)) ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq ext_expr exte
          (spec_call_array_proto_join_elements_1 a1 a2 a3 a4 a5) ->
        @eq out o oo -> P S C a1 a2 a3 a4 a5 oo) ->
       (red_expr S C (spec_call_array_proto_join_elements_1 a1 a2 a3 a4 a5)
          oo ->
        forall (S0 : state) (C0 : execution_ctx) (l : object_loc)
          (k length : Z) (sep str : string) (y : specret string) 
          (o : out),
        @red_spec string S C (spec_call_array_proto_join_vtsfj a1 a2) y ->
        red_expr S C (spec_call_array_proto_join_elements_2 a1 a2 a3 a4 a5 y)
          oo ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq object_loc l a1 ->
        @eq Z k a2 ->
        @eq Z length a3 ->
        @eq string sep a4 ->
        @eq string str a5 -> @eq out o oo -> P S C a1 a2 a3 a4 a5 oo) ->
       red_expr S C (spec_call_array_proto_join_elements_1 a1 a2 a3 a4 a5) oo ->
       P S C a1 a2 a3 a4 a5 oo.

Parameter inv_red_expr_spec_call_array_proto_join_elements_2
     : forall (S : state) (C : execution_ctx) (a1 : object_loc) 
         (a2 a3 : Z) (a4 a5 : string) (a6 : specret string) 
         (oo : out)
         (P : state ->
              execution_ctx ->
              object_loc ->
              Z -> Z -> string -> string -> specret string -> out -> Prop),
       (red_expr S C
          (spec_call_array_proto_join_elements_2 a1 a2 a3 a4 a5 a6) oo ->
        forall (S0 : state) (C0 : execution_ctx) (exte : ext_expr) (o : out),
        @eq (option out)
          (out_of_ext_expr
             (spec_call_array_proto_join_elements_2 a1 a2 a3 a4 a5 a6))
          (@Some out oo) ->
        abort oo ->
        not
          (abort_intercepted_expr
             (spec_call_array_proto_join_elements_2 a1 a2 a3 a4 a5 a6)) ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq ext_expr exte
          (spec_call_array_proto_join_elements_2 a1 a2 a3 a4 a5 a6) ->
        @eq out o oo -> P S C a1 a2 a3 a4 a5 a6 oo) ->
       (red_expr S C
          (spec_call_array_proto_join_elements_2 a1 a2 a3 a4 a5 a6) oo ->
        forall (S0 S' : state) (C0 : execution_ctx) 
          (l : object_loc) (k length : Z) (sep str next : string) 
          (o : out),
        red_expr S' C
          (spec_call_array_proto_join_elements a1 (Z.add a2 (Zpos xH)) a3 a4
             (String.append a5 next)) oo ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq object_loc l a1 ->
        @eq Z k a2 ->
        @eq Z length a3 ->
        @eq string sep a4 ->
        @eq string str a5 ->
        @eq (specret string) (@ret string S' next) a6 ->
        @eq out o oo -> P S C a1 a2 a3 a4 a5 (@ret string S' next) oo) ->
       red_expr S C (spec_call_array_proto_join_elements_2 a1 a2 a3 a4 a5 a6)
         oo -> P S C a1 a2 a3 a4 a5 a6 oo.

Parameter inv_red_expr_spec_call_array_proto_to_string
     : forall (S : state) (C : execution_ctx) (a1 oo : out)
         (P : state -> execution_ctx -> out -> out -> Prop),
       (red_expr S C (spec_call_array_proto_to_string a1) oo ->
        forall (S0 : state) (C0 : execution_ctx) (exte : ext_expr) (o : out),
        @eq (option out)
          (out_of_ext_expr (spec_call_array_proto_to_string a1))
          (@Some out oo) ->
        abort oo ->
        not (abort_intercepted_expr (spec_call_array_proto_to_string a1)) ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq ext_expr exte (spec_call_array_proto_to_string a1) ->
        @eq out o oo -> P S C a1 oo) ->
       (red_expr S C (spec_call_array_proto_to_string a1) oo ->
        forall (S0 S' : state) (C0 : execution_ctx) 
          (l : object_loc) (o o1 : out),
        red_expr S' C
          (spec_object_get l
             (String (Ascii false true false true false true true false)
                (String (Ascii true true true true false true true false)
                   (String
                      (Ascii true false false true false true true false)
                      (String
                         (Ascii false true true true false true true false)
                         EmptyString))))) o1 ->
        red_expr S' C (spec_call_array_proto_to_string_1 l o1) oo ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq out (out_ter S' (res_val (value_object l))) a1 ->
        @eq out o oo -> P S C (out_ter S' (res_val (value_object l))) oo) ->
       red_expr S C (spec_call_array_proto_to_string a1) oo -> P S C a1 oo.

Parameter inv_red_expr_spec_call_array_proto_to_string_1
     : forall (S : state) (C : execution_ctx) (a1 : object_loc) 
         (a2 oo : out)
         (P : state -> execution_ctx -> object_loc -> out -> out -> Prop),
       (red_expr S C (spec_call_array_proto_to_string_1 a1 a2) oo ->
        forall (S0 : state) (C0 : execution_ctx) (exte : ext_expr) (o : out),
        @eq (option out)
          (out_of_ext_expr (spec_call_array_proto_to_string_1 a1 a2))
          (@Some out oo) ->
        abort oo ->
        not
          (abort_intercepted_expr (spec_call_array_proto_to_string_1 a1 a2)) ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq ext_expr exte (spec_call_array_proto_to_string_1 a1 a2) ->
        @eq out o oo -> P S C a1 a2 oo) ->
       (red_expr S C (spec_call_array_proto_to_string_1 a1 a2) oo ->
        forall (S0 S' : state) (C0 : execution_ctx) 
          (l : object_loc) (o : out) (vfunc : value),
        not (is_callable S' vfunc) ->
        red_expr S' C
          (spec_call_prealloc prealloc_object_proto_to_string
             (value_object a1) (@nil value)) oo ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq object_loc l a1 ->
        @eq out (out_ter S' (res_val vfunc)) a2 ->
        @eq out o oo -> P S C a1 (out_ter S' (res_val vfunc)) oo) ->
       (red_expr S C (spec_call_array_proto_to_string_1 a1 a2) oo ->
        forall (S0 S' : state) (C0 : execution_ctx) 
          (l : object_loc) (o : out) (vfunc : value) 
          (func : object_loc),
        is_callable S' vfunc ->
        @eq value vfunc (value_object func) ->
        red_expr S' C (spec_call func (value_object a1) (@nil value)) oo ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq object_loc l a1 ->
        @eq out (out_ter S' (res_val vfunc)) a2 ->
        @eq out o oo -> P S C a1 (out_ter S' (res_val vfunc)) oo) ->
       red_expr S C (spec_call_array_proto_to_string_1 a1 a2) oo ->
       P S C a1 a2 oo.

Parameter inv_red_expr_spec_call_array_proto_pop_1
     : forall (S : state) (C : execution_ctx) (a1 oo : out)
         (P : state -> execution_ctx -> out -> out -> Prop),
       (red_expr S C (spec_call_array_proto_pop_1 a1) oo ->
        forall (S0 : state) (C0 : execution_ctx) (exte : ext_expr) (o : out),
        @eq (option out) (out_of_ext_expr (spec_call_array_proto_pop_1 a1))
          (@Some out oo) ->
        abort oo ->
        not (abort_intercepted_expr (spec_call_array_proto_pop_1 a1)) ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq ext_expr exte (spec_call_array_proto_pop_1 a1) ->
        @eq out o oo -> P S C a1 oo) ->
       (red_expr S C (spec_call_array_proto_pop_1 a1) oo ->
        forall (S0 S1 : state) (C0 : execution_ctx) 
          (l : object_loc) (o o1 : out),
        red_expr S1 C
          (spec_object_get l
             (String (Ascii false false true true false true true false)
                (String (Ascii true false true false false true true false)
                   (String (Ascii false true true true false true true false)
                      (String
                         (Ascii true true true false false true true false)
                         (String
                            (Ascii false false true false true true true
                               false)
                            (String
                               (Ascii false false false true false true true
                                  false) EmptyString))))))) o1 ->
        red_expr S1 C (spec_call_array_proto_pop_2 l o1) oo ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq out (out_ter S1 (res_val (value_object l))) a1 ->
        @eq out o oo -> P S C (out_ter S1 (res_val (value_object l))) oo) ->
       red_expr S C (spec_call_array_proto_pop_1 a1) oo -> P S C a1 oo.

Parameter inv_red_expr_spec_call_array_proto_pop_2
     : forall (S : state) (C : execution_ctx) (a1 : object_loc) 
         (a2 oo : out)
         (P : state -> execution_ctx -> object_loc -> out -> out -> Prop),
       (red_expr S C (spec_call_array_proto_pop_2 a1 a2) oo ->
        forall (S0 : state) (C0 : execution_ctx) (exte : ext_expr) (o : out),
        @eq (option out)
          (out_of_ext_expr (spec_call_array_proto_pop_2 a1 a2))
          (@Some out oo) ->
        abort oo ->
        not (abort_intercepted_expr (spec_call_array_proto_pop_2 a1 a2)) ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq ext_expr exte (spec_call_array_proto_pop_2 a1 a2) ->
        @eq out o oo -> P S C a1 a2 oo) ->
       (red_expr S C (spec_call_array_proto_pop_2 a1 a2) oo ->
        forall (S0 S1 : state) (C0 : execution_ctx) 
          (l : object_loc) (vlen : value) (o : out) 
          (y : specret Z),
        @red_spec Z S1 C (spec_to_uint32 vlen) y ->
        red_expr S1 C (spec_call_array_proto_pop_3 a1 y) oo ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq object_loc l a1 ->
        @eq out (out_ter S1 (res_val vlen)) a2 ->
        @eq out o oo -> P S C a1 (out_ter S1 (res_val vlen)) oo) ->
       red_expr S C (spec_call_array_proto_pop_2 a1 a2) oo -> P S C a1 a2 oo.

Parameter inv_red_expr_spec_call_array_proto_pop_3
     : forall (S : state) (C : execution_ctx) (a1 : object_loc)
         (a2 : specret Z) (oo : out)
         (P : state ->
              execution_ctx -> object_loc -> specret Z -> out -> Prop),
       (red_expr S C (spec_call_array_proto_pop_3 a1 a2) oo ->
        forall (S0 : state) (C0 : execution_ctx) (exte : ext_expr) (o : out),
        @eq (option out)
          (out_of_ext_expr (spec_call_array_proto_pop_3 a1 a2))
          (@Some out oo) ->
        abort oo ->
        not (abort_intercepted_expr (spec_call_array_proto_pop_3 a1 a2)) ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq ext_expr exte (spec_call_array_proto_pop_3 a1 a2) ->
        @eq out o oo -> P S C a1 a2 oo) ->
       (red_expr S C (spec_call_array_proto_pop_3 a1 a2) oo ->
        forall (S0 S1 : state) (C0 : execution_ctx) 
          (l : object_loc) (o : out),
        red_expr S1 C (spec_call_array_proto_pop_3_empty_1 a1) oo ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq object_loc l a1 ->
        @eq (specret Z) (@ret Z S1 (my_Z_of_nat O)) a2 ->
        @eq out o oo -> P S C a1 (@ret Z S1 (my_Z_of_nat O)) oo) ->
       (red_expr S C (spec_call_array_proto_pop_3 a1 a2) oo ->
        forall (S0 S1 : state) (C0 : execution_ctx) 
          (l : object_loc) (lenuint32 : Z) (o : out),
        not (@eq Z lenuint32 (my_Z_of_nat O)) ->
        red_expr S1 C (spec_call_array_proto_pop_3_nonempty_1 a1 lenuint32)
          oo ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq object_loc l a1 ->
        @eq (specret Z) (@ret Z S1 lenuint32) a2 ->
        @eq out o oo -> P S C a1 (@ret Z S1 lenuint32) oo) ->
       red_expr S C (spec_call_array_proto_pop_3 a1 a2) oo -> P S C a1 a2 oo.

Parameter inv_red_expr_spec_call_array_proto_pop_3_empty_1
     : forall (S : state) (C : execution_ctx) (a1 : object_loc) 
         (oo : out) (P : state -> execution_ctx -> object_loc -> out -> Prop),
       (red_expr S C (spec_call_array_proto_pop_3_empty_1 a1) oo ->
        forall (S0 : state) (C0 : execution_ctx) (exte : ext_expr) (o : out),
        @eq (option out)
          (out_of_ext_expr (spec_call_array_proto_pop_3_empty_1 a1))
          (@Some out oo) ->
        abort oo ->
        not (abort_intercepted_expr (spec_call_array_proto_pop_3_empty_1 a1)) ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq ext_expr exte (spec_call_array_proto_pop_3_empty_1 a1) ->
        @eq out o oo -> P S C a1 oo) ->
       (red_expr S C (spec_call_array_proto_pop_3_empty_1 a1) oo ->
        forall (S0 : state) (C0 : execution_ctx) (l : object_loc)
          (o o1 : out),
        red_expr S C
          (spec_object_put a1
             (String (Ascii false false true true false true true false)
                (String (Ascii true false true false false true true false)
                   (String (Ascii false true true true false true true false)
                      (String
                         (Ascii true true true false false true true false)
                         (String
                            (Ascii false false true false true true true
                               false)
                            (String
                               (Ascii false false false true false true true
                                  false) EmptyString))))))
             (value_prim (prim_number JsNumber.zero)) throw_true) o1 ->
        red_expr S C (spec_call_array_proto_pop_3_empty_2 o1) oo ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq object_loc l a1 -> @eq out o oo -> P S C a1 oo) ->
       red_expr S C (spec_call_array_proto_pop_3_empty_1 a1) oo ->
       P S C a1 oo.

Parameter inv_red_expr_spec_call_array_proto_pop_3_empty_2
     : forall (S : state) (C : execution_ctx) (a1 oo : out)
         (P : state -> execution_ctx -> out -> out -> Prop),
       (red_expr S C (spec_call_array_proto_pop_3_empty_2 a1) oo ->
        forall (S0 : state) (C0 : execution_ctx) (exte : ext_expr) (o : out),
        @eq (option out)
          (out_of_ext_expr (spec_call_array_proto_pop_3_empty_2 a1))
          (@Some out oo) ->
        abort oo ->
        not (abort_intercepted_expr (spec_call_array_proto_pop_3_empty_2 a1)) ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq ext_expr exte (spec_call_array_proto_pop_3_empty_2 a1) ->
        @eq out o oo -> P S C a1 oo) ->
       (red_expr S C (spec_call_array_proto_pop_3_empty_2 a1) oo ->
        forall (S0 S1 : state) (C0 : execution_ctx) (R : res),
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq out (out_ter S1 R) a1 ->
        @eq out (out_ter S1 (res_val (value_prim prim_undef))) oo ->
        P S C (out_ter S1 R) (out_ter S1 (res_val (value_prim prim_undef)))) ->
       red_expr S C (spec_call_array_proto_pop_3_empty_2 a1) oo ->
       P S C a1 oo.

Parameter inv_red_expr_spec_call_array_proto_pop_3_nonempty_1
     : forall (S : state) (C : execution_ctx) (a1 : object_loc) 
         (a2 : Z) (oo : out)
         (P : state -> execution_ctx -> object_loc -> Z -> out -> Prop),
       (red_expr S C (spec_call_array_proto_pop_3_nonempty_1 a1 a2) oo ->
        forall (S0 : state) (C0 : execution_ctx) (exte : ext_expr) (o : out),
        @eq (option out)
          (out_of_ext_expr (spec_call_array_proto_pop_3_nonempty_1 a1 a2))
          (@Some out oo) ->
        abort oo ->
        not
          (abort_intercepted_expr
             (spec_call_array_proto_pop_3_nonempty_1 a1 a2)) ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq ext_expr exte (spec_call_array_proto_pop_3_nonempty_1 a1 a2) ->
        @eq out o oo -> P S C a1 a2 oo) ->
       (red_expr S C (spec_call_array_proto_pop_3_nonempty_1 a1 a2) oo ->
        forall (S0 : state) (C0 : execution_ctx) (l : object_loc)
          (lenuint32 : Z) (o o1 : out),
        red_expr S C
          (spec_to_string
             (value_prim (prim_number (JsNumber.of_int (Z.sub a2 (Zpos xH))))))
          o1 ->
        red_expr S C (spec_call_array_proto_pop_3_nonempty_2 a1 o1) oo ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq object_loc l a1 ->
        @eq Z lenuint32 a2 -> @eq out o oo -> P S C a1 a2 oo) ->
       red_expr S C (spec_call_array_proto_pop_3_nonempty_1 a1 a2) oo ->
       P S C a1 a2 oo.

Parameter inv_red_expr_spec_call_array_proto_pop_3_nonempty_2
     : forall (S : state) (C : execution_ctx) (a1 : object_loc) 
         (a2 oo : out)
         (P : state -> execution_ctx -> object_loc -> out -> out -> Prop),
       (red_expr S C (spec_call_array_proto_pop_3_nonempty_2 a1 a2) oo ->
        forall (S0 : state) (C0 : execution_ctx) (exte : ext_expr) (o : out),
        @eq (option out)
          (out_of_ext_expr (spec_call_array_proto_pop_3_nonempty_2 a1 a2))
          (@Some out oo) ->
        abort oo ->
        not
          (abort_intercepted_expr
             (spec_call_array_proto_pop_3_nonempty_2 a1 a2)) ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq ext_expr exte (spec_call_array_proto_pop_3_nonempty_2 a1 a2) ->
        @eq out o oo -> P S C a1 a2 oo) ->
       (red_expr S C (spec_call_array_proto_pop_3_nonempty_2 a1 a2) oo ->
        forall (S0 S1 : state) (C0 : execution_ctx) 
          (l : object_loc) (vindx : prop_name) (o o1 : out),
        red_expr S1 C (spec_object_get a1 vindx) o1 ->
        red_expr S1 C
          (spec_call_array_proto_pop_3_nonempty_3 a1
             (value_prim (prim_string vindx)) o1) oo ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq object_loc l a1 ->
        @eq out (out_ter S1 (res_val (value_prim (prim_string vindx)))) a2 ->
        @eq out o oo ->
        P S C a1 (out_ter S1 (res_val (value_prim (prim_string vindx)))) oo) ->
       red_expr S C (spec_call_array_proto_pop_3_nonempty_2 a1 a2) oo ->
       P S C a1 a2 oo.

Parameter inv_red_expr_spec_call_array_proto_pop_3_nonempty_3
     : forall (S : state) (C : execution_ctx) (a1 : object_loc) 
         (a2 : value) (a3 oo : out)
         (P : state ->
              execution_ctx -> object_loc -> value -> out -> out -> Prop),
       (red_expr S C (spec_call_array_proto_pop_3_nonempty_3 a1 a2 a3) oo ->
        forall (S0 : state) (C0 : execution_ctx) (exte : ext_expr) (o : out),
        @eq (option out)
          (out_of_ext_expr (spec_call_array_proto_pop_3_nonempty_3 a1 a2 a3))
          (@Some out oo) ->
        abort oo ->
        not
          (abort_intercepted_expr
             (spec_call_array_proto_pop_3_nonempty_3 a1 a2 a3)) ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq ext_expr exte (spec_call_array_proto_pop_3_nonempty_3 a1 a2 a3) ->
        @eq out o oo -> P S C a1 a2 a3 oo) ->
       (red_expr S C (spec_call_array_proto_pop_3_nonempty_3 a1 a2 a3) oo ->
        forall (S0 S1 : state) (C0 : execution_ctx) 
          (l : object_loc) (vindx : prop_name) (velem : value) 
          (o o1 : out),
        red_expr S1 C
          (spec_object_delete_1 builtin_delete_default a1 vindx throw_true)
          o1 ->
        red_expr S1 C
          (spec_call_array_proto_pop_3_nonempty_4 a1
             (value_prim (prim_string vindx)) velem o1) oo ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq object_loc l a1 ->
        @eq value (value_prim (prim_string vindx)) a2 ->
        @eq out (out_ter S1 (res_val velem)) a3 ->
        @eq out o oo ->
        P S C a1 (value_prim (prim_string vindx))
          (out_ter S1 (res_val velem)) oo) ->
       red_expr S C (spec_call_array_proto_pop_3_nonempty_3 a1 a2 a3) oo ->
       P S C a1 a2 a3 oo.

Parameter inv_red_expr_spec_call_array_proto_pop_3_nonempty_4
     : forall (S : state) (C : execution_ctx) (a1 : object_loc)
         (a2 a3 : value) (a4 oo : out)
         (P : state ->
              execution_ctx ->
              object_loc -> value -> value -> out -> out -> Prop),
       (red_expr S C (spec_call_array_proto_pop_3_nonempty_4 a1 a2 a3 a4) oo ->
        forall (S0 : state) (C0 : execution_ctx) (exte : ext_expr) (o : out),
        @eq (option out)
          (out_of_ext_expr
             (spec_call_array_proto_pop_3_nonempty_4 a1 a2 a3 a4))
          (@Some out oo) ->
        abort oo ->
        not
          (abort_intercepted_expr
             (spec_call_array_proto_pop_3_nonempty_4 a1 a2 a3 a4)) ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq ext_expr exte
          (spec_call_array_proto_pop_3_nonempty_4 a1 a2 a3 a4) ->
        @eq out o oo -> P S C a1 a2 a3 a4 oo) ->
       (red_expr S C (spec_call_array_proto_pop_3_nonempty_4 a1 a2 a3 a4) oo ->
        forall (S0 S1 : state) (C0 : execution_ctx) 
          (l : object_loc) (vindx velem : value) (o o1 : out) 
          (R : res),
        red_expr S1 C
          (spec_object_put a1
             (String (Ascii false false true true false true true false)
                (String (Ascii true false true false false true true false)
                   (String (Ascii false true true true false true true false)
                      (String
                         (Ascii true true true false false true true false)
                         (String
                            (Ascii false false true false true true true
                               false)
                            (String
                               (Ascii false false false true false true true
                                  false) EmptyString)))))) a2 throw_true) o1 ->
        red_expr S1 C (spec_call_array_proto_pop_3_nonempty_5 a3 o1) oo ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq object_loc l a1 ->
        @eq value vindx a2 ->
        @eq value velem a3 ->
        @eq out (out_ter S1 R) a4 ->
        @eq out o oo -> P S C a1 a2 a3 (out_ter S1 R) oo) ->
       red_expr S C (spec_call_array_proto_pop_3_nonempty_4 a1 a2 a3 a4) oo ->
       P S C a1 a2 a3 a4 oo.

Parameter inv_red_expr_spec_call_array_proto_pop_3_nonempty_5
     : forall (S : state) (C : execution_ctx) (a1 : value) 
         (a2 oo : out)
         (P : state -> execution_ctx -> value -> out -> out -> Prop),
       (red_expr S C (spec_call_array_proto_pop_3_nonempty_5 a1 a2) oo ->
        forall (S0 : state) (C0 : execution_ctx) (exte : ext_expr) (o : out),
        @eq (option out)
          (out_of_ext_expr (spec_call_array_proto_pop_3_nonempty_5 a1 a2))
          (@Some out oo) ->
        abort oo ->
        not
          (abort_intercepted_expr
             (spec_call_array_proto_pop_3_nonempty_5 a1 a2)) ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq ext_expr exte (spec_call_array_proto_pop_3_nonempty_5 a1 a2) ->
        @eq out o oo -> P S C a1 a2 oo) ->
       (red_expr S C (spec_call_array_proto_pop_3_nonempty_5 a1 a2) oo ->
        forall (S0 S1 : state) (C0 : execution_ctx) (velem : value) (R : res),
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq value velem a1 ->
        @eq out (out_ter S1 R) a2 ->
        @eq out (out_ter S1 (res_val a1)) oo ->
        P S C a1 (out_ter S1 R) (out_ter S1 (res_val a1))) ->
       red_expr S C (spec_call_array_proto_pop_3_nonempty_5 a1 a2) oo ->
       P S C a1 a2 oo.

Parameter inv_red_expr_spec_call_array_proto_push_1
     : forall (S : state) (C : execution_ctx) (a1 : out) 
         (a2 : list value) (oo : out)
         (P : state -> execution_ctx -> out -> list value -> out -> Prop),
       (red_expr S C (spec_call_array_proto_push_1 a1 a2) oo ->
        forall (S0 : state) (C0 : execution_ctx) (exte : ext_expr) (o : out),
        @eq (option out)
          (out_of_ext_expr (spec_call_array_proto_push_1 a1 a2))
          (@Some out oo) ->
        abort oo ->
        not (abort_intercepted_expr (spec_call_array_proto_push_1 a1 a2)) ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq ext_expr exte (spec_call_array_proto_push_1 a1 a2) ->
        @eq out o oo -> P S C a1 a2 oo) ->
       (red_expr S C (spec_call_array_proto_push_1 a1 a2) oo ->
        forall (S0 S1 : state) (C0 : execution_ctx) 
          (l : object_loc) (args : list value) (o o1 : out),
        red_expr S1 C
          (spec_object_get l
             (String (Ascii false false true true false true true false)
                (String (Ascii true false true false false true true false)
                   (String (Ascii false true true true false true true false)
                      (String
                         (Ascii true true true false false true true false)
                         (String
                            (Ascii false false true false true true true
                               false)
                            (String
                               (Ascii false false false true false true true
                                  false) EmptyString))))))) o1 ->
        red_expr S1 C (spec_call_array_proto_push_2 l a2 o1) oo ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq out (out_ter S1 (res_val (value_object l))) a1 ->
        @eq (list value) args a2 ->
        @eq out o oo -> P S C (out_ter S1 (res_val (value_object l))) a2 oo) ->
       red_expr S C (spec_call_array_proto_push_1 a1 a2) oo -> P S C a1 a2 oo.

Parameter inv_red_expr_spec_call_array_proto_push_2
     : forall (S : state) (C : execution_ctx) (a1 : object_loc)
         (a2 : list value) (a3 oo : out)
         (P : state ->
              execution_ctx -> object_loc -> list value -> out -> out -> Prop),
       (red_expr S C (spec_call_array_proto_push_2 a1 a2 a3) oo ->
        forall (S0 : state) (C0 : execution_ctx) (exte : ext_expr) (o : out),
        @eq (option out)
          (out_of_ext_expr (spec_call_array_proto_push_2 a1 a2 a3))
          (@Some out oo) ->
        abort oo ->
        not (abort_intercepted_expr (spec_call_array_proto_push_2 a1 a2 a3)) ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq ext_expr exte (spec_call_array_proto_push_2 a1 a2 a3) ->
        @eq out o oo -> P S C a1 a2 a3 oo) ->
       (red_expr S C (spec_call_array_proto_push_2 a1 a2 a3) oo ->
        forall (S0 S1 : state) (C0 : execution_ctx) 
          (l : object_loc) (args : list value) (vlen : value) 
          (y : specret Z) (o : out),
        @red_spec Z S1 C (spec_to_uint32 vlen) y ->
        red_expr S1 C (spec_call_array_proto_push_3 a1 a2 y) oo ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq object_loc l a1 ->
        @eq (list value) args a2 ->
        @eq out (out_ter S1 (res_val vlen)) a3 ->
        @eq out o oo -> P S C a1 a2 (out_ter S1 (res_val vlen)) oo) ->
       red_expr S C (spec_call_array_proto_push_2 a1 a2 a3) oo ->
       P S C a1 a2 a3 oo.

Parameter inv_red_expr_spec_call_array_proto_push_3
     : forall (S : state) (C : execution_ctx) (a1 : object_loc)
         (a2 : list value) (a3 : specret Z) (oo : out)
         (P : state ->
              execution_ctx ->
              object_loc -> list value -> specret Z -> out -> Prop),
       (red_expr S C (spec_call_array_proto_push_3 a1 a2 a3) oo ->
        forall (S0 : state) (C0 : execution_ctx) (exte : ext_expr) (o : out),
        @eq (option out)
          (out_of_ext_expr (spec_call_array_proto_push_3 a1 a2 a3))
          (@Some out oo) ->
        abort oo ->
        not (abort_intercepted_expr (spec_call_array_proto_push_3 a1 a2 a3)) ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq ext_expr exte (spec_call_array_proto_push_3 a1 a2 a3) ->
        @eq out o oo -> P S C a1 a2 a3 oo) ->
       (red_expr S C (spec_call_array_proto_push_3 a1 a2 a3) oo ->
        forall (S0 S1 : state) (C0 : execution_ctx) 
          (l : object_loc) (args : list value) (lenuint32 : Z) 
          (o : out),
        red_expr S1 C (spec_call_array_proto_push_4 a1 a2 lenuint32) oo ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq object_loc l a1 ->
        @eq (list value) args a2 ->
        @eq (specret Z) (@ret Z S1 lenuint32) a3 ->
        @eq out o oo -> P S C a1 a2 (@ret Z S1 lenuint32) oo) ->
       red_expr S C (spec_call_array_proto_push_3 a1 a2 a3) oo ->
       P S C a1 a2 a3 oo.

Parameter inv_red_expr_spec_call_array_proto_push_4
     : forall (S : state) (C : execution_ctx) (a1 : object_loc)
         (a2 : list value) (a3 : Z) (oo : out)
         (P : state ->
              execution_ctx -> object_loc -> list value -> Z -> out -> Prop),
       (red_expr S C (spec_call_array_proto_push_4 a1 a2 a3) oo ->
        forall (S0 : state) (C0 : execution_ctx) (exte : ext_expr) (o : out),
        @eq (option out)
          (out_of_ext_expr (spec_call_array_proto_push_4 a1 a2 a3))
          (@Some out oo) ->
        abort oo ->
        not (abort_intercepted_expr (spec_call_array_proto_push_4 a1 a2 a3)) ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq ext_expr exte (spec_call_array_proto_push_4 a1 a2 a3) ->
        @eq out o oo -> P S C a1 a2 a3 oo) ->
       (red_expr S C (spec_call_array_proto_push_4 a1 a2 a3) oo ->
        forall (S0 : state) (C0 : execution_ctx) (l : object_loc)
          (lenuint32 : Z) (o : out),
        red_expr S C
          (spec_call_array_proto_push_5 a1
             (value_prim (prim_number (JsNumber.of_int a3)))) oo ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq object_loc l a1 ->
        @eq (list value) (@nil value) a2 ->
        @eq Z lenuint32 a3 -> @eq out o oo -> P S C a1 (@nil value) a3 oo) ->
       (red_expr S C (spec_call_array_proto_push_4 a1 a2 a3) oo ->
        forall (S0 : state) (C0 : execution_ctx) (l : object_loc) 
          (v : value) (vs : list value) (lenuint32 : Z) 
          (o : out),
        red_expr S C (spec_call_array_proto_push_4_nonempty_1 a1 vs a3 v) oo ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq object_loc l a1 ->
        @eq (list value) (@cons value v vs) a2 ->
        @eq Z lenuint32 a3 ->
        @eq out o oo -> P S C a1 (@cons value v vs) a3 oo) ->
       red_expr S C (spec_call_array_proto_push_4 a1 a2 a3) oo ->
       P S C a1 a2 a3 oo.

Parameter inv_red_expr_spec_call_array_proto_push_4_nonempty_1
     : forall (S : state) (C : execution_ctx) (a1 : object_loc)
         (a2 : list value) (a3 : Z) (a4 : value) (oo : out)
         (P : state ->
              execution_ctx ->
              object_loc -> list value -> Z -> value -> out -> Prop),
       (red_expr S C (spec_call_array_proto_push_4_nonempty_1 a1 a2 a3 a4) oo ->
        forall (S0 : state) (C0 : execution_ctx) (exte : ext_expr) (o : out),
        @eq (option out)
          (out_of_ext_expr
             (spec_call_array_proto_push_4_nonempty_1 a1 a2 a3 a4))
          (@Some out oo) ->
        abort oo ->
        not
          (abort_intercepted_expr
             (spec_call_array_proto_push_4_nonempty_1 a1 a2 a3 a4)) ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq ext_expr exte
          (spec_call_array_proto_push_4_nonempty_1 a1 a2 a3 a4) ->
        @eq out o oo -> P S C a1 a2 a3 a4 oo) ->
       (red_expr S C (spec_call_array_proto_push_4_nonempty_1 a1 a2 a3 a4) oo ->
        forall (S0 : state) (C0 : execution_ctx) (l : object_loc) 
          (v : value) (vs : list value) (lenuint32 : Z) 
          (o o1 : out),
        red_expr S C
          (spec_to_string (value_prim (prim_number (JsNumber.of_int a3)))) o1 ->
        red_expr S C (spec_call_array_proto_push_4_nonempty_2 a1 a2 a3 a4 o1)
          oo ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq object_loc l a1 ->
        @eq (list value) vs a2 ->
        @eq Z lenuint32 a3 ->
        @eq value v a4 -> @eq out o oo -> P S C a1 a2 a3 a4 oo) ->
       red_expr S C (spec_call_array_proto_push_4_nonempty_1 a1 a2 a3 a4) oo ->
       P S C a1 a2 a3 a4 oo.

Parameter inv_red_expr_spec_call_array_proto_push_4_nonempty_2
     : forall (S : state) (C : execution_ctx) (a1 : object_loc)
         (a2 : list value) (a3 : Z) (a4 : value) (a5 oo : out)
         (P : state ->
              execution_ctx ->
              object_loc -> list value -> Z -> value -> out -> out -> Prop),
       (red_expr S C (spec_call_array_proto_push_4_nonempty_2 a1 a2 a3 a4 a5)
          oo ->
        forall (S0 : state) (C0 : execution_ctx) (exte : ext_expr) (o : out),
        @eq (option out)
          (out_of_ext_expr
             (spec_call_array_proto_push_4_nonempty_2 a1 a2 a3 a4 a5))
          (@Some out oo) ->
        abort oo ->
        not
          (abort_intercepted_expr
             (spec_call_array_proto_push_4_nonempty_2 a1 a2 a3 a4 a5)) ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq ext_expr exte
          (spec_call_array_proto_push_4_nonempty_2 a1 a2 a3 a4 a5) ->
        @eq out o oo -> P S C a1 a2 a3 a4 a5 oo) ->
       (red_expr S C (spec_call_array_proto_push_4_nonempty_2 a1 a2 a3 a4 a5)
          oo ->
        forall (S0 S1 : state) (C0 : execution_ctx) 
          (l : object_loc) (vindx : prop_name) (v : value) 
          (vs : list value) (lenuint32 : Z) (o o1 : out),
        red_expr S1 C (spec_object_put a1 vindx a4 throw_true) o1 ->
        red_expr S1 C
          (spec_call_array_proto_push_4_nonempty_3 a1 a2 a3 a4 o1) oo ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq object_loc l a1 ->
        @eq (list value) vs a2 ->
        @eq Z lenuint32 a3 ->
        @eq value v a4 ->
        @eq out (out_ter S1 (res_val (value_prim (prim_string vindx)))) a5 ->
        @eq out o oo ->
        P S C a1 a2 a3 a4
          (out_ter S1 (res_val (value_prim (prim_string vindx)))) oo) ->
       red_expr S C (spec_call_array_proto_push_4_nonempty_2 a1 a2 a3 a4 a5)
         oo -> P S C a1 a2 a3 a4 a5 oo.

Parameter inv_red_expr_spec_call_array_proto_push_4_nonempty_3
     : forall (S : state) (C : execution_ctx) (a1 : object_loc)
         (a2 : list value) (a3 : Z) (a4 : value) (a5 oo : out)
         (P : state ->
              execution_ctx ->
              object_loc -> list value -> Z -> value -> out -> out -> Prop),
       (red_expr S C (spec_call_array_proto_push_4_nonempty_3 a1 a2 a3 a4 a5)
          oo ->
        forall (S0 : state) (C0 : execution_ctx) (exte : ext_expr) (o : out),
        @eq (option out)
          (out_of_ext_expr
             (spec_call_array_proto_push_4_nonempty_3 a1 a2 a3 a4 a5))
          (@Some out oo) ->
        abort oo ->
        not
          (abort_intercepted_expr
             (spec_call_array_proto_push_4_nonempty_3 a1 a2 a3 a4 a5)) ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq ext_expr exte
          (spec_call_array_proto_push_4_nonempty_3 a1 a2 a3 a4 a5) ->
        @eq out o oo -> P S C a1 a2 a3 a4 a5 oo) ->
       (red_expr S C (spec_call_array_proto_push_4_nonempty_3 a1 a2 a3 a4 a5)
          oo ->
        forall (S0 S1 : state) (C0 : execution_ctx) 
          (l : object_loc) (v : value) (vs : list value) 
          (lenuint32 : Z) (o : out) (R : res),
        red_expr S1 C
          (spec_call_array_proto_push_4 a1 a2 (Z.add a3 (Zpos xH))) oo ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq object_loc l a1 ->
        @eq (list value) vs a2 ->
        @eq Z lenuint32 a3 ->
        @eq value v a4 ->
        @eq out (out_ter S1 R) a5 ->
        @eq out o oo -> P S C a1 a2 a3 a4 (out_ter S1 R) oo) ->
       red_expr S C (spec_call_array_proto_push_4_nonempty_3 a1 a2 a3 a4 a5)
         oo -> P S C a1 a2 a3 a4 a5 oo.

Parameter inv_red_expr_spec_call_array_proto_push_5
     : forall (S : state) (C : execution_ctx) (a1 : object_loc) 
         (a2 : value) (oo : out)
         (P : state -> execution_ctx -> object_loc -> value -> out -> Prop),
       (red_expr S C (spec_call_array_proto_push_5 a1 a2) oo ->
        forall (S0 : state) (C0 : execution_ctx) (exte : ext_expr) (o : out),
        @eq (option out)
          (out_of_ext_expr (spec_call_array_proto_push_5 a1 a2))
          (@Some out oo) ->
        abort oo ->
        not (abort_intercepted_expr (spec_call_array_proto_push_5 a1 a2)) ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq ext_expr exte (spec_call_array_proto_push_5 a1 a2) ->
        @eq out o oo -> P S C a1 a2 oo) ->
       (red_expr S C (spec_call_array_proto_push_5 a1 a2) oo ->
        forall (S0 : state) (C0 : execution_ctx) (l : object_loc)
          (vlen : value) (o o1 : out),
        red_expr S C
          (spec_object_put a1
             (String (Ascii false false true true false true true false)
                (String (Ascii true false true false false true true false)
                   (String (Ascii false true true true false true true false)
                      (String
                         (Ascii true true true false false true true false)
                         (String
                            (Ascii false false true false true true true
                               false)
                            (String
                               (Ascii false false false true false true true
                                  false) EmptyString)))))) a2 throw_true) o1 ->
        red_expr S C (spec_call_array_proto_push_6 a2 o1) oo ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq object_loc l a1 ->
        @eq value vlen a2 -> @eq out o oo -> P S C a1 a2 oo) ->
       red_expr S C (spec_call_array_proto_push_5 a1 a2) oo -> P S C a1 a2 oo.

Parameter inv_red_expr_spec_call_array_proto_push_6
     : forall (S : state) (C : execution_ctx) (a1 : value) 
         (a2 oo : out)
         (P : state -> execution_ctx -> value -> out -> out -> Prop),
       (red_expr S C (spec_call_array_proto_push_6 a1 a2) oo ->
        forall (S0 : state) (C0 : execution_ctx) (exte : ext_expr) (o : out),
        @eq (option out)
          (out_of_ext_expr (spec_call_array_proto_push_6 a1 a2))
          (@Some out oo) ->
        abort oo ->
        not (abort_intercepted_expr (spec_call_array_proto_push_6 a1 a2)) ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq ext_expr exte (spec_call_array_proto_push_6 a1 a2) ->
        @eq out o oo -> P S C a1 a2 oo) ->
       (red_expr S C (spec_call_array_proto_push_6 a1 a2) oo ->
        forall (S0 S1 : state) (C0 : execution_ctx) (vlen : value) (R : res),
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq value vlen a1 ->
        @eq out (out_ter S1 R) a2 ->
        @eq out (out_ter S1 (res_val a1)) oo ->
        P S C a1 (out_ter S1 R) (out_ter S1 (res_val a1))) ->
       red_expr S C (spec_call_array_proto_push_6 a1 a2) oo -> P S C a1 a2 oo.

Parameter inv_red_expr_spec_call_string_non_empty
     : forall (S : state) (C : execution_ctx) (a1 oo : out)
         (P : state -> execution_ctx -> out -> out -> Prop),
       (red_expr S C (spec_call_string_non_empty a1) oo ->
        forall (S0 : state) (C0 : execution_ctx) (exte : ext_expr) (o : out),
        @eq (option out) (out_of_ext_expr (spec_call_string_non_empty a1))
          (@Some out oo) ->
        abort oo ->
        not (abort_intercepted_expr (spec_call_string_non_empty a1)) ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq ext_expr exte (spec_call_string_non_empty a1) ->
        @eq out o oo -> P S C a1 oo) ->
       (red_expr S C (spec_call_string_non_empty a1) oo ->
        forall (S0 S' : state) (C0 : execution_ctx) (s : string),
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq out (out_ter S' (res_val (value_prim (prim_string s)))) a1 ->
        @eq out (out_ter S' (res_val (value_prim (prim_string s)))) oo ->
        P S C (out_ter S' (res_val (value_prim (prim_string s))))
          (out_ter S' (res_val (value_prim (prim_string s))))) ->
       red_expr S C (spec_call_string_non_empty a1) oo -> P S C a1 oo.

Parameter inv_red_expr_spec_construct_string_1
     : forall (S : state) (C : execution_ctx) (a1 : value) 
         (oo : out) (P : state -> execution_ctx -> value -> out -> Prop),
       (red_expr S C (spec_construct_string_1 a1) oo ->
        forall (S0 : state) (C0 : execution_ctx) (exte : ext_expr) (o : out),
        @eq (option out) (out_of_ext_expr (spec_construct_string_1 a1))
          (@Some out oo) ->
        abort oo ->
        not (abort_intercepted_expr (spec_construct_string_1 a1)) ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq ext_expr exte (spec_construct_string_1 a1) ->
        @eq out o oo -> P S C a1 oo) ->
       (red_expr S C (spec_construct_string_1 a1) oo ->
        forall (S0 : state) (C0 : execution_ctx) (v : value) (o' o : out),
        red_expr S C (spec_to_string a1) o' ->
        red_expr S C (spec_construct_string_2 o') oo ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq value v a1 -> @eq out o oo -> P S C a1 oo) ->
       red_expr S C (spec_construct_string_1 a1) oo -> P S C a1 oo.

Parameter inv_red_expr_spec_construct_string_2
     : forall (S : state) (C : execution_ctx) (a1 oo : out)
         (P : state -> execution_ctx -> out -> out -> Prop),
       (red_expr S C (spec_construct_string_2 a1) oo ->
        forall (S0 : state) (C0 : execution_ctx) (exte : ext_expr) (o : out),
        @eq (option out) (out_of_ext_expr (spec_construct_string_2 a1))
          (@Some out oo) ->
        abort oo ->
        not (abort_intercepted_expr (spec_construct_string_2 a1)) ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq ext_expr exte (spec_construct_string_2 a1) ->
        @eq out o oo -> P S C a1 oo) ->
       (red_expr S C (spec_construct_string_2 a1) oo ->
        forall (S0 S1 S' S'' : state) (C0 : execution_ctx) 
          (l : object_loc) (s : string) (O : object),
        @eq value (object_proto_ O)
          (value_object (object_loc_prealloc prealloc_string_proto)) ->
        @eq class_name (object_class_ O)
          (String (Ascii true true false false true false true false)
             (String (Ascii false false true false true true true false)
                (String (Ascii false true false false true true true false)
                   (String
                      (Ascii true false false true false true true false)
                      (String
                         (Ascii false true true true false true true false)
                         (String
                            (Ascii true true true false false true true false)
                            EmptyString)))))) ->
        @eq bool (object_extensible_ O) true ->
        @eq (option value) (object_prim_value_ O)
          (@Some value (value_prim (prim_string s))) ->
        @eq builtin_get_own_prop (object_get_own_prop_ O)
          builtin_get_own_prop_string ->
        @eq (prod object_loc state) (@pair object_loc state l S')
          (object_alloc S1 O) ->
        object_set_property S' l
          (String (Ascii false false true true false true true false)
             (String (Ascii true false true false false true true false)
                (String (Ascii false true true true false true true false)
                   (String (Ascii true true true false false true true false)
                      (String
                         (Ascii false false true false true true true false)
                         (String
                            (Ascii false false false true false true true
                               false) EmptyString))))))
          (attributes_data_of
             (attributes_data_intro_constant
                (value_prim
                   (prim_number
                      (JsNumber.of_int (my_Z_of_nat (String.length s)))))))
          S'' ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq out (out_ter S1 (res_val (value_prim (prim_string s)))) a1 ->
        @eq out (out_ter S'' (res_val (value_object l))) oo ->
        P S C (out_ter S1 (res_val (value_prim (prim_string s))))
          (out_ter S'' (res_val (value_object l)))) ->
       red_expr S C (spec_construct_string_2 a1) oo -> P S C a1 oo.

Parameter inv_red_expr_spec_call_bool_proto_to_string_1
     : forall (S : state) (C : execution_ctx) (a1 oo : out)
         (P : state -> execution_ctx -> out -> out -> Prop),
       (red_expr S C (spec_call_bool_proto_to_string_1 a1) oo ->
        forall (S0 : state) (C0 : execution_ctx) (exte : ext_expr) (o : out),
        @eq (option out)
          (out_of_ext_expr (spec_call_bool_proto_to_string_1 a1))
          (@Some out oo) ->
        abort oo ->
        not (abort_intercepted_expr (spec_call_bool_proto_to_string_1 a1)) ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq ext_expr exte (spec_call_bool_proto_to_string_1 a1) ->
        @eq out o oo -> P S C a1 oo) ->
       red_expr S C (spec_call_bool_proto_to_string_1 a1) oo -> P S C a1 oo.

Parameter inv_red_expr_spec_call_bool_proto_value_of_1
     : forall (S : state) (C : execution_ctx) (a1 : value) 
         (oo : out) (P : state -> execution_ctx -> value -> out -> Prop),
       (red_expr S C (spec_call_bool_proto_value_of_1 a1) oo ->
        forall (S0 : state) (C0 : execution_ctx) (exte : ext_expr) (o : out),
        @eq (option out)
          (out_of_ext_expr (spec_call_bool_proto_value_of_1 a1))
          (@Some out oo) ->
        abort oo ->
        not (abort_intercepted_expr (spec_call_bool_proto_value_of_1 a1)) ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq ext_expr exte (spec_call_bool_proto_value_of_1 a1) ->
        @eq out o oo -> P S C a1 oo) ->
       red_expr S C (spec_call_bool_proto_value_of_1 a1) oo -> P S C a1 oo.

Parameter inv_red_expr_spec_call_bool_proto_value_of_2
     : forall (S : state) (C : execution_ctx) (a1 : value) 
         (oo : out) (P : state -> execution_ctx -> value -> out -> Prop),
       (red_expr S C (spec_call_bool_proto_value_of_2 a1) oo ->
        forall (S0 : state) (C0 : execution_ctx) (exte : ext_expr) (o : out),
        @eq (option out)
          (out_of_ext_expr (spec_call_bool_proto_value_of_2 a1))
          (@Some out oo) ->
        abort oo ->
        not (abort_intercepted_expr (spec_call_bool_proto_value_of_2 a1)) ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq ext_expr exte (spec_call_bool_proto_value_of_2 a1) ->
        @eq out o oo -> P S C a1 oo) ->
       red_expr S C (spec_call_bool_proto_value_of_2 a1) oo -> P S C a1 oo.

Parameter inv_red_expr_spec_call_number_proto_to_string_1
     : forall (S : state) (C : execution_ctx) (a1 : value) 
         (a2 : list value) (oo : out)
         (P : state -> execution_ctx -> value -> list value -> out -> Prop),
       (red_expr S C (spec_call_number_proto_to_string_1 a1 a2) oo ->
        forall (S0 : state) (C0 : execution_ctx) (exte : ext_expr) (o : out),
        @eq (option out)
          (out_of_ext_expr (spec_call_number_proto_to_string_1 a1 a2))
          (@Some out oo) ->
        abort oo ->
        not
          (abort_intercepted_expr (spec_call_number_proto_to_string_1 a1 a2)) ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq ext_expr exte (spec_call_number_proto_to_string_1 a1 a2) ->
        @eq out o oo -> P S C a1 a2 oo) ->
       red_expr S C (spec_call_number_proto_to_string_1 a1 a2) oo ->
       P S C a1 a2 oo.

Parameter inv_red_expr_spec_call_number_proto_to_string_2
     : forall (S : state) (C : execution_ctx) (a1 : value) 
         (a2 oo : out)
         (P : state -> execution_ctx -> value -> out -> out -> Prop),
       (red_expr S C (spec_call_number_proto_to_string_2 a1 a2) oo ->
        forall (S0 : state) (C0 : execution_ctx) (exte : ext_expr) (o : out),
        @eq (option out)
          (out_of_ext_expr (spec_call_number_proto_to_string_2 a1 a2))
          (@Some out oo) ->
        abort oo ->
        not
          (abort_intercepted_expr (spec_call_number_proto_to_string_2 a1 a2)) ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq ext_expr exte (spec_call_number_proto_to_string_2 a1 a2) ->
        @eq out o oo -> P S C a1 a2 oo) ->
       red_expr S C (spec_call_number_proto_to_string_2 a1 a2) oo ->
       P S C a1 a2 oo.

Parameter inv_red_expr_spec_call_number_proto_value_of_1
     : forall (S : state) (C : execution_ctx) (a1 : value) 
         (oo : out) (P : state -> execution_ctx -> value -> out -> Prop),
       (red_expr S C (spec_call_number_proto_value_of_1 a1) oo ->
        forall (S0 : state) (C0 : execution_ctx) (exte : ext_expr) (o : out),
        @eq (option out)
          (out_of_ext_expr (spec_call_number_proto_value_of_1 a1))
          (@Some out oo) ->
        abort oo ->
        not (abort_intercepted_expr (spec_call_number_proto_value_of_1 a1)) ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq ext_expr exte (spec_call_number_proto_value_of_1 a1) ->
        @eq out o oo -> P S C a1 oo) ->
       red_expr S C (spec_call_number_proto_value_of_1 a1) oo -> P S C a1 oo.

Parameter inv_red_expr_spec_call_error_proto_to_string_1
     : forall (S : state) (C : execution_ctx) (a1 : value) 
         (oo : out) (P : state -> execution_ctx -> value -> out -> Prop),
       (red_expr S C (spec_call_error_proto_to_string_1 a1) oo ->
        forall (S0 : state) (C0 : execution_ctx) (exte : ext_expr) (o : out),
        @eq (option out)
          (out_of_ext_expr (spec_call_error_proto_to_string_1 a1))
          (@Some out oo) ->
        abort oo ->
        not (abort_intercepted_expr (spec_call_error_proto_to_string_1 a1)) ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq ext_expr exte (spec_call_error_proto_to_string_1 a1) ->
        @eq out o oo -> P S C a1 oo) ->
       (red_expr S C (spec_call_error_proto_to_string_1 a1) oo ->
        forall (S0 : state) (C0 : execution_ctx) (v : value) (o : out),
        not (@eq type (type_of a1) type_object) ->
        red_expr S C (spec_error native_error_type) oo ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq value v a1 -> @eq out o oo -> P S C a1 oo) ->
       (red_expr S C (spec_call_error_proto_to_string_1 a1) oo ->
        forall (S0 : state) (C0 : execution_ctx) (l : object_loc)
          (o1 o : out),
        red_expr S C
          (spec_object_get l
             (String (Ascii false true true true false true true false)
                (String (Ascii true false false false false true true false)
                   (String (Ascii true false true true false true true false)
                      (String
                         (Ascii true false true false false true true false)
                         EmptyString))))) o1 ->
        red_expr S C (spec_call_error_proto_to_string_2 l o1) oo ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq value (value_object l) a1 ->
        @eq out o oo -> P S C (value_object l) oo) ->
       red_expr S C (spec_call_error_proto_to_string_1 a1) oo -> P S C a1 oo.

Parameter inv_red_expr_spec_call_error_proto_to_string_2
     : forall (S : state) (C : execution_ctx) (a1 : object_loc) 
         (a2 oo : out)
         (P : state -> execution_ctx -> object_loc -> out -> out -> Prop),
       (red_expr S C (spec_call_error_proto_to_string_2 a1 a2) oo ->
        forall (S0 : state) (C0 : execution_ctx) (exte : ext_expr) (o : out),
        @eq (option out)
          (out_of_ext_expr (spec_call_error_proto_to_string_2 a1 a2))
          (@Some out oo) ->
        abort oo ->
        not
          (abort_intercepted_expr (spec_call_error_proto_to_string_2 a1 a2)) ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq ext_expr exte (spec_call_error_proto_to_string_2 a1 a2) ->
        @eq out o oo -> P S C a1 a2 oo) ->
       (red_expr S C (spec_call_error_proto_to_string_2 a1 a2) oo ->
        forall (S0 S1 : state) (C0 : execution_ctx) 
          (l : object_loc) (o : out),
        red_expr S1 C
          (spec_call_error_proto_to_string_3 a1
             (out_ter S1
                (res_val
                   (value_prim
                      (prim_string
                         (String
                            (Ascii true false true false false false true
                               false)
                            (String
                               (Ascii false true false false true true true
                                  false)
                               (String
                                  (Ascii false true false false true true
                                     true false)
                                  (String
                                     (Ascii true true true true false true
                                        true false)
                                     (String
                                        (Ascii false true false false true
                                           true true false) EmptyString))))))))))
          oo ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq object_loc l a1 ->
        @eq out (out_ter S1 (res_val (value_prim prim_undef))) a2 ->
        @eq out o oo ->
        P S C a1 (out_ter S1 (res_val (value_prim prim_undef))) oo) ->
       (red_expr S C (spec_call_error_proto_to_string_2 a1 a2) oo ->
        forall (S0 S1 : state) (C0 : execution_ctx) 
          (l : object_loc) (v : value) (o1 o : out),
        not (@eq value v (value_prim prim_undef)) ->
        red_expr S1 C (spec_to_string v) o1 ->
        red_expr S1 C (spec_call_error_proto_to_string_3 a1 o1) oo ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq object_loc l a1 ->
        @eq out (out_ter S1 (res_val v)) a2 ->
        @eq out o oo -> P S C a1 (out_ter S1 (res_val v)) oo) ->
       red_expr S C (spec_call_error_proto_to_string_2 a1 a2) oo ->
       P S C a1 a2 oo.

Parameter inv_red_expr_spec_call_error_proto_to_string_3
     : forall (S : state) (C : execution_ctx) (a1 : object_loc) 
         (a2 oo : out)
         (P : state -> execution_ctx -> object_loc -> out -> out -> Prop),
       (red_expr S C (spec_call_error_proto_to_string_3 a1 a2) oo ->
        forall (S0 : state) (C0 : execution_ctx) (exte : ext_expr) (o : out),
        @eq (option out)
          (out_of_ext_expr (spec_call_error_proto_to_string_3 a1 a2))
          (@Some out oo) ->
        abort oo ->
        not
          (abort_intercepted_expr (spec_call_error_proto_to_string_3 a1 a2)) ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq ext_expr exte (spec_call_error_proto_to_string_3 a1 a2) ->
        @eq out o oo -> P S C a1 a2 oo) ->
       (red_expr S C (spec_call_error_proto_to_string_3 a1 a2) oo ->
        forall (S0 S1 : state) (C0 : execution_ctx) 
          (l : object_loc) (sname : string) (o1 o : out),
        red_expr S1 C
          (spec_object_get a1
             (String (Ascii true false true true false true true false)
                (String (Ascii true false true false false true true false)
                   (String (Ascii true true false false true true true false)
                      (String
                         (Ascii true true false false true true true false)
                         (String
                            (Ascii true false false false false true true
                               false)
                            (String
                               (Ascii true true true false false true true
                                  false)
                               (String
                                  (Ascii true false true false false true
                                     true false) EmptyString)))))))) o1 ->
        red_expr S1 C (spec_call_error_proto_to_string_4 a1 sname o1) oo ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq object_loc l a1 ->
        @eq out (out_ter S1 (res_val (value_prim (prim_string sname)))) a2 ->
        @eq out o oo ->
        P S C a1 (out_ter S1 (res_val (value_prim (prim_string sname)))) oo) ->
       red_expr S C (spec_call_error_proto_to_string_3 a1 a2) oo ->
       P S C a1 a2 oo.

Parameter inv_red_expr_spec_call_error_proto_to_string_4
     : forall (S : state) (C : execution_ctx) (a1 : object_loc) 
         (a2 : string) (a3 oo : out)
         (P : state ->
              execution_ctx -> object_loc -> string -> out -> out -> Prop),
       (red_expr S C (spec_call_error_proto_to_string_4 a1 a2 a3) oo ->
        forall (S0 : state) (C0 : execution_ctx) (exte : ext_expr) (o : out),
        @eq (option out)
          (out_of_ext_expr (spec_call_error_proto_to_string_4 a1 a2 a3))
          (@Some out oo) ->
        abort oo ->
        not
          (abort_intercepted_expr
             (spec_call_error_proto_to_string_4 a1 a2 a3)) ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq ext_expr exte (spec_call_error_proto_to_string_4 a1 a2 a3) ->
        @eq out o oo -> P S C a1 a2 a3 oo) ->
       (red_expr S C (spec_call_error_proto_to_string_4 a1 a2 a3) oo ->
        forall (S0 S1 : state) (C0 : execution_ctx) 
          (l : object_loc) (sname : string) (o : out),
        red_expr S1 C
          (spec_call_error_proto_to_string_5 a1 a2
             (out_ter S1 (res_val (value_prim (prim_string EmptyString)))))
          oo ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq object_loc l a1 ->
        @eq string sname a2 ->
        @eq out (out_ter S1 (res_val (value_prim prim_undef))) a3 ->
        @eq out o oo ->
        P S C a1 a2 (out_ter S1 (res_val (value_prim prim_undef))) oo) ->
       (red_expr S C (spec_call_error_proto_to_string_4 a1 a2 a3) oo ->
        forall (S0 S1 : state) (C0 : execution_ctx) 
          (l : object_loc) (sname : string) (v : value) 
          (o1 o : out),
        not (@eq value v (value_prim prim_undef)) ->
        red_expr S1 C (spec_to_string v) o1 ->
        red_expr S1 C (spec_call_error_proto_to_string_5 a1 a2 o1) oo ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq object_loc l a1 ->
        @eq string sname a2 ->
        @eq out (out_ter S1 (res_val v)) a3 ->
        @eq out o oo -> P S C a1 a2 (out_ter S1 (res_val v)) oo) ->
       red_expr S C (spec_call_error_proto_to_string_4 a1 a2 a3) oo ->
       P S C a1 a2 a3 oo.

Parameter inv_red_expr_spec_call_error_proto_to_string_5
     : forall (S : state) (C : execution_ctx) (a1 : object_loc) 
         (a2 : string) (a3 oo : out)
         (P : state ->
              execution_ctx -> object_loc -> string -> out -> out -> Prop),
       (red_expr S C (spec_call_error_proto_to_string_5 a1 a2 a3) oo ->
        forall (S0 : state) (C0 : execution_ctx) (exte : ext_expr) (o : out),
        @eq (option out)
          (out_of_ext_expr (spec_call_error_proto_to_string_5 a1 a2 a3))
          (@Some out oo) ->
        abort oo ->
        not
          (abort_intercepted_expr
             (spec_call_error_proto_to_string_5 a1 a2 a3)) ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq ext_expr exte (spec_call_error_proto_to_string_5 a1 a2 a3) ->
        @eq out o oo -> P S C a1 a2 a3 oo) ->
       (red_expr S C (spec_call_error_proto_to_string_5 a1 a2 a3) oo ->
        forall (S0 S1 : state) (C0 : execution_ctx) 
          (l : object_loc) (sname : string) (o : out),
        red_expr S1 C
          (spec_call_error_proto_to_string_6 a1 a2
             (out_ter S1 (res_val (value_prim (prim_string EmptyString)))))
          oo ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq object_loc l a1 ->
        @eq string sname a2 ->
        @eq out (out_ter S1 (res_val (value_prim prim_undef))) a3 ->
        @eq out o oo ->
        P S C a1 a2 (out_ter S1 (res_val (value_prim prim_undef))) oo) ->
       (red_expr S C (spec_call_error_proto_to_string_5 a1 a2 a3) oo ->
        forall (S0 S1 : state) (C0 : execution_ctx) 
          (l : object_loc) (sname : string) (v : value) 
          (o1 o : out),
        not (@eq value v (value_prim prim_undef)) ->
        red_expr S1 C (spec_to_string v) o1 ->
        red_expr S1 C (spec_call_error_proto_to_string_6 a1 a2 o1) oo ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq object_loc l a1 ->
        @eq string sname a2 ->
        @eq out (out_ter S1 (res_val v)) a3 ->
        @eq out o oo -> P S C a1 a2 (out_ter S1 (res_val v)) oo) ->
       red_expr S C (spec_call_error_proto_to_string_5 a1 a2 a3) oo ->
       P S C a1 a2 a3 oo.

Parameter inv_red_expr_spec_call_error_proto_to_string_6
     : forall (S : state) (C : execution_ctx) (a1 : object_loc) 
         (a2 : string) (a3 oo : out)
         (P : state ->
              execution_ctx -> object_loc -> string -> out -> out -> Prop),
       (red_expr S C (spec_call_error_proto_to_string_6 a1 a2 a3) oo ->
        forall (S0 : state) (C0 : execution_ctx) (exte : ext_expr) (o : out),
        @eq (option out)
          (out_of_ext_expr (spec_call_error_proto_to_string_6 a1 a2 a3))
          (@Some out oo) ->
        abort oo ->
        not
          (abort_intercepted_expr
             (spec_call_error_proto_to_string_6 a1 a2 a3)) ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq ext_expr exte (spec_call_error_proto_to_string_6 a1 a2 a3) ->
        @eq out o oo -> P S C a1 a2 a3 oo) ->
       (red_expr S C (spec_call_error_proto_to_string_6 a1 a2 a3) oo ->
        forall (S0 S1 : state) (C0 : execution_ctx) 
          (l : object_loc) (sname smsg s : string),
        @eq string s
          match classicT (@eq string a2 EmptyString) return string with
          | left _ => smsg
          | right _ =>
              match classicT (@eq string smsg EmptyString) return string with
              | left _ => a2
              | right _ =>
                  string_concat
                    (string_concat a2
                       (String
                          (Ascii false true false true true true false false)
                          (String
                             (Ascii false false false false false true false
                                false) EmptyString))) smsg
              end
          end ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq object_loc l a1 ->
        @eq string sname a2 ->
        @eq out (out_ter S1 (res_val (value_prim (prim_string smsg)))) a3 ->
        @eq out (out_ter S1 (res_val (value_prim (prim_string s)))) oo ->
        P S C a1 a2 (out_ter S1 (res_val (value_prim (prim_string smsg))))
          (out_ter S1 (res_val (value_prim (prim_string s))))) ->
       red_expr S C (spec_call_error_proto_to_string_6 a1 a2 a3) oo ->
       P S C a1 a2 a3 oo.

Parameter inv_red_expr_spec_returns
     : forall (S : state) (C : execution_ctx) (a1 oo : out)
         (P : state -> execution_ctx -> out -> out -> Prop),
       (red_expr S C (spec_returns a1) oo ->
        forall (S0 : state) (C0 : execution_ctx) (exte : ext_expr) (o : out),
        @eq (option out) (out_of_ext_expr (spec_returns a1)) (@Some out oo) ->
        abort oo ->
        not (abort_intercepted_expr (spec_returns a1)) ->
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq ext_expr exte (spec_returns a1) -> @eq out o oo -> P S C a1 oo) ->
       (red_expr S C (spec_returns a1) oo ->
        forall (S0 : state) (C0 : execution_ctx) (o : out),
        @eq state S0 S ->
        @eq execution_ctx C0 C ->
        @eq out o a1 -> @eq out a1 oo -> P S C oo oo) ->
       red_expr S C (spec_returns a1) oo -> P S C a1 oo.


(**************************************************************)
(** ** Five renegade inversion schemes                        *)

Parameter inv_red_expr_spec_prim_new_object : 
  forall (S : state) (C : execution_ctx) (a1 : prim) (oo : out)
         (P : state -> execution_ctx -> prim -> out -> Prop),
    (red_expr S C (spec_prim_new_object a1) oo ->
       out_of_ext_expr (spec_prim_new_object a1) = Some oo ->
       abort oo ->
       not (abort_intercepted_expr (spec_prim_new_object a1)) ->
       P S C a1 oo) ->
    (red_expr S C (spec_prim_new_object a1) oo ->
       forall l S' (b : bool),
       let O1 := object_new prealloc_bool_proto "Boolean" in
       let O := object_with_primitive_value O1 b in
       (l, S') = object_alloc S O ->
       a1 = prim_bool b -> oo = out_ter S' l ->
       P S C a1 oo) ->
    (red_expr S C (spec_prim_new_object a1) oo ->
       forall l S' S'' (s : string),
       let O2 := object_new prealloc_string_proto "String" in
       let O1 := object_with_get_own_property O2 builtin_get_own_prop_string in
       let O := object_with_primitive_value O1 s in
       (l, S') = object_alloc S O ->
       object_set_property S' l "length" (attributes_data_intro_constant (JsNumber.of_int (String.length s))) S'' ->
       a1 = prim_string s -> oo = out_ter S'' l ->
       P S C a1 oo) ->
    (red_expr S C (spec_prim_new_object a1) oo ->
       forall l S' (n : number),
       let O1 := object_new prealloc_number_proto "Number" in
       let O := object_with_primitive_value O1 n in
       (l, S') = object_alloc S O ->
       a1 = prim_number n -> oo = out_ter S' l ->
       P S C a1 oo) ->
    red_expr S C (spec_prim_new_object a1) oo -> P S C a1 oo.

Parameter inv_red_expr_spec_construct_bool_1 : 
  forall (S : state) (C : execution_ctx) (a1 : out) (oo : out)
         (P : state -> execution_ctx -> out -> out -> Prop),
    (red_expr S C (spec_construct_bool_1 a1) oo ->
       out_of_ext_expr (spec_construct_bool_1 a1) = Some oo ->
       abort oo ->
       not (abort_intercepted_expr (spec_construct_bool_1 a1)) ->
       P S C a1 oo) ->
    (red_expr S C (spec_construct_bool_1 a1) oo ->
       forall (b : bool) l S' S'',
       let O1 := object_new prealloc_bool_proto "Boolean" in
       let O := object_with_primitive_value O1 b in
       (l, S'') = object_alloc S' O ->
       a1 = out_ter S' b -> oo = out_ter S'' l ->
       P S C a1 oo) ->
    red_expr S C (spec_construct_bool_1 a1) oo -> P S C a1 oo.

Parameter inv_red_expr_spec_construct_number_1 : 
  forall (S : state) (C : execution_ctx) (a1 : out) (oo : out)
         (P : state -> execution_ctx -> out -> out -> Prop),
    (red_expr S C (spec_construct_number_1 a1) oo ->
       out_of_ext_expr (spec_construct_number_1 a1) = Some oo ->
       abort oo ->
       not (abort_intercepted_expr (spec_construct_number_1 a1)) ->
       P S C a1 oo) ->
    (red_expr S C (spec_construct_number_1 a1) oo ->
       forall (v : value) l S' S'',
       let O1 := object_new prealloc_number_proto "Number" in
       let O := object_with_primitive_value O1 v in
       (l, S'') = object_alloc S' O ->
       a1 = out_ter S' v -> oo = out_ter S'' l ->
       P S C a1 oo) ->
    red_expr S C (spec_construct_number_1 a1) oo -> P S C a1 oo.

Parameter inv_red_expr_spec_creating_function_object_proto_1 : 
  forall (S : state) (C : execution_ctx) (a1 : object_loc) (a2 : out) (oo : out)
         (P : state -> execution_ctx -> object_loc -> out -> out -> Prop),
    (red_expr S C (spec_creating_function_object_proto_1 a1 a2) oo ->
       out_of_ext_expr (spec_creating_function_object_proto_1 a1 a2) = Some oo ->
       abort oo ->
       not (abort_intercepted_expr (spec_creating_function_object_proto_1 a1 a2)) ->
       P S C a1 a2 oo) ->
    (red_expr S C (spec_creating_function_object_proto_1 a1 a2) oo ->
       forall S' l o o1 lproto,
       let A := attributes_data_intro (value_object l) true false true in
       red_expr S' C (spec_object_define_own_prop lproto "constructor" A false) o1 ->
       red_expr S' C (spec_creating_function_object_proto_2 l lproto o1) o ->
       a2 = out_ter S' lproto -> oo = o ->
       P S C a1 a2 oo) ->
    red_expr S C (spec_creating_function_object_proto_1 a1 a2) oo -> P S C a1 a2 oo.

Parameter inv_red_expr_spec_creating_function_object_proto_2 : 
  forall (S : state) (C : execution_ctx) (a1 : object_loc) (a2 : object_loc) (a3 : out) (oo : out)
         (P : state -> execution_ctx -> object_loc -> object_loc -> out -> out -> Prop),
    (red_expr S C (spec_creating_function_object_proto_2 a1 a2 a3) oo ->
       out_of_ext_expr (spec_creating_function_object_proto_2 a1 a2 a3) = Some oo ->
       abort oo ->
       not (abort_intercepted_expr (spec_creating_function_object_proto_2 a1 a2 a3)) ->
       P S C a1 a2 a3 oo) ->
    (red_expr S C (spec_creating_function_object_proto_2 a1 a2 a3) oo ->
       forall S' l o (b : bool) lproto,
       let A := attributes_data_intro (value_object a2) true false false in
       red_expr S' C (spec_object_define_own_prop l "prototype" A false) o ->
       a2 = lproto -> a3 = out_ter S' b -> oo = o ->
       P S C a1 a2 a3 oo) ->
    red_expr S C (spec_creating_function_object_proto_2 a1 a2 a3) oo -> P S C a1 a2 a3 oo.

Parameter inv_red_expr_spec_call_prealloc
     : forall (S : state) (C : execution_ctx) (a1 : prealloc) (a2 : value) (a3 : list value) (oo : out) (P : state -> execution_ctx -> prealloc -> value -> list value -> out -> Prop),
       (red_expr S C (spec_call_prealloc a1 a2 a3) oo -> forall (S0 : state) (C0 : execution_ctx) (exte : ext_expr) (o : out), @eq (option out) (out_of_ext_expr (spec_call_prealloc a1 a2 a3)) (@Some out oo) -> abort oo -> not (abort_intercepted_expr (spec_call_prealloc a1 a2 a3)) -> @eq state S0 S -> @eq execution_ctx C0 C -> @eq ext_expr exte (spec_call_prealloc a1 a2 a3) -> @eq out o oo -> P S C a1 a2 a3 oo) ->
       (red_expr S C (spec_call_prealloc a1 a2 a3) oo -> forall (S0 : state) (C0 : execution_ctx) (o : out) (vthis : value) (args : list value), red_expr S C (spec_error native_error_type) oo -> @eq state S0 S -> @eq execution_ctx C0 C -> @eq prealloc prealloc_throw_type_error a1 -> @eq value vthis a2 -> @eq (list value) args a3 -> @eq out o oo -> P S C prealloc_throw_type_error a2 a3 oo) ->
       (red_expr S C (spec_call_prealloc a1 a2 a3) oo -> forall (S0 : state) (C0 : execution_ctx) (v : value) (o o1 : out) (vthis : value) (args : list value), arguments_from a3 (@cons value v (@nil value)) -> red_expr S C (spec_to_number v) o1 -> red_expr S C (spec_call_global_is_nan_1 o1) oo -> @eq state S0 S -> @eq execution_ctx C0 C -> @eq prealloc prealloc_global_is_nan a1 -> @eq value vthis a2 -> @eq (list value) args a3 -> @eq out o oo -> P S C prealloc_global_is_nan a2 a3 oo) ->
       (red_expr S C (spec_call_prealloc a1 a2 a3) oo -> forall (S0 : state) (C0 : execution_ctx) (v : value) (o o1 : out) (vthis : value) (args : list value), arguments_from a3 (@cons value v (@nil value)) -> red_expr S C (spec_to_number v) o1 -> red_expr S C (spec_call_global_is_finite_1 o1) oo -> @eq state S0 S -> @eq execution_ctx C0 C -> @eq prealloc prealloc_global_is_finite a1 -> @eq value vthis a2 -> @eq (list value) args a3 -> @eq out o oo -> P S C prealloc_global_is_finite a2 a3 oo) ->
       (red_expr S C (spec_call_prealloc a1 a2 a3) oo -> forall (S0 : state) (C0 : execution_ctx) (vthis : value) (args : list value) (v : value) (o : out), arguments_from a3 (@cons value v (@nil value)) -> red_expr S C (spec_call_object_call_1 v a3) oo -> @eq state S0 S -> @eq execution_ctx C0 C -> @eq prealloc prealloc_object a1 -> @eq value vthis a2 -> @eq (list value) args a3 -> @eq out o oo -> P S C prealloc_object a2 a3 oo) ->
       (red_expr S C (spec_call_prealloc a1 a2 a3) oo -> forall (S0 : state) (C0 : execution_ctx) (v vthis : value) (args : list value) (o : out), arguments_from a3 (@cons value v (@nil value)) -> red_expr S C (spec_call_object_get_proto_of_1 v) oo -> @eq state S0 S -> @eq execution_ctx C0 C -> @eq prealloc prealloc_object_get_proto_of a1 -> @eq value vthis a2 -> @eq (list value) args a3 -> @eq out o oo -> P S C prealloc_object_get_proto_of a2 a3 oo) ->
       (red_expr S C (spec_call_prealloc a1 a2 a3) oo -> forall (S0 : state) (C0 : execution_ctx) (vo vx : value) (o : out) (vthis : value) (args : list value), arguments_from a3 (@cons value vo (@cons value vx (@nil value))) -> red_expr S C (spec_call_object_get_own_prop_descriptor_1 vo vx) oo -> @eq state S0 S -> @eq execution_ctx C0 C -> @eq prealloc prealloc_object_get_own_prop_descriptor a1 -> @eq value vthis a2 -> @eq (list value) args a3 -> @eq out o oo -> P S C prealloc_object_get_own_prop_descriptor a2 a3 oo) ->
       (red_expr S C (spec_call_prealloc a1 a2 a3) oo -> forall (S0 : state) (C0 : execution_ctx) (vo vp vthis : value) (args : list value) (o : out), arguments_from a3 (@cons value vo (@cons value vp (@nil value))) -> red_expr S C (spec_call_object_create_1 vo vp) oo -> @eq state S0 S -> @eq execution_ctx C0 C -> @eq prealloc prealloc_object_create a1 -> @eq value vthis a2 -> @eq (list value) args a3 -> @eq out o oo -> P S C prealloc_object_create a2 a3 oo) ->
       (red_expr S C (spec_call_prealloc a1 a2 a3) oo -> forall (S0 : state) (C0 : execution_ctx) (vo vx va : value) (o : out) (vthis : value) (args : list value), arguments_from a3 (@cons value vo (@cons value vx (@cons value va (@nil value)))) -> red_expr S C (spec_call_object_define_prop_1 vo vx va) oo -> @eq state S0 S -> @eq execution_ctx C0 C -> @eq prealloc prealloc_object_define_prop a1 -> @eq value vthis a2 -> @eq (list value) args a3 -> @eq out o oo -> P S C prealloc_object_define_prop a2 a3 oo) ->
       (red_expr S C (spec_call_prealloc a1 a2 a3) oo -> forall (S0 : state) (C0 : execution_ctx) (vo vp : value) (o : out) (vthis : value) (args : list value), arguments_from a3 (@cons value vo (@cons value vp (@nil value))) -> red_expr S C (spec_call_object_define_props_1 vo vp) oo -> @eq state S0 S -> @eq execution_ctx C0 C -> @eq prealloc prealloc_object_define_props a1 -> @eq value vthis a2 -> @eq (list value) args a3 -> @eq out o oo -> P S C prealloc_object_define_props a2 a3 oo) ->
       (red_expr S C (spec_call_prealloc a1 a2 a3) oo -> forall (S0 : state) (C0 : execution_ctx) (v : value) (o : out) (vthis : value) (args : list value), arguments_from a3 (@cons value v (@nil value)) -> red_expr S C (spec_call_object_seal_1 v) oo -> @eq state S0 S -> @eq execution_ctx C0 C -> @eq prealloc prealloc_object_seal a1 -> @eq value vthis a2 -> @eq (list value) args a3 -> @eq out o oo -> P S C prealloc_object_seal a2 a3 oo) ->
       (red_expr S C (spec_call_prealloc a1 a2 a3) oo -> forall (S0 : state) (C0 : execution_ctx) (v : value) (o : out) (vthis : value) (args : list value), arguments_from a3 (@cons value v (@nil value)) -> red_expr S C (spec_call_object_freeze_1 v) oo -> @eq state S0 S -> @eq execution_ctx C0 C -> @eq prealloc prealloc_object_freeze a1 -> @eq value vthis a2 -> @eq (list value) args a3 -> @eq out o oo -> P S C prealloc_object_freeze a2 a3 oo) ->
       (red_expr S C (spec_call_prealloc a1 a2 a3) oo -> forall (S0 : state) (C0 : execution_ctx) (v : value) (o : out) (vthis : value) (args : list value), arguments_from a3 (@cons value v (@nil value)) -> red_expr S C (spec_call_object_prevent_extensions_1 v) oo -> @eq state S0 S -> @eq execution_ctx C0 C -> @eq prealloc prealloc_object_prevent_extensions a1 -> @eq value vthis a2 -> @eq (list value) args a3 -> @eq out o oo -> P S C prealloc_object_prevent_extensions a2 a3 oo) ->
       (red_expr S C (spec_call_prealloc a1 a2 a3) oo -> forall (S0 : state) (C0 : execution_ctx) (v : value) (o : out) (vthis : value) (args : list value), arguments_from a3 (@cons value v (@nil value)) -> red_expr S C (spec_call_object_is_sealed_1 v) oo -> @eq state S0 S -> @eq execution_ctx C0 C -> @eq prealloc prealloc_object_is_sealed a1 -> @eq value vthis a2 -> @eq (list value) args a3 -> @eq out o oo -> P S C prealloc_object_is_sealed a2 a3 oo) ->
       (red_expr S C (spec_call_prealloc a1 a2 a3) oo -> forall (S0 : state) (C0 : execution_ctx) (v : value) (o : out) (vthis : value) (args : list value), arguments_from a3 (@cons value v (@nil value)) -> red_expr S C (spec_call_object_is_frozen_1 v) oo -> @eq state S0 S -> @eq execution_ctx C0 C -> @eq prealloc prealloc_object_is_frozen a1 -> @eq value vthis a2 -> @eq (list value) args a3 -> @eq out o oo -> P S C prealloc_object_is_frozen a2 a3 oo) ->
       (red_expr S C (spec_call_prealloc a1 a2 a3) oo -> forall (S0 : state) (C0 : execution_ctx) (v : value) (o : out) (vthis : value) (args : list value), arguments_from a3 (@cons value v (@nil value)) -> red_expr S C (spec_call_object_is_extensible_1 v) oo -> @eq state S0 S -> @eq execution_ctx C0 C -> @eq prealloc prealloc_object_is_extensible a1 -> @eq value vthis a2 -> @eq (list value) args a3 -> @eq out o oo -> P S C prealloc_object_is_extensible a2 a3 oo) ->
       (red_expr S C (spec_call_prealloc a1 a2 a3) oo -> forall (S0 : state) (C0 : execution_ctx) (vthis : value) (args : list value) (o : out), red_expr S C (spec_call_object_proto_to_string_1 a2) oo -> @eq state S0 S -> @eq execution_ctx C0 C -> @eq prealloc prealloc_object_proto_to_string a1 -> @eq value vthis a2 -> @eq (list value) args a3 -> @eq out o oo -> P S C prealloc_object_proto_to_string a2 a3 oo) ->
       (red_expr S C (spec_call_prealloc a1 a2 a3) oo -> forall (S0 : state) (C0 : execution_ctx) (vthis : value) (args : list value) (o : out), red_expr S C (spec_to_object a2) oo -> @eq state S0 S -> @eq execution_ctx C0 C -> @eq prealloc prealloc_object_proto_value_of a1 -> @eq value vthis a2 -> @eq (list value) args a3 -> @eq out o oo -> P S C prealloc_object_proto_value_of a2 a3 oo) ->
       (red_expr S C (spec_call_prealloc a1 a2 a3) oo -> forall (S0 : state) (C0 : execution_ctx) (v vthis : value) (args : list value) (o o1 : out), arguments_from a3 (@cons value v (@nil value)) -> red_expr S C (spec_to_string v) o1 -> red_expr S C (spec_call_object_proto_has_own_prop_1 o1 a2) oo -> @eq state S0 S -> @eq execution_ctx C0 C -> @eq prealloc prealloc_object_proto_has_own_prop a1 -> @eq value vthis a2 -> @eq (list value) args a3 -> @eq out o oo -> P S C prealloc_object_proto_has_own_prop a2 a3 oo) ->
       (red_expr S C (spec_call_prealloc a1 a2 a3) oo -> forall (S0 : state) (C0 : execution_ctx) (vthis : value) (args : list value) (v : value) (o : out), arguments_from a3 (@cons value v (@nil value)) -> red_expr S C (spec_call_object_proto_is_prototype_of_2_1 v a2) oo -> @eq state S0 S -> @eq execution_ctx C0 C -> @eq prealloc prealloc_object_proto_is_prototype_of a1 -> @eq value vthis a2 -> @eq (list value) args a3 -> @eq out o oo -> P S C prealloc_object_proto_is_prototype_of a2 a3 oo) ->
       (red_expr S C (spec_call_prealloc a1 a2 a3) oo -> forall (S0 : state) (C0 : execution_ctx) (v : value) (o : out) (vthis : value) (args : list value), arguments_from a3 (@cons value v (@nil value)) -> red_expr S C (spec_call_object_proto_prop_is_enumerable_1 v a2) oo -> @eq state S0 S -> @eq execution_ctx C0 C -> @eq prealloc prealloc_object_proto_prop_is_enumerable a1 -> @eq value vthis a2 -> @eq (list value) args a3 -> @eq out o oo -> P S C prealloc_object_proto_prop_is_enumerable a2 a3 oo) ->
       (red_expr S C (spec_call_prealloc a1 a2 a3) oo -> forall (S0 : state) (C0 : execution_ctx) (vthis : value) (args : list value), @eq state S0 S -> @eq execution_ctx C0 C -> @eq prealloc prealloc_function_proto a1 -> @eq value vthis a2 -> @eq (list value) args a3 -> @eq out (out_ter S (res_val (value_prim prim_undef))) oo -> P S C prealloc_function_proto a2 a3 (out_ter S (res_val (value_prim prim_undef)))) ->
       (red_expr S C (spec_call_prealloc a1 a2 a3) oo -> forall (S0 : state) (C0 : execution_ctx) (o : out) (vthis : value) (args : list value), not (is_callable S a2) -> red_expr S C (spec_error native_error_type) oo -> @eq state S0 S -> @eq execution_ctx C0 C -> @eq prealloc prealloc_function_proto_call a1 -> @eq value vthis a2 -> @eq (list value) args a3 -> @eq out o oo -> P S C prealloc_function_proto_call a2 a3 oo) ->
       (red_expr S C (spec_call_prealloc a1 a2 a3) oo -> forall (S0 : state) (C0 : execution_ctx) (o : out) (this : object_loc) (vthis : value) (args : list value) (thisArg : value) (arguments : list value), @eq value a2 (value_object this) -> is_callable S (value_object this) -> arguments_first_and_rest a3 (@pair value (list value) thisArg arguments) -> red_expr S C (spec_call this thisArg arguments) oo -> @eq state S0 S -> @eq execution_ctx C0 C -> @eq prealloc prealloc_function_proto_call a1 -> @eq value vthis a2 -> @eq (list value) args a3 -> @eq out o oo -> P S C prealloc_function_proto_call a2 a3 oo) ->
       (red_expr S C (spec_call_prealloc a1 a2 a3) oo -> forall (S0 : state) (C0 : execution_ctx) (vthis : value) (args : list value) (o : out), not (is_callable S a2) -> red_expr S C (spec_error native_error_type) oo -> @eq state S0 S -> @eq execution_ctx C0 C -> @eq prealloc prealloc_function_proto_to_string a1 -> @eq value vthis a2 -> @eq (list value) args a3 -> @eq out o oo -> P S C prealloc_function_proto_to_string a2 a3 oo) ->
       (red_expr S C (spec_call_prealloc a1 a2 a3) oo -> forall (S0 : state) (C0 : execution_ctx) (vthis : value) (o : out) (args : list value), not (is_callable S a2) -> red_expr S C (spec_error native_error_type) oo -> @eq state S0 S -> @eq execution_ctx C0 C -> @eq prealloc prealloc_function_proto_apply a1 -> @eq value vthis a2 -> @eq (list value) args a3 -> @eq out o oo -> P S C prealloc_function_proto_apply a2 a3 oo) ->
       (red_expr S C (spec_call_prealloc a1 a2 a3) oo -> forall (S0 : state) (C0 : execution_ctx) (vthis : value) (o : out) (func : object_loc) (args : list value) (thisArg argArray : value), is_callable S a2 -> @eq value a2 (value_object func) -> arguments_from a3 (@cons value thisArg (@cons value argArray (@nil value))) -> red_expr S C (spec_function_proto_apply func thisArg argArray) oo -> @eq state S0 S -> @eq execution_ctx C0 C -> @eq prealloc prealloc_function_proto_apply a1 -> @eq value vthis a2 -> @eq (list value) args a3 -> @eq out o oo -> P S C prealloc_function_proto_apply a2 a3 oo) ->
       (red_expr S C (spec_call_prealloc a1 a2 a3) oo -> forall (S0 : state) (C0 : execution_ctx) (vthis : value) (o : out) (args : list value), not (is_callable S a2) -> red_expr S C (spec_error native_error_type) oo -> @eq state S0 S -> @eq execution_ctx C0 C -> @eq prealloc prealloc_function_proto_bind a1 -> @eq value vthis a2 -> @eq (list value) args a3 -> @eq out o oo -> P S C prealloc_function_proto_bind a2 a3 oo) ->
       (red_expr S C (spec_call_prealloc a1 a2 a3) oo -> forall (S0 : state) (C0 : execution_ctx) (vthis : value) (target : object_loc) (thisArg : value) (A : list value) (o : out) (args : list value), is_callable S a2 -> @eq value a2 (value_object target) -> arguments_first_and_rest a3 (@pair value (list value) thisArg A) -> red_expr S C (spec_function_proto_bind_1 target thisArg A) oo -> @eq state S0 S -> @eq execution_ctx C0 C -> @eq prealloc prealloc_function_proto_bind a1 -> @eq value vthis a2 -> @eq (list value) args a3 -> @eq out o oo -> P S C prealloc_function_proto_bind a2 a3 oo) ->
       (red_expr S C (spec_call_prealloc a1 a2 a3) oo -> forall (S0 : state) (C0 : execution_ctx) (vthis : value) (args : list value) (o : out), red_expr S C (spec_construct_prealloc prealloc_array a3) oo -> @eq state S0 S -> @eq execution_ctx C0 C -> @eq prealloc prealloc_array a1 -> @eq value vthis a2 -> @eq (list value) args a3 -> @eq out o oo -> P S C prealloc_array a2 a3 oo) ->
       (red_expr S C (spec_call_prealloc a1 a2 a3) oo -> forall (S0 : state) (C0 : execution_ctx) (vthis : value) (o : out) (args : list value) (arg : value), arguments_from a3 (@cons value arg (@nil value)) -> red_expr S C (spec_call_array_is_array_1 arg) oo -> @eq state S0 S -> @eq execution_ctx C0 C -> @eq prealloc prealloc_array_is_array a1 -> @eq value vthis a2 -> @eq (list value) args a3 -> @eq out o oo -> P S C prealloc_array_is_array a2 a3 oo) ->
       (red_expr S C (spec_call_prealloc a1 a2 a3) oo -> forall (S0 : state) (C0 : execution_ctx) (vthis : value) (args : list value) (o1 o : out), red_expr S C (spec_to_object a2) o1 -> red_expr S C (spec_call_array_proto_to_string o1) oo -> @eq state S0 S -> @eq execution_ctx C0 C -> @eq prealloc prealloc_array_proto_to_string a1 -> @eq value vthis a2 -> @eq (list value) args a3 -> @eq out o oo -> P S C prealloc_array_proto_to_string a2 a3 oo) ->
       (red_expr S C (spec_call_prealloc a1 a2 a3) oo -> forall (S0 : state) (C0 : execution_ctx) (vthis : value) (args : list value) (o1 o : out), red_expr S C (spec_to_object a2) o1 -> red_expr S C (spec_call_array_proto_join o1 a3) oo -> @eq state S0 S -> @eq execution_ctx C0 C -> @eq prealloc prealloc_array_proto_join a1 -> @eq value vthis a2 -> @eq (list value) args a3 -> @eq out o oo -> P S C prealloc_array_proto_join a2 a3 oo) ->
       (red_expr S C (spec_call_prealloc a1 a2 a3) oo -> forall (S0 : state) (C0 : execution_ctx) (vthis : value) (o o1 : out) (args : list value), red_expr S C (spec_to_object a2) o1 -> red_expr S C (spec_call_array_proto_pop_1 o1) oo -> @eq state S0 S -> @eq execution_ctx C0 C -> @eq prealloc prealloc_array_proto_pop a1 -> @eq value vthis a2 -> @eq (list value) args a3 -> @eq out o oo -> P S C prealloc_array_proto_pop a2 a3 oo) ->
       (red_expr S C (spec_call_prealloc a1 a2 a3) oo -> forall (S0 : state) (C0 : execution_ctx) (vthis : value) (args : list value) (o o1 : out), red_expr S C (spec_to_object a2) o1 -> red_expr S C (spec_call_array_proto_push_1 o1 a3) oo -> @eq state S0 S -> @eq execution_ctx C0 C -> @eq prealloc prealloc_array_proto_push a1 -> @eq value vthis a2 -> @eq (list value) args a3 -> @eq out o oo -> P S C prealloc_array_proto_push a2 a3 oo) ->
       (red_expr S C (spec_call_prealloc a1 a2 a3) oo -> forall (S0 : state) (C0 : execution_ctx) (args : list value) (o o1 : out) (v vthis : value), arguments_from a3 (@cons value v (@nil value)) -> red_expr S C (spec_to_string v) o1 -> red_expr S C (spec_call_string_non_empty o1) oo -> @eq state S0 S -> @eq execution_ctx C0 C -> @eq prealloc prealloc_string a1 -> @eq value vthis a2 -> @eq (list value) args a3 -> @eq out o oo -> P S C prealloc_string a2 a3 oo) ->
       (red_expr S C (spec_call_prealloc a1 a2 a3) oo -> forall (S0 : state) (C0 : execution_ctx) (vthis : value), @eq state S0 S -> @eq execution_ctx C0 C -> @eq prealloc prealloc_string a1 -> @eq value vthis a2 -> @eq (list value) (@nil value) a3 -> @eq out (out_ter S (res_val (value_prim (prim_string EmptyString)))) oo -> P S C prealloc_string a2 (@nil value) (out_ter S (res_val (value_prim (prim_string EmptyString))))) ->
       (red_expr S C (spec_call_prealloc a1 a2 a3) oo -> forall (S0 : state) (C0 : execution_ctx) (vthis : value) (args : list value) (o : out), red_expr S C (spec_call_prealloc prealloc_string_proto_value_of a2 a3) oo -> @eq state S0 S -> @eq execution_ctx C0 C -> @eq prealloc prealloc_string_proto_to_string a1 -> @eq value vthis a2 -> @eq (list value) args a3 -> @eq out o oo -> P S C prealloc_string_proto_to_string a2 a3 oo) ->
       (red_expr S C (spec_call_prealloc a1 a2 a3) oo -> forall (S0 : state) (C0 : execution_ctx) (vthis : value) (args : list value), @eq type (type_of a2) type_string -> @eq state S0 S -> @eq execution_ctx C0 C -> @eq prealloc prealloc_string_proto_value_of a1 -> @eq value vthis a2 -> @eq (list value) args a3 -> @eq out (out_ter S (res_val a2)) oo -> P S C prealloc_string_proto_value_of a2 a3 (out_ter S (res_val a2))) ->
       (red_expr S C (spec_call_prealloc a1 a2 a3) oo -> forall (S0 : state) (C0 : execution_ctx) (l : object_loc) (v : value) (args : list value), object_class S l (String (Ascii true true false false true false true false) (String (Ascii false false true false true true true false) (String (Ascii false true false false true true true false) (String (Ascii true false false true false true true false) (String (Ascii false true true true false true true false) (String (Ascii true true true false false true true false) EmptyString)))))) -> object_prim_value S l v -> @eq state S0 S -> @eq execution_ctx C0 C -> @eq prealloc prealloc_string_proto_value_of a1 -> @eq value (value_object l) a2 -> @eq (list value) args a3 -> @eq out (out_ter S (res_val v)) oo -> P S C prealloc_string_proto_value_of (value_object l) a3 (out_ter S (res_val v))) ->
       (red_expr S C (spec_call_prealloc a1 a2 a3) oo -> forall (S0 : state) (C0 : execution_ctx) (l : object_loc) (args : list value) (o : out), not (object_class S l (String (Ascii true true false false true false true false) (String (Ascii false false true false true true true false) (String (Ascii false true false false true true true false) (String (Ascii true false false true false true true false) (String (Ascii false true true true false true true false) (String (Ascii true true true false false true true false) EmptyString))))))) -> red_expr S C (spec_error native_error_type) oo -> @eq state S0 S -> @eq execution_ctx C0 C -> @eq prealloc prealloc_string_proto_value_of a1 -> @eq value (value_object l) a2 -> @eq (list value) args a3 -> @eq out o oo -> P S C prealloc_string_proto_value_of (value_object l) a3 oo) ->
       (red_expr S C (spec_call_prealloc a1 a2 a3) oo -> forall (S0 : state) (C0 : execution_ctx) (vthis : value) (args : list value) (o : out), not (@eq type (type_of a2) type_string) -> not (@eq type (type_of a2) type_object) -> red_expr S C (spec_error native_error_type) oo -> @eq state S0 S -> @eq execution_ctx C0 C -> @eq prealloc prealloc_string_proto_value_of a1 -> @eq value vthis a2 -> @eq (list value) args a3 -> @eq out o oo -> P S C prealloc_string_proto_value_of a2 a3 oo) ->
       (red_expr S C (spec_call_prealloc a1 a2 a3) oo -> forall (S0 : state) (C0 : execution_ctx) (v : value) (o : out) (vthis : value) (args : list value), arguments_from a3 (@cons value v (@nil value)) -> red_expr S C (spec_to_boolean v) oo -> @eq state S0 S -> @eq execution_ctx C0 C -> @eq prealloc prealloc_bool a1 -> @eq value vthis a2 -> @eq (list value) args a3 -> @eq out o oo -> P S C prealloc_bool a2 a3 oo) ->
       (red_expr S C (spec_call_prealloc a1 a2 a3) oo -> forall (S0 : state) (C0 : execution_ctx) (vthis : value) (args : list value) (s : string) (o : out) (b : bool), value_viewable_as (String (Ascii false true false false false false true false) (String (Ascii true true true true false true true false) (String (Ascii true true true true false true true false) (String (Ascii false false true true false true true false) (String (Ascii true false true false false true true false) (String (Ascii true false false false false true true false) (String (Ascii false true true true false true true false) EmptyString))))))) S a2 (prim_bool b) -> @eq string s (convert_bool_to_string b) -> @eq state S0 S -> @eq execution_ctx C0 C -> @eq prealloc prealloc_bool_proto_to_string a1 -> @eq value vthis a2 -> @eq (list value) args a3 -> @eq out o oo -> P S C prealloc_bool_proto_to_string a2 a3 oo) ->
       (red_expr S C (spec_call_prealloc a1 a2 a3) oo -> forall (S0 : state) (C0 : execution_ctx) (vthis : value) (args : list value) (o : out), (forall b : bool, not (value_viewable_as (String (Ascii false true false false false false true false) (String (Ascii true true true true false true true false) (String (Ascii true true true true false true true false) (String (Ascii false false true true false true true false) (String (Ascii true false true false false true true false) (String (Ascii true false false false false true true false) (String (Ascii false true true true false true true false) EmptyString))))))) S a2 (prim_bool b))) -> red_expr S C (spec_error native_error_type) oo -> @eq state S0 S -> @eq execution_ctx C0 C -> @eq prealloc prealloc_bool_proto_to_string a1 -> @eq value vthis a2 -> @eq (list value) args a3 -> @eq out o oo -> P S C prealloc_bool_proto_to_string a2 a3 oo) ->
       (red_expr S C (spec_call_prealloc a1 a2 a3) oo -> forall (S0 : state) (C0 : execution_ctx) (vthis : value) (args : list value) (b : bool), value_viewable_as (String (Ascii false true false false false false true false) (String (Ascii true true true true false true true false) (String (Ascii true true true true false true true false) (String (Ascii false false true true false true true false) (String (Ascii true false true false false true true false) (String (Ascii true false false false false true true false) (String (Ascii false true true true false true true false) EmptyString))))))) S a2 (prim_bool b) -> @eq state S0 S -> @eq execution_ctx C0 C -> @eq prealloc prealloc_bool_proto_value_of a1 -> @eq value vthis a2 -> @eq (list value) args a3 -> @eq out (out_ter S (res_val (value_prim (prim_bool b)))) oo -> P S C prealloc_bool_proto_value_of a2 a3 (out_ter S (res_val (value_prim (prim_bool b))))) ->
       (red_expr S C (spec_call_prealloc a1 a2 a3) oo -> forall (S0 : state) (C0 : execution_ctx) (vthis : value) (args : list value) (o : out), (forall b : bool, not (value_viewable_as (String (Ascii false true false false false false true false) (String (Ascii true true true true false true true false) (String (Ascii true true true true false true true false) (String (Ascii false false true true false true true false) (String (Ascii true false true false false true true false) (String (Ascii true false false false false true true false) (String (Ascii false true true true false true true false) EmptyString))))))) S a2 (prim_bool b))) -> red_expr S C (spec_error native_error_type) oo -> @eq state S0 S -> @eq execution_ctx C0 C -> @eq prealloc prealloc_bool_proto_value_of a1 -> @eq value vthis a2 -> @eq (list value) args a3 -> @eq out o oo -> P S C prealloc_bool_proto_value_of a2 a3 oo) ->
       (red_expr S C (spec_call_prealloc a1 a2 a3) oo -> forall (S0 : state) (C0 : execution_ctx) (vthis : value), @eq state S0 S -> @eq execution_ctx C0 C -> @eq prealloc prealloc_number a1 -> @eq value vthis a2 -> @eq (list value) (@nil value) a3 -> @eq out (out_ter S (res_val (value_prim (prim_number JsNumber.zero)))) oo -> P S C prealloc_number a2 (@nil value) (out_ter S (res_val (value_prim (prim_number JsNumber.zero))))) ->
       (red_expr S C (spec_call_prealloc a1 a2 a3) oo -> forall (S0 : state) (C0 : execution_ctx) (v : value) (o : out) (vthis : value) (args : list value), not (@eq (list value) a3 (@nil value)) -> arguments_from a3 (@cons value v (@nil value)) -> red_expr S C (spec_to_number v) oo -> @eq state S0 S -> @eq execution_ctx C0 C -> @eq prealloc prealloc_number a1 -> @eq value vthis a2 -> @eq (list value) args a3 -> @eq out o oo -> P S C prealloc_number a2 a3 oo) ->
       (red_expr S C (spec_call_prealloc a1 a2 a3) oo -> forall (S0 : state) (C0 : execution_ctx) (vthis : value) (args : list value) (n : JsNumber.number), value_viewable_as (String (Ascii false true true true false false true false) (String (Ascii true false true false true true true false) (String (Ascii true false true true false true true false) (String (Ascii false true false false false true true false) (String (Ascii true false true false false true true false) (String (Ascii false true false false true true true false) EmptyString)))))) S a2 (prim_number n) -> @eq state S0 S -> @eq execution_ctx C0 C -> @eq prealloc prealloc_number_proto_value_of a1 -> @eq value vthis a2 -> @eq (list value) args a3 -> @eq out (out_ter S (res_val (value_prim (prim_number n)))) oo -> P S C prealloc_number_proto_value_of a2 a3 (out_ter S (res_val (value_prim (prim_number n))))) ->
       (red_expr S C (spec_call_prealloc a1 a2 a3) oo -> forall (S0 : state) (C0 : execution_ctx) (vthis : value) (args : list value) (o : out), (forall n : JsNumber.number, not (value_viewable_as (String (Ascii false true true true false false true false) (String (Ascii true false true false true true true false) (String (Ascii true false true true false true true false) (String (Ascii false true false false false true true false) (String (Ascii true false true false false true true false) (String (Ascii false true false false true true true false) EmptyString)))))) S a2 (prim_number n))) -> red_expr S C (spec_error native_error_type) oo -> @eq state S0 S -> @eq execution_ctx C0 C -> @eq prealloc prealloc_number_proto_value_of a1 -> @eq value vthis a2 -> @eq (list value) args a3 -> @eq out o oo -> P S C prealloc_number_proto_value_of a2 a3 oo) ->
       (red_expr S C (spec_call_prealloc a1 a2 a3) oo -> forall (S0 : state) (C0 : execution_ctx) (v : value) (o : out) (vthis : value) (args : list value), arguments_from a3 (@cons value v (@nil value)) -> red_expr S C (spec_build_error (value_object (object_loc_prealloc prealloc_error_proto)) v) oo -> @eq state S0 S -> @eq execution_ctx C0 C -> @eq prealloc prealloc_error a1 -> @eq value vthis a2 -> @eq (list value) args a3 -> @eq out o oo -> P S C prealloc_error a2 a3 oo) ->
       (red_expr S C (spec_call_prealloc a1 a2 a3) oo -> forall (S0 : state) (C0 : execution_ctx) (args : list value) (vthis : value) (o : out), red_expr S C (spec_call_error_proto_to_string_1 a2) oo -> @eq state S0 S -> @eq execution_ctx C0 C -> @eq prealloc prealloc_error_proto_to_string a1 -> @eq value vthis a2 -> @eq (list value) args a3 -> @eq out o oo -> P S C prealloc_error_proto_to_string a2 a3 oo) ->
       (red_expr S C (spec_call_prealloc a1 a2 a3) oo -> forall (S0 : state) (C0 : execution_ctx) (v : value) (o : out) (ne : native_error) (vthis : value) (args : list value), arguments_from a3 (@cons value v (@nil value)) -> red_expr S C (spec_build_error (value_object (object_loc_prealloc (prealloc_native_error_proto ne))) v) oo -> @eq state S0 S -> @eq execution_ctx C0 C -> @eq prealloc (prealloc_native_error ne) a1 -> @eq value vthis a2 -> @eq (list value) args a3 -> @eq out o oo -> P S C (prealloc_native_error ne) a2 a3 oo) -> (red_expr S C (spec_call_prealloc a1 a2 a3) oo -> forall (S0 : state) (C0 : execution_ctx) (B : prealloc) (vthis : value) (args : list value) (o : out), implementation_prealloc a1 -> @eq state S0 S -> @eq execution_ctx C0 C -> @eq prealloc B a1 -> @eq value vthis a2 -> @eq (list value) args a3 -> @eq out o oo -> P S C a1 a2 a3 oo) -> red_expr S C (spec_call_prealloc a1 a2 a3) oo -> P S C a1 a2 a3 oo.

End InvExpr.