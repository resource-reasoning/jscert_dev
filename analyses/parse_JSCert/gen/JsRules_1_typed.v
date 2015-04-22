(* This file has been generated automatically by some OCaml scripts. *)
(* Please do not edit it, or your changes will probably be erased later. *)

(******************************************)

Require Import JsCommon.
Require Import JsCommonAux.
Require Import JsPrettyInterm.
Require Import JsPrettyIntermAux.
Require Import JsSyntaxInfos.
Require Import JsInit.

(******************************************)


(******************************************)

Implicit Type sc : switchclause.
Implicit Type sb : switchbody.
Implicit Type xs : (list prop_name).
Implicit Type cstr : construct.
Implicit Type c : call.
Implicit Type t : stat.
Implicit Type p : prog.
Implicit Type e : expr.
Implicit Type P : object_properties_type.
Implicit Type C : execution_ctx.
Implicit Type S : state.
Implicit Type O : object.
Implicit Type X : lexical_env.
Implicit Type Ed : decl_env_record.
Implicit Type E : env_record.
Implicit Type L : env_loc.
Implicit Type D : full_descriptor.
Implicit Type Desc : descriptor.
Implicit Type A : attributes.
Implicit Type Aa : attributes_accessor.
Implicit Type Ad : attributes_data.
Implicit Type m : mutability.
Implicit Type str : strictness_flag.
Implicit Type x : prop_name.
Implicit Type ct : codetype.
Implicit Type o : out.
Implicit Type R : res.
Implicit Type labs : label_set.
Implicit Type lab : label.
Implicit Type rv : resvalue.
Implicit Type rt : restype.
Implicit Type ty : type.
Implicit Type r : ref.
Implicit Type vthis : value.
Implicit Type vp : value.
Implicit Type vi : value.
Implicit Type v : value.
Implicit Type w : prim.
Implicit Type lp : object_loc.
Implicit Type l : object_loc.
Implicit Type i : literal.
Implicit Type s : string.
Implicit Type k : int.
Implicit Type n : number.
Implicit Type b : bool.

(******************************************)

Inductive red_javascript : prog (* input *) -> out -> Prop :=

  | red_javascript_intro :
      forall (S : state) (C : execution_ctx) (p : prog (* input *)) (p' : prog) (o : out) (o1 : out),
        (S = (state_initial : state)) ->
        (p' = ((add_infos_prog strictness_false p) : prog)) ->
        (C = ((execution_ctx_initial ((prog_intro_strictness p') : strictness_flag)) : execution_ctx)) ->
        (* ========================================== *)
        (red_expr (S : state) (C : execution_ctx) ((spec_binding_inst (codetype_global : codetype) (None : (option object_loc)) (p' : prog) (nil : (list value))) : ext_expr) (o1 : out)) ->
        (red_prog (S : state) (C : execution_ctx) ((javascript_1 (o1 : out) (p' : prog)) : ext_prog) (o : out)) ->
        (* ------------------------------------------ *)
        (red_javascript (p : prog) (o : out))


with red_prog : state (* input *) -> execution_ctx (* input *) -> ext_prog (* input *) -> out -> Prop :=

  | red_prog_abort :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (extp : ext_prog (* input *)) (o : out),
        ((out_of_ext_prog (extp : ext_prog)) = ((Some o) : (option out))) ->
        (abort (o : out)) ->
        (~ (abort_intercepted_prog (extp : ext_prog))) ->
        (* ========================================== *)
        (* ------------------------------------------ *)
        (red_prog (S : state) (C : execution_ctx) (extp : ext_prog) (o : out))

  | red_javascript_intro_1 :
      forall (S : state (* input *)) (S' : state (* input *)) (C : execution_ctx (* input *)) (p : prog (* input *)) (o : out),
        (* ========================================== *)
        (red_prog (S' : state) (C : execution_ctx) (p : ext_prog) (o : out)) ->
        (* ------------------------------------------ *)
        (red_prog (S : state) (C : execution_ctx) ((javascript_1 ((out_ter (S' : state) (res_intro restype_normal resvalue_empty label_empty)) : out) (p : prog)) : ext_prog) (o : out))

  | red_prog_nil :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (str : strictness_flag (* input *)),
        (* ========================================== *)
        (* ------------------------------------------ *)
        (red_prog (S : state) (C : execution_ctx) ((prog_intro (str : strictness_flag) (nil : (list element))) : ext_prog) ((out_ter (S : state) (resvalue_empty : res)) : out))

  | red_prog_cons :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (str : strictness_flag (* input *)) (el : element (* input *)) (els : (list element) (* input *)) (o1 : out) (o : out),
        (* ========================================== *)
        (red_prog (S : state) (C : execution_ctx) ((prog_intro (str : strictness_flag) (els : (list element))) : ext_prog) (o1 : out)) ->
        (red_prog (S : state) (C : execution_ctx) ((prog_1 (o1 : out) (el : element)) : ext_prog) (o : out)) ->
        (* ------------------------------------------ *)
        (red_prog (S : state) (C : execution_ctx) ((prog_intro (str : strictness_flag) ((els & el) : (list element))) : ext_prog) (o : out))

  | red_prog_1_funcdecl :
      forall (S0 : state (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (rv : resvalue (* input *)) (name : string (* input *)) (args : (list string) (* input *)) (bd : funcbody (* input *)),
        (* ========================================== *)
        (* ------------------------------------------ *)
        (red_prog (S0 : state) (C : execution_ctx) ((prog_1 ((out_ter (S : state) (rv : res)) : out) ((element_func_decl (name : string) (args : (list string)) (bd : funcbody)) : element)) : ext_prog) ((out_ter (S : state) (rv : res)) : out))

  | red_prog_1_stat :
      forall (S0 : state (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (t : stat (* input *)) (rv : resvalue (* input *)) (o1 : out) (o : out),
        (* ========================================== *)
        (red_stat (S : state) (C : execution_ctx) (t : ext_stat) (o1 : out)) ->
        (red_prog (S : state) (C : execution_ctx) ((prog_2 (rv : resvalue) (o1 : out)) : ext_prog) (o : out)) ->
        (* ------------------------------------------ *)
        (red_prog (S0 : state) (C : execution_ctx) ((prog_1 ((out_ter (S : state) (rv : res)) : out) ((element_stat (t : stat)) : element)) : ext_prog) (o : out))

  | red_prog_2 :
      forall (S0 : state (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (R : res (* input *)) (R' : res) (rv : resvalue (* input *)),
        (R' = ((res_overwrite_value_if_empty (rv : resvalue) (R : res)) : res)) ->
        (* ========================================== *)
        (* ------------------------------------------ *)
        (red_prog (S0 : state) (C : execution_ctx) ((prog_2 (rv : resvalue) ((out_ter (S : state) (R : res)) : out)) : ext_prog) ((out_ter (S : state) (R' : res)) : out))


with red_stat : state (* input *) -> execution_ctx (* input *) -> ext_stat (* input *) -> out -> Prop :=

  | red_stat_abort :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (extt : ext_stat (* input *)) (o : out),
        ((out_of_ext_stat (extt : ext_stat)) = ((Some o) : (option out))) ->
        (abort (o : out)) ->
        (~ (abort_intercepted_stat (extt : ext_stat))) ->
        (* ========================================== *)
        (* ------------------------------------------ *)
        (red_stat (S : state) (C : execution_ctx) (extt : ext_stat) (o : out))

  | red_stat_block_nil :
      forall (S : state (* input *)) (C : execution_ctx (* input *)),
        (* ========================================== *)
        (* ------------------------------------------ *)
        (red_stat (S : state) (C : execution_ctx) ((stat_block (nil : (list stat))) : ext_stat) ((out_ter (S : state) (resvalue_empty : res)) : out))

  | red_stat_block_cons :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (t : stat (* input *)) (ts : (list stat) (* input *)) (o1 : out) (o : out),
        (* ========================================== *)
        (red_stat (S : state) (C : execution_ctx) ((stat_block (ts : (list stat))) : ext_stat) (o1 : out)) ->
        (red_stat (S : state) (C : execution_ctx) ((stat_block_1 (o1 : out) (t : stat)) : ext_stat) (o : out)) ->
        (* ------------------------------------------ *)
        (red_stat (S : state) (C : execution_ctx) ((stat_block ((ts ++ ((t :: (nil : (list stat))) : (list stat))) : (list stat))) : ext_stat) (o : out))

  | red_stat_block_1 :
      forall (S0 : state (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (t : stat (* input *)) (rv : resvalue (* input *)) (o : out) (o1 : out),
        (* ========================================== *)
        (red_stat (S : state) (C : execution_ctx) (t : ext_stat) (o1 : out)) ->
        (red_stat (S : state) (C : execution_ctx) ((stat_block_2 (rv : resvalue) (o1 : out)) : ext_stat) (o : out)) ->
        (* ------------------------------------------ *)
        (red_stat (S0 : state) (C : execution_ctx) ((stat_block_1 ((out_ter (S : state) (rv : res)) : out) (t : stat)) : ext_stat) (o : out))

  | red_stat_block_2_throw :
      forall (S0 : state (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (R : res (* input *)) (rv : resvalue (* input *)),
        ((res_type (R : res)) = (restype_throw : restype)) ->
        (* ========================================== *)
        (* ------------------------------------------ *)
        (red_stat (S0 : state) (C : execution_ctx) ((stat_block_2 (rv : resvalue) ((out_ter (S : state) (R : res)) : out)) : ext_stat) ((out_ter (S : state) (R : res)) : out))

  | red_stat_block_2_not_throw :
      forall (S0 : state (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (R : res (* input *)) (R' : res) (rv : resvalue (* input *)),
        ((res_type (R : res)) <> (restype_throw : restype)) ->
        (R' = ((res_overwrite_value_if_empty (rv : resvalue) (R : res)) : res)) ->
        (* ========================================== *)
        (* ------------------------------------------ *)
        (red_stat (S0 : state) (C : execution_ctx) ((stat_block_2 (rv : resvalue) ((out_ter (S : state) (R : res)) : out)) : ext_stat) ((out_ter (S : state) (R' : res)) : out))

  | red_stat_var_decl_nil :
      forall (S : state (* input *)) (C : execution_ctx (* input *)),
        (* ========================================== *)
        (* ------------------------------------------ *)
        (red_stat (S : state) (C : execution_ctx) ((stat_var_decl (nil : (list (string * (option expr))))) : ext_stat) ((out_ter (S : state) (res_empty : res)) : out))

  | red_stat_var_decl_cons :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (o : out) (o1 : out) (d : (string * (option expr)) (* input *)) (ds : (list (string * (option expr))) (* input *)),
        (* ========================================== *)
        (red_stat (S : state) (C : execution_ctx) ((stat_var_decl_item (d : (string * (option expr)))) : ext_stat) (o1 : out)) ->
        (red_stat (S : state) (C : execution_ctx) ((stat_var_decl_1 (o1 : out) (ds : (list (string * (option expr))))) : ext_stat) (o : out)) ->
        (* ------------------------------------------ *)
        (red_stat (S : state) (C : execution_ctx) ((stat_var_decl ((d :: ds) : (list (string * (option expr))))) : ext_stat) (o : out))

  | red_stat_var_decl_1 :
      forall (S : state (* input *)) (S0 : state (* input *)) (C : execution_ctx (* input *)) (ds : (list (string * (option expr))) (* input *)) (o : out) (rv : resvalue (* input *)),
        (* ========================================== *)
        (red_stat (S : state) (C : execution_ctx) ((stat_var_decl (ds : (list (string * (option expr))))) : ext_stat) (o : out)) ->
        (* ------------------------------------------ *)
        (red_stat (S0 : state) (C : execution_ctx) ((stat_var_decl_1 ((out_ter (S : state) (rv : res)) : out) (ds : (list (string * (option expr))))) : ext_stat) (o : out))

  | red_stat_var_decl_item_none :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (x : prop_name (* input *)),
        (* ========================================== *)
        (* ------------------------------------------ *)
        (red_stat (S : state) (C : execution_ctx) ((stat_var_decl_item ((x, None) : (string * (option expr)))) : ext_stat) ((out_ter (S : state) (x : res)) : out))

  | red_stat_var_decl_item_some :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (x : prop_name (* input *)) (e : expr (* input *)) (y1 : (specret ref)) (o : out),
        (* ========================================== *)
        (red_spec S C (spec_identifier_resolution (C : execution_ctx) (x : prop_name)) y1) ->
        (red_stat (S : state) (C : execution_ctx) ((stat_var_decl_item_1 (x : string) (y1 : (specret ref)) (e : expr)) : ext_stat) (o : out)) ->
        (* ------------------------------------------ *)
        (red_stat (S : state) (C : execution_ctx) ((stat_var_decl_item ((x, (Some e)) : (string * (option expr)))) : ext_stat) (o : out))

  | red_stat_var_decl_item_1 :
      forall (S : state (* input *)) (S0 : state (* input *)) (C : execution_ctx (* input *)) (x : prop_name (* input *)) (e : expr (* input *)) (r : ref (* input *)) (y1 : (specret value)) (o : out),
        (* ========================================== *)
        (red_spec S C (spec_expr_get_value (e : expr)) y1) ->
        (red_stat (S : state) (C : execution_ctx) ((stat_var_decl_item_2 (x : string) (r : ref) (y1 : (specret value))) : ext_stat) (o : out)) ->
        (* ------------------------------------------ *)
        (red_stat (S0 : state) (C : execution_ctx) ((stat_var_decl_item_1 (x : string) ((specret_val S r) : (specret ref)) (e : expr)) : ext_stat) (o : out))

  | red_stat_var_decl_item_2 :
      forall (S : state (* input *)) (S0 : state (* input *)) (C : execution_ctx (* input *)) (r : ref (* input *)) (v : value (* input *)) (o : out) (o1 : out) (x : prop_name (* input *)),
        (* ========================================== *)
        (red_expr (S : state) (C : execution_ctx) ((spec_put_value (r : resvalue) (v : value)) : ext_expr) (o1 : out)) ->
        (red_stat (S : state) (C : execution_ctx) ((stat_var_decl_item_3 (x : string) (o1 : out)) : ext_stat) (o : out)) ->
        (* ------------------------------------------ *)
        (red_stat (S0 : state) (C : execution_ctx) ((stat_var_decl_item_2 (x : string) (r : ref) ((specret_val S v) : (specret value))) : ext_stat) (o : out))

  | red_stat_var_decl_item_3 :
      forall (S : state (* input *)) (S0 : state (* input *)) (C : execution_ctx (* input *)) (x : prop_name (* input *)),
        (* ========================================== *)
        (* ------------------------------------------ *)
        (red_stat (S0 : state) (C : execution_ctx) ((stat_var_decl_item_3 (x : string) ((out_ter (S : state) (res_intro restype_normal resvalue_empty label_empty)) : out)) : ext_stat) ((out_ter (S : state) (x : res)) : out))

  | red_stat_expr :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (e : expr (* input *)) (o : out) (y1 : (specret value)),
        (* ========================================== *)
        (red_spec S C (spec_expr_get_value (e : expr)) y1) ->
        (red_stat (S : state) (C : execution_ctx) ((stat_expr_1 (y1 : (specret value))) : ext_stat) (o : out)) ->
        (* ------------------------------------------ *)
        (red_stat (S : state) (C : execution_ctx) ((stat_expr (e : expr)) : ext_stat) (o : out))

  | red_stat_expr_1 :
      forall (S0 : state (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (v : value (* input *)),
        (* ========================================== *)
        (* ------------------------------------------ *)
        (red_stat (S0 : state) (C : execution_ctx) ((stat_expr_1 ((specret_val S v) : (specret value))) : ext_stat) ((out_ter (S : state) (v : res)) : out))

  | red_stat_if :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (e1 : expr (* input *)) (t2 : stat (* input *)) (t3opt : (option stat) (* input *)) (y1 : (specret value)) (o : out),
        (* ========================================== *)
        (red_spec S C (spec_expr_get_value_conv (spec_to_boolean : (value -> ext_expr)) (e1 : expr)) y1) ->
        (red_stat (S : state) (C : execution_ctx) ((stat_if_1 (y1 : (specret value)) (t2 : stat) (t3opt : (option stat))) : ext_stat) (o : out)) ->
        (* ------------------------------------------ *)
        (red_stat (S : state) (C : execution_ctx) ((stat_if (e1 : expr) (t2 : stat) (t3opt : (option stat))) : ext_stat) (o : out))

  | red_stat_if_1_true :
      forall (S0 : state (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (t2 : stat (* input *)) (t3opt : (option stat) (* input *)) (o : out),
        (* ========================================== *)
        (red_stat (S : state) (C : execution_ctx) (t2 : ext_stat) (o : out)) ->
        (* ------------------------------------------ *)
        (red_stat (S0 : state) (C : execution_ctx) ((stat_if_1 ((specret_val (S : state) (true : value)) : (specret value)) (t2 : stat) (t3opt : (option stat))) : ext_stat) (o : out))

  | red_stat_if_1_false :
      forall (S0 : state (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (t2 : stat (* input *)) (t3 : stat (* input *)) (o : out),
        (* ========================================== *)
        (red_stat (S : state) (C : execution_ctx) (t3 : ext_stat) (o : out)) ->
        (* ------------------------------------------ *)
        (red_stat (S0 : state) (C : execution_ctx) ((stat_if_1 ((specret_val (S : state) (false : value)) : (specret value)) (t2 : stat) ((Some t3) : (option stat))) : ext_stat) (o : out))

  | red_stat_if_1_false_implicit :
      forall (S0 : state (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (t2 : stat (* input *)),
        (* ========================================== *)
        (* ------------------------------------------ *)
        (red_stat (S0 : state) (C : execution_ctx) ((stat_if_1 ((specret_val (S : state) (false : value)) : (specret value)) (t2 : stat) (None : (option stat))) : ext_stat) ((out_ter (S : state) (resvalue_empty : res)) : out))

  | red_stat_do_while :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (labs : label_set (* input *)) (t1 : stat (* input *)) (e2 : expr (* input *)) (o : out),
        (* ========================================== *)
        (red_stat (S : state) (C : execution_ctx) ((stat_do_while_1 (labs : label_set) (t1 : stat) (e2 : expr) (resvalue_empty : resvalue)) : ext_stat) (o : out)) ->
        (* ------------------------------------------ *)
        (red_stat (S : state) (C : execution_ctx) ((stat_do_while (labs : label_set) (t1 : stat) (e2 : expr)) : ext_stat) (o : out))

  | red_stat_do_while_1 :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (labs : label_set (* input *)) (t1 : stat (* input *)) (e2 : expr (* input *)) (rv : resvalue (* input *)) (o1 : out) (o : out),
        (* ========================================== *)
        (red_stat (S : state) (C : execution_ctx) (t1 : ext_stat) (o1 : out)) ->
        (red_stat (S : state) (C : execution_ctx) ((stat_do_while_2 (labs : label_set) (t1 : stat) (e2 : expr) (rv : resvalue) (o1 : out)) : ext_stat) (o : out)) ->
        (* ------------------------------------------ *)
        (red_stat (S : state) (C : execution_ctx) ((stat_do_while_1 (labs : label_set) (t1 : stat) (e2 : expr) (rv : resvalue)) : ext_stat) (o : out))

  | red_stat_do_while_2 :
      forall (rv : resvalue) (S0 : state (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (labs : label_set (* input *)) (t1 : stat (* input *)) (e2 : expr (* input *)) (rv_old : resvalue (* input *)) (R : res (* input *)) (o : out),
        (rv = ((ifb ((res_value (R : res)) = (resvalue_empty : resvalue)) then (rv_old : resvalue) else (res_value (R : res))) : resvalue)) ->
        (* ========================================== *)
        (red_stat (S : state) (C : execution_ctx) ((stat_do_while_3 (labs : label_set) (t1 : stat) (e2 : expr) (rv : resvalue) (R : res)) : ext_stat) (o : out)) ->
        (* ------------------------------------------ *)
        (red_stat (S0 : state) (C : execution_ctx) ((stat_do_while_2 (labs : label_set) (t1 : stat) (e2 : expr) (rv_old : resvalue) ((out_ter (S : state) (R : res)) : out)) : ext_stat) (o : out))

  | red_stat_do_while_3_continue :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (labs : label_set (* input *)) (t1 : stat (* input *)) (e2 : expr (* input *)) (rv : resvalue (* input *)) (R : res (* input *)) (o : out),
        ((((res_type R) = restype_continue) : Prop) /\ ((res_label_in R labs) : Prop)) ->
        (* ========================================== *)
        (red_stat (S : state) (C : execution_ctx) ((stat_do_while_6 (labs : label_set) (t1 : stat) (e2 : expr) (rv : resvalue)) : ext_stat) (o : out)) ->
        (* ------------------------------------------ *)
        (red_stat (S : state) (C : execution_ctx) ((stat_do_while_3 (labs : label_set) (t1 : stat) (e2 : expr) (rv : resvalue) (R : res)) : ext_stat) (o : out))

  | red_stat_do_while_3_not_continue :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (labs : label_set (* input *)) (t1 : stat (* input *)) (e2 : expr (* input *)) (rv : resvalue (* input *)) (R : res (* input *)) (o : out),
        (~ ((((res_type R) = restype_continue) : Prop) /\ ((res_label_in R labs) : Prop))) ->
        (* ========================================== *)
        (red_stat (S : state) (C : execution_ctx) ((stat_do_while_4 (labs : label_set) (t1 : stat) (e2 : expr) (rv : resvalue) (R : res)) : ext_stat) (o : out)) ->
        (* ------------------------------------------ *)
        (red_stat (S : state) (C : execution_ctx) ((stat_do_while_3 (labs : label_set) (t1 : stat) (e2 : expr) (rv : resvalue) (R : res)) : ext_stat) (o : out))

  | red_stat_do_while_4_break :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (labs : label_set (* input *)) (t1 : stat (* input *)) (e2 : expr (* input *)) (rv : resvalue (* input *)) (R : res (* input *)),
        ((((res_type R) = restype_break) : Prop) /\ ((res_label_in R labs) : Prop)) ->
        (* ========================================== *)
        (* ------------------------------------------ *)
        (red_stat (S : state) (C : execution_ctx) ((stat_do_while_4 (labs : label_set) (t1 : stat) (e2 : expr) (rv : resvalue) (R : res)) : ext_stat) ((out_ter (S : state) (rv : res)) : out))

  | red_stat_do_while_4_not_break :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (labs : label_set (* input *)) (t1 : stat (* input *)) (e2 : expr (* input *)) (rv : resvalue (* input *)) (R : res (* input *)) (o : out),
        (~ ((((res_type R) = restype_break) : Prop) /\ ((res_label_in R labs) : Prop))) ->
        (* ========================================== *)
        (red_stat (S : state) (C : execution_ctx) ((stat_do_while_5 (labs : label_set) (t1 : stat) (e2 : expr) (rv : resvalue) (R : res)) : ext_stat) (o : out)) ->
        (* ------------------------------------------ *)
        (red_stat (S : state) (C : execution_ctx) ((stat_do_while_4 (labs : label_set) (t1 : stat) (e2 : expr) (rv : resvalue) (R : res)) : ext_stat) (o : out))

  | red_stat_do_while_5_abort :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (labs : label_set (* input *)) (t1 : stat (* input *)) (e2 : expr (* input *)) (rv : resvalue (* input *)) (R : res (* input *)),
        ((res_type (R : res)) <> (restype_normal : restype)) ->
        (* ========================================== *)
        (* ------------------------------------------ *)
        (red_stat (S : state) (C : execution_ctx) ((stat_do_while_5 (labs : label_set) (t1 : stat) (e2 : expr) (rv : resvalue) (R : res)) : ext_stat) ((out_ter (S : state) (R : res)) : out))

  | red_stat_do_while_5_normal :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (labs : label_set (* input *)) (t1 : stat (* input *)) (e2 : expr (* input *)) (rv : resvalue (* input *)) (R : res (* input *)) (o : out),
        ((res_type (R : res)) = (restype_normal : restype)) ->
        (* ========================================== *)
        (red_stat (S : state) (C : execution_ctx) ((stat_do_while_6 (labs : label_set) (t1 : stat) (e2 : expr) (rv : resvalue)) : ext_stat) (o : out)) ->
        (* ------------------------------------------ *)
        (red_stat (S : state) (C : execution_ctx) ((stat_do_while_5 (labs : label_set) (t1 : stat) (e2 : expr) (rv : resvalue) (R : res)) : ext_stat) (o : out))

  | red_stat_do_while_6 :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (labs : label_set (* input *)) (t1 : stat (* input *)) (e2 : expr (* input *)) (rv : resvalue (* input *)) (y1 : (specret value)) (o : out),
        (* ========================================== *)
        (red_spec S C (spec_expr_get_value_conv (spec_to_boolean : (value -> ext_expr)) (e2 : expr)) y1) ->
        (red_stat (S : state) (C : execution_ctx) ((stat_do_while_7 (labs : label_set) (t1 : stat) (e2 : expr) (rv : resvalue) (y1 : (specret value))) : ext_stat) (o : out)) ->
        (* ------------------------------------------ *)
        (red_stat (S : state) (C : execution_ctx) ((stat_do_while_6 (labs : label_set) (t1 : stat) (e2 : expr) (rv : resvalue)) : ext_stat) (o : out))

  | red_stat_do_while_7_false :
      forall (S0 : state (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (labs : label_set (* input *)) (t1 : stat (* input *)) (e2 : expr (* input *)) (rv : resvalue (* input *)),
        (* ========================================== *)
        (* ------------------------------------------ *)
        (red_stat (S0 : state) (C : execution_ctx) ((stat_do_while_7 (labs : label_set) (t1 : stat) (e2 : expr) (rv : resvalue) ((specret_val (S : state) (false : value)) : (specret value))) : ext_stat) ((out_ter (S : state) (rv : res)) : out))

  | red_stat_do_while_7_true :
      forall (S0 : state (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (labs : label_set (* input *)) (t1 : stat (* input *)) (e2 : expr (* input *)) (rv : resvalue (* input *)) (o : out),
        (* ========================================== *)
        (red_stat (S : state) (C : execution_ctx) ((stat_do_while_1 (labs : label_set) (t1 : stat) (e2 : expr) (rv : resvalue)) : ext_stat) (o : out)) ->
        (* ------------------------------------------ *)
        (red_stat (S0 : state) (C : execution_ctx) ((stat_do_while_7 (labs : label_set) (t1 : stat) (e2 : expr) (rv : resvalue) ((specret_val (S : state) (true : value)) : (specret value))) : ext_stat) (o : out))

  | red_stat_while :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (labs : label_set (* input *)) (e1 : expr (* input *)) (t2 : stat (* input *)) (o : out),
        (* ========================================== *)
        (red_stat (S : state) (C : execution_ctx) ((stat_while_1 (labs : label_set) (e1 : expr) (t2 : stat) (resvalue_empty : resvalue)) : ext_stat) (o : out)) ->
        (* ------------------------------------------ *)
        (red_stat (S : state) (C : execution_ctx) ((stat_while (labs : label_set) (e1 : expr) (t2 : stat)) : ext_stat) (o : out))

  | red_stat_while_1 :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (labs : label_set (* input *)) (e1 : expr (* input *)) (t2 : stat (* input *)) (rv : resvalue (* input *)) (y1 : (specret value)) (o : out),
        (* ========================================== *)
        (red_spec S C (spec_expr_get_value_conv (spec_to_boolean : (value -> ext_expr)) (e1 : expr)) y1) ->
        (red_stat (S : state) (C : execution_ctx) ((stat_while_2 (labs : label_set) (e1 : expr) (t2 : stat) (rv : resvalue) (y1 : (specret value))) : ext_stat) (o : out)) ->
        (* ------------------------------------------ *)
        (red_stat (S : state) (C : execution_ctx) ((stat_while_1 (labs : label_set) (e1 : expr) (t2 : stat) (rv : resvalue)) : ext_stat) (o : out))

  | red_stat_while_2_false :
      forall (S0 : state (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (labs : label_set (* input *)) (e1 : expr (* input *)) (t2 : stat (* input *)) (rv : resvalue (* input *)),
        (* ========================================== *)
        (* ------------------------------------------ *)
        (red_stat (S0 : state) (C : execution_ctx) ((stat_while_2 (labs : label_set) (e1 : expr) (t2 : stat) (rv : resvalue) ((specret_val (S : state) (false : value)) : (specret value))) : ext_stat) ((out_ter (S : state) (rv : res)) : out))

  | red_stat_while_2_true :
      forall (S0 : state (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (labs : label_set (* input *)) (e1 : expr (* input *)) (t2 : stat (* input *)) (rv : resvalue (* input *)) (o1 : out) (o : out),
        (* ========================================== *)
        (red_stat (S : state) (C : execution_ctx) (t2 : ext_stat) (o1 : out)) ->
        (red_stat (S : state) (C : execution_ctx) ((stat_while_3 (labs : label_set) (e1 : expr) (t2 : stat) (rv : resvalue) (o1 : out)) : ext_stat) (o : out)) ->
        (* ------------------------------------------ *)
        (red_stat (S0 : state) (C : execution_ctx) ((stat_while_2 (labs : label_set) (e1 : expr) (t2 : stat) (rv : resvalue) ((specret_val (S : state) (true : value)) : (specret value))) : ext_stat) (o : out))

  | red_stat_while_3 :
      forall (rv : resvalue (* input *)) (S0 : state (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (labs : label_set (* input *)) (e1 : expr (* input *)) (t2 : stat (* input *)) (rv' : resvalue) (R : res (* input *)) (o : out),
        (rv' = ((ifb ((res_value (R : res)) <> (resvalue_empty : resvalue)) then ((res_value (R : res)) : resvalue) else rv) : resvalue)) ->
        (* ========================================== *)
        (red_stat (S : state) (C : execution_ctx) ((stat_while_4 (labs : label_set) (e1 : expr) (t2 : stat) (rv' : resvalue) (R : res)) : ext_stat) (o : out)) ->
        (* ------------------------------------------ *)
        (red_stat (S0 : state) (C : execution_ctx) ((stat_while_3 (labs : label_set) (e1 : expr) (t2 : stat) (rv : resvalue) ((out_ter (S : state) (R : res)) : out)) : ext_stat) (o : out))

  | red_stat_while_4_continue :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (labs : label_set (* input *)) (e1 : expr (* input *)) (t2 : stat (* input *)) (rv : resvalue (* input *)) (R : res (* input *)) (o : out),
        ((((res_type R) = restype_continue) : Prop) /\ ((res_label_in R labs) : Prop)) ->
        (* ========================================== *)
        (red_stat (S : state) (C : execution_ctx) ((stat_while_1 (labs : label_set) (e1 : expr) (t2 : stat) (rv : resvalue)) : ext_stat) (o : out)) ->
        (* ------------------------------------------ *)
        (red_stat (S : state) (C : execution_ctx) ((stat_while_4 (labs : label_set) (e1 : expr) (t2 : stat) (rv : resvalue) (R : res)) : ext_stat) (o : out))

  | red_stat_while_4_not_continue :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (labs : label_set (* input *)) (e1 : expr (* input *)) (t2 : stat (* input *)) (rv : resvalue (* input *)) (R : res (* input *)) (o : out),
        (~ ((((res_type R) = restype_continue) : Prop) /\ ((res_label_in R labs) : Prop))) ->
        (* ========================================== *)
        (red_stat (S : state) (C : execution_ctx) ((stat_while_5 (labs : label_set) (e1 : expr) (t2 : stat) (rv : resvalue) (R : res)) : ext_stat) (o : out)) ->
        (* ------------------------------------------ *)
        (red_stat (S : state) (C : execution_ctx) ((stat_while_4 (labs : label_set) (e1 : expr) (t2 : stat) (rv : resvalue) (R : res)) : ext_stat) (o : out))

  | red_stat_while_5_break :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (labs : label_set (* input *)) (e1 : expr (* input *)) (t2 : stat (* input *)) (rv : resvalue (* input *)) (R : res (* input *)),
        ((((res_type R) = restype_break) : Prop) /\ ((res_label_in R labs) : Prop)) ->
        (* ========================================== *)
        (* ------------------------------------------ *)
        (red_stat (S : state) (C : execution_ctx) ((stat_while_5 (labs : label_set) (e1 : expr) (t2 : stat) (rv : resvalue) (R : res)) : ext_stat) ((out_ter (S : state) (rv : res)) : out))

  | red_stat_while_5_not_break :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (labs : label_set (* input *)) (e1 : expr (* input *)) (t2 : stat (* input *)) (rv : resvalue (* input *)) (R : res (* input *)) (o : out),
        (~ ((((res_type R) = restype_break) : Prop) /\ ((res_label_in R labs) : Prop))) ->
        (* ========================================== *)
        (red_stat (S : state) (C : execution_ctx) ((stat_while_6 (labs : label_set) (e1 : expr) (t2 : stat) (rv : resvalue) (R : res)) : ext_stat) (o : out)) ->
        (* ------------------------------------------ *)
        (red_stat (S : state) (C : execution_ctx) ((stat_while_5 (labs : label_set) (e1 : expr) (t2 : stat) (rv : resvalue) (R : res)) : ext_stat) (o : out))

  | red_stat_while_6_abort :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (labs : label_set (* input *)) (e1 : expr (* input *)) (t2 : stat (* input *)) (rv : resvalue (* input *)) (R : res (* input *)),
        ((res_type (R : res)) <> (restype_normal : restype)) ->
        (* ========================================== *)
        (* ------------------------------------------ *)
        (red_stat (S : state) (C : execution_ctx) ((stat_while_6 (labs : label_set) (e1 : expr) (t2 : stat) (rv : resvalue) (R : res)) : ext_stat) ((out_ter (S : state) (R : res)) : out))

  | red_stat_while_6_normal :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (labs : label_set (* input *)) (e1 : expr (* input *)) (t2 : stat (* input *)) (rv : resvalue (* input *)) (R : res (* input *)) (o : out),
        ((res_type (R : res)) = (restype_normal : restype)) ->
        (* ========================================== *)
        (red_stat (S : state) (C : execution_ctx) ((stat_while_1 (labs : label_set) (e1 : expr) (t2 : stat) (rv : resvalue)) : ext_stat) (o : out)) ->
        (* ------------------------------------------ *)
        (red_stat (S : state) (C : execution_ctx) ((stat_while_6 (labs : label_set) (e1 : expr) (t2 : stat) (rv : resvalue) (R : res)) : ext_stat) (o : out))

  | red_stat_for_none :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (labs : label_set (* input *)) (eo2 : (option expr) (* input *)) (eo3 : (option expr) (* input *)) (t : stat (* input *)) (o : out),
        (* ========================================== *)
        (red_stat (S : state) (C : execution_ctx) ((stat_for_2 (labs : label_set) (resvalue_empty : resvalue) (eo2 : (option expr)) (eo3 : (option expr)) (t : stat)) : ext_stat) (o : out)) ->
        (* ------------------------------------------ *)
        (red_stat (S : state) (C : execution_ctx) ((stat_for (labs : label_set) (None : (option expr)) (eo2 : (option expr)) (eo3 : (option expr)) (t : stat)) : ext_stat) (o : out))

  | red_stat_for_some :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (labs : label_set (* input *)) (e1 : expr (* input *)) (eo2 : (option expr) (* input *)) (eo3 : (option expr) (* input *)) (t : stat (* input *)) (o : out) (y1 : (specret value)),
        (* ========================================== *)
        (red_spec S C (spec_expr_get_value (e1 : expr)) y1) ->
        (red_stat (S : state) (C : execution_ctx) ((stat_for_1 (labs : label_set) (y1 : (specret value)) (eo2 : (option expr)) (eo3 : (option expr)) (t : stat)) : ext_stat) (o : out)) ->
        (* ------------------------------------------ *)
        (red_stat (S : state) (C : execution_ctx) ((stat_for (labs : label_set) ((Some e1) : (option expr)) (eo2 : (option expr)) (eo3 : (option expr)) (t : stat)) : ext_stat) (o : out))

  | red_stat_for_1 :
      forall (S0 : state (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (labs : label_set (* input *)) (v : value (* input *)) (eo2 : (option expr) (* input *)) (eo3 : (option expr) (* input *)) (t : stat (* input *)) (o : out),
        (* ========================================== *)
        (red_stat (S : state) (C : execution_ctx) ((stat_for_2 (labs : label_set) (resvalue_empty : resvalue) (eo2 : (option expr)) (eo3 : (option expr)) (t : stat)) : ext_stat) (o : out)) ->
        (* ------------------------------------------ *)
        (red_stat (S0 : state) (C : execution_ctx) ((stat_for_1 (labs : label_set) ((specret_val S v) : (specret value)) (eo2 : (option expr)) (eo3 : (option expr)) (t : stat)) : ext_stat) (o : out))

  | red_stat_for_2_none :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (labs : label_set (* input *)) (rv : resvalue (* input *)) (eo3 : (option expr) (* input *)) (t : stat (* input *)) (o : out),
        (* ========================================== *)
        (red_stat (S : state) (C : execution_ctx) ((stat_for_4 (labs : label_set) (rv : resvalue) (None : (option expr)) (eo3 : (option expr)) (t : stat)) : ext_stat) (o : out)) ->
        (* ------------------------------------------ *)
        (red_stat (S : state) (C : execution_ctx) ((stat_for_2 (labs : label_set) (rv : resvalue) (None : (option expr)) (eo3 : (option expr)) (t : stat)) : ext_stat) (o : out))

  | red_stat_for_2_some :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (labs : label_set (* input *)) (rv : resvalue (* input *)) (e2 : expr (* input *)) (eo3 : (option expr) (* input *)) (t : stat (* input *)) (o : out) (y1 : (specret value)),
        (* ========================================== *)
        (red_spec S C (spec_expr_get_value_conv (spec_to_boolean : (value -> ext_expr)) (e2 : expr)) y1) ->
        (red_stat (S : state) (C : execution_ctx) ((stat_for_3 (labs : label_set) (rv : resvalue) (e2 : expr) (y1 : (specret value)) (eo3 : (option expr)) (t : stat)) : ext_stat) (o : out)) ->
        (* ------------------------------------------ *)
        (red_stat (S : state) (C : execution_ctx) ((stat_for_2 (labs : label_set) (rv : resvalue) ((Some e2) : (option expr)) (eo3 : (option expr)) (t : stat)) : ext_stat) (o : out))

  | red_stat_for_3_false :
      forall (S0 : state (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (labs : label_set (* input *)) (rv : resvalue (* input *)) (e2 : expr (* input *)) (eo3 : (option expr) (* input *)) (t : stat (* input *)),
        (* ========================================== *)
        (* ------------------------------------------ *)
        (red_stat (S0 : state) (C : execution_ctx) ((stat_for_3 (labs : label_set) (rv : resvalue) (e2 : expr) ((specret_val (S : state) (false : value)) : (specret value)) (eo3 : (option expr)) (t : stat)) : ext_stat) ((out_ter (S : state) (rv : res)) : out))

  | red_stat_for_3_not_false :
      forall (S0 : state (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (labs : label_set (* input *)) (rv : resvalue (* input *)) (e2 : expr (* input *)) (v : value (* input *)) (eo3 : (option expr) (* input *)) (t : stat (* input *)) (o : out),
        (v <> (false : value)) ->
        (* ========================================== *)
        (red_stat (S : state) (C : execution_ctx) ((stat_for_4 (labs : label_set) (rv : resvalue) ((Some e2) : (option expr)) (eo3 : (option expr)) (t : stat)) : ext_stat) (o : out)) ->
        (* ------------------------------------------ *)
        (red_stat (S0 : state) (C : execution_ctx) ((stat_for_3 (labs : label_set) (rv : resvalue) (e2 : expr) ((specret_val (S : state) (v : value)) : (specret value)) (eo3 : (option expr)) (t : stat)) : ext_stat) (o : out))

  | red_stat_for_4 :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (labs : label_set (* input *)) (rv : resvalue (* input *)) (eo2 : (option expr) (* input *)) (eo3 : (option expr) (* input *)) (t : stat (* input *)) (o : out) (o1 : out),
        (* ========================================== *)
        (red_stat (S : state) (C : execution_ctx) (t : ext_stat) (o1 : out)) ->
        (red_stat (S : state) (C : execution_ctx) ((stat_for_5 (labs : label_set) (rv : resvalue) (eo2 : (option expr)) (o1 : out) (eo3 : (option expr)) (t : stat)) : ext_stat) (o : out)) ->
        (* ------------------------------------------ *)
        (red_stat (S : state) (C : execution_ctx) ((stat_for_4 (labs : label_set) (rv : resvalue) (eo2 : (option expr)) (eo3 : (option expr)) (t : stat)) : ext_stat) (o : out))

  | red_stat_for_5 :
      forall (S0 : state (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (labs : label_set (* input *)) (rv : resvalue (* input *)) (rv' : resvalue) (R : res (* input *)) (eo2 : (option expr) (* input *)) (eo3 : (option expr) (* input *)) (t : stat (* input *)) (o : out),
        (rv' = ((ifb ((res_value (R : res)) <> (resvalue_empty : resvalue)) then ((res_value (R : res)) : resvalue) else rv) : resvalue)) ->
        (* ========================================== *)
        (red_stat (S : state) (C : execution_ctx) ((stat_for_6 (labs : label_set) (rv' : resvalue) (eo2 : (option expr)) (eo3 : (option expr)) (t : stat) (R : res)) : ext_stat) (o : out)) ->
        (* ------------------------------------------ *)
        (red_stat (S0 : state) (C : execution_ctx) ((stat_for_5 (labs : label_set) (rv : resvalue) (eo2 : (option expr)) ((out_ter (S : state) (R : res)) : out) (eo3 : (option expr)) (t : stat)) : ext_stat) (o : out))

  | red_stat_for_6_break :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (labs : label_set (* input *)) (rv : resvalue (* input *)) (R : res (* input *)) (eo2 : (option expr) (* input *)) (eo3 : (option expr) (* input *)) (t : stat (* input *)),
        ((((res_type R) = restype_break) : Prop) /\ ((res_label_in R labs) : Prop)) ->
        (* ========================================== *)
        (* ------------------------------------------ *)
        (red_stat (S : state) (C : execution_ctx) ((stat_for_6 (labs : label_set) (rv : resvalue) (eo2 : (option expr)) (eo3 : (option expr)) (t : stat) (R : res)) : ext_stat) ((out_ter (S : state) (rv : res)) : out))

  | red_stat_for_6_not_break :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (labs : label_set (* input *)) (rv : resvalue (* input *)) (R : res (* input *)) (eo2 : (option expr) (* input *)) (eo3 : (option expr) (* input *)) (t : stat (* input *)) (o : out),
        ((((res_type R) <> restype_break) : Prop) \/ ((~ (res_label_in R labs)) : Prop)) ->
        (* ========================================== *)
        (red_stat (S : state) (C : execution_ctx) ((stat_for_7 (labs : label_set) (rv : resvalue) (eo2 : (option expr)) (eo3 : (option expr)) (t : stat) (R : res)) : ext_stat) (o : out)) ->
        (* ------------------------------------------ *)
        (red_stat (S : state) (C : execution_ctx) ((stat_for_6 (labs : label_set) (rv : resvalue) (eo2 : (option expr)) (eo3 : (option expr)) (t : stat) (R : res)) : ext_stat) (o : out))

  | red_stat_for_7_abort :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (labs : label_set (* input *)) (rv : resvalue (* input *)) (R : res (* input *)) (eo2 : (option expr) (* input *)) (eo3 : (option expr) (* input *)) (t : stat (* input *)),
        ((res_type (R : res)) <> (restype_normal : restype)) ->
        ((((res_type R) <> restype_continue) : Prop) \/ ((~ (res_label_in R labs)) : Prop)) ->
        (* ========================================== *)
        (* ------------------------------------------ *)
        (red_stat (S : state) (C : execution_ctx) ((stat_for_7 (labs : label_set) (rv : resvalue) (eo2 : (option expr)) (eo3 : (option expr)) (t : stat) (R : res)) : ext_stat) ((out_ter (S : state) (R : res)) : out))

  | red_stat_for_7_continue :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (labs : label_set (* input *)) (rv : resvalue (* input *)) (R : res (* input *)) (eo2 : (option expr) (* input *)) (eo3 : (option expr) (* input *)) (t : stat (* input *)) (o : out),
        ((((res_type R) = restype_normal) : Prop) \/ ((((res_type R) = restype_continue) /\ (res_label_in R labs)) : Prop)) ->
        (* ========================================== *)
        (red_stat (S : state) (C : execution_ctx) ((stat_for_8 (labs : label_set) (rv : resvalue) (eo2 : (option expr)) (eo3 : (option expr)) (t : stat)) : ext_stat) (o : out)) ->
        (* ------------------------------------------ *)
        (red_stat (S : state) (C : execution_ctx) ((stat_for_7 (labs : label_set) (rv : resvalue) (eo2 : (option expr)) (eo3 : (option expr)) (t : stat) (R : res)) : ext_stat) (o : out))

  | red_stat_for_8_none :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (labs : label_set (* input *)) (rv : resvalue (* input *)) (eo2 : (option expr) (* input *)) (t : stat (* input *)) (o : out),
        (* ========================================== *)
        (red_stat (S : state) (C : execution_ctx) ((stat_for_2 (labs : label_set) (rv : resvalue) (eo2 : (option expr)) (None : (option expr)) (t : stat)) : ext_stat) (o : out)) ->
        (* ------------------------------------------ *)
        (red_stat (S : state) (C : execution_ctx) ((stat_for_8 (labs : label_set) (rv : resvalue) (eo2 : (option expr)) (None : (option expr)) (t : stat)) : ext_stat) (o : out))

  | red_stat_for_8_some :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (labs : label_set (* input *)) (rv : resvalue (* input *)) (eo2 : (option expr) (* input *)) (e3 : expr (* input *)) (t : stat (* input *)) (o : out) (y1 : (specret value)),
        (* ========================================== *)
        (red_spec S C (spec_expr_get_value (e3 : expr)) y1) ->
        (red_stat (S : state) (C : execution_ctx) ((stat_for_9 (labs : label_set) (rv : resvalue) (eo2 : (option expr)) (e3 : expr) (y1 : (specret value)) (t : stat)) : ext_stat) (o : out)) ->
        (* ------------------------------------------ *)
        (red_stat (S : state) (C : execution_ctx) ((stat_for_8 (labs : label_set) (rv : resvalue) (eo2 : (option expr)) ((Some e3) : (option expr)) (t : stat)) : ext_stat) (o : out))

  | red_stat_for_9 :
      forall (S0 : state (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (labs : label_set (* input *)) (rv : resvalue (* input *)) (v : value (* input *)) (eo2 : (option expr) (* input *)) (e3 : expr (* input *)) (t : stat (* input *)) (o : out),
        (* ========================================== *)
        (red_stat (S : state) (C : execution_ctx) ((stat_for_2 (labs : label_set) (rv : resvalue) (eo2 : (option expr)) ((Some e3) : (option expr)) (t : stat)) : ext_stat) (o : out)) ->
        (* ------------------------------------------ *)
        (red_stat (S0 : state) (C : execution_ctx) ((stat_for_9 (labs : label_set) (rv : resvalue) (eo2 : (option expr)) (e3 : expr) ((specret_val (S : state) (v : value)) : (specret value)) (t : stat)) : ext_stat) (o : out))

  | red_stat_for_var :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (labs : label_set (* input *)) (ds : (list (string * (option expr))) (* input *)) (eo2 : (option expr) (* input *)) (eo3 : (option expr) (* input *)) (t : stat (* input *)) (o : out) (o1 : out),
        (* ========================================== *)
        (red_stat (S : state) (C : execution_ctx) ((stat_var_decl (ds : (list (string * (option expr))))) : ext_stat) (o1 : out)) ->
        (red_stat (S : state) (C : execution_ctx) ((stat_for_var_1 (o1 : out) (labs : label_set) (eo2 : (option expr)) (eo3 : (option expr)) (t : stat)) : ext_stat) (o : out)) ->
        (* ------------------------------------------ *)
        (red_stat (S : state) (C : execution_ctx) ((stat_for_var (labs : label_set) (ds : (list (string * (option expr)))) (eo2 : (option expr)) (eo3 : (option expr)) (t : stat)) : ext_stat) (o : out))

  | red_stat_for_var_1 :
      forall (S0 : state (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (R : res (* input *)) (labs : label_set (* input *)) (eo2 : (option expr) (* input *)) (eo3 : (option expr) (* input *)) (t : stat (* input *)) (o : out),
        (* ========================================== *)
        (red_stat (S : state) (C : execution_ctx) ((stat_for_2 (labs : label_set) (resvalue_empty : resvalue) (eo2 : (option expr)) (eo3 : (option expr)) (t : stat)) : ext_stat) (o : out)) ->
        (* ------------------------------------------ *)
        (red_stat (S0 : state) (C : execution_ctx) ((stat_for_var_1 ((out_ter (S : state) (R : res)) : out) (labs : label_set) (eo2 : (option expr)) (eo3 : (option expr)) (t : stat)) : ext_stat) (o : out))

  | red_stat_continue :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (lab : label (* input *)),
        (* ========================================== *)
        (* ------------------------------------------ *)
        (red_stat (S : state) (C : execution_ctx) ((stat_continue (lab : label)) : ext_stat) ((out_ter (S : state) ((res_continue (lab : label)) : res)) : out))

  | red_stat_break :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (lab : label (* input *)),
        (* ========================================== *)
        (* ------------------------------------------ *)
        (red_stat (S : state) (C : execution_ctx) ((stat_break (lab : label)) : ext_stat) ((out_ter (S : state) ((res_break (lab : label)) : res)) : out))

  | red_stat_return_none :
      forall (S : state (* input *)) (C : execution_ctx (* input *)),
        (* ========================================== *)
        (* ------------------------------------------ *)
        (red_stat (S : state) (C : execution_ctx) ((stat_return (None : (option expr))) : ext_stat) ((out_ter (S : state) ((res_return (undef : resvalue)) : res)) : out))

  | red_stat_return_some :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (e : expr (* input *)) (o : out) (y1 : (specret value)),
        (* ========================================== *)
        (red_spec S C (spec_expr_get_value (e : expr)) y1) ->
        (red_stat (S : state) (C : execution_ctx) ((stat_return_1 (y1 : (specret value))) : ext_stat) (o : out)) ->
        (* ------------------------------------------ *)
        (red_stat (S : state) (C : execution_ctx) ((stat_return ((Some e) : (option expr))) : ext_stat) (o : out))

  | red_stat_return_1 :
      forall (S0 : state (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (v : value (* input *)),
        (* ========================================== *)
        (* ------------------------------------------ *)
        (red_stat (S0 : state) (C : execution_ctx) ((stat_return_1 ((specret_val S v) : (specret value))) : ext_stat) ((out_ter (S : state) ((res_return (v : resvalue)) : res)) : out))

  | red_stat_with :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (e1 : expr (* input *)) (t2 : stat (* input *)) (y1 : (specret value)) (o : out),
        (* ========================================== *)
        (red_spec S C (spec_expr_get_value_conv (spec_to_object : (value -> ext_expr)) (e1 : expr)) y1) ->
        (red_stat (S : state) (C : execution_ctx) ((stat_with_1 (t2 : stat) (y1 : (specret value))) : ext_stat) (o : out)) ->
        (* ------------------------------------------ *)
        (red_stat (S : state) (C : execution_ctx) ((stat_with (e1 : expr) (t2 : stat)) : ext_stat) (o : out))

  | red_stat_with_1 :
      forall (S0 : state (* input *)) (S : state (* input *)) (S' : state) (C : execution_ctx (* input *)) (t2 : stat (* input *)) (l : object_loc (* input *)) (o : out) (lex : lexical_env) (lex' : lexical_env) (C' : execution_ctx),
        ((lex : lexical_env) = (execution_ctx_lexical_env (C : execution_ctx))) ->
        ((lex', S') = (lexical_env_alloc_object S lex l provide_this_true)) ->
        (C' = ((execution_ctx_with_lex (C : execution_ctx) (lex' : lexical_env)) : execution_ctx)) ->
        (* ========================================== *)
        (red_stat (S' : state) (C' : execution_ctx) (t2 : ext_stat) (o : out)) ->
        (* ------------------------------------------ *)
        (red_stat (S0 : state) (C : execution_ctx) ((stat_with_1 (t2 : stat) ((specret_val (S : state) (l : value)) : (specret value))) : ext_stat) (o : out))

  | red_stat_switch :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (e : expr (* input *)) (o : out) (sb : switchbody (* input *)) (labs : label_set (* input *)) (y1 : (specret value)),
        (* ========================================== *)
        (red_spec S C (spec_expr_get_value (e : expr)) y1) ->
        (red_stat (S : state) (C : execution_ctx) ((stat_switch_1 (y1 : (specret value)) (labs : label_set) (sb : switchbody)) : ext_stat) (o : out)) ->
        (* ------------------------------------------ *)
        (red_stat (S : state) (C : execution_ctx) ((stat_switch (labs : label_set) (e : expr) (sb : switchbody)) : ext_stat) (o : out))

  | red_stat_switch_1_nodefault :
      forall (S : state (* input *)) (S0 : state (* input *)) (C : execution_ctx (* input *)) (vi : value (* input *)) (o : out) (o1 : out) (scs : (list switchclause) (* input *)) (labs : label_set (* input *)),
        (* ========================================== *)
        (red_stat (S : state) (C : execution_ctx) ((stat_switch_nodefault_1 (vi : value) (resvalue_empty : resvalue) (scs : (list switchclause))) : ext_stat) (o1 : out)) ->
        (red_stat (S : state) (C : execution_ctx) ((stat_switch_2 (o1 : out) (labs : label_set)) : ext_stat) (o : out)) ->
        (* ------------------------------------------ *)
        (red_stat (S0 : state) (C : execution_ctx) ((stat_switch_1 ((specret_val S vi) : (specret value)) (labs : label_set) ((switchbody_nodefault (scs : (list switchclause))) : switchbody)) : ext_stat) (o : out))

  | red_stat_switch_1_default :
      forall (S : state (* input *)) (S0 : state (* input *)) (C : execution_ctx (* input *)) (o : out) (o1 : out) (vi : value (* input *)) (scs1 : (list switchclause) (* input *)) (scs2 : (list switchclause) (* input *)) (ts1 : (list stat) (* input *)) (labs : label_set (* input *)),
        (* ========================================== *)
        (red_stat (S : state) (C : execution_ctx) ((stat_switch_default_A_1 (false : bool) (vi : value) (resvalue_empty : resvalue) (scs1 : (list switchclause)) (ts1 : (list stat)) (scs2 : (list switchclause))) : ext_stat) (o1 : out)) ->
        (red_stat (S : state) (C : execution_ctx) ((stat_switch_2 (o1 : out) (labs : label_set)) : ext_stat) (o : out)) ->
        (* ------------------------------------------ *)
        (red_stat (S0 : state) (C : execution_ctx) ((stat_switch_1 ((specret_val S vi) : (specret value)) (labs : label_set) ((switchbody_withdefault (scs1 : (list switchclause)) (ts1 : (list stat)) (scs2 : (list switchclause))) : switchbody)) : ext_stat) (o : out))

  | red_stat_switch_2_break :
      forall (S : state (* input *)) (S0 : state (* input *)) (C : execution_ctx (* input *)) (R : res (* input *)) (rv : resvalue) (lab : label) (labs : label_set (* input *)),
        (R = ((res_intro (restype_break : restype) (rv : resvalue) (lab : label)) : res)) ->
        (res_label_in R labs) ->
        (* ========================================== *)
        (* ------------------------------------------ *)
        (red_stat (S0 : state) (C : execution_ctx) ((stat_switch_2 ((out_ter (S : state) (R : res)) : out) (labs : label_set)) : ext_stat) ((out_ter (S : state) ((res_normal (rv : resvalue)) : res)) : out))

  | red_stat_switch_2_normal :
      forall (S0 : state (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (rv : resvalue (* input *)) (labs : label_set (* input *)),
        (* ========================================== *)
        (* ------------------------------------------ *)
        (red_stat (S0 : state) (C : execution_ctx) ((stat_switch_2 ((out_ter (S : state) (rv : res)) : out) (labs : label_set)) : ext_stat) ((out_ter (S : state) (rv : res)) : out))

  | red_stat_switch_nodefault_1_nil :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (vi : value (* input *)) (rv : resvalue (* input *)) (o : out),
        (* ========================================== *)
        (red_stat (S : state) (C : execution_ctx) ((stat_switch_nodefault_5 (rv : resvalue) (nil : (list switchclause))) : ext_stat) (o : out)) ->
        (* ------------------------------------------ *)
        (red_stat (S : state) (C : execution_ctx) ((stat_switch_nodefault_1 (vi : value) (rv : resvalue) (nil : (list switchclause))) : ext_stat) (o : out))

  | red_stat_switch_nodefault_1_cons :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (e : expr (* input *)) (vi : value (* input *)) (rv : resvalue (* input *)) (ts : (list stat) (* input *)) (scs : (list switchclause) (* input *)) (o : out) (y1 : (specret value)),
        (* ========================================== *)
        (red_spec S C (spec_expr_get_value (e : expr)) y1) ->
        (red_stat (S : state) (C : execution_ctx) ((stat_switch_nodefault_2 (y1 : (specret value)) (vi : value) (rv : resvalue) (ts : (list stat)) (scs : (list switchclause))) : ext_stat) (o : out)) ->
        (* ------------------------------------------ *)
        (red_stat (S : state) (C : execution_ctx) ((stat_switch_nodefault_1 (vi : value) (rv : resvalue) (((switchclause_intro (e : expr) (ts : (list stat))) :: (scs : (list switchclause))) : (list switchclause))) : ext_stat) (o : out))

  | red_stat_switch_nodefault_2 :
      forall (S0 : state (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (b : bool) (vi : value (* input *)) (v1 : value (* input *)) (rv : resvalue (* input *)) (ts : (list stat) (* input *)) (scs : (list switchclause) (* input *)) (o : out),
        (b = ((strict_equality_test (v1 : value) (vi : value)) : bool)) ->
        (* ========================================== *)
        (red_stat (S : state) (C : execution_ctx) ((stat_switch_nodefault_3 (b : bool) (vi : value) (rv : resvalue) (ts : (list stat)) (scs : (list switchclause))) : ext_stat) (o : out)) ->
        (* ------------------------------------------ *)
        (red_stat (S0 : state) (C : execution_ctx) ((stat_switch_nodefault_2 ((specret_val S v1) : (specret value)) (vi : value) (rv : resvalue) (ts : (list stat)) (scs : (list switchclause))) : ext_stat) (o : out))

  | red_stat_switch_nodefault_3_false :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (vi : value (* input *)) (rv : resvalue (* input *)) (scs : (list switchclause) (* input *)) (ts : (list stat) (* input *)) (o : out),
        (* ========================================== *)
        (red_stat (S : state) (C : execution_ctx) ((stat_switch_nodefault_1 (vi : value) (rv : resvalue) (scs : (list switchclause))) : ext_stat) (o : out)) ->
        (* ------------------------------------------ *)
        (red_stat (S : state) (C : execution_ctx) ((stat_switch_nodefault_3 (false : bool) (vi : value) (rv : resvalue) (ts : (list stat)) (scs : (list switchclause))) : ext_stat) (o : out))

  | red_stat_switch_nodefault_3_true :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (ts : (list stat) (* input *)) (o : out) (o1 : out) (scs : (list switchclause) (* input *)) (vi : value (* input *)) (rv : resvalue (* input *)),
        (* ========================================== *)
        (red_stat (S : state) (C : execution_ctx) ((stat_block (ts : (list stat))) : ext_stat) (o1 : out)) ->
        (red_stat (S : state) (C : execution_ctx) ((stat_switch_nodefault_4 (o1 : out) (scs : (list switchclause))) : ext_stat) (o : out)) ->
        (* ------------------------------------------ *)
        (red_stat (S : state) (C : execution_ctx) ((stat_switch_nodefault_3 (true : bool) (vi : value) (rv : resvalue) (ts : (list stat)) (scs : (list switchclause))) : ext_stat) (o : out))

  | red_stat_switch_nodefault_4 :
      forall (S0 : state (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (rv : resvalue (* input *)) (scs : (list switchclause) (* input *)) (o : out),
        (* ========================================== *)
        (red_stat (S : state) (C : execution_ctx) ((stat_switch_nodefault_5 (rv : resvalue) (scs : (list switchclause))) : ext_stat) (o : out)) ->
        (* ------------------------------------------ *)
        (red_stat (S0 : state) (C : execution_ctx) ((stat_switch_nodefault_4 ((out_ter (S : state) (rv : res)) : out) (scs : (list switchclause))) : ext_stat) (o : out))

  | red_stat_switch_nodefault_5_nil :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (rv : resvalue (* input *)),
        (* ========================================== *)
        (* ------------------------------------------ *)
        (red_stat (S : state) (C : execution_ctx) ((stat_switch_nodefault_5 (rv : resvalue) (nil : (list switchclause))) : ext_stat) ((out_ter (S : state) (rv : res)) : out))

  | red_stat_switch_nodefault_5_cons :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (ts : (list stat) (* input *)) (o : out) (o1 : out) (scs : (list switchclause) (* input *)) (rv : resvalue (* input *)) (e : expr (* input *)),
        (* ========================================== *)
        (red_stat (S : state) (C : execution_ctx) ((stat_block (ts : (list stat))) : ext_stat) (o1 : out)) ->
        (red_stat (S : state) (C : execution_ctx) ((stat_switch_nodefault_6 (rv : resvalue) (o1 : out) (scs : (list switchclause))) : ext_stat) (o : out)) ->
        (* ------------------------------------------ *)
        (red_stat (S : state) (C : execution_ctx) ((stat_switch_nodefault_5 (rv : resvalue) (((switchclause_intro (e : expr) (ts : (list stat))) :: (scs : (list switchclause))) : (list switchclause))) : ext_stat) (o : out))

  | red_stat_switch_nodefault_6_normal :
      forall (S0 : state (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (R : res (* input *)) (rv : resvalue (* input *)) (rv' : resvalue) (scs : (list switchclause) (* input *)) (o : out),
        (rv' = ((ifb ((res_value (R : res)) <> (resvalue_empty : resvalue)) then ((res_value (R : res)) : resvalue) else rv) : resvalue)) ->
        (* ========================================== *)
        (red_stat (S : state) (C : execution_ctx) ((stat_switch_nodefault_5 (rv' : resvalue) (scs : (list switchclause))) : ext_stat) (o : out)) ->
        (* ------------------------------------------ *)
        (red_stat (S0 : state) (C : execution_ctx) ((stat_switch_nodefault_6 (rv : resvalue) ((out_ter (S : state) (R : res)) : out) (scs : (list switchclause))) : ext_stat) (o : out))

  | red_stat_switch_nodefault_6_abrupt :
      forall (S : state (* input *)) (S0 : state (* input *)) (C : execution_ctx (* input *)) (R : res (* input *)) (R' : res) (scs : (list switchclause) (* input *)) (rv : resvalue (* input *)),
        (abrupt_res (R : res)) ->
        ((res_type (R : res)) <> (restype_throw : restype)) ->
        (R' = ((res_overwrite_value_if_empty (rv : resvalue) (R : res)) : res)) ->
        (* ========================================== *)
        (* ------------------------------------------ *)
        (red_stat (S0 : state) (C : execution_ctx) ((stat_switch_nodefault_6 (rv : resvalue) ((out_ter (S : state) (R : res)) : out) (scs : (list switchclause))) : ext_stat) ((out_ter (S : state) (R' : res)) : out))

  | red_stat_switch_default_A_1_nil_true :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (vi : value (* input *)) (rv : resvalue (* input *)) (ts1 : (list stat) (* input *)) (scs2 : (list switchclause) (* input *)) (o : out),
        (* ========================================== *)
        (red_stat (S : state) (C : execution_ctx) ((stat_switch_default_5 (vi : value) (rv : resvalue) (ts1 : (list stat)) (scs2 : (list switchclause))) : ext_stat) (o : out)) ->
        (* ------------------------------------------ *)
        (red_stat (S : state) (C : execution_ctx) ((stat_switch_default_A_1 (true : bool) (vi : value) (rv : resvalue) (nil : (list switchclause)) (ts1 : (list stat)) (scs2 : (list switchclause))) : ext_stat) (o : out))

  | red_stat_switch_default_A_1_nil_false :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (vi : value (* input *)) (rv : resvalue (* input *)) (ts1 : (list stat) (* input *)) (scs2 : (list switchclause) (* input *)) (o : out),
        (* ========================================== *)
        (red_stat (S : state) (C : execution_ctx) ((stat_switch_default_B_1 (vi : value) (rv : resvalue) (ts1 : (list stat)) (scs2 : (list switchclause))) : ext_stat) (o : out)) ->
        (* ------------------------------------------ *)
        (red_stat (S : state) (C : execution_ctx) ((stat_switch_default_A_1 (false : bool) (vi : value) (rv : resvalue) (nil : (list switchclause)) (ts1 : (list stat)) (scs2 : (list switchclause))) : ext_stat) (o : out))

  | red_stat_switch_default_A_1_cons_true :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (e : expr (* input *)) (o : out) (vi : value (* input *)) (rv : resvalue (* input *)) (ts : (list stat) (* input *)) (ts1 : (list stat) (* input *)) (scs : (list switchclause) (* input *)) (scs2 : (list switchclause) (* input *)),
        (* ========================================== *)
        (red_stat (S : state) (C : execution_ctx) ((stat_switch_default_A_4 (rv : resvalue) (vi : value) (ts : (list stat)) (scs : (list switchclause)) (ts1 : (list stat)) (scs2 : (list switchclause))) : ext_stat) (o : out)) ->
        (* ------------------------------------------ *)
        (red_stat (S : state) (C : execution_ctx) ((stat_switch_default_A_1 (true : bool) (vi : value) (rv : resvalue) (((switchclause_intro (e : expr) (ts : (list stat))) :: (scs : (list switchclause))) : (list switchclause)) (ts1 : (list stat)) (scs2 : (list switchclause))) : ext_stat) (o : out))

  | red_stat_switch_default_A_1_cons_false :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (e : expr (* input *)) (vi : value (* input *)) (rv : resvalue (* input *)) (ts : (list stat) (* input *)) (ts1 : (list stat) (* input *)) (scs : (list switchclause) (* input *)) (scs2 : (list switchclause) (* input *)) (y1 : (specret value)) (o : out),
        (* ========================================== *)
        (red_spec S C (spec_expr_get_value (e : expr)) y1) ->
        (red_stat (S : state) (C : execution_ctx) ((stat_switch_default_A_2 (y1 : (specret value)) (vi : value) (rv : resvalue) (ts : (list stat)) (scs : (list switchclause)) (ts1 : (list stat)) (scs2 : (list switchclause))) : ext_stat) (o : out)) ->
        (* ------------------------------------------ *)
        (red_stat (S : state) (C : execution_ctx) ((stat_switch_default_A_1 (false : bool) (vi : value) (rv : resvalue) (((switchclause_intro (e : expr) (ts : (list stat))) :: (scs : (list switchclause))) : (list switchclause)) (ts1 : (list stat)) (scs2 : (list switchclause))) : ext_stat) (o : out))

  | red_stat_switch_default_A_2 :
      forall (S0 : state (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (b : bool) (vi : value (* input *)) (v1 : value (* input *)) (rv : resvalue (* input *)) (ts : (list stat) (* input *)) (scs : (list switchclause) (* input *)) (ts1 : (list stat) (* input *)) (scs2 : (list switchclause) (* input *)) (o : out),
        (b = ((strict_equality_test (v1 : value) (vi : value)) : bool)) ->
        (* ========================================== *)
        (red_stat (S : state) (C : execution_ctx) ((stat_switch_default_A_3 (b : bool) (vi : value) (rv : resvalue) (ts : (list stat)) (scs : (list switchclause)) (ts1 : (list stat)) (scs2 : (list switchclause))) : ext_stat) (o : out)) ->
        (* ------------------------------------------ *)
        (red_stat (S0 : state) (C : execution_ctx) ((stat_switch_default_A_2 ((specret_val S v1) : (specret value)) (vi : value) (rv : resvalue) (ts : (list stat)) (scs : (list switchclause)) (ts1 : (list stat)) (scs2 : (list switchclause))) : ext_stat) (o : out))

  | red_stat_switch_default_A_3_false :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (vi : value (* input *)) (rv : resvalue (* input *)) (scs : (list switchclause) (* input *)) (ts : (list stat) (* input *)) (ts1 : (list stat) (* input *)) (scs2 : (list switchclause) (* input *)) (o : out),
        (* ========================================== *)
        (red_stat (S : state) (C : execution_ctx) ((stat_switch_default_A_1 (false : bool) (vi : value) (rv : resvalue) (scs : (list switchclause)) (ts1 : (list stat)) (scs2 : (list switchclause))) : ext_stat) (o : out)) ->
        (* ------------------------------------------ *)
        (red_stat (S : state) (C : execution_ctx) ((stat_switch_default_A_3 (false : bool) (vi : value) (rv : resvalue) (ts : (list stat)) (scs : (list switchclause)) (ts1 : (list stat)) (scs2 : (list switchclause))) : ext_stat) (o : out))

  | red_stat_switch_default_A_3_true :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (vi : value (* input *)) (rv : resvalue (* input *)) (scs : (list switchclause) (* input *)) (ts : (list stat) (* input *)) (ts1 : (list stat) (* input *)) (scs2 : (list switchclause) (* input *)) (o : out),
        (* ========================================== *)
        (red_stat (S : state) (C : execution_ctx) ((stat_switch_default_A_4 (rv : resvalue) (vi : value) (ts : (list stat)) (scs : (list switchclause)) (ts1 : (list stat)) (scs2 : (list switchclause))) : ext_stat) (o : out)) ->
        (* ------------------------------------------ *)
        (red_stat (S : state) (C : execution_ctx) ((stat_switch_default_A_3 (true : bool) (vi : value) (rv : resvalue) (ts : (list stat)) (scs : (list switchclause)) (ts1 : (list stat)) (scs2 : (list switchclause))) : ext_stat) (o : out))

  | red_stat_switch_default_A_4 :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (o1 : out) (rv : resvalue (* input *)) (ts : (list stat) (* input *)) (scs : (list switchclause) (* input *)) (ts1 : (list stat) (* input *)) (scs2 : (list switchclause) (* input *)) (o : out) (vi : value (* input *)),
        (* ========================================== *)
        (red_stat (S : state) (C : execution_ctx) ((stat_block (ts : (list stat))) : ext_stat) (o1 : out)) ->
        (red_stat (S : state) (C : execution_ctx) ((stat_switch_default_A_5 (rv : resvalue) (o1 : out) (vi : value) (scs : (list switchclause)) (ts1 : (list stat)) (scs2 : (list switchclause))) : ext_stat) (o : out)) ->
        (* ------------------------------------------ *)
        (red_stat (S : state) (C : execution_ctx) ((stat_switch_default_A_4 (rv : resvalue) (vi : value) (ts : (list stat)) (scs : (list switchclause)) (ts1 : (list stat)) (scs2 : (list switchclause))) : ext_stat) (o : out))

  | red_stat_switch_default_A_5 :
      forall (S : state (* input *)) (S0 : state (* input *)) (C : execution_ctx (* input *)) (vi : value (* input *)) (rv0 : resvalue (* input *)) (rv : resvalue (* input *)) (rv' : resvalue) (scs : (list switchclause) (* input *)) (scs2 : (list switchclause) (* input *)) (ts1 : (list stat) (* input *)) (o : out),
        (rv' = ((ifb (rv <> (resvalue_empty : resvalue)) then (rv : resvalue) else rv0) : resvalue)) ->
        (* ========================================== *)
        (red_stat (S : state) (C : execution_ctx) ((stat_switch_default_A_1 (true : bool) (vi : value) (rv' : resvalue) (scs : (list switchclause)) (ts1 : (list stat)) (scs2 : (list switchclause))) : ext_stat) (o : out)) ->
        (* ------------------------------------------ *)
        (red_stat (S0 : state) (C : execution_ctx) ((stat_switch_default_A_5 (rv0 : resvalue) ((out_ter (S : state) (rv : res)) : out) (vi : value) (scs : (list switchclause)) (ts1 : (list stat)) (scs2 : (list switchclause))) : ext_stat) (o : out))

  | red_stat_switch_default_A_5_abrupt :
      forall (S : state (* input *)) (S0 : state (* input *)) (C : execution_ctx (* input *)) (vi : value (* input *)) (rv : resvalue (* input *)) (R : res (* input *)) (scs : (list switchclause) (* input *)) (scs2 : (list switchclause) (* input *)) (ts1 : (list stat) (* input *)),
        (abrupt_res (R : res)) ->
        ((res_type (R : res)) <> (restype_throw : restype)) ->
        (* ========================================== *)
        (* ------------------------------------------ *)
        (red_stat (S0 : state) (C : execution_ctx) ((stat_switch_default_A_5 (rv : resvalue) ((out_ter (S : state) (R : res)) : out) (vi : value) (scs : (list switchclause)) (ts1 : (list stat)) (scs2 : (list switchclause))) : ext_stat) ((out_ter (S : state) ((res_overwrite_value_if_empty (rv : resvalue) (R : res)) : res)) : out))

  | red_stat_switch_default_B_1_nil :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (vi : value (* input *)) (rv : resvalue (* input *)) (ts1 : (list stat) (* input *)) (o : out),
        (* ========================================== *)
        (red_stat (S : state) (C : execution_ctx) ((stat_switch_default_5 (vi : value) (rv : resvalue) (ts1 : (list stat)) (nil : (list switchclause))) : ext_stat) (o : out)) ->
        (* ------------------------------------------ *)
        (red_stat (S : state) (C : execution_ctx) ((stat_switch_default_B_1 (vi : value) (rv : resvalue) (ts1 : (list stat)) (nil : (list switchclause))) : ext_stat) (o : out))

  | red_stat_switch_default_B_1_cons :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (e : expr (* input *)) (o : out) (vi : value (* input *)) (rv : resvalue (* input *)) (ts : (list stat) (* input *)) (ts1 : (list stat) (* input *)) (scs : (list switchclause) (* input *)) (y1 : (specret value)),
        (* ========================================== *)
        (red_spec S C (spec_expr_get_value (e : expr)) y1) ->
        (red_stat (S : state) (C : execution_ctx) ((stat_switch_default_B_2 (y1 : (specret value)) (vi : value) (rv : resvalue) (ts : (list stat)) (ts1 : (list stat)) (scs : (list switchclause))) : ext_stat) (o : out)) ->
        (* ------------------------------------------ *)
        (red_stat (S : state) (C : execution_ctx) ((stat_switch_default_B_1 (vi : value) (rv : resvalue) (ts1 : (list stat)) (((switchclause_intro (e : expr) (ts : (list stat))) :: (scs : (list switchclause))) : (list switchclause))) : ext_stat) (o : out))

  | red_stat_switch_default_B_2 :
      forall (S : state (* input *)) (S0 : state (* input *)) (C : execution_ctx (* input *)) (b : bool) (vi : value (* input *)) (v1 : value (* input *)) (rv : resvalue (* input *)) (ts : (list stat) (* input *)) (scs : (list switchclause) (* input *)) (ts1 : (list stat) (* input *)) (o : out),
        (b = ((strict_equality_test (v1 : value) (vi : value)) : bool)) ->
        (* ========================================== *)
        (red_stat (S : state) (C : execution_ctx) ((stat_switch_default_B_3 (b : bool) (vi : value) (rv : resvalue) (ts : (list stat)) (ts1 : (list stat)) (scs : (list switchclause))) : ext_stat) (o : out)) ->
        (* ------------------------------------------ *)
        (red_stat (S0 : state) (C : execution_ctx) ((stat_switch_default_B_2 ((specret_val S v1) : (specret value)) (vi : value) (rv : resvalue) (ts : (list stat)) (ts1 : (list stat)) (scs : (list switchclause))) : ext_stat) (o : out))

  | red_stat_switch_default_B_3_false :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (vi : value (* input *)) (rv : resvalue (* input *)) (scs : (list switchclause) (* input *)) (ts : (list stat) (* input *)) (ts1 : (list stat) (* input *)) (o : out),
        (* ========================================== *)
        (red_stat (S : state) (C : execution_ctx) ((stat_switch_default_B_1 (vi : value) (rv : resvalue) (ts1 : (list stat)) (scs : (list switchclause))) : ext_stat) (o : out)) ->
        (* ------------------------------------------ *)
        (red_stat (S : state) (C : execution_ctx) ((stat_switch_default_B_3 (false : bool) (vi : value) (rv : resvalue) (ts : (list stat)) (ts1 : (list stat)) (scs : (list switchclause))) : ext_stat) (o : out))

  | red_stat_switch_default_B_3_true :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (o1 : out) (rv : resvalue (* input *)) (ts : (list stat) (* input *)) (scs : (list switchclause) (* input *)) (ts1 : (list stat) (* input *)) (o : out) (vi : value (* input *)),
        (* ========================================== *)
        (red_stat (S : state) (C : execution_ctx) ((stat_block (ts : (list stat))) : ext_stat) (o1 : out)) ->
        (red_stat (S : state) (C : execution_ctx) ((stat_switch_default_B_4 (o1 : out) (ts1 : (list stat)) (scs : (list switchclause))) : ext_stat) (o : out)) ->
        (* ------------------------------------------ *)
        (red_stat (S : state) (C : execution_ctx) ((stat_switch_default_B_3 (true : bool) (vi : value) (rv : resvalue) (ts : (list stat)) (ts1 : (list stat)) (scs : (list switchclause))) : ext_stat) (o : out))

  | red_stat_switch_default_B_4 :
      forall (S : state (* input *)) (S0 : state (* input *)) (C : execution_ctx (* input *)) (rv : resvalue (* input *)) (scs : (list switchclause) (* input *)) (ts1 : (list stat) (* input *)) (o : out),
        (* ========================================== *)
        (red_stat (S : state) (C : execution_ctx) ((stat_switch_default_7 (rv : resvalue) (scs : (list switchclause))) : ext_stat) (o : out)) ->
        (* ------------------------------------------ *)
        (red_stat (S0 : state) (C : execution_ctx) ((stat_switch_default_B_4 ((out_ter (S : state) (rv : res)) : out) (ts1 : (list stat)) (scs : (list switchclause))) : ext_stat) (o : out))

  | red_stat_switch_default_5 :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (o : out) (o1 : out) (ts : (list stat) (* input *)) (vi : value (* input *)) (rv : resvalue (* input *)) (scs : (list switchclause) (* input *)),
        (* ========================================== *)
        (red_stat (S : state) (C : execution_ctx) ((stat_block (ts : (list stat))) : ext_stat) (o1 : out)) ->
        (red_stat (S : state) (C : execution_ctx) ((stat_switch_default_6 (o1 : out) (scs : (list switchclause))) : ext_stat) (o : out)) ->
        (* ------------------------------------------ *)
        (red_stat (S : state) (C : execution_ctx) ((stat_switch_default_5 (vi : value) (rv : resvalue) (ts : (list stat)) (scs : (list switchclause))) : ext_stat) (o : out))

  | red_stat_switch_default_6 :
      forall (S : state (* input *)) (S0 : state (* input *)) (C : execution_ctx (* input *)) (o : out) (rv : resvalue (* input *)) (scs : (list switchclause) (* input *)),
        (* ========================================== *)
        (red_stat (S : state) (C : execution_ctx) ((stat_switch_default_7 (rv : resvalue) (scs : (list switchclause))) : ext_stat) (o : out)) ->
        (* ------------------------------------------ *)
        (red_stat (S0 : state) (C : execution_ctx) ((stat_switch_default_6 ((out_ter (S : state) (rv : res)) : out) (scs : (list switchclause))) : ext_stat) (o : out))

  | red_stat_switch_default_7_nil :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (rv : resvalue (* input *)),
        (* ========================================== *)
        (* ------------------------------------------ *)
        (red_stat (S : state) (C : execution_ctx) ((stat_switch_default_7 (rv : resvalue) (nil : (list switchclause))) : ext_stat) ((out_ter (S : state) (rv : res)) : out))

  | red_stat_switch_default_7_cons :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (ts : (list stat) (* input *)) (rv : resvalue (* input *)) (o : out) (o1 : out) (scs : (list switchclause) (* input *)) (e : expr (* input *)),
        (* ========================================== *)
        (red_stat (S : state) (C : execution_ctx) ((stat_block (ts : (list stat))) : ext_stat) (o1 : out)) ->
        (red_stat (S : state) (C : execution_ctx) ((stat_switch_default_8 (rv : resvalue) (o1 : out) (scs : (list switchclause))) : ext_stat) (o : out)) ->
        (* ------------------------------------------ *)
        (red_stat (S : state) (C : execution_ctx) ((stat_switch_default_7 (rv : resvalue) (((switchclause_intro (e : expr) (ts : (list stat))) :: (scs : (list switchclause))) : (list switchclause))) : ext_stat) (o : out))

  | red_stat_switch_default_8_normal :
      forall (S : state (* input *)) (S0 : state (* input *)) (C : execution_ctx (* input *)) (rv0 : resvalue (* input *)) (rv : resvalue (* input *)) (rv' : resvalue) (scs : (list switchclause) (* input *)) (o : out),
        (rv' = ((ifb (rv <> (resvalue_empty : resvalue)) then (rv : resvalue) else rv0) : resvalue)) ->
        (* ========================================== *)
        (red_stat (S : state) (C : execution_ctx) ((stat_switch_default_7 (rv' : resvalue) (scs : (list switchclause))) : ext_stat) (o : out)) ->
        (* ------------------------------------------ *)
        (red_stat (S0 : state) (C : execution_ctx) ((stat_switch_default_8 (rv0 : resvalue) ((out_ter (S : state) (rv : res)) : out) (scs : (list switchclause))) : ext_stat) (o : out))

  | red_stat_switch_default_8_abrupt :
      forall (S : state (* input *)) (S0 : state (* input *)) (C : execution_ctx (* input *)) (R : res (* input *)) (scs : (list switchclause) (* input *)) (rv : resvalue (* input *)),
        (abrupt_res (R : res)) ->
        ((res_type (R : res)) <> (restype_throw : restype)) ->
        (* ========================================== *)
        (* ------------------------------------------ *)
        (red_stat (S0 : state) (C : execution_ctx) ((stat_switch_default_8 (rv : resvalue) ((out_ter (S : state) (R : res)) : out) (scs : (list switchclause))) : ext_stat) ((out_ter (S : state) ((res_overwrite_value_if_empty (rv : resvalue) (R : res)) : res)) : out))

  | red_stat_label :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (slab : string (* input *)) (t : stat (* input *)) (o1 : out) (o : out),
        (* ========================================== *)
        (red_stat (S : state) (C : execution_ctx) (t : ext_stat) (o1 : out)) ->
        (red_stat (S : state) (C : execution_ctx) ((stat_label_1 ((label_string (slab : string)) : label) (o1 : out)) : ext_stat) (o : out)) ->
        (* ------------------------------------------ *)
        (red_stat (S : state) (C : execution_ctx) ((stat_label (slab : string) (t : stat)) : ext_stat) (o : out))

  | red_stat_label_1_normal :
      forall (S0 : state (* input *)) (S : state (* input *)) (lab : label (* input *)) (C : execution_ctx (* input *)) (R : res (* input *)),
        ((res_type (R : res)) = (restype_normal : restype)) ->
        (* ========================================== *)
        (* ------------------------------------------ *)
        (red_stat (S0 : state) (C : execution_ctx) ((stat_label_1 (lab : label) ((out_ter (S : state) (R : res)) : out)) : ext_stat) ((out_ter (S : state) (R : res)) : out))

  | red_stat_label_1_break_eq :
      forall (S0 : state (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (R : res (* input *)) (rv : resvalue) (lab : label (* input *)),
        (R = ((res_intro (restype_break : restype) (rv : resvalue) (lab : label)) : res)) ->
        (* ========================================== *)
        (* ------------------------------------------ *)
        (red_stat (S0 : state) (C : execution_ctx) ((stat_label_1 (lab : label) ((out_ter (S : state) (R : res)) : out)) : ext_stat) ((out_ter (S : state) ((res_normal (rv : resvalue)) : res)) : out))

  | red_stat_throw :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (e : expr (* input *)) (o : out) (y1 : (specret value)),
        (* ========================================== *)
        (red_spec S C (spec_expr_get_value (e : expr)) y1) ->
        (red_stat (S : state) (C : execution_ctx) ((stat_throw_1 (y1 : (specret value))) : ext_stat) (o : out)) ->
        (* ------------------------------------------ *)
        (red_stat (S : state) (C : execution_ctx) ((stat_throw (e : expr)) : ext_stat) (o : out))

  | red_stat_throw_1 :
      forall (S0 : state (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (v : value (* input *)),
        (* ========================================== *)
        (* ------------------------------------------ *)
        (red_stat (S0 : state) (C : execution_ctx) ((stat_throw_1 ((specret_val S v) : (specret value))) : ext_stat) ((out_ter (S : state) ((res_throw (v : resvalue)) : res)) : out))

  | red_stat_try :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (t : stat (* input *)) (co : (option (string * stat)) (* input *)) (fo : (option stat) (* input *)) (o : out) (o1 : out),
        (* ========================================== *)
        (red_stat (S : state) (C : execution_ctx) (t : ext_stat) (o1 : out)) ->
        (red_stat (S : state) (C : execution_ctx) ((stat_try_1 (o1 : out) (co : (option (string * stat))) (fo : (option stat))) : ext_stat) (o : out)) ->
        (* ------------------------------------------ *)
        (red_stat (S : state) (C : execution_ctx) ((stat_try (t : stat) (co : (option (string * stat))) (fo : (option stat))) : ext_stat) (o : out))

  | red_stat_try_1_no_throw :
      forall (S0 : state (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (R : res (* input *)) (co : (option (string * stat)) (* input *)) (fo : (option stat) (* input *)) (o : out),
        ((res_type (R : res)) <> (restype_throw : restype)) ->
        (* ========================================== *)
        (red_stat (S : state) (C : execution_ctx) ((stat_try_4 (R : res) (fo : (option stat))) : ext_stat) (o : out)) ->
        (* ------------------------------------------ *)
        (red_stat (S0 : state) (C : execution_ctx) ((stat_try_1 ((out_ter (S : state) (R : res)) : out) (co : (option (string * stat))) (fo : (option stat))) : ext_stat) (o : out))

  | red_stat_try_1_throw_no_catch :
      forall (S0 : state (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (R : res (* input *)) (fo : (option stat) (* input *)) (o : out),
        ((res_type (R : res)) = (restype_throw : restype)) ->
        (* ========================================== *)
        (red_stat (S : state) (C : execution_ctx) ((stat_try_4 (R : res) (fo : (option stat))) : ext_stat) (o : out)) ->
        (* ------------------------------------------ *)
        (red_stat (S0 : state) (C : execution_ctx) ((stat_try_1 ((out_ter (S : state) (R : res)) : out) (None : (option (string * stat))) (fo : (option stat))) : ext_stat) (o : out))

  | red_stat_try_1_throw_catch :
      forall (v : value) (S0 : state (* input *)) (S : state (* input *)) (S' : state) (C : execution_ctx (* input *)) (lex : lexical_env) (lex' : lexical_env) (oldlex : (list env_loc)) (L : env_loc) (x : prop_name (* input *)) (R : res (* input *)) (t1 : stat (* input *)) (fo : (option stat) (* input *)) (o1 : out) (o : out),
        ((res_type (R : res)) = (restype_throw : restype)) ->
        ((lex : lexical_env) = (execution_ctx_lexical_env (C : execution_ctx))) ->
        ((lex', S') = (lexical_env_alloc_decl S lex)) ->
        ((lex' : (list env_loc)) = (L :: (oldlex : (list env_loc)))) ->
        ((res_value (R : res)) = ((resvalue_value (v : value)) : resvalue)) ->
        (* ========================================== *)
        (red_expr (S' : state) (C : execution_ctx) ((spec_env_record_create_set_mutable_binding (L : env_loc) (x : prop_name) (None : (option bool)) (v : value) (throw_irrelevant : bool)) : ext_expr) (o1 : out)) ->
        (red_stat (S' : state) (C : execution_ctx) ((stat_try_2 (o1 : out) (lex' : lexical_env) (t1 : stat) (fo : (option stat))) : ext_stat) (o : out)) ->
        (* ------------------------------------------ *)
        (red_stat (S0 : state) (C : execution_ctx) ((stat_try_1 ((out_ter (S : state) (R : res)) : out) ((Some (x, t1)) : (option (string * stat))) (fo : (option stat))) : ext_stat) (o : out))

  | red_stat_try_2_catch :
      forall (C : execution_ctx (* input *)) (S0 : state (* input *)) (S : state (* input *)) (lex' : lexical_env (* input *)) (t1 : stat (* input *)) (fo : (option stat) (* input *)) (o : out) (o1 : out),
        (* ========================================== *)
        (red_stat (S : state) ((execution_ctx_with_lex (C : execution_ctx) (lex' : lexical_env)) : execution_ctx) (t1 : ext_stat) (o1 : out)) ->
        (red_stat (S : state) (C : execution_ctx) ((stat_try_3 (o1 : out) (fo : (option stat))) : ext_stat) (o : out)) ->
        (* ------------------------------------------ *)
        (red_stat (S0 : state) (C : execution_ctx) ((stat_try_2 ((out_ter (S : state) (res_intro restype_normal resvalue_empty label_empty)) : out) (lex' : lexical_env) (t1 : stat) (fo : (option stat))) : ext_stat) (o : out))

  | red_stat_try_3_catch_result :
      forall (S0 : state (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (R : res (* input *)) (fo : (option stat) (* input *)) (o : out),
        (* ========================================== *)
        (red_stat (S : state) (C : execution_ctx) ((stat_try_4 (R : res) (fo : (option stat))) : ext_stat) (o : out)) ->
        (* ------------------------------------------ *)
        (red_stat (S0 : state) (C : execution_ctx) ((stat_try_3 ((out_ter (S : state) (R : res)) : out) (fo : (option stat))) : ext_stat) (o : out))

  | red_stat_try_4_no_finally :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (R : res (* input *)),
        (* ========================================== *)
        (* ------------------------------------------ *)
        (red_stat (S : state) (C : execution_ctx) ((stat_try_4 (R : res) (None : (option stat))) : ext_stat) ((out_ter (S : state) (R : res)) : out))

  | red_stat_try_4_finally :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (R : res (* input *)) (t1 : stat (* input *)) (o : out) (o1 : out),
        (* ========================================== *)
        (red_stat (S : state) (C : execution_ctx) (t1 : ext_stat) (o1 : out)) ->
        (red_stat (S : state) (C : execution_ctx) ((stat_try_5 (R : res) (o1 : out)) : ext_stat) (o : out)) ->
        (* ------------------------------------------ *)
        (red_stat (S : state) (C : execution_ctx) ((stat_try_4 (R : res) ((Some t1) : (option stat))) : ext_stat) (o : out))

  | red_stat_try_5_finally_result :
      forall (S0 : state (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (R : res (* input *)) (rv : resvalue (* input *)),
        (* ========================================== *)
        (* ------------------------------------------ *)
        (red_stat (S0 : state) (C : execution_ctx) ((stat_try_5 (R : res) ((out_ter (S : state) (rv : res)) : out)) : ext_stat) ((out_ter (S : state) (R : res)) : out))

  | red_stat_debugger :
      forall (S : state (* input *)) (C : execution_ctx (* input *)),
        (* ========================================== *)
        (* ------------------------------------------ *)
        (red_stat (S : state) (C : execution_ctx) (stat_debugger : ext_stat) ((out_ter (S : state) (res_empty : res)) : out))


with red_expr : state (* input *) -> execution_ctx (* input *) -> ext_expr (* input *) -> out -> Prop :=

  | red_expr_abort :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (exte : ext_expr (* input *)) (o : out),
        ((out_of_ext_expr (exte : ext_expr)) = ((Some o) : (option out))) ->
        (abort (o : out)) ->
        (~ (abort_intercepted_expr (exte : ext_expr))) ->
        (* ========================================== *)
        (* ------------------------------------------ *)
        (red_expr (S : state) (C : execution_ctx) (exte : ext_expr) (o : out))

  | red_expr_this :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (v : value),
        (v = ((execution_ctx_this_binding (C : execution_ctx)) : value)) ->
        (* ========================================== *)
        (* ------------------------------------------ *)
        (red_expr (S : state) (C : execution_ctx) (expr_this : ext_expr) ((out_ter (S : state) (v : res)) : out))

  | red_expr_identifier :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (x : prop_name (* input *)) (y1 : (specret ref)) (o : out),
        (* ========================================== *)
        (red_spec S C (spec_identifier_resolution (C : execution_ctx) (x : prop_name)) y1) ->
        (red_expr (S : state) (C : execution_ctx) ((expr_identifier_1 (y1 : (specret ref))) : ext_expr) (o : out)) ->
        (* ------------------------------------------ *)
        (red_expr (S : state) (C : execution_ctx) ((expr_identifier (x : string)) : ext_expr) (o : out))

  | red_expr_identifier_1 :
      forall (S0 : state (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (r : ref (* input *)),
        (* ========================================== *)
        (* ------------------------------------------ *)
        (red_expr (S0 : state) (C : execution_ctx) ((expr_identifier_1 ((specret_val S r) : (specret ref))) : ext_expr) ((out_ter (S : state) (r : res)) : out))

  | red_expr_literal :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (i : literal (* input *)) (v : value),
        (v = ((convert_literal_to_prim i) : value)) ->
        (* ========================================== *)
        (* ------------------------------------------ *)
        (red_expr (S : state) (C : execution_ctx) ((expr_literal (i : literal)) : ext_expr) ((out_ter (S : state) (v : res)) : out))

  | red_expr_object :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (pds : (list (propname * propbody)) (* input *)) (o1 : out) (o : out),
        (* ========================================== *)
        (red_expr (S : state) (C : execution_ctx) ((spec_construct_prealloc (prealloc_object : prealloc) (nil : (list value))) : ext_expr) (o1 : out)) ->
        (red_expr (S : state) (C : execution_ctx) ((expr_object_0 (o1 : out) (pds : propdefs)) : ext_expr) (o : out)) ->
        (* ------------------------------------------ *)
        (red_expr (S : state) (C : execution_ctx) ((expr_object (pds : (list (propname * propbody)))) : ext_expr) (o : out))

  | red_expr_object_0 :
      forall (S0 : state (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (l : object_loc (* input *)) (pds : propdefs (* input *)) (o : out),
        (* ========================================== *)
        (red_expr (S : state) (C : execution_ctx) ((expr_object_1 (l : object_loc) (pds : propdefs)) : ext_expr) (o : out)) ->
        (* ------------------------------------------ *)
        (red_expr (S0 : state) (C : execution_ctx) ((expr_object_0 ((out_ter (S : state) (l : res)) : out) (pds : propdefs)) : ext_expr) (o : out))

  | red_expr_object_1_nil :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (l : object_loc (* input *)),
        (* ========================================== *)
        (* ------------------------------------------ *)
        (red_expr (S : state) (C : execution_ctx) ((expr_object_1 (l : object_loc) (nil : propdefs)) : ext_expr) ((out_ter (S : state) (l : res)) : out))

  | red_expr_object_1_cons :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (x : prop_name) (l : object_loc (* input *)) (pn : propname (* input *)) (pb : propbody (* input *)) (pds : propdefs (* input *)) (o : out),
        (x = ((string_of_propname (pn : propname)) : prop_name)) ->
        (* ========================================== *)
        (red_expr (S : state) (C : execution_ctx) ((expr_object_2 (l : object_loc) (x : string) (pb : propbody) (pds : propdefs)) : ext_expr) (o : out)) ->
        (* ------------------------------------------ *)
        (red_expr (S : state) (C : execution_ctx) ((expr_object_1 (l : object_loc) (((pn, pb) :: pds) : propdefs)) : ext_expr) (o : out))

  | red_expr_object_2_val :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (e : expr (* input *)) (l : object_loc (* input *)) (x : prop_name (* input *)) (pds : propdefs (* input *)) (y1 : (specret value)) (o : out),
        (* ========================================== *)
        (red_spec S C (spec_expr_get_value (e : expr)) y1) ->
        (red_expr (S : state) (C : execution_ctx) ((expr_object_3_val (l : object_loc) (x : string) (y1 : (specret value)) (pds : propdefs)) : ext_expr) (o : out)) ->
        (* ------------------------------------------ *)
        (red_expr (S : state) (C : execution_ctx) ((expr_object_2 (l : object_loc) (x : string) ((propbody_val (e : expr)) : propbody) (pds : propdefs)) : ext_expr) (o : out))

  | red_expr_object_3_val :
      forall (S : state (* input *)) (S0 : state (* input *)) (C : execution_ctx (* input *)) (l : object_loc (* input *)) (x : prop_name (* input *)) (A : attributes) (v : value (* input *)) (o : out) (pds : propdefs (* input *)),
        (A = ((attributes_data_intro (v : value) (true : bool) (true : bool) (true : bool)) : attributes)) ->
        (* ========================================== *)
        (red_expr (S : state) (C : execution_ctx) ((expr_object_4 (l : object_loc) (x : string) (A : descriptor) (pds : propdefs)) : ext_expr) (o : out)) ->
        (* ------------------------------------------ *)
        (red_expr (S0 : state) (C : execution_ctx) ((expr_object_3_val (l : object_loc) (x : string) ((specret_val S v) : (specret value)) (pds : propdefs)) : ext_expr) (o : out))

  | red_expr_object_2_get :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (bd : funcbody (* input *)) (l : object_loc (* input *)) (x : prop_name (* input *)) (o : out) (o1 : out) (pds : propdefs (* input *)),
        (* ========================================== *)
        (red_expr (S : state) (C : execution_ctx) ((spec_create_new_function_in (C : execution_ctx) (nil : (list string)) (bd : funcbody)) : ext_expr) (o1 : out)) ->
        (red_expr (S : state) (C : execution_ctx) ((expr_object_3_get (l : object_loc) (x : string) (o1 : out) (pds : propdefs)) : ext_expr) (o : out)) ->
        (* ------------------------------------------ *)
        (red_expr (S : state) (C : execution_ctx) ((expr_object_2 (l : object_loc) (x : string) ((propbody_get (bd : funcbody)) : propbody) (pds : propdefs)) : ext_expr) (o : out))

  | red_expr_object_3_get :
      forall (S : state (* input *)) (S0 : state (* input *)) (C : execution_ctx (* input *)) (Desc : descriptor) (l : object_loc (* input *)) (x : prop_name (* input *)) (v : value (* input *)) (pds : propdefs (* input *)) (o : out),
        (Desc = ((descriptor_intro (None : (option value)) (None : (option bool)) ((Some v) : (option value)) (None : (option value)) ((Some true) : (option bool)) ((Some true) : (option bool))) : descriptor)) ->
        (* ========================================== *)
        (red_expr (S : state) (C : execution_ctx) ((expr_object_4 (l : object_loc) (x : string) (Desc : descriptor) (pds : propdefs)) : ext_expr) (o : out)) ->
        (* ------------------------------------------ *)
        (red_expr (S0 : state) (C : execution_ctx) ((expr_object_3_get (l : object_loc) (x : string) ((out_ter (S : state) (v : res)) : out) (pds : propdefs)) : ext_expr) (o : out))

  | red_expr_object_2_set :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (l : object_loc (* input *)) (x : prop_name (* input *)) (pds : propdefs (* input *)) (o : out) (o1 : out) (bd : funcbody (* input *)) (args : (list string) (* input *)),
        (* ========================================== *)
        (red_expr (S : state) (C : execution_ctx) ((spec_create_new_function_in (C : execution_ctx) (args : (list string)) (bd : funcbody)) : ext_expr) (o1 : out)) ->
        (red_expr (S : state) (C : execution_ctx) ((expr_object_3_set (l : object_loc) (x : string) (o1 : out) (pds : propdefs)) : ext_expr) (o : out)) ->
        (* ------------------------------------------ *)
        (red_expr (S : state) (C : execution_ctx) ((expr_object_2 (l : object_loc) (x : string) ((propbody_set (args : (list string)) (bd : funcbody)) : propbody) (pds : propdefs)) : ext_expr) (o : out))

  | red_expr_object_3_set :
      forall (S : state (* input *)) (S0 : state (* input *)) (C : execution_ctx (* input *)) (Desc : descriptor) (l : object_loc (* input *)) (x : prop_name (* input *)) (v : value (* input *)) (pds : propdefs (* input *)) (o : out),
        (Desc = ((descriptor_intro (None : (option value)) (None : (option bool)) (None : (option value)) ((Some v) : (option value)) ((Some true) : (option bool)) ((Some true) : (option bool))) : descriptor)) ->
        (* ========================================== *)
        (red_expr (S : state) (C : execution_ctx) ((expr_object_4 (l : object_loc) (x : string) (Desc : descriptor) (pds : propdefs)) : ext_expr) (o : out)) ->
        (* ------------------------------------------ *)
        (red_expr (S0 : state) (C : execution_ctx) ((expr_object_3_set (l : object_loc) (x : string) ((out_ter (S : state) (v : res)) : out) (pds : propdefs)) : ext_expr) (o : out))

  | red_expr_object_4 :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (Desc : descriptor (* input *)) (l : object_loc (* input *)) (x : prop_name (* input *)) (pds : propdefs (* input *)) (o : out) (o1 : out),
        (* ========================================== *)
        (red_expr (S : state) (C : execution_ctx) ((spec_object_define_own_prop (l : object_loc) (x : prop_name) (Desc : descriptor) (false : bool)) : ext_expr) (o1 : out)) ->
        (red_expr (S : state) (C : execution_ctx) ((expr_object_5 (l : object_loc) (pds : propdefs) (o1 : out)) : ext_expr) (o : out)) ->
        (* ------------------------------------------ *)
        (red_expr (S : state) (C : execution_ctx) ((expr_object_4 (l : object_loc) (x : string) (Desc : descriptor) (pds : propdefs)) : ext_expr) (o : out))

  | red_expr_object_5 :
      forall (S : state (* input *)) (S0 : state (* input *)) (C : execution_ctx (* input *)) (rv : resvalue (* input *)) (l : object_loc (* input *)) (pds : propdefs (* input *)) (o : out),
        (* ========================================== *)
        (red_expr (S : state) (C : execution_ctx) ((expr_object_1 (l : object_loc) (pds : propdefs)) : ext_expr) (o : out)) ->
        (* ------------------------------------------ *)
        (red_expr (S0 : state) (C : execution_ctx) ((expr_object_5 (l : object_loc) (pds : propdefs) ((out_ter (S : state) (rv : res)) : out)) : ext_expr) (o : out))

  | red_expr_member :
      forall (x : prop_name (* input *)) (S0 : state (* input *)) (C : execution_ctx (* input *)) (e1 : expr (* input *)) (o : out),
        (* ========================================== *)
        (red_expr (S0 : state) (C : execution_ctx) ((expr_access (e1 : expr) ((expr_literal ((literal_string (x : string)) : literal)) : expr)) : ext_expr) (o : out)) ->
        (* ------------------------------------------ *)
        (red_expr (S0 : state) (C : execution_ctx) ((expr_member (e1 : expr) (x : string)) : ext_expr) (o : out))

  | red_expr_access :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (e1 : expr (* input *)) (e2 : expr (* input *)) (y1 : (specret value)) (o : out),
        (* ========================================== *)
        (red_spec S C (spec_expr_get_value (e1 : expr)) y1) ->
        (red_expr (S : state) (C : execution_ctx) ((expr_access_1 (y1 : (specret value)) (e2 : expr)) : ext_expr) (o : out)) ->
        (* ------------------------------------------ *)
        (red_expr (S : state) (C : execution_ctx) ((expr_access (e1 : expr) (e2 : expr)) : ext_expr) (o : out))

  | red_expr_access_1 :
      forall (S0 : state (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (v1 : value (* input *)) (e2 : expr (* input *)) (y1 : (specret value)) (o : out),
        (* ========================================== *)
        (red_spec S C (spec_expr_get_value (e2 : expr)) y1) ->
        (red_expr (S : state) (C : execution_ctx) ((expr_access_2 (v1 : value) (y1 : (specret value))) : ext_expr) (o : out)) ->
        (* ------------------------------------------ *)
        (red_expr (S0 : state) (C : execution_ctx) ((expr_access_1 ((specret_val S v1) : (specret value)) (e2 : expr)) : ext_expr) (o : out))

  | red_expr_access_2 :
      forall (S0 : state (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (v1 : value (* input *)) (v2 : value (* input *)) (o1 : out) (o : out),
        (* ========================================== *)
        (red_expr (S : state) (C : execution_ctx) ((spec_check_object_coercible (v1 : value)) : ext_expr) (o1 : out)) ->
        (red_expr (S : state) (C : execution_ctx) ((expr_access_3 (v1 : value) (o1 : out) (v2 : value)) : ext_expr) (o : out)) ->
        (* ------------------------------------------ *)
        (red_expr (S0 : state) (C : execution_ctx) ((expr_access_2 (v1 : value) ((specret_val S v2) : (specret value))) : ext_expr) (o : out))

  | red_expr_access_3 :
      forall (S0 : state (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (v1 : value (* input *)) (v2 : value (* input *)) (o1 : out) (o : out),
        (* ========================================== *)
        (red_expr (S : state) (C : execution_ctx) ((spec_to_string (v2 : value)) : ext_expr) (o1 : out)) ->
        (red_expr (S : state) (C : execution_ctx) ((expr_access_4 (v1 : value) (o1 : out)) : ext_expr) (o : out)) ->
        (* ------------------------------------------ *)
        (red_expr (S0 : state) (C : execution_ctx) ((expr_access_3 (v1 : value) ((out_ter (S : state) (res_intro restype_normal resvalue_empty label_empty)) : out) (v2 : value)) : ext_expr) (o : out))

  | red_expr_access_4 :
      forall (S0 : state (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (v1 : value (* input *)) (x : prop_name (* input *)) (r : ref),
        (r = ((ref_create_value v1 x (execution_ctx_strict (C : execution_ctx))) : ref)) ->
        (* ========================================== *)
        (* ------------------------------------------ *)
        (red_expr (S0 : state) (C : execution_ctx) ((expr_access_4 (v1 : value) ((out_ter (S : state) (x : res)) : out)) : ext_expr) ((out_ter (S : state) (r : res)) : out))

  | red_expr_new :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (e1 : expr (* input *)) (e2s : (list expr) (* input *)) (y1 : (specret value)) (o : out),
        (* ========================================== *)
        (red_spec S C (spec_expr_get_value (e1 : expr)) y1) ->
        (red_expr (S : state) (C : execution_ctx) ((expr_new_1 (y1 : (specret value)) (e2s : (list expr))) : ext_expr) (o : out)) ->
        (* ------------------------------------------ *)
        (red_expr (S : state) (C : execution_ctx) ((expr_new (e1 : expr) (e2s : (list expr))) : ext_expr) (o : out))

  | red_expr_new_1 :
      forall (S0 : state (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (e2s : (list expr) (* input *)) (v : value (* input *)) (y1 : (specret (list value))) (o : out),
        (* ========================================== *)
        (red_spec S C (spec_list_expr (e2s : (list expr))) y1) ->
        (red_expr (S : state) (C : execution_ctx) ((expr_new_2 (v : value) (y1 : (specret (list value)))) : ext_expr) (o : out)) ->
        (* ------------------------------------------ *)
        (red_expr (S0 : state) (C : execution_ctx) ((expr_new_1 ((specret_val S v) : (specret value)) (e2s : (list expr))) : ext_expr) (o : out))

  | red_expr_new_2_type_error_not_object :
      forall (S : state (* input *)) (S0 : state (* input *)) (C : execution_ctx (* input *)) (o : out) (v : value (* input *)) (vs : (list value) (* input *)),
        (((type_of v) : type) <> type_object) ->
        (* ========================================== *)
        (red_expr (S : state) (C : execution_ctx) ((spec_error (native_error_type : native_error)) : ext_expr) (o : out)) ->
        (* ------------------------------------------ *)
        (red_expr (S0 : state) (C : execution_ctx) ((expr_new_2 (v : value) ((specret_val S vs) : (specret (list value)))) : ext_expr) (o : out))

  | red_expr_new_2_type_error_no_construct :
      forall (S : state (* input *)) (S0 : state (* input *)) (C : execution_ctx (* input *)) (o : out) (l : object_loc (* input *)) (vs : (list value) (* input *)),
        (object_method object_construct_ S l None) ->
        (* ========================================== *)
        (red_expr (S : state) (C : execution_ctx) ((spec_error (native_error_type : native_error)) : ext_expr) (o : out)) ->
        (* ------------------------------------------ *)
        (red_expr (S0 : state) (C : execution_ctx) ((expr_new_2 ((value_object (l : object_loc)) : value) ((specret_val S vs) : (specret (list value)))) : ext_expr) (o : out))

  | red_expr_new_2_construct :
      forall (S : state (* input *)) (S0 : state (* input *)) (C : execution_ctx (* input *)) (l : object_loc (* input *)) (vs : (list value) (* input *)) (o : out),
        (* ========================================== *)
        (red_expr (S : state) (C : execution_ctx) ((spec_construct (l : object_loc) (vs : (list value))) : ext_expr) (o : out)) ->
        (* ------------------------------------------ *)
        (red_expr (S0 : state) (C : execution_ctx) ((expr_new_2 ((value_object (l : object_loc)) : value) ((specret_val S vs) : (specret (list value)))) : ext_expr) (o : out))

  | red_expr_call :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (e1 : expr (* input *)) (e2s : (list expr) (* input *)) (o1 : out) (o2 : out),
        (* ========================================== *)
        (red_expr (S : state) (C : execution_ctx) (e1 : ext_expr) (o1 : out)) ->
        (red_expr (S : state) (C : execution_ctx) ((expr_call_1 (o1 : out) ((is_syntactic_eval (e1 : expr)) : bool) (e2s : (list expr))) : ext_expr) (o2 : out)) ->
        (* ------------------------------------------ *)
        (red_expr (S : state) (C : execution_ctx) ((expr_call (e1 : expr) (e2s : (list expr))) : ext_expr) (o2 : out))

  | red_expr_call_1 :
      forall (S0 : state (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (rv : resvalue (* input *)) (is_eval_direct : bool (* input *)) (e2s : (list expr) (* input *)) (y1 : (specret value)) (o : out),
        (* ========================================== *)
        (red_spec S C (spec_get_value (rv : resvalue)) y1) ->
        (red_expr (S : state) (C : execution_ctx) ((expr_call_2 (rv : res) (is_eval_direct : bool) (e2s : (list expr)) (y1 : (specret value))) : ext_expr) (o : out)) ->
        (* ------------------------------------------ *)
        (red_expr (S0 : state) (C : execution_ctx) ((expr_call_1 ((out_ter (S : state) (rv : res)) : out) (is_eval_direct : bool) (e2s : (list expr))) : ext_expr) (o : out))

  | red_expr_call_2 :
      forall (S0 : state (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (rv : resvalue (* input *)) (v : value (* input *)) (e2s : (list expr) (* input *)) (is_eval_direct : bool (* input *)) (y1 : (specret (list value))) (o : out),
        (* ========================================== *)
        (red_spec S C (spec_list_expr (e2s : (list expr))) y1) ->
        (red_expr (S : state) (C : execution_ctx) ((expr_call_3 (rv : res) (v : value) (is_eval_direct : bool) (y1 : (specret (list value)))) : ext_expr) (o : out)) ->
        (* ------------------------------------------ *)
        (red_expr (S0 : state) (C : execution_ctx) ((expr_call_2 (rv : res) (is_eval_direct : bool) (e2s : (list expr)) ((specret_val S v) : (specret value))) : ext_expr) (o : out))

  | red_expr_call_3 :
      forall (S0 : state (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (o : out) (rv : resvalue (* input *)) (v : value (* input *)) (is_eval_direct : bool (* input *)) (vs : (list value) (* input *)),
        ((((type_of v) <> type_object) : Prop) \/ ((exists l, ((v = (value_object l)) /\ (~ (is_callable S l)))) : Prop)) ->
        (* ========================================== *)
        (red_expr (S : state) (C : execution_ctx) ((spec_error (native_error_type : native_error)) : ext_expr) (o : out)) ->
        (* ------------------------------------------ *)
        (red_expr (S0 : state) (C : execution_ctx) ((expr_call_3 (rv : res) (v : value) (is_eval_direct : bool) ((specret_val S vs) : (specret (list value)))) : ext_expr) (o : out))

  | red_expr_call_3_callable :
      forall (l : object_loc (* input *)) (S0 : state (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (o : out) (rv : resvalue (* input *)) (is_eval_direct : bool (* input *)) (vs : (list value) (* input *)),
        (is_callable (S : state) (l : value)) ->
        (* ========================================== *)
        (red_expr (S : state) (C : execution_ctx) ((expr_call_4 (rv : res) (l : object_loc) (is_eval_direct : bool) (vs : (list value))) : ext_expr) (o : out)) ->
        (* ------------------------------------------ *)
        (red_expr (S0 : state) (C : execution_ctx) ((expr_call_3 (rv : res) ((value_object (l : object_loc)) : value) (is_eval_direct : bool) ((specret_val S vs) : (specret (list value)))) : ext_expr) (o : out))

  | red_expr_call_4_prop :
      forall (v : value) (S : state (* input *)) (C : execution_ctx (* input *)) (o : out) (r : ref (* input *)) (l : object_loc (* input *)) (is_eval_direct : bool (* input *)) (vs : (list value) (* input *)),
        (ref_is_property (r : ref)) ->
        (ref_is_value (r : ref) (v : value)) ->
        (* ========================================== *)
        (red_expr (S : state) (C : execution_ctx) ((expr_call_5 (l : object_loc) (is_eval_direct : bool) (vs : (list value)) ((out_ter (S : state) (v : res)) : out)) : ext_expr) (o : out)) ->
        (* ------------------------------------------ *)
        (red_expr (S : state) (C : execution_ctx) ((expr_call_4 ((resvalue_ref (r : ref)) : res) (l : object_loc) (is_eval_direct : bool) (vs : (list value))) : ext_expr) (o : out))

  | red_expr_call_4_env :
      forall (L : env_loc) (o1 : out) (S : state (* input *)) (C : execution_ctx (* input *)) (o : out) (r : ref (* input *)) (l : object_loc (* input *)) (is_eval_direct : bool (* input *)) (vs : (list value) (* input *)),
        (ref_is_env_record (r : ref) (L : env_loc)) ->
        (* ========================================== *)
        (red_expr (S : state) (C : execution_ctx) ((spec_env_record_implicit_this_value (L : env_loc)) : ext_expr) (o1 : out)) ->
        (red_expr (S : state) (C : execution_ctx) ((expr_call_5 (l : object_loc) (is_eval_direct : bool) (vs : (list value)) (o1 : out)) : ext_expr) (o : out)) ->
        (* ------------------------------------------ *)
        (red_expr (S : state) (C : execution_ctx) ((expr_call_4 ((resvalue_ref (r : ref)) : res) (l : object_loc) (is_eval_direct : bool) (vs : (list value))) : ext_expr) (o : out))

  | red_expr_call_4_not_ref :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (v : value (* input *)) (l : object_loc (* input *)) (is_eval_direct : bool (* input *)) (vs : (list value) (* input *)) (o : out),
        (* ========================================== *)
        (red_expr (S : state) (C : execution_ctx) ((expr_call_5 (l : object_loc) (is_eval_direct : bool) (vs : (list value)) ((out_ter (S : state) (undef : res)) : out)) : ext_expr) (o : out)) ->
        (* ------------------------------------------ *)
        (red_expr (S : state) (C : execution_ctx) ((expr_call_4 ((resvalue_value (v : value)) : res) (l : object_loc) (is_eval_direct : bool) (vs : (list value))) : ext_expr) (o : out))

  | red_expr_call_5_eval :
      forall (S0 : state (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (is_eval_direct : bool (* input *)) (vs : (list value) (* input *)) (v : value (* input *)) (o : out),
        (* ========================================== *)
        (red_expr (S : state) (C : execution_ctx) ((spec_call_global_eval (is_eval_direct : bool) (vs : (list value))) : ext_expr) (o : out)) ->
        (* ------------------------------------------ *)
        (red_expr (S0 : state) (C : execution_ctx) ((expr_call_5 (prealloc_global_eval : object_loc) (is_eval_direct : bool) (vs : (list value)) ((out_ter (S : state) (v : res)) : out)) : ext_expr) (o : out))

  | red_expr_call_5_not_eval :
      forall (S0 : state (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (l : object_loc (* input *)) (is_eval_direct : bool (* input *)) (vs : (list value) (* input *)) (v : value (* input *)) (o : out),
        (l <> (prealloc_global_eval : object_loc)) ->
        (* ========================================== *)
        (red_expr (S : state) (C : execution_ctx) ((spec_call (l : object_loc) (v : value) (vs : (list value))) : ext_expr) (o : out)) ->
        (* ------------------------------------------ *)
        (red_expr (S0 : state) (C : execution_ctx) ((expr_call_5 (l : object_loc) (is_eval_direct : bool) (vs : (list value)) ((out_ter (S : state) (v : res)) : out)) : ext_expr) (o : out))

  | red_expr_function_unnamed :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (args : (list string) (* input *)) (bd : funcbody (* input *)) (lex : lexical_env) (o : out),
        ((lex : lexical_env) = (execution_ctx_lexical_env (C : execution_ctx))) ->
        (* ========================================== *)
        (red_expr (S : state) (C : execution_ctx) ((spec_creating_function_object (args : (list string)) (bd : funcbody) (lex : lexical_env) ((funcbody_is_strict bd) : strictness_flag)) : ext_expr) (o : out)) ->
        (* ------------------------------------------ *)
        (red_expr (S : state) (C : execution_ctx) ((expr_function (None : (option string)) (args : (list string)) (bd : funcbody)) : ext_expr) (o : out))

  | red_expr_function_named :
      forall (lex' : lexical_env) (S' : state) (L : env_loc) (lextail : (list env_loc)) (E : env_record) (o1 : out) (S : state (* input *)) (C : execution_ctx (* input *)) (s : string (* input *)) (args : (list string) (* input *)) (bd : funcbody (* input *)) (o : out),
        ((lex', S') = (lexical_env_alloc_decl S (execution_ctx_lexical_env (C : execution_ctx)))) ->
        ((lex' : (list env_loc)) = (L :: (lextail : (list env_loc)))) ->
        (env_record_binds (S' : state) (L : env_loc) (E : env_record)) ->
        (* ========================================== *)
        (red_expr (S' : state) (C : execution_ctx) ((spec_env_record_create_immutable_binding (L : env_loc) (s : prop_name)) : ext_expr) (o1 : out)) ->
        (red_expr (S' : state) (C : execution_ctx) ((expr_function_1 (s : string) (args : (list string)) (bd : funcbody) (L : env_loc) (lex' : lexical_env) (o1 : out)) : ext_expr) (o : out)) ->
        (* ------------------------------------------ *)
        (red_expr (S : state) (C : execution_ctx) ((expr_function ((Some s) : (option string)) (args : (list string)) (bd : funcbody)) : ext_expr) (o : out))

  | red_expr_function_named_1 :
      forall (o1 : out) (S0 : state (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (s : string (* input *)) (args : (list string) (* input *)) (bd : funcbody (* input *)) (L : env_loc (* input *)) (scope : lexical_env (* input *)) (o : out),
        (* ========================================== *)
        (red_expr (S : state) (C : execution_ctx) ((spec_creating_function_object (args : (list string)) (bd : funcbody) (scope : lexical_env) ((funcbody_is_strict bd) : strictness_flag)) : ext_expr) (o1 : out)) ->
        (red_expr (S : state) (C : execution_ctx) ((expr_function_2 (s : string) (L : env_loc) (o1 : out)) : ext_expr) (o : out)) ->
        (* ------------------------------------------ *)
        (red_expr (S0 : state) (C : execution_ctx) ((expr_function_1 (s : string) (args : (list string)) (bd : funcbody) (L : env_loc) (scope : lexical_env) ((out_ter (S : state) (res_intro restype_normal resvalue_empty label_empty)) : out)) : ext_expr) (o : out))

  | red_expr_function_named_2 :
      forall (o1 : out) (S0 : state (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (s : string (* input *)) (L : env_loc (* input *)) (l : object_loc (* input *)) (o : out),
        (* ========================================== *)
        (red_expr (S : state) (C : execution_ctx) ((spec_env_record_initialize_immutable_binding (L : env_loc) (s : prop_name) (l : value)) : ext_expr) (o1 : out)) ->
        (red_expr (S : state) (C : execution_ctx) ((expr_function_3 (l : object_loc) (o1 : out)) : ext_expr) (o : out)) ->
        (* ------------------------------------------ *)
        (red_expr (S0 : state) (C : execution_ctx) ((expr_function_2 (s : string) (L : env_loc) ((out_ter (S : state) (l : res)) : out)) : ext_expr) (o : out))

  | red_expr_function_named_3 :
      forall (S0 : state (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (l : object_loc (* input *)),
        (* ========================================== *)
        (* ------------------------------------------ *)
        (red_expr (S0 : state) (C : execution_ctx) ((expr_function_3 (l : object_loc) ((out_ter (S : state) (res_intro restype_normal resvalue_empty label_empty)) : out)) : ext_expr) ((out_ter (S : state) (l : res)) : out))

  | red_expr_prepost :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (op : unary_op (* input *)) (e : expr (* input *)) (o1 : out) (o : out),
        (prepost_unary_op op) ->
        (* ========================================== *)
        (red_expr (S : state) (C : execution_ctx) (e : ext_expr) (o1 : out)) ->
        (red_expr (S : state) (C : execution_ctx) ((expr_prepost_1 (op : unary_op) (o1 : out)) : ext_expr) (o : out)) ->
        (* ------------------------------------------ *)
        (red_expr (S : state) (C : execution_ctx) ((expr_unary_op (op : unary_op) (e : expr)) : ext_expr) (o : out))

  | red_expr_prepost_1_valid :
      forall (S0 : state (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (rv : resvalue (* input *)) (op : unary_op (* input *)) (y1 : (specret value)) (o : out),
        (* ========================================== *)
        (red_spec S C (spec_get_value (rv : resvalue)) y1) ->
        (red_expr (S : state) (C : execution_ctx) ((expr_prepost_2 (op : unary_op) (rv : res) (y1 : (specret value))) : ext_expr) (o : out)) ->
        (* ------------------------------------------ *)
        (red_expr (S0 : state) (C : execution_ctx) ((expr_prepost_1 (op : unary_op) ((out_ter (S : state) (rv : res)) : out)) : ext_expr) (o : out))

  | red_expr_prepost_2 :
      forall (S0 : state (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (rv : resvalue (* input *)) (op : unary_op (* input *)) (v : value (* input *)) (o1 : out) (o : out),
        (* ========================================== *)
        (red_expr (S : state) (C : execution_ctx) ((spec_to_number (v : value)) : ext_expr) (o1 : out)) ->
        (red_expr (S : state) (C : execution_ctx) ((expr_prepost_3 (op : unary_op) (rv : res) (o1 : out)) : ext_expr) (o : out)) ->
        (* ------------------------------------------ *)
        (red_expr (S0 : state) (C : execution_ctx) ((expr_prepost_2 (op : unary_op) (rv : res) ((specret_val S v) : (specret value))) : ext_expr) (o : out))

  | red_expr_prepost_3 :
      forall (S0 : state (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (rv : resvalue (* input *)) (op : unary_op (* input *)) (number_op : (number -> number)) (is_pre : bool) (v : value) (n1 : number (* input *)) (n2 : number) (o1 : out) (o : out),
        (prepost_op (op : unary_op) (number_op : (number -> number)) (is_pre : bool)) ->
        (n2 = ((number_op n1) : number)) ->
        (v = ((prim_number ((ifb is_pre then (n2 : number) else n1) : number)) : value)) ->
        (* ========================================== *)
        (red_expr (S : state) (C : execution_ctx) ((spec_put_value (rv : resvalue) (n2 : value)) : ext_expr) (o1 : out)) ->
        (red_expr (S : state) (C : execution_ctx) ((expr_prepost_4 (v : value) (o1 : out)) : ext_expr) (o : out)) ->
        (* ------------------------------------------ *)
        (red_expr (S0 : state) (C : execution_ctx) ((expr_prepost_3 (op : unary_op) (rv : res) ((out_ter (S : state) (n1 : res)) : out)) : ext_expr) (o : out))

  | red_expr_prepost_4 :
      forall (S0 : state (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (v : value (* input *)),
        (* ========================================== *)
        (* ------------------------------------------ *)
        (red_expr (S0 : state) (C : execution_ctx) ((expr_prepost_4 (v : value) ((out_ter (S : state) (res_intro restype_normal resvalue_empty label_empty)) : out)) : ext_expr) ((out_ter (S : state) (v : res)) : out))

  | red_expr_unary_op :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (op : unary_op (* input *)) (e : expr (* input *)) (y1 : (specret value)) (o : out),
        (regular_unary_op op) ->
        (* ========================================== *)
        (red_spec S C (spec_expr_get_value (e : expr)) y1) ->
        (red_expr (S : state) (C : execution_ctx) ((expr_unary_op_1 (op : unary_op) (y1 : (specret value))) : ext_expr) (o : out)) ->
        (* ------------------------------------------ *)
        (red_expr (S : state) (C : execution_ctx) ((expr_unary_op (op : unary_op) (e : expr)) : ext_expr) (o : out))

  | red_expr_unary_op_1 :
      forall (S0 : state (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (op : unary_op (* input *)) (v : value (* input *)) (o : out),
        (* ========================================== *)
        (red_expr (S : state) (C : execution_ctx) ((expr_unary_op_2 (op : unary_op) (v : value)) : ext_expr) (o : out)) ->
        (* ------------------------------------------ *)
        (red_expr (S0 : state) (C : execution_ctx) ((expr_unary_op_1 (op : unary_op) ((specret_val S v) : (specret value))) : ext_expr) (o : out))

  | red_expr_delete :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (e : expr (* input *)) (o1 : out) (o : out),
        (* ========================================== *)
        (red_expr (S : state) (C : execution_ctx) (e : ext_expr) (o1 : out)) ->
        (red_expr (S : state) (C : execution_ctx) ((expr_delete_1 (o1 : out)) : ext_expr) (o : out)) ->
        (* ------------------------------------------ *)
        (red_expr (S : state) (C : execution_ctx) ((expr_unary_op (unary_op_delete : unary_op) (e : expr)) : ext_expr) (o : out))

  | red_expr_delete_1_not_ref :
      forall (S0 : state (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (rv : resvalue (* input *)),
        (~ (resvalue_is_ref (rv : resvalue))) ->
        (* ========================================== *)
        (* ------------------------------------------ *)
        (red_expr (S0 : state) (C : execution_ctx) ((expr_delete_1 ((out_ter (S : state) (rv : res)) : out)) : ext_expr) ((out_ter (S : state) (true : res)) : out))

  | red_expr_delete_1_ref_unresolvable :
      forall (S0 : state (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (r : ref (* input *)) (o : out),
        (ref_is_unresolvable (r : ref)) ->
        (* ========================================== *)
        (red_expr (S : state) (C : execution_ctx) ((expr_delete_2 (r : ref)) : ext_expr) (o : out)) ->
        (* ------------------------------------------ *)
        (red_expr (S0 : state) (C : execution_ctx) ((expr_delete_1 ((out_ter (S : state) (r : res)) : out)) : ext_expr) (o : out))

  | red_expr_delete_2_strict :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (r : ref (* input *)) (o : out),
        ((ref_strict (r : ref)) = (true : bool)) ->
        (* ========================================== *)
        (red_expr (S : state) (C : execution_ctx) ((spec_error (native_error_syntax : native_error)) : ext_expr) (o : out)) ->
        (* ------------------------------------------ *)
        (red_expr (S : state) (C : execution_ctx) ((expr_delete_2 (r : ref)) : ext_expr) (o : out))

  | red_expr_delete_2_not_strict :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (r : ref (* input *)),
        ((ref_strict (r : ref)) = (false : bool)) ->
        (* ========================================== *)
        (* ------------------------------------------ *)
        (red_expr (S : state) (C : execution_ctx) ((expr_delete_2 (r : ref)) : ext_expr) ((out_ter (S : state) (true : res)) : out))

  | red_expr_delete_1_ref_property :
      forall (S0 : state (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (r : ref (* input *)) (v : value) (o1 : out) (o : out),
        (ref_is_property (r : ref)) ->
        ((ref_base (r : ref)) = ((ref_base_type_value (v : value)) : ref_base_type)) ->
        (* ========================================== *)
        (red_expr (S : state) (C : execution_ctx) ((spec_to_object (v : value)) : ext_expr) (o1 : out)) ->
        (red_expr (S : state) (C : execution_ctx) ((expr_delete_3 (r : ref) (o1 : out)) : ext_expr) (o : out)) ->
        (* ------------------------------------------ *)
        (red_expr (S0 : state) (C : execution_ctx) ((expr_delete_1 ((out_ter (S : state) (r : res)) : out)) : ext_expr) (o : out))

  | red_expr_delete_3 :
      forall (S0 : state (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (r : ref (* input *)) (l : object_loc (* input *)) (o : out),
        (* ========================================== *)
        (red_expr (S : state) (C : execution_ctx) ((spec_object_delete (l : object_loc) ((ref_name (r : ref)) : prop_name) ((ref_strict (r : ref)) : bool)) : ext_expr) (o : out)) ->
        (* ------------------------------------------ *)
        (red_expr (S0 : state) (C : execution_ctx) ((expr_delete_3 (r : ref) ((out_ter (S : state) (l : res)) : out)) : ext_expr) (o : out))

  | red_expr_delete_1_ref_env_record :
      forall (S0 : state (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (r : ref (* input *)) (L : env_loc) (o : out),
        (ref_is_env_record (r : ref) (L : env_loc)) ->
        (* ========================================== *)
        (red_expr (S : state) (C : execution_ctx) ((expr_delete_4 (r : ref) (L : env_loc)) : ext_expr) (o : out)) ->
        (* ------------------------------------------ *)
        (red_expr (S0 : state) (C : execution_ctx) ((expr_delete_1 ((out_ter (S : state) (r : res)) : out)) : ext_expr) (o : out))

  | red_expr_delete_4_strict :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (r : ref (* input *)) (L : env_loc (* input *)) (o : out),
        ((ref_strict (r : ref)) = (true : bool)) ->
        (* ========================================== *)
        (red_expr (S : state) (C : execution_ctx) ((spec_error (native_error_syntax : native_error)) : ext_expr) (o : out)) ->
        (* ------------------------------------------ *)
        (red_expr (S : state) (C : execution_ctx) ((expr_delete_4 (r : ref) (L : env_loc)) : ext_expr) (o : out))

  | red_expr_delete_4_not_strict :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (r : ref (* input *)) (L : env_loc (* input *)) (o : out),
        ((ref_strict (r : ref)) = (false : bool)) ->
        (* ========================================== *)
        (red_expr (S : state) (C : execution_ctx) ((spec_env_record_delete_binding (L : env_loc) ((ref_name (r : ref)) : prop_name)) : ext_expr) (o : out)) ->
        (* ------------------------------------------ *)
        (red_expr (S : state) (C : execution_ctx) ((expr_delete_4 (r : ref) (L : env_loc)) : ext_expr) (o : out))

  | red_expr_unary_op_void :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (v : value (* input *)),
        (* ========================================== *)
        (* ------------------------------------------ *)
        (red_expr (S : state) (C : execution_ctx) ((expr_unary_op_2 (unary_op_void : unary_op) (v : value)) : ext_expr) ((out_ter (S : state) (undef : res)) : out))

  | red_expr_typeof :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (e : expr (* input *)) (o1 : out) (o : out),
        (* ========================================== *)
        (red_expr (S : state) (C : execution_ctx) (e : ext_expr) (o1 : out)) ->
        (red_expr (S : state) (C : execution_ctx) ((expr_typeof_1 (o1 : out)) : ext_expr) (o : out)) ->
        (* ------------------------------------------ *)
        (red_expr (S : state) (C : execution_ctx) ((expr_unary_op (unary_op_typeof : unary_op) (e : expr)) : ext_expr) (o : out))

  | red_expr_typeof_1_value :
      forall (S0 : state (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (v : value (* input *)) (o : out),
        (* ========================================== *)
        (red_expr (S : state) (C : execution_ctx) ((expr_typeof_2 ((ret S v) : (specret value))) : ext_expr) (o : out)) ->
        (* ------------------------------------------ *)
        (red_expr (S0 : state) (C : execution_ctx) ((expr_typeof_1 ((out_ter (S : state) (v : res)) : out)) : ext_expr) (o : out))

  | red_expr_typeof_1_ref_unresolvable :
      forall (S0 : state (* input *)) (S : state (* input *)) (r : ref (* input *)) (C : execution_ctx (* input *)),
        (ref_is_unresolvable (r : ref)) ->
        (* ========================================== *)
        (* ------------------------------------------ *)
        (red_expr (S0 : state) (C : execution_ctx) ((expr_typeof_1 ((out_ter (S : state) (r : res)) : out)) : ext_expr) ((out_ter (S : state) ((("undefined")%string) : res)) : out))

  | red_expr_typeof_1_ref_resolvable :
      forall (S0 : state (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (r : ref (* input *)) (y1 : (specret value)) (o : out),
        (~ (ref_is_unresolvable (r : ref))) ->
        (* ========================================== *)
        (red_spec S C (spec_get_value (r : resvalue)) y1) ->
        (red_expr (S : state) (C : execution_ctx) ((expr_typeof_2 (y1 : (specret value))) : ext_expr) (o : out)) ->
        (* ------------------------------------------ *)
        (red_expr (S0 : state) (C : execution_ctx) ((expr_typeof_1 ((out_ter (S : state) (r : res)) : out)) : ext_expr) (o : out))

  | red_expr_typeof_2 :
      forall (S0 : state (* input *)) (S : state (* input *)) (s : string) (C : execution_ctx (* input *)) (v : value (* input *)),
        (s = ((typeof_value (S : state) (v : value)) : string)) ->
        (* ========================================== *)
        (* ------------------------------------------ *)
        (red_expr (S0 : state) (C : execution_ctx) ((expr_typeof_2 ((specret_val S v) : (specret value))) : ext_expr) ((out_ter (S : state) (s : res)) : out))

  | red_expr_unary_op_add :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (v : value (* input *)) (o : out),
        (* ========================================== *)
        (red_expr (S : state) (C : execution_ctx) ((spec_to_number (v : value)) : ext_expr) (o : out)) ->
        (* ------------------------------------------ *)
        (red_expr (S : state) (C : execution_ctx) ((expr_unary_op_2 (unary_op_add : unary_op) (v : value)) : ext_expr) (o : out))

  | red_expr_unary_op_neg :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (v : value (* input *)) (o1 : out) (o : out),
        (* ========================================== *)
        (red_expr (S : state) (C : execution_ctx) ((spec_to_number (v : value)) : ext_expr) (o1 : out)) ->
        (red_expr (S : state) (C : execution_ctx) ((expr_unary_op_neg_1 (o1 : out)) : ext_expr) (o : out)) ->
        (* ------------------------------------------ *)
        (red_expr (S : state) (C : execution_ctx) ((expr_unary_op_2 (unary_op_neg : unary_op) (v : value)) : ext_expr) (o : out))

  | red_expr_unary_op_neg_1 :
      forall (S0 : state (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (n : number (* input *)),
        (* ========================================== *)
        (* ------------------------------------------ *)
        (red_expr (S0 : state) (C : execution_ctx) ((expr_unary_op_neg_1 ((out_ter (S : state) (n : res)) : out)) : ext_expr) ((out_ter (S : state) ((JsNumber.neg n) : res)) : out))

  | red_expr_unary_op_bitwise_not :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (v : value (* input *)) (y1 : (specret int)) (o : out),
        (* ========================================== *)
        (red_spec S C (spec_to_int32 (v : value)) y1) ->
        (red_expr (S : state) (C : execution_ctx) ((expr_unary_op_bitwise_not_1 (y1 : (specret int))) : ext_expr) (o : out)) ->
        (* ------------------------------------------ *)
        (red_expr (S : state) (C : execution_ctx) ((expr_unary_op_2 (unary_op_bitwise_not : unary_op) (v : value)) : ext_expr) (o : out))

  | red_expr_unary_op_bitwise_not_1 :
      forall (S0 : state (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (k : int (* input *)) (n : number),
        (n = ((JsNumber.of_int (JsNumber.int32_bitwise_not k)) : number)) ->
        (* ========================================== *)
        (* ------------------------------------------ *)
        (red_expr (S0 : state) (C : execution_ctx) ((expr_unary_op_bitwise_not_1 ((specret_val S k) : (specret int))) : ext_expr) ((out_ter (S : state) (n : res)) : out))

  | red_expr_unary_op_not :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (v : value (* input *)) (o1 : out) (o : out),
        (* ========================================== *)
        (red_expr (S : state) (C : execution_ctx) ((spec_to_boolean (v : value)) : ext_expr) (o1 : out)) ->
        (red_expr (S : state) (C : execution_ctx) ((expr_unary_op_not_1 (o1 : out)) : ext_expr) (o : out)) ->
        (* ------------------------------------------ *)
        (red_expr (S : state) (C : execution_ctx) ((expr_unary_op_2 (unary_op_not : unary_op) (v : value)) : ext_expr) (o : out))

  | red_expr_unary_op_not_1 :
      forall (S0 : state (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (b : bool (* input *)),
        (* ========================================== *)
        (* ------------------------------------------ *)
        (red_expr (S0 : state) (C : execution_ctx) ((expr_unary_op_not_1 ((out_ter (S : state) (b : res)) : out)) : ext_expr) ((out_ter (S : state) ((neg b) : res)) : out))

  | red_expr_binary_op :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (op : binary_op (* input *)) (e1 : expr (* input *)) (e2 : expr (* input *)) (y1 : (specret value)) (o : out),
        (regular_binary_op op) ->
        (* ========================================== *)
        (red_spec S C (spec_expr_get_value (e1 : expr)) y1) ->
        (red_expr (S : state) (C : execution_ctx) ((expr_binary_op_1 (op : binary_op) (y1 : (specret value)) (e2 : expr)) : ext_expr) (o : out)) ->
        (* ------------------------------------------ *)
        (red_expr (S : state) (C : execution_ctx) ((expr_binary_op (e1 : expr) (op : binary_op) (e2 : expr)) : ext_expr) (o : out))

  | red_expr_binary_op_1 :
      forall (S0 : state (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (op : binary_op (* input *)) (v1 : value (* input *)) (e2 : expr (* input *)) (y1 : (specret value)) (o : out),
        (* ========================================== *)
        (red_spec S C (spec_expr_get_value (e2 : expr)) y1) ->
        (red_expr (S : state) (C : execution_ctx) ((expr_binary_op_2 (op : binary_op) (v1 : value) (y1 : (specret value))) : ext_expr) (o : out)) ->
        (* ------------------------------------------ *)
        (red_expr (S0 : state) (C : execution_ctx) ((expr_binary_op_1 (op : binary_op) ((specret_val S v1) : (specret value)) (e2 : expr)) : ext_expr) (o : out))

  | red_expr_binary_op_2 :
      forall (S0 : state (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (op : binary_op (* input *)) (v1 : value (* input *)) (v2 : value (* input *)) (o : out),
        (* ========================================== *)
        (red_expr (S : state) (C : execution_ctx) ((expr_binary_op_3 (op : binary_op) (v1 : value) (v2 : value)) : ext_expr) (o : out)) ->
        (* ------------------------------------------ *)
        (red_expr (S0 : state) (C : execution_ctx) ((expr_binary_op_2 (op : binary_op) (v1 : value) ((specret_val S v2) : (specret value))) : ext_expr) (o : out))

  | red_expr_binary_op_add :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (v1 : value (* input *)) (v2 : value (* input *)) (y1 : (specret (value * value))) (o : out),
        (* ========================================== *)
        (red_spec S C (spec_convert_twice ((spec_to_primitive_auto (v1 : value)) : ext_expr) ((spec_to_primitive_auto (v2 : value)) : ext_expr)) y1) ->
        (red_expr (S : state) (C : execution_ctx) ((expr_binary_op_add_1 (y1 : (specret (value * value)))) : ext_expr) (o : out)) ->
        (* ------------------------------------------ *)
        (red_expr (S : state) (C : execution_ctx) ((expr_binary_op_3 (binary_op_add : binary_op) (v1 : value) (v2 : value)) : ext_expr) (o : out))

  | red_expr_binary_op_add_1_string :
      forall (S0 : state (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (v1 : value (* input *)) (v2 : value (* input *)) (y1 : (specret (value * value))) (o : out),
        ((((type_of v1) = type_string) : Prop) \/ (((type_of v2) = type_string) : Prop)) ->
        (* ========================================== *)
        (red_spec S C (spec_convert_twice ((spec_to_string (v1 : value)) : ext_expr) ((spec_to_string (v2 : value)) : ext_expr)) y1) ->
        (red_expr (S : state) (C : execution_ctx) ((expr_binary_op_add_string_1 (y1 : (specret (value * value)))) : ext_expr) (o : out)) ->
        (* ------------------------------------------ *)
        (red_expr (S0 : state) (C : execution_ctx) ((expr_binary_op_add_1 ((specret_val S (v1, v2)) : (specret (value * value)))) : ext_expr) (o : out))

  | red_expr_binary_op_add_string_1 :
      forall (S0 : state (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (s1 : string (* input *)) (s2 : string (* input *)) (s : string),
        (s = ((String.append s1 s2) : string)) ->
        (* ========================================== *)
        (* ------------------------------------------ *)
        (red_expr (S0 : state) (C : execution_ctx) ((expr_binary_op_add_string_1 ((specret_val S ((value_prim (s1 : prim)), (value_prim (s2 : prim)))) : (specret (value * value)))) : ext_expr) ((out_ter (S : state) (s : res)) : out))

  | red_expr_binary_op_add_1_number :
      forall (S0 : state (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (v1 : value (* input *)) (v2 : value (* input *)) (y1 : (specret (value * value))) (o : out),
        (~ ((((type_of v1) = type_string) : Prop) \/ (((type_of v2) = type_string) : Prop))) ->
        (* ========================================== *)
        (red_spec S C (spec_convert_twice ((spec_to_number (v1 : value)) : ext_expr) ((spec_to_number (v2 : value)) : ext_expr)) y1) ->
        (red_expr (S : state) (C : execution_ctx) ((expr_puremath_op_1 (JsNumber.add : (number -> (number -> number))) (y1 : (specret (value * value)))) : ext_expr) (o : out)) ->
        (* ------------------------------------------ *)
        (red_expr (S0 : state) (C : execution_ctx) ((expr_binary_op_add_1 ((specret_val S (v1, v2)) : (specret (value * value)))) : ext_expr) (o : out))

  | red_expr_puremath_op :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (op : binary_op (* input *)) (F : (number -> (number -> number))) (v1 : value (* input *)) (v2 : value (* input *)) (y1 : (specret (value * value))) (o : out),
        (puremath_op (op : binary_op) (F : (number -> (number -> number)))) ->
        (* ========================================== *)
        (red_spec S C (spec_convert_twice ((spec_to_number (v1 : value)) : ext_expr) ((spec_to_number (v2 : value)) : ext_expr)) y1) ->
        (red_expr (S : state) (C : execution_ctx) ((expr_puremath_op_1 (F : (number -> (number -> number))) (y1 : (specret (value * value)))) : ext_expr) (o : out)) ->
        (* ------------------------------------------ *)
        (red_expr (S : state) (C : execution_ctx) ((expr_binary_op_3 (op : binary_op) (v1 : value) (v2 : value)) : ext_expr) (o : out))

  | red_expr_puremath_op_1 :
      forall (S0 : state (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (F : (number -> (number -> number)) (* input *)) (n : number) (n1 : number (* input *)) (n2 : number (* input *)),
        (n = ((F n1 n2) : number)) ->
        (* ========================================== *)
        (* ------------------------------------------ *)
        (red_expr (S0 : state) (C : execution_ctx) ((expr_puremath_op_1 (F : (number -> (number -> number))) ((specret_val S ((value_prim (n1 : prim)), (value_prim (n2 : prim)))) : (specret (value * value)))) : ext_expr) ((out_ter (S : state) (n : res)) : out))

  | red_expr_shift_op :
      forall (b_unsigned : bool) (S : state (* input *)) (C : execution_ctx (* input *)) (op : binary_op (* input *)) (F : (int -> (int -> int))) (ext : (value -> ext_spec)) (v1 : value (* input *)) (v2 : value (* input *)) (y1 : (specret int)) (o : out),
        (shift_op (op : binary_op) (b_unsigned : bool) (F : (int -> (int -> int)))) ->
        ((ext : (value -> ext_spec)) = (ifb b_unsigned then (spec_to_uint32 : (value -> ext_spec)) else spec_to_int32)) ->
        (* ========================================== *)
        (red_spec S C (ext v1) y1) ->
        (red_expr (S : state) (C : execution_ctx) ((expr_shift_op_1 (F : (int -> (int -> int))) (y1 : (specret int)) (v2 : value)) : ext_expr) (o : out)) ->
        (* ------------------------------------------ *)
        (red_expr (S : state) (C : execution_ctx) ((expr_binary_op_3 (op : binary_op) (v1 : value) (v2 : value)) : ext_expr) (o : out))

  | red_expr_shift_op_1 :
      forall (S0 : state (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (F : (int -> (int -> int)) (* input *)) (k1 : int (* input *)) (v2 : value (* input *)) (y1 : (specret int)) (o : out),
        (* ========================================== *)
        (red_spec S C (spec_to_uint32 (v2 : value)) y1) ->
        (red_expr (S : state) (C : execution_ctx) ((expr_shift_op_2 (F : (int -> (int -> int))) (k1 : int) (y1 : (specret int))) : ext_expr) (o : out)) ->
        (* ------------------------------------------ *)
        (red_expr (S0 : state) (C : execution_ctx) ((expr_shift_op_1 (F : (int -> (int -> int))) ((specret_val S k1) : (specret int)) (v2 : value)) : ext_expr) (o : out))

  | red_expr_shift_op_2 :
      forall (S0 : state (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (k1 : int (* input *)) (k2 : int (* input *)) (F : (int -> (int -> int)) (* input *)) (n : number),
        (n = ((JsNumber.of_int (F k1 (JsNumber.modulo_32 k2))) : number)) ->
        (* ========================================== *)
        (* ------------------------------------------ *)
        (red_expr (S0 : state) (C : execution_ctx) ((expr_shift_op_2 (F : (int -> (int -> int))) (k1 : int) ((specret_val S k2) : (specret int))) : ext_expr) ((out_ter (S : state) (n : res)) : out))

  | red_expr_inequality_op :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (v1 : value (* input *)) (v2 : value (* input *)) (op : binary_op (* input *)) (b_swap : bool) (b_neg : bool) (o : out),
        (inequality_op (op : binary_op) (b_swap : bool) (b_neg : bool)) ->
        (* ========================================== *)
        (red_expr (S : state) (C : execution_ctx) ((expr_inequality_op_1 (b_swap : bool) (b_neg : bool) (v1 : value) (v2 : value)) : ext_expr) (o : out)) ->
        (* ------------------------------------------ *)
        (red_expr (S : state) (C : execution_ctx) ((expr_binary_op_3 (op : binary_op) (v1 : value) (v2 : value)) : ext_expr) (o : out))

  | red_expr_inequality_op_1 :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (v1 : value (* input *)) (v2 : value (* input *)) (b_swap : bool (* input *)) (b_neg : bool (* input *)) (y1 : (specret (value * value))) (o : out),
        (* ========================================== *)
        (red_spec S C (spec_convert_twice ((spec_to_primitive_auto (v1 : value)) : ext_expr) ((spec_to_primitive_auto (v2 : value)) : ext_expr)) y1) ->
        (red_expr (S : state) (C : execution_ctx) ((expr_inequality_op_2 (b_swap : bool) (b_neg : bool) (y1 : (specret (value * value)))) : ext_expr) (o : out)) ->
        (* ------------------------------------------ *)
        (red_expr (S : state) (C : execution_ctx) ((expr_inequality_op_1 (b_swap : bool) (b_neg : bool) (v1 : value) (v2 : value)) : ext_expr) (o : out))

  | red_expr_inequality_op_2 :
      forall (S0 : state (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (w1 : prim (* input *)) (w2 : prim (* input *)) (wa : prim) (wb : prim) (wr : prim) (wr' : prim) (b_swap : bool (* input *)) (b_neg : bool (* input *)),
        ((wa, wb) = ((ifb b_swap then ((w2, w1) : (prim * prim)) else (w1, w2)) : (prim * prim))) ->
        (wr = ((inequality_test_primitive (wa : prim) (wb : prim)) : prim)) ->
        (wr' = ((ifb (wr = (prim_undef : prim)) then (false : prim) else (ifb (((b_neg = true) : Prop) /\ ((wr = true) : Prop)) then (false : prim) else (ifb (((b_neg = true) : Prop) /\ ((wr = false) : Prop)) then (true : prim) else wr))) : prim)) ->
        (* ========================================== *)
        (* ------------------------------------------ *)
        (red_expr (S0 : state) (C : execution_ctx) ((expr_inequality_op_2 (b_swap : bool) (b_neg : bool) ((specret_val S ((value_prim (w1 : prim)), (value_prim (w2 : prim)))) : (specret (value * value)))) : ext_expr) ((out_ter (S : state) (wr' : res)) : out))

  | red_expr_binary_op_instanceof_non_object :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (v1 : value (* input *)) (v2 : value (* input *)) (o : out),
        (((type_of v2) : type) <> type_object) ->
        (* ========================================== *)
        (red_expr (S : state) (C : execution_ctx) ((spec_error (native_error_type : native_error)) : ext_expr) (o : out)) ->
        (* ------------------------------------------ *)
        (red_expr (S : state) (C : execution_ctx) ((expr_binary_op_3 (binary_op_instanceof : binary_op) (v1 : value) (v2 : value)) : ext_expr) (o : out))

  | red_expr_binary_op_instanceof_non_instance :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (v1 : value (* input *)) (l : object_loc (* input *)) (o : out),
        (object_method object_has_instance_ S l None) ->
        (* ========================================== *)
        (red_expr (S : state) (C : execution_ctx) ((spec_error (native_error_type : native_error)) : ext_expr) (o : out)) ->
        (* ------------------------------------------ *)
        (red_expr (S : state) (C : execution_ctx) ((expr_binary_op_3 (binary_op_instanceof : binary_op) (v1 : value) ((value_object (l : object_loc)) : value)) : ext_expr) (o : out))

  | red_expr_binary_op_instanceof_normal :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (v1 : value (* input *)) (l : object_loc (* input *)) (o : out),
        (* ========================================== *)
        (red_expr (S : state) (C : execution_ctx) ((spec_object_has_instance (l : object_loc) (v1 : value)) : ext_expr) (o : out)) ->
        (* ------------------------------------------ *)
        (red_expr (S : state) (C : execution_ctx) ((expr_binary_op_3 (binary_op_instanceof : binary_op) (v1 : value) ((value_object (l : object_loc)) : value)) : ext_expr) (o : out))

  | red_expr_binary_op_in_non_object :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (v1 : value (* input *)) (v2 : value (* input *)) (o : out),
        (((type_of v2) : type) <> type_object) ->
        (* ========================================== *)
        (red_expr (S : state) (C : execution_ctx) ((spec_error (native_error_type : native_error)) : ext_expr) (o : out)) ->
        (* ------------------------------------------ *)
        (red_expr (S : state) (C : execution_ctx) ((expr_binary_op_3 (binary_op_in : binary_op) (v1 : value) (v2 : value)) : ext_expr) (o : out))

  | red_expr_binary_op_in_object :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (v1 : value (* input *)) (l : object_loc (* input *)) (o1 : out) (o : out),
        (* ========================================== *)
        (red_expr (S : state) (C : execution_ctx) ((spec_to_string (v1 : value)) : ext_expr) (o1 : out)) ->
        (red_expr (S : state) (C : execution_ctx) ((expr_binary_op_in_1 (l : object_loc) (o1 : out)) : ext_expr) (o : out)) ->
        (* ------------------------------------------ *)
        (red_expr (S : state) (C : execution_ctx) ((expr_binary_op_3 (binary_op_in : binary_op) (v1 : value) ((value_object (l : object_loc)) : value)) : ext_expr) (o : out))

  | red_expr_binary_op_in_1 :
      forall (S0 : state (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (l : object_loc (* input *)) (x : prop_name (* input *)) (o : out),
        (* ========================================== *)
        (red_expr (S : state) (C : execution_ctx) ((spec_object_has_prop (l : object_loc) (x : prop_name)) : ext_expr) (o : out)) ->
        (* ------------------------------------------ *)
        (red_expr (S0 : state) (C : execution_ctx) ((expr_binary_op_in_1 (l : object_loc) ((out_ter (S : state) (x : res)) : out)) : ext_expr) (o : out))

  | red_expr_binary_op_equal :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (v1 : value (* input *)) (v2 : value (* input *)) (o : out),
        (* ========================================== *)
        (red_expr (S : state) (C : execution_ctx) ((spec_equal (v1 : value) (v2 : value)) : ext_expr) (o : out)) ->
        (* ------------------------------------------ *)
        (red_expr (S : state) (C : execution_ctx) ((expr_binary_op_3 (binary_op_equal : binary_op) (v1 : value) (v2 : value)) : ext_expr) (o : out))

  | red_expr_binary_op_disequal :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (v1 : value (* input *)) (v2 : value (* input *)) (o1 : out) (o : out),
        (* ========================================== *)
        (red_expr (S : state) (C : execution_ctx) ((spec_equal (v1 : value) (v2 : value)) : ext_expr) (o1 : out)) ->
        (red_expr (S : state) (C : execution_ctx) ((expr_binary_op_disequal_1 (o1 : out)) : ext_expr) (o : out)) ->
        (* ------------------------------------------ *)
        (red_expr (S : state) (C : execution_ctx) ((expr_binary_op_3 (binary_op_disequal : binary_op) (v1 : value) (v2 : value)) : ext_expr) (o : out))

  | red_expr_binary_op_disequal_1 :
      forall (S0 : state (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (b : bool (* input *)),
        (* ========================================== *)
        (* ------------------------------------------ *)
        (red_expr (S0 : state) (C : execution_ctx) ((expr_binary_op_disequal_1 ((out_ter (S : state) (b : res)) : out)) : ext_expr) ((out_ter (S : state) ((negb b) : res)) : out))

  | red_spec_equal :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (v1 : value (* input *)) (v2 : value (* input *)) (ty1 : type) (ty2 : type) (o : out),
        (ty1 = ((type_of v1) : type)) ->
        (ty2 = ((type_of v2) : type)) ->
        (* ========================================== *)
        (red_expr (S : state) (C : execution_ctx) ((spec_equal_1 (ty1 : type) (ty2 : type) (v1 : value) (v2 : value)) : ext_expr) (o : out)) ->
        (* ------------------------------------------ *)
        (red_expr (S : state) (C : execution_ctx) ((spec_equal (v1 : value) (v2 : value)) : ext_expr) (o : out))

  | red_spec_equal_1_same_type :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (v1 : value (* input *)) (v2 : value (* input *)) (ty : type (* input *)) (b : bool),
        (b = ((equality_test_for_same_type (ty : type) (v1 : value) (v2 : value)) : bool)) ->
        (* ========================================== *)
        (* ------------------------------------------ *)
        (red_expr (S : state) (C : execution_ctx) ((spec_equal_1 (ty : type) (ty : type) (v1 : value) (v2 : value)) : ext_expr) ((out_ter (S : state) (b : res)) : out))

  | red_spec_equal_1_diff_type :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (v1 : value (* input *)) (v2 : value (* input *)) (ty1 : type (* input *)) (ty2 : type (* input *)) (ext : ext_expr) (o : out),
        ((ext : ext_expr) = (ifb (((ty1 = type_null) : Prop) /\ ((ty2 = type_undef) : Prop)) then ((spec_equal_2 (true : bool)) : ext_expr) else (ifb (((ty1 = type_undef) : Prop) /\ ((ty2 = type_null) : Prop)) then ((spec_equal_2 (true : bool)) : ext_expr) else (ifb (((ty1 = type_number) : Prop) /\ ((ty2 = type_string) : Prop)) then ((spec_equal_3 (v1 : value) (spec_to_number : (value -> ext_expr)) (v2 : value)) : ext_expr) else (ifb (((ty1 = type_string) : Prop) /\ ((ty2 = type_number) : Prop)) then ((spec_equal_3 (v2 : value) (spec_to_number : (value -> ext_expr)) (v1 : value)) : ext_expr) else (ifb (ty1 = (type_bool : type)) then ((spec_equal_3 (v2 : value) (spec_to_number : (value -> ext_expr)) (v1 : value)) : ext_expr) else (ifb (ty2 = (type_bool : type)) then ((spec_equal_3 (v1 : value) (spec_to_number : (value -> ext_expr)) (v2 : value)) : ext_expr) else (ifb ((((ty1 = type_string) \/ (ty1 = type_number)) : Prop) /\ ((ty2 = type_object) : Prop)) then ((spec_equal_3 (v1 : value) (spec_to_primitive_auto : (value -> ext_expr)) (v2 : value)) : ext_expr) else (ifb (((ty1 = type_object) : Prop) /\ (((ty2 = type_string) \/ (ty2 = type_number)) : Prop)) then ((spec_equal_3 (v2 : value) (spec_to_primitive_auto : (value -> ext_expr)) (v1 : value)) : ext_expr) else (spec_equal_2 (false : bool))))))))))) ->
        (* ========================================== *)
        (red_expr (S : state) (C : execution_ctx) (ext : ext_expr) (o : out)) ->
        (* ------------------------------------------ *)
        (red_expr (S : state) (C : execution_ctx) ((spec_equal_1 (ty1 : type) (ty2 : type) (v1 : value) (v2 : value)) : ext_expr) (o : out))

  | red_spec_equal_2_return :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (b : bool (* input *)),
        (* ========================================== *)
        (* ------------------------------------------ *)
        (red_expr (S : state) (C : execution_ctx) ((spec_equal_2 (b : bool)) : ext_expr) ((out_ter (S : state) (b : res)) : out))

  | red_spec_equal_3_convert_and_recurse :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (v1 : value (* input *)) (v2 : value (* input *)) (K : (value -> ext_expr) (* input *)) (o2 : out) (o : out),
        (* ========================================== *)
        (red_expr (S : state) (C : execution_ctx) ((K v2) : ext_expr) (o2 : out)) ->
        (red_expr (S : state) (C : execution_ctx) ((spec_equal_4 (v1 : value) (o2 : out)) : ext_expr) (o : out)) ->
        (* ------------------------------------------ *)
        (red_expr (S : state) (C : execution_ctx) ((spec_equal_3 (v1 : value) (K : (value -> ext_expr)) (v2 : value)) : ext_expr) (o : out))

  | red_spec_equal_4_recurse :
      forall (S0 : state (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (v1 : value (* input *)) (v2 : value (* input *)) (o : out),
        (* ========================================== *)
        (red_expr (S : state) (C : execution_ctx) ((spec_equal (v1 : value) (v2 : value)) : ext_expr) (o : out)) ->
        (* ------------------------------------------ *)
        (red_expr (S0 : state) (C : execution_ctx) ((spec_equal_4 (v1 : value) ((out_ter (S : state) (v2 : res)) : out)) : ext_expr) (o : out))

  | red_expr_binary_op_strict_equal :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (v1 : value (* input *)) (v2 : value (* input *)) (b : bool),
        (b = ((strict_equality_test (v1 : value) (v2 : value)) : bool)) ->
        (* ========================================== *)
        (* ------------------------------------------ *)
        (red_expr (S : state) (C : execution_ctx) ((expr_binary_op_3 (binary_op_strict_equal : binary_op) (v1 : value) (v2 : value)) : ext_expr) ((out_ter (S : state) (b : res)) : out))

  | red_expr_binary_op_strict_disequal :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (v1 : value (* input *)) (v2 : value (* input *)) (b : bool),
        (b = ((negb (strict_equality_test (v1 : value) (v2 : value))) : bool)) ->
        (* ========================================== *)
        (* ------------------------------------------ *)
        (red_expr (S : state) (C : execution_ctx) ((expr_binary_op_3 (binary_op_strict_disequal : binary_op) (v1 : value) (v2 : value)) : ext_expr) ((out_ter (S : state) (b : res)) : out))

  | red_expr_bitwise_op :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (op : binary_op (* input *)) (F : (int -> (int -> int))) (v1 : value (* input *)) (v2 : value (* input *)) (y1 : (specret int)) (o : out),
        (bitwise_op (op : binary_op) (F : (int -> (int -> int)))) ->
        (* ========================================== *)
        (red_spec S C (spec_to_int32 (v1 : value)) y1) ->
        (red_expr (S : state) (C : execution_ctx) ((expr_bitwise_op_1 (F : (int -> (int -> int))) (y1 : (specret int)) (v2 : value)) : ext_expr) (o : out)) ->
        (* ------------------------------------------ *)
        (red_expr (S : state) (C : execution_ctx) ((expr_binary_op_3 (op : binary_op) (v1 : value) (v2 : value)) : ext_expr) (o : out))

  | red_expr_bitwise_op_1 :
      forall (S0 : state (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (F : (int -> (int -> int)) (* input *)) (k1 : int (* input *)) (v2 : value (* input *)) (y1 : (specret int)) (o : out),
        (* ========================================== *)
        (red_spec S C (spec_to_int32 (v2 : value)) y1) ->
        (red_expr (S : state) (C : execution_ctx) ((expr_bitwise_op_2 (F : (int -> (int -> int))) (k1 : int) (y1 : (specret int))) : ext_expr) (o : out)) ->
        (* ------------------------------------------ *)
        (red_expr (S0 : state) (C : execution_ctx) ((expr_bitwise_op_1 (F : (int -> (int -> int))) ((specret_val S k1) : (specret int)) (v2 : value)) : ext_expr) (o : out))

  | red_expr_bitwise_op_2 :
      forall (S0 : state (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (F : (int -> (int -> int)) (* input *)) (k1 : int (* input *)) (k2 : int (* input *)) (n : number),
        (n = ((JsNumber.of_int (F k1 k2)) : number)) ->
        (* ========================================== *)
        (* ------------------------------------------ *)
        (red_expr (S0 : state) (C : execution_ctx) ((expr_bitwise_op_2 (F : (int -> (int -> int))) (k1 : int) ((specret_val S k2) : (specret int))) : ext_expr) ((out_ter (S : state) (n : res)) : out))

  | red_expr_binary_op_lazy :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (op : binary_op (* input *)) (b_ret : bool) (e1 : expr (* input *)) (e2 : expr (* input *)) (y1 : (specret value)) (o : out),
        (lazy_op (op : binary_op) (b_ret : bool)) ->
        (* ========================================== *)
        (red_spec S C (spec_expr_get_value (e1 : expr)) y1) ->
        (red_expr (S : state) (C : execution_ctx) ((expr_lazy_op_1 (b_ret : bool) (y1 : (specret value)) (e2 : expr)) : ext_expr) (o : out)) ->
        (* ------------------------------------------ *)
        (red_expr (S : state) (C : execution_ctx) ((expr_binary_op (e1 : expr) (op : binary_op) (e2 : expr)) : ext_expr) (o : out))

  | red_expr_lazy_op_1 :
      forall (S0 : state (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (b_ret : bool (* input *)) (e2 : expr (* input *)) (v1 : value (* input *)) (o1 : out) (o : out),
        (* ========================================== *)
        (red_expr (S : state) (C : execution_ctx) ((spec_to_boolean (v1 : value)) : ext_expr) (o1 : out)) ->
        (red_expr (S : state) (C : execution_ctx) ((expr_lazy_op_2 (b_ret : bool) (v1 : value) (o1 : out) (e2 : expr)) : ext_expr) (o : out)) ->
        (* ------------------------------------------ *)
        (red_expr (S0 : state) (C : execution_ctx) ((expr_lazy_op_1 (b_ret : bool) ((specret_val S v1) : (specret value)) (e2 : expr)) : ext_expr) (o : out))

  | red_expr_lazy_op_2_first :
      forall (S0 : state (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (b_ret : bool (* input *)) (b1 : bool (* input *)) (e2 : expr (* input *)) (v1 : value (* input *)),
        (b1 = (b_ret : bool)) ->
        (* ========================================== *)
        (* ------------------------------------------ *)
        (red_expr (S0 : state) (C : execution_ctx) ((expr_lazy_op_2 (b_ret : bool) (v1 : value) ((out_ter (S : state) (b1 : res)) : out) (e2 : expr)) : ext_expr) ((out_ter (S : state) (v1 : res)) : out))

  | red_expr_lazy_op_2_second :
      forall (S0 : state (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (v1 : value (* input *)) (b_ret : bool (* input *)) (b1 : bool (* input *)) (e2 : expr (* input *)) (y1 : (specret value)) (o : out),
        (b1 <> (b_ret : bool)) ->
        (* ========================================== *)
        (red_spec S C (spec_expr_get_value (e2 : expr)) y1) ->
        (red_expr (S : state) (C : execution_ctx) ((expr_lazy_op_2_1 (y1 : (specret value))) : ext_expr) (o : out)) ->
        (* ------------------------------------------ *)
        (red_expr (S0 : state) (C : execution_ctx) ((expr_lazy_op_2 (b_ret : bool) (v1 : value) ((out_ter (S : state) (b1 : res)) : out) (e2 : expr)) : ext_expr) (o : out))

  | red_expr_lazy_op_2_second_1 :
      forall (S0 : state (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (v : value (* input *)),
        (* ========================================== *)
        (* ------------------------------------------ *)
        (red_expr (S0 : state) (C : execution_ctx) ((expr_lazy_op_2_1 ((specret_val S v) : (specret value))) : ext_expr) ((out_ter (S : state) (v : res)) : out))

  | red_expr_conditional :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (e1 : expr (* input *)) (e2 : expr (* input *)) (e3 : expr (* input *)) (y1 : (specret value)) (o : out),
        (* ========================================== *)
        (red_spec S C (spec_expr_get_value_conv (spec_to_boolean : (value -> ext_expr)) (e1 : expr)) y1) ->
        (red_expr (S : state) (C : execution_ctx) ((expr_conditional_1 (y1 : (specret value)) (e2 : expr) (e3 : expr)) : ext_expr) (o : out)) ->
        (* ------------------------------------------ *)
        (red_expr (S : state) (C : execution_ctx) ((expr_conditional (e1 : expr) (e2 : expr) (e3 : expr)) : ext_expr) (o : out))

  | red_expr_conditional_1 :
      forall (S0 : state (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (e : expr) (b : bool (* input *)) (e2 : expr (* input *)) (e3 : expr (* input *)) (y1 : (specret value)) (o : out),
        (e = ((ifb (b = (true : bool)) then (e2 : expr) else e3) : expr)) ->
        (* ========================================== *)
        (red_spec S C (spec_expr_get_value (e : expr)) y1) ->
        (red_expr (S : state) (C : execution_ctx) ((expr_conditional_2 (y1 : (specret value))) : ext_expr) (o : out)) ->
        (* ------------------------------------------ *)
        (red_expr (S0 : state) (C : execution_ctx) ((expr_conditional_1 ((specret_val (S : state) (b : value)) : (specret value)) (e2 : expr) (e3 : expr)) : ext_expr) (o : out))

  | red_expr_conditional_2 :
      forall (S0 : state (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (v : value (* input *)),
        (* ========================================== *)
        (* ------------------------------------------ *)
        (red_expr (S0 : state) (C : execution_ctx) ((expr_conditional_2 ((specret_val S v) : (specret value))) : ext_expr) ((out_ter (S : state) (v : res)) : out))

  | red_expr_assign :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (opo : (option binary_op) (* input *)) (e1 : expr (* input *)) (e2 : expr (* input *)) (o : out) (o1 : out),
        (* ========================================== *)
        (red_expr (S : state) (C : execution_ctx) (e1 : ext_expr) (o1 : out)) ->
        (red_expr (S : state) (C : execution_ctx) ((expr_assign_1 (o1 : out) (opo : (option binary_op)) (e2 : expr)) : ext_expr) (o : out)) ->
        (* ------------------------------------------ *)
        (red_expr (S : state) (C : execution_ctx) ((expr_assign (e1 : expr) (opo : (option binary_op)) (e2 : expr)) : ext_expr) (o : out))

  | red_expr_assign_1_simple :
      forall (S0 : state (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (rv : resvalue (* input *)) (e2 : expr (* input *)) (y1 : (specret value)) (o : out),
        (* ========================================== *)
        (red_spec S C (spec_expr_get_value (e2 : expr)) y1) ->
        (red_expr (S : state) (C : execution_ctx) ((expr_assign_4 (rv : res) (y1 : (specret value))) : ext_expr) (o : out)) ->
        (* ------------------------------------------ *)
        (red_expr (S0 : state) (C : execution_ctx) ((expr_assign_1 ((out_ter (S : state) (rv : res)) : out) (None : (option binary_op)) (e2 : expr)) : ext_expr) (o : out))

  | red_expr_assign_1_compound :
      forall (S0 : state (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (rv : resvalue (* input *)) (op : binary_op (* input *)) (e2 : expr (* input *)) (y1 : (specret value)) (o : out),
        (* ========================================== *)
        (red_spec S C (spec_get_value (rv : resvalue)) y1) ->
        (red_expr (S : state) (C : execution_ctx) ((expr_assign_2 (rv : res) (y1 : (specret value)) (op : binary_op) (e2 : expr)) : ext_expr) (o : out)) ->
        (* ------------------------------------------ *)
        (red_expr (S0 : state) (C : execution_ctx) ((expr_assign_1 ((out_ter (S : state) (rv : res)) : out) ((Some op) : (option binary_op)) (e2 : expr)) : ext_expr) (o : out))

  | red_expr_assign_2_compound_get_value :
      forall (S0 : state (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (rv : resvalue (* input *)) (op : binary_op (* input *)) (v1 : value (* input *)) (e2 : expr (* input *)) (y1 : (specret value)) (o : out),
        (* ========================================== *)
        (red_spec S C (spec_expr_get_value (e2 : expr)) y1) ->
        (red_expr (S : state) (C : execution_ctx) ((expr_assign_3 (rv : res) (v1 : value) (op : binary_op) (y1 : (specret value))) : ext_expr) (o : out)) ->
        (* ------------------------------------------ *)
        (red_expr (S0 : state) (C : execution_ctx) ((expr_assign_2 (rv : res) ((specret_val S v1) : (specret value)) (op : binary_op) (e2 : expr)) : ext_expr) (o : out))

  | red_expr_assign_3_compound_op :
      forall (S0 : state (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (rv : resvalue (* input *)) (op : binary_op (* input *)) (v1 : value (* input *)) (v2 : value (* input *)) (o1 : out) (o : out),
        (* ========================================== *)
        (red_expr (S : state) (C : execution_ctx) ((expr_binary_op_3 (op : binary_op) (v1 : value) (v2 : value)) : ext_expr) (o1 : out)) ->
        (red_expr (S : state) (C : execution_ctx) ((expr_assign_3' (rv : res) (o1 : out)) : ext_expr) (o : out)) ->
        (* ------------------------------------------ *)
        (red_expr (S0 : state) (C : execution_ctx) ((expr_assign_3 (rv : res) (v1 : value) (op : binary_op) ((specret_val S v2) : (specret value))) : ext_expr) (o : out))

  | red_expr_assign_3' :
      forall (S0 : state (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (v : value (* input *)) (rv : resvalue (* input *)) (o : out),
        (* ========================================== *)
        (red_expr (S : state) (C : execution_ctx) ((expr_assign_4 (rv : res) ((ret S v) : (specret value))) : ext_expr) (o : out)) ->
        (* ------------------------------------------ *)
        (red_expr (S0 : state) (C : execution_ctx) ((expr_assign_3' (rv : res) ((out_ter (S : state) (v : res)) : out)) : ext_expr) (o : out))

  | red_expr_assign_4_put_value :
      forall (S0 : state (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (rv : resvalue (* input *)) (v : value (* input *)) (o1 : out) (o : out),
        (* ========================================== *)
        (red_expr (S : state) (C : execution_ctx) ((spec_put_value (rv : resvalue) (v : value)) : ext_expr) (o1 : out)) ->
        (red_expr (S : state) (C : execution_ctx) ((expr_assign_5 (v : value) (o1 : out)) : ext_expr) (o : out)) ->
        (* ------------------------------------------ *)
        (red_expr (S0 : state) (C : execution_ctx) ((expr_assign_4 (rv : res) ((specret_val S v) : (specret value))) : ext_expr) (o : out))

  | red_expr_assign_5_return :
      forall (S0 : state (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (rv' : resvalue (* input *)) (v : value (* input *)),
        (* ========================================== *)
        (* ------------------------------------------ *)
        (red_expr (S0 : state) (C : execution_ctx) ((expr_assign_5 (v : value) ((out_ter (S : state) (rv' : res)) : out)) : ext_expr) ((out_ter (S : state) (v : res)) : out))

  | red_expr_binary_op_coma :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (v1 : value (* input *)) (v2 : value (* input *)),
        (* ========================================== *)
        (* ------------------------------------------ *)
        (red_expr (S : state) (C : execution_ctx) ((expr_binary_op_3 (binary_op_coma : binary_op) (v1 : value) (v2 : value)) : ext_expr) ((out_ter (S : state) (v2 : res)) : out))

  | red_spec_returns :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (o : out (* input *)),
        (* ========================================== *)
        (* ------------------------------------------ *)
        (red_expr (S : state) (C : execution_ctx) ((spec_returns (o : out)) : ext_expr) (o : out))

  | red_spec_prim_new_object_bool :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (b : bool (* input *)) (S' : state) (l : object_loc),
        let O1 : object := (object_new prealloc_bool_proto (("Boolean")%string)) in
        let O : object := (object_with_primitive_value O1 b) in
        ((l, S') = ((object_alloc S O) : (object_loc * state))) ->
        (* ========================================== *)
        (* ------------------------------------------ *)
        (red_expr (S : state) (C : execution_ctx) ((spec_prim_new_object ((prim_bool (b : bool)) : prim)) : ext_expr) ((out_ter (S' : state) (l : res)) : out))

  | red_spec_prim_new_object_number :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (n : number (* input *)) (S' : state) (l : object_loc),
        let O1 : object := (object_new prealloc_number_proto (("Number")%string)) in
        let O : object := (object_with_primitive_value O1 n) in
        ((l, S') = ((object_alloc S O) : (object_loc * state))) ->
        (* ========================================== *)
        (* ------------------------------------------ *)
        (red_expr (S : state) (C : execution_ctx) ((spec_prim_new_object ((prim_number (n : number)) : prim)) : ext_expr) ((out_ter (S' : state) (l : res)) : out))

  | red_spec_prim_new_object_string :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (s : string (* input *)) (S' : state) (l : object_loc),
        let O2 : object := (object_new prealloc_string_proto (("String")%string)) in
        let O1 : object := (object_with_get_own_property O2 builtin_get_own_prop_string) in
        let O : object := (object_with_primitive_value O1 s) in
        ((l, S') = ((object_alloc S O) : (object_loc * state))) ->
        (* ========================================== *)
        (* ------------------------------------------ *)
        (red_expr (S : state) (C : execution_ctx) ((spec_prim_new_object ((prim_string (s : string)) : prim)) : ext_expr) ((out_ter (S' : state) (l : res)) : out))

  | red_spec_to_primitive_pref_prim :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (w : prim (* input *)) (prefo : (option preftype) (* input *)),
        (* ========================================== *)
        (* ------------------------------------------ *)
        (red_expr (S : state) (C : execution_ctx) ((spec_to_primitive ((value_prim (w : prim)) : value) (prefo : (option preftype))) : ext_expr) ((out_ter (S : state) (w : res)) : out))

  | red_spec_to_primitive_pref_object :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (l : object_loc (* input *)) (prefo : (option preftype) (* input *)) (o : out),
        (* ========================================== *)
        (red_expr (S : state) (C : execution_ctx) ((spec_object_default_value (l : object_loc) (prefo : (option preftype))) : ext_expr) (o : out)) ->
        (* ------------------------------------------ *)
        (red_expr (S : state) (C : execution_ctx) ((spec_to_primitive ((value_object (l : object_loc)) : value) (prefo : (option preftype))) : ext_expr) (o : out))

  | red_spec_to_boolean :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (v : value (* input *)) (b : bool),
        (b = ((convert_value_to_boolean (v : value)) : bool)) ->
        (* ========================================== *)
        (* ------------------------------------------ *)
        (red_expr (S : state) (C : execution_ctx) ((spec_to_boolean (v : value)) : ext_expr) ((out_ter (S : state) (b : res)) : out))

  | red_spec_to_number_prim :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (w : prim (* input *)) (n : number),
        (n = ((convert_prim_to_number (w : prim)) : number)) ->
        (* ========================================== *)
        (* ------------------------------------------ *)
        (red_expr (S : state) (C : execution_ctx) ((spec_to_number ((value_prim (w : prim)) : value)) : ext_expr) ((out_ter (S : state) (n : res)) : out))

  | red_spec_to_number_object :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (l : object_loc (* input *)) (o1 : out) (o : out),
        (* ========================================== *)
        (red_expr (S : state) (C : execution_ctx) ((spec_to_primitive ((value_object (l : object_loc)) : value) ((Some preftype_number) : (option preftype))) : ext_expr) (o1 : out)) ->
        (red_expr (S : state) (C : execution_ctx) ((spec_to_number_1 (o1 : out)) : ext_expr) (o : out)) ->
        (* ------------------------------------------ *)
        (red_expr (S : state) (C : execution_ctx) ((spec_to_number ((value_object (l : object_loc)) : value)) : ext_expr) (o : out))

  | red_spec_to_number_1 :
      forall (S0 : state (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (w : prim (* input *)) (n : number),
        (n = ((convert_prim_to_number (w : prim)) : number)) ->
        (* ========================================== *)
        (* ------------------------------------------ *)
        (red_expr (S0 : state) (C : execution_ctx) ((spec_to_number_1 ((out_ter (S : state) (w : res)) : out)) : ext_expr) ((out_ter (S : state) (n : res)) : out))

  | red_spec_to_integer :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (v : value (* input *)) (o1 : out) (o : out),
        (* ========================================== *)
        (red_expr (S : state) (C : execution_ctx) ((spec_to_number (v : value)) : ext_expr) (o1 : out)) ->
        (red_expr (S : state) (C : execution_ctx) ((spec_to_integer_1 (o1 : out)) : ext_expr) (o : out)) ->
        (* ------------------------------------------ *)
        (red_expr (S : state) (C : execution_ctx) ((spec_to_integer (v : value)) : ext_expr) (o : out))

  | red_spec_to_integer_1 :
      forall (S0 : state (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (n : number (* input *)) (n' : number),
        (n' = ((convert_number_to_integer (n : number)) : number)) ->
        (* ========================================== *)
        (* ------------------------------------------ *)
        (red_expr (S0 : state) (C : execution_ctx) ((spec_to_integer_1 ((out_ter (S : state) (n : res)) : out)) : ext_expr) ((out_ter (S : state) (n' : res)) : out))

  | red_spec_to_string_prim :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (w : prim (* input *)) (s : string),
        (s = ((convert_prim_to_string (w : prim)) : string)) ->
        (* ========================================== *)
        (* ------------------------------------------ *)
        (red_expr (S : state) (C : execution_ctx) ((spec_to_string ((value_prim (w : prim)) : value)) : ext_expr) ((out_ter (S : state) (s : res)) : out))

  | red_spec_to_string_object :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (l : object_loc (* input *)) (o1 : out) (o : out),
        (* ========================================== *)
        (red_expr (S : state) (C : execution_ctx) ((spec_to_primitive ((value_object (l : object_loc)) : value) ((Some preftype_string) : (option preftype))) : ext_expr) (o1 : out)) ->
        (red_expr (S : state) (C : execution_ctx) ((spec_to_string_1 (o1 : out)) : ext_expr) (o : out)) ->
        (* ------------------------------------------ *)
        (red_expr (S : state) (C : execution_ctx) ((spec_to_string ((value_object (l : object_loc)) : value)) : ext_expr) (o : out))

  | red_spec_to_string_1 :
      forall (S0 : state (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (w : prim (* input *)) (s : string),
        (s = ((convert_prim_to_string (w : prim)) : string)) ->
        (* ========================================== *)
        (* ------------------------------------------ *)
        (red_expr (S0 : state) (C : execution_ctx) ((spec_to_string_1 ((out_ter (S : state) (w : res)) : out)) : ext_expr) ((out_ter (S : state) (s : res)) : out))

  | red_spec_to_object_undef_or_null :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (v : value (* input *)) (o : out),
        (((v = prim_undef) : Prop) \/ ((v = prim_null) : Prop)) ->
        (* ========================================== *)
        (red_expr (S : state) (C : execution_ctx) ((spec_error (native_error_type : native_error)) : ext_expr) (o : out)) ->
        (* ------------------------------------------ *)
        (red_expr (S : state) (C : execution_ctx) ((spec_to_object (v : value)) : ext_expr) (o : out))

  | red_spec_to_object_prim :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (w : prim (* input *)) (o : out),
        (~ (((w = prim_undef) : Prop) \/ ((w = prim_null) : Prop))) ->
        (* ========================================== *)
        (red_expr (S : state) (C : execution_ctx) ((spec_prim_new_object (w : prim)) : ext_expr) (o : out)) ->
        (* ------------------------------------------ *)
        (red_expr (S : state) (C : execution_ctx) ((spec_to_object ((value_prim (w : prim)) : value)) : ext_expr) (o : out))

  | red_spec_to_object_object :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (l : object_loc (* input *)),
        (* ========================================== *)
        (* ------------------------------------------ *)
        (red_expr (S : state) (C : execution_ctx) ((spec_to_object ((value_object (l : object_loc)) : value)) : ext_expr) ((out_ter (S : state) (l : res)) : out))

  | red_spec_check_object_coercible_undef_or_null :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (v : value (* input *)) (o : out),
        (((v = prim_undef) : Prop) \/ ((v = prim_null) : Prop)) ->
        (* ========================================== *)
        (red_expr (S : state) (C : execution_ctx) ((spec_error (native_error_type : native_error)) : ext_expr) (o : out)) ->
        (* ------------------------------------------ *)
        (red_expr (S : state) (C : execution_ctx) ((spec_check_object_coercible (v : value)) : ext_expr) (o : out))

  | red_spec_check_object_coercible_return :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (v : value (* input *)),
        (~ (((v = prim_undef) : Prop) \/ ((v = prim_null) : Prop))) ->
        (* ========================================== *)
        (* ------------------------------------------ *)
        (red_expr (S : state) (C : execution_ctx) ((spec_check_object_coercible (v : value)) : ext_expr) ((out_void (S : state)) : out))

  | red_spec_object_get :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (l : object_loc (* input *)) (x : prop_name (* input *)) (B : builtin_get) (o : out),
        (object_method object_get_ S l B) ->
        (* ========================================== *)
        (red_expr (S : state) (C : execution_ctx) ((spec_object_get_1 (B : builtin_get) (l : value) (l : object_loc) (x : prop_name)) : ext_expr) (o : out)) ->
        (* ------------------------------------------ *)
        (red_expr (S : state) (C : execution_ctx) ((spec_object_get (l : value) (x : prop_name)) : ext_expr) (o : out))

  | red_spec_object_put :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (l : object_loc (* input *)) (x : prop_name (* input *)) (v : value (* input *)) (throw : bool (* input *)) (B : builtin_put) (o : out),
        (object_method object_put_ S l B) ->
        (* ========================================== *)
        (red_expr (S : state) (C : execution_ctx) ((spec_object_put_1 (B : builtin_put) (l : value) (l : object_loc) (x : prop_name) (v : value) (throw : bool)) : ext_expr) (o : out)) ->
        (* ------------------------------------------ *)
        (red_expr (S : state) (C : execution_ctx) ((spec_object_put (l : value) (x : prop_name) (v : value) (throw : bool)) : ext_expr) (o : out))

  | red_spec_object_can_put :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (l : object_loc (* input *)) (x : prop_name (* input *)) (B : builtin_can_put) (o : out),
        (object_method object_can_put_ S l B) ->
        (* ========================================== *)
        (red_expr (S : state) (C : execution_ctx) ((spec_object_can_put_1 (B : builtin_can_put) (l : object_loc) (x : prop_name)) : ext_expr) (o : out)) ->
        (* ------------------------------------------ *)
        (red_expr (S : state) (C : execution_ctx) ((spec_object_can_put (l : object_loc) (x : prop_name)) : ext_expr) (o : out))

  | red_spec_object_has_prop :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (l : object_loc (* input *)) (x : prop_name (* input *)) (B : builtin_has_prop) (o : out),
        (object_method object_has_prop_ S l B) ->
        (* ========================================== *)
        (red_expr (S : state) (C : execution_ctx) ((spec_object_has_prop_1 (B : builtin_has_prop) (l : object_loc) (x : prop_name)) : ext_expr) (o : out)) ->
        (* ------------------------------------------ *)
        (red_expr (S : state) (C : execution_ctx) ((spec_object_has_prop (l : object_loc) (x : prop_name)) : ext_expr) (o : out))

  | red_spec_object_delete :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (l : object_loc (* input *)) (x : prop_name (* input *)) (throw : bool (* input *)) (B : builtin_delete) (o : out),
        (object_method object_delete_ S l B) ->
        (* ========================================== *)
        (red_expr (S : state) (C : execution_ctx) ((spec_object_delete_1 (B : builtin_delete) (l : object_loc) (x : prop_name) (throw : bool)) : ext_expr) (o : out)) ->
        (* ------------------------------------------ *)
        (red_expr (S : state) (C : execution_ctx) ((spec_object_delete (l : object_loc) (x : prop_name) (throw : bool)) : ext_expr) (o : out))

  | red_spec_object_default_value :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (l : object_loc (* input *)) (prefo : (option preftype) (* input *)) (B : builtin_default_value) (o : out),
        (object_method object_default_value_ S l B) ->
        (* ========================================== *)
        (red_expr (S : state) (C : execution_ctx) ((spec_object_default_value_1 (B : builtin_default_value) (l : object_loc) (prefo : (option preftype))) : ext_expr) (o : out)) ->
        (* ------------------------------------------ *)
        (red_expr (S : state) (C : execution_ctx) ((spec_object_default_value (l : object_loc) (prefo : (option preftype))) : ext_expr) (o : out))

  | red_spec_object_define_own_prop :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (l : object_loc (* input *)) (x : prop_name (* input *)) (Desc : descriptor (* input *)) (throw : bool (* input *)) (B : builtin_define_own_prop) (o : out),
        (object_method object_define_own_prop_ S l B) ->
        (* ========================================== *)
        (red_expr (S : state) (C : execution_ctx) ((spec_object_define_own_prop_1 (B : builtin_define_own_prop) (l : object_loc) (x : prop_name) (Desc : descriptor) (throw : bool)) : ext_expr) (o : out)) ->
        (* ------------------------------------------ *)
        (red_expr (S : state) (C : execution_ctx) ((spec_object_define_own_prop (l : object_loc) (x : prop_name) (Desc : descriptor) (throw : bool)) : ext_expr) (o : out))

  | red_spec_object_has_instance :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (l : object_loc (* input *)) (v : value (* input *)) (B : builtin_has_instance) (o : out),
        (object_method object_has_instance_ S l (Some B)) ->
        (* ========================================== *)
        (red_expr (S : state) (C : execution_ctx) ((spec_object_has_instance_1 (B : builtin_has_instance) (l : object_loc) (v : value)) : ext_expr) (o : out)) ->
        (* ------------------------------------------ *)
        (red_expr (S : state) (C : execution_ctx) ((spec_object_has_instance (l : object_loc) (v : value)) : ext_expr) (o : out))

  | red_spec_call :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (l : object_loc (* input *)) (B : call) (this : value (* input *)) (args : (list value) (* input *)) (o : out),
        (object_method object_call_ S l (Some B)) ->
        (* ========================================== *)
        (red_expr (S : state) (C : execution_ctx) ((spec_call_1 (B : call) (l : object_loc) (this : value) (args : (list value))) : ext_expr) (o : out)) ->
        (* ------------------------------------------ *)
        (red_expr (S : state) (C : execution_ctx) ((spec_call (l : object_loc) (this : value) (args : (list value))) : ext_expr) (o : out))

  | red_spec_constructor :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (l : object_loc (* input *)) (B : construct) (args : (list value) (* input *)) (o : out),
        (object_method object_construct_ S l (Some B)) ->
        (* ========================================== *)
        (red_expr (S : state) (C : execution_ctx) ((spec_construct_1 (B : construct) (l : object_loc) (args : (list value))) : ext_expr) (o : out)) ->
        (* ------------------------------------------ *)
        (red_expr (S : state) (C : execution_ctx) ((spec_construct (l : object_loc) (args : (list value))) : ext_expr) (o : out))

  | red_spec_call_1_prealloc :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (B : prealloc (* input *)) (lo : object_loc (* input *)) (this : value (* input *)) (args : (list value) (* input *)) (o : out),
        (* ========================================== *)
        (red_expr (S : state) (C : execution_ctx) ((spec_call_prealloc (B : prealloc) (this : value) (args : (list value))) : ext_expr) (o : out)) ->
        (* ------------------------------------------ *)
        (red_expr (S : state) (C : execution_ctx) ((spec_call_1 ((call_prealloc (B : prealloc)) : call) (lo : object_loc) (this : value) (args : (list value))) : ext_expr) (o : out))

  | red_spec_construct_1_prealloc :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (B : prealloc (* input *)) (l : object_loc (* input *)) (args : (list value) (* input *)) (o : out),
        (* ========================================== *)
        (red_expr (S : state) (C : execution_ctx) ((spec_construct_prealloc (B : prealloc) (args : (list value))) : ext_expr) (o : out)) ->
        (* ------------------------------------------ *)
        (red_expr (S : state) (C : execution_ctx) ((spec_construct_1 ((construct_prealloc (B : prealloc)) : construct) (l : object_loc) (args : (list value))) : ext_expr) (o : out))

  | red_spec_object_get_1_default :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (vthis : value (* input *)) (l : object_loc (* input *)) (x : prop_name (* input *)) (y1 : (specret full_descriptor)) (o : out),
        (* ========================================== *)
        (red_spec S C (spec_object_get_prop (l : object_loc) (x : prop_name)) y1) ->
        (red_expr (S : state) (C : execution_ctx) ((spec_object_get_2 (vthis : value) (y1 : (specret full_descriptor))) : ext_expr) (o : out)) ->
        (* ------------------------------------------ *)
        (red_expr (S : state) (C : execution_ctx) ((spec_object_get_1 (builtin_get_default : builtin_get) (vthis : value) (l : object_loc) (x : prop_name)) : ext_expr) (o : out))

  | red_spec_object_get_2_undef :
      forall (S0 : state (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (vthis : value (* input *)),
        (* ========================================== *)
        (* ------------------------------------------ *)
        (red_expr (S0 : state) (C : execution_ctx) ((spec_object_get_2 (vthis : value) ((specret_val (S : state) (full_descriptor_undef : full_descriptor)) : (specret full_descriptor))) : ext_expr) ((out_ter (S : state) (undef : res)) : out))

  | red_spec_object_get_2_data :
      forall (S0 : state (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (vthis : value (* input *)) (Ad : attributes_data (* input *)) (v : value),
        (v = ((attributes_data_value (Ad : attributes_data)) : value)) ->
        (* ========================================== *)
        (* ------------------------------------------ *)
        (red_expr (S0 : state) (C : execution_ctx) ((spec_object_get_2 (vthis : value) ((specret_val (S : state) ((attributes_data_of (Ad : attributes_data)) : full_descriptor)) : (specret full_descriptor))) : ext_expr) ((out_ter (S : state) (v : res)) : out))

  | red_spec_object_get_2_accessor :
      forall (S0 : state (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (vthis : value (* input *)) (Aa : attributes_accessor (* input *)) (o : out),
        (* ========================================== *)
        (red_expr (S : state) (C : execution_ctx) ((spec_object_get_3 (vthis : value) ((attributes_accessor_get (Aa : attributes_accessor)) : value)) : ext_expr) (o : out)) ->
        (* ------------------------------------------ *)
        (red_expr (S0 : state) (C : execution_ctx) ((spec_object_get_2 (vthis : value) ((specret_val (S : state) ((attributes_accessor_of (Aa : attributes_accessor)) : full_descriptor)) : (specret full_descriptor))) : ext_expr) (o : out))

  | red_spec_object_get_3_accessor_undef :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (vthis : value (* input *)),
        (* ========================================== *)
        (* ------------------------------------------ *)
        (red_expr (S : state) (C : execution_ctx) ((spec_object_get_3 (vthis : value) (undef : value)) : ext_expr) ((out_ter (S : state) (undef : res)) : out))

  | red_spec_object_get_3_accessor_object :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (vthis : value (* input *)) (lf : object_loc (* input *)) (o : out),
        (* ========================================== *)
        (red_expr (S : state) (C : execution_ctx) ((spec_call (lf : object_loc) (vthis : value) (nil : (list value))) : ext_expr) (o : out)) ->
        (* ------------------------------------------ *)
        (red_expr (S : state) (C : execution_ctx) ((spec_object_get_3 (vthis : value) (lf : value)) : ext_expr) (o : out))

  | red_spec_object_can_put_1_default :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (l : object_loc (* input *)) (x : prop_name (* input *)) (o : out) (y : (specret full_descriptor)),
        (* ========================================== *)
        (red_spec S C (spec_object_get_own_prop (l : object_loc) (x : prop_name)) y) ->
        (red_expr (S : state) (C : execution_ctx) ((spec_object_can_put_2 (l : object_loc) (x : prop_name) (y : (specret full_descriptor))) : ext_expr) (o : out)) ->
        (* ------------------------------------------ *)
        (red_expr (S : state) (C : execution_ctx) ((spec_object_can_put_1 (builtin_can_put_default : builtin_can_put) (l : object_loc) (x : prop_name)) : ext_expr) (o : out))

  | red_spec_object_can_put_2_accessor :
      forall (S0 : state (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (l : object_loc (* input *)) (x : prop_name (* input *)) (Aa : attributes_accessor (* input *)) (b : bool),
        (b = ((ifb ((attributes_accessor_set (Aa : attributes_accessor)) = (undef : value)) then (false : bool) else true) : bool)) ->
        (* ========================================== *)
        (* ------------------------------------------ *)
        (red_expr (S : state) (C : execution_ctx) ((spec_object_can_put_2 (l : object_loc) (x : prop_name) ((specret_val (S0 : state) ((attributes_accessor_of (Aa : attributes_accessor)) : full_descriptor)) : (specret full_descriptor))) : ext_expr) ((out_ter (S0 : state) (b : res)) : out))

  | red_spec_object_can_put_2_data :
      forall (S0 : state (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (l : object_loc (* input *)) (x : prop_name (* input *)) (Ad : attributes_data (* input *)) (b : bool),
        (b = ((attributes_data_writable (Ad : attributes_data)) : bool)) ->
        (* ========================================== *)
        (* ------------------------------------------ *)
        (red_expr (S : state) (C : execution_ctx) ((spec_object_can_put_2 (l : object_loc) (x : prop_name) ((specret_val (S0 : state) ((attributes_data_of (Ad : attributes_data)) : full_descriptor)) : (specret full_descriptor))) : ext_expr) ((out_ter (S0 : state) (b : res)) : out))

  | red_spec_object_can_put_2_undef :
      forall (S0 : state (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (l : object_loc (* input *)) (x : prop_name (* input *)) (o : out) (lproto : value),
        (object_proto (S : state) (l : object_loc) (lproto : value)) ->
        (* ========================================== *)
        (red_expr (S : state) (C : execution_ctx) ((spec_object_can_put_4 (l : object_loc) (x : prop_name) (lproto : value)) : ext_expr) (o : out)) ->
        (* ------------------------------------------ *)
        (red_expr (S0 : state) (C : execution_ctx) ((spec_object_can_put_2 (l : object_loc) (x : prop_name) ((specret_val S full_descriptor_undef) : (specret full_descriptor))) : ext_expr) (o : out))

  | red_spec_object_can_put_4_null :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (l : object_loc (* input *)) (x : prop_name (* input *)) (b : bool),
        (object_extensible (S : state) (l : object_loc) (b : bool)) ->
        (* ========================================== *)
        (* ------------------------------------------ *)
        (red_expr (S : state) (C : execution_ctx) ((spec_object_can_put_4 (l : object_loc) (x : prop_name) (null : value)) : ext_expr) ((out_ter (S : state) (b : res)) : out))

  | red_spec_object_can_put_4_not_null :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (l : object_loc (* input *)) (x : prop_name (* input *)) (lproto : object_loc (* input *)) (y1 : (specret full_descriptor)) (o : out),
        (* ========================================== *)
        (red_spec S C (spec_object_get_prop (lproto : object_loc) (x : prop_name)) y1) ->
        (red_expr (S : state) (C : execution_ctx) ((spec_object_can_put_5 (l : object_loc) (y1 : (specret full_descriptor))) : ext_expr) (o : out)) ->
        (* ------------------------------------------ *)
        (red_expr (S : state) (C : execution_ctx) ((spec_object_can_put_4 (l : object_loc) (x : prop_name) (lproto : value)) : ext_expr) (o : out))

  | red_spec_object_can_put_5_undef :
      forall (S0 : state (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (l : object_loc (* input *)) (b : bool),
        (object_extensible (S : state) (l : object_loc) (b : bool)) ->
        (* ========================================== *)
        (* ------------------------------------------ *)
        (red_expr (S0 : state) (C : execution_ctx) ((spec_object_can_put_5 (l : object_loc) ((specret_val (S : state) (full_descriptor_undef : full_descriptor)) : (specret full_descriptor))) : ext_expr) ((out_ter (S : state) (b : res)) : out))

  | red_spec_object_can_put_5_accessor :
      forall (S0 : state (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (l : object_loc (* input *)) (Aa : attributes_accessor (* input *)) (b : bool),
        (b = ((ifb ((attributes_accessor_set (Aa : attributes_accessor)) = (undef : value)) then (false : bool) else true) : bool)) ->
        (* ========================================== *)
        (* ------------------------------------------ *)
        (red_expr (S0 : state) (C : execution_ctx) ((spec_object_can_put_5 (l : object_loc) ((specret_val (S : state) ((attributes_accessor_of (Aa : attributes_accessor)) : full_descriptor)) : (specret full_descriptor))) : ext_expr) ((out_ter (S : state) (b : res)) : out))

  | red_spec_object_can_put_5_data :
      forall (S0 : state (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (l : object_loc (* input *)) (Ad : attributes_data (* input *)) (bext : bool) (o : out),
        (object_extensible (S : state) (l : object_loc) (bext : bool)) ->
        (* ========================================== *)
        (red_expr (S : state) (C : execution_ctx) ((spec_object_can_put_6 (Ad : attributes_data) (bext : bool)) : ext_expr) (o : out)) ->
        (* ------------------------------------------ *)
        (red_expr (S0 : state) (C : execution_ctx) ((spec_object_can_put_5 (l : object_loc) ((specret_val (S : state) ((attributes_data_of (Ad : attributes_data)) : full_descriptor)) : (specret full_descriptor))) : ext_expr) (o : out))

  | red_spec_object_can_put_6_extens_false :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (Ad : attributes_data (* input *)),
        (* ========================================== *)
        (* ------------------------------------------ *)
        (red_expr (S : state) (C : execution_ctx) ((spec_object_can_put_6 (Ad : attributes_data) (false : bool)) : ext_expr) ((out_ter (S : state) (false : res)) : out))

  | red_spec_object_can_put_6_extens_true :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (Ad : attributes_data (* input *)) (b : bool),
        (b = ((attributes_data_writable (Ad : attributes_data)) : bool)) ->
        (* ========================================== *)
        (* ------------------------------------------ *)
        (red_expr (S : state) (C : execution_ctx) ((spec_object_can_put_6 (Ad : attributes_data) (true : bool)) : ext_expr) ((out_ter (S : state) (b : res)) : out))

  | red_spec_object_put_1_default :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (vthis : value (* input *)) (l : object_loc (* input *)) (x : prop_name (* input *)) (v : value (* input *)) (throw : bool (* input *)) (o1 : out) (o : out),
        (* ========================================== *)
        (red_expr (S : state) (C : execution_ctx) ((spec_object_can_put (l : object_loc) (x : prop_name)) : ext_expr) (o1 : out)) ->
        (red_expr (S : state) (C : execution_ctx) ((spec_object_put_2 (vthis : value) (l : object_loc) (x : prop_name) (v : value) (throw : bool) (o1 : out)) : ext_expr) (o : out)) ->
        (* ------------------------------------------ *)
        (red_expr (S : state) (C : execution_ctx) ((spec_object_put_1 (builtin_put_default : builtin_put) (vthis : value) (l : object_loc) (x : prop_name) (v : value) (throw : bool)) : ext_expr) (o : out))

  | red_spec_object_put_2_false :
      forall (S0 : state (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (vthis : value (* input *)) (l : object_loc (* input *)) (x : prop_name (* input *)) (v : value (* input *)) (throw : bool (* input *)) (o : out),
        (* ========================================== *)
        (red_expr (S : state) (C : execution_ctx) ((spec_error_or_void (throw : bool) (native_error_type : native_error)) : ext_expr) (o : out)) ->
        (* ------------------------------------------ *)
        (red_expr (S0 : state) (C : execution_ctx) ((spec_object_put_2 (vthis : value) (l : object_loc) (x : prop_name) (v : value) (throw : bool) ((out_ter (S : state) (false : res)) : out)) : ext_expr) (o : out))

  | red_spec_object_put_2_true :
      forall (S0 : state (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (vthis : value (* input *)) (l : object_loc (* input *)) (x : prop_name (* input *)) (v : value (* input *)) (throw : bool (* input *)) (o : out) (y : (specret full_descriptor)),
        (* ========================================== *)
        (red_spec S C (spec_object_get_own_prop (l : object_loc) (x : prop_name)) y) ->
        (red_expr (S : state) (C : execution_ctx) ((spec_object_put_3 (vthis : value) (l : object_loc) (x : prop_name) (v : value) (throw : bool) (y : (specret full_descriptor))) : ext_expr) (o : out)) ->
        (* ------------------------------------------ *)
        (red_expr (S0 : state) (C : execution_ctx) ((spec_object_put_2 (vthis : value) (l : object_loc) (x : prop_name) (v : value) (throw : bool) ((out_ter (S : state) (true : res)) : out)) : ext_expr) (o : out))

  | red_spec_object_put_3_data_object :
      forall (S0 : state (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (lthis : object_loc (* input *)) (l : object_loc (* input *)) (x : prop_name (* input *)) (v : value (* input *)) (throw : bool (* input *)) (Ad : attributes_data (* input *)) (Desc : descriptor) (o1 : out) (o : out),
        (Desc = ((descriptor_intro ((Some v) : (option value)) (None : (option bool)) (None : (option value)) (None : (option value)) (None : (option bool)) (None : (option bool))) : descriptor)) ->
        (* ========================================== *)
        (red_expr (S : state) (C : execution_ctx) ((spec_object_define_own_prop (l : object_loc) (x : prop_name) (Desc : descriptor) (throw : bool)) : ext_expr) (o1 : out)) ->
        (red_expr (S : state) (C : execution_ctx) ((spec_object_put_5 (o1 : out)) : ext_expr) (o : out)) ->
        (* ------------------------------------------ *)
        (red_expr (S0 : state) (C : execution_ctx) ((spec_object_put_3 (lthis : value) (l : object_loc) (x : prop_name) (v : value) (throw : bool) ((specret_val (S : state) ((attributes_data_of (Ad : attributes_data)) : full_descriptor)) : (specret full_descriptor))) : ext_expr) (o : out))

  | red_spec_object_put_3_data_prim :
      forall (S0 : state (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (wthis : prim (* input *)) (l : object_loc (* input *)) (x : prop_name (* input *)) (v : value (* input *)) (throw : bool (* input *)) (Ad : attributes_data (* input *)) (o : out),
        (* ========================================== *)
        (red_expr (S : state) (C : execution_ctx) ((spec_error_or_void (throw : bool) (native_error_type : native_error)) : ext_expr) (o : out)) ->
        (* ------------------------------------------ *)
        (red_expr (S0 : state) (C : execution_ctx) ((spec_object_put_3 (wthis : value) (l : object_loc) (x : prop_name) (v : value) (throw : bool) ((specret_val (S : state) ((attributes_data_of (Ad : attributes_data)) : full_descriptor)) : (specret full_descriptor))) : ext_expr) (o : out))

  | red_spec_object_put_3_not_data :
      forall (S0 : state (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (vthis : value (* input *)) (l : object_loc (* input *)) (x : prop_name (* input *)) (v : value (* input *)) (throw : bool (* input *)) (Aa : attributes_accessor) (y1 : (specret full_descriptor)) (o : out) (D : full_descriptor (* input *)),
        (((D = full_descriptor_undef) : Prop) \/ ((D = (attributes_accessor_of Aa)) : Prop)) ->
        (* ========================================== *)
        (red_spec S C (spec_object_get_prop (l : object_loc) (x : prop_name)) y1) ->
        (red_expr (S : state) (C : execution_ctx) ((spec_object_put_4 (vthis : value) (l : object_loc) (x : prop_name) (v : value) (throw : bool) (y1 : (specret full_descriptor))) : ext_expr) (o : out)) ->
        (* ------------------------------------------ *)
        (red_expr (S0 : state) (C : execution_ctx) ((spec_object_put_3 (vthis : value) (l : object_loc) (x : prop_name) (v : value) (throw : bool) ((specret_val S D) : (specret full_descriptor))) : ext_expr) (o : out))

  | red_spec_object_put_4_accessor :
      forall (S0 : state (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (vsetter : value) (lfsetter : object_loc) (vthis : value (* input *)) (l : object_loc (* input *)) (x : prop_name (* input *)) (v : value (* input *)) (throw : bool (* input *)) (Aa : attributes_accessor (* input *)) (o1 : out) (o : out),
        ((vsetter : value) = (attributes_accessor_set (Aa : attributes_accessor))) ->
        ((vsetter : value) <> undef) ->
        ((vsetter : value) = (value_object (lfsetter : object_loc))) ->
        (* ========================================== *)
        (red_expr (S : state) (C : execution_ctx) ((spec_call (lfsetter : object_loc) (vthis : value) ((v :: (nil : (list value))) : (list value))) : ext_expr) (o1 : out)) ->
        (red_expr (S : state) (C : execution_ctx) ((spec_object_put_5 (o1 : out)) : ext_expr) (o : out)) ->
        (* ------------------------------------------ *)
        (red_expr (S0 : state) (C : execution_ctx) ((spec_object_put_4 (vthis : value) (l : object_loc) (x : prop_name) (v : value) (throw : bool) ((specret_val (S : state) ((attributes_accessor_of (Aa : attributes_accessor)) : full_descriptor)) : (specret full_descriptor))) : ext_expr) (o : out))

  | red_spec_object_put_4_not_accessor_object :
      forall (S0 : state (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (D : full_descriptor (* input *)) (lthis : object_loc (* input *)) (l : object_loc (* input *)) (x : prop_name (* input *)) (v : value (* input *)) (throw : bool (* input *)) (Ad : attributes_data) (Desc : descriptor) (o1 : out) (o : out),
        (((D = full_descriptor_undef) : Prop) \/ ((D = (attributes_data_of Ad)) : Prop)) ->
        (Desc = ((descriptor_intro_data v true true true) : descriptor)) ->
        (* ========================================== *)
        (red_expr (S : state) (C : execution_ctx) ((spec_object_define_own_prop (l : object_loc) (x : prop_name) (Desc : descriptor) (throw : bool)) : ext_expr) (o1 : out)) ->
        (red_expr (S : state) (C : execution_ctx) ((spec_object_put_5 (o1 : out)) : ext_expr) (o : out)) ->
        (* ------------------------------------------ *)
        (red_expr (S0 : state) (C : execution_ctx) ((spec_object_put_4 (lthis : value) (l : object_loc) (x : prop_name) (v : value) (throw : bool) ((specret_val (S : state) (D : full_descriptor)) : (specret full_descriptor))) : ext_expr) (o : out))

  | red_spec_object_put_4_not_accessor_prim :
      forall (S0 : state (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (wthis : prim (* input *)) (D : full_descriptor (* input *)) (l : object_loc (* input *)) (x : prop_name (* input *)) (v : value (* input *)) (throw : bool (* input *)) (Ad : attributes_data) (o : out),
        (((D = full_descriptor_undef) : Prop) \/ ((D = (attributes_data_of Ad)) : Prop)) ->
        (* ========================================== *)
        (red_expr (S : state) (C : execution_ctx) ((spec_error_or_void (throw : bool) (native_error_type : native_error)) : ext_expr) (o : out)) ->
        (* ------------------------------------------ *)
        (red_expr (S0 : state) (C : execution_ctx) ((spec_object_put_4 (wthis : value) (l : object_loc) (x : prop_name) (v : value) (throw : bool) ((specret_val (S : state) (D : full_descriptor)) : (specret full_descriptor))) : ext_expr) (o : out))

  | red_spec_object_put_5_return :
      forall (S0 : state (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (rv : resvalue (* input *)),
        (* ========================================== *)
        (* ------------------------------------------ *)
        (red_expr (S0 : state) (C : execution_ctx) ((spec_object_put_5 ((out_ter (S : state) (rv : res)) : out)) : ext_expr) ((out_void (S : state)) : out))

  | red_spec_object_has_prop_1_default :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (l : object_loc (* input *)) (x : prop_name (* input *)) (y1 : (specret full_descriptor)) (o : out),
        (* ========================================== *)
        (red_spec S C (spec_object_get_prop (l : object_loc) (x : prop_name)) y1) ->
        (red_expr (S : state) (C : execution_ctx) ((spec_object_has_prop_2 (y1 : (specret full_descriptor))) : ext_expr) (o : out)) ->
        (* ------------------------------------------ *)
        (red_expr (S : state) (C : execution_ctx) ((spec_object_has_prop_1 (builtin_has_prop_default : builtin_has_prop) (l : object_loc) (x : prop_name)) : ext_expr) (o : out))

  | red_spec_object_has_prop_2 :
      forall (S0 : state (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (D : full_descriptor (* input *)) (b : bool),
        (b = ((ifb (D = (full_descriptor_undef : full_descriptor)) then (false : bool) else true) : bool)) ->
        (* ========================================== *)
        (* ------------------------------------------ *)
        (red_expr (S0 : state) (C : execution_ctx) ((spec_object_has_prop_2 ((specret_val S D) : (specret full_descriptor))) : ext_expr) ((out_ter (S : state) (b : res)) : out))

  | red_spec_object_delete_1_default :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (l : object_loc (* input *)) (x : prop_name (* input *)) (throw : bool (* input *)) (o : out) (y : (specret full_descriptor)),
        (* ========================================== *)
        (red_spec S C (spec_object_get_own_prop (l : object_loc) (x : prop_name)) y) ->
        (red_expr (S : state) (C : execution_ctx) ((spec_object_delete_2 (l : object_loc) (x : prop_name) (throw : bool) (y : (specret full_descriptor))) : ext_expr) (o : out)) ->
        (* ------------------------------------------ *)
        (red_expr (S : state) (C : execution_ctx) ((spec_object_delete_1 (builtin_delete_default : builtin_delete) (l : object_loc) (x : prop_name) (throw : bool)) : ext_expr) (o : out))

  | red_spec_object_delete_2_undef :
      forall (S0 : state (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (l : object_loc (* input *)) (x : prop_name (* input *)) (throw : bool (* input *)),
        (* ========================================== *)
        (* ------------------------------------------ *)
        (red_expr (S0 : state) (C : execution_ctx) ((spec_object_delete_2 (l : object_loc) (x : prop_name) (throw : bool) ((specret_val S full_descriptor_undef) : (specret full_descriptor))) : ext_expr) ((out_ter (S : state) (true : res)) : out))

  | red_spec_object_delete_2_some_configurable :
      forall (S0 : state (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (l : object_loc (* input *)) (x : prop_name (* input *)) (throw : bool (* input *)) (A : attributes (* input *)) (S' : state),
        ((attributes_configurable (A : attributes)) = (true : bool)) ->
        (object_rem_property S l x S') ->
        (* ========================================== *)
        (* ------------------------------------------ *)
        (red_expr (S0 : state) (C : execution_ctx) ((spec_object_delete_2 (l : object_loc) (x : prop_name) (throw : bool) ((specret_val S (full_descriptor_some (A : attributes))) : (specret full_descriptor))) : ext_expr) ((out_ter (S' : state) (true : res)) : out))

  | red_spec_object_delete_3_some_non_configurable :
      forall (S0 : state (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (l : object_loc (* input *)) (x : prop_name (* input *)) (throw : bool (* input *)) (A : attributes (* input *)) (o : out),
        ((attributes_configurable (A : attributes)) = (false : bool)) ->
        (* ========================================== *)
        (red_expr (S : state) (C : execution_ctx) ((spec_error_or_cst (throw : bool) (native_error_type : native_error) (false : value)) : ext_expr) (o : out)) ->
        (* ------------------------------------------ *)
        (red_expr (S0 : state) (C : execution_ctx) ((spec_object_delete_2 (l : object_loc) (x : prop_name) (throw : bool) ((specret_val S (full_descriptor_some (A : attributes))) : (specret full_descriptor))) : ext_expr) (o : out))

  | red_spec_object_default_value_1_default :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (l : object_loc (* input *)) (prefo : (option preftype) (* input *)) (pref : preftype) (o : out),
        (pref = (unsome_default preftype_number prefo)) ->
        (* ========================================== *)
        (red_expr (S : state) (C : execution_ctx) ((spec_object_default_value_2 (l : object_loc) (pref : preftype) ((other_preftypes pref) : preftype)) : ext_expr) (o : out)) ->
        (* ------------------------------------------ *)
        (red_expr (S : state) (C : execution_ctx) ((spec_object_default_value_1 (builtin_default_value_default : builtin_default_value) (l : object_loc) (prefo : (option preftype))) : ext_expr) (o : out))

  | red_spec_object_default_value_2 :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (l : object_loc (* input *)) (pref1 : preftype (* input *)) (pref2 : preftype (* input *)) (o : out),
        (* ========================================== *)
        (red_expr (S : state) (C : execution_ctx) ((spec_object_default_value_sub_1 (l : object_loc) ((method_of_preftype (pref1 : preftype)) : string) ((spec_object_default_value_3 (l : object_loc) (pref2 : preftype)) : ext_expr)) : ext_expr) (o : out)) ->
        (* ------------------------------------------ *)
        (red_expr (S : state) (C : execution_ctx) ((spec_object_default_value_2 (l : object_loc) (pref1 : preftype) (pref2 : preftype)) : ext_expr) (o : out))

  | red_spec_object_default_value_3 :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (l : object_loc (* input *)) (pref2 : preftype (* input *)) (o : out),
        (* ========================================== *)
        (red_expr (S : state) (C : execution_ctx) ((spec_object_default_value_sub_1 (l : object_loc) ((method_of_preftype (pref2 : preftype)) : string) (spec_object_default_value_4 : ext_expr)) : ext_expr) (o : out)) ->
        (* ------------------------------------------ *)
        (red_expr (S : state) (C : execution_ctx) ((spec_object_default_value_3 (l : object_loc) (pref2 : preftype)) : ext_expr) (o : out))

  | red_spec_object_default_value_4 :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (o : out),
        (* ========================================== *)
        (red_expr (S : state) (C : execution_ctx) ((spec_error (native_error_type : native_error)) : ext_expr) (o : out)) ->
        (* ------------------------------------------ *)
        (red_expr (S : state) (C : execution_ctx) (spec_object_default_value_4 : ext_expr) (o : out))

  | red_spec_object_default_value_sub_1 :
      forall (o1 : out) (S : state (* input *)) (C : execution_ctx (* input *)) (l : object_loc (* input *)) (x : prop_name (* input *)) (K : ext_expr (* input *)) (o : out),
        (* ========================================== *)
        (red_expr (S : state) (C : execution_ctx) ((spec_object_get (l : value) (x : prop_name)) : ext_expr) (o1 : out)) ->
        (red_expr (S : state) (C : execution_ctx) ((spec_object_default_value_sub_2 (l : object_loc) (o1 : out) (K : ext_expr)) : ext_expr) (o : out)) ->
        (* ------------------------------------------ *)
        (red_expr (S : state) (C : execution_ctx) ((spec_object_default_value_sub_1 (l : object_loc) (x : string) (K : ext_expr)) : ext_expr) (o : out))

  | red_spec_object_default_value_sub_2_not_callable :
      forall (S0 : state (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (l : object_loc (* input *)) (v : value (* input *)) (K : ext_expr (* input *)) (o : out),
        (callable S v None) ->
        (* ========================================== *)
        (red_expr (S : state) (C : execution_ctx) (K : ext_expr) (o : out)) ->
        (* ------------------------------------------ *)
        (red_expr (S0 : state) (C : execution_ctx) ((spec_object_default_value_sub_2 (l : object_loc) ((out_ter (S : state) (v : res)) : out) (K : ext_expr)) : ext_expr) (o : out))

  | red_spec_object_default_value_sub_2_callable :
      forall (S0 : state (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (lfunc : object_loc) (l : object_loc (* input *)) (v : value (* input *)) (K : ext_expr (* input *)) (o : out) (B : _) (o1 : out),
        (callable S v (Some B)) ->
        (v = ((value_object (lfunc : object_loc)) : value)) ->
        (* ========================================== *)
        (red_expr (S : state) (C : execution_ctx) ((spec_call (lfunc : object_loc) (l : value) (nil : (list value))) : ext_expr) (o1 : out)) ->
        (red_expr (S : state) (C : execution_ctx) ((spec_object_default_value_sub_3 (o1 : out) (K : ext_expr)) : ext_expr) (o : out)) ->
        (* ------------------------------------------ *)
        (red_expr (S0 : state) (C : execution_ctx) ((spec_object_default_value_sub_2 (l : object_loc) ((out_ter (S : state) (v : res)) : out) (K : ext_expr)) : ext_expr) (o : out))

  | red_spec_object_default_value_sub_3_prim :
      forall (S0 : state (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (K : ext_expr (* input *)) (w : prim (* input *)),
        (* ========================================== *)
        (* ------------------------------------------ *)
        (red_expr (S0 : state) (C : execution_ctx) ((spec_object_default_value_sub_3 ((out_ter (S : state) (w : res)) : out) (K : ext_expr)) : ext_expr) ((out_ter (S : state) (w : res)) : out))

  | red_spec_object_default_value_sub_3_object :
      forall (S0 : state (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (l : object_loc (* input *)) (K : ext_expr (* input *)) (o : out),
        (* ========================================== *)
        (red_expr (S : state) (C : execution_ctx) (K : ext_expr) (o : out)) ->
        (* ------------------------------------------ *)
        (red_expr (S0 : state) (C : execution_ctx) ((spec_object_default_value_sub_3 ((out_ter (S : state) ((value_object (l : object_loc)) : res)) : out) (K : ext_expr)) : ext_expr) (o : out))

  | red_spec_object_define_own_prop_1_default :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (l : object_loc (* input *)) (x : prop_name (* input *)) (Desc : descriptor (* input *)) (throw : bool (* input *)) (o : out) (y : (specret full_descriptor)),
        (* ========================================== *)
        (red_spec S C (spec_object_get_own_prop (l : object_loc) (x : prop_name)) y) ->
        (red_expr (S : state) (C : execution_ctx) ((spec_object_define_own_prop_2 (l : object_loc) (x : prop_name) (Desc : descriptor) (throw : bool) (y : (specret full_descriptor))) : ext_expr) (o : out)) ->
        (* ------------------------------------------ *)
        (red_expr (S : state) (C : execution_ctx) ((spec_object_define_own_prop_1 (builtin_define_own_prop_default : builtin_define_own_prop) (l : object_loc) (x : prop_name) (Desc : descriptor) (throw : bool)) : ext_expr) (o : out))

  | red_spec_object_define_own_prop_2 :
      forall (S0 : state (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (l : object_loc (* input *)) (x : prop_name (* input *)) (Desc : descriptor (* input *)) (throw : bool (* input *)) (An : full_descriptor (* input *)) (bext : bool) (o : out),
        (object_extensible (S : state) (l : object_loc) (bext : bool)) ->
        (* ========================================== *)
        (red_expr (S : state) (C : execution_ctx) ((spec_object_define_own_prop_3 (l : object_loc) (x : prop_name) (Desc : descriptor) (throw : bool) (An : full_descriptor) (bext : bool)) : ext_expr) (o : out)) ->
        (* ------------------------------------------ *)
        (red_expr (S0 : state) (C : execution_ctx) ((spec_object_define_own_prop_2 (l : object_loc) (x : prop_name) (Desc : descriptor) (throw : bool) ((specret_val S An) : (specret full_descriptor))) : ext_expr) (o : out))

  | red_spec_object_define_own_prop_3_undef_false :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (l : object_loc (* input *)) (x : prop_name (* input *)) (Desc : descriptor (* input *)) (throw : bool (* input *)) (o : out),
        (* ========================================== *)
        (red_expr (S : state) (C : execution_ctx) ((spec_object_define_own_prop_reject (throw : bool)) : ext_expr) (o : out)) ->
        (* ------------------------------------------ *)
        (red_expr (S : state) (C : execution_ctx) ((spec_object_define_own_prop_3 (l : object_loc) (x : prop_name) (Desc : descriptor) (throw : bool) (full_descriptor_undef : full_descriptor) (false : bool)) : ext_expr) (o : out))

  | red_spec_object_define_own_prop_3_undef_true :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (l : object_loc (* input *)) (x : prop_name (* input *)) (Desc : descriptor (* input *)) (throw : bool (* input *)) (A : attributes) (S' : state),
        (A = ((ifb (((descriptor_is_generic Desc) : Prop) \/ ((descriptor_is_data Desc) : Prop)) then ((attributes_data_of_descriptor (Desc : descriptor)) : attributes) else ((attributes_accessor_of_descriptor (Desc : descriptor)) : attributes)) : attributes)) ->
        (object_set_property S l x A S') ->
        (* ========================================== *)
        (* ------------------------------------------ *)
        (red_expr (S : state) (C : execution_ctx) ((spec_object_define_own_prop_3 (l : object_loc) (x : prop_name) (Desc : descriptor) (throw : bool) (full_descriptor_undef : full_descriptor) (true : bool)) : ext_expr) ((out_ter (S' : state) (true : res)) : out))

  | red_spec_object_define_own_prop_3_includes :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (l : object_loc (* input *)) (x : prop_name (* input *)) (A : attributes (* input *)) (Desc : descriptor (* input *)) (throw : bool (* input *)) (bext : bool (* input *)),
        (descriptor_contains A Desc) ->
        (* ========================================== *)
        (* ------------------------------------------ *)
        (red_expr (S : state) (C : execution_ctx) ((spec_object_define_own_prop_3 (l : object_loc) (x : prop_name) (Desc : descriptor) (throw : bool) ((full_descriptor_some (A : attributes)) : full_descriptor) (bext : bool)) : ext_expr) ((out_ter (S : state) (true : res)) : out))

  | red_spec_object_define_own_prop_3_not_include :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (l : object_loc (* input *)) (x : prop_name (* input *)) (A : attributes (* input *)) (Desc : descriptor (* input *)) (throw : bool (* input *)) (o : out) (bext : bool (* input *)),
        (~ (descriptor_contains A Desc)) ->
        (* ========================================== *)
        (red_expr (S : state) (C : execution_ctx) ((spec_object_define_own_prop_4 (l : object_loc) (x : prop_name) (A : attributes) (Desc : descriptor) (throw : bool)) : ext_expr) (o : out)) ->
        (* ------------------------------------------ *)
        (red_expr (S : state) (C : execution_ctx) ((spec_object_define_own_prop_3 (l : object_loc) (x : prop_name) (Desc : descriptor) (throw : bool) ((full_descriptor_some (A : attributes)) : full_descriptor) (bext : bool)) : ext_expr) (o : out))

  | red_spec_object_define_own_prop_4_reject :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (l : object_loc (* input *)) (x : prop_name (* input *)) (A : attributes (* input *)) (Desc : descriptor (* input *)) (throw : bool (* input *)) (o : out),
        (attributes_change_enumerable_on_non_configurable (A : attributes) (Desc : descriptor)) ->
        (* ========================================== *)
        (red_expr (S : state) (C : execution_ctx) ((spec_object_define_own_prop_reject (throw : bool)) : ext_expr) (o : out)) ->
        (* ------------------------------------------ *)
        (red_expr (S : state) (C : execution_ctx) ((spec_object_define_own_prop_4 (l : object_loc) (x : prop_name) (A : attributes) (Desc : descriptor) (throw : bool)) : ext_expr) (o : out))

  | red_spec_object_define_own_prop_4_not_reject :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (l : object_loc (* input *)) (x : prop_name (* input *)) (A : attributes (* input *)) (Desc : descriptor (* input *)) (throw : bool (* input *)) (o : out),
        (~ (attributes_change_enumerable_on_non_configurable (A : attributes) (Desc : descriptor))) ->
        (* ========================================== *)
        (red_expr (S : state) (C : execution_ctx) ((spec_object_define_own_prop_5 (l : object_loc) (x : prop_name) (A : attributes) (Desc : descriptor) (throw : bool)) : ext_expr) (o : out)) ->
        (* ------------------------------------------ *)
        (red_expr (S : state) (C : execution_ctx) ((spec_object_define_own_prop_4 (l : object_loc) (x : prop_name) (A : attributes) (Desc : descriptor) (throw : bool)) : ext_expr) (o : out))

  | red_spec_object_define_own_prop_5_generic :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (l : object_loc (* input *)) (x : prop_name (* input *)) (A : attributes (* input *)) (Desc : descriptor (* input *)) (throw : bool (* input *)) (o : out),
        (descriptor_is_generic (Desc : descriptor)) ->
        (* ========================================== *)
        (red_expr (S : state) (C : execution_ctx) ((spec_object_define_own_prop_write (l : object_loc) (x : prop_name) (A : attributes) (Desc : descriptor) (throw : bool)) : ext_expr) (o : out)) ->
        (* ------------------------------------------ *)
        (red_expr (S : state) (C : execution_ctx) ((spec_object_define_own_prop_5 (l : object_loc) (x : prop_name) (A : attributes) (Desc : descriptor) (throw : bool)) : ext_expr) (o : out))

  | red_spec_object_define_own_prop_5_a :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (l : object_loc (* input *)) (x : prop_name (* input *)) (A : attributes (* input *)) (Desc : descriptor (* input *)) (throw : bool (* input *)) (o : out),
        ((attributes_is_data (A : attributes)) <> ((descriptor_is_data (Desc : descriptor)) : Prop)) ->
        (* ========================================== *)
        (red_expr (S : state) (C : execution_ctx) ((spec_object_define_own_prop_6a (l : object_loc) (x : prop_name) (A : attributes) (Desc : descriptor) (throw : bool)) : ext_expr) (o : out)) ->
        (* ------------------------------------------ *)
        (red_expr (S : state) (C : execution_ctx) ((spec_object_define_own_prop_5 (l : object_loc) (x : prop_name) (A : attributes) (Desc : descriptor) (throw : bool)) : ext_expr) (o : out))

  | red_spec_object_define_own_prop_6a_reject :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (l : object_loc (* input *)) (x : prop_name (* input *)) (A : attributes (* input *)) (Desc : descriptor (* input *)) (throw : bool (* input *)) (o : out),
        ((attributes_configurable (A : attributes)) = (false : bool)) ->
        (* ========================================== *)
        (red_expr (S : state) (C : execution_ctx) ((spec_object_define_own_prop_reject (throw : bool)) : ext_expr) (o : out)) ->
        (* ------------------------------------------ *)
        (red_expr (S : state) (C : execution_ctx) ((spec_object_define_own_prop_6a (l : object_loc) (x : prop_name) (A : attributes) (Desc : descriptor) (throw : bool)) : ext_expr) (o : out))

  | red_spec_object_define_own_prop_6a_accept :
      forall (S : state (* input *)) (S' : state) (C : execution_ctx (* input *)) (l : object_loc (* input *)) (x : prop_name (* input *)) (A : attributes (* input *)) (A' : attributes) (Desc : descriptor (* input *)) (throw : bool (* input *)) (o : out),
        ((attributes_configurable (A : attributes)) = (true : bool)) ->
        (A' = match A return attributes with (attributes_data_of Ad) => (attributes_accessor_of_attributes_data (Ad : attributes_data)) | (attributes_accessor_of Aa) => (attributes_data_of_attributes_accessor (Aa : attributes_accessor)) end) ->
        (object_set_property S l x A' S') ->
        (* ========================================== *)
        (red_expr (S' : state) (C : execution_ctx) ((spec_object_define_own_prop_write (l : object_loc) (x : prop_name) (A' : attributes) (Desc : descriptor) (throw : bool)) : ext_expr) (o : out)) ->
        (* ------------------------------------------ *)
        (red_expr (S : state) (C : execution_ctx) ((spec_object_define_own_prop_6a (l : object_loc) (x : prop_name) (A : attributes) (Desc : descriptor) (throw : bool)) : ext_expr) (o : out))

  | red_spec_object_define_own_prop_5_b :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (l : object_loc (* input *)) (x : prop_name (* input *)) (Ad : attributes_data (* input *)) (Desc : descriptor (* input *)) (throw : bool (* input *)) (o : out),
        (descriptor_is_data (Desc : descriptor)) ->
        (* ========================================== *)
        (red_expr (S : state) (C : execution_ctx) ((spec_object_define_own_prop_6b (l : object_loc) (x : prop_name) (Ad : attributes) (Desc : descriptor) (throw : bool)) : ext_expr) (o : out)) ->
        (* ------------------------------------------ *)
        (red_expr (S : state) (C : execution_ctx) ((spec_object_define_own_prop_5 (l : object_loc) (x : prop_name) ((attributes_data_of (Ad : attributes_data)) : attributes) (Desc : descriptor) (throw : bool)) : ext_expr) (o : out))

  | red_spec_object_define_own_prop_6b_false_reject :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (l : object_loc (* input *)) (x : prop_name (* input *)) (Ad : attributes_data (* input *)) (Desc : descriptor (* input *)) (throw : bool (* input *)) (o : out),
        (attributes_change_data_on_non_configurable (Ad : attributes_data) (Desc : descriptor)) ->
        (* ========================================== *)
        (red_expr (S : state) (C : execution_ctx) ((spec_object_define_own_prop_reject (throw : bool)) : ext_expr) (o : out)) ->
        (* ------------------------------------------ *)
        (red_expr (S : state) (C : execution_ctx) ((spec_object_define_own_prop_6b (l : object_loc) (x : prop_name) (Ad : attributes) (Desc : descriptor) (throw : bool)) : ext_expr) (o : out))

  | red_spec_object_define_own_prop_6b_false_accept :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (l : object_loc (* input *)) (x : prop_name (* input *)) (Ad : attributes_data (* input *)) (Desc : descriptor (* input *)) (throw : bool (* input *)) (o : out),
        (~ (attributes_change_data_on_non_configurable (Ad : attributes_data) (Desc : descriptor))) ->
        (* ========================================== *)
        (red_expr (S : state) (C : execution_ctx) ((spec_object_define_own_prop_write (l : object_loc) (x : prop_name) (Ad : attributes) (Desc : descriptor) (throw : bool)) : ext_expr) (o : out)) ->
        (* ------------------------------------------ *)
        (red_expr (S : state) (C : execution_ctx) ((spec_object_define_own_prop_6b (l : object_loc) (x : prop_name) (Ad : attributes) (Desc : descriptor) (throw : bool)) : ext_expr) (o : out))

  | red_spec_object_define_own_prop_5_c :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (l : object_loc (* input *)) (x : prop_name (* input *)) (Aa : attributes_accessor (* input *)) (Desc : descriptor (* input *)) (throw : bool (* input *)) (o : out),
        (descriptor_is_accessor (Desc : descriptor)) ->
        (* ========================================== *)
        (red_expr (S : state) (C : execution_ctx) ((spec_object_define_own_prop_6c (l : object_loc) (x : prop_name) (Aa : attributes) (Desc : descriptor) (throw : bool)) : ext_expr) (o : out)) ->
        (* ------------------------------------------ *)
        (red_expr (S : state) (C : execution_ctx) ((spec_object_define_own_prop_5 (l : object_loc) (x : prop_name) ((attributes_accessor_of (Aa : attributes_accessor)) : attributes) (Desc : descriptor) (throw : bool)) : ext_expr) (o : out))

  | red_spec_object_define_own_prop_6c_1 :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (l : object_loc (* input *)) (x : prop_name (* input *)) (Aa : attributes_accessor (* input *)) (Desc : descriptor (* input *)) (throw : bool (* input *)) (o : out),
        (attributes_change_accessor_on_non_configurable (Aa : attributes_accessor) (Desc : descriptor)) ->
        (* ========================================== *)
        (red_expr (S : state) (C : execution_ctx) ((spec_object_define_own_prop_reject (throw : bool)) : ext_expr) (o : out)) ->
        (* ------------------------------------------ *)
        (red_expr (S : state) (C : execution_ctx) ((spec_object_define_own_prop_6c (l : object_loc) (x : prop_name) (Aa : attributes) (Desc : descriptor) (throw : bool)) : ext_expr) (o : out))

  | red_spec_object_define_own_prop_6c_2 :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (l : object_loc (* input *)) (x : prop_name (* input *)) (Aa : attributes_accessor (* input *)) (Desc : descriptor (* input *)) (throw : bool (* input *)) (o : out),
        (~ (attributes_change_accessor_on_non_configurable (Aa : attributes_accessor) (Desc : descriptor))) ->
        (* ========================================== *)
        (red_expr (S : state) (C : execution_ctx) ((spec_object_define_own_prop_write (l : object_loc) (x : prop_name) (Aa : attributes) (Desc : descriptor) (throw : bool)) : ext_expr) (o : out)) ->
        (* ------------------------------------------ *)
        (red_expr (S : state) (C : execution_ctx) ((spec_object_define_own_prop_6c (l : object_loc) (x : prop_name) (Aa : attributes) (Desc : descriptor) (throw : bool)) : ext_expr) (o : out))

  | red_spec_object_define_own_prop_write :
      forall (S : state (* input *)) (S' : state) (C : execution_ctx (* input *)) (l : object_loc (* input *)) (x : prop_name (* input *)) (A : attributes (* input *)) (Desc : descriptor (* input *)) (throw : bool (* input *)) (A' : attributes),
        (A' = ((attributes_update (A : attributes) (Desc : descriptor)) : attributes)) ->
        (object_set_property S l x A' S') ->
        (* ========================================== *)
        (* ------------------------------------------ *)
        (red_expr (S : state) (C : execution_ctx) ((spec_object_define_own_prop_write (l : object_loc) (x : prop_name) (A : attributes) (Desc : descriptor) (throw : bool)) : ext_expr) ((out_ter (S' : state) (true : res)) : out))

  | red_spec_object_define_own_prop_reject :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (throw : bool (* input *)) (o : out),
        (* ========================================== *)
        (red_expr (S : state) (C : execution_ctx) ((spec_error_or_cst (throw : bool) (native_error_type : native_error) (false : value)) : ext_expr) (o : out)) ->
        (* ------------------------------------------ *)
        (red_expr (S : state) (C : execution_ctx) ((spec_object_define_own_prop_reject (throw : bool)) : ext_expr) (o : out))

  | red_spec_prim_value_get :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (v : value (* input *)) (x : prop_name (* input *)) (o1 : out) (o : out),
        (* ========================================== *)
        (red_expr (S : state) (C : execution_ctx) ((spec_to_object (v : value)) : ext_expr) (o1 : out)) ->
        (red_expr (S : state) (C : execution_ctx) ((spec_prim_value_get_1 (v : value) (x : prop_name) (o1 : out)) : ext_expr) (o : out)) ->
        (* ------------------------------------------ *)
        (red_expr (S : state) (C : execution_ctx) ((spec_prim_value_get (v : value) (x : prop_name)) : ext_expr) (o : out))

  | red_spec_prim_value_get_1 :
      forall (S0 : state (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (v : value (* input *)) (x : prop_name (* input *)) (l : object_loc (* input *)) (o : out),
        (* ========================================== *)
        (red_expr (S : state) (C : execution_ctx) ((spec_object_get_1 (builtin_get_default : builtin_get) (v : value) (l : object_loc) (x : prop_name)) : ext_expr) (o : out)) ->
        (* ------------------------------------------ *)
        (red_expr (S0 : state) (C : execution_ctx) ((spec_prim_value_get_1 (v : value) (x : prop_name) ((out_ter (S : state) (l : res)) : out)) : ext_expr) (o : out))

  | red_spec_ref_put_value_value :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (v : value (* input *)) (vnew : value (* input *)) (o : out),
        (* ========================================== *)
        (red_expr (S : state) (C : execution_ctx) ((spec_error (native_error_ref : native_error)) : ext_expr) (o : out)) ->
        (* ------------------------------------------ *)
        (red_expr (S : state) (C : execution_ctx) ((spec_put_value (v : resvalue) (vnew : value)) : ext_expr) (o : out))

  | red_spec_ref_put_value_ref_a_1 :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (r : ref (* input *)) (vnew : value (* input *)) (o : out),
        (ref_is_unresolvable (r : ref)) ->
        ((ref_strict (r : ref)) = (true : bool)) ->
        (* ========================================== *)
        (red_expr (S : state) (C : execution_ctx) ((spec_error (native_error_ref : native_error)) : ext_expr) (o : out)) ->
        (* ------------------------------------------ *)
        (red_expr (S : state) (C : execution_ctx) ((spec_put_value (r : resvalue) (vnew : value)) : ext_expr) (o : out))

  | red_spec_ref_put_value_ref_a_2 :
      forall (o : out) (S : state (* input *)) (C : execution_ctx (* input *)) (r : ref (* input *)) (vnew : value (* input *)),
        (ref_is_unresolvable (r : ref)) ->
        ((ref_strict (r : ref)) = (false : bool)) ->
        (* ========================================== *)
        (red_expr (S : state) (C : execution_ctx) ((spec_object_put (prealloc_global : value) ((ref_name (r : ref)) : prop_name) (vnew : value) (throw_false : bool)) : ext_expr) (o : out)) ->
        (* ------------------------------------------ *)
        (red_expr (S : state) (C : execution_ctx) ((spec_put_value (r : resvalue) (vnew : value)) : ext_expr) (o : out))

  | red_spec_ref_put_value_ref_b :
      forall (v : value) (ext_put : (value -> (prop_name -> (value -> (bool -> ext_expr))))) (S : state (* input *)) (C : execution_ctx (* input *)) (r : ref (* input *)) (vnew : value (* input *)) (o : out),
        (ref_is_property (r : ref)) ->
        ((ref_base (r : ref)) = ((ref_base_type_value (v : value)) : ref_base_type)) ->
        ((ext_put : (value -> (prop_name -> (value -> (bool -> ext_expr))))) = (ifb (ref_has_primitive_base (r : ref)) then (spec_prim_value_put : (value -> (prop_name -> (value -> (bool -> ext_expr))))) else spec_object_put)) ->
        (* ========================================== *)
        (red_expr (S : state) (C : execution_ctx) ((ext_put v (ref_name (r : ref)) vnew (ref_strict (r : ref))) : ext_expr) (o : out)) ->
        (* ------------------------------------------ *)
        (red_expr (S : state) (C : execution_ctx) ((spec_put_value ((resvalue_ref (r : ref)) : resvalue) (vnew : value)) : ext_expr) (o : out))

  | red_spec_ref_put_value_ref_c :
      forall (L : env_loc) (S : state (* input *)) (C : execution_ctx (* input *)) (r : ref (* input *)) (vnew : value (* input *)) (o : out),
        ((ref_base (r : ref)) = ((ref_base_type_env_loc (L : env_loc)) : ref_base_type)) ->
        (* ========================================== *)
        (red_expr (S : state) (C : execution_ctx) ((spec_env_record_set_mutable_binding (L : env_loc) ((ref_name (r : ref)) : prop_name) (vnew : value) ((ref_strict (r : ref)) : bool)) : ext_expr) (o : out)) ->
        (* ------------------------------------------ *)
        (red_expr (S : state) (C : execution_ctx) ((spec_put_value ((resvalue_ref (r : ref)) : resvalue) (vnew : value)) : ext_expr) (o : out))

  | red_spec_prim_value_put :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (w : prim (* input *)) (x : prop_name (* input *)) (v : value (* input *)) (throw : bool (* input *)) (o1 : out) (o : out),
        (* ========================================== *)
        (red_expr (S : state) (C : execution_ctx) ((spec_to_object (w : value)) : ext_expr) (o1 : out)) ->
        (red_expr (S : state) (C : execution_ctx) ((spec_prim_value_put_1 (w : prim) (x : prop_name) (v : value) (throw : bool) (o1 : out)) : ext_expr) (o : out)) ->
        (* ------------------------------------------ *)
        (red_expr (S : state) (C : execution_ctx) ((spec_prim_value_put (w : value) (x : prop_name) (v : value) (throw : bool)) : ext_expr) (o : out))

  | red_spec_prim_value_put_1 :
      forall (S0 : state (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (w : prim (* input *)) (x : prop_name (* input *)) (v : value (* input *)) (throw : bool (* input *)) (l : object_loc (* input *)) (o : out),
        (* ========================================== *)
        (red_expr (S : state) (C : execution_ctx) ((spec_object_put_1 (builtin_put_default : builtin_put) (w : value) (l : object_loc) (x : prop_name) (v : value) (throw : bool)) : ext_expr) (o : out)) ->
        (* ------------------------------------------ *)
        (red_expr (S0 : state) (C : execution_ctx) ((spec_prim_value_put_1 (w : prim) (x : prop_name) (v : value) (throw : bool) ((out_ter (S : state) (l : res)) : out)) : ext_expr) (o : out))

  | red_spec_env_record_has_binding :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (L : env_loc (* input *)) (x : prop_name (* input *)) (o : out) (E : env_record),
        (env_record_binds (S : state) (L : env_loc) (E : env_record)) ->
        (* ========================================== *)
        (red_expr (S : state) (C : execution_ctx) ((spec_env_record_has_binding_1 (L : env_loc) (x : prop_name) (E : env_record)) : ext_expr) (o : out)) ->
        (* ------------------------------------------ *)
        (red_expr (S : state) (C : execution_ctx) ((spec_env_record_has_binding (L : env_loc) (x : prop_name)) : ext_expr) (o : out))

  | red_spec_env_record_has_binding_1_decl :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (L : env_loc (* input *)) (x : prop_name (* input *)) (Ed : decl_env_record (* input *)) (b : bool),
        (b = ((ifb (decl_env_record_indom (Ed : decl_env_record) (x : string)) then (true : bool) else false) : bool)) ->
        (* ========================================== *)
        (* ------------------------------------------ *)
        (red_expr (S : state) (C : execution_ctx) ((spec_env_record_has_binding_1 (L : env_loc) (x : prop_name) ((env_record_decl (Ed : decl_env_record)) : env_record)) : ext_expr) ((out_ter (S : state) (b : res)) : out))

  | red_spec_env_record_has_binding_1_object :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (L : env_loc (* input *)) (x : prop_name (* input *)) (l : object_loc (* input *)) (pt : provide_this_flag (* input *)) (o : out),
        (* ========================================== *)
        (red_expr (S : state) (C : execution_ctx) ((spec_object_has_prop (l : object_loc) (x : prop_name)) : ext_expr) (o : out)) ->
        (* ------------------------------------------ *)
        (red_expr (S : state) (C : execution_ctx) ((spec_env_record_has_binding_1 (L : env_loc) (x : prop_name) ((env_record_object (l : object_loc) (pt : provide_this_flag)) : env_record)) : ext_expr) (o : out))

  | red_spec_env_record_create_mutable_binding :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (L : env_loc (* input *)) (x : prop_name (* input *)) (deletable_opt : (option bool) (* input *)) (deletable : bool) (o : out) (E : env_record),
        (deletable = (unsome_default false deletable_opt)) ->
        (env_record_binds (S : state) (L : env_loc) (E : env_record)) ->
        (* ========================================== *)
        (red_expr (S : state) (C : execution_ctx) ((spec_env_record_create_mutable_binding_1 (L : env_loc) (x : prop_name) (deletable : bool) (E : env_record)) : ext_expr) (o : out)) ->
        (* ------------------------------------------ *)
        (red_expr (S : state) (C : execution_ctx) ((spec_env_record_create_mutable_binding (L : env_loc) (x : prop_name) (deletable_opt : (option bool))) : ext_expr) (o : out))

  | red_spec_env_record_create_mutable_binding_1_decl_indom :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (L : env_loc (* input *)) (x : prop_name (* input *)) (deletable : bool (* input *)) (Ed : decl_env_record (* input *)) (S' : state),
        (~ (decl_env_record_indom (Ed : decl_env_record) (x : string))) ->
        (S' = ((env_record_write_decl_env S L x (mutability_of_bool (deletable : bool)) undef) : state)) ->
        (* ========================================== *)
        (* ------------------------------------------ *)
        (red_expr (S : state) (C : execution_ctx) ((spec_env_record_create_mutable_binding_1 (L : env_loc) (x : prop_name) (deletable : bool) ((env_record_decl (Ed : decl_env_record)) : env_record)) : ext_expr) ((out_void (S' : state)) : out))

  | red_spec_env_record_create_mutable_binding_1_object :
      forall (o1 : out) (S : state (* input *)) (C : execution_ctx (* input *)) (L : env_loc (* input *)) (x : prop_name (* input *)) (deletable : bool (* input *)) (l : object_loc (* input *)) (pt : provide_this_flag (* input *)) (o : out),
        (* ========================================== *)
        (red_expr (S : state) (C : execution_ctx) ((spec_object_has_prop (l : object_loc) (x : prop_name)) : ext_expr) (o1 : out)) ->
        (red_expr (S : state) (C : execution_ctx) ((spec_env_record_create_mutable_binding_2 (L : env_loc) (x : prop_name) (deletable : bool) (l : object_loc) (o1 : out)) : ext_expr) (o : out)) ->
        (* ------------------------------------------ *)
        (red_expr (S : state) (C : execution_ctx) ((spec_env_record_create_mutable_binding_1 (L : env_loc) (x : prop_name) (deletable : bool) ((env_record_object (l : object_loc) (pt : provide_this_flag)) : env_record)) : ext_expr) (o : out))

  | red_spec_env_record_create_mutable_binding_obj_2 :
      forall (A : attributes) (S0 : state (* input *)) (C : execution_ctx (* input *)) (L : env_loc (* input *)) (x : prop_name (* input *)) (deletable : bool (* input *)) (l : object_loc (* input *)) (S : state (* input *)) (o1 : out) (o : out),
        (A = ((attributes_data_intro (undef : value) (true : bool) (true : bool) (deletable : bool)) : attributes)) ->
        (* ========================================== *)
        (red_expr (S : state) (C : execution_ctx) ((spec_object_define_own_prop (l : object_loc) (x : prop_name) (A : descriptor) (throw_true : bool)) : ext_expr) (o1 : out)) ->
        (red_expr (S : state) (C : execution_ctx) ((spec_env_record_create_mutable_binding_3 (o1 : out)) : ext_expr) (o : out)) ->
        (* ------------------------------------------ *)
        (red_expr (S0 : state) (C : execution_ctx) ((spec_env_record_create_mutable_binding_2 (L : env_loc) (x : prop_name) (deletable : bool) (l : object_loc) ((out_ter (S : state) (false : res)) : out)) : ext_expr) (o : out))

  | red_spec_env_record_create_mutable_binding_obj_3 :
      forall (S0 : state (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (rv : resvalue (* input *)),
        (* ========================================== *)
        (* ------------------------------------------ *)
        (red_expr (S0 : state) (C : execution_ctx) ((spec_env_record_create_mutable_binding_3 ((out_ter (S : state) (rv : res)) : out)) : ext_expr) ((out_void (S : state)) : out))

  | red_spec_env_record_set_mutable_binding :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (L : env_loc (* input *)) (x : prop_name (* input *)) (v : value (* input *)) (str : strictness_flag (* input *)) (o : out) (E : env_record),
        (env_record_binds (S : state) (L : env_loc) (E : env_record)) ->
        (* ========================================== *)
        (red_expr (S : state) (C : execution_ctx) ((spec_env_record_set_mutable_binding_1 (L : env_loc) (x : prop_name) (v : value) (str : bool) (E : env_record)) : ext_expr) (o : out)) ->
        (* ------------------------------------------ *)
        (red_expr (S : state) (C : execution_ctx) ((spec_env_record_set_mutable_binding (L : env_loc) (x : prop_name) (v : value) (str : bool)) : ext_expr) (o : out))

  | red_spec_env_record_set_mutable_binding_1_decl_mutable :
      forall (v_old : value) (mu : mutability) (S : state (* input *)) (C : execution_ctx (* input *)) (L : env_loc (* input *)) (x : prop_name (* input *)) (v : value (* input *)) (str : strictness_flag (* input *)) (Ed : decl_env_record (* input *)) (o : out),
        (decl_env_record_binds (Ed : decl_env_record) (x : string) (mu : mutability) (v_old : value)) ->
        (mutability_is_mutable (mu : mutability)) ->
        (* ========================================== *)
        (red_expr (S : state) (C : execution_ctx) ((spec_returns ((out_void ((env_record_write_decl_env S L x mu v) : state)) : out)) : ext_expr) (o : out)) ->
        (* ------------------------------------------ *)
        (red_expr (S : state) (C : execution_ctx) ((spec_env_record_set_mutable_binding_1 (L : env_loc) (x : prop_name) (v : value) (str : bool) ((env_record_decl (Ed : decl_env_record)) : env_record)) : ext_expr) (o : out))

  | red_spec_env_record_set_mutable_binding_1_decl_non_mutable :
      forall (v_old : value) (mu : mutability) (S : state (* input *)) (C : execution_ctx (* input *)) (L : env_loc (* input *)) (x : prop_name (* input *)) (v : value (* input *)) (str : strictness_flag (* input *)) (Ed : decl_env_record (* input *)) (o : out),
        (decl_env_record_binds (Ed : decl_env_record) (x : string) (mu : mutability) (v_old : value)) ->
        (~ (mutability_is_mutable (mu : mutability))) ->
        (* ========================================== *)
        (red_expr (S : state) (C : execution_ctx) ((spec_error_or_void (str : bool) (native_error_type : native_error)) : ext_expr) (o : out)) ->
        (* ------------------------------------------ *)
        (red_expr (S : state) (C : execution_ctx) ((spec_env_record_set_mutable_binding_1 (L : env_loc) (x : prop_name) (v : value) (str : bool) ((env_record_decl (Ed : decl_env_record)) : env_record)) : ext_expr) (o : out))

  | red_spec_env_record_set_mutable_binding_1_object :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (L : env_loc (* input *)) (x : prop_name (* input *)) (v : value (* input *)) (str : strictness_flag (* input *)) (l : object_loc (* input *)) (pt : provide_this_flag (* input *)) (o : out),
        (* ========================================== *)
        (red_expr (S : state) (C : execution_ctx) ((spec_object_put (l : value) (x : prop_name) (v : value) (str : bool)) : ext_expr) (o : out)) ->
        (* ------------------------------------------ *)
        (red_expr (S : state) (C : execution_ctx) ((spec_env_record_set_mutable_binding_1 (L : env_loc) (x : prop_name) (v : value) (str : bool) ((env_record_object (l : object_loc) (pt : provide_this_flag)) : env_record)) : ext_expr) (o : out))

  | red_spec_env_record_get_binding_value :
      forall (E : env_record) (S : state (* input *)) (C : execution_ctx (* input *)) (L : env_loc (* input *)) (x : prop_name (* input *)) (str : strictness_flag (* input *)) (o : out),
        (env_record_binds (S : state) (L : env_loc) (E : env_record)) ->
        (* ========================================== *)
        (red_expr (S : state) (C : execution_ctx) ((spec_env_record_get_binding_value_1 (L : env_loc) (x : prop_name) (str : bool) (E : env_record)) : ext_expr) (o : out)) ->
        (* ------------------------------------------ *)
        (red_expr (S : state) (C : execution_ctx) ((spec_env_record_get_binding_value (L : env_loc) (x : prop_name) (str : bool)) : ext_expr) (o : out))

  | red_spec_env_record_get_binding_value_1_decl_uninitialized :
      forall (mu : mutability) (v : value) (S : state (* input *)) (C : execution_ctx (* input *)) (L : env_loc (* input *)) (x : prop_name (* input *)) (str : strictness_flag (* input *)) (Ed : decl_env_record (* input *)) (o : out),
        (decl_env_record_binds (Ed : decl_env_record) (x : string) (mu : mutability) (v : value)) ->
        ((mu : mutability) = mutability_uninitialized_immutable) ->
        (* ========================================== *)
        (red_expr (S : state) (C : execution_ctx) ((spec_error_or_cst (str : bool) (native_error_ref : native_error) (undef : value)) : ext_expr) (o : out)) ->
        (* ------------------------------------------ *)
        (red_expr (S : state) (C : execution_ctx) ((spec_env_record_get_binding_value_1 (L : env_loc) (x : prop_name) (str : bool) ((env_record_decl (Ed : decl_env_record)) : env_record)) : ext_expr) (o : out))

  | red_spec_env_record_get_binding_value_1_decl_initialized :
      forall (mu : mutability) (v : value) (S : state (* input *)) (C : execution_ctx (* input *)) (L : env_loc (* input *)) (x : prop_name (* input *)) (str : strictness_flag (* input *)) (Ed : decl_env_record (* input *)) (o : out),
        (decl_env_record_binds (Ed : decl_env_record) (x : string) (mu : mutability) (v : value)) ->
        ((mu : mutability) <> mutability_uninitialized_immutable) ->
        (* ========================================== *)
        (red_expr (S : state) (C : execution_ctx) ((spec_returns ((out_ter (S : state) (v : res)) : out)) : ext_expr) (o : out)) ->
        (* ------------------------------------------ *)
        (red_expr (S : state) (C : execution_ctx) ((spec_env_record_get_binding_value_1 (L : env_loc) (x : prop_name) (str : bool) ((env_record_decl (Ed : decl_env_record)) : env_record)) : ext_expr) (o : out))

  | red_spec_env_record_get_binding_value_1_object :
      forall (o1 : out) (S : state (* input *)) (C : execution_ctx (* input *)) (L : env_loc (* input *)) (x : prop_name (* input *)) (str : strictness_flag (* input *)) (l : object_loc (* input *)) (pt : provide_this_flag (* input *)) (o : out),
        (* ========================================== *)
        (red_expr (S : state) (C : execution_ctx) ((spec_object_has_prop (l : object_loc) (x : prop_name)) : ext_expr) (o1 : out)) ->
        (red_expr (S : state) (C : execution_ctx) ((spec_env_record_get_binding_value_2 (x : prop_name) (str : bool) (l : object_loc) (o1 : out)) : ext_expr) (o : out)) ->
        (* ------------------------------------------ *)
        (red_expr (S : state) (C : execution_ctx) ((spec_env_record_get_binding_value_1 (L : env_loc) (x : prop_name) (str : bool) ((env_record_object (l : object_loc) (pt : provide_this_flag)) : env_record)) : ext_expr) (o : out))

  | red_spec_env_record_get_binding_value_obj_2_false :
      forall (S0 : state (* input *)) (C : execution_ctx (* input *)) (x : prop_name (* input *)) (str : strictness_flag (* input *)) (l : object_loc (* input *)) (S : state (* input *)) (o : out),
        (* ========================================== *)
        (red_expr (S : state) (C : execution_ctx) ((spec_error_or_cst (str : bool) (native_error_ref : native_error) (undef : value)) : ext_expr) (o : out)) ->
        (* ------------------------------------------ *)
        (red_expr (S0 : state) (C : execution_ctx) ((spec_env_record_get_binding_value_2 (x : prop_name) (str : bool) (l : object_loc) ((out_ter (S : state) (false : res)) : out)) : ext_expr) (o : out))

  | red_spec_env_record_get_binding_value_obj_2_true :
      forall (S0 : state (* input *)) (C : execution_ctx (* input *)) (x : prop_name (* input *)) (str : strictness_flag (* input *)) (l : object_loc (* input *)) (S : state (* input *)) (o : out),
        (* ========================================== *)
        (red_expr (S : state) (C : execution_ctx) ((spec_object_get (l : value) (x : prop_name)) : ext_expr) (o : out)) ->
        (* ------------------------------------------ *)
        (red_expr (S0 : state) (C : execution_ctx) ((spec_env_record_get_binding_value_2 (x : prop_name) (str : bool) (l : object_loc) ((out_ter (S : state) (true : res)) : out)) : ext_expr) (o : out))

  | red_spec_env_record_delete_binding :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (L : env_loc (* input *)) (x : prop_name (* input *)) (o : out) (E : env_record),
        (env_record_binds (S : state) (L : env_loc) (E : env_record)) ->
        (* ========================================== *)
        (red_expr (S : state) (C : execution_ctx) ((spec_env_record_delete_binding_1 (L : env_loc) (x : prop_name) (E : env_record)) : ext_expr) (o : out)) ->
        (* ------------------------------------------ *)
        (red_expr (S : state) (C : execution_ctx) ((spec_env_record_delete_binding (L : env_loc) (x : prop_name)) : ext_expr) (o : out))

  | red_spec_env_record_delete_binding_1_decl_indom :
      forall (mu : mutability) (v : value) (S : state (* input *)) (C : execution_ctx (* input *)) (L : env_loc (* input *)) (x : prop_name (* input *)) (Ed : decl_env_record (* input *)) (S' : state) (b : bool),
        (decl_env_record_binds (Ed : decl_env_record) (x : string) (mu : mutability) (v : value)) ->
        (ifb ((mu : mutability) = mutability_deletable) then ((((S' = (env_record_write S L (decl_env_record_rem Ed x))) : Prop) /\ ((b = true) : Prop)) : Prop) else (((S' = S) : Prop) /\ ((b = false) : Prop))) ->
        (* ========================================== *)
        (* ------------------------------------------ *)
        (red_expr (S : state) (C : execution_ctx) ((spec_env_record_delete_binding_1 (L : env_loc) (x : prop_name) ((env_record_decl (Ed : decl_env_record)) : env_record)) : ext_expr) ((out_ter (S' : state) (b : res)) : out))

  | red_spec_env_record_delete_binding_1_decl_not_indom :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (L : env_loc (* input *)) (x : prop_name (* input *)) (Ed : decl_env_record (* input *)),
        (~ (decl_env_record_indom (Ed : decl_env_record) (x : string))) ->
        (* ========================================== *)
        (* ------------------------------------------ *)
        (red_expr (S : state) (C : execution_ctx) ((spec_env_record_delete_binding_1 (L : env_loc) (x : prop_name) ((env_record_decl (Ed : decl_env_record)) : env_record)) : ext_expr) ((out_ter (S : state) (true : res)) : out))

  | red_spec_env_record_delete_binding_1_object :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (L : env_loc (* input *)) (x : prop_name (* input *)) (l : object_loc (* input *)) (pt : provide_this_flag (* input *)) (o : out),
        (* ========================================== *)
        (red_expr (S : state) (C : execution_ctx) ((spec_object_delete (l : object_loc) (x : prop_name) (throw_false : bool)) : ext_expr) (o : out)) ->
        (* ------------------------------------------ *)
        (red_expr (S : state) (C : execution_ctx) ((spec_env_record_delete_binding_1 (L : env_loc) (x : prop_name) ((env_record_object (l : object_loc) (pt : provide_this_flag)) : env_record)) : ext_expr) (o : out))

  | red_spec_env_record_implicit_this_value :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (L : env_loc (* input *)) (o : out) (E : env_record),
        (env_record_binds (S : state) (L : env_loc) (E : env_record)) ->
        (* ========================================== *)
        (red_expr (S : state) (C : execution_ctx) ((spec_env_record_implicit_this_value_1 (L : env_loc) (E : env_record)) : ext_expr) (o : out)) ->
        (* ------------------------------------------ *)
        (red_expr (S : state) (C : execution_ctx) ((spec_env_record_implicit_this_value (L : env_loc)) : ext_expr) (o : out))

  | red_spec_env_record_implicit_this_value_1_decl :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (L : env_loc (* input *)) (Ed : decl_env_record (* input *)),
        (* ========================================== *)
        (* ------------------------------------------ *)
        (red_expr (S : state) (C : execution_ctx) ((spec_env_record_implicit_this_value_1 (L : env_loc) ((env_record_decl (Ed : decl_env_record)) : env_record)) : ext_expr) ((out_ter (S : state) (undef : res)) : out))

  | red_spec_env_record_implicit_this_value_1_object :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (L : env_loc (* input *)) (l : object_loc (* input *)) (pt : bool (* input *)) (v : value),
        (v = ((ifb pt then (l : value) else undef) : value)) ->
        (* ========================================== *)
        (* ------------------------------------------ *)
        (red_expr (S : state) (C : execution_ctx) ((spec_env_record_implicit_this_value_1 (L : env_loc) ((env_record_object (l : object_loc) (pt : provide_this_flag)) : env_record)) : ext_expr) ((out_ter (S : state) (v : res)) : out))

  | red_spec_env_record_create_immutable_binding :
      forall (Ed : decl_env_record) (S : state (* input *)) (C : execution_ctx (* input *)) (L : env_loc (* input *)) (x : prop_name (* input *)) (S' : state),
        (env_record_binds (S : state) (L : env_loc) ((env_record_decl (Ed : decl_env_record)) : env_record)) ->
        (~ (decl_env_record_indom (Ed : decl_env_record) (x : string))) ->
        (S' = ((env_record_write_decl_env S L x mutability_uninitialized_immutable undef) : state)) ->
        (* ========================================== *)
        (* ------------------------------------------ *)
        (red_expr (S : state) (C : execution_ctx) ((spec_env_record_create_immutable_binding (L : env_loc) (x : prop_name)) : ext_expr) ((out_void (S' : state)) : out))

  | red_spec_env_record_initialize_immutable_binding :
      forall (Ed : decl_env_record) (v_old : value) (S : state (* input *)) (C : execution_ctx (* input *)) (L : env_loc (* input *)) (x : prop_name (* input *)) (v : value (* input *)) (S' : state),
        (env_record_binds (S : state) (L : env_loc) ((env_record_decl (Ed : decl_env_record)) : env_record)) ->
        (decl_env_record_binds (Ed : decl_env_record) (x : string) (mutability_uninitialized_immutable : mutability) (v_old : value)) ->
        (S' = ((env_record_write_decl_env S L x mutability_immutable v) : state)) ->
        (* ========================================== *)
        (* ------------------------------------------ *)
        (red_expr (S : state) (C : execution_ctx) ((spec_env_record_initialize_immutable_binding (L : env_loc) (x : prop_name) (v : value)) : ext_expr) ((out_void (S' : state)) : out))

  | red_spec_env_record_create_set_mutable_binding :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (L : env_loc (* input *)) (x : prop_name (* input *)) (deletable_opt : (option bool) (* input *)) (v : value (* input *)) (str : strictness_flag (* input *)) (o : out) (o1 : out),
        (* ========================================== *)
        (red_expr (S : state) (C : execution_ctx) ((spec_env_record_create_mutable_binding (L : env_loc) (x : prop_name) (deletable_opt : (option bool))) : ext_expr) (o1 : out)) ->
        (red_expr (S : state) (C : execution_ctx) ((spec_env_record_create_set_mutable_binding_1 (o1 : out) (L : env_loc) (x : prop_name) (v : value) (str : bool)) : ext_expr) (o : out)) ->
        (* ------------------------------------------ *)
        (red_expr (S : state) (C : execution_ctx) ((spec_env_record_create_set_mutable_binding (L : env_loc) (x : prop_name) (deletable_opt : (option bool)) (v : value) (str : bool)) : ext_expr) (o : out))

  | red_spec_env_record_create_set_mutable_binding_1 :
      forall (S : state (* input *)) (S0 : state (* input *)) (C : execution_ctx (* input *)) (L : env_loc (* input *)) (x : prop_name (* input *)) (v : value (* input *)) (str : strictness_flag (* input *)) (o : out),
        (* ========================================== *)
        (red_expr (S : state) (C : execution_ctx) ((spec_env_record_set_mutable_binding (L : env_loc) (x : prop_name) (v : value) (str : bool)) : ext_expr) (o : out)) ->
        (* ------------------------------------------ *)
        (red_expr (S0 : state) (C : execution_ctx) ((spec_env_record_create_set_mutable_binding_1 ((out_ter (S : state) (res_intro restype_normal resvalue_empty label_empty)) : out) (L : env_loc) (x : prop_name) (v : value) (str : bool)) : ext_expr) (o : out))

  | red_spec_entering_eval_code :
      forall (str : bool) (C' : execution_ctx) (S : state (* input *)) (C : execution_ctx (* input *)) (bdirect : bool (* input *)) (bd : funcbody (* input *)) (K : ext_expr (* input *)) (o : out),
        (str = ((((funcbody_is_strict bd) : bool) || ((bdirect && (execution_ctx_strict C)) : bool)) : strictness_flag)) ->
        (C' = ((ifb bdirect then (C : execution_ctx) else (execution_ctx_initial (str : strictness_flag))) : execution_ctx)) ->
        (* ========================================== *)
        (red_expr (S : state) (C' : execution_ctx) ((spec_entering_eval_code_1 (bd : funcbody) (K : ext_expr) (str : bool)) : ext_expr) (o : out)) ->
        (* ------------------------------------------ *)
        (red_expr (S : state) (C : execution_ctx) ((spec_entering_eval_code (bdirect : bool) (bd : funcbody) (K : ext_expr)) : ext_expr) (o : out))

  | red_spec_entering_eval_code_1 :
      forall (str : bool (* input *)) (lex : lexical_env) (S' : state) (C' : execution_ctx) (o1 : out) (S : state (* input *)) (C : execution_ctx (* input *)) (bd : funcbody (* input *)) (K : ext_expr (* input *)) (o : out),
        (((lex, S') : (lexical_env * state)) = (ifb str then ((lexical_env_alloc_decl S (execution_ctx_lexical_env (C : execution_ctx))) : (lexical_env * state)) else ((execution_ctx_lexical_env (C : execution_ctx)), S))) ->
        (C' = ((ifb str then ((execution_ctx_with_lex_same (C : execution_ctx) (lex : lexical_env)) : execution_ctx) else C) : execution_ctx)) ->
        (* ========================================== *)
        (red_expr (S' : state) (C' : execution_ctx) ((spec_binding_inst (codetype_eval : codetype) (None : (option object_loc)) ((funcbody_prog bd) : prog) (nil : (list value))) : ext_expr) (o1 : out)) ->
        (red_expr (S' : state) (C' : execution_ctx) ((spec_entering_eval_code_2 (o1 : out) (K : ext_expr)) : ext_expr) (o : out)) ->
        (* ------------------------------------------ *)
        (red_expr (S : state) (C : execution_ctx) ((spec_entering_eval_code_1 (bd : funcbody) (K : ext_expr) (str : bool)) : ext_expr) (o : out))

  | red_spec_entering_eval_code_2 :
      forall (S0 : state (* input *)) (C : execution_ctx (* input *)) (S : state (* input *)) (K : ext_expr (* input *)) (o : out),
        (* ========================================== *)
        (red_expr (S : state) (C : execution_ctx) (K : ext_expr) (o : out)) ->
        (* ------------------------------------------ *)
        (red_expr (S0 : state) (C : execution_ctx) ((spec_entering_eval_code_2 ((out_ter (S : state) (res_intro restype_normal resvalue_empty label_empty)) : out) (K : ext_expr)) : ext_expr) (o : out))

  | red_spec_entering_func_code :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (lf : object_loc (* input *)) (vthis : value (* input *)) (args : (list value) (* input *)) (bd : funcbody) (str : strictness_flag) (K : ext_expr (* input *)) (o : out),
        (object_method object_code_ S lf (Some bd)) ->
        (str = ((funcbody_is_strict bd) : strictness_flag)) ->
        (* ========================================== *)
        (red_expr (S : state) (C : execution_ctx) ((spec_entering_func_code_1 (lf : object_loc) (args : (list value)) (bd : funcbody) (vthis : value) (str : strictness_flag) (K : ext_expr)) : ext_expr) (o : out)) ->
        (* ------------------------------------------ *)
        (red_expr (S : state) (C : execution_ctx) ((spec_entering_func_code (lf : object_loc) (vthis : value) (args : (list value)) (K : ext_expr)) : ext_expr) (o : out))

  | red_spec_entering_func_code_1_strict :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (lf : object_loc (* input *)) (args : (list value) (* input *)) (bd : funcbody (* input *)) (vthis : value (* input *)) (K : ext_expr (* input *)) (o : out),
        (* ========================================== *)
        (red_expr (S : state) (C : execution_ctx) ((spec_entering_func_code_3 (lf : object_loc) (args : (list value)) (true : strictness_flag) (bd : funcbody) (vthis : value) (K : ext_expr)) : ext_expr) (o : out)) ->
        (* ------------------------------------------ *)
        (red_expr (S : state) (C : execution_ctx) ((spec_entering_func_code_1 (lf : object_loc) (args : (list value)) (bd : funcbody) (vthis : value) (true : strictness_flag) (K : ext_expr)) : ext_expr) (o : out))

  | red_spec_entering_func_code_1_null_or_undef :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (lf : object_loc (* input *)) (args : (list value) (* input *)) (bd : funcbody (* input *)) (vthis : value (* input *)) (K : ext_expr (* input *)) (o : out),
        (((vthis = null) : Prop) \/ ((vthis = undef) : Prop)) ->
        (* ========================================== *)
        (red_expr (S : state) (C : execution_ctx) ((spec_entering_func_code_3 (lf : object_loc) (args : (list value)) (false : strictness_flag) (bd : funcbody) (prealloc_global : value) (K : ext_expr)) : ext_expr) (o : out)) ->
        (* ------------------------------------------ *)
        (red_expr (S : state) (C : execution_ctx) ((spec_entering_func_code_1 (lf : object_loc) (args : (list value)) (bd : funcbody) (vthis : value) (false : strictness_flag) (K : ext_expr)) : ext_expr) (o : out))

  | red_spec_entering_func_code_1_not_object :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (lf : object_loc (* input *)) (args : (list value) (* input *)) (bd : funcbody (* input *)) (vthis : value (* input *)) (o1 : out) (K : ext_expr (* input *)) (o : out),
        ((((vthis <> null) /\ (vthis <> undef)) : Prop) /\ (((type_of vthis) <> type_object) : Prop)) ->
        (* ========================================== *)
        (red_expr (S : state) (C : execution_ctx) ((spec_to_object (vthis : value)) : ext_expr) (o1 : out)) ->
        (red_expr (S : state) (C : execution_ctx) ((spec_entering_func_code_2 (lf : object_loc) (args : (list value)) (bd : funcbody) (o1 : out) (K : ext_expr)) : ext_expr) (o : out)) ->
        (* ------------------------------------------ *)
        (red_expr (S : state) (C : execution_ctx) ((spec_entering_func_code_1 (lf : object_loc) (args : (list value)) (bd : funcbody) (vthis : value) (false : strictness_flag) (K : ext_expr)) : ext_expr) (o : out))

  | red_spec_entering_func_code_2 :
      forall (S : state (* input *)) (S0 : state (* input *)) (C : execution_ctx (* input *)) (lf : object_loc (* input *)) (args : (list value) (* input *)) (bd : funcbody (* input *)) (vthis : value (* input *)) (K : ext_expr (* input *)) (o : out),
        (* ========================================== *)
        (red_expr (S : state) (C : execution_ctx) ((spec_entering_func_code_3 (lf : object_loc) (args : (list value)) (strictness_false : strictness_flag) (bd : funcbody) (vthis : value) (K : ext_expr)) : ext_expr) (o : out)) ->
        (* ------------------------------------------ *)
        (red_expr (S0 : state) (C : execution_ctx) ((spec_entering_func_code_2 (lf : object_loc) (args : (list value)) (bd : funcbody) ((out_ter (S : state) (vthis : res)) : out) (K : ext_expr)) : ext_expr) (o : out))

  | red_spec_entering_func_code_1_object :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (lf : object_loc (* input *)) (args : (list value) (* input *)) (bd : funcbody (* input *)) (lthis : object_loc (* input *)) (K : ext_expr (* input *)) (o : out),
        (* ========================================== *)
        (red_expr (S : state) (C : execution_ctx) ((spec_entering_func_code_3 (lf : object_loc) (args : (list value)) (strictness_false : strictness_flag) (bd : funcbody) (lthis : value) (K : ext_expr)) : ext_expr) (o : out)) ->
        (* ------------------------------------------ *)
        (red_expr (S : state) (C : execution_ctx) ((spec_entering_func_code_1 (lf : object_loc) (args : (list value)) (bd : funcbody) (lthis : value) (false : strictness_flag) (K : ext_expr)) : ext_expr) (o : out))

  | red_spec_entering_func_code_3 :
      forall (lex' : lexical_env) (S' : state) (C' : execution_ctx) (o1 : out) (S : state (* input *)) (C : execution_ctx (* input *)) (lf : object_loc (* input *)) (args : (list value) (* input *)) (str : strictness_flag (* input *)) (bd : funcbody (* input *)) (vthis : value (* input *)) (lex : _) (K : ext_expr (* input *)) (o : out),
        (object_method object_scope_ S lf (Some lex)) ->
        ((lex', S') = (lexical_env_alloc_decl S lex)) ->
        (C' = ((execution_ctx_intro_same (lex' : lexical_env) (vthis : value) (str : strictness_flag)) : execution_ctx)) ->
        (* ========================================== *)
        (red_expr (S' : state) (C' : execution_ctx) ((spec_binding_inst (codetype_func : codetype) ((Some lf) : (option object_loc)) ((funcbody_prog bd) : prog) (args : (list value))) : ext_expr) (o1 : out)) ->
        (red_expr (S' : state) (C' : execution_ctx) ((spec_entering_func_code_4 (o1 : out) (K : ext_expr)) : ext_expr) (o : out)) ->
        (* ------------------------------------------ *)
        (red_expr (S : state) (C : execution_ctx) ((spec_entering_func_code_3 (lf : object_loc) (args : (list value)) (str : strictness_flag) (bd : funcbody) (vthis : value) (K : ext_expr)) : ext_expr) (o : out))

  | red_spec_entering_func_code_4 :
      forall (S0 : state (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (K : ext_expr (* input *)) (o : out),
        (* ========================================== *)
        (red_expr (S : state) (C : execution_ctx) (K : ext_expr) (o : out)) ->
        (* ------------------------------------------ *)
        (red_expr (S0 : state) (C : execution_ctx) ((spec_entering_func_code_4 ((out_ter (S : state) (res_intro restype_normal resvalue_empty label_empty)) : out) (K : ext_expr)) : ext_expr) (o : out))

  | red_spec_binding_inst_formal_params_empty :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (args : (list value) (* input *)) (L : env_loc (* input *)) (str : strictness_flag (* input *)),
        (* ========================================== *)
        (* ------------------------------------------ *)
        (red_expr (S : state) (C : execution_ctx) ((spec_binding_inst_formal_params (args : (list value)) (L : env_loc) (nil : (list string)) (str : strictness_flag)) : ext_expr) ((out_void (S : state)) : out))

  | red_spec_binding_inst_formal_params_non_empty :
      forall (v : value) (args' : (list value)) (S : state (* input *)) (C : execution_ctx (* input *)) (args : (list value) (* input *)) (L : env_loc (* input *)) (x : prop_name (* input *)) (xs : (list prop_name) (* input *)) (str : strictness_flag (* input *)) (o1 : out) (o : out),
        ((v, args') = match args with nil => (undef, nil) | (v :: args') => (v, args') end) ->
        (* ========================================== *)
        (red_expr (S : state) (C : execution_ctx) ((spec_env_record_has_binding (L : env_loc) (x : prop_name)) : ext_expr) (o1 : out)) ->
        (red_expr (S : state) (C : execution_ctx) ((spec_binding_inst_formal_params_1 (args' : (list value)) (L : env_loc) (x : string) (xs : (list string)) (str : strictness_flag) (v : value) (o1 : out)) : ext_expr) (o : out)) ->
        (* ------------------------------------------ *)
        (red_expr (S : state) (C : execution_ctx) ((spec_binding_inst_formal_params (args : (list value)) (L : env_loc) ((x :: (xs : (list prop_name))) : (list string)) (str : strictness_flag)) : ext_expr) (o : out))

  | red_spec_binding_inst_formal_params_1_not_declared :
      forall (S0 : state (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (args : (list value) (* input *)) (L : env_loc (* input *)) (x : prop_name (* input *)) (xs : (list prop_name) (* input *)) (str : strictness_flag (* input *)) (v : value (* input *)) (o : out) (o1 : out),
        (* ========================================== *)
        (red_expr (S : state) (C : execution_ctx) ((spec_env_record_create_mutable_binding (L : env_loc) (x : prop_name) (None : (option bool))) : ext_expr) (o1 : out)) ->
        (red_expr (S : state) (C : execution_ctx) ((spec_binding_inst_formal_params_2 (args : (list value)) (L : env_loc) (x : string) (xs : (list string)) (str : strictness_flag) (v : value) (o1 : out)) : ext_expr) (o : out)) ->
        (* ------------------------------------------ *)
        (red_expr (S0 : state) (C : execution_ctx) ((spec_binding_inst_formal_params_1 (args : (list value)) (L : env_loc) (x : string) (xs : (list string)) (str : strictness_flag) (v : value) ((out_ter (S : state) (false : res)) : out)) : ext_expr) (o : out))

  | red_spec_binding_inst_formal_params_2 :
      forall (S0 : state (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (args : (list value) (* input *)) (L : env_loc (* input *)) (x : prop_name (* input *)) (xs : (list prop_name) (* input *)) (str : strictness_flag (* input *)) (v : value (* input *)) (o : out),
        (* ========================================== *)
        (red_expr (S : state) (C : execution_ctx) ((spec_binding_inst_formal_params_3 (args : (list value)) (L : env_loc) (x : string) (xs : (list string)) (str : strictness_flag) (v : value)) : ext_expr) (o : out)) ->
        (* ------------------------------------------ *)
        (red_expr (S0 : state) (C : execution_ctx) ((spec_binding_inst_formal_params_2 (args : (list value)) (L : env_loc) (x : string) (xs : (list string)) (str : strictness_flag) (v : value) ((out_ter (S : state) (res_intro restype_normal resvalue_empty label_empty)) : out)) : ext_expr) (o : out))

  | red_spec_binding_inst_formal_params_1_declared :
      forall (S0 : state (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (args : (list value) (* input *)) (L : env_loc (* input *)) (x : prop_name (* input *)) (xs : (list prop_name) (* input *)) (str : strictness_flag (* input *)) (v : value (* input *)) (o : out),
        (* ========================================== *)
        (red_expr (S : state) (C : execution_ctx) ((spec_binding_inst_formal_params_3 (args : (list value)) (L : env_loc) (x : string) (xs : (list string)) (str : strictness_flag) (v : value)) : ext_expr) (o : out)) ->
        (* ------------------------------------------ *)
        (red_expr (S0 : state) (C : execution_ctx) ((spec_binding_inst_formal_params_1 (args : (list value)) (L : env_loc) (x : string) (xs : (list string)) (str : strictness_flag) (v : value) ((out_ter (S : state) (true : res)) : out)) : ext_expr) (o : out))

  | red_spec_binding_inst_formal_params_3 :
      forall (o1 : out) (S : state (* input *)) (C : execution_ctx (* input *)) (args : (list value) (* input *)) (L : env_loc (* input *)) (x : prop_name (* input *)) (xs : (list prop_name) (* input *)) (str : strictness_flag (* input *)) (v : value (* input *)) (o : out),
        (* ========================================== *)
        (red_expr (S : state) (C : execution_ctx) ((spec_env_record_set_mutable_binding (L : env_loc) (x : prop_name) (v : value) (str : bool)) : ext_expr) (o1 : out)) ->
        (red_expr (S : state) (C : execution_ctx) ((spec_binding_inst_formal_params_4 (args : (list value)) (L : env_loc) (xs : (list string)) (str : strictness_flag) (o1 : out)) : ext_expr) (o : out)) ->
        (* ------------------------------------------ *)
        (red_expr (S : state) (C : execution_ctx) ((spec_binding_inst_formal_params_3 (args : (list value)) (L : env_loc) (x : string) (xs : (list string)) (str : strictness_flag) (v : value)) : ext_expr) (o : out))

  | red_spec_binding_inst_formal_params_4 :
      forall (S0 : state (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (args : (list value) (* input *)) (L : env_loc (* input *)) (xs : (list prop_name) (* input *)) (str : strictness_flag (* input *)) (o : out),
        (* ========================================== *)
        (red_expr (S : state) (C : execution_ctx) ((spec_binding_inst_formal_params (args : (list value)) (L : env_loc) (xs : (list string)) (str : strictness_flag)) : ext_expr) (o : out)) ->
        (* ------------------------------------------ *)
        (red_expr (S0 : state) (C : execution_ctx) ((spec_binding_inst_formal_params_4 (args : (list value)) (L : env_loc) (xs : (list string)) (str : strictness_flag) ((out_ter (S : state) (res_intro restype_normal resvalue_empty label_empty)) : out)) : ext_expr) (o : out))

  | red_spec_binding_inst_function_decls_nil :
      forall (L : env_loc (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (args : (list value) (* input *)) (str : strictness_flag (* input *)) (bconfig : bool (* input *)),
        (* ========================================== *)
        (* ------------------------------------------ *)
        (red_expr (S : state) (C : execution_ctx) ((spec_binding_inst_function_decls (args : (list value)) (L : env_loc) (nil : (list funcdecl)) (str : strictness_flag) (bconfig : bool)) : ext_expr) ((out_void (S : state)) : out))

  | red_spec_binding_inst_function_decls_cons :
      forall (str_fd : strictness_flag) (S : state (* input *)) (C : execution_ctx (* input *)) (L : env_loc (* input *)) (args : (list value) (* input *)) (fd : funcdecl (* input *)) (fds : (list funcdecl) (* input *)) (str : strictness_flag (* input *)) (bconfig : bool (* input *)) (o1 : out) (o : out),
        (str_fd = (funcbody_is_strict (funcdecl_body (fd : funcdecl)))) ->
        (* ========================================== *)
        (red_expr (S : state) (C : execution_ctx) ((spec_creating_function_object ((funcdecl_parameters (fd : funcdecl)) : (list string)) ((funcdecl_body (fd : funcdecl)) : funcbody) ((execution_ctx_variable_env (C : execution_ctx)) : lexical_env) (str_fd : strictness_flag)) : ext_expr) (o1 : out)) ->
        (red_expr (S : state) (C : execution_ctx) ((spec_binding_inst_function_decls_1 (args : (list value)) (L : env_loc) (fd : funcdecl) (fds : (list funcdecl)) (str : strictness_flag) (bconfig : bool) (o1 : out)) : ext_expr) (o : out)) ->
        (* ------------------------------------------ *)
        (red_expr (S : state) (C : execution_ctx) ((spec_binding_inst_function_decls (args : (list value)) (L : env_loc) ((fd :: fds) : (list funcdecl)) (str : strictness_flag) (bconfig : bool)) : ext_expr) (o : out))

  | red_spec_binding_inst_function_decls_1 :
      forall (o1 : out) (L : env_loc (* input *)) (S0 : state (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (args : (list value) (* input *)) (fd : funcdecl (* input *)) (fds : (list funcdecl) (* input *)) (str : strictness_flag (* input *)) (fo : object_loc (* input *)) (bconfig : bool (* input *)) (o : out),
        (* ========================================== *)
        (red_expr (S : state) (C : execution_ctx) ((spec_env_record_has_binding (L : env_loc) ((funcdecl_name (fd : funcdecl)) : prop_name)) : ext_expr) (o1 : out)) ->
        (red_expr (S : state) (C : execution_ctx) ((spec_binding_inst_function_decls_2 (args : (list value)) (L : env_loc) (fd : funcdecl) (fds : (list funcdecl)) (str : strictness_flag) (fo : object_loc) (bconfig : bool) (o1 : out)) : ext_expr) (o : out)) ->
        (* ------------------------------------------ *)
        (red_expr (S0 : state) (C : execution_ctx) ((spec_binding_inst_function_decls_1 (args : (list value)) (L : env_loc) (fd : funcdecl) (fds : (list funcdecl)) (str : strictness_flag) (bconfig : bool) ((out_ter (S : state) (fo : res)) : out)) : ext_expr) (o : out))

  | red_spec_binding_inst_function_decls_2_false :
      forall (o1 : out) (L : env_loc (* input *)) (S0 : state (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (args : (list value) (* input *)) (fd : funcdecl (* input *)) (fds : (list funcdecl) (* input *)) (str : strictness_flag (* input *)) (fo : object_loc (* input *)) (bconfig : bool (* input *)) (o : out),
        (* ========================================== *)
        (red_expr (S : state) (C : execution_ctx) ((spec_env_record_create_mutable_binding (L : env_loc) ((funcdecl_name (fd : funcdecl)) : prop_name) ((Some bconfig) : (option bool))) : ext_expr) (o1 : out)) ->
        (red_expr (S : state) (C : execution_ctx) ((spec_binding_inst_function_decls_4 (args : (list value)) (L : env_loc) (fd : funcdecl) (fds : (list funcdecl)) (str : strictness_flag) (fo : object_loc) (bconfig : bool) (o1 : out)) : ext_expr) (o : out)) ->
        (* ------------------------------------------ *)
        (red_expr (S0 : state) (C : execution_ctx) ((spec_binding_inst_function_decls_2 (args : (list value)) (L : env_loc) (fd : funcdecl) (fds : (list funcdecl)) (str : strictness_flag) (fo : object_loc) (bconfig : bool) ((out_ter (S : state) (false : res)) : out)) : ext_expr) (o : out))

  | red_spec_binding_inst_function_decls_2_true_global :
      forall (S0 : state (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (args : (list value) (* input *)) (fd : funcdecl (* input *)) (fds : (list funcdecl) (* input *)) (str : strictness_flag (* input *)) (fo : object_loc (* input *)) (bconfig : bool (* input *)) (y1 : (specret full_descriptor)) (o : out),
        (* ========================================== *)
        (red_spec S C (spec_object_get_prop (prealloc_global : object_loc) ((funcdecl_name (fd : funcdecl)) : prop_name)) y1) ->
        (red_expr (S : state) (C : execution_ctx) ((spec_binding_inst_function_decls_3 (args : (list value)) (fd : funcdecl) (fds : (list funcdecl)) (str : strictness_flag) (fo : object_loc) (bconfig : bool) (y1 : (specret full_descriptor))) : ext_expr) (o : out)) ->
        (* ------------------------------------------ *)
        (red_expr (S0 : state) (C : execution_ctx) ((spec_binding_inst_function_decls_2 (args : (list value)) (env_loc_global_env_record : env_loc) (fd : funcdecl) (fds : (list funcdecl)) (str : strictness_flag) (fo : object_loc) (bconfig : bool) ((out_ter (S : state) (true : res)) : out)) : ext_expr) (o : out))

  | red_spec_binding_inst_function_decls_3_true :
      forall (S0 : state (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (args : (list value) (* input *)) (fd : funcdecl (* input *)) (fds : (list funcdecl) (* input *)) (str : strictness_flag (* input *)) (fo : object_loc (* input *)) (bconfig : bool (* input *)) (A : attributes (* input *)) (Anew : attributes_data) (o1 : out) (o : out),
        ((attributes_configurable (A : attributes)) = (true : bool)) ->
        ((Anew : attributes_data) = (attributes_data_intro (undef : value) (true : bool) (true : bool) (bconfig : bool))) ->
        (* ========================================== *)
        (red_expr (S : state) (C : execution_ctx) ((spec_object_define_own_prop (prealloc_global : object_loc) ((funcdecl_name (fd : funcdecl)) : prop_name) (Anew : descriptor) (true : bool)) : ext_expr) (o1 : out)) ->
        (red_expr (S : state) (C : execution_ctx) ((spec_binding_inst_function_decls_4 (args : (list value)) (env_loc_global_env_record : env_loc) (fd : funcdecl) (fds : (list funcdecl)) (str : strictness_flag) (fo : object_loc) (bconfig : bool) (o1 : out)) : ext_expr) (o : out)) ->
        (* ------------------------------------------ *)
        (red_expr (S0 : state) (C : execution_ctx) ((spec_binding_inst_function_decls_3 (args : (list value)) (fd : funcdecl) (fds : (list funcdecl)) (str : strictness_flag) (fo : object_loc) (bconfig : bool) ((specret_val S (full_descriptor_some (A : attributes))) : (specret full_descriptor))) : ext_expr) (o : out))

  | red_spec_binding_inst_function_decls_4 :
      forall (S0 : state (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (args : (list value) (* input *)) (L : env_loc (* input *)) (fd : funcdecl (* input *)) (fds : (list funcdecl) (* input *)) (str : strictness_flag (* input *)) (fo : object_loc (* input *)) (bconfig : bool (* input *)) (rv : resvalue (* input *)) (o : out),
        (* ========================================== *)
        (red_expr (S : state) (C : execution_ctx) ((spec_binding_inst_function_decls_5 (args : (list value)) (L : env_loc) (fd : funcdecl) (fds : (list funcdecl)) (str : strictness_flag) (fo : object_loc) (bconfig : bool)) : ext_expr) (o : out)) ->
        (* ------------------------------------------ *)
        (red_expr (S0 : state) (C : execution_ctx) ((spec_binding_inst_function_decls_4 (args : (list value)) (L : env_loc) (fd : funcdecl) (fds : (list funcdecl)) (str : strictness_flag) (fo : object_loc) (bconfig : bool) ((out_ter (S : state) (rv : res)) : out)) : ext_expr) (o : out))

  | red_spec_binding_inst_function_decls_3_false :
      forall (S0 : state (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (args : (list value) (* input *)) (fd : funcdecl (* input *)) (fds : (list funcdecl) (* input *)) (str : strictness_flag (* input *)) (fo : object_loc (* input *)) (A : attributes (* input *)) (bconfig : bool (* input *)) (o : out),
        ((attributes_configurable (A : attributes)) = (false : bool)) ->
        (* ========================================== *)
        (red_expr (S : state) (C : execution_ctx) ((spec_binding_inst_function_decls_3a (args : (list value)) (fd : funcdecl) (fds : (list funcdecl)) (str : strictness_flag) (fo : object_loc) (bconfig : bool) (A : full_descriptor)) : ext_expr) (o : out)) ->
        (* ------------------------------------------ *)
        (red_expr (S0 : state) (C : execution_ctx) ((spec_binding_inst_function_decls_3 (args : (list value)) (fd : funcdecl) (fds : (list funcdecl)) (str : strictness_flag) (fo : object_loc) (bconfig : bool) ((specret_val S (full_descriptor_some (A : attributes))) : (specret full_descriptor))) : ext_expr) (o : out))

  | red_spec_binding_inst_function_decls_3a_type_error :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (args : (list value) (* input *)) (fd : funcdecl (* input *)) (fds : (list funcdecl) (* input *)) (str : strictness_flag (* input *)) (fo : object_loc (* input *)) (A : attributes (* input *)) (bconfig : bool (* input *)) (o : out),
        ((((descriptor_is_accessor A) \/ ((attributes_writable A) = false)) : Prop) \/ (((attributes_enumerable A) = false) : Prop)) ->
        (* ========================================== *)
        (red_expr (S : state) (C : execution_ctx) ((spec_error (native_error_type : native_error)) : ext_expr) (o : out)) ->
        (* ------------------------------------------ *)
        (red_expr (S : state) (C : execution_ctx) ((spec_binding_inst_function_decls_3a (args : (list value)) (fd : funcdecl) (fds : (list funcdecl)) (str : strictness_flag) (fo : object_loc) (bconfig : bool) (A : full_descriptor)) : ext_expr) (o : out))

  | red_spec_binding_inst_function_decls_3a_no_error :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (args : (list value) (* input *)) (fd : funcdecl (* input *)) (fds : (list funcdecl) (* input *)) (str : strictness_flag (* input *)) (fo : object_loc (* input *)) (A : attributes (* input *)) (bconfig : bool (* input *)) (o : out),
        (~ ((((descriptor_is_accessor A) \/ ((attributes_writable A) = false)) : Prop) \/ (((attributes_enumerable A) = false) : Prop))) ->
        (* ========================================== *)
        (red_expr (S : state) (C : execution_ctx) ((spec_binding_inst_function_decls_5 (args : (list value)) (env_loc_global_env_record : env_loc) (fd : funcdecl) (fds : (list funcdecl)) (str : strictness_flag) (fo : object_loc) (bconfig : bool)) : ext_expr) (o : out)) ->
        (* ------------------------------------------ *)
        (red_expr (S : state) (C : execution_ctx) ((spec_binding_inst_function_decls_3a (args : (list value)) (fd : funcdecl) (fds : (list funcdecl)) (str : strictness_flag) (fo : object_loc) (bconfig : bool) (A : full_descriptor)) : ext_expr) (o : out))

  | red_spec_binding_inst_function_decls_2_true :
      forall (L : env_loc (* input *)) (S0 : state (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (args : (list value) (* input *)) (fd : funcdecl (* input *)) (fds : (list funcdecl) (* input *)) (str : strictness_flag (* input *)) (fo : object_loc (* input *)) (bconfig : bool (* input *)) (o : out),
        (L <> (env_loc_global_env_record : env_loc)) ->
        (* ========================================== *)
        (red_expr (S : state) (C : execution_ctx) ((spec_binding_inst_function_decls_5 (args : (list value)) (L : env_loc) (fd : funcdecl) (fds : (list funcdecl)) (str : strictness_flag) (fo : object_loc) (bconfig : bool)) : ext_expr) (o : out)) ->
        (* ------------------------------------------ *)
        (red_expr (S0 : state) (C : execution_ctx) ((spec_binding_inst_function_decls_2 (args : (list value)) (L : env_loc) (fd : funcdecl) (fds : (list funcdecl)) (str : strictness_flag) (fo : object_loc) (bconfig : bool) ((out_ter (S : state) (true : res)) : out)) : ext_expr) (o : out))

  | red_spec_binding_inst_function_decls_5 :
      forall (o1 : out) (L : env_loc (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (args : (list value) (* input *)) (fd : funcdecl (* input *)) (fds : (list funcdecl) (* input *)) (str : strictness_flag (* input *)) (fo : object_loc (* input *)) (bconfig : bool (* input *)) (o : out),
        (* ========================================== *)
        (red_expr (S : state) (C : execution_ctx) ((spec_env_record_set_mutable_binding (L : env_loc) ((funcdecl_name (fd : funcdecl)) : prop_name) ((value_object (fo : object_loc)) : value) (str : bool)) : ext_expr) (o1 : out)) ->
        (red_expr (S : state) (C : execution_ctx) ((spec_binding_inst_function_decls_6 (args : (list value)) (L : env_loc) (fds : (list funcdecl)) (str : strictness_flag) (bconfig : bool) (o1 : out)) : ext_expr) (o : out)) ->
        (* ------------------------------------------ *)
        (red_expr (S : state) (C : execution_ctx) ((spec_binding_inst_function_decls_5 (args : (list value)) (L : env_loc) (fd : funcdecl) (fds : (list funcdecl)) (str : strictness_flag) (fo : object_loc) (bconfig : bool)) : ext_expr) (o : out))

  | red_spec_binding_inst_function_decls_6 :
      forall (L : env_loc (* input *)) (S0 : state (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (args : (list value) (* input *)) (fds : (list funcdecl) (* input *)) (str : strictness_flag (* input *)) (bconfig : bool (* input *)) (o : out),
        (* ========================================== *)
        (red_expr (S : state) (C : execution_ctx) ((spec_binding_inst_function_decls (args : (list value)) (L : env_loc) (fds : (list funcdecl)) (str : strictness_flag) (bconfig : bool)) : ext_expr) (o : out)) ->
        (* ------------------------------------------ *)
        (red_expr (S0 : state) (C : execution_ctx) ((spec_binding_inst_function_decls_6 (args : (list value)) (L : env_loc) (fds : (list funcdecl)) (str : strictness_flag) (bconfig : bool) ((out_ter (S : state) (res_intro restype_normal resvalue_empty label_empty)) : out)) : ext_expr) (o : out))

  | red_spec_binding_inst_arg_obj :
      forall (str : strictness_flag) (o1 : out) (L : env_loc (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (lf : object_loc (* input *)) (code : prog (* input *)) (xs : (list prop_name) (* input *)) (args : (list value) (* input *)) (o : out),
        (str = ((prog_intro_strictness code) : strictness_flag)) ->
        (* ========================================== *)
        (red_expr (S : state) (C : execution_ctx) ((spec_create_arguments_object (lf : object_loc) (xs : (list string)) (args : (list value)) ((execution_ctx_variable_env (C : execution_ctx)) : lexical_env) (str : strictness_flag)) : ext_expr) (o1 : out)) ->
        (red_expr (S : state) (C : execution_ctx) ((spec_binding_inst_arg_obj_1 (code : prog) (L : env_loc) (str : strictness_flag) (o1 : out)) : ext_expr) (o : out)) ->
        (* ------------------------------------------ *)
        (red_expr (S : state) (C : execution_ctx) ((spec_binding_inst_arg_obj (lf : object_loc) (code : prog) (xs : (list string)) (args : (list value)) (L : env_loc)) : ext_expr) (o : out))

  | red_spec_binding_inst_arg_obj_1_strict :
      forall (o1 : out) (L : env_loc (* input *)) (S0 : state (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (code : prog (* input *)) (largs : object_loc (* input *)) (o : out),
        (* ========================================== *)
        (red_expr (S : state) (C : execution_ctx) ((spec_env_record_create_immutable_binding (L : env_loc) ((("arguments")%string) : prop_name)) : ext_expr) (o1 : out)) ->
        (red_expr (S : state) (C : execution_ctx) ((spec_binding_inst_arg_obj_2 (code : prog) (L : env_loc) (largs : object_loc) (o1 : out)) : ext_expr) (o : out)) ->
        (* ------------------------------------------ *)
        (red_expr (S0 : state) (C : execution_ctx) ((spec_binding_inst_arg_obj_1 (code : prog) (L : env_loc) (true : strictness_flag) ((out_ter (S : state) (largs : res)) : out)) : ext_expr) (o : out))

  | red_spec_binding_inst_arg_obj_2 :
      forall (L : env_loc (* input *)) (S0 : state (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (code : prog (* input *)) (largs : object_loc (* input *)) (o : out),
        (* ========================================== *)
        (red_expr (S : state) (C : execution_ctx) ((spec_env_record_initialize_immutable_binding (L : env_loc) ((("arguments")%string) : prop_name) ((value_object (largs : object_loc)) : value)) : ext_expr) (o : out)) ->
        (* ------------------------------------------ *)
        (red_expr (S0 : state) (C : execution_ctx) ((spec_binding_inst_arg_obj_2 (code : prog) (L : env_loc) (largs : object_loc) ((out_ter (S : state) (res_intro restype_normal resvalue_empty label_empty)) : out)) : ext_expr) (o : out))

  | red_spec_binding_inst_arg_obj_1_not_strict :
      forall (L : env_loc (* input *)) (S0 : state (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (code : prog (* input *)) (largs : value (* input *)) (o : out),
        (* ========================================== *)
        (red_expr (S : state) (C : execution_ctx) ((spec_env_record_create_set_mutable_binding (L : env_loc) ((("arguments")%string) : prop_name) (None : (option bool)) (largs : value) (false : bool)) : ext_expr) (o : out)) ->
        (* ------------------------------------------ *)
        (red_expr (S0 : state) (C : execution_ctx) ((spec_binding_inst_arg_obj_1 (code : prog) (L : env_loc) (false : strictness_flag) ((out_ter (S : state) (largs : res)) : out)) : ext_expr) (o : out))

  | red_spec_binding_inst_var_decls_nil :
      forall (L : env_loc (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (bconfig : bool (* input *)) (str : strictness_flag (* input *)),
        (* ========================================== *)
        (* ------------------------------------------ *)
        (red_expr (S : state) (C : execution_ctx) ((spec_binding_inst_var_decls (L : env_loc) (nil : (list string)) (bconfig : bool) (str : strictness_flag)) : ext_expr) ((out_void (S : state)) : out))

  | red_spec_binding_inst_var_decls_cons :
      forall (o1 : out) (L : env_loc (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (vd : string (* input *)) (vds : (list string) (* input *)) (bconfig : bool (* input *)) (str : strictness_flag (* input *)) (o : out),
        (* ========================================== *)
        (red_expr (S : state) (C : execution_ctx) ((spec_env_record_has_binding (L : env_loc) (vd : prop_name)) : ext_expr) (o1 : out)) ->
        (red_expr (S : state) (C : execution_ctx) ((spec_binding_inst_var_decls_1 (L : env_loc) (vd : string) (vds : (list string)) (bconfig : bool) (str : strictness_flag) (o1 : out)) : ext_expr) (o : out)) ->
        (* ------------------------------------------ *)
        (red_expr (S : state) (C : execution_ctx) ((spec_binding_inst_var_decls (L : env_loc) ((vd :: vds) : (list string)) (bconfig : bool) (str : strictness_flag)) : ext_expr) (o : out))

  | red_spec_binding_inst_var_decls_1_true :
      forall (L : env_loc (* input *)) (S0 : state (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (vd : string (* input *)) (vds : (list string) (* input *)) (bconfig : bool (* input *)) (str : strictness_flag (* input *)) (o : out),
        (* ========================================== *)
        (red_expr (S : state) (C : execution_ctx) ((spec_binding_inst_var_decls (L : env_loc) (vds : (list string)) (bconfig : bool) (str : strictness_flag)) : ext_expr) (o : out)) ->
        (* ------------------------------------------ *)
        (red_expr (S0 : state) (C : execution_ctx) ((spec_binding_inst_var_decls_1 (L : env_loc) (vd : string) (vds : (list string)) (bconfig : bool) (str : strictness_flag) ((out_ter (S : state) (true : res)) : out)) : ext_expr) (o : out))

  | red_spec_binding_inst_var_decls_1_false :
      forall (o1 : out) (L : env_loc (* input *)) (S0 : state (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (vd : string (* input *)) (vds : (list string) (* input *)) (bconfig : bool (* input *)) (str : strictness_flag (* input *)) (o : out),
        (* ========================================== *)
        (red_expr (S : state) (C : execution_ctx) ((spec_env_record_create_set_mutable_binding (L : env_loc) (vd : prop_name) ((Some bconfig) : (option bool)) (undef : value) (str : bool)) : ext_expr) (o1 : out)) ->
        (red_expr (S : state) (C : execution_ctx) ((spec_binding_inst_var_decls_2 (L : env_loc) (vds : (list string)) (bconfig : bool) (str : strictness_flag) (o1 : out)) : ext_expr) (o : out)) ->
        (* ------------------------------------------ *)
        (red_expr (S0 : state) (C : execution_ctx) ((spec_binding_inst_var_decls_1 (L : env_loc) (vd : string) (vds : (list string)) (bconfig : bool) (str : strictness_flag) ((out_ter (S : state) (false : res)) : out)) : ext_expr) (o : out))

  | red_spec_binding_inst_var_decls_2 :
      forall (L : env_loc (* input *)) (S0 : state (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (vds : (list string) (* input *)) (bconfig : bool (* input *)) (str : strictness_flag (* input *)) (o : out),
        (* ========================================== *)
        (red_expr (S : state) (C : execution_ctx) ((spec_binding_inst_var_decls (L : env_loc) (vds : (list string)) (bconfig : bool) (str : strictness_flag)) : ext_expr) (o : out)) ->
        (* ------------------------------------------ *)
        (red_expr (S0 : state) (C : execution_ctx) ((spec_binding_inst_var_decls_2 (L : env_loc) (vds : (list string)) (bconfig : bool) (str : strictness_flag) ((out_ter (S : state) (res_intro restype_normal resvalue_empty label_empty)) : out)) : ext_expr) (o : out))

  | red_spec_binding_inst :
      forall (L : env_loc) (Ls : (list env_loc)) (S : state (* input *)) (C : execution_ctx (* input *)) (ct : codetype (* input *)) (olf : (option object_loc) (* input *)) (code : prog (* input *)) (args : (list value) (* input *)) (o : out),
        ((execution_ctx_variable_env (C : execution_ctx)) = ((L :: (Ls : (list env_loc))) : lexical_env)) ->
        (* ========================================== *)
        (red_expr (S : state) (C : execution_ctx) ((spec_binding_inst_1 (ct : codetype) (olf : (option object_loc)) (code : prog) (args : (list value)) (L : env_loc)) : ext_expr) (o : out)) ->
        (* ------------------------------------------ *)
        (red_expr (S : state) (C : execution_ctx) ((spec_binding_inst (ct : codetype) (olf : (option object_loc)) (code : prog) (args : (list value))) : ext_expr) (o : out))

  | red_spec_binding_inst_1_function :
      forall (o1 : out) (xs : (list prop_name)) (S : state (* input *)) (C : execution_ctx (* input *)) (lf : object_loc (* input *)) (code : prog (* input *)) (args : (list value) (* input *)) (L : env_loc (* input *)) (o : out),
        (object_method object_formal_parameters_ S lf (Some xs)) ->
        (* ========================================== *)
        (red_expr (S : state) (C : execution_ctx) ((spec_binding_inst_formal_params (args : (list value)) (L : env_loc) (xs : (list string)) ((prog_intro_strictness code) : strictness_flag)) : ext_expr) (o1 : out)) ->
        (red_expr (S : state) (C : execution_ctx) ((spec_binding_inst_2 (codetype_func : codetype) (lf : object_loc) (code : prog) (xs : (list string)) (args : (list value)) (L : env_loc) (o1 : out)) : ext_expr) (o : out)) ->
        (* ------------------------------------------ *)
        (red_expr (S : state) (C : execution_ctx) ((spec_binding_inst_1 (codetype_func : codetype) ((Some lf) : (option object_loc)) (code : prog) (args : (list value)) (L : env_loc)) : ext_expr) (o : out))

  | red_spec_binding_inst_2 :
      forall (S0 : state (* input *)) (xs : (list prop_name) (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (lf : object_loc (* input *)) (code : prog (* input *)) (args : (list value) (* input *)) (L : env_loc (* input *)) (o : out),
        (* ========================================== *)
        (red_expr (S : state) (C : execution_ctx) ((spec_binding_inst_3 (codetype_func : codetype) ((Some lf) : (option object_loc)) (code : prog) (xs : (list string)) (args : (list value)) (L : env_loc)) : ext_expr) (o : out)) ->
        (* ------------------------------------------ *)
        (red_expr (S0 : state) (C : execution_ctx) ((spec_binding_inst_2 (codetype_func : codetype) (lf : object_loc) (code : prog) (xs : (list string)) (args : (list value)) (L : env_loc) ((out_ter (S : state) (res_intro restype_normal resvalue_empty label_empty)) : out)) : ext_expr) (o : out))

  | red_spec_binding_inst_1_not_function :
      forall (L : env_loc (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (ct : codetype (* input *)) (code : prog (* input *)) (args : (list value) (* input *)) (o : out),
        (ct <> (codetype_func : codetype)) ->
        (* ========================================== *)
        (red_expr (S : state) (C : execution_ctx) ((spec_binding_inst_3 (ct : codetype) (None : (option object_loc)) (code : prog) (nil : (list string)) (args : (list value)) (L : env_loc)) : ext_expr) (o : out)) ->
        (* ------------------------------------------ *)
        (red_expr (S : state) (C : execution_ctx) ((spec_binding_inst_1 (ct : codetype) (None : (option object_loc)) (code : prog) (args : (list value)) (L : env_loc)) : ext_expr) (o : out))

  | red_spec_binding_inst_3 :
      forall (bconfig : bool) (L : env_loc (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (ct : codetype (* input *)) (olf : (option object_loc) (* input *)) (code : prog (* input *)) (fds : (list funcdecl)) (xs : (list prop_name) (* input *)) (args : (list value) (* input *)) (o1 : out) (o : out),
        ((bconfig : bool) = (ifb (ct = (codetype_eval : codetype)) then (true : bool) else false)) ->
        ((fds : (list funcdecl)) = (prog_funcdecl (code : prog))) ->
        (* ========================================== *)
        (red_expr (S : state) (C : execution_ctx) ((spec_binding_inst_function_decls (args : (list value)) (L : env_loc) (fds : (list funcdecl)) ((prog_intro_strictness code) : strictness_flag) (bconfig : bool)) : ext_expr) (o1 : out)) ->
        (red_expr (S : state) (C : execution_ctx) ((spec_binding_inst_4 (ct : codetype) (olf : (option object_loc)) (code : prog) (xs : (list string)) (args : (list value)) (bconfig : bool) (L : env_loc) (o1 : out)) : ext_expr) (o : out)) ->
        (* ------------------------------------------ *)
        (red_expr (S : state) (C : execution_ctx) ((spec_binding_inst_3 (ct : codetype) (olf : (option object_loc)) (code : prog) (xs : (list string)) (args : (list value)) (L : env_loc)) : ext_expr) (o : out))

  | red_spec_binding_inst_4 :
      forall (bconfig : bool (* input *)) (L : env_loc (* input *)) (S0 : state (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (ct : codetype (* input *)) (olf : (option object_loc) (* input *)) (code : prog (* input *)) (xs : (list prop_name) (* input *)) (args : (list value) (* input *)) (o : out),
        (* ========================================== *)
        (red_expr (S : state) (C : execution_ctx) ((spec_binding_inst_5 (ct : codetype) (olf : (option object_loc)) (code : prog) (xs : (list string)) (args : (list value)) (bconfig : bool) (L : env_loc)) : ext_expr) (o : out)) ->
        (* ------------------------------------------ *)
        (red_expr (S0 : state) (C : execution_ctx) ((spec_binding_inst_4 (ct : codetype) (olf : (option object_loc)) (code : prog) (xs : (list string)) (args : (list value)) (bconfig : bool) (L : env_loc) ((out_ter (S : state) (res_intro restype_normal resvalue_empty label_empty)) : out)) : ext_expr) (o : out))

  | red_spec_binding_inst_5 :
      forall (o1 : out) (L : env_loc (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (ct : codetype (* input *)) (olf : (option object_loc) (* input *)) (code : prog (* input *)) (xs : (list prop_name) (* input *)) (args : (list value) (* input *)) (bconfig : bool (* input *)) (o : out),
        (* ========================================== *)
        (red_expr (S : state) (C : execution_ctx) ((spec_env_record_has_binding (L : env_loc) ((("arguments")%string) : prop_name)) : ext_expr) (o1 : out)) ->
        (red_expr (S : state) (C : execution_ctx) ((spec_binding_inst_6 (ct : codetype) (olf : (option object_loc)) (code : prog) (xs : (list string)) (args : (list value)) (bconfig : bool) (L : env_loc) (o1 : out)) : ext_expr) (o : out)) ->
        (* ------------------------------------------ *)
        (red_expr (S : state) (C : execution_ctx) ((spec_binding_inst_5 (ct : codetype) (olf : (option object_loc)) (code : prog) (xs : (list string)) (args : (list value)) (bconfig : bool) (L : env_loc)) : ext_expr) (o : out))

  | red_spec_binding_inst_6_arguments :
      forall (o1 : out) (L : env_loc (* input *)) (S0 : state (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (lf : object_loc (* input *)) (code : prog (* input *)) (xs : (list prop_name) (* input *)) (args : (list value) (* input *)) (bconfig : bool (* input *)) (o : out),
        (* ========================================== *)
        (red_expr (S : state) (C : execution_ctx) ((spec_binding_inst_arg_obj (lf : object_loc) (code : prog) (xs : (list string)) (args : (list value)) (L : env_loc)) : ext_expr) (o1 : out)) ->
        (red_expr (S : state) (C : execution_ctx) ((spec_binding_inst_7 (code : prog) (bconfig : bool) (L : env_loc) (o1 : out)) : ext_expr) (o : out)) ->
        (* ------------------------------------------ *)
        (red_expr (S0 : state) (C : execution_ctx) ((spec_binding_inst_6 (codetype_func : codetype) ((Some lf) : (option object_loc)) (code : prog) (xs : (list string)) (args : (list value)) (bconfig : bool) (L : env_loc) ((out_ter (S : state) (false : res)) : out)) : ext_expr) (o : out))

  | red_spec_binding_inst_7 :
      forall (S0 : state (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (code : prog (* input *)) (bconfig : bool (* input *)) (L : env_loc (* input *)) (o : out),
        (* ========================================== *)
        (red_expr (S : state) (C : execution_ctx) ((spec_binding_inst_8 (code : prog) (bconfig : bool) (L : env_loc)) : ext_expr) (o : out)) ->
        (* ------------------------------------------ *)
        (red_expr (S0 : state) (C : execution_ctx) ((spec_binding_inst_7 (code : prog) (bconfig : bool) (L : env_loc) ((out_ter (S : state) (res_intro restype_normal resvalue_empty label_empty)) : out)) : ext_expr) (o : out))

  | red_spec_binding_inst_6_no_arguments :
      forall (L : env_loc (* input *)) (S0 : state (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (ct : codetype (* input *)) (olf : (option object_loc) (* input *)) (code : prog (* input *)) (xs : (list prop_name) (* input *)) (args : (list value) (* input *)) (bconfig : bool (* input *)) (bdefined : res (* input *)) (o : out),
        (~ (((ct = codetype_func) : Prop) /\ ((bdefined = false) : Prop))) ->
        (* ========================================== *)
        (red_expr (S : state) (C : execution_ctx) ((spec_binding_inst_8 (code : prog) (bconfig : bool) (L : env_loc)) : ext_expr) (o : out)) ->
        (* ------------------------------------------ *)
        (red_expr (S0 : state) (C : execution_ctx) ((spec_binding_inst_6 (ct : codetype) (olf : (option object_loc)) (code : prog) (xs : (list string)) (args : (list value)) (bconfig : bool) (L : env_loc) ((out_ter (S : state) (bdefined : res)) : out)) : ext_expr) (o : out))

  | red_spec_binding_inst_8 :
      forall (S0 : state (* input *)) (L : env_loc (* input *)) (S : state) (C : execution_ctx (* input *)) (code : prog (* input *)) (bconfig : bool (* input *)) (o : out),
        (* ========================================== *)
        (red_expr (S : state) (C : execution_ctx) ((spec_binding_inst_var_decls (L : env_loc) ((prog_vardecl (code : prog)) : (list string)) (bconfig : bool) ((prog_intro_strictness code) : strictness_flag)) : ext_expr) (o : out)) ->
        (* ------------------------------------------ *)
        (red_expr (S0 : state) (C : execution_ctx) ((spec_binding_inst_8 (code : prog) (bconfig : bool) (L : env_loc)) : ext_expr) (o : out))

  | red_spec_make_arg_getter :
      forall (xbd : string) (bd : funcbody) (S : state (* input *)) (C : execution_ctx (* input *)) (x : prop_name (* input *)) (X : lexical_env (* input *)) (o : out),
        ((xbd : string) = ((("return ")%string) ++ ((x ++ (((";")%string) : prop_name)) : string))) ->
        ((bd : funcbody) = (funcbody_intro ((prog_intro (true : strictness_flag) (((element_stat ((stat_return ((Some (expr_identifier (x : string))) : (option expr))) : stat)) :: (nil : (list element))) : (list element))) : prog) (xbd : string))) ->
        (* ========================================== *)
        (red_expr (S : state) (C : execution_ctx) ((spec_creating_function_object (nil : (list string)) (bd : funcbody) (X : lexical_env) (true : strictness_flag)) : ext_expr) (o : out)) ->
        (* ------------------------------------------ *)
        (red_expr (S : state) (C : execution_ctx) ((spec_make_arg_getter (x : string) (X : lexical_env)) : ext_expr) (o : out))

  | red_spec_make_arg_setter :
      forall (xparam : string) (xbd : string) (bd : funcbody) (S : state (* input *)) (C : execution_ctx (* input *)) (x : prop_name (* input *)) (X : lexical_env (* input *)) (o : out),
        ((xparam : prop_name) = (x ++ ((("_arg")%string) : prop_name))) ->
        ((xbd : prop_name) = (x ++ ((((" = ")%string) ++ (((xparam : string) ++ ((";")%string)) : string)) : prop_name))) ->
        ((bd : funcbody) = (funcbody_intro ((prog_intro (true : strictness_flag) (((element_stat ((expr_assign ((expr_identifier (x : string)) : expr) (None : (option binary_op)) ((expr_identifier (xparam : string)) : expr)) : stat)) :: (nil : (list element))) : (list element))) : prog) (xbd : string))) ->
        (* ========================================== *)
        (red_expr (S : state) (C : execution_ctx) ((spec_creating_function_object ((xparam :: nil) : (list string)) (bd : funcbody) (X : lexical_env) (true : strictness_flag)) : ext_expr) (o : out)) ->
        (* ------------------------------------------ *)
        (red_expr (S : state) (C : execution_ctx) ((spec_make_arg_setter (x : string) (X : lexical_env)) : ext_expr) (o : out))

  | red_spec_object_get_args_obj :
      forall (lmap : object_loc) (S : state (* input *)) (C : execution_ctx (* input *)) (vthis : value (* input *)) (l : object_loc (* input *)) (x : prop_name (* input *)) (o : out) (y : (specret full_descriptor)),
        (object_method object_parameter_map_ S l (Some lmap)) ->
        (* ========================================== *)
        (red_spec S C (spec_object_get_own_prop (lmap : object_loc) (x : prop_name)) y) ->
        (red_expr (S : state) (C : execution_ctx) ((spec_args_obj_get_1 (vthis : value) (l : object_loc) (x : prop_name) (lmap : object_loc) (y : (specret full_descriptor))) : ext_expr) (o : out)) ->
        (* ------------------------------------------ *)
        (red_expr (S : state) (C : execution_ctx) ((spec_object_get_1 (builtin_get_args_obj : builtin_get) (vthis : value) (l : object_loc) (x : prop_name)) : ext_expr) (o : out))

  | red_spec_object_get_args_obj_1_undef :
      forall (S0 : state (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (vthis : value (* input *)) (l : object_loc (* input *)) (x : prop_name (* input *)) (lmap : object_loc (* input *)) (o : out),
        (* ========================================== *)
        (red_expr (S0 : state) (C : execution_ctx) ((spec_object_get_1 (builtin_get_function : builtin_get) (vthis : value) (l : object_loc) (x : prop_name)) : ext_expr) (o : out)) ->
        (* ------------------------------------------ *)
        (red_expr (S : state) (C : execution_ctx) ((spec_args_obj_get_1 (vthis : value) (l : object_loc) (x : prop_name) (lmap : object_loc) ((specret_val S0 full_descriptor_undef) : (specret full_descriptor))) : ext_expr) (o : out))

  | red_spec_object_get_args_obj_1_attrs :
      forall (S0 : state (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (vthis : value (* input *)) (l : object_loc (* input *)) (x : prop_name (* input *)) (lmap : object_loc (* input *)) (A : attributes (* input *)) (o : out),
        (* ========================================== *)
        (red_expr (S0 : state) (C : execution_ctx) ((spec_object_get ((value_object (lmap : object_loc)) : value) (x : prop_name)) : ext_expr) (o : out)) ->
        (* ------------------------------------------ *)
        (red_expr (S : state) (C : execution_ctx) ((spec_args_obj_get_1 (vthis : value) (l : object_loc) (x : prop_name) (lmap : object_loc) ((specret_val S0 (full_descriptor_some (A : attributes))) : (specret full_descriptor))) : ext_expr) (o : out))

  | red_spec_object_define_own_prop_args_obj :
      forall (lmap : object_loc) (S : state (* input *)) (C : execution_ctx (* input *)) (l : object_loc (* input *)) (x : prop_name (* input *)) (Desc : descriptor (* input *)) (throw : bool (* input *)) (o : out) (y : (specret full_descriptor)),
        (object_method object_parameter_map_ S l (Some lmap)) ->
        (* ========================================== *)
        (red_spec S C (spec_object_get_own_prop (lmap : object_loc) (x : prop_name)) y) ->
        (red_expr (S : state) (C : execution_ctx) ((spec_args_obj_define_own_prop_1 (l : object_loc) (x : prop_name) (Desc : descriptor) (throw : bool) (lmap : object_loc) (y : (specret full_descriptor))) : ext_expr) (o : out)) ->
        (* ------------------------------------------ *)
        (red_expr (S : state) (C : execution_ctx) ((spec_object_define_own_prop_1 (builtin_define_own_prop_args_obj : builtin_define_own_prop) (l : object_loc) (x : prop_name) (Desc : descriptor) (throw : bool)) : ext_expr) (o : out))

  | red_spec_object_define_own_prop_args_obj_1 :
      forall (o1 : out) (S0 : state (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (l : object_loc (* input *)) (x : prop_name (* input *)) (Desc : descriptor (* input *)) (throw : bool (* input *)) (lmap : object_loc (* input *)) (Dmap : full_descriptor (* input *)) (o : out),
        (* ========================================== *)
        (red_expr (S0 : state) (C : execution_ctx) ((spec_object_define_own_prop_1 (builtin_define_own_prop_default : builtin_define_own_prop) (l : object_loc) (x : prop_name) (Desc : descriptor) (false : bool)) : ext_expr) (o1 : out)) ->
        (red_expr (S0 : state) (C : execution_ctx) ((spec_args_obj_define_own_prop_2 (l : object_loc) (x : prop_name) (Desc : descriptor) (throw : bool) (lmap : object_loc) (Dmap : full_descriptor) (o1 : out)) : ext_expr) (o : out)) ->
        (* ------------------------------------------ *)
        (red_expr (S : state) (C : execution_ctx) ((spec_args_obj_define_own_prop_1 (l : object_loc) (x : prop_name) (Desc : descriptor) (throw : bool) (lmap : object_loc) ((specret_val S0 Dmap) : (specret full_descriptor))) : ext_expr) (o : out))

  | red_spec_object_define_own_prop_args_obj_2_false :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (l : object_loc (* input *)) (x : prop_name (* input *)) (Desc : descriptor (* input *)) (throw : bool (* input *)) (lmap : object_loc (* input *)) (Dmap : full_descriptor (* input *)) (S' : state (* input *)) (o : out),
        (* ========================================== *)
        (red_expr (S' : state) (C : execution_ctx) ((spec_object_define_own_prop_reject (throw : bool)) : ext_expr) (o : out)) ->
        (* ------------------------------------------ *)
        (red_expr (S : state) (C : execution_ctx) ((spec_args_obj_define_own_prop_2 (l : object_loc) (x : prop_name) (Desc : descriptor) (throw : bool) (lmap : object_loc) (Dmap : full_descriptor) ((out_ter (S' : state) (false : res)) : out)) : ext_expr) (o : out))

  | red_spec_object_define_own_prop_args_obj_2_true_acc :
      forall (o1 : out) (S : state (* input *)) (C : execution_ctx (* input *)) (l : object_loc (* input *)) (x : prop_name (* input *)) (Desc : descriptor (* input *)) (throw : bool (* input *)) (lmap : object_loc (* input *)) (A : attributes (* input *)) (S' : state (* input *)) (o : out),
        (descriptor_is_accessor (Desc : descriptor)) ->
        (* ========================================== *)
        (red_expr (S' : state) (C : execution_ctx) ((spec_object_delete (lmap : object_loc) (x : prop_name) (false : bool)) : ext_expr) (o1 : out)) ->
        (red_expr (S' : state) (C : execution_ctx) ((spec_args_obj_define_own_prop_5 (o1 : out)) : ext_expr) (o : out)) ->
        (* ------------------------------------------ *)
        (red_expr (S : state) (C : execution_ctx) ((spec_args_obj_define_own_prop_2 (l : object_loc) (x : prop_name) (Desc : descriptor) (throw : bool) (lmap : object_loc) ((full_descriptor_some (A : attributes)) : full_descriptor) ((out_ter (S' : state) (true : res)) : out)) : ext_expr) (o : out))

  | red_spec_object_define_own_prop_args_obj_2_true_not_acc_some :
      forall (v : value) (o1 : out) (S : state (* input *)) (C : execution_ctx (* input *)) (l : object_loc (* input *)) (x : prop_name (* input *)) (Desc : descriptor (* input *)) (throw : bool (* input *)) (lmap : object_loc (* input *)) (A : attributes (* input *)) (S' : state (* input *)) (o : out),
        (~ (descriptor_is_accessor (Desc : descriptor))) ->
        ((descriptor_value (Desc : descriptor)) = ((Some v) : (option value))) ->
        (* ========================================== *)
        (red_expr (S' : state) (C : execution_ctx) ((spec_object_put ((value_object (lmap : object_loc)) : value) (x : prop_name) (v : value) (throw : bool)) : ext_expr) (o1 : out)) ->
        (red_expr (S' : state) (C : execution_ctx) ((spec_args_obj_define_own_prop_3 (l : object_loc) (x : prop_name) (Desc : descriptor) (throw : bool) (lmap : object_loc) (o1 : out)) : ext_expr) (o : out)) ->
        (* ------------------------------------------ *)
        (red_expr (S : state) (C : execution_ctx) ((spec_args_obj_define_own_prop_2 (l : object_loc) (x : prop_name) (Desc : descriptor) (throw : bool) (lmap : object_loc) ((full_descriptor_some (A : attributes)) : full_descriptor) ((out_ter (S' : state) (true : res)) : out)) : ext_expr) (o : out))

  | red_spec_object_define_own_prop_args_obj_3 :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (l : object_loc (* input *)) (x : prop_name (* input *)) (Desc : descriptor (* input *)) (throw : bool (* input *)) (lmap : object_loc (* input *)) (S' : state (* input *)) (o : out),
        (* ========================================== *)
        (red_expr (S' : state) (C : execution_ctx) ((spec_args_obj_define_own_prop_4 (l : object_loc) (x : prop_name) (Desc : descriptor) (throw : bool) (lmap : object_loc)) : ext_expr) (o : out)) ->
        (* ------------------------------------------ *)
        (red_expr (S : state) (C : execution_ctx) ((spec_args_obj_define_own_prop_3 (l : object_loc) (x : prop_name) (Desc : descriptor) (throw : bool) (lmap : object_loc) ((out_ter (S' : state) (res_intro restype_normal resvalue_empty label_empty)) : out)) : ext_expr) (o : out))

  | red_spec_object_define_own_prop_args_obj_2_true_not_acc_none :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (l : object_loc (* input *)) (x : prop_name (* input *)) (Desc : descriptor (* input *)) (throw : bool (* input *)) (lmap : object_loc (* input *)) (A : attributes (* input *)) (S' : state (* input *)) (o : out),
        (~ (descriptor_is_accessor (Desc : descriptor))) ->
        ((descriptor_value (Desc : descriptor)) = (None : (option value))) ->
        (* ========================================== *)
        (red_expr (S' : state) (C : execution_ctx) ((spec_args_obj_define_own_prop_4 (l : object_loc) (x : prop_name) (Desc : descriptor) (throw : bool) (lmap : object_loc)) : ext_expr) (o : out)) ->
        (* ------------------------------------------ *)
        (red_expr (S : state) (C : execution_ctx) ((spec_args_obj_define_own_prop_2 (l : object_loc) (x : prop_name) (Desc : descriptor) (throw : bool) (lmap : object_loc) ((full_descriptor_some (A : attributes)) : full_descriptor) ((out_ter (S' : state) (true : res)) : out)) : ext_expr) (o : out))

  | red_spec_object_define_own_prop_args_obj_4_false :
      forall (o1 : out) (S : state (* input *)) (C : execution_ctx (* input *)) (l : object_loc (* input *)) (x : prop_name (* input *)) (Desc : descriptor (* input *)) (throw : bool (* input *)) (lmap : object_loc (* input *)) (o : out),
        ((descriptor_writable (Desc : descriptor)) = ((Some false) : (option bool))) ->
        (* ========================================== *)
        (red_expr (S : state) (C : execution_ctx) ((spec_object_delete (lmap : object_loc) (x : prop_name) (false : bool)) : ext_expr) (o1 : out)) ->
        (red_expr (S : state) (C : execution_ctx) ((spec_args_obj_define_own_prop_5 (o1 : out)) : ext_expr) (o : out)) ->
        (* ------------------------------------------ *)
        (red_expr (S : state) (C : execution_ctx) ((spec_args_obj_define_own_prop_4 (l : object_loc) (x : prop_name) (Desc : descriptor) (throw : bool) (lmap : object_loc)) : ext_expr) (o : out))

  | red_spec_object_define_own_prop_args_obj_5 :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (S' : state (* input *)) (b : bool (* input *)) (o : out),
        (* ========================================== *)
        (red_expr (S' : state) (C : execution_ctx) (spec_args_obj_define_own_prop_6 : ext_expr) (o : out)) ->
        (* ------------------------------------------ *)
        (red_expr (S : state) (C : execution_ctx) ((spec_args_obj_define_own_prop_5 ((out_ter (S' : state) (b : res)) : out)) : ext_expr) (o : out))

  | red_spec_object_define_own_prop_args_obj_4_not_false :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (l : object_loc (* input *)) (x : prop_name (* input *)) (Desc : descriptor (* input *)) (throw : bool (* input *)) (lmap : object_loc (* input *)) (o : out),
        ((descriptor_writable (Desc : descriptor)) <> ((Some false) : (option bool))) ->
        (* ========================================== *)
        (red_expr (S : state) (C : execution_ctx) (spec_args_obj_define_own_prop_6 : ext_expr) (o : out)) ->
        (* ------------------------------------------ *)
        (red_expr (S : state) (C : execution_ctx) ((spec_args_obj_define_own_prop_4 (l : object_loc) (x : prop_name) (Desc : descriptor) (throw : bool) (lmap : object_loc)) : ext_expr) (o : out))

  | red_spec_object_define_own_prop_args_obj_2_true_undef :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (l : object_loc (* input *)) (x : prop_name (* input *)) (Desc : descriptor (* input *)) (throw : bool (* input *)) (lmap : object_loc (* input *)) (S' : state (* input *)) (o : out),
        (* ========================================== *)
        (red_expr (S' : state) (C : execution_ctx) (spec_args_obj_define_own_prop_6 : ext_expr) (o : out)) ->
        (* ------------------------------------------ *)
        (red_expr (S : state) (C : execution_ctx) ((spec_args_obj_define_own_prop_2 (l : object_loc) (x : prop_name) (Desc : descriptor) (throw : bool) (lmap : object_loc) (full_descriptor_undef : full_descriptor) ((out_ter (S' : state) (true : res)) : out)) : ext_expr) (o : out))

  | red_spec_object_define_own_prop_args_obj_6 :
      forall (S : state (* input *)) (C : execution_ctx (* input *)),
        (* ========================================== *)
        (* ------------------------------------------ *)
        (red_expr (S : state) (C : execution_ctx) (spec_args_obj_define_own_prop_6 : ext_expr) ((out_ter (S : state) (true : res)) : out))

  | red_spec_object_delete_args_obj :
      forall (lmap : object_loc) (S : state (* input *)) (C : execution_ctx (* input *)) (l : object_loc (* input *)) (x : prop_name (* input *)) (throw : bool (* input *)) (o : out) (y : (specret full_descriptor)),
        (object_method object_parameter_map_ S l (Some lmap)) ->
        (* ========================================== *)
        (red_spec S C (spec_object_get_own_prop (lmap : object_loc) (x : prop_name)) y) ->
        (red_expr (S : state) (C : execution_ctx) ((spec_args_obj_delete_1 (l : object_loc) (x : prop_name) (throw : bool) (lmap : object_loc) (y : (specret full_descriptor))) : ext_expr) (o : out)) ->
        (* ------------------------------------------ *)
        (red_expr (S : state) (C : execution_ctx) ((spec_object_delete_1 (builtin_delete_args_obj : builtin_delete) (l : object_loc) (x : prop_name) (throw : bool)) : ext_expr) (o : out))

  | red_spec_object_delete_args_obj_1 :
      forall (o1 : out) (S0 : state (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (l : object_loc (* input *)) (x : prop_name (* input *)) (throw : bool (* input *)) (lmap : object_loc (* input *)) (D : full_descriptor (* input *)) (o : out),
        (* ========================================== *)
        (red_expr (S0 : state) (C : execution_ctx) ((spec_object_delete_1 (builtin_delete_default : builtin_delete) (l : object_loc) (x : prop_name) (throw : bool)) : ext_expr) (o1 : out)) ->
        (red_expr (S0 : state) (C : execution_ctx) ((spec_args_obj_delete_2 (l : object_loc) (x : prop_name) (throw : bool) (lmap : object_loc) (D : full_descriptor) (o1 : out)) : ext_expr) (o : out)) ->
        (* ------------------------------------------ *)
        (red_expr (S : state) (C : execution_ctx) ((spec_args_obj_delete_1 (l : object_loc) (x : prop_name) (throw : bool) (lmap : object_loc) ((specret_val S0 D) : (specret full_descriptor))) : ext_expr) (o : out))

  | red_spec_object_delete_args_obj_2_if :
      forall (o1 : out) (S : state (* input *)) (C : execution_ctx (* input *)) (l : object_loc (* input *)) (x : prop_name (* input *)) (throw : bool (* input *)) (lmap : object_loc (* input *)) (A : attributes (* input *)) (S' : state (* input *)) (o : out),
        (* ========================================== *)
        (red_expr (S' : state) (C : execution_ctx) ((spec_object_delete (lmap : object_loc) (x : prop_name) (false : bool)) : ext_expr) (o1 : out)) ->
        (red_expr (S' : state) (C : execution_ctx) ((spec_args_obj_delete_3 (o1 : out)) : ext_expr) (o : out)) ->
        (* ------------------------------------------ *)
        (red_expr (S : state) (C : execution_ctx) ((spec_args_obj_delete_2 (l : object_loc) (x : prop_name) (throw : bool) (lmap : object_loc) ((full_descriptor_some (A : attributes)) : full_descriptor) ((out_ter (S' : state) (true : res)) : out)) : ext_expr) (o : out))

  | red_spec_object_delete_args_obj_3 :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (S' : state (* input *)) (b : bool (* input *)) (o : out),
        (* ========================================== *)
        (red_expr (S' : state) (C : execution_ctx) ((spec_args_obj_delete_4 (true : bool)) : ext_expr) (o : out)) ->
        (* ------------------------------------------ *)
        (red_expr (S : state) (C : execution_ctx) ((spec_args_obj_delete_3 ((out_ter (S' : state) (b : res)) : out)) : ext_expr) (o : out))

  | red_spec_object_delete_args_obj_2_else :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (l : object_loc (* input *)) (x : prop_name (* input *)) (throw : bool (* input *)) (lmap : object_loc (* input *)) (D : full_descriptor (* input *)) (S' : state (* input *)) (b : bool (* input *)) (o : out),
        (((b = false) : Prop) \/ ((D = full_descriptor_undef) : Prop)) ->
        (* ========================================== *)
        (red_expr (S' : state) (C : execution_ctx) ((spec_args_obj_delete_4 (b : bool)) : ext_expr) (o : out)) ->
        (* ------------------------------------------ *)
        (red_expr (S : state) (C : execution_ctx) ((spec_args_obj_delete_2 (l : object_loc) (x : prop_name) (throw : bool) (lmap : object_loc) (D : full_descriptor) ((out_ter (S' : state) (b : res)) : out)) : ext_expr) (o : out))

  | red_spec_object_delete_args_obj_4 :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (b : bool (* input *)),
        (* ========================================== *)
        (* ------------------------------------------ *)
        (red_expr (S : state) (C : execution_ctx) ((spec_args_obj_delete_4 (b : bool)) : ext_expr) ((out_ter (S : state) (b : res)) : out))

  | red_spec_arguments_object_map :
      forall (o1 : out) (S : state (* input *)) (C : execution_ctx (* input *)) (l : object_loc (* input *)) (xs : (list prop_name) (* input *)) (args : (list value) (* input *)) (X : lexical_env (* input *)) (str : strictness_flag (* input *)) (o : out),
        (* ========================================== *)
        (red_expr (S : state) (C : execution_ctx) ((spec_construct_prealloc (prealloc_object : prealloc) (nil : (list value))) : ext_expr) (o1 : out)) ->
        (red_expr (S : state) (C : execution_ctx) ((spec_arguments_object_map_1 (l : object_loc) (xs : (list string)) (args : (list value)) (X : lexical_env) (str : strictness_flag) (o1 : out)) : ext_expr) (o : out)) ->
        (* ------------------------------------------ *)
        (red_expr (S : state) (C : execution_ctx) ((spec_arguments_object_map (l : object_loc) (xs : (list string)) (args : (list value)) (X : lexical_env) (str : strictness_flag)) : ext_expr) (o : out))

  | red_spec_arguments_object_map_1 :
      forall (S' : state (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (l : object_loc (* input *)) (xs : (list prop_name) (* input *)) (args : (list value) (* input *)) (X : lexical_env (* input *)) (str : strictness_flag (* input *)) (lmap : object_loc (* input *)) (o : out),
        (* ========================================== *)
        (red_expr (S' : state) (C : execution_ctx) ((spec_arguments_object_map_2 (l : object_loc) (xs : (list string)) (args : (list value)) (X : lexical_env) (str : strictness_flag) (lmap : object_loc) (nil : (list string)) (((length args) - ((1%nat) : nat)) : int)) : ext_expr) (o : out)) ->
        (* ------------------------------------------ *)
        (red_expr (S : state) (C : execution_ctx) ((spec_arguments_object_map_1 (l : object_loc) (xs : (list string)) (args : (list value)) (X : lexical_env) (str : strictness_flag) ((out_ter (S' : state) (lmap : res)) : out)) : ext_expr) (o : out))

  | red_spec_arguments_object_map_2_negative :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (l : object_loc (* input *)) (xs : (list prop_name) (* input *)) (args : (list value) (* input *)) (X : lexical_env (* input *)) (str : strictness_flag (* input *)) (lmap : object_loc (* input *)) (xsmap : (list string) (* input *)) (k : int (* input *)) (o : out),
        (k < ((0%nat) : int)) ->
        (* ========================================== *)
        (red_expr (S : state) (C : execution_ctx) ((spec_arguments_object_map_8 (l : object_loc) (lmap : object_loc) (xsmap : (list string))) : ext_expr) (o : out)) ->
        (* ------------------------------------------ *)
        (red_expr (S : state) (C : execution_ctx) ((spec_arguments_object_map_2 (l : object_loc) (xs : (list string)) (args : (list value)) (X : lexical_env) (str : strictness_flag) (lmap : object_loc) (xsmap : (list string)) (k : int)) : ext_expr) (o : out))

  | red_spec_arguments_object_map_2_positive :
      forall (A : attributes) (o1 : out) (S : state (* input *)) (C : execution_ctx (* input *)) (l : object_loc (* input *)) (xs : (list prop_name) (* input *)) (args : (list value) (* input *)) (X : lexical_env (* input *)) (str : strictness_flag (* input *)) (lmap : object_loc (* input *)) (xsmap : (list string) (* input *)) (k : int (* input *)) (v : value) (o : out),
        (ZNth k args v) ->
        (A = ((attributes_data_intro_all_true (v : value)) : attributes)) ->
        (* ========================================== *)
        (red_expr (S : state) (C : execution_ctx) ((spec_object_define_own_prop (l : object_loc) ((convert_prim_to_string (k : prim)) : prop_name) (A : descriptor) (false : bool)) : ext_expr) (o1 : out)) ->
        (red_expr (S : state) (C : execution_ctx) ((spec_arguments_object_map_3 (l : object_loc) (xs : (list string)) (args : (list value)) (X : lexical_env) (str : strictness_flag) (lmap : object_loc) (xsmap : (list string)) (k : int) (o1 : out)) : ext_expr) (o : out)) ->
        (* ------------------------------------------ *)
        (red_expr (S : state) (C : execution_ctx) ((spec_arguments_object_map_2 (l : object_loc) (xs : (list string)) (args : (list value)) (X : lexical_env) (str : strictness_flag) (lmap : object_loc) (xsmap : (list string)) (k : int)) : ext_expr) (o : out))

  | red_spec_arguments_object_map_3_next :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (l : object_loc (* input *)) (xs : (list prop_name) (* input *)) (args : (list value) (* input *)) (X : lexical_env (* input *)) (str : strictness_flag (* input *)) (lmap : object_loc (* input *)) (xsmap : (list string) (* input *)) (k : int (* input *)) (S' : state (* input *)) (b : bool (* input *)) (o : out),
        (k >= ((length xs) : int)) ->
        (* ========================================== *)
        (red_expr (S' : state) (C : execution_ctx) ((spec_arguments_object_map_2 (l : object_loc) (xs : (list string)) (args : (list value)) (X : lexical_env) (str : strictness_flag) (lmap : object_loc) (xsmap : (list string)) ((k - ((1%nat) : int)) : int)) : ext_expr) (o : out)) ->
        (* ------------------------------------------ *)
        (red_expr (S : state) (C : execution_ctx) ((spec_arguments_object_map_3 (l : object_loc) (xs : (list string)) (args : (list value)) (X : lexical_env) (str : strictness_flag) (lmap : object_loc) (xsmap : (list string)) (k : int) ((out_ter (S' : state) (b : res)) : out)) : ext_expr) (o : out))

  | red_spec_arguments_object_map_3_cont_next :
      forall (x : prop_name) (S : state (* input *)) (C : execution_ctx (* input *)) (l : object_loc (* input *)) (xs : (list prop_name) (* input *)) (args : (list value) (* input *)) (X : lexical_env (* input *)) (str : strictness_flag (* input *)) (lmap : object_loc (* input *)) (xsmap : (list string) (* input *)) (k : int (* input *)) (S' : state (* input *)) (b : bool (* input *)) (o : out),
        (ZNth k xs x) ->
        (((str = true) : Prop) \/ ((Mem x xsmap) : Prop)) ->
        (* ========================================== *)
        (red_expr (S' : state) (C : execution_ctx) ((spec_arguments_object_map_2 (l : object_loc) (xs : (list string)) (args : (list value)) (X : lexical_env) (str : strictness_flag) (lmap : object_loc) (xsmap : (list string)) ((k - ((1%nat) : int)) : int)) : ext_expr) (o : out)) ->
        (* ------------------------------------------ *)
        (red_expr (S : state) (C : execution_ctx) ((spec_arguments_object_map_3 (l : object_loc) (xs : (list string)) (args : (list value)) (X : lexical_env) (str : strictness_flag) (lmap : object_loc) (xsmap : (list string)) (k : int) ((out_ter (S' : state) (b : res)) : out)) : ext_expr) (o : out))

  | red_spec_arguments_object_map_3_cont_cont :
      forall (x : prop_name) (S : state (* input *)) (C : execution_ctx (* input *)) (l : object_loc (* input *)) (xs : (list prop_name) (* input *)) (args : (list value) (* input *)) (X : lexical_env (* input *)) (str : strictness_flag (* input *)) (lmap : object_loc (* input *)) (xsmap : (list string) (* input *)) (k : int (* input *)) (S' : state (* input *)) (b : bool (* input *)) (o : out),
        (ZNth k xs x) ->
        (((str = false) : Prop) /\ ((~ (Mem x xsmap)) : Prop)) ->
        (* ========================================== *)
        (red_expr (S' : state) (C : execution_ctx) ((spec_arguments_object_map_4 (l : object_loc) (xs : (list string)) (args : (list value)) (X : lexical_env) (str : strictness_flag) (lmap : object_loc) (xsmap : (list string)) (k : int) (x : string)) : ext_expr) (o : out)) ->
        (* ------------------------------------------ *)
        (red_expr (S : state) (C : execution_ctx) ((spec_arguments_object_map_3 (l : object_loc) (xs : (list string)) (args : (list value)) (X : lexical_env) (str : strictness_flag) (lmap : object_loc) (xsmap : (list string)) (k : int) ((out_ter (S' : state) (b : res)) : out)) : ext_expr) (o : out))

  | red_spec_arguments_object_map_4 :
      forall (o1 : out) (S : state (* input *)) (C : execution_ctx (* input *)) (l : object_loc (* input *)) (xs : (list prop_name) (* input *)) (args : (list value) (* input *)) (X : lexical_env (* input *)) (str : strictness_flag (* input *)) (lmap : object_loc (* input *)) (xsmap : (list string) (* input *)) (k : int (* input *)) (x : prop_name (* input *)) (o : out),
        (* ========================================== *)
        (red_expr (S : state) (C : execution_ctx) ((spec_make_arg_getter (x : string) (X : lexical_env)) : ext_expr) (o1 : out)) ->
        (red_expr (S : state) (C : execution_ctx) ((spec_arguments_object_map_5 (l : object_loc) (xs : (list string)) (args : (list value)) (X : lexical_env) (str : strictness_flag) (lmap : object_loc) ((x :: (xsmap : (list prop_name))) : (list string)) (k : int) (x : string) (o1 : out)) : ext_expr) (o : out)) ->
        (* ------------------------------------------ *)
        (red_expr (S : state) (C : execution_ctx) ((spec_arguments_object_map_4 (l : object_loc) (xs : (list string)) (args : (list value)) (X : lexical_env) (str : strictness_flag) (lmap : object_loc) (xsmap : (list string)) (k : int) (x : string)) : ext_expr) (o : out))

  | red_spec_arguments_object_map_5 :
      forall (o1 : out) (S : state (* input *)) (C : execution_ctx (* input *)) (l : object_loc (* input *)) (xs : (list prop_name) (* input *)) (args : (list value) (* input *)) (X : lexical_env (* input *)) (str : strictness_flag (* input *)) (lmap : object_loc (* input *)) (xsmap : (list string) (* input *)) (k : int (* input *)) (x : prop_name (* input *)) (S' : state (* input *)) (lgetter : object_loc (* input *)) (o : out),
        (* ========================================== *)
        (red_expr (S' : state) (C : execution_ctx) ((spec_make_arg_setter (x : string) (X : lexical_env)) : ext_expr) (o1 : out)) ->
        (red_expr (S' : state) (C : execution_ctx) ((spec_arguments_object_map_6 (l : object_loc) (xs : (list string)) (args : (list value)) (X : lexical_env) (str : strictness_flag) (lmap : object_loc) (xsmap : (list string)) (k : int) (lgetter : object_loc) (o1 : out)) : ext_expr) (o : out)) ->
        (* ------------------------------------------ *)
        (red_expr (S : state) (C : execution_ctx) ((spec_arguments_object_map_5 (l : object_loc) (xs : (list string)) (args : (list value)) (X : lexical_env) (str : strictness_flag) (lmap : object_loc) (xsmap : (list string)) (k : int) (x : string) ((out_ter (S' : state) (lgetter : res)) : out)) : ext_expr) (o : out))

  | red_spec_arguments_object_map_6 :
      forall (A : attributes) (o1 : out) (S : state (* input *)) (C : execution_ctx (* input *)) (l : object_loc (* input *)) (xs : (list prop_name) (* input *)) (args : (list value) (* input *)) (X : lexical_env (* input *)) (str : strictness_flag (* input *)) (lmap : object_loc (* input *)) (xsmap : (list string) (* input *)) (k : int (* input *)) (lgetter : object_loc (* input *)) (S' : state (* input *)) (lsetter : object_loc (* input *)) (o : out),
        (A = ((attributes_accessor_intro ((value_object (lgetter : object_loc)) : value) ((value_object (lsetter : object_loc)) : value) (false : bool) (true : bool)) : attributes)) ->
        (* ========================================== *)
        (red_expr (S' : state) (C : execution_ctx) ((spec_object_define_own_prop (lmap : object_loc) ((convert_prim_to_string (k : prim)) : prop_name) (A : descriptor) (false : bool)) : ext_expr) (o1 : out)) ->
        (red_expr (S' : state) (C : execution_ctx) ((spec_arguments_object_map_7 (l : object_loc) (xs : (list string)) (args : (list value)) (X : lexical_env) (str : strictness_flag) (lmap : object_loc) (xsmap : (list string)) (k : int) (o1 : out)) : ext_expr) (o : out)) ->
        (* ------------------------------------------ *)
        (red_expr (S : state) (C : execution_ctx) ((spec_arguments_object_map_6 (l : object_loc) (xs : (list string)) (args : (list value)) (X : lexical_env) (str : strictness_flag) (lmap : object_loc) (xsmap : (list string)) (k : int) (lgetter : object_loc) ((out_ter (S' : state) (lsetter : res)) : out)) : ext_expr) (o : out))

  | red_spec_arguments_object_map_7 :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (l : object_loc (* input *)) (xs : (list prop_name) (* input *)) (args : (list value) (* input *)) (X : lexical_env (* input *)) (str : strictness_flag (* input *)) (lmap : object_loc (* input *)) (xsmap : (list string) (* input *)) (k : int (* input *)) (S' : state (* input *)) (b : bool (* input *)) (o : out),
        (* ========================================== *)
        (red_expr (S' : state) (C : execution_ctx) ((spec_arguments_object_map_2 (l : object_loc) (xs : (list string)) (args : (list value)) (X : lexical_env) (str : strictness_flag) (lmap : object_loc) (xsmap : (list string)) ((k - ((1%nat) : int)) : int)) : ext_expr) (o : out)) ->
        (* ------------------------------------------ *)
        (red_expr (S : state) (C : execution_ctx) ((spec_arguments_object_map_7 (l : object_loc) (xs : (list string)) (args : (list value)) (X : lexical_env) (str : strictness_flag) (lmap : object_loc) (xsmap : (list string)) (k : int) ((out_ter (S' : state) (b : res)) : out)) : ext_expr) (o : out))

  | red_spec_arguments_object_map_8_cons :
      forall (O : object) (O' : object) (S : state (* input *)) (C : execution_ctx (* input *)) (l : object_loc (* input *)) (lmap : object_loc (* input *)) (xsmap : (list string) (* input *)) (S' : state),
        (xsmap <> nil) ->
        (object_binds (S : state) (l : object_loc) (O : object)) ->
        (O' = ((object_for_args_object O lmap builtin_get_args_obj builtin_get_own_prop_args_obj builtin_define_own_prop_args_obj builtin_delete_args_obj) : object)) ->
        (S' = ((object_write S l O') : state)) ->
        (* ========================================== *)
        (* ------------------------------------------ *)
        (red_expr (S : state) (C : execution_ctx) ((spec_arguments_object_map_8 (l : object_loc) (lmap : object_loc) (xsmap : (list string))) : ext_expr) ((out_void (S' : state)) : out))

  | red_spec_arguments_object_map_8_nil :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (l : object_loc (* input *)) (lmap : object_loc (* input *)),
        (* ========================================== *)
        (* ------------------------------------------ *)
        (red_expr (S : state) (C : execution_ctx) ((spec_arguments_object_map_8 (l : object_loc) (lmap : object_loc) (nil : (list string))) : ext_expr) ((out_void (S : state)) : out))

  | red_spec_create_arguments_object :
      forall (O : object) (l : object_loc) (S' : state) (A : attributes) (o1 : out) (S : state (* input *)) (C : execution_ctx (* input *)) (lf : object_loc (* input *)) (xs : (list prop_name) (* input *)) (args : (list value) (* input *)) (X : lexical_env (* input *)) (str : strictness_flag (* input *)) (o : out),
        (O = ((object_new prealloc_object_proto (("Arguments")%string)) : object)) ->
        ((l, S') = ((object_alloc S O) : (object_loc * state))) ->
        (A = ((attributes_data_intro ((JsNumber.of_int (length args)) : value) (true : bool) (false : bool) (true : bool)) : attributes)) ->
        (* ========================================== *)
        (red_expr (S' : state) (C : execution_ctx) ((spec_object_define_own_prop (l : object_loc) ((("length")%string) : prop_name) (A : descriptor) (false : bool)) : ext_expr) (o1 : out)) ->
        (red_expr (S' : state) (C : execution_ctx) ((spec_create_arguments_object_1 (lf : object_loc) (xs : (list string)) (args : (list value)) (X : lexical_env) (str : strictness_flag) (l : object_loc) (o1 : out)) : ext_expr) (o : out)) ->
        (* ------------------------------------------ *)
        (red_expr (S : state) (C : execution_ctx) ((spec_create_arguments_object (lf : object_loc) (xs : (list string)) (args : (list value)) (X : lexical_env) (str : strictness_flag)) : ext_expr) (o : out))

  | red_spec_create_arguments_object_1 :
      forall (o1 : out) (S : state (* input *)) (C : execution_ctx (* input *)) (lf : object_loc (* input *)) (xs : (list prop_name) (* input *)) (args : (list value) (* input *)) (X : lexical_env (* input *)) (str : strictness_flag (* input *)) (l : object_loc (* input *)) (S' : state (* input *)) (b : bool (* input *)) (o : out),
        (* ========================================== *)
        (red_expr (S' : state) (C : execution_ctx) ((spec_arguments_object_map (l : object_loc) (xs : (list string)) (args : (list value)) (X : lexical_env) (str : strictness_flag)) : ext_expr) (o1 : out)) ->
        (red_expr (S' : state) (C : execution_ctx) ((spec_create_arguments_object_2 (lf : object_loc) (str : strictness_flag) (l : object_loc) (o1 : out)) : ext_expr) (o : out)) ->
        (* ------------------------------------------ *)
        (red_expr (S : state) (C : execution_ctx) ((spec_create_arguments_object_1 (lf : object_loc) (xs : (list string)) (args : (list value)) (X : lexical_env) (str : strictness_flag) (l : object_loc) ((out_ter (S' : state) (b : res)) : out)) : ext_expr) (o : out))

  | red_spec_create_arguments_object_2_non_strict :
      forall (A : attributes) (o1 : out) (S : state (* input *)) (C : execution_ctx (* input *)) (lf : object_loc (* input *)) (l : object_loc (* input *)) (S' : state (* input *)) (o : out),
        (A = ((attributes_data_intro ((value_object (lf : object_loc)) : value) (true : bool) (false : bool) (true : bool)) : attributes)) ->
        (* ========================================== *)
        (red_expr (S' : state) (C : execution_ctx) ((spec_object_define_own_prop (l : object_loc) ((("callee")%string) : prop_name) (A : descriptor) (false : bool)) : ext_expr) (o1 : out)) ->
        (red_expr (S' : state) (C : execution_ctx) ((spec_create_arguments_object_4 (l : object_loc) (o1 : out)) : ext_expr) (o : out)) ->
        (* ------------------------------------------ *)
        (red_expr (S : state) (C : execution_ctx) ((spec_create_arguments_object_2 (lf : object_loc) (false : strictness_flag) (l : object_loc) ((out_ter (S' : state) (res_intro restype_normal resvalue_empty label_empty)) : out)) : ext_expr) (o : out))

  | red_spec_create_arguments_object_2_strict :
      forall (vthrower : value) (A : attributes) (o1 : out) (S : state (* input *)) (C : execution_ctx (* input *)) (lf : object_loc (* input *)) (l : object_loc (* input *)) (S' : state (* input *)) (o : out),
        ((vthrower : value) = (value_object (prealloc_throw_type_error : object_loc))) ->
        (A = ((attributes_accessor_intro (vthrower : value) (vthrower : value) (false : bool) (false : bool)) : attributes)) ->
        (* ========================================== *)
        (red_expr (S' : state) (C : execution_ctx) ((spec_object_define_own_prop (l : object_loc) ((("caller")%string) : prop_name) (A : descriptor) (false : bool)) : ext_expr) (o1 : out)) ->
        (red_expr (S' : state) (C : execution_ctx) ((spec_create_arguments_object_3 (l : object_loc) (vthrower : value) (A : attributes) (o1 : out)) : ext_expr) (o : out)) ->
        (* ------------------------------------------ *)
        (red_expr (S : state) (C : execution_ctx) ((spec_create_arguments_object_2 (lf : object_loc) (true : strictness_flag) (l : object_loc) ((out_ter (S' : state) (res_intro restype_normal resvalue_empty label_empty)) : out)) : ext_expr) (o : out))

  | red_spec_create_arguments_object_3 :
      forall (o1 : out) (S : state (* input *)) (C : execution_ctx (* input *)) (l : object_loc (* input *)) (vthrower : value (* input *)) (A : attributes (* input *)) (S' : state (* input *)) (b : bool (* input *)) (o : out),
        (* ========================================== *)
        (red_expr (S' : state) (C : execution_ctx) ((spec_object_define_own_prop (l : object_loc) ((("callee")%string) : prop_name) (A : descriptor) (false : bool)) : ext_expr) (o1 : out)) ->
        (red_expr (S' : state) (C : execution_ctx) ((spec_create_arguments_object_4 (l : object_loc) (o1 : out)) : ext_expr) (o : out)) ->
        (* ------------------------------------------ *)
        (red_expr (S : state) (C : execution_ctx) ((spec_create_arguments_object_3 (l : object_loc) (vthrower : value) (A : attributes) ((out_ter (S' : state) (b : res)) : out)) : ext_expr) (o : out))

  | red_spec_create_arguments_object_4 :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (l : object_loc (* input *)) (S' : state (* input *)) (b : bool (* input *)),
        (* ========================================== *)
        (* ------------------------------------------ *)
        (red_expr (S : state) (C : execution_ctx) ((spec_create_arguments_object_4 (l : object_loc) ((out_ter (S' : state) (b : res)) : out)) : ext_expr) ((out_ter (S' : state) (l : res)) : out))

  | red_spec_creating_function_object_proto :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (l : object_loc (* input *)) (o1 : out) (o : out),
        (* ========================================== *)
        (red_expr (S : state) (C : execution_ctx) ((spec_construct_prealloc (prealloc_object : prealloc) (nil : (list value))) : ext_expr) (o1 : out)) ->
        (red_expr (S : state) (C : execution_ctx) ((spec_creating_function_object_proto_1 (l : object_loc) (o1 : out)) : ext_expr) (o : out)) ->
        (* ------------------------------------------ *)
        (red_expr (S : state) (C : execution_ctx) ((spec_creating_function_object_proto (l : object_loc)) : ext_expr) (o : out))

  | red_spec_creating_function_object_proto_1 :
      forall (S0 : state (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (l : object_loc (* input *)) (lproto : object_loc (* input *)) (o1 : out) (o : out),
        let A : attributes_data := (attributes_data_intro ((value_object (l : object_loc)) : value) (true : bool) (false : bool) (true : bool)) in
        (* ========================================== *)
        (red_expr (S : state) (C : execution_ctx) ((spec_object_define_own_prop (lproto : object_loc) ((("constructor")%string) : prop_name) (A : descriptor) (false : bool)) : ext_expr) (o1 : out)) ->
        (red_expr (S : state) (C : execution_ctx) ((spec_creating_function_object_proto_2 (l : object_loc) (lproto : object_loc) (o1 : out)) : ext_expr) (o : out)) ->
        (* ------------------------------------------ *)
        (red_expr (S0 : state) (C : execution_ctx) ((spec_creating_function_object_proto_1 (l : object_loc) ((out_ter (S : state) (lproto : res)) : out)) : ext_expr) (o : out))

  | red_spec_creating_function_object_proto_2 :
      forall (S0 : state (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (l : object_loc (* input *)) (lproto : object_loc (* input *)) (b : bool (* input *)) (o : out),
        let A : attributes_data := (attributes_data_intro ((value_object (lproto : object_loc)) : value) (true : bool) (false : bool) (false : bool)) in
        (* ========================================== *)
        (red_expr (S : state) (C : execution_ctx) ((spec_object_define_own_prop (l : object_loc) ((("prototype")%string) : prop_name) (A : descriptor) (false : bool)) : ext_expr) (o : out)) ->
        (* ------------------------------------------ *)
        (red_expr (S0 : state) (C : execution_ctx) ((spec_creating_function_object_proto_2 (l : object_loc) (lproto : object_loc) ((out_ter (S : state) (b : res)) : out)) : ext_expr) (o : out))

  | red_spec_creating_function_object :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (S' : state) (O : object) (O1 : object) (O2 : object) (O3 : object) (A : attributes) (l : object_loc) (names : (list string) (* input *)) (bd : funcbody (* input *)) (X : lexical_env (* input *)) (str : strictness_flag (* input *)) (o1 : out) (o : out),
        (O = ((object_new prealloc_function_proto (("Function")%string)) : object)) ->
        (O1 = ((object_with_get O builtin_get_function) : object)) ->
        (O2 = ((object_with_invokation O1 (Some construct_default) (Some call_default) (Some builtin_has_instance_function)) : object)) ->
        (O3 = ((object_with_details O2 (Some X) (Some names) (Some bd) None None None None) : object)) ->
        ((l, S') = ((object_alloc S O3) : (object_loc * state))) ->
        (A = ((attributes_data_intro ((JsNumber.of_int (length names)) : value) (false : bool) (false : bool) (false : bool)) : attributes)) ->
        (* ========================================== *)
        (red_expr (S' : state) (C : execution_ctx) ((spec_object_define_own_prop (l : object_loc) ((("length")%string) : prop_name) (A : descriptor) (false : bool)) : ext_expr) (o1 : out)) ->
        (red_expr (S' : state) (C : execution_ctx) ((spec_creating_function_object_1 (str : strictness_flag) (l : object_loc) (o1 : out)) : ext_expr) (o : out)) ->
        (* ------------------------------------------ *)
        (red_expr (S : state) (C : execution_ctx) ((spec_creating_function_object (names : (list string)) (bd : funcbody) (X : lexical_env) (str : strictness_flag)) : ext_expr) (o : out))

  | red_spec_creating_function_object_1 :
      forall (S0 : state (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (str : strictness_flag (* input *)) (l : object_loc (* input *)) (b : bool (* input *)) (o1 : out) (o : out),
        (* ========================================== *)
        (red_expr (S : state) (C : execution_ctx) ((spec_creating_function_object_proto (l : object_loc)) : ext_expr) (o1 : out)) ->
        (red_expr (S : state) (C : execution_ctx) ((spec_creating_function_object_2 (str : strictness_flag) (l : object_loc) (o1 : out)) : ext_expr) (o : out)) ->
        (* ------------------------------------------ *)
        (red_expr (S0 : state) (C : execution_ctx) ((spec_creating_function_object_1 (str : strictness_flag) (l : object_loc) ((out_ter (S : state) (b : res)) : out)) : ext_expr) (o : out))

  | red_spec_creating_function_object_2_not_strict :
      forall (S0 : state (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (l : object_loc (* input *)) (b : bool (* input *)),
        (* ========================================== *)
        (* ------------------------------------------ *)
        (red_expr (S0 : state) (C : execution_ctx) ((spec_creating_function_object_2 (false : strictness_flag) (l : object_loc) ((out_ter (S : state) (b : res)) : out)) : ext_expr) ((out_ter (S : state) (l : res)) : out))

  | red_spec_creating_function_object_2_strict :
      forall (S0 : state (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (vthrower : value) (A : attributes) (l : object_loc (* input *)) (b : bool (* input *)) (o1 : out) (o : out),
        ((vthrower : value) = (value_object (prealloc_throw_type_error : object_loc))) ->
        (A = ((attributes_accessor_intro (vthrower : value) (vthrower : value) (false : bool) (false : bool)) : attributes)) ->
        (* ========================================== *)
        (red_expr (S : state) (C : execution_ctx) ((spec_object_define_own_prop (l : object_loc) ((("caller")%string) : prop_name) (A : descriptor) (false : bool)) : ext_expr) (o1 : out)) ->
        (red_expr (S : state) (C : execution_ctx) ((spec_creating_function_object_3 (l : object_loc) (o1 : out)) : ext_expr) (o : out)) ->
        (* ------------------------------------------ *)
        (red_expr (S0 : state) (C : execution_ctx) ((spec_creating_function_object_2 (true : strictness_flag) (l : object_loc) ((out_ter (S : state) (b : res)) : out)) : ext_expr) (o : out))

  | red_spec_creating_function_object_3 :
      forall (S0 : state (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (vthrower : value) (A : attributes) (l : object_loc (* input *)) (b : bool (* input *)) (o1 : out) (o : out),
        ((vthrower : value) = (value_object (prealloc_throw_type_error : object_loc))) ->
        (A = ((attributes_accessor_intro (vthrower : value) (vthrower : value) (false : bool) (false : bool)) : attributes)) ->
        (* ========================================== *)
        (red_expr (S : state) (C : execution_ctx) ((spec_object_define_own_prop (l : object_loc) ((("arguments")%string) : prop_name) (A : descriptor) (false : bool)) : ext_expr) (o1 : out)) ->
        (red_expr (S : state) (C : execution_ctx) ((spec_creating_function_object_4 (l : object_loc) (o1 : out)) : ext_expr) (o : out)) ->
        (* ------------------------------------------ *)
        (red_expr (S0 : state) (C : execution_ctx) ((spec_creating_function_object_3 (l : object_loc) ((out_ter (S : state) (b : res)) : out)) : ext_expr) (o : out))

  | red_spec_creating_function_object_4 :
      forall (S0 : state (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (l : object_loc (* input *)) (b : bool (* input *)),
        (* ========================================== *)
        (* ------------------------------------------ *)
        (red_expr (S0 : state) (C : execution_ctx) ((spec_creating_function_object_4 (l : object_loc) ((out_ter (S : state) (b : res)) : out)) : ext_expr) ((out_ter (S : state) (l : res)) : out))

  | red_spec_call_1_default :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (l : object_loc (* input *)) (this : value (* input *)) (args : (list value) (* input *)) (o : out),
        (* ========================================== *)
        (red_expr (S : state) (C : execution_ctx) ((spec_call_default (l : object_loc) (this : value) (args : (list value))) : ext_expr) (o : out)) ->
        (* ------------------------------------------ *)
        (red_expr (S : state) (C : execution_ctx) ((spec_call_1 (call_default : call) (l : object_loc) (this : value) (args : (list value))) : ext_expr) (o : out))

  | red_spec_call_default :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (l : object_loc (* input *)) (this : value (* input *)) (args : (list value) (* input *)) (o : out),
        (* ========================================== *)
        (red_expr (S : state) (C : execution_ctx) ((spec_entering_func_code (l : object_loc) (this : value) (args : (list value)) ((spec_call_default_1 (l : object_loc)) : ext_expr)) : ext_expr) (o : out)) ->
        (* ------------------------------------------ *)
        (red_expr (S : state) (C : execution_ctx) ((spec_call_default (l : object_loc) (this : value) (args : (list value))) : ext_expr) (o : out))

  | red_spec_call_default_1 :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (l : object_loc (* input *)) (bdo : (option funcbody)) (o : out),
        (object_method object_code_ S l bdo) ->
        (* ========================================== *)
        (red_expr (S : state) (C : execution_ctx) ((spec_call_default_2 (bdo : (option funcbody))) : ext_expr) (o : out)) ->
        (* ------------------------------------------ *)
        (red_expr (S : state) (C : execution_ctx) ((spec_call_default_1 (l : object_loc)) : ext_expr) (o : out))

  | red_spec_call_default_2_body :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (bd : _ (* input *)) (o1 : out) (o : out),
        (~ (funcbody_empty bd)) ->
        (* ========================================== *)
        (red_prog (S : state) (C : execution_ctx) ((funcbody_prog bd) : ext_prog) (o1 : out)) ->
        (red_expr (S : state) (C : execution_ctx) ((spec_call_default_3 (o1 : out)) : ext_expr) (o : out)) ->
        (* ------------------------------------------ *)
        (red_expr (S : state) (C : execution_ctx) ((spec_call_default_2 ((Some bd) : (option funcbody))) : ext_expr) (o : out))

  | red_spec_call_default_2_empty_body :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (bdo : (option funcbody) (* input *)) (o : out),
        match bdo with None => True | (Some bd) => (funcbody_empty bd) end ->
        (* ========================================== *)
        (red_expr (S : state) (C : execution_ctx) ((spec_call_default_3 ((out_ter (S : state) ((res_normal (undef : resvalue)) : res)) : out)) : ext_expr) (o : out)) ->
        (* ------------------------------------------ *)
        (red_expr (S : state) (C : execution_ctx) ((spec_call_default_2 (bdo : (option funcbody))) : ext_expr) (o : out))

  | red_spec_call_default_3_return :
      forall (S0 : state (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (rv : resvalue (* input *)),
        (* ========================================== *)
        (* ------------------------------------------ *)
        (red_expr (S0 : state) (C : execution_ctx) ((spec_call_default_3 ((out_ter (S : state) ((res_intro restype_return (rv : resvalue) label_empty) : res)) : out)) : ext_expr) ((out_ter (S : state) (rv : res)) : out))

  | red_spec_call_default_3_normal :
      forall (S0 : state (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (rv : resvalue (* input *)),
        (* ========================================== *)
        (* ------------------------------------------ *)
        (red_expr (S0 : state) (C : execution_ctx) ((spec_call_default_3 ((out_ter (S : state) ((res_intro restype_normal (rv : resvalue) label_empty) : res)) : out)) : ext_expr) ((out_ter (S : state) (undef : res)) : out))

  | red_spec_construct_1_default :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (l : object_loc (* input *)) (args : (list value) (* input *)) (o : out),
        (* ========================================== *)
        (red_expr (S : state) (C : execution_ctx) ((spec_construct_default (l : object_loc) (args : (list value))) : ext_expr) (o : out)) ->
        (* ------------------------------------------ *)
        (red_expr (S : state) (C : execution_ctx) ((spec_construct_1 (construct_default : construct) (l : object_loc) (args : (list value))) : ext_expr) (o : out))

  | red_spec_construct_default :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (l : object_loc (* input *)) (args : (list value) (* input *)) (o1 : out) (o : out),
        (* ========================================== *)
        (red_expr (S : state) (C : execution_ctx) ((spec_object_get (l : value) ((("prototype")%string) : prop_name)) : ext_expr) (o1 : out)) ->
        (red_expr (S : state) (C : execution_ctx) ((spec_construct_default_1 (l : object_loc) (args : (list value)) (o1 : out)) : ext_expr) (o : out)) ->
        (* ------------------------------------------ *)
        (red_expr (S : state) (C : execution_ctx) ((spec_construct_default (l : object_loc) (args : (list value))) : ext_expr) (o : out))

  | red_spec_construct_default_1 :
      forall (S0 : state (* input *)) (S : state (* input *)) (S' : state) (C : execution_ctx (* input *)) (l' : object_loc) (vproto : value) (O : object) (l : object_loc (* input *)) (args : (list value) (* input *)) (v : value (* input *)) (o1 : out) (o : out),
        ((vproto : value) = (ifb (((type_of v) : type) = type_object) then v else (prealloc_object_proto : value))) ->
        (O = ((object_new vproto (("Object")%string)) : object)) ->
        ((l', S') = ((object_alloc S O) : (object_loc * state))) ->
        (* ========================================== *)
        (red_expr (S' : state) (C : execution_ctx) ((spec_call (l : object_loc) ((value_object (l' : object_loc)) : value) (args : (list value))) : ext_expr) (o1 : out)) ->
        (red_expr (S' : state) (C : execution_ctx) ((spec_construct_default_2 (l' : object_loc) (o1 : out)) : ext_expr) (o : out)) ->
        (* ------------------------------------------ *)
        (red_expr (S0 : state) (C : execution_ctx) ((spec_construct_default_1 (l : object_loc) (args : (list value)) ((out_ter (S : state) (v : res)) : out)) : ext_expr) (o : out))

  | red_spec_function_construct_2 :
      forall (S0 : state (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (l' : object_loc (* input *)) (v : value (* input *)) (v' : value),
        (v' = ((ifb (((type_of v) : type) = type_object) then v else (l' : value)) : value)) ->
        (* ========================================== *)
        (* ------------------------------------------ *)
        (red_expr (S0 : state) (C : execution_ctx) ((spec_construct_default_2 (l' : object_loc) ((out_ter (S : state) (v : res)) : out)) : ext_expr) ((out_ter (S : state) (v' : res)) : out))

  | red_spec_create_new_function_in :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (args : (list string) (* input *)) (bd : funcbody (* input *)) (o : out),
        (* ========================================== *)
        (red_expr (S : state) (C : execution_ctx) ((spec_creating_function_object (args : (list string)) (bd : funcbody) ((execution_ctx_lexical_env (C : execution_ctx)) : lexical_env) ((execution_ctx_strict (C : execution_ctx)) : strictness_flag)) : ext_expr) (o : out)) ->
        (* ------------------------------------------ *)
        (red_expr (S : state) (C : execution_ctx) ((spec_create_new_function_in (C : execution_ctx) (args : (list string)) (bd : funcbody)) : ext_expr) (o : out))

  | red_spec_from_descriptor_undef :
      forall (S0 : state (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)),
        (* ========================================== *)
        (* ------------------------------------------ *)
        (red_expr (S0 : state) (C : execution_ctx) ((spec_from_descriptor ((specret_val S full_descriptor_undef) : (specret full_descriptor))) : ext_expr) ((out_ter (S : state) (undef : res)) : out))

  | red_spec_from_descriptor_some :
      forall (S0 : state (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (A : attributes (* input *)) (o : out) (o1 : out),
        (* ========================================== *)
        (red_expr (S : state) (C : execution_ctx) ((spec_construct_prealloc (prealloc_object : prealloc) (nil : (list value))) : ext_expr) (o1 : out)) ->
        (red_expr (S : state) (C : execution_ctx) ((spec_from_descriptor_1 (A : attributes) (o1 : out)) : ext_expr) (o : out)) ->
        (* ------------------------------------------ *)
        (red_expr (S0 : state) (C : execution_ctx) ((spec_from_descriptor ((specret_val S (full_descriptor_some (A : attributes))) : (specret full_descriptor))) : ext_expr) (o : out))

  | red_spec_from_descriptor_1_data :
      forall (S0 : state (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (Ad : attributes_data (* input *)) (A' : attributes) (l : object_loc (* input *)) (o : out) (o1 : out),
        (A' = ((attributes_data_intro_all_true ((attributes_data_value (Ad : attributes_data)) : value)) : attributes)) ->
        (* ========================================== *)
        (red_expr (S : state) (C : execution_ctx) ((spec_object_define_own_prop (l : object_loc) ((("value")%string) : prop_name) ((descriptor_of_attributes A') : descriptor) (throw_false : bool)) : ext_expr) (o1 : out)) ->
        (red_expr (S : state) (C : execution_ctx) ((spec_from_descriptor_2 (l : object_loc) (Ad : attributes_data) (o1 : out)) : ext_expr) (o : out)) ->
        (* ------------------------------------------ *)
        (red_expr (S0 : state) (C : execution_ctx) ((spec_from_descriptor_1 ((attributes_data_of (Ad : attributes_data)) : attributes) ((out_ter (S : state) (l : res)) : out)) : ext_expr) (o : out))

  | red_spec_from_descriptor_2_data :
      forall (S0 : state (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (Ad : attributes_data (* input *)) (A' : attributes) (l : object_loc (* input *)) (b : bool (* input *)) (o : out) (o1 : out),
        (A' = ((attributes_data_intro_all_true ((attributes_data_writable (Ad : attributes_data)) : value)) : attributes)) ->
        (* ========================================== *)
        (red_expr (S : state) (C : execution_ctx) ((spec_object_define_own_prop (l : object_loc) ((("writable")%string) : prop_name) ((descriptor_of_attributes A') : descriptor) (throw_false : bool)) : ext_expr) (o1 : out)) ->
        (red_expr (S : state) (C : execution_ctx) ((spec_from_descriptor_4 (l : object_loc) (Ad : attributes) (o1 : out)) : ext_expr) (o : out)) ->
        (* ------------------------------------------ *)
        (red_expr (S0 : state) (C : execution_ctx) ((spec_from_descriptor_2 (l : object_loc) (Ad : attributes_data) ((out_ter (S : state) (b : res)) : out)) : ext_expr) (o : out))

  | red_spec_from_descriptor_1_accessor :
      forall (S0 : state (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (Aa : attributes_accessor (* input *)) (A' : attributes) (l : object_loc (* input *)) (o : out) (o1 : out),
        (A' = ((attributes_data_intro_all_true ((attributes_accessor_get (Aa : attributes_accessor)) : value)) : attributes)) ->
        (* ========================================== *)
        (red_expr (S : state) (C : execution_ctx) ((spec_object_define_own_prop (l : object_loc) ((("get")%string) : prop_name) ((descriptor_of_attributes A') : descriptor) (throw_false : bool)) : ext_expr) (o1 : out)) ->
        (red_expr (S : state) (C : execution_ctx) ((spec_from_descriptor_3 (l : object_loc) (Aa : attributes_accessor) (o1 : out)) : ext_expr) (o : out)) ->
        (* ------------------------------------------ *)
        (red_expr (S0 : state) (C : execution_ctx) ((spec_from_descriptor_1 ((attributes_accessor_of (Aa : attributes_accessor)) : attributes) ((out_ter (S : state) (l : res)) : out)) : ext_expr) (o : out))

  | red_spec_from_descriptor_3_accessor :
      forall (S0 : state (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (Aa : attributes_accessor (* input *)) (A' : attributes) (l : object_loc (* input *)) (b : bool (* input *)) (o : out) (o1 : out),
        (A' = ((attributes_data_intro_all_true ((attributes_accessor_set (Aa : attributes_accessor)) : value)) : attributes)) ->
        (* ========================================== *)
        (red_expr (S : state) (C : execution_ctx) ((spec_object_define_own_prop (l : object_loc) ((("set")%string) : prop_name) ((descriptor_of_attributes A') : descriptor) (throw_false : bool)) : ext_expr) (o1 : out)) ->
        (red_expr (S : state) (C : execution_ctx) ((spec_from_descriptor_4 (l : object_loc) (Aa : attributes) (o1 : out)) : ext_expr) (o : out)) ->
        (* ------------------------------------------ *)
        (red_expr (S0 : state) (C : execution_ctx) ((spec_from_descriptor_3 (l : object_loc) (Aa : attributes_accessor) ((out_ter (S : state) (b : res)) : out)) : ext_expr) (o : out))

  | red_spec_from_descriptor_4 :
      forall (S0 : state (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (A : attributes (* input *)) (A' : attributes) (l : object_loc (* input *)) (b : bool (* input *)) (o : out) (o1 : out),
        (A' = ((attributes_data_intro_all_true ((attributes_enumerable (A : attributes)) : value)) : attributes)) ->
        (* ========================================== *)
        (red_expr (S : state) (C : execution_ctx) ((spec_object_define_own_prop (l : object_loc) ((("enumerable")%string) : prop_name) ((descriptor_of_attributes A') : descriptor) (throw_false : bool)) : ext_expr) (o1 : out)) ->
        (red_expr (S : state) (C : execution_ctx) ((spec_from_descriptor_5 (l : object_loc) (A : attributes) (o1 : out)) : ext_expr) (o : out)) ->
        (* ------------------------------------------ *)
        (red_expr (S0 : state) (C : execution_ctx) ((spec_from_descriptor_4 (l : object_loc) (A : attributes) ((out_ter (S : state) (b : res)) : out)) : ext_expr) (o : out))

  | red_spec_from_descriptor_5 :
      forall (S0 : state (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (A : attributes (* input *)) (A' : attributes) (l : object_loc (* input *)) (b : bool (* input *)) (o : out) (o1 : out),
        (A' = ((attributes_data_intro_all_true ((attributes_configurable (A : attributes)) : value)) : attributes)) ->
        (* ========================================== *)
        (red_expr (S : state) (C : execution_ctx) ((spec_object_define_own_prop (l : object_loc) ((("configurable")%string) : prop_name) ((descriptor_of_attributes A') : descriptor) (throw_false : bool)) : ext_expr) (o1 : out)) ->
        (red_expr (S : state) (C : execution_ctx) ((spec_from_descriptor_6 (l : object_loc) (o1 : out)) : ext_expr) (o : out)) ->
        (* ------------------------------------------ *)
        (red_expr (S0 : state) (C : execution_ctx) ((spec_from_descriptor_5 (l : object_loc) (A : attributes) ((out_ter (S : state) (b : res)) : out)) : ext_expr) (o : out))

  | red_spec_from_descriptor_6 :
      forall (S0 : state (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (l : object_loc (* input *)) (b : bool (* input *)),
        (* ========================================== *)
        (* ------------------------------------------ *)
        (red_expr (S0 : state) (C : execution_ctx) ((spec_from_descriptor_6 (l : object_loc) ((out_ter (S : state) (b : res)) : out)) : ext_expr) ((out_ter (S : state) (l : res)) : out))

  | red_spec_call_throw_type_error :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (o : out) (vthis : value (* input *)) (args : (list value) (* input *)),
        (* ========================================== *)
        (red_expr (S : state) (C : execution_ctx) ((spec_error (native_error_type : native_error)) : ext_expr) (o : out)) ->
        (* ------------------------------------------ *)
        (red_expr (S : state) (C : execution_ctx) ((spec_call_prealloc (prealloc_throw_type_error : prealloc) (vthis : value) (args : (list value))) : ext_expr) (o : out))

  | red_spec_call_global_eval :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (bdirect : bool (* input *)) (args : (list value) (* input *)) (v : value) (o : out),
        (arguments_from (args : (list value)) ((v :: (nil : (list value))) : (list value))) ->
        (* ========================================== *)
        (red_expr (S : state) (C : execution_ctx) ((spec_call_global_eval_1 (bdirect : bool) (v : value)) : ext_expr) (o : out)) ->
        (* ------------------------------------------ *)
        (red_expr (S : state) (C : execution_ctx) ((spec_call_global_eval (bdirect : bool) (args : (list value))) : ext_expr) (o : out))

  | red_spec_call_global_eval_1_not_string :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (bdirect : bool (* input *)) (v : value (* input *)),
        (((type_of v) : type) <> type_string) ->
        (* ========================================== *)
        (* ------------------------------------------ *)
        (red_expr (S : state) (C : execution_ctx) ((spec_call_global_eval_1 (bdirect : bool) (v : value)) : ext_expr) ((out_ter (S : state) (v : res)) : out))

  | red_spec_call_global_eval_1_string_not_parse :
      forall (s : string (* input *)) (b : bool) (S : state (* input *)) (C : execution_ctx (* input *)) (bdirect : bool (* input *)) (o : out),
        (forall p, (~ (parse s b p))) ->
        (* ========================================== *)
        (red_expr (S : state) (C : execution_ctx) ((spec_error (native_error_syntax : native_error)) : ext_expr) (o : out)) ->
        (* ------------------------------------------ *)
        (red_expr (S : state) (C : execution_ctx) ((spec_call_global_eval_1 (bdirect : bool) (s : value)) : ext_expr) (o : out))

  | red_spec_call_global_eval_1_string_parse :
      forall (s : string (* input *)) (b : bool) (p : prog) (S : state (* input *)) (C : execution_ctx (* input *)) (bdirect : bool (* input *)) (o : out),
        (parse (s : string) (b : bool) (p : prog)) ->
        (* ========================================== *)
        (red_expr (S : state) (C : execution_ctx) ((spec_entering_eval_code (bdirect : bool) ((funcbody_intro (p : prog) (s : string)) : funcbody) ((spec_call_global_eval_2 (p : prog)) : ext_expr)) : ext_expr) (o : out)) ->
        (* ------------------------------------------ *)
        (red_expr (S : state) (C : execution_ctx) ((spec_call_global_eval_1 (bdirect : bool) (s : value)) : ext_expr) (o : out))

  | red_spec_call_global_eval_2 :
      forall (o1 : out) (S : state (* input *)) (C : execution_ctx (* input *)) (p : prog (* input *)) (o : out),
        (* ========================================== *)
        (red_prog (S : state) (C : execution_ctx) (p : ext_prog) (o1 : out)) ->
        (red_expr (S : state) (C : execution_ctx) ((spec_call_global_eval_3 (o1 : out)) : ext_expr) (o : out)) ->
        (* ------------------------------------------ *)
        (red_expr (S : state) (C : execution_ctx) ((spec_call_global_eval_2 (p : prog)) : ext_expr) (o : out))

  | red_spec_call_global_eval_3_normal_value :
      forall (S0 : state (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (v : value (* input *)),
        (* ========================================== *)
        (* ------------------------------------------ *)
        (red_expr (S0 : state) (C : execution_ctx) ((spec_call_global_eval_3 ((out_ter (S : state) (v : res)) : out)) : ext_expr) ((out_ter (S : state) (v : res)) : out))

  | red_spec_call_global_eval_3_normal_empty :
      forall (S0 : state (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (R : res (* input *)),
        ((res_type (R : res)) = (restype_normal : restype)) ->
        ((res_value (R : res)) = (resvalue_empty : resvalue)) ->
        (* ========================================== *)
        (* ------------------------------------------ *)
        (red_expr (S0 : state) (C : execution_ctx) ((spec_call_global_eval_3 ((out_ter (S : state) (R : res)) : out)) : ext_expr) ((out_ter (S : state) (undef : res)) : out))

  | red_spec_call_global_eval_3_throw :
      forall (S0 : state (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (R : res (* input *)),
        ((res_type (R : res)) = (restype_throw : restype)) ->
        (* ========================================== *)
        (* ------------------------------------------ *)
        (red_expr (S0 : state) (C : execution_ctx) ((spec_call_global_eval_3 ((out_ter (S : state) (R : res)) : out)) : ext_expr) ((out_ter (S : state) ((res_throw ((res_value (R : res)) : resvalue)) : res)) : out))

  | red_spec_call_global_is_nan :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (v : value) (o : out) (o1 : out) (vthis : value (* input *)) (args : (list value) (* input *)),
        (arguments_from (args : (list value)) ((v :: (nil : (list value))) : (list value))) ->
        (* ========================================== *)
        (red_expr (S : state) (C : execution_ctx) ((spec_to_number (v : value)) : ext_expr) (o1 : out)) ->
        (red_expr (S : state) (C : execution_ctx) ((spec_call_global_is_nan_1 (o1 : out)) : ext_expr) (o : out)) ->
        (* ------------------------------------------ *)
        (red_expr (S : state) (C : execution_ctx) ((spec_call_prealloc (prealloc_global_is_nan : prealloc) (vthis : value) (args : (list value))) : ext_expr) (o : out))

  | red_spec_call_global_is_nan_1 :
      forall (S : state (* input *)) (S0 : state (* input *)) (C : execution_ctx (* input *)) (b : bool) (n : number (* input *)),
        (b = ((ifb (n = (JsNumber.nan : number)) then (true : bool) else false) : bool)) ->
        (* ========================================== *)
        (* ------------------------------------------ *)
        (red_expr (S0 : state) (C : execution_ctx) ((spec_call_global_is_nan_1 ((out_ter (S : state) (n : res)) : out)) : ext_expr) ((out_ter (S : state) (b : res)) : out))

  | red_spec_call_global_is_finite :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (v : value) (o : out) (o1 : out) (vthis : value (* input *)) (args : (list value) (* input *)),
        (arguments_from (args : (list value)) ((v :: (nil : (list value))) : (list value))) ->
        (* ========================================== *)
        (red_expr (S : state) (C : execution_ctx) ((spec_to_number (v : value)) : ext_expr) (o1 : out)) ->
        (red_expr (S : state) (C : execution_ctx) ((spec_call_global_is_finite_1 (o1 : out)) : ext_expr) (o : out)) ->
        (* ------------------------------------------ *)
        (red_expr (S : state) (C : execution_ctx) ((spec_call_prealloc (prealloc_global_is_finite : prealloc) (vthis : value) (args : (list value))) : ext_expr) (o : out))

  | red_spec_call_global_is_finite_1 :
      forall (S : state (* input *)) (S0 : state (* input *)) (C : execution_ctx (* input *)) (b : bool) (n : number (* input *)),
        (b = ((ifb ((((n = JsNumber.nan) \/ (n = JsNumber.infinity)) : Prop) \/ ((n = JsNumber.neg_infinity) : Prop)) then (false : bool) else true) : bool)) ->
        (* ========================================== *)
        (* ------------------------------------------ *)
        (red_expr (S0 : state) (C : execution_ctx) ((spec_call_global_is_finite_1 ((out_ter (S : state) (n : res)) : out)) : ext_expr) ((out_ter (S : state) (b : res)) : out))

  | red_spec_call_object_call :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (vthis : value (* input *)) (args : (list value) (* input *)) (v : value) (o : out),
        (arguments_from (args : (list value)) ((v :: (nil : (list value))) : (list value))) ->
        (* ========================================== *)
        (red_expr (S : state) (C : execution_ctx) ((spec_call_object_call_1 (v : value)) : ext_expr) (o : out)) ->
        (* ------------------------------------------ *)
        (red_expr (S : state) (C : execution_ctx) ((spec_call_prealloc (prealloc_object : prealloc) (vthis : value) (args : (list value))) : ext_expr) (o : out))

  | red_spec_call_object_call_1_null_or_undef :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (v : value (* input *)) (o : out),
        (((v = null) : Prop) \/ ((v = undef) : Prop)) ->
        (* ========================================== *)
        (red_expr (S : state) (C : execution_ctx) ((spec_call_object_new_1 (v : value)) : ext_expr) (o : out)) ->
        (* ------------------------------------------ *)
        (red_expr (S : state) (C : execution_ctx) ((spec_call_object_call_1 (v : value)) : ext_expr) (o : out))

  | red_spec_call_object_call_1_other :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (v : value (* input *)) (o : out),
        (((v <> null) : Prop) /\ ((v <> undef) : Prop)) ->
        (* ========================================== *)
        (red_expr (S : state) (C : execution_ctx) ((spec_to_object (v : value)) : ext_expr) (o : out)) ->
        (* ------------------------------------------ *)
        (red_expr (S : state) (C : execution_ctx) ((spec_call_object_call_1 (v : value)) : ext_expr) (o : out))

  | red_spec_call_object_new :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (args : (list value) (* input *)) (v : value) (o : out),
        (arguments_from (args : (list value)) ((v :: (nil : (list value))) : (list value))) ->
        (* ========================================== *)
        (red_expr (S : state) (C : execution_ctx) ((spec_call_object_new_1 (v : value)) : ext_expr) (o : out)) ->
        (* ------------------------------------------ *)
        (red_expr (S : state) (C : execution_ctx) ((spec_construct_prealloc (prealloc_object : prealloc) (args : (list value))) : ext_expr) (o : out))

  | red_spec_call_object_new_1_object :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (v : value (* input *)),
        (((type_of v) : type) = type_object) ->
        (* ========================================== *)
        (* ------------------------------------------ *)
        (red_expr (S : state) (C : execution_ctx) ((spec_call_object_new_1 (v : value)) : ext_expr) ((out_ter (S : state) (v : res)) : out))

  | red_spec_call_object_new_1_prim :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (v : value (* input *)) (ty : type) (o : out),
        (ty = ((type_of v) : type)) ->
        ((((ty = type_string) \/ (ty = type_bool)) : Prop) \/ ((ty = type_number) : Prop)) ->
        (* ========================================== *)
        (red_expr (S : state) (C : execution_ctx) ((spec_to_object (v : value)) : ext_expr) (o : out)) ->
        (* ------------------------------------------ *)
        (red_expr (S : state) (C : execution_ctx) ((spec_call_object_new_1 (v : value)) : ext_expr) (o : out))

  | red_spec_call_object_new_1_null_or_undef :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (v : value (* input *)) (O : object) (l : object_loc) (S' : state),
        (((v = null) : Prop) \/ ((v = undef) : Prop)) ->
        (O = ((object_new prealloc_object_proto (("Object")%string)) : object)) ->
        ((l, S') = ((object_alloc S O) : (object_loc * state))) ->
        (* ========================================== *)
        (* ------------------------------------------ *)
        (red_expr (S : state) (C : execution_ctx) ((spec_call_object_new_1 (v : value)) : ext_expr) ((out_ter (S' : state) (l : res)) : out))

  | red_spec_call_object_get_proto_of :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (v : value) (vthis : value (* input *)) (args : (list value) (* input *)) (o : out),
        (arguments_from (args : (list value)) ((v :: (nil : (list value))) : (list value))) ->
        (* ========================================== *)
        (red_expr (S : state) (C : execution_ctx) ((spec_call_object_get_proto_of_1 (v : value)) : ext_expr) (o : out)) ->
        (* ------------------------------------------ *)
        (red_expr (S : state) (C : execution_ctx) ((spec_call_prealloc (prealloc_object_get_proto_of : prealloc) (vthis : value) (args : (list value))) : ext_expr) (o : out))

  | red_spec_call_object_get_proto_of_1_not_object :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (w : prim (* input *)) (o : out),
        (* ========================================== *)
        (red_expr (S : state) (C : execution_ctx) ((spec_error (native_error_type : native_error)) : ext_expr) (o : out)) ->
        (* ------------------------------------------ *)
        (red_expr (S : state) (C : execution_ctx) ((spec_call_object_get_proto_of_1 (w : value)) : ext_expr) (o : out))

  | red_spec_call_object_get_proto_of_1_object :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (l : object_loc (* input *)) (v : value),
        (object_proto (S : state) (l : object_loc) (v : value)) ->
        (* ========================================== *)
        (* ------------------------------------------ *)
        (red_expr (S : state) (C : execution_ctx) ((spec_call_object_get_proto_of_1 (l : value)) : ext_expr) ((out_ter (S : state) (v : res)) : out))

  | red_spec_call_object_get_own_prop_descriptor :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (vo : value) (vx : value) (o : out) (vthis : value (* input *)) (args : (list value) (* input *)),
        (arguments_from (args : (list value)) ((vo :: (vx :: nil)) : (list value))) ->
        (* ========================================== *)
        (red_expr (S : state) (C : execution_ctx) ((spec_call_object_get_own_prop_descriptor_1 (vo : value) (vx : value)) : ext_expr) (o : out)) ->
        (* ------------------------------------------ *)
        (red_expr (S : state) (C : execution_ctx) ((spec_call_prealloc (prealloc_object_get_own_prop_descriptor : prealloc) (vthis : value) (args : (list value))) : ext_expr) (o : out))

  | red_spec_call_object_get_own_prop_descriptor_1_not_object :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (vo : value (* input *)) (vx : value (* input *)) (o : out),
        (((type_of vo) : type) <> type_object) ->
        (* ========================================== *)
        (red_expr (S : state) (C : execution_ctx) ((spec_error (native_error_type : native_error)) : ext_expr) (o : out)) ->
        (* ------------------------------------------ *)
        (red_expr (S : state) (C : execution_ctx) ((spec_call_object_get_own_prop_descriptor_1 (vo : value) (vx : value)) : ext_expr) (o : out))

  | red_spec_call_object_get_own_prop_descriptor_1_object :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (l : object_loc (* input *)) (vx : value (* input *)) (o : out) (o1 : out),
        (* ========================================== *)
        (red_expr (S : state) (C : execution_ctx) ((spec_to_string (vx : value)) : ext_expr) (o1 : out)) ->
        (red_expr (S : state) (C : execution_ctx) ((spec_call_object_get_own_prop_descriptor_2 (l : object_loc) (o1 : out)) : ext_expr) (o : out)) ->
        (* ------------------------------------------ *)
        (red_expr (S : state) (C : execution_ctx) ((spec_call_object_get_own_prop_descriptor_1 (l : value) (vx : value)) : ext_expr) (o : out))

  | red_spec_call_object_get_own_prop_descriptor_2 :
      forall (S0 : state (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (l : object_loc (* input *)) (x : prop_name (* input *)) (o : out) (y : (specret full_descriptor)),
        (* ========================================== *)
        (red_spec S C (spec_object_get_own_prop (l : object_loc) (x : prop_name)) y) ->
        (red_expr (S : state) (C : execution_ctx) ((spec_from_descriptor (y : (specret full_descriptor))) : ext_expr) (o : out)) ->
        (* ------------------------------------------ *)
        (red_expr (S0 : state) (C : execution_ctx) ((spec_call_object_get_own_prop_descriptor_2 (l : object_loc) ((out_ter (S : state) (x : res)) : out)) : ext_expr) (o : out))

  | red_spec_call_object_object_create :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (vo : value) (vp : value) (vthis : value (* input *)) (args : (list value) (* input *)) (o : out),
        (arguments_from (args : (list value)) (((vo : value) :: (vp :: (nil : (list value)))) : (list value))) ->
        (* ========================================== *)
        (red_expr (S : state) (C : execution_ctx) ((spec_call_object_create_1 (vo : value) (vp : value)) : ext_expr) (o : out)) ->
        (* ------------------------------------------ *)
        (red_expr (S : state) (C : execution_ctx) ((spec_call_prealloc (prealloc_object_create : prealloc) (vthis : value) (args : (list value))) : ext_expr) (o : out))

  | red_spec_call_object_object_create_1_not_object :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (vo : value (* input *)) (vp : value (* input *)) (o : out),
        (((type_of vo) : type) <> type_object) ->
        (((type_of vo) : type) <> type_null) ->
        (* ========================================== *)
        (red_expr (S : state) (C : execution_ctx) ((spec_error (native_error_type : native_error)) : ext_expr) (o : out)) ->
        (* ------------------------------------------ *)
        (red_expr (S : state) (C : execution_ctx) ((spec_call_object_create_1 (vo : value) (vp : value)) : ext_expr) (o : out))

  | red_spec_call_object_object_create_1_object :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (vo : value (* input *)) (vp : value (* input *)) (o : out) (o1 : out),
        (* ========================================== *)
        (red_expr (S : state) (C : execution_ctx) ((spec_construct_prealloc (prealloc_object : prealloc) (nil : (list value))) : ext_expr) (o1 : out)) ->
        (red_expr (S : state) (C : execution_ctx) ((spec_call_object_create_2 (o1 : out) (vo : value) (vp : value)) : ext_expr) (o : out)) ->
        (* ------------------------------------------ *)
        (red_expr (S : state) (C : execution_ctx) ((spec_call_object_create_1 (vo : value) (vp : value)) : ext_expr) (o : out))

  | red_spec_call_object_object_create_2 :
      forall (S : state (* input *)) (S0 : state (* input *)) (C : execution_ctx (* input *)) (l : object_loc (* input *)) (O : object) (O' : object) (S' : state) (vo : value (* input *)) (vp : value (* input *)) (o : out),
        (object_binds (S : state) (l : object_loc) (O : object)) ->
        (O' = ((object_set_proto O vo) : object)) ->
        (S' = ((object_write S l O') : state)) ->
        (* ========================================== *)
        (red_expr (S' : state) (C : execution_ctx) ((spec_call_object_create_3 (l : object_loc) (vp : value)) : ext_expr) (o : out)) ->
        (* ------------------------------------------ *)
        (red_expr (S0 : state) (C : execution_ctx) ((spec_call_object_create_2 ((out_ter (S : state) (l : res)) : out) (vo : value) (vp : value)) : ext_expr) (o : out))

  | red_spec_call_object_object_create_3_def :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (l : object_loc (* input *)) (vp : value (* input *)) (o : out),
        (vp <> (undef : value)) ->
        (* ========================================== *)
        (red_expr (S : state) (C : execution_ctx) ((spec_call_object_define_props_1 (l : value) (vp : value)) : ext_expr) (o : out)) ->
        (* ------------------------------------------ *)
        (red_expr (S : state) (C : execution_ctx) ((spec_call_object_create_3 (l : object_loc) (vp : value)) : ext_expr) (o : out))

  | red_spec_call_object_object_create_3_undef :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (l : object_loc (* input *)),
        (* ========================================== *)
        (* ------------------------------------------ *)
        (red_expr (S : state) (C : execution_ctx) ((spec_call_object_create_3 (l : object_loc) (undef : value)) : ext_expr) ((out_ter (S : state) (l : res)) : out))

  | red_spec_call_object_object_define_prop :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (vo : value) (vx : value) (va : value) (o : out) (vthis : value (* input *)) (args : (list value) (* input *)),
        (arguments_from (args : (list value)) ((vo :: (vx :: (va :: nil))) : (list value))) ->
        (* ========================================== *)
        (red_expr (S : state) (C : execution_ctx) ((spec_call_object_define_prop_1 (vo : value) (vx : value) (va : value)) : ext_expr) (o : out)) ->
        (* ------------------------------------------ *)
        (red_expr (S : state) (C : execution_ctx) ((spec_call_prealloc (prealloc_object_define_prop : prealloc) (vthis : value) (args : (list value))) : ext_expr) (o : out))

  | red_spec_call_object_object_define_prop_1_not_object :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (vo : value (* input *)) (vx : value (* input *)) (va : value (* input *)) (o : out),
        (((type_of vo) : type) <> type_object) ->
        (* ========================================== *)
        (red_expr (S : state) (C : execution_ctx) ((spec_error (native_error_type : native_error)) : ext_expr) (o : out)) ->
        (* ------------------------------------------ *)
        (red_expr (S : state) (C : execution_ctx) ((spec_call_object_define_prop_1 (vo : value) (vx : value) (va : value)) : ext_expr) (o : out))

  | red_spec_call_object_object_define_prop_1_object :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (l : object_loc (* input *)) (vx : value (* input *)) (va : value (* input *)) (o1 : out) (o : out),
        (* ========================================== *)
        (red_expr (S : state) (C : execution_ctx) ((spec_to_string (vx : value)) : ext_expr) (o1 : out)) ->
        (red_expr (S : state) (C : execution_ctx) ((spec_call_object_define_prop_2 (l : object_loc) (o1 : out) (va : value)) : ext_expr) (o : out)) ->
        (* ------------------------------------------ *)
        (red_expr (S : state) (C : execution_ctx) ((spec_call_object_define_prop_1 (l : value) (vx : value) (va : value)) : ext_expr) (o : out))

  | red_spec_call_object_object_define_prop_2 :
      forall (S : state (* input *)) (S0 : state (* input *)) (C : execution_ctx (* input *)) (l : object_loc (* input *)) (x : prop_name (* input *)) (va : value (* input *)) (o : out) (y : (specret descriptor)),
        (* ========================================== *)
        (red_spec S C (spec_to_descriptor (va : value)) y) ->
        (red_expr (S : state) (C : execution_ctx) ((spec_call_object_define_prop_3 (l : object_loc) (x : string) (y : (specret descriptor))) : ext_expr) (o : out)) ->
        (* ------------------------------------------ *)
        (red_expr (S0 : state) (C : execution_ctx) ((spec_call_object_define_prop_2 (l : object_loc) ((out_ter (S : state) (x : res)) : out) (va : value)) : ext_expr) (o : out))

  | red_spec_call_object_object_define_prop_3 :
      forall (S : state (* input *)) (S0 : state (* input *)) (C : execution_ctx (* input *)) (l : object_loc (* input *)) (s : string (* input *)) (Desc : descriptor (* input *)) (o1 : out) (o : out),
        (* ========================================== *)
        (red_expr (S : state) (C : execution_ctx) ((spec_object_define_own_prop (l : object_loc) (s : prop_name) (Desc : descriptor) (throw_true : bool)) : ext_expr) (o1 : out)) ->
        (red_expr (S : state) (C : execution_ctx) ((spec_call_object_define_prop_4 (l : object_loc) (o1 : out)) : ext_expr) (o : out)) ->
        (* ------------------------------------------ *)
        (red_expr (S0 : state) (C : execution_ctx) ((spec_call_object_define_prop_3 (l : object_loc) (s : string) ((specret_val S Desc) : (specret descriptor))) : ext_expr) (o : out))

  | red_spec_call_object_object_define_prop_4 :
      forall (S : state (* input *)) (S0 : state (* input *)) (C : execution_ctx (* input *)) (l : object_loc (* input *)) (b : bool (* input *)),
        (* ========================================== *)
        (* ------------------------------------------ *)
        (red_expr (S0 : state) (C : execution_ctx) ((spec_call_object_define_prop_4 (l : object_loc) ((out_ter (S : state) (b : res)) : out)) : ext_expr) ((out_ter (S : state) (l : res)) : out))

  | red_spec_call_object_object_define_props :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (vo : value) (vp : value) (o : out) (vthis : value (* input *)) (args : (list value) (* input *)),
        (arguments_from (args : (list value)) (((vo : value) :: (vp :: (nil : (list value)))) : (list value))) ->
        (* ========================================== *)
        (red_expr (S : state) (C : execution_ctx) ((spec_call_object_define_props_1 (vo : value) (vp : value)) : ext_expr) (o : out)) ->
        (* ------------------------------------------ *)
        (red_expr (S : state) (C : execution_ctx) ((spec_call_prealloc (prealloc_object_define_props : prealloc) (vthis : value) (args : (list value))) : ext_expr) (o : out))

  | red_spec_call_object_object_define_props_1_not_object :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (vo : value (* input *)) (vp : value (* input *)) (o : out),
        (((type_of vo) : type) <> type_object) ->
        (* ========================================== *)
        (red_expr (S : state) (C : execution_ctx) ((spec_error (native_error_type : native_error)) : ext_expr) (o : out)) ->
        (* ------------------------------------------ *)
        (red_expr (S : state) (C : execution_ctx) ((spec_call_object_define_props_1 (vo : value) (vp : value)) : ext_expr) (o : out))

  | red_spec_call_object_object_define_props_1_object :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (l : object_loc (* input *)) (vp : value (* input *)) (o : out) (o1 : out),
        (* ========================================== *)
        (red_expr (S : state) (C : execution_ctx) ((spec_to_object (vp : value)) : ext_expr) (o1 : out)) ->
        (red_expr (S : state) (C : execution_ctx) ((spec_call_object_define_props_2 (o1 : out) (l : object_loc)) : ext_expr) (o : out)) ->
        (* ------------------------------------------ *)
        (red_expr (S : state) (C : execution_ctx) ((spec_call_object_define_props_1 (l : value) (vp : value)) : ext_expr) (o : out))

  | red_spec_call_object_object_define_props_2 :
      forall (S0 : state (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (l : object_loc (* input *)) (lp : object_loc (* input *)) (xs : (list prop_name)) (o : out),
        (object_properties_enumerable_keys_as_list S lp xs) ->
        (* ========================================== *)
        (red_expr (S : state) (C : execution_ctx) ((spec_call_object_define_props_3 (l : object_loc) (lp : object_loc) (xs : (list prop_name)) (nil : (list (prop_name * attributes)))) : ext_expr) (o : out)) ->
        (* ------------------------------------------ *)
        (red_expr (S0 : state) (C : execution_ctx) ((spec_call_object_define_props_2 ((out_ter (S : state) (lp : res)) : out) (l : object_loc)) : ext_expr) (o : out))

  | red_spec_call_object_define_props_3_nil :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (l : object_loc (* input *)) (lp : object_loc (* input *)) (Descs : (list (prop_name * attributes)) (* input *)) (o : out),
        (* ========================================== *)
        (red_expr (S : state) (C : execution_ctx) ((spec_call_object_define_props_6 (l : object_loc) (Descs : (list (prop_name * attributes)))) : ext_expr) (o : out)) ->
        (* ------------------------------------------ *)
        (red_expr (S : state) (C : execution_ctx) ((spec_call_object_define_props_3 (l : object_loc) (lp : object_loc) (nil : (list prop_name)) (Descs : (list (prop_name * attributes)))) : ext_expr) (o : out))

  | red_spec_call_object_define_props_3_cons :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (l : object_loc (* input *)) (lp : object_loc (* input *)) (x : prop_name (* input *)) (xs : (list prop_name) (* input *)) (Descs : (list (prop_name * attributes)) (* input *)) (o : out) (o1 : out),
        (* ========================================== *)
        (red_expr (S : state) (C : execution_ctx) ((spec_object_get (lp : value) (x : prop_name)) : ext_expr) (o1 : out)) ->
        (red_expr (S : state) (C : execution_ctx) ((spec_call_object_define_props_4 (o1 : out) (l : object_loc) (lp : object_loc) (x : prop_name) (xs : (list prop_name)) (Descs : (list (prop_name * attributes)))) : ext_expr) (o : out)) ->
        (* ------------------------------------------ *)
        (red_expr (S : state) (C : execution_ctx) ((spec_call_object_define_props_3 (l : object_loc) (lp : object_loc) ((x :: (xs : (list prop_name))) : (list prop_name)) (Descs : (list (prop_name * attributes)))) : ext_expr) (o : out))

  | red_spec_call_object_define_props_4 :
      forall (S0 : state (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (v : value (* input *)) (l : object_loc (* input *)) (lp : object_loc (* input *)) (o : out) (o1 : out) (x : prop_name (* input *)) (xs : (list prop_name) (* input *)) (Descs : (list (prop_name * attributes)) (* input *)) (y : (specret attributes)),
        (* ========================================== *)
        (red_spec S C (spec_to_descriptor (v : value)) y) ->
        (red_expr (S : state) (C : execution_ctx) ((spec_call_object_define_props_5 (l : object_loc) (lp : object_loc) (x : prop_name) (xs : (list prop_name)) (Descs : (list (prop_name * attributes))) (y : (specret attributes))) : ext_expr) (o1 : out)) ->
        (* ------------------------------------------ *)
        (red_expr (S0 : state) (C : execution_ctx) ((spec_call_object_define_props_4 ((out_ter (S : state) (v : res)) : out) (l : object_loc) (lp : object_loc) (x : prop_name) (xs : (list prop_name)) (Descs : (list (prop_name * attributes)))) : ext_expr) (o : out))

  | red_spec_call_object_define_props_5 :
      forall (S : state (* input *)) (S0 : state (* input *)) (C : execution_ctx (* input *)) (A : attributes (* input *)) (l : object_loc (* input *)) (lp : object_loc (* input *)) (o : out) (x : prop_name (* input *)) (xs : (list prop_name) (* input *)) (xAs : (list (prop_name * attributes)) (* input *)),
        (* ========================================== *)
        (red_expr (S : state) (C : execution_ctx) ((spec_call_object_define_props_3 (l : object_loc) (lp : object_loc) (xs : (list prop_name)) (((xAs : (list (prop_name * attributes))) ++ ((x, A) :: (nil : (list (prop_name * attributes))))) : (list (prop_name * attributes)))) : ext_expr) (o : out)) ->
        (* ------------------------------------------ *)
        (red_expr (S0 : state) (C : execution_ctx) ((spec_call_object_define_props_5 (l : object_loc) (lp : object_loc) (x : prop_name) (xs : (list prop_name)) (xAs : (list (prop_name * attributes))) ((specret_val S A) : (specret attributes))) : ext_expr) (o : out))

  | red_spec_call_object_define_props_6_cons :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (l : object_loc (* input *)) (x : prop_name (* input *)) (A : attributes (* input *)) (xAs : (list (prop_name * attributes)) (* input *)) (o1 : out) (o : out),
        (* ========================================== *)
        (red_expr (S : state) (C : execution_ctx) ((spec_object_define_own_prop (l : object_loc) (x : prop_name) ((descriptor_of_attributes A) : descriptor) (throw_true : bool)) : ext_expr) (o1 : out)) ->
        (red_expr (S : state) (C : execution_ctx) ((spec_call_object_define_props_7 (o1 : out) (l : object_loc) (xAs : (list (prop_name * attributes)))) : ext_expr) (o : out)) ->
        (* ------------------------------------------ *)
        (red_expr (S : state) (C : execution_ctx) ((spec_call_object_define_props_6 (l : object_loc) (((x, A) :: (xAs : (list (prop_name * attributes)))) : (list (prop_name * attributes)))) : ext_expr) (o : out))

  | red_spec_call_object_define_props_7 :
      forall (S0 : state (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (l : object_loc (* input *)) (xAs : (list (prop_name * attributes)) (* input *)) (b : bool (* input *)) (o : out),
        (* ========================================== *)
        (red_expr (S : state) (C : execution_ctx) ((spec_call_object_define_props_6 (l : object_loc) (xAs : (list (prop_name * attributes)))) : ext_expr) (o : out)) ->
        (* ------------------------------------------ *)
        (red_expr (S0 : state) (C : execution_ctx) ((spec_call_object_define_props_7 ((out_ter (S : state) (b : res)) : out) (l : object_loc) (xAs : (list (prop_name * attributes)))) : ext_expr) (o : out))

  | red_spec_call_object_define_props_6_nil :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (l : object_loc (* input *)),
        (* ========================================== *)
        (* ------------------------------------------ *)
        (red_expr (S : state) (C : execution_ctx) ((spec_call_object_define_props_6 (l : object_loc) (nil : (list (prop_name * attributes)))) : ext_expr) ((out_ter (S : state) (l : res)) : out))

  | red_spec_call_object_seal :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (v : value) (o : out) (vthis : value (* input *)) (args : (list value) (* input *)),
        (arguments_from (args : (list value)) ((v :: (nil : (list value))) : (list value))) ->
        (* ========================================== *)
        (red_expr (S : state) (C : execution_ctx) ((spec_call_object_seal_1 (v : value)) : ext_expr) (o : out)) ->
        (* ------------------------------------------ *)
        (red_expr (S : state) (C : execution_ctx) ((spec_call_prealloc (prealloc_object_seal : prealloc) (vthis : value) (args : (list value))) : ext_expr) (o : out))

  | red_spec_call_object_seal_1_not_object :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (v : value (* input *)) (o : out),
        (((type_of v) : type) <> type_object) ->
        (* ========================================== *)
        (red_expr (S : state) (C : execution_ctx) ((spec_error (native_error_type : native_error)) : ext_expr) (o : out)) ->
        (* ------------------------------------------ *)
        (red_expr (S : state) (C : execution_ctx) ((spec_call_object_seal_1 (v : value)) : ext_expr) (o : out))

  | red_spec_call_object_seal_1_object :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (l : object_loc (* input *)) (xs : (list prop_name)) (o : out),
        (object_properties_keys_as_list S l xs) ->
        (* ========================================== *)
        (red_expr (S : state) (C : execution_ctx) ((spec_call_object_seal_2 (l : object_loc) (xs : (list prop_name))) : ext_expr) (o : out)) ->
        (* ------------------------------------------ *)
        (red_expr (S : state) (C : execution_ctx) ((spec_call_object_seal_1 (l : value)) : ext_expr) (o : out))

  | red_spec_call_object_seal_2_cons :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (l : object_loc (* input *)) (xs : (list prop_name) (* input *)) (x : prop_name (* input *)) (o : out) (y : (specret full_descriptor)),
        (* ========================================== *)
        (red_spec S C (spec_object_get_own_prop (l : object_loc) (x : prop_name)) y) ->
        (red_expr (S : state) (C : execution_ctx) ((spec_call_object_seal_3 (l : object_loc) (x : prop_name) (xs : (list prop_name)) (y : (specret full_descriptor))) : ext_expr) (o : out)) ->
        (* ------------------------------------------ *)
        (red_expr (S : state) (C : execution_ctx) ((spec_call_object_seal_2 (l : object_loc) ((x :: (xs : (list prop_name))) : (list prop_name))) : ext_expr) (o : out))

  | red_spec_call_object_seal_3 :
      forall (S0 : state (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (l : object_loc (* input *)) (xs : (list prop_name) (* input *)) (x : prop_name (* input *)) (A : attributes (* input *)) (A' : attributes) (o1 : out) (o : out),
        (A' = ((ifb (attributes_configurable (A : attributes)) then ((attributes_with_configurable A false) : attributes) else A) : attributes)) ->
        (* ========================================== *)
        (red_expr (S : state) (C : execution_ctx) ((spec_object_define_own_prop (l : object_loc) (x : prop_name) ((descriptor_of_attributes A') : descriptor) (throw_true : bool)) : ext_expr) (o1 : out)) ->
        (red_expr (S : state) (C : execution_ctx) ((spec_call_object_seal_4 (l : object_loc) (xs : (list prop_name)) (o1 : out)) : ext_expr) (o : out)) ->
        (* ------------------------------------------ *)
        (red_expr (S0 : state) (C : execution_ctx) ((spec_call_object_seal_3 (l : object_loc) (x : prop_name) (xs : (list prop_name)) ((specret_val (S : state) (A : full_descriptor)) : (specret full_descriptor))) : ext_expr) (o : out))

  | red_spec_call_object_seal_4 :
      forall (S0 : state (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (l : object_loc (* input *)) (xs : (list prop_name) (* input *)) (b : bool (* input *)) (o : out),
        (* ========================================== *)
        (red_expr (S : state) (C : execution_ctx) ((spec_call_object_seal_2 (l : object_loc) (xs : (list prop_name))) : ext_expr) (o : out)) ->
        (* ------------------------------------------ *)
        (red_expr (S0 : state) (C : execution_ctx) ((spec_call_object_seal_4 (l : object_loc) (xs : (list prop_name)) ((out_ter (S : state) (b : res)) : out)) : ext_expr) (o : out))

  | red_spec_call_object_seal_2_nil :
      forall (S : state (* input *)) (S' : state) (C : execution_ctx (* input *)) (l : object_loc (* input *)),
        (object_heap_set_extensible (false : bool) (S : state) (l : object_loc) (S' : state)) ->
        (* ========================================== *)
        (* ------------------------------------------ *)
        (red_expr (S : state) (C : execution_ctx) ((spec_call_object_seal_2 (l : object_loc) (nil : (list prop_name))) : ext_expr) ((out_ter (S' : state) (l : res)) : out))

  | red_spec_call_object_freeze :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (v : value) (o : out) (vthis : value (* input *)) (args : (list value) (* input *)),
        (arguments_from (args : (list value)) ((v :: (nil : (list value))) : (list value))) ->
        (* ========================================== *)
        (red_expr (S : state) (C : execution_ctx) ((spec_call_object_freeze_1 (v : value)) : ext_expr) (o : out)) ->
        (* ------------------------------------------ *)
        (red_expr (S : state) (C : execution_ctx) ((spec_call_prealloc (prealloc_object_freeze : prealloc) (vthis : value) (args : (list value))) : ext_expr) (o : out))

  | red_spec_call_object_freeze_1_not_object :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (v : value (* input *)) (o : out),
        (((type_of v) : type) <> type_object) ->
        (* ========================================== *)
        (red_expr (S : state) (C : execution_ctx) ((spec_error (native_error_type : native_error)) : ext_expr) (o : out)) ->
        (* ------------------------------------------ *)
        (red_expr (S : state) (C : execution_ctx) ((spec_call_object_freeze_1 (v : value)) : ext_expr) (o : out))

  | red_spec_call_object_freeze_1_object :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (l : object_loc (* input *)) (xs : (list prop_name)) (o : out),
        (object_properties_keys_as_list S l xs) ->
        (* ========================================== *)
        (red_expr (S : state) (C : execution_ctx) ((spec_call_object_freeze_2 (l : object_loc) (xs : (list prop_name))) : ext_expr) (o : out)) ->
        (* ------------------------------------------ *)
        (red_expr (S : state) (C : execution_ctx) ((spec_call_object_freeze_1 (l : value)) : ext_expr) (o : out))

  | red_spec_call_object_freeze_2_cons :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (l : object_loc (* input *)) (xs : (list prop_name) (* input *)) (x : prop_name (* input *)) (o : out) (y : (specret full_descriptor)),
        (* ========================================== *)
        (red_spec S C (spec_object_get_own_prop (l : object_loc) (x : prop_name)) y) ->
        (red_expr (S : state) (C : execution_ctx) ((spec_call_object_freeze_3 (l : object_loc) (x : prop_name) (xs : (list prop_name)) (y : (specret full_descriptor))) : ext_expr) (o : out)) ->
        (* ------------------------------------------ *)
        (red_expr (S : state) (C : execution_ctx) ((spec_call_object_freeze_2 (l : object_loc) ((x :: (xs : (list prop_name))) : (list prop_name))) : ext_expr) (o : out))

  | red_spec_call_object_freeze_3 :
      forall (S0 : state (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (A : attributes (* input *)) (A' : attributes) (xs : (list prop_name) (* input *)) (l : object_loc (* input *)) (x : prop_name (* input *)) (o : out),
        (A' = match A return attributes with (attributes_data_of Ad) => (attributes_data_of ((ifb (attributes_data_writable (Ad : attributes_data)) then ((attributes_data_with_writable Ad false) : attributes_data) else Ad) : attributes_data)) | (attributes_accessor_of Aa) => (attributes_accessor_of (Aa : attributes_accessor)) end) ->
        (* ========================================== *)
        (red_expr (S : state) (C : execution_ctx) ((spec_call_object_freeze_4 (l : object_loc) (x : prop_name) (xs : (list prop_name)) (A' : full_descriptor)) : ext_expr) (o : out)) ->
        (* ------------------------------------------ *)
        (red_expr (S0 : state) (C : execution_ctx) ((spec_call_object_freeze_3 (l : object_loc) (x : prop_name) (xs : (list prop_name)) ((specret_val (S : state) (A : full_descriptor)) : (specret full_descriptor))) : ext_expr) (o : out))

  | red_spec_call_object_freeze_4 :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (A : attributes (* input *)) (A' : attributes) (xs : (list prop_name) (* input *)) (l : object_loc (* input *)) (x : prop_name (* input *)) (o1 : out) (o : out),
        (A' = ((ifb (attributes_configurable (A : attributes)) then ((attributes_with_configurable A false) : attributes) else A) : attributes)) ->
        (* ========================================== *)
        (red_expr (S : state) (C : execution_ctx) ((spec_object_define_own_prop (l : object_loc) (x : prop_name) ((descriptor_of_attributes A') : descriptor) (throw_true : bool)) : ext_expr) (o1 : out)) ->
        (red_expr (S : state) (C : execution_ctx) ((spec_call_object_freeze_5 (l : object_loc) (xs : (list prop_name)) (o1 : out)) : ext_expr) (o : out)) ->
        (* ------------------------------------------ *)
        (red_expr (S : state) (C : execution_ctx) ((spec_call_object_freeze_4 (l : object_loc) (x : prop_name) (xs : (list prop_name)) (A : full_descriptor)) : ext_expr) (o : out))

  | red_spec_call_object_freeze_5 :
      forall (S0 : state (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (xs : (list prop_name) (* input *)) (l : object_loc (* input *)) (b : bool (* input *)) (o : out),
        (* ========================================== *)
        (red_expr (S : state) (C : execution_ctx) ((spec_call_object_freeze_2 (l : object_loc) (xs : (list prop_name))) : ext_expr) (o : out)) ->
        (* ------------------------------------------ *)
        (red_expr (S0 : state) (C : execution_ctx) ((spec_call_object_freeze_5 (l : object_loc) (xs : (list prop_name)) ((out_ter (S : state) (b : res)) : out)) : ext_expr) (o : out))

  | red_spec_call_object_freeze_2_nil :
      forall (S : state (* input *)) (S' : state) (C : execution_ctx (* input *)) (l : object_loc (* input *)),
        (object_heap_set_extensible (false : bool) (S : state) (l : object_loc) (S' : state)) ->
        (* ========================================== *)
        (* ------------------------------------------ *)
        (red_expr (S : state) (C : execution_ctx) ((spec_call_object_freeze_2 (l : object_loc) (nil : (list prop_name))) : ext_expr) ((out_ter (S' : state) (l : res)) : out))

  | red_spec_call_object_prevent_extensions :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (v : value) (o : out) (vthis : value (* input *)) (args : (list value) (* input *)),
        (arguments_from (args : (list value)) ((v :: (nil : (list value))) : (list value))) ->
        (* ========================================== *)
        (red_expr (S : state) (C : execution_ctx) ((spec_call_object_prevent_extensions_1 (v : value)) : ext_expr) (o : out)) ->
        (* ------------------------------------------ *)
        (red_expr (S : state) (C : execution_ctx) ((spec_call_prealloc (prealloc_object_prevent_extensions : prealloc) (vthis : value) (args : (list value))) : ext_expr) (o : out))

  | red_spec_call_object_prevent_extensions_not_object :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (v : value (* input *)) (o : out),
        (((type_of v) : type) <> type_object) ->
        (* ========================================== *)
        (red_expr (S : state) (C : execution_ctx) ((spec_error (native_error_type : native_error)) : ext_expr) (o : out)) ->
        (* ------------------------------------------ *)
        (red_expr (S : state) (C : execution_ctx) ((spec_call_object_prevent_extensions_1 (v : value)) : ext_expr) (o : out))

  | red_spec_call_object_prevent_extensions_object :
      forall (S : state (* input *)) (S' : state) (C : execution_ctx (* input *)) (O : object) (O' : object) (l : object_loc (* input *)),
        (object_binds (S : state) (l : object_loc) (O : object)) ->
        (O' = ((object_with_extension O false) : object)) ->
        (S' = ((object_write S l O') : state)) ->
        (* ========================================== *)
        (* ------------------------------------------ *)
        (red_expr (S : state) (C : execution_ctx) ((spec_call_object_prevent_extensions_1 (l : value)) : ext_expr) ((out_ter (S' : state) (l : res)) : out))

  | red_spec_call_object_is_sealed :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (v : value) (o : out) (vthis : value (* input *)) (args : (list value) (* input *)),
        (arguments_from (args : (list value)) ((v :: (nil : (list value))) : (list value))) ->
        (* ========================================== *)
        (red_expr (S : state) (C : execution_ctx) ((spec_call_object_is_sealed_1 (v : value)) : ext_expr) (o : out)) ->
        (* ------------------------------------------ *)
        (red_expr (S : state) (C : execution_ctx) ((spec_call_prealloc (prealloc_object_is_sealed : prealloc) (vthis : value) (args : (list value))) : ext_expr) (o : out))

  | red_spec_call_object_is_sealed_1_not_object :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (v : value (* input *)) (o : out),
        (((type_of v) : type) <> type_object) ->
        (* ========================================== *)
        (red_expr (S : state) (C : execution_ctx) ((spec_error (native_error_type : native_error)) : ext_expr) (o : out)) ->
        (* ------------------------------------------ *)
        (red_expr (S : state) (C : execution_ctx) ((spec_call_object_is_sealed_1 (v : value)) : ext_expr) (o : out))

  | red_spec_call_object_is_sealed_1_object :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (l : object_loc (* input *)) (xs : (list prop_name)) (o : out),
        (object_properties_keys_as_list S l xs) ->
        (* ========================================== *)
        (red_expr (S : state) (C : execution_ctx) ((spec_call_object_is_sealed_2 (l : object_loc) (xs : (list prop_name))) : ext_expr) (o : out)) ->
        (* ------------------------------------------ *)
        (red_expr (S : state) (C : execution_ctx) ((spec_call_object_is_sealed_1 (l : value)) : ext_expr) (o : out))

  | red_spec_call_object_is_sealed_2_cons :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (l : object_loc (* input *)) (xs : (list prop_name) (* input *)) (x : prop_name (* input *)) (o : out) (y : (specret full_descriptor)),
        (* ========================================== *)
        (red_spec S C (spec_object_get_own_prop (l : object_loc) (x : prop_name)) y) ->
        (red_expr (S : state) (C : execution_ctx) ((spec_call_object_is_sealed_3 (l : object_loc) (xs : (list prop_name)) (y : (specret full_descriptor))) : ext_expr) (o : out)) ->
        (* ------------------------------------------ *)
        (red_expr (S : state) (C : execution_ctx) ((spec_call_object_is_sealed_2 (l : object_loc) ((x :: (xs : (list prop_name))) : (list prop_name))) : ext_expr) (o : out))

  | red_spec_call_object_is_sealed_3_prop_configurable :
      forall (S0 : state (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (A : attributes (* input *)) (xs : (list prop_name) (* input *)) (l : object_loc (* input *)),
        ((attributes_configurable (A : attributes)) = (true : bool)) ->
        (* ========================================== *)
        (* ------------------------------------------ *)
        (red_expr (S0 : state) (C : execution_ctx) ((spec_call_object_is_sealed_3 (l : object_loc) (xs : (list prop_name)) ((specret_val (S : state) (A : full_descriptor)) : (specret full_descriptor))) : ext_expr) ((out_ter (S : state) (false : res)) : out))

  | red_spec_call_object_is_sealed_3_prop_not_configurable :
      forall (S0 : state (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (A : attributes (* input *)) (xs : (list prop_name) (* input *)) (l : object_loc (* input *)) (o : out),
        ((attributes_configurable (A : attributes)) = (false : bool)) ->
        (* ========================================== *)
        (red_expr (S : state) (C : execution_ctx) ((spec_call_object_is_sealed_2 (l : object_loc) (xs : (list prop_name))) : ext_expr) (o : out)) ->
        (* ------------------------------------------ *)
        (red_expr (S0 : state) (C : execution_ctx) ((spec_call_object_is_sealed_3 (l : object_loc) (xs : (list prop_name)) ((specret_val (S : state) (A : full_descriptor)) : (specret full_descriptor))) : ext_expr) (o : out))

  | red_spec_call_object_is_sealed_2_nil :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (l : object_loc (* input *)) (b : bool),
        (object_extensible (S : state) (l : object_loc) (b : bool)) ->
        (* ========================================== *)
        (* ------------------------------------------ *)
        (red_expr (S : state) (C : execution_ctx) ((spec_call_object_is_sealed_2 (l : object_loc) (nil : (list prop_name))) : ext_expr) ((out_ter (S : state) ((negb b) : res)) : out))

  | red_spec_call_object_is_frozen :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (v : value) (o : out) (vthis : value (* input *)) (args : (list value) (* input *)),
        (arguments_from (args : (list value)) ((v :: (nil : (list value))) : (list value))) ->
        (* ========================================== *)
        (red_expr (S : state) (C : execution_ctx) ((spec_call_object_is_frozen_1 (v : value)) : ext_expr) (o : out)) ->
        (* ------------------------------------------ *)
        (red_expr (S : state) (C : execution_ctx) ((spec_call_prealloc (prealloc_object_is_frozen : prealloc) (vthis : value) (args : (list value))) : ext_expr) (o : out))

  | red_spec_call_object_is_frozen_1_not_object :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (v : value (* input *)) (o : out),
        (((type_of v) : type) <> type_object) ->
        (* ========================================== *)
        (red_expr (S : state) (C : execution_ctx) ((spec_error (native_error_type : native_error)) : ext_expr) (o : out)) ->
        (* ------------------------------------------ *)
        (red_expr (S : state) (C : execution_ctx) ((spec_call_object_is_frozen_1 (v : value)) : ext_expr) (o : out))

  | red_spec_call_object_is_frozen_1_object :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (l : object_loc (* input *)) (xs : (list prop_name)) (o : out),
        (object_properties_keys_as_list S l xs) ->
        (* ========================================== *)
        (red_expr (S : state) (C : execution_ctx) ((spec_call_object_is_frozen_2 (l : object_loc) (xs : (list prop_name))) : ext_expr) (o : out)) ->
        (* ------------------------------------------ *)
        (red_expr (S : state) (C : execution_ctx) ((spec_call_object_is_frozen_1 (l : value)) : ext_expr) (o : out))

  | red_spec_call_object_is_frozen_2_cons :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (l : object_loc (* input *)) (xs : (list prop_name) (* input *)) (x : prop_name (* input *)) (o : out) (y : (specret full_descriptor)),
        (* ========================================== *)
        (red_spec S C (spec_object_get_own_prop (l : object_loc) (x : prop_name)) y) ->
        (red_expr (S : state) (C : execution_ctx) ((spec_call_object_is_frozen_3 (l : object_loc) (xs : (list prop_name)) (y : (specret full_descriptor))) : ext_expr) (o : out)) ->
        (* ------------------------------------------ *)
        (red_expr (S : state) (C : execution_ctx) ((spec_call_object_is_frozen_2 (l : object_loc) ((x :: (xs : (list prop_name))) : (list prop_name))) : ext_expr) (o : out))

  | red_spec_call_object_is_frozen_3_desc_is_data :
      forall (S0 : state (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (A : attributes (* input *)) (xs : (list prop_name) (* input *)) (l : object_loc (* input *)) (o : out),
        (attributes_is_data (A : attributes)) ->
        (* ========================================== *)
        (red_expr (S : state) (C : execution_ctx) ((spec_call_object_is_frozen_4 (l : object_loc) (xs : (list prop_name)) (A : full_descriptor)) : ext_expr) (o : out)) ->
        (* ------------------------------------------ *)
        (red_expr (S0 : state) (C : execution_ctx) ((spec_call_object_is_frozen_3 (l : object_loc) (xs : (list prop_name)) ((specret_val (S : state) (A : full_descriptor)) : (specret full_descriptor))) : ext_expr) (o : out))

  | red_spec_call_object_is_frozen_3_desc_is_not_data :
      forall (S0 : state (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (A : attributes (* input *)) (xs : (list prop_name) (* input *)) (l : object_loc (* input *)) (o : out),
        (~ (attributes_is_data (A : attributes))) ->
        (* ========================================== *)
        (red_expr (S : state) (C : execution_ctx) ((spec_call_object_is_frozen_5 (l : object_loc) (xs : (list prop_name)) (A : full_descriptor)) : ext_expr) (o : out)) ->
        (* ------------------------------------------ *)
        (red_expr (S0 : state) (C : execution_ctx) ((spec_call_object_is_frozen_3 (l : object_loc) (xs : (list prop_name)) ((specret_val (S : state) (A : full_descriptor)) : (specret full_descriptor))) : ext_expr) (o : out))

  | red_spec_call_object_is_frozen_4_prop_is_writable :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (A : attributes (* input *)) (xs : (list prop_name) (* input *)) (l : object_loc (* input *)),
        ((attributes_writable (A : attributes)) = (true : bool)) ->
        (* ========================================== *)
        (* ------------------------------------------ *)
        (red_expr (S : state) (C : execution_ctx) ((spec_call_object_is_frozen_4 (l : object_loc) (xs : (list prop_name)) (A : full_descriptor)) : ext_expr) ((out_ter (S : state) (false : res)) : out))

  | red_spec_call_object_is_frozen_4_prop_is_not_writable :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (A : attributes (* input *)) (xs : (list prop_name) (* input *)) (l : object_loc (* input *)) (o : out),
        ((attributes_writable (A : attributes)) = (false : bool)) ->
        (* ========================================== *)
        (red_expr (S : state) (C : execution_ctx) ((spec_call_object_is_frozen_5 (l : object_loc) (xs : (list prop_name)) (A : full_descriptor)) : ext_expr) (o : out)) ->
        (* ------------------------------------------ *)
        (red_expr (S : state) (C : execution_ctx) ((spec_call_object_is_frozen_4 (l : object_loc) (xs : (list prop_name)) (A : full_descriptor)) : ext_expr) (o : out))

  | red_spec_call_object_is_frozen_5_prop_configurable :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (A : attributes (* input *)) (xs : (list prop_name) (* input *)) (l : object_loc (* input *)),
        ((attributes_configurable (A : attributes)) = (true : bool)) ->
        (* ========================================== *)
        (* ------------------------------------------ *)
        (red_expr (S : state) (C : execution_ctx) ((spec_call_object_is_frozen_5 (l : object_loc) (xs : (list prop_name)) (A : full_descriptor)) : ext_expr) ((out_ter (S : state) (false : res)) : out))

  | red_spec_call_object_is_frozen_5_prop_not_configurable :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (A : attributes (* input *)) (xs : (list prop_name) (* input *)) (l : object_loc (* input *)) (o : out),
        ((attributes_configurable (A : attributes)) = (false : bool)) ->
        (* ========================================== *)
        (red_expr (S : state) (C : execution_ctx) ((spec_call_object_is_frozen_2 (l : object_loc) (xs : (list prop_name))) : ext_expr) (o : out)) ->
        (* ------------------------------------------ *)
        (red_expr (S : state) (C : execution_ctx) ((spec_call_object_is_frozen_5 (l : object_loc) (xs : (list prop_name)) (A : full_descriptor)) : ext_expr) (o : out))

  | red_spec_call_object_is_frozen_2_nil :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (l : object_loc (* input *)) (b : bool),
        (object_extensible (S : state) (l : object_loc) (b : bool)) ->
        (* ========================================== *)
        (* ------------------------------------------ *)
        (red_expr (S : state) (C : execution_ctx) ((spec_call_object_is_frozen_2 (l : object_loc) (nil : (list prop_name))) : ext_expr) ((out_ter (S : state) ((negb b) : res)) : out))

  | red_spec_call_object_is_extensible :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (v : value) (o : out) (vthis : value (* input *)) (args : (list value) (* input *)),
        (arguments_from (args : (list value)) ((v :: (nil : (list value))) : (list value))) ->
        (* ========================================== *)
        (red_expr (S : state) (C : execution_ctx) ((spec_call_object_is_extensible_1 (v : value)) : ext_expr) (o : out)) ->
        (* ------------------------------------------ *)
        (red_expr (S : state) (C : execution_ctx) ((spec_call_prealloc (prealloc_object_is_extensible : prealloc) (vthis : value) (args : (list value))) : ext_expr) (o : out))

  | red_spec_call_object_is_extensible_1_not_object :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (v : value (* input *)) (o : out),
        (((type_of v) : type) <> type_object) ->
        (* ========================================== *)
        (red_expr (S : state) (C : execution_ctx) ((spec_error (native_error_type : native_error)) : ext_expr) (o : out)) ->
        (* ------------------------------------------ *)
        (red_expr (S : state) (C : execution_ctx) ((spec_call_object_is_extensible_1 (v : value)) : ext_expr) (o : out))

  | red_spec_call_object_is_extensible_1_object :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (l : object_loc (* input *)) (b : bool),
        (object_extensible (S : state) (l : object_loc) (b : bool)) ->
        (* ========================================== *)
        (* ------------------------------------------ *)
        (red_expr (S : state) (C : execution_ctx) ((spec_call_object_is_extensible_1 (l : value)) : ext_expr) ((out_ter (S : state) (b : res)) : out))

  | red_spec_call_object_proto_to_string :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (vthis : value (* input *)) (args : (list value) (* input *)) (o : out),
        (* ========================================== *)
        (red_expr (S : state) (C : execution_ctx) ((spec_call_object_proto_to_string_1 (vthis : value)) : ext_expr) (o : out)) ->
        (* ------------------------------------------ *)
        (red_expr (S : state) (C : execution_ctx) ((spec_call_prealloc (prealloc_object_proto_to_string : prealloc) (vthis : value) (args : (list value))) : ext_expr) (o : out))

  | red_spec_call_object_proto_to_string_1_undef :
      forall (S : state (* input *)) (C : execution_ctx (* input *)),
        (* ========================================== *)
        (* ------------------------------------------ *)
        (red_expr (S : state) (C : execution_ctx) ((spec_call_object_proto_to_string_1 (undef : value)) : ext_expr) ((out_ter (S : state) ((("[object Undefined]")%string) : res)) : out))

  | red_spec_call_object_proto_to_string_1_null :
      forall (S : state (* input *)) (C : execution_ctx (* input *)),
        (* ========================================== *)
        (* ------------------------------------------ *)
        (red_expr (S : state) (C : execution_ctx) ((spec_call_object_proto_to_string_1 (null : value)) : ext_expr) ((out_ter (S : state) ((("[object Null]")%string) : res)) : out))

  | red_spec_call_object_proto_to_string_1_other :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (v : value (* input *)) (o : out) (o1 : out),
        (~ (((v = null) : Prop) \/ ((v = undef) : Prop))) ->
        (* ========================================== *)
        (red_expr (S : state) (C : execution_ctx) ((spec_to_object (v : value)) : ext_expr) (o1 : out)) ->
        (red_expr (S : state) (C : execution_ctx) ((spec_call_object_proto_to_string_2 (o1 : out)) : ext_expr) (o : out)) ->
        (* ------------------------------------------ *)
        (red_expr (S : state) (C : execution_ctx) ((spec_call_object_proto_to_string_1 (v : value)) : ext_expr) (o : out))

  | red_spec_call_object_proto_to_string_2 :
      forall (S0 : state (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (l : object_loc (* input *)) (s : string) (sclass : string),
        (object_class (S : state) (l : object_loc) (sclass : string)) ->
        (s = (((("[object ")%string) ++ (((sclass : string) ++ (("]")%string)) : string)) : string)) ->
        (* ========================================== *)
        (* ------------------------------------------ *)
        (red_expr (S0 : state) (C : execution_ctx) ((spec_call_object_proto_to_string_2 ((out_ter (S : state) (l : res)) : out)) : ext_expr) ((out_ter (S : state) (s : res)) : out))

  | red_spec_call_object_proto_value_of :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (vthis : value (* input *)) (args : (list value) (* input *)) (o : out),
        (* ========================================== *)
        (red_expr (S : state) (C : execution_ctx) ((spec_to_object (vthis : value)) : ext_expr) (o : out)) ->
        (* ------------------------------------------ *)
        (red_expr (S : state) (C : execution_ctx) ((spec_call_prealloc (prealloc_object_proto_value_of : prealloc) (vthis : value) (args : (list value))) : ext_expr) (o : out))

  | red_spec_call_object_proto_has_own_prop :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (v : value) (vthis : value (* input *)) (args : (list value) (* input *)) (o : out) (o1 : out),
        (arguments_from (args : (list value)) ((v :: (nil : (list value))) : (list value))) ->
        (* ========================================== *)
        (red_expr (S : state) (C : execution_ctx) ((spec_to_string (v : value)) : ext_expr) (o1 : out)) ->
        (red_expr (S : state) (C : execution_ctx) ((spec_call_object_proto_has_own_prop_1 (o1 : out) (vthis : value)) : ext_expr) (o : out)) ->
        (* ------------------------------------------ *)
        (red_expr (S : state) (C : execution_ctx) ((spec_call_prealloc (prealloc_object_proto_has_own_prop : prealloc) (vthis : value) (args : (list value))) : ext_expr) (o : out))

  | red_spec_call_object_proto_has_own_prop_1 :
      forall (S : state (* input *)) (S' : state (* input *)) (C : execution_ctx (* input *)) (vthis : value (* input *)) (s : string (* input *)) (o : out) (o1 : out),
        (* ========================================== *)
        (red_expr (S' : state) (C : execution_ctx) ((spec_to_object (vthis : value)) : ext_expr) (o1 : out)) ->
        (red_expr (S' : state) (C : execution_ctx) ((spec_call_object_proto_has_own_prop_2 (o1 : out) (s : prop_name)) : ext_expr) (o : out)) ->
        (* ------------------------------------------ *)
        (red_expr (S : state) (C : execution_ctx) ((spec_call_object_proto_has_own_prop_1 ((out_ter (S' : state) (s : res)) : out) (vthis : value)) : ext_expr) (o : out))

  | red_spec_call_object_proto_has_own_prop_2 :
      forall (S : state (* input *)) (S' : state (* input *)) (C : execution_ctx (* input *)) (l : object_loc (* input *)) (s : string (* input *)) (o : out) (y : (specret full_descriptor)),
        (* ========================================== *)
        (red_spec S' C (spec_object_get_own_prop (l : object_loc) (s : prop_name)) y) ->
        (red_expr (S' : state) (C : execution_ctx) ((spec_call_object_proto_has_own_prop_3 (y : (specret full_descriptor))) : ext_expr) (o : out)) ->
        (* ------------------------------------------ *)
        (red_expr (S : state) (C : execution_ctx) ((spec_call_object_proto_has_own_prop_2 ((out_ter (S' : state) (l : res)) : out) (s : prop_name)) : ext_expr) (o : out))

  | red_spec_call_object_proto_has_own_prop_3_undef :
      forall (S : state (* input *)) (S' : state (* input *)) (C : execution_ctx (* input *)),
        (* ========================================== *)
        (* ------------------------------------------ *)
        (red_expr (S : state) (C : execution_ctx) ((spec_call_object_proto_has_own_prop_3 ((specret_val S' full_descriptor_undef) : (specret full_descriptor))) : ext_expr) ((out_ter (S' : state) (false : res)) : out))

  | red_spec_call_object_proto_has_own_prop_3_not_undef :
      forall (S : state (* input *)) (S' : state (* input *)) (C : execution_ctx (* input *)) (A : attributes (* input *)),
        (* ========================================== *)
        (* ------------------------------------------ *)
        (red_expr (S : state) (C : execution_ctx) ((spec_call_object_proto_has_own_prop_3 ((specret_val (S' : state) (A : full_descriptor)) : (specret full_descriptor))) : ext_expr) ((out_ter (S' : state) (true : res)) : out))

  | red_spec_call_object_proto_is_prototype_of_not_object :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (vthis : value (* input *)) (args : (list value) (* input *)) (v : value) (o : out),
        (arguments_from (args : (list value)) ((v :: (nil : (list value))) : (list value))) ->
        (* ========================================== *)
        (red_expr (S : state) (C : execution_ctx) ((spec_call_object_proto_is_prototype_of_2_1 (v : value) (vthis : value)) : ext_expr) (o : out)) ->
        (* ------------------------------------------ *)
        (red_expr (S : state) (C : execution_ctx) ((spec_call_prealloc (prealloc_object_proto_is_prototype_of : prealloc) (vthis : value) (args : (list value))) : ext_expr) (o : out))

  | red_spec_call_object_proto_is_prototype_of_1_not_object :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (v : value (* input *)) (vthis : value (* input *)),
        (((type_of v) : type) <> type_object) ->
        (* ========================================== *)
        (* ------------------------------------------ *)
        (red_expr (S : state) (C : execution_ctx) ((spec_call_object_proto_is_prototype_of_2_1 (v : value) (vthis : value)) : ext_expr) ((out_ter (S : state) (false : res)) : out))

  | red_spec_call_object_proto_is_prototype_of_1_object :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (l : object_loc (* input *)) (vthis : value (* input *)) (o1 : out) (o : out),
        (* ========================================== *)
        (red_expr (S : state) (C : execution_ctx) ((spec_to_object (vthis : value)) : ext_expr) (o1 : out)) ->
        (red_expr (S : state) (C : execution_ctx) ((spec_call_object_proto_is_prototype_of_2_2 (o1 : out) (l : object_loc)) : ext_expr) (o : out)) ->
        (* ------------------------------------------ *)
        (red_expr (S : state) (C : execution_ctx) ((spec_call_object_proto_is_prototype_of_2_1 (l : value) (vthis : value)) : ext_expr) (o : out))

  | red_spec_call_object_proto_is_prototype_of_2 :
      forall (S0 : state (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (l : object_loc (* input *)) (lthis : object_loc (* input *)) (o : out),
        (* ========================================== *)
        (red_expr (S : state) (C : execution_ctx) ((spec_call_object_proto_is_prototype_of_2_3 (lthis : object_loc) (l : object_loc)) : ext_expr) (o : out)) ->
        (* ------------------------------------------ *)
        (red_expr (S0 : state) (C : execution_ctx) ((spec_call_object_proto_is_prototype_of_2_2 ((out_ter (S : state) (lthis : res)) : out) (l : object_loc)) : ext_expr) (o : out))

  | red_spec_call_object_proto_is_prototype_of_3 :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (l : object_loc (* input *)) (lthis : object_loc (* input *)) (vproto : value) (o : out),
        (object_proto (S : state) (l : object_loc) (vproto : value)) ->
        (* ========================================== *)
        (red_expr (S : state) (C : execution_ctx) ((spec_call_object_proto_is_prototype_of_2_4 (lthis : object_loc) (vproto : value)) : ext_expr) (o : out)) ->
        (* ------------------------------------------ *)
        (red_expr (S : state) (C : execution_ctx) ((spec_call_object_proto_is_prototype_of_2_3 (lthis : object_loc) (l : object_loc)) : ext_expr) (o : out))

  | red_spec_call_object_proto_is_prototype_of_4_null :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (lthis : object_loc (* input *)),
        (* ========================================== *)
        (* ------------------------------------------ *)
        (red_expr (S : state) (C : execution_ctx) ((spec_call_object_proto_is_prototype_of_2_4 (lthis : object_loc) (null : value)) : ext_expr) ((out_ter (S : state) (false : res)) : out))

  | red_spec_call_object_proto_is_prototype_of_4_equal :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (lthis : object_loc (* input *)),
        (* ========================================== *)
        (* ------------------------------------------ *)
        (red_expr (S : state) (C : execution_ctx) ((spec_call_object_proto_is_prototype_of_2_4 (lthis : object_loc) (lthis : value)) : ext_expr) ((out_ter (S : state) (true : res)) : out))

  | red_spec_call_object_proto_is_prototype_of_4_not_equal :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (lthis : object_loc (* input *)) (lproto : object_loc (* input *)) (o : out),
        (lproto <> lthis) ->
        (* ========================================== *)
        (red_expr (S : state) (C : execution_ctx) ((spec_call_object_proto_is_prototype_of_2_3 (lthis : object_loc) (lproto : object_loc)) : ext_expr) (o : out)) ->
        (* ------------------------------------------ *)
        (red_expr (S : state) (C : execution_ctx) ((spec_call_object_proto_is_prototype_of_2_4 (lthis : object_loc) (lproto : value)) : ext_expr) (o : out))

  | red_spec_call_object_proto_prop_is_enumerable :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (v : value) (o : out) (vthis : value (* input *)) (args : (list value) (* input *)),
        (arguments_from (args : (list value)) ((v :: (nil : (list value))) : (list value))) ->
        (* ========================================== *)
        (red_expr (S : state) (C : execution_ctx) ((spec_call_object_proto_prop_is_enumerable_1 (v : value) (vthis : value)) : ext_expr) (o : out)) ->
        (* ------------------------------------------ *)
        (red_expr (S : state) (C : execution_ctx) ((spec_call_prealloc (prealloc_object_proto_prop_is_enumerable : prealloc) (vthis : value) (args : (list value))) : ext_expr) (o : out))

  | red_spec_call_object_proto_prop_is_enumerable_1 :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (v : value (* input *)) (vthis : value (* input *)) (o : out) (o1 : out),
        (* ========================================== *)
        (red_expr (S : state) (C : execution_ctx) ((spec_to_string (v : value)) : ext_expr) (o1 : out)) ->
        (red_expr (S : state) (C : execution_ctx) ((spec_call_object_proto_prop_is_enumerable_2 (vthis : value) (o1 : out)) : ext_expr) (o : out)) ->
        (* ------------------------------------------ *)
        (red_expr (S : state) (C : execution_ctx) ((spec_call_object_proto_prop_is_enumerable_1 (v : value) (vthis : value)) : ext_expr) (o : out))

  | red_spec_call_object_proto_prop_is_enumerable_2 :
      forall (S : state (* input *)) (S' : state (* input *)) (C : execution_ctx (* input *)) (vthis : value (* input *)) (s : string (* input *)) (o : out) (o1 : out),
        (* ========================================== *)
        (red_expr (S' : state) (C : execution_ctx) ((spec_to_object (vthis : value)) : ext_expr) (o1 : out)) ->
        (red_expr (S' : state) (C : execution_ctx) ((spec_call_object_proto_prop_is_enumerable_3 (o1 : out) (s : string)) : ext_expr) (o : out)) ->
        (* ------------------------------------------ *)
        (red_expr (S : state) (C : execution_ctx) ((spec_call_object_proto_prop_is_enumerable_2 (vthis : value) ((out_ter (S' : state) (s : res)) : out)) : ext_expr) (o : out))

  | red_spec_call_object_proto_prop_is_enumerable_3 :
      forall (S : state (* input *)) (S' : state (* input *)) (C : execution_ctx (* input *)) (l : object_loc (* input *)) (x : prop_name (* input *)) (o : out) (y : (specret full_descriptor)),
        (* ========================================== *)
        (red_spec S' C (spec_object_get_own_prop (l : object_loc) (x : prop_name)) y) ->
        (red_expr (S' : state) (C : execution_ctx) ((spec_call_object_proto_prop_is_enumerable_4 (y : (specret full_descriptor))) : ext_expr) (o : out)) ->
        (* ------------------------------------------ *)
        (red_expr (S : state) (C : execution_ctx) ((spec_call_object_proto_prop_is_enumerable_3 ((out_ter (S' : state) (l : res)) : out) (x : string)) : ext_expr) (o : out))

  | red_spec_call_object_proto_prop_is_enumerable_4_undef :
      forall (S0 : state (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)),
        (* ========================================== *)
        (* ------------------------------------------ *)
        (red_expr (S : state) (C : execution_ctx) ((spec_call_object_proto_prop_is_enumerable_4 ((specret_val (S0 : state) (full_descriptor_undef : full_descriptor)) : (specret full_descriptor))) : ext_expr) ((out_ter (S0 : state) (false : res)) : out))

  | red_spec_call_object_proto_prop_is_enumerable_4_not_undef :
      forall (S0 : state (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (A : attributes (* input *)) (b : bool),
        (b = ((attributes_enumerable (A : attributes)) : bool)) ->
        (* ========================================== *)
        (* ------------------------------------------ *)
        (red_expr (S : state) (C : execution_ctx) ((spec_call_object_proto_prop_is_enumerable_4 ((specret_val (S0 : state) (A : full_descriptor)) : (specret full_descriptor))) : ext_expr) ((out_ter (S0 : state) (b : res)) : out))

  | red_spec_call_function_proto_invoked :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (vthis : value (* input *)) (args : (list value) (* input *)),
        (* ========================================== *)
        (* ------------------------------------------ *)
        (red_expr (S : state) (C : execution_ctx) ((spec_call_prealloc (prealloc_function_proto : prealloc) (vthis : value) (args : (list value))) : ext_expr) ((out_ter (S : state) (undef : res)) : out))

  | red_spec_object_get_1_function :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (vthis : value (* input *)) (l : object_loc (* input *)) (x : prop_name (* input *)) (o1 : out) (o : out),
        (* ========================================== *)
        (red_expr (S : state) (C : execution_ctx) ((spec_object_get_1 (builtin_get_default : builtin_get) (vthis : value) (l : object_loc) (x : prop_name)) : ext_expr) (o1 : out)) ->
        (red_expr (S : state) (C : execution_ctx) ((spec_function_get_1 (l : object_loc) (x : prop_name) (o1 : out)) : ext_expr) (o : out)) ->
        (* ------------------------------------------ *)
        (red_expr (S : state) (C : execution_ctx) ((spec_object_get_1 (builtin_get_function : builtin_get) (vthis : value) (l : object_loc) (x : prop_name)) : ext_expr) (o : out))

  | red_spec_function_get_1_error :
      forall (S0 : state (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (l : object_loc (* input *)) (x : prop_name (* input *)) (v : value (* input *)) (o : out),
        (spec_function_get_error_case (S : state) (x : prop_name) (v : value)) ->
        (* ========================================== *)
        (red_expr (S : state) (C : execution_ctx) ((spec_error (native_error_type : native_error)) : ext_expr) (o : out)) ->
        (* ------------------------------------------ *)
        (red_expr (S0 : state) (C : execution_ctx) ((spec_function_get_1 (l : object_loc) (x : prop_name) ((out_ter (S : state) (v : res)) : out)) : ext_expr) (o : out))

  | red_spec_function_get_1_normal :
      forall (S0 : state (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (l : object_loc (* input *)) (x : prop_name (* input *)) (v : value (* input *)),
        (~ (spec_function_get_error_case (S : state) (x : prop_name) (v : value))) ->
        (* ========================================== *)
        (* ------------------------------------------ *)
        (red_expr (S0 : state) (C : execution_ctx) ((spec_function_get_1 (l : object_loc) (x : prop_name) ((out_ter (S : state) (v : res)) : out)) : ext_expr) ((out_ter (S : state) (v : res)) : out))

  | red_spec_object_has_instance_1_function_prim :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (l : object_loc (* input *)) (w : prim (* input *)),
        (* ========================================== *)
        (* ------------------------------------------ *)
        (red_expr (S : state) (C : execution_ctx) ((spec_object_has_instance_1 (builtin_has_instance_function : builtin_has_instance) (l : object_loc) ((value_prim (w : prim)) : value)) : ext_expr) ((out_ter (S : state) (false : res)) : out))

  | red_spec_object_has_instance_1_function_object :
      forall (o1 : out) (S : state (* input *)) (C : execution_ctx (* input *)) (l : object_loc (* input *)) (lv : object_loc (* input *)) (o : out),
        (* ========================================== *)
        (red_expr (S : state) (C : execution_ctx) ((spec_object_get (l : value) ((("prototype")%string) : prop_name)) : ext_expr) (o1 : out)) ->
        (red_expr (S : state) (C : execution_ctx) ((spec_function_has_instance_1 (lv : object_loc) (o1 : out)) : ext_expr) (o : out)) ->
        (* ------------------------------------------ *)
        (red_expr (S : state) (C : execution_ctx) ((spec_object_has_instance_1 (builtin_has_instance_function : builtin_has_instance) (l : object_loc) ((value_object (lv : object_loc)) : value)) : ext_expr) (o : out))

  | red_spec_function_has_instance_1_prim :
      forall (S0 : state (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (lv : object_loc (* input *)) (v : value (* input *)) (o : out),
        (((type_of v) : type) <> type_object) ->
        (* ========================================== *)
        (red_expr (S : state) (C : execution_ctx) ((spec_error (native_error_type : native_error)) : ext_expr) (o : out)) ->
        (* ------------------------------------------ *)
        (red_expr (S0 : state) (C : execution_ctx) ((spec_function_has_instance_1 (lv : object_loc) ((out_ter (S : state) (v : res)) : out)) : ext_expr) (o : out))

  | red_spec_function_has_instance_1_object :
      forall (S0 : state (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (lv : object_loc (* input *)) (lo : object_loc (* input *)) (o : out),
        (* ========================================== *)
        (red_expr (S : state) (C : execution_ctx) ((spec_function_has_instance_2 (lo : object_loc) (lv : object_loc)) : ext_expr) (o : out)) ->
        (* ------------------------------------------ *)
        (red_expr (S0 : state) (C : execution_ctx) ((spec_function_has_instance_1 (lv : object_loc) ((out_ter (S : state) ((value_object (lo : object_loc)) : res)) : out)) : ext_expr) (o : out))

  | red_spec_function_has_instance_2 :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (lo : object_loc (* input *)) (lv : object_loc (* input *)) (vproto : value) (o : out),
        (object_proto (S : state) (lv : object_loc) (vproto : value)) ->
        (* ========================================== *)
        (red_expr (S : state) (C : execution_ctx) ((spec_function_has_instance_3 (lo : object_loc) (vproto : value)) : ext_expr) (o : out)) ->
        (* ------------------------------------------ *)
        (red_expr (S : state) (C : execution_ctx) ((spec_function_has_instance_2 (lo : object_loc) (lv : object_loc)) : ext_expr) (o : out))

  | red_spec_function_has_instance_3_null :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (lo : object_loc (* input *)),
        (* ========================================== *)
        (* ------------------------------------------ *)
        (red_expr (S : state) (C : execution_ctx) ((spec_function_has_instance_3 (lo : object_loc) (null : value)) : ext_expr) ((out_ter (S : state) (false : res)) : out))

  | red_spec_function_has_instance_3_eq :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (lo : object_loc (* input *)) (lv : value (* input *)),
        (lv = lo) ->
        (* ========================================== *)
        (* ------------------------------------------ *)
        (red_expr (S : state) (C : execution_ctx) ((spec_function_has_instance_3 (lo : object_loc) (lv : value)) : ext_expr) ((out_ter (S : state) (true : res)) : out))

  | red_spec_function_has_instance_3_neq :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (lo : object_loc (* input *)) (lv : object_loc (* input *)) (o : out),
        (lv <> lo) ->
        (* ========================================== *)
        (red_expr (S : state) (C : execution_ctx) ((spec_function_has_instance_2 (lo : object_loc) (lv : object_loc)) : ext_expr) (o : out)) ->
        (* ------------------------------------------ *)
        (red_expr (S : state) (C : execution_ctx) ((spec_function_has_instance_3 (lo : object_loc) (lv : value)) : ext_expr) (o : out))

  | red_spec_call_array_new_no_args :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (args : (list value) (* input *)) (o : out),
        (args = nil) ->
        (* ========================================== *)
        (red_expr (S : state) (C : execution_ctx) ((spec_call_array_new_1 (args : (list value))) : ext_expr) (o : out)) ->
        (* ------------------------------------------ *)
        (red_expr (S : state) (C : execution_ctx) ((spec_construct_prealloc (prealloc_array : prealloc) (args : (list value))) : ext_expr) (o : out))

  | red_spec_call_array_new_multiple_args :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (args : (list value) (* input *)) (v1 : value) (v2 : value) (vs : (list value)) (o : out),
        ((args : (list value)) = (v1 :: ((v2 :: (vs : (list value))) : (list value)))) ->
        (* ========================================== *)
        (red_expr (S : state) (C : execution_ctx) ((spec_call_array_new_1 (args : (list value))) : ext_expr) (o : out)) ->
        (* ------------------------------------------ *)
        (red_expr (S : state) (C : execution_ctx) ((spec_construct_prealloc (prealloc_array : prealloc) (args : (list value))) : ext_expr) (o : out))

  | red_spec_call_array_new_1 :
      forall (S : state (* input *)) (S' : state) (C : execution_ctx (* input *)) (args : (list value) (* input *)) (O : object) (l : object_loc) (o : out),
        (O = ((object_new prealloc_array_proto (("Array")%string)) : object)) ->
        ((l, S') = ((object_alloc S O) : (object_loc * state))) ->
        (* ========================================== *)
        (red_expr (S' : state) (C : execution_ctx) ((spec_call_array_new_2 (l : object_loc) (args : (list value)) ((0%nat) : int)) : ext_expr) (o : out)) ->
        (* ------------------------------------------ *)
        (red_expr (S : state) (C : execution_ctx) ((spec_call_array_new_1 (args : (list value))) : ext_expr) (o : out))

  | red_spec_call_array_new_2_nonempty :
      forall (S : state (* input *)) (S' : state) (C : execution_ctx (* input *)) (l : object_loc (* input *)) (v : value (* input *)) (vs : (list value) (* input *)) (ilen : nat (* input *)) (o : out),
        (object_set_property S l (JsNumber.to_string (JsNumber.of_int ilen)) (attributes_data_intro (v : value) (true : bool) (true : bool) (true : bool)) S') ->
        (* ========================================== *)
        (red_expr (S' : state) (C : execution_ctx) ((spec_call_array_new_2 (l : object_loc) (vs : (list value)) (((ilen : nat) + (1%nat)) : int)) : ext_expr) (o : out)) ->
        (* ------------------------------------------ *)
        (red_expr (S : state) (C : execution_ctx) ((spec_call_array_new_2 (l : object_loc) ((v :: (vs : (list value))) : (list value)) (ilen : int)) : ext_expr) (o : out))

  | red_spec_call_array_new_2_empty :
      forall (S : state (* input *)) (S' : state) (C : execution_ctx (* input *)) (l : object_loc (* input *)) (ilen : int (* input *)),
        (object_set_property S l (("length")%string) (attributes_data_intro ((JsNumber.of_int ilen) : value) (true : bool) (true : bool) (true : bool)) S') ->
        (* ========================================== *)
        (* ------------------------------------------ *)
        (red_expr (S : state) (C : execution_ctx) ((spec_call_array_new_2 (l : object_loc) (nil : (list value)) (ilen : int)) : ext_expr) ((out_ter (S' : state) (l : res)) : out))

  | red_spec_call_array_proto_pop :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (vthis : value (* input *)) (o : out) (o1 : out) (args : (list value) (* input *)),
        (* ========================================== *)
        (red_expr (S : state) (C : execution_ctx) ((spec_to_object (vthis : value)) : ext_expr) (o1 : out)) ->
        (red_expr (S : state) (C : execution_ctx) ((spec_call_array_proto_pop_1 (o1 : out)) : ext_expr) (o : out)) ->
        (* ------------------------------------------ *)
        (red_expr (S : state) (C : execution_ctx) ((spec_call_prealloc (prealloc_array_proto_pop : prealloc) (vthis : value) (args : (list value))) : ext_expr) (o : out))

  | red_spec_call_array_proto_pop_1 :
      forall (S0 : state (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (l : object_loc (* input *)) (o : out) (o1 : out),
        (* ========================================== *)
        (red_expr (S : state) (C : execution_ctx) ((spec_object_get (l : value) ((("length")%string) : prop_name)) : ext_expr) (o1 : out)) ->
        (red_expr (S : state) (C : execution_ctx) ((spec_call_array_proto_pop_2 (l : object_loc) (o1 : out)) : ext_expr) (o : out)) ->
        (* ------------------------------------------ *)
        (red_expr (S0 : state) (C : execution_ctx) ((spec_call_array_proto_pop_1 ((out_ter (S : state) (l : res)) : out)) : ext_expr) (o : out))

  | red_spec_call_array_proto_pop_2 :
      forall (S0 : state (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (l : object_loc (* input *)) (vlen : value (* input *)) (o : out) (y : (specret int)),
        (* ========================================== *)
        (red_spec S C (spec_to_uint32 (vlen : value)) y) ->
        (red_expr (S : state) (C : execution_ctx) ((spec_call_array_proto_pop_3 (l : object_loc) (y : (specret int))) : ext_expr) (o : out)) ->
        (* ------------------------------------------ *)
        (red_expr (S0 : state) (C : execution_ctx) ((spec_call_array_proto_pop_2 (l : object_loc) ((out_ter (S : state) (vlen : res)) : out)) : ext_expr) (o : out))

  | red_spec_call_array_proto_pop_3_empty :
      forall (S0 : state (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (l : object_loc (* input *)) (o : out),
        (* ========================================== *)
        (red_expr (S : state) (C : execution_ctx) ((spec_call_array_proto_pop_3_empty_1 (l : object_loc)) : ext_expr) (o : out)) ->
        (* ------------------------------------------ *)
        (red_expr (S0 : state) (C : execution_ctx) ((spec_call_array_proto_pop_3 (l : object_loc) ((specret_val S (0%Z)) : (specret int))) : ext_expr) (o : out))

  | red_spec_call_array_proto_pop_3_empty_1 :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (l : object_loc (* input *)) (o : out) (o1 : out),
        (* ========================================== *)
        (red_expr (S : state) (C : execution_ctx) ((spec_object_put (l : value) ((("length")%string) : prop_name) ((0%nat) : value) (throw_true : bool)) : ext_expr) (o1 : out)) ->
        (red_expr (S : state) (C : execution_ctx) ((spec_call_array_proto_pop_3_empty_2 (o1 : out)) : ext_expr) (o : out)) ->
        (* ------------------------------------------ *)
        (red_expr (S : state) (C : execution_ctx) ((spec_call_array_proto_pop_3_empty_1 (l : object_loc)) : ext_expr) (o : out))

  | red_spec_call_array_proto_pop_3_empty_2 :
      forall (S0 : state (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (r0 : ref (* input *)),
        (* ========================================== *)
        (* ------------------------------------------ *)
        (red_expr (S0 : state) (C : execution_ctx) ((spec_call_array_proto_pop_3_empty_2 ((out_ter (S : state) (r0 : res)) : out)) : ext_expr) ((out_ter (S : state) (undef : res)) : out))

  | red_spec_call_array_proto_pop_3_nonempty :
      forall (S0 : state (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (l : object_loc (* input *)) (lenuint32 : int (* input *)) (o : out),
        (lenuint32 > ((0%nat) : int)) ->
        (* ========================================== *)
        (red_expr (S : state) (C : execution_ctx) ((spec_call_array_proto_pop_3_nonempty_1 (l : object_loc) (lenuint32 : int)) : ext_expr) (o : out)) ->
        (* ------------------------------------------ *)
        (red_expr (S0 : state) (C : execution_ctx) ((spec_call_array_proto_pop_3 (l : object_loc) ((specret_val S lenuint32) : (specret int))) : ext_expr) (o : out))

  | red_spec_call_array_proto_pop_3_nonempty_1 :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (l : object_loc (* input *)) (lenuint32 : nat (* input *)) (o : out) (o1 : out),
        (* ========================================== *)
        (red_expr (S : state) (C : execution_ctx) ((spec_to_string (((lenuint32 : nat) - (1%nat)) : value)) : ext_expr) (o1 : out)) ->
        (red_expr (S : state) (C : execution_ctx) ((spec_call_array_proto_pop_3_nonempty_2 (l : object_loc) (o1 : out)) : ext_expr) (o : out)) ->
        (* ------------------------------------------ *)
        (red_expr (S : state) (C : execution_ctx) ((spec_call_array_proto_pop_3_nonempty_1 (l : object_loc) (lenuint32 : int)) : ext_expr) (o : out))

  | red_spec_call_array_proto_pop_3_nonempty_2 :
      forall (S0 : state (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (l : object_loc (* input *)) (vindx : prop_name (* input *)) (o : out) (o1 : out),
        (* ========================================== *)
        (red_expr (S : state) (C : execution_ctx) ((spec_object_get (l : value) (vindx : prop_name)) : ext_expr) (o1 : out)) ->
        (red_expr (S : state) (C : execution_ctx) ((spec_call_array_proto_pop_3_nonempty_3 (l : object_loc) (vindx : value) (o1 : out)) : ext_expr) (o : out)) ->
        (* ------------------------------------------ *)
        (red_expr (S0 : state) (C : execution_ctx) ((spec_call_array_proto_pop_3_nonempty_2 (l : object_loc) ((out_ter (S : state) (vindx : res)) : out)) : ext_expr) (o : out))

  | red_spec_call_array_proto_pop_3_nonempty_3 :
      forall (S0 : state (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (l : object_loc (* input *)) (vindx : prop_name (* input *)) (velem : value (* input *)) (o : out) (o1 : out),
        (* ========================================== *)
        (red_expr (S : state) (C : execution_ctx) ((spec_object_delete (l : object_loc) (vindx : prop_name) (throw_true : bool)) : ext_expr) (o1 : out)) ->
        (red_expr (S : state) (C : execution_ctx) ((spec_call_array_proto_pop_3_nonempty_4 (l : object_loc) (vindx : value) (velem : value) (o1 : out)) : ext_expr) (o : out)) ->
        (* ------------------------------------------ *)
        (red_expr (S0 : state) (C : execution_ctx) ((spec_call_array_proto_pop_3_nonempty_3 (l : object_loc) (vindx : value) ((out_ter (S : state) (velem : res)) : out)) : ext_expr) (o : out))

  | red_spec_call_array_proto_pop_3_nonempty_4 :
      forall (S0 : state (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (l : object_loc (* input *)) (vindx : value (* input *)) (velem : value (* input *)) (o : out) (o1 : out) (r0 : ref (* input *)),
        (* ========================================== *)
        (red_expr (S : state) (C : execution_ctx) ((spec_object_put (l : value) ((("length")%string) : prop_name) (vindx : value) (throw_true : bool)) : ext_expr) (o1 : out)) ->
        (red_expr (S : state) (C : execution_ctx) ((spec_call_array_proto_pop_3_nonempty_5 (velem : value) (o1 : out)) : ext_expr) (o : out)) ->
        (* ------------------------------------------ *)
        (red_expr (S0 : state) (C : execution_ctx) ((spec_call_array_proto_pop_3_nonempty_4 (l : object_loc) (vindx : value) (velem : value) ((out_ter (S : state) (r0 : res)) : out)) : ext_expr) (o : out))

  | red_spec_call_array_proto_pop_3_nonempty_5 :
      forall (S0 : state (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (velem : value (* input *)) (r0 : ref (* input *)),
        (* ========================================== *)
        (* ------------------------------------------ *)
        (red_expr (S0 : state) (C : execution_ctx) ((spec_call_array_proto_pop_3_nonempty_5 (velem : value) ((out_ter (S : state) (r0 : res)) : out)) : ext_expr) ((out_ter (S : state) (velem : res)) : out))

  | red_spec_call_array_proto_push :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (vthis : value (* input *)) (args : (list value) (* input *)) (o : out) (o1 : out),
        (* ========================================== *)
        (red_expr (S : state) (C : execution_ctx) ((spec_to_object (vthis : value)) : ext_expr) (o1 : out)) ->
        (red_expr (S : state) (C : execution_ctx) ((spec_call_array_proto_push_1 (o1 : out) (args : (list value))) : ext_expr) (o : out)) ->
        (* ------------------------------------------ *)
        (red_expr (S : state) (C : execution_ctx) ((spec_call_prealloc (prealloc_array_proto_push : prealloc) (vthis : value) (args : (list value))) : ext_expr) (o : out))

  | red_spec_call_array_proto_push_1 :
      forall (S0 : state (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (l : object_loc (* input *)) (args : (list value) (* input *)) (o : out) (o1 : out),
        (* ========================================== *)
        (red_expr (S : state) (C : execution_ctx) ((spec_object_get (l : value) ((("length")%string) : prop_name)) : ext_expr) (o1 : out)) ->
        (red_expr (S : state) (C : execution_ctx) ((spec_call_array_proto_push_2 (l : object_loc) (args : (list value)) (o1 : out)) : ext_expr) (o : out)) ->
        (* ------------------------------------------ *)
        (red_expr (S0 : state) (C : execution_ctx) ((spec_call_array_proto_push_1 ((out_ter (S : state) (l : res)) : out) (args : (list value))) : ext_expr) (o : out))

  | red_spec_call_array_proto_push_2 :
      forall (S0 : state (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (l : object_loc (* input *)) (args : (list value) (* input *)) (vlen : value (* input *)) (y : (specret int)) (o : out),
        (* ========================================== *)
        (red_spec S C (spec_to_uint32 (vlen : value)) y) ->
        (red_expr (S : state) (C : execution_ctx) ((spec_call_array_proto_push_3 (l : object_loc) (args : (list value)) (y : (specret int))) : ext_expr) (o : out)) ->
        (* ------------------------------------------ *)
        (red_expr (S0 : state) (C : execution_ctx) ((spec_call_array_proto_push_2 (l : object_loc) (args : (list value)) ((out_ter (S : state) (vlen : res)) : out)) : ext_expr) (o : out))

  | red_spec_call_array_proto_push_3 :
      forall (S0 : state (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (l : object_loc (* input *)) (args : (list value) (* input *)) (lenuint32 : int (* input *)) (o : out),
        (* ========================================== *)
        (red_expr (S : state) (C : execution_ctx) ((spec_call_array_proto_push_4 (l : object_loc) (args : (list value)) (lenuint32 : int)) : ext_expr) (o : out)) ->
        (* ------------------------------------------ *)
        (red_expr (S0 : state) (C : execution_ctx) ((spec_call_array_proto_push_3 (l : object_loc) (args : (list value)) ((specret_val S lenuint32) : (specret int))) : ext_expr) (o : out))

  | red_spec_call_array_proto_push_4_empty :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (l : object_loc (* input *)) (lenuint32 : int (* input *)) (o : out),
        (* ========================================== *)
        (red_expr (S : state) (C : execution_ctx) ((spec_call_array_proto_push_5 (l : object_loc) ((JsNumber.of_int lenuint32) : value)) : ext_expr) (o : out)) ->
        (* ------------------------------------------ *)
        (red_expr (S : state) (C : execution_ctx) ((spec_call_array_proto_push_4 (l : object_loc) (nil : (list value)) (lenuint32 : int)) : ext_expr) (o : out))

  | red_spec_call_array_proto_push_4_nonempty :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (l : object_loc (* input *)) (v : value (* input *)) (vs : (list value) (* input *)) (lenuint32 : int (* input *)) (o : out),
        (* ========================================== *)
        (red_expr (S : state) (C : execution_ctx) ((spec_call_array_proto_push_4_nonempty_1 (l : object_loc) (vs : (list value)) (lenuint32 : int) (v : value)) : ext_expr) (o : out)) ->
        (* ------------------------------------------ *)
        (red_expr (S : state) (C : execution_ctx) ((spec_call_array_proto_push_4 (l : object_loc) ((v :: (vs : (list value))) : (list value)) (lenuint32 : int)) : ext_expr) (o : out))

  | red_spec_call_array_proto_push_4_nonempty_1 :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (l : object_loc (* input *)) (v : value (* input *)) (vs : (list value) (* input *)) (lenuint32 : int (* input *)) (o : out) (o1 : out),
        (* ========================================== *)
        (red_expr (S : state) (C : execution_ctx) ((spec_to_string ((JsNumber.of_int lenuint32) : value)) : ext_expr) (o1 : out)) ->
        (red_expr (S : state) (C : execution_ctx) ((spec_call_array_proto_push_4_nonempty_2 (l : object_loc) (vs : (list value)) (lenuint32 : int) (v : value) (o1 : out)) : ext_expr) (o : out)) ->
        (* ------------------------------------------ *)
        (red_expr (S : state) (C : execution_ctx) ((spec_call_array_proto_push_4_nonempty_1 (l : object_loc) (vs : (list value)) (lenuint32 : int) (v : value)) : ext_expr) (o : out))

  | red_spec_call_array_proto_push_4_nonempty_2 :
      forall (S0 : state (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (l : object_loc (* input *)) (vindx : prop_name (* input *)) (v : value (* input *)) (vs : (list value) (* input *)) (lenuint32 : int (* input *)) (o : out) (o1 : out),
        (* ========================================== *)
        (red_expr (S : state) (C : execution_ctx) ((spec_object_put (l : value) (vindx : prop_name) (v : value) (throw_true : bool)) : ext_expr) (o1 : out)) ->
        (red_expr (S : state) (C : execution_ctx) ((spec_call_array_proto_push_4_nonempty_3 (l : object_loc) (vs : (list value)) (lenuint32 : int) (v : value) (o1 : out)) : ext_expr) (o : out)) ->
        (* ------------------------------------------ *)
        (red_expr (S0 : state) (C : execution_ctx) ((spec_call_array_proto_push_4_nonempty_2 (l : object_loc) (vs : (list value)) (lenuint32 : int) (v : value) ((out_ter (S : state) (vindx : res)) : out)) : ext_expr) (o : out))

  | red_spec_call_array_proto_push_4_nonempty_3 :
      forall (S0 : state (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (l : object_loc (* input *)) (v : value (* input *)) (vs : (list value) (* input *)) (lenuint32 : nat (* input *)) (o : out) (r0 : ref (* input *)),
        (* ========================================== *)
        (red_expr (S : state) (C : execution_ctx) ((spec_call_array_proto_push_4 (l : object_loc) (vs : (list value)) (((lenuint32 : nat) + (1%nat)) : int)) : ext_expr) (o : out)) ->
        (* ------------------------------------------ *)
        (red_expr (S0 : state) (C : execution_ctx) ((spec_call_array_proto_push_4_nonempty_3 (l : object_loc) (vs : (list value)) (lenuint32 : int) (v : value) ((out_ter (S : state) (r0 : res)) : out)) : ext_expr) (o : out))

  | red_spec_call_array_proto_push_5 :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (l : object_loc (* input *)) (vlen : value (* input *)) (o : out) (o1 : out),
        (* ========================================== *)
        (red_expr (S : state) (C : execution_ctx) ((spec_object_put (l : value) ((("length")%string) : prop_name) (vlen : value) (throw_true : bool)) : ext_expr) (o1 : out)) ->
        (red_expr (S : state) (C : execution_ctx) ((spec_call_array_proto_push_6 (vlen : value) (o1 : out)) : ext_expr) (o : out)) ->
        (* ------------------------------------------ *)
        (red_expr (S : state) (C : execution_ctx) ((spec_call_array_proto_push_5 (l : object_loc) (vlen : value)) : ext_expr) (o : out))

  | red_spec_call_array_proto_push_6 :
      forall (S0 : state (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (vlen : value (* input *)) (r0 : ref (* input *)),
        (* ========================================== *)
        (* ------------------------------------------ *)
        (red_expr (S0 : state) (C : execution_ctx) ((spec_call_array_proto_push_6 (vlen : value) ((out_ter (S : state) (r0 : res)) : out)) : ext_expr) ((out_ter (S : state) (vlen : res)) : out))

  | red_spec_construct_string_non_empty :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (v : value) (args : (list value) (* input *)) (o : out),
        (args <> nil) ->
        (arguments_from (args : (list value)) ((v :: (nil : (list value))) : (list value))) ->
        (* ========================================== *)
        (red_expr (S : state) (C : execution_ctx) ((spec_construct_string_1 (v : value)) : ext_expr) (o : out)) ->
        (* ------------------------------------------ *)
        (red_expr (S : state) (C : execution_ctx) ((spec_construct_prealloc (prealloc_string : prealloc) (args : (list value))) : ext_expr) (o : out))

  | red_spec_construct_string_empty :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (v : value) (o : out),
        (* ========================================== *)
        (red_expr (S : state) (C : execution_ctx) ((spec_construct_string_2 ((out_ter (S : state) ((("")%string) : res)) : out)) : ext_expr) (o : out)) ->
        (* ------------------------------------------ *)
        (red_expr (S : state) (C : execution_ctx) ((spec_construct_prealloc (prealloc_string : prealloc) (nil : (list value))) : ext_expr) (o : out))

  | red_spec_construct_string_1 :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (v : value (* input *)) (o' : out) (o : out),
        (* ========================================== *)
        (red_expr (S : state) (C : execution_ctx) ((spec_to_string (v : value)) : ext_expr) (o' : out)) ->
        (red_expr (S : state) (C : execution_ctx) ((spec_construct_string_2 (o' : out)) : ext_expr) (o : out)) ->
        (* ------------------------------------------ *)
        (red_expr (S : state) (C : execution_ctx) ((spec_construct_string_1 (v : value)) : ext_expr) (o : out))

  | red_spec_construct_string_2 :
      forall (S0 : state (* input *)) (S : state (* input *)) (S' : state) (C : execution_ctx (* input *)) (l : object_loc) (s : string (* input *)) (P : object_properties_type) (A : attributes) (O : object),
        ((object_proto_ (O : object)) = (prealloc_string_proto : value)) ->
        ((object_class_ (O : object)) = ((("String")%string) : class_name)) ->
        ((object_extensible_ (O : object)) = (true : bool)) ->
        ((object_prim_value_ (O : object)) = ((Some (s : value)) : (option value))) ->
        ((object_get_own_prop_ (O : object)) = (builtin_get_own_prop_string : builtin_get_own_prop)) ->
        (P = ((object_properties_ (O : object)) : object_properties_type)) ->
        (Heap.binds P ((("length")%string) : prop_name) (A : attributes)) ->
        (A = ((attributes_data_intro_constant ((String.length s) : value)) : attributes)) ->
        ((l, S') = ((object_alloc S O) : (object_loc * state))) ->
        (* ========================================== *)
        (* ------------------------------------------ *)
        (red_expr (S0 : state) (C : execution_ctx) ((spec_construct_string_2 ((out_ter (S : state) (s : res)) : out)) : ext_expr) ((out_ter (S' : state) (l : res)) : out))

  | red_spec_call_string_proto_to_string :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (vthis : value (* input *)) (args : (list value) (* input *)) (o : out),
        (* ========================================== *)
        (red_expr (S : state) (C : execution_ctx) ((spec_call_prealloc (prealloc_string_proto_value_of : prealloc) (vthis : value) (args : (list value))) : ext_expr) (o : out)) ->
        (* ------------------------------------------ *)
        (red_expr (S : state) (C : execution_ctx) ((spec_call_prealloc (prealloc_string_proto_to_string : prealloc) (vthis : value) (args : (list value))) : ext_expr) (o : out))

  | red_spec_call_string_proto_value_of_prim_string :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (vthis : value (* input *)) (args : (list value) (* input *)),
        (((type_of vthis) : type) = type_string) ->
        (* ========================================== *)
        (* ------------------------------------------ *)
        (red_expr (S : state) (C : execution_ctx) ((spec_call_prealloc (prealloc_string_proto_value_of : prealloc) (vthis : value) (args : (list value))) : ext_expr) ((out_ter (S : state) (vthis : res)) : out))

  | red_spec_call_string_proto_value_of_obj_string :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (l : object_loc (* input *)) (v : value) (args : (list value) (* input *)),
        (object_class (S : state) (l : object_loc) ((("String")%string) : string)) ->
        (object_prim_value (S : state) (l : object_loc) (v : value)) ->
        (* ========================================== *)
        (* ------------------------------------------ *)
        (red_expr (S : state) (C : execution_ctx) ((spec_call_prealloc (prealloc_string_proto_value_of : prealloc) ((value_object (l : object_loc)) : value) (args : (list value))) : ext_expr) ((out_ter (S : state) (v : res)) : out))

  | red_spec_call_string_proto_value_of_obj_other :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (l : object_loc (* input *)) (args : (list value) (* input *)) (o : out),
        (~ (object_class (S : state) (l : object_loc) ((("String")%string) : string))) ->
        (* ========================================== *)
        (red_expr (S : state) (C : execution_ctx) ((spec_error (native_error_type : native_error)) : ext_expr) (o : out)) ->
        (* ------------------------------------------ *)
        (red_expr (S : state) (C : execution_ctx) ((spec_call_prealloc (prealloc_string_proto_value_of : prealloc) ((value_object (l : object_loc)) : value) (args : (list value))) : ext_expr) (o : out))

  | red_spec_call_string_proto_value_of_bad_type :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (vthis : value (* input *)) (args : (list value) (* input *)) (o : out),
        (((type_of vthis) : type) <> type_string) ->
        (((type_of vthis) : type) <> type_object) ->
        (* ========================================== *)
        (red_expr (S : state) (C : execution_ctx) ((spec_error (native_error_type : native_error)) : ext_expr) (o : out)) ->
        (* ------------------------------------------ *)
        (red_expr (S : state) (C : execution_ctx) ((spec_call_prealloc (prealloc_string_proto_value_of : prealloc) (vthis : value) (args : (list value))) : ext_expr) (o : out))

  | red_spec_call_bool :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (v : value) (o : out) (vthis : value (* input *)) (args : (list value) (* input *)),
        (arguments_from (args : (list value)) ((v :: (nil : (list value))) : (list value))) ->
        (* ========================================== *)
        (red_expr (S : state) (C : execution_ctx) ((spec_to_boolean (v : value)) : ext_expr) (o : out)) ->
        (* ------------------------------------------ *)
        (red_expr (S : state) (C : execution_ctx) ((spec_call_prealloc (prealloc_bool : prealloc) (vthis : value) (args : (list value))) : ext_expr) (o : out))

  | red_spec_construct_bool :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (v : value) (o : out) (o1 : out) (args : (list value) (* input *)),
        (arguments_from (args : (list value)) ((v :: (nil : (list value))) : (list value))) ->
        (* ========================================== *)
        (red_expr (S : state) (C : execution_ctx) ((spec_to_boolean (v : value)) : ext_expr) (o1 : out)) ->
        (red_expr (S : state) (C : execution_ctx) ((spec_construct_bool_1 (o1 : out)) : ext_expr) (o : out)) ->
        (* ------------------------------------------ *)
        (red_expr (S : state) (C : execution_ctx) ((spec_construct_prealloc (prealloc_bool : prealloc) (args : (list value))) : ext_expr) (o : out))

  | red_spec_construct_bool_1 :
      forall (O : object) (l : object_loc) (b : bool (* input *)) (S' : state) (S : state (* input *)) (S0 : state (* input *)) (C : execution_ctx (* input *)),
        let O1 : object := (object_new prealloc_bool_proto (("Boolean")%string)) in
        let O : object := (object_with_primitive_value O1 b) in
        ((l, S') = ((object_alloc S O) : (object_loc * state))) ->
        (* ========================================== *)
        (* ------------------------------------------ *)
        (red_expr (S0 : state) (C : execution_ctx) ((spec_construct_bool_1 ((out_ter (S : state) (b : res)) : out)) : ext_expr) ((out_ter (S' : state) (l : res)) : out))

  | red_spec_call_bool_proto_to_string :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (vthis : value (* input *)) (args : (list value) (* input *)) (o1 : out) (o : out),
        (* ========================================== *)
        (red_expr (S : state) (C : execution_ctx) ((spec_call_prealloc (prealloc_bool_proto_value_of : prealloc) (vthis : value) (args : (list value))) : ext_expr) (o1 : out)) ->
        (red_expr (S : state) (C : execution_ctx) ((spec_call_bool_proto_to_string_1 (o1 : out)) : ext_expr) (o : out)) ->
        (* ------------------------------------------ *)
        (red_expr (S : state) (C : execution_ctx) ((spec_call_prealloc (prealloc_bool_proto_to_string : prealloc) (vthis : value) (args : (list value))) : ext_expr) (o : out))

  | red_spec_call_bool_proto_to_string_1 :
      forall (S0 : state (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (s : string) (b : bool (* input *)),
        (s = ((convert_bool_to_string (b : bool)) : string)) ->
        (* ========================================== *)
        (* ------------------------------------------ *)
        (red_expr (S0 : state) (C : execution_ctx) ((spec_call_bool_proto_to_string_1 ((out_ter (S : state) (b : res)) : out)) : ext_expr) ((out_ter (S : state) (s : res)) : out))

  | red_spec_call_bool_proto_value_of :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (o : out) (vthis : value (* input *)) (args : (list value) (* input *)),
        (* ========================================== *)
        (red_expr (S : state) (C : execution_ctx) ((spec_call_bool_proto_value_of_1 (vthis : value)) : ext_expr) (o : out)) ->
        (* ------------------------------------------ *)
        (red_expr (S : state) (C : execution_ctx) ((spec_call_prealloc (prealloc_bool_proto_value_of : prealloc) (vthis : value) (args : (list value))) : ext_expr) (o : out))

  | red_spec_call_bool_proto_value_of_1_bool :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (v : value (* input *)) (b : bool),
        (value_viewable_as ((("Boolean")%string) : string) (S : state) (v : value) (b : prim)) ->
        (* ========================================== *)
        (* ------------------------------------------ *)
        (red_expr (S : state) (C : execution_ctx) ((spec_call_bool_proto_value_of_1 (v : value)) : ext_expr) ((out_ter (S : state) (b : res)) : out))

  | red_spec_call_bool_proto_value_of_1_not_bool :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (v : value (* input *)) (o : out),
        (forall b, (~ (value_viewable_as (("Boolean")%string) S v b))) ->
        (* ========================================== *)
        (red_expr (S : state) (C : execution_ctx) ((spec_error (native_error_type : native_error)) : ext_expr) (o : out)) ->
        (* ------------------------------------------ *)
        (red_expr (S : state) (C : execution_ctx) ((spec_call_bool_proto_value_of_1 (v : value)) : ext_expr) (o : out))

  | red_spec_call_number_nil :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (vthis : value (* input *)),
        (* ========================================== *)
        (* ------------------------------------------ *)
        (red_expr (S : state) (C : execution_ctx) ((spec_call_prealloc (prealloc_number : prealloc) (vthis : value) (nil : (list value))) : ext_expr) ((out_ter (S : state) (JsNumber.zero : res)) : out))

  | red_spec_call_number_not_nil :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (v : value) (o : out) (vthis : value (* input *)) (args : (list value) (* input *)),
        (args <> nil) ->
        (arguments_from (args : (list value)) ((v :: (nil : (list value))) : (list value))) ->
        (* ========================================== *)
        (red_expr (S : state) (C : execution_ctx) ((spec_to_number (v : value)) : ext_expr) (o : out)) ->
        (* ------------------------------------------ *)
        (red_expr (S : state) (C : execution_ctx) ((spec_call_prealloc (prealloc_number : prealloc) (vthis : value) (args : (list value))) : ext_expr) (o : out))

  | red_spec_construct_number_nil :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (o : out),
        (* ========================================== *)
        (red_expr (S : state) (C : execution_ctx) ((spec_construct_number_1 ((out_ter (S : state) (JsNumber.zero : res)) : out)) : ext_expr) (o : out)) ->
        (* ------------------------------------------ *)
        (red_expr (S : state) (C : execution_ctx) ((spec_construct_prealloc (prealloc_number : prealloc) (nil : (list value))) : ext_expr) (o : out))

  | red_spec_construct_number_not_nil :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (v : value) (o : out) (o1 : out) (args : (list value) (* input *)),
        (args <> nil) ->
        (arguments_from (args : (list value)) ((v :: (nil : (list value))) : (list value))) ->
        (* ========================================== *)
        (red_expr (S : state) (C : execution_ctx) ((spec_to_number (v : value)) : ext_expr) (o1 : out)) ->
        (red_expr (S : state) (C : execution_ctx) ((spec_construct_number_1 (o1 : out)) : ext_expr) (o : out)) ->
        (* ------------------------------------------ *)
        (red_expr (S : state) (C : execution_ctx) ((spec_construct_prealloc (prealloc_number : prealloc) (args : (list value))) : ext_expr) (o : out))

  | red_spec_construct_number_1 :
      forall (S0 : state (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (S' : state) (O : object) (l : object_loc) (v : value (* input *)),
        let O1 : object := (object_new prealloc_number_proto (("Number")%string)) in
        let O : object := (object_with_primitive_value O1 v) in
        ((l, S') = ((object_alloc S O) : (object_loc * state))) ->
        (* ========================================== *)
        (* ------------------------------------------ *)
        (red_expr (S0 : state) (C : execution_ctx) ((spec_construct_number_1 ((out_ter (S : state) (v : res)) : out)) : ext_expr) ((out_ter (S' : state) (l : res)) : out))

  | red_spec_call_number_proto_value_of :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (o : out) (vthis : value (* input *)) (args : (list value) (* input *)),
        (* ========================================== *)
        (red_expr (S : state) (C : execution_ctx) ((spec_call_number_proto_value_of_1 (vthis : value)) : ext_expr) (o : out)) ->
        (* ------------------------------------------ *)
        (red_expr (S : state) (C : execution_ctx) ((spec_call_prealloc (prealloc_number_proto_value_of : prealloc) (vthis : value) (args : (list value))) : ext_expr) (o : out))

  | red_spec_call_number_proto_value_of_1_number :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (v : value (* input *)) (n : number),
        (value_viewable_as ((("Number")%string) : string) (S : state) (v : value) (n : prim)) ->
        (* ========================================== *)
        (* ------------------------------------------ *)
        (red_expr (S : state) (C : execution_ctx) ((spec_call_number_proto_value_of_1 (v : value)) : ext_expr) ((out_ter (S : state) (n : res)) : out))

  | red_spec_call_number_proto_value_of_1_not_number :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (v : value (* input *)) (o : out),
        (forall n, (~ (value_viewable_as (("Number")%string) S v n))) ->
        (* ========================================== *)
        (red_expr (S : state) (C : execution_ctx) ((spec_error (native_error_type : native_error)) : ext_expr) (o : out)) ->
        (* ------------------------------------------ *)
        (red_expr (S : state) (C : execution_ctx) ((spec_call_number_proto_value_of_1 (v : value)) : ext_expr) (o : out))

  | red_spec_error :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (ne : native_error (* input *)) (o1 : out) (o : out),
        (* ========================================== *)
        (red_expr (S : state) (C : execution_ctx) ((spec_build_error ((prealloc_native_error_proto (ne : native_error)) : value) (undef : value)) : ext_expr) (o1 : out)) ->
        (red_expr (S : state) (C : execution_ctx) ((spec_error_1 (o1 : out)) : ext_expr) (o : out)) ->
        (* ------------------------------------------ *)
        (red_expr (S : state) (C : execution_ctx) ((spec_error (ne : native_error)) : ext_expr) (o : out))

  | red_spec_error_1 :
      forall (S0 : state (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (l : object_loc (* input *)),
        (* ========================================== *)
        (* ------------------------------------------ *)
        (red_expr (S0 : state) (C : execution_ctx) ((spec_error_1 ((out_ter (S : state) (l : res)) : out)) : ext_expr) ((out_ter (S : state) ((res_throw (l : resvalue)) : res)) : out))

  | red_spec_error_or_cst_true :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (ne : native_error (* input *)) (v : value (* input *)) (o : out),
        (* ========================================== *)
        (red_expr (S : state) (C : execution_ctx) ((spec_error (ne : native_error)) : ext_expr) (o : out)) ->
        (* ------------------------------------------ *)
        (red_expr (S : state) (C : execution_ctx) ((spec_error_or_cst (true : bool) (ne : native_error) (v : value)) : ext_expr) (o : out))

  | red_spec_error_or_cst_false :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (ne : native_error (* input *)) (v : value (* input *)),
        (* ========================================== *)
        (* ------------------------------------------ *)
        (red_expr (S : state) (C : execution_ctx) ((spec_error_or_cst (false : bool) (ne : native_error) (v : value)) : ext_expr) ((out_ter (S : state) (v : res)) : out))

  | red_spec_error_or_void_true :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (ne : native_error (* input *)) (o : out),
        (* ========================================== *)
        (red_expr (S : state) (C : execution_ctx) ((spec_error (ne : native_error)) : ext_expr) (o : out)) ->
        (* ------------------------------------------ *)
        (red_expr (S : state) (C : execution_ctx) ((spec_error_or_void (true : bool) (ne : native_error)) : ext_expr) (o : out))

  | red_spec_error_or_void_false :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (ne : native_error (* input *)),
        (* ========================================== *)
        (* ------------------------------------------ *)
        (red_expr (S : state) (C : execution_ctx) ((spec_error_or_void (false : bool) (ne : native_error)) : ext_expr) ((out_void (S : state)) : out))

  | red_spec_build_error :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (O : object) (vproto : value (* input *)) (vmsg : value (* input *)) (l : object_loc) (S' : state) (o : out),
        (O = ((object_new vproto (("Error")%string)) : object)) ->
        ((l, S') = ((object_alloc S O) : (object_loc * state))) ->
        (* ========================================== *)
        (red_expr (S' : state) (C : execution_ctx) ((spec_build_error_1 (l : object_loc) (vmsg : value)) : ext_expr) (o : out)) ->
        (* ------------------------------------------ *)
        (red_expr (S : state) (C : execution_ctx) ((spec_build_error (vproto : value) (vmsg : value)) : ext_expr) (o : out))

  | red_spec_build_error_1_no_msg :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (l : object_loc (* input *)) (vmsg : value (* input *)),
        ((vmsg : value) = undef) ->
        (* ========================================== *)
        (* ------------------------------------------ *)
        (red_expr (S : state) (C : execution_ctx) ((spec_build_error_1 (l : object_loc) (vmsg : value)) : ext_expr) ((out_ter (S : state) (l : res)) : out))

  | red_spec_build_error_1_msg :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (l : object_loc (* input *)) (vmsg : value (* input *)) (o1 : out) (o : out),
        ((vmsg : value) <> undef) ->
        (* ========================================== *)
        (red_expr (S : state) (C : execution_ctx) ((spec_to_string (vmsg : value)) : ext_expr) (o1 : out)) ->
        (red_expr (S : state) (C : execution_ctx) ((spec_build_error_2 (l : object_loc) (o1 : out)) : ext_expr) (o : out)) ->
        (* ------------------------------------------ *)
        (red_expr (S : state) (C : execution_ctx) ((spec_build_error_1 (l : object_loc) (vmsg : value)) : ext_expr) (o : out))

  | red_spec_build_error_2 :
      forall (S0 : state (* input *)) (S : state (* input *)) (S' : state) (C : execution_ctx (* input *)) (l : object_loc (* input *)) (smsg : value (* input *)),
        (object_set_property S l (("message")%string) (attributes_data_intro (smsg : value) (true : bool) (false : bool) (true : bool)) S') ->
        (* ========================================== *)
        (* ------------------------------------------ *)
        (red_expr (S0 : state) (C : execution_ctx) ((spec_build_error_2 (l : object_loc) ((out_ter (S : state) (smsg : res)) : out)) : ext_expr) ((out_ter (S' : state) (l : res)) : out))

  | red_spec_call_error :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (v : value) (o : out) (vthis : value (* input *)) (args : (list value) (* input *)),
        (arguments_from (args : (list value)) ((v :: (nil : (list value))) : (list value))) ->
        (* ========================================== *)
        (red_expr (S : state) (C : execution_ctx) ((spec_build_error (prealloc_error_proto : value) (v : value)) : ext_expr) (o : out)) ->
        (* ------------------------------------------ *)
        (red_expr (S : state) (C : execution_ctx) ((spec_call_prealloc (prealloc_error : prealloc) (vthis : value) (args : (list value))) : ext_expr) (o : out))

  | red_spec_construct_error :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (v : value) (o : out) (args : (list value) (* input *)),
        (arguments_from (args : (list value)) ((v :: (nil : (list value))) : (list value))) ->
        (* ========================================== *)
        (red_expr (S : state) (C : execution_ctx) ((spec_build_error (prealloc_error_proto : value) (v : value)) : ext_expr) (o : out)) ->
        (* ------------------------------------------ *)
        (red_expr (S : state) (C : execution_ctx) ((spec_construct_prealloc (prealloc_error : prealloc) (args : (list value))) : ext_expr) (o : out))

  | red_spec_call_error_proto_to_string :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (args : (list value) (* input *)) (vthis : value (* input *)) (o : out),
        (* ========================================== *)
        (red_expr (S : state) (C : execution_ctx) ((spec_call_error_proto_to_string_1 (vthis : value)) : ext_expr) (o : out)) ->
        (* ------------------------------------------ *)
        (red_expr (S : state) (C : execution_ctx) ((spec_call_prealloc (prealloc_error_proto_to_string : prealloc) (vthis : value) (args : (list value))) : ext_expr) (o : out))

  | red_spec_call_error_proto_to_string_1_not_object :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (v : value (* input *)) (o : out),
        (((type_of v) : type) <> type_object) ->
        (* ========================================== *)
        (red_expr (S : state) (C : execution_ctx) ((spec_error (native_error_type : native_error)) : ext_expr) (o : out)) ->
        (* ------------------------------------------ *)
        (red_expr (S : state) (C : execution_ctx) ((spec_call_error_proto_to_string_1 (v : value)) : ext_expr) (o : out))

  | red_spec_call_error_proto_to_string_1_object :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (l : object_loc (* input *)) (o1 : out) (o : out),
        (* ========================================== *)
        (red_expr (S : state) (C : execution_ctx) ((spec_object_get (l : value) ((("name")%string) : prop_name)) : ext_expr) (o1 : out)) ->
        (red_expr (S : state) (C : execution_ctx) ((spec_call_error_proto_to_string_2 (l : object_loc) (o1 : out)) : ext_expr) (o : out)) ->
        (* ------------------------------------------ *)
        (red_expr (S : state) (C : execution_ctx) ((spec_call_error_proto_to_string_1 (l : value)) : ext_expr) (o : out))

  | red_spec_call_error_proto_to_string_2_undef :
      forall (S0 : state (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (l : object_loc (* input *)) (o : out),
        (* ========================================== *)
        (red_expr (S : state) (C : execution_ctx) ((spec_call_error_proto_to_string_3 (l : object_loc) ((out_ter (S : state) ((("Error")%string) : res)) : out)) : ext_expr) (o : out)) ->
        (* ------------------------------------------ *)
        (red_expr (S0 : state) (C : execution_ctx) ((spec_call_error_proto_to_string_2 (l : object_loc) ((out_ter (S : state) (undef : res)) : out)) : ext_expr) (o : out))

  | red_spec_call_error_proto_to_string_2_not_undef :
      forall (S0 : state (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (l : object_loc (* input *)) (v : value (* input *)) (o1 : out) (o : out),
        (v <> (undef : value)) ->
        (* ========================================== *)
        (red_expr (S : state) (C : execution_ctx) ((spec_to_string (v : value)) : ext_expr) (o1 : out)) ->
        (red_expr (S : state) (C : execution_ctx) ((spec_call_error_proto_to_string_3 (l : object_loc) (o1 : out)) : ext_expr) (o : out)) ->
        (* ------------------------------------------ *)
        (red_expr (S0 : state) (C : execution_ctx) ((spec_call_error_proto_to_string_2 (l : object_loc) ((out_ter (S : state) (v : res)) : out)) : ext_expr) (o : out))

  | red_spec_call_error_proto_to_string_3 :
      forall (S0 : state (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (l : object_loc (* input *)) (sname : string (* input *)) (o1 : out) (o : out),
        (* ========================================== *)
        (red_expr (S : state) (C : execution_ctx) ((spec_object_get (l : value) ((("message")%string) : prop_name)) : ext_expr) (o1 : out)) ->
        (red_expr (S : state) (C : execution_ctx) ((spec_call_error_proto_to_string_4 (l : object_loc) (sname : string) (o1 : out)) : ext_expr) (o : out)) ->
        (* ------------------------------------------ *)
        (red_expr (S0 : state) (C : execution_ctx) ((spec_call_error_proto_to_string_3 (l : object_loc) ((out_ter (S : state) (sname : res)) : out)) : ext_expr) (o : out))

  | red_spec_call_error_proto_to_string_4_undef :
      forall (S0 : state (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (l : object_loc (* input *)) (sname : string (* input *)) (o : out),
        (* ========================================== *)
        (red_expr (S : state) (C : execution_ctx) ((spec_call_error_proto_to_string_5 (l : object_loc) (sname : string) ((out_ter (S : state) ((("")%string) : res)) : out)) : ext_expr) (o : out)) ->
        (* ------------------------------------------ *)
        (red_expr (S0 : state) (C : execution_ctx) ((spec_call_error_proto_to_string_4 (l : object_loc) (sname : string) ((out_ter (S : state) (undef : res)) : out)) : ext_expr) (o : out))

  | red_spec_call_error_proto_to_string_4_not_undef :
      forall (S0 : state (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (l : object_loc (* input *)) (sname : string (* input *)) (v : value (* input *)) (o1 : out) (o : out),
        (v <> (undef : value)) ->
        (* ========================================== *)
        (red_expr (S : state) (C : execution_ctx) ((spec_to_string (v : value)) : ext_expr) (o1 : out)) ->
        (red_expr (S : state) (C : execution_ctx) ((spec_call_error_proto_to_string_5 (l : object_loc) (sname : string) (o1 : out)) : ext_expr) (o : out)) ->
        (* ------------------------------------------ *)
        (red_expr (S0 : state) (C : execution_ctx) ((spec_call_error_proto_to_string_4 (l : object_loc) (sname : string) ((out_ter (S : state) (v : res)) : out)) : ext_expr) (o : out))

  | red_spec_call_error_proto_to_string_5_undef :
      forall (S0 : state (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (l : object_loc (* input *)) (sname : string (* input *)) (o : out),
        (* ========================================== *)
        (red_expr (S : state) (C : execution_ctx) ((spec_call_error_proto_to_string_6 (l : object_loc) (sname : string) ((out_ter (S : state) ((("")%string) : res)) : out)) : ext_expr) (o : out)) ->
        (* ------------------------------------------ *)
        (red_expr (S0 : state) (C : execution_ctx) ((spec_call_error_proto_to_string_5 (l : object_loc) (sname : string) ((out_ter (S : state) (undef : res)) : out)) : ext_expr) (o : out))

  | red_spec_call_error_proto_to_string_5_not_undef :
      forall (S0 : state (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (l : object_loc (* input *)) (sname : string (* input *)) (v : value (* input *)) (o1 : out) (o : out),
        (v <> (undef : value)) ->
        (* ========================================== *)
        (red_expr (S : state) (C : execution_ctx) ((spec_to_string (v : value)) : ext_expr) (o1 : out)) ->
        (red_expr (S : state) (C : execution_ctx) ((spec_call_error_proto_to_string_6 (l : object_loc) (sname : string) (o1 : out)) : ext_expr) (o : out)) ->
        (* ------------------------------------------ *)
        (red_expr (S0 : state) (C : execution_ctx) ((spec_call_error_proto_to_string_5 (l : object_loc) (sname : string) ((out_ter (S : state) (v : res)) : out)) : ext_expr) (o : out))

  | red_spec_call_error_proto_to_string_6 :
      forall (S0 : state (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (l : object_loc (* input *)) (sname : string (* input *)) (smsg : string (* input *)) (s : string),
        (s = ((ifb ((sname : string) = (("")%string)) then smsg else (ifb ((smsg : string) = (("")%string)) then sname else (string_concat (string_concat sname ((": ")%string)) smsg))) : string)) ->
        (* ========================================== *)
        (* ------------------------------------------ *)
        (red_expr (S0 : state) (C : execution_ctx) ((spec_call_error_proto_to_string_6 (l : object_loc) (sname : string) ((out_ter (S : state) (smsg : res)) : out)) : ext_expr) ((out_ter (S : state) (s : res)) : out))

  | red_spec_call_native_error :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (v : value) (o : out) (ne : native_error (* input *)) (vthis : value (* input *)) (args : (list value) (* input *)),
        (arguments_from (args : (list value)) ((v :: (nil : (list value))) : (list value))) ->
        (* ========================================== *)
        (red_expr (S : state) (C : execution_ctx) ((spec_build_error ((prealloc_native_error_proto (ne : native_error)) : value) (v : value)) : ext_expr) (o : out)) ->
        (* ------------------------------------------ *)
        (red_expr (S : state) (C : execution_ctx) ((spec_call_prealloc ((prealloc_native_error (ne : native_error)) : prealloc) (vthis : value) (args : (list value))) : ext_expr) (o : out))

  | red_spec_construct_native_error :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (v : value) (o : out) (ne : native_error (* input *)) (args : (list value) (* input *)),
        (arguments_from (args : (list value)) ((v :: (nil : (list value))) : (list value))) ->
        (* ========================================== *)
        (red_expr (S : state) (C : execution_ctx) ((spec_build_error ((prealloc_native_error_proto (ne : native_error)) : value) (v : value)) : ext_expr) (o : out)) ->
        (* ------------------------------------------ *)
        (red_expr (S : state) (C : execution_ctx) ((spec_construct_prealloc ((prealloc_native_error (ne : native_error)) : prealloc) (args : (list value))) : ext_expr) (o : out))

  | red_spec_construct_implementation :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (B : prealloc (* input *)) (args : (list value) (* input *)) (o : out),
        (implementation_prealloc (B : prealloc)) ->
        (* ========================================== *)
        (* ------------------------------------------ *)
        (red_expr (S : state) (C : execution_ctx) ((spec_construct_prealloc (B : prealloc) (args : (list value))) : ext_expr) (o : out))

  | red_spec_call_implementation :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (B : prealloc (* input *)) (vthis : value (* input *)) (args : (list value) (* input *)) (o : out),
        (implementation_prealloc (B : prealloc)) ->
        (* ========================================== *)
        (* ------------------------------------------ *)
        (red_expr (S : state) (C : execution_ctx) ((spec_call_prealloc (B : prealloc) (vthis : value) (args : (list value))) : ext_expr) (o : out))


with red_spec : forall {T : Type}, state (* input *) -> execution_ctx (* input *) -> ext_spec (* input *) -> (specret T) -> Prop :=

  | red_spec_abort :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (exts : ext_spec (* input *)) (T : _) (o : out),
        ((out_of_ext_spec (exts : ext_spec)) = ((Some o) : (option out))) ->
        (abort (o : out)) ->
        (~ (abort_intercepted_spec (exts : ext_spec))) ->
        (* ========================================== *)
        (* ------------------------------------------ *)
        (red_spec S C exts (@specret_out T o))

  | red_spec_to_int32 :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (v : value (* input *)) (o1 : out) (y : (specret int)),
        (* ========================================== *)
        (red_expr (S : state) (C : execution_ctx) ((spec_to_number (v : value)) : ext_expr) (o1 : out)) ->
        (red_spec S C (spec_to_int32_1 (o1 : out)) y) ->
        (* ------------------------------------------ *)
        (red_spec S C (spec_to_int32 (v : value)) y)

  | red_spec_to_int32_1 :
      forall (S0 : state (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (n : number (* input *)),
        (* ========================================== *)
        (* ------------------------------------------ *)
        (red_spec S0 C (spec_to_int32_1 ((out_ter (S : state) (n : res)) : out)) (ret S (JsNumber.to_int32 n)))

  | red_spec_to_uint32 :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (v : value (* input *)) (o1 : out) (y : (specret int)),
        (* ========================================== *)
        (red_expr (S : state) (C : execution_ctx) ((spec_to_number (v : value)) : ext_expr) (o1 : out)) ->
        (red_spec S C (spec_to_uint32_1 (o1 : out)) y) ->
        (* ------------------------------------------ *)
        (red_spec S C (spec_to_uint32 (v : value)) y)

  | red_spec_to_uint32_1 :
      forall (S0 : state (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (n : number (* input *)),
        (* ========================================== *)
        (* ------------------------------------------ *)
        (red_spec S0 C (spec_to_uint32_1 ((out_ter (S : state) (n : res)) : out)) (ret S (JsNumber.to_uint32 n)))

  | red_spec_convert_twice :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (ex1 : ext_expr (* input *)) (ex2 : ext_expr (* input *)) (o1 : out) (y : (specret (value * value))),
        (* ========================================== *)
        (red_expr (S : state) (C : execution_ctx) (ex1 : ext_expr) (o1 : out)) ->
        (red_spec S C (spec_convert_twice_1 (o1 : out) (ex2 : ext_expr)) y) ->
        (* ------------------------------------------ *)
        (red_spec S C (spec_convert_twice (ex1 : ext_expr) (ex2 : ext_expr)) y)

  | red_spec_convert_twice_1 :
      forall (S0 : state (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (v1 : value (* input *)) (ex2 : ext_expr (* input *)) (o2 : out) (y : (specret (value * value))),
        (* ========================================== *)
        (red_expr (S : state) (C : execution_ctx) (ex2 : ext_expr) (o2 : out)) ->
        (red_spec S C (spec_convert_twice_2 (v1 : value) (o2 : out)) y) ->
        (* ------------------------------------------ *)
        (red_spec S0 C (spec_convert_twice_1 ((out_ter (S : state) (v1 : res)) : out) (ex2 : ext_expr)) y)

  | red_spec_convert_twice_2 :
      forall (S0 : state (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (v1 : value (* input *)) (v2 : value (* input *)),
        (* ========================================== *)
        (* ------------------------------------------ *)
        (red_spec S0 C (spec_convert_twice_2 (v1 : value) ((out_ter (S : state) (v2 : res)) : out)) (ret S (v1, v2)))

  | red_spec_expr_get_value_conv :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (e : expr (* input *)) (K : (value -> ext_expr) (* input *)) (y : (specret value)) (y1 : (specret value)),
        (* ========================================== *)
        (red_spec S C (spec_expr_get_value (e : expr)) y1) ->
        (red_spec S C (spec_expr_get_value_conv_1 (K : (value -> ext_expr)) (y1 : (specret value))) y) ->
        (* ------------------------------------------ *)
        (red_spec S C (spec_expr_get_value_conv (K : (value -> ext_expr)) (e : expr)) y)

  | red_spec_expr_get_value_conv_1 :
      forall (S0 : state (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (K : (value -> ext_expr) (* input *)) (v : value (* input *)) (o1 : out) (y : (specret value)),
        (* ========================================== *)
        (red_expr (S : state) (C : execution_ctx) ((K v) : ext_expr) (o1 : out)) ->
        (red_spec S0 C (spec_expr_get_value_conv_2 (o1 : out)) y) ->
        (* ------------------------------------------ *)
        (red_spec S0 C (spec_expr_get_value_conv_1 (K : (value -> ext_expr)) ((specret_val S v) : (specret value))) y)

  | red_spec_expr_get_value_conv_2 :
      forall (S0 : state (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (v : value (* input *)),
        (* ========================================== *)
        (* ------------------------------------------ *)
        (red_spec S0 C (spec_expr_get_value_conv_2 ((out_ter (S : state) (v : res)) : out)) (vret (S : state) (v : value)))

  | red_spec_list_expr :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (es : (list expr) (* input *)) (y : (specret (list value))),
        (* ========================================== *)
        (red_spec S C (spec_list_expr_1 (nil : (list value)) (es : (list expr))) y) ->
        (* ------------------------------------------ *)
        (red_spec S C (spec_list_expr (es : (list expr))) y)

  | red_spec_list_expr_1_nil :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (vs : (list value) (* input *)),
        (* ========================================== *)
        (* ------------------------------------------ *)
        (red_spec S C (spec_list_expr_1 (vs : (list value)) (nil : (list expr))) (ret S vs))

  | red_spec_list_expr_1_cons :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (vs : (list value) (* input *)) (es : (list expr) (* input *)) (e : expr (* input *)) (y1 : (specret value)) (y : (specret (list value))),
        (* ========================================== *)
        (red_spec S C (spec_expr_get_value (e : expr)) y1) ->
        (red_spec S C (spec_list_expr_2 (vs : (list value)) (y1 : (specret value)) (es : (list expr))) y) ->
        (* ------------------------------------------ *)
        (red_spec S C (spec_list_expr_1 (vs : (list value)) ((e :: (es : (list expr))) : (list expr))) y)

  | red_spec_list_expr_2 :
      forall (S0 : state (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (v : value (* input *)) (vs : (list value) (* input *)) (es : (list expr) (* input *)) (y : (specret (list value))),
        (* ========================================== *)
        (red_spec S C (spec_list_expr_1 (((vs : (list value)) & v) : (list value)) (es : (list expr))) y) ->
        (* ------------------------------------------ *)
        (red_spec S0 C (spec_list_expr_2 (vs : (list value)) ((specret_val S v) : (specret value)) (es : (list expr))) y)

  | red_spec_to_descriptor_not_object :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (v : value (* input *)) (y : (specret descriptor)),
        (((type_of v) : type) <> type_object) ->
        (* ========================================== *)
        (red_spec S C (spec_error_spec (native_error_type : native_error)) y) ->
        (* ------------------------------------------ *)
        (red_spec S C (spec_to_descriptor (v : value)) y)

  | red_spec_to_descriptor_object :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (l : object_loc (* input *)) (Desc : descriptor) (y : (specret descriptor)),
        (Desc = (descriptor_intro_empty : descriptor)) ->
        (* ========================================== *)
        (red_spec S C (spec_to_descriptor_1a (l : object_loc) (Desc : descriptor)) y) ->
        (* ------------------------------------------ *)
        (red_spec S C (spec_to_descriptor (l : value)) y)

  | red_spec_to_descriptor_1a :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (o1 : out) (l : object_loc (* input *)) (Desc : descriptor (* input *)) (y : (specret descriptor)),
        (* ========================================== *)
        (red_expr (S : state) (C : execution_ctx) ((spec_object_has_prop (l : object_loc) ((("enumerable")%string) : prop_name)) : ext_expr) (o1 : out)) ->
        (red_spec S C (spec_to_descriptor_1b (o1 : out) (l : object_loc) (Desc : descriptor)) y) ->
        (* ------------------------------------------ *)
        (red_spec S C (spec_to_descriptor_1a (l : object_loc) (Desc : descriptor)) y)

  | red_spec_to_descriptor_1b_false :
      forall (S0 : state (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (l : object_loc (* input *)) (Desc : descriptor (* input *)) (y : (specret descriptor)),
        (* ========================================== *)
        (red_spec S C (spec_to_descriptor_2a (l : object_loc) (Desc : descriptor)) y) ->
        (* ------------------------------------------ *)
        (red_spec S0 C (spec_to_descriptor_1b ((out_ter (S : state) (false : res)) : out) (l : object_loc) (Desc : descriptor)) y)

  | red_spec_to_descriptor_1b_true :
      forall (S0 : state (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (o1 : out) (l : object_loc (* input *)) (Desc : descriptor (* input *)) (y : (specret descriptor)),
        (* ========================================== *)
        (red_expr (S : state) (C : execution_ctx) ((spec_object_get (l : value) ((("enumerable")%string) : prop_name)) : ext_expr) (o1 : out)) ->
        (red_spec S C (spec_to_descriptor_1c (o1 : out) (l : object_loc) (Desc : descriptor)) y) ->
        (* ------------------------------------------ *)
        (red_spec S0 C (spec_to_descriptor_1b ((out_ter (S : state) (true : res)) : out) (l : object_loc) (Desc : descriptor)) y)

  | red_spec_to_descriptor_1c :
      forall (S0 : state (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (l : object_loc (* input *)) (v : value (* input *)) (b : bool) (Desc : descriptor (* input *)) (Desc' : descriptor) (y : (specret descriptor)),
        (b = ((convert_value_to_boolean (v : value)) : bool)) ->
        (Desc' = ((descriptor_with_enumerable Desc (Some b)) : descriptor)) ->
        (* ========================================== *)
        (red_spec S C (spec_to_descriptor_2a (l : object_loc) (Desc' : descriptor)) y) ->
        (* ------------------------------------------ *)
        (red_spec S0 C (spec_to_descriptor_1c ((out_ter (S : state) (v : res)) : out) (l : object_loc) (Desc : descriptor)) y)

  | red_spec_to_descriptor_2a :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (o1 : out) (l : object_loc (* input *)) (Desc : descriptor (* input *)) (y : (specret descriptor)),
        (* ========================================== *)
        (red_expr (S : state) (C : execution_ctx) ((spec_object_has_prop (l : object_loc) ((("configurable")%string) : prop_name)) : ext_expr) (o1 : out)) ->
        (red_spec S C (spec_to_descriptor_2b (o1 : out) (l : object_loc) (Desc : descriptor)) y) ->
        (* ------------------------------------------ *)
        (red_spec S C (spec_to_descriptor_2a (l : object_loc) (Desc : descriptor)) y)

  | red_spec_to_descriptor_2b_false :
      forall (S0 : state (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (l : object_loc (* input *)) (Desc : descriptor (* input *)) (y : (specret descriptor)),
        (* ========================================== *)
        (red_spec S C (spec_to_descriptor_3a (l : object_loc) (Desc : descriptor)) y) ->
        (* ------------------------------------------ *)
        (red_spec S0 C (spec_to_descriptor_2b ((out_ter (S : state) (false : res)) : out) (l : object_loc) (Desc : descriptor)) y)

  | red_spec_to_descriptor_2b_true :
      forall (S0 : state (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (o1 : out) (l : object_loc (* input *)) (Desc : descriptor (* input *)) (y : (specret descriptor)),
        (* ========================================== *)
        (red_expr (S : state) (C : execution_ctx) ((spec_object_get (l : value) ((("configurable")%string) : prop_name)) : ext_expr) (o1 : out)) ->
        (red_spec S C (spec_to_descriptor_2c (o1 : out) (l : object_loc) (Desc : descriptor)) y) ->
        (* ------------------------------------------ *)
        (red_spec S0 C (spec_to_descriptor_2b ((out_ter (S : state) (true : res)) : out) (l : object_loc) (Desc : descriptor)) y)

  | red_spec_to_descriptor_2c :
      forall (S0 : state (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (l : object_loc (* input *)) (v : value (* input *)) (b : bool) (Desc : descriptor (* input *)) (Desc' : descriptor) (y : (specret descriptor)),
        (b = ((convert_value_to_boolean (v : value)) : bool)) ->
        (Desc' = ((descriptor_with_configurable Desc (Some b)) : descriptor)) ->
        (* ========================================== *)
        (red_spec S C (spec_to_descriptor_3a (l : object_loc) (Desc' : descriptor)) y) ->
        (* ------------------------------------------ *)
        (red_spec S0 C (spec_to_descriptor_2c ((out_ter (S : state) (v : res)) : out) (l : object_loc) (Desc : descriptor)) y)

  | red_spec_to_descriptor_3a :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (o1 : out) (l : object_loc (* input *)) (Desc : descriptor (* input *)) (y : (specret descriptor)),
        (* ========================================== *)
        (red_expr (S : state) (C : execution_ctx) ((spec_object_has_prop (l : object_loc) ((("value")%string) : prop_name)) : ext_expr) (o1 : out)) ->
        (red_spec S C (spec_to_descriptor_3b (o1 : out) (l : object_loc) (Desc : descriptor)) y) ->
        (* ------------------------------------------ *)
        (red_spec S C (spec_to_descriptor_3a (l : object_loc) (Desc : descriptor)) y)

  | red_spec_to_descriptor_3b_false :
      forall (S0 : state (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (l : object_loc (* input *)) (Desc : descriptor (* input *)) (y : (specret descriptor)),
        (* ========================================== *)
        (red_spec S C (spec_to_descriptor_4a (l : object_loc) (Desc : descriptor)) y) ->
        (* ------------------------------------------ *)
        (red_spec S0 C (spec_to_descriptor_3b ((out_ter (S : state) (false : res)) : out) (l : object_loc) (Desc : descriptor)) y)

  | red_spec_to_descriptor_3b_true :
      forall (S0 : state (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (o1 : out) (l : object_loc (* input *)) (Desc : descriptor (* input *)) (y : (specret descriptor)),
        (* ========================================== *)
        (red_expr (S : state) (C : execution_ctx) ((spec_object_get (l : value) ((("value")%string) : prop_name)) : ext_expr) (o1 : out)) ->
        (red_spec S C (spec_to_descriptor_3c (o1 : out) (l : object_loc) (Desc : descriptor)) y) ->
        (* ------------------------------------------ *)
        (red_spec S0 C (spec_to_descriptor_3b ((out_ter (S : state) (true : res)) : out) (l : object_loc) (Desc : descriptor)) y)

  | red_spec_to_descriptor_3c :
      forall (S0 : state (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (l : object_loc (* input *)) (v : value (* input *)) (Desc : descriptor (* input *)) (Desc' : descriptor) (y : (specret descriptor)),
        (Desc' = ((descriptor_with_value Desc (Some v)) : descriptor)) ->
        (* ========================================== *)
        (red_spec S C (spec_to_descriptor_4a (l : object_loc) (Desc' : descriptor)) y) ->
        (* ------------------------------------------ *)
        (red_spec S0 C (spec_to_descriptor_3c ((out_ter (S : state) (v : res)) : out) (l : object_loc) (Desc : descriptor)) y)

  | red_spec_to_descriptor_4a :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (o1 : out) (l : object_loc (* input *)) (Desc : descriptor (* input *)) (y : (specret descriptor)),
        (* ========================================== *)
        (red_expr (S : state) (C : execution_ctx) ((spec_object_has_prop (l : object_loc) ((("writable")%string) : prop_name)) : ext_expr) (o1 : out)) ->
        (red_spec S C (spec_to_descriptor_4b (o1 : out) (l : object_loc) (Desc : descriptor)) y) ->
        (* ------------------------------------------ *)
        (red_spec S C (spec_to_descriptor_4a (l : object_loc) (Desc : descriptor)) y)

  | red_spec_to_descriptor_4b_false :
      forall (S0 : state (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (l : object_loc (* input *)) (Desc : descriptor (* input *)) (y : (specret descriptor)),
        (* ========================================== *)
        (red_spec S C (spec_to_descriptor_5a (l : object_loc) (Desc : descriptor)) y) ->
        (* ------------------------------------------ *)
        (red_spec S0 C (spec_to_descriptor_4b ((out_ter (S : state) (false : res)) : out) (l : object_loc) (Desc : descriptor)) y)

  | red_spec_to_descriptor_4b_true :
      forall (S0 : state (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (o1 : out) (l : object_loc (* input *)) (Desc : descriptor (* input *)) (y : (specret descriptor)),
        (* ========================================== *)
        (red_expr (S : state) (C : execution_ctx) ((spec_object_get (l : value) ((("writable")%string) : prop_name)) : ext_expr) (o1 : out)) ->
        (red_spec S C (spec_to_descriptor_4c (o1 : out) (l : object_loc) (Desc : descriptor)) y) ->
        (* ------------------------------------------ *)
        (red_spec S0 C (spec_to_descriptor_4b ((out_ter (S : state) (true : res)) : out) (l : object_loc) (Desc : descriptor)) y)

  | red_spec_to_descriptor_4c :
      forall (S0 : state (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (l : object_loc (* input *)) (v : value (* input *)) (b : bool) (Desc : descriptor (* input *)) (Desc' : descriptor) (y : (specret descriptor)),
        (b = ((convert_value_to_boolean (v : value)) : bool)) ->
        (Desc' = ((descriptor_with_writable Desc (Some b)) : descriptor)) ->
        (* ========================================== *)
        (red_spec S C (spec_to_descriptor_5a (l : object_loc) (Desc' : descriptor)) y) ->
        (* ------------------------------------------ *)
        (red_spec S0 C (spec_to_descriptor_4c ((out_ter (S : state) (v : res)) : out) (l : object_loc) (Desc : descriptor)) y)

  | red_spec_to_descriptor_5a :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (o1 : out) (l : object_loc (* input *)) (Desc : descriptor (* input *)) (y : (specret descriptor)),
        (* ========================================== *)
        (red_expr (S : state) (C : execution_ctx) ((spec_object_has_prop (l : object_loc) ((("get")%string) : prop_name)) : ext_expr) (o1 : out)) ->
        (red_spec S C (spec_to_descriptor_5b (o1 : out) (l : object_loc) (Desc : descriptor)) y) ->
        (* ------------------------------------------ *)
        (red_spec S C (spec_to_descriptor_5a (l : object_loc) (Desc : descriptor)) y)

  | red_spec_to_descriptor_5b_false :
      forall (S0 : state (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (l : object_loc (* input *)) (Desc : descriptor (* input *)) (y : (specret descriptor)),
        (* ========================================== *)
        (red_spec S C (spec_to_descriptor_6a (l : object_loc) (Desc : descriptor)) y) ->
        (* ------------------------------------------ *)
        (red_spec S0 C (spec_to_descriptor_5b ((out_ter (S : state) (false : res)) : out) (l : object_loc) (Desc : descriptor)) y)

  | red_spec_to_descriptor_5b_true :
      forall (S0 : state (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (o1 : out) (l : object_loc (* input *)) (Desc : descriptor (* input *)) (y : (specret descriptor)),
        (* ========================================== *)
        (red_expr (S : state) (C : execution_ctx) ((spec_object_get (l : value) ((("get")%string) : prop_name)) : ext_expr) (o1 : out)) ->
        (red_spec S C (spec_to_descriptor_5c (o1 : out) (l : object_loc) (Desc : descriptor)) y) ->
        (* ------------------------------------------ *)
        (red_spec S0 C (spec_to_descriptor_5b ((out_ter (S : state) (true : res)) : out) (l : object_loc) (Desc : descriptor)) y)

  | red_spec_to_descriptor_5c_error :
      forall (S0 : state (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (l : object_loc (* input *)) (v : value (* input *)) (Desc : descriptor (* input *)) (y : (specret descriptor)),
        ((((is_callable S v) = false) : Prop) /\ ((v <> undef) : Prop)) ->
        (* ========================================== *)
        (red_spec S C (spec_error_spec (native_error_type : native_error)) y) ->
        (* ------------------------------------------ *)
        (red_spec S0 C (spec_to_descriptor_5c ((out_ter (S : state) (v : res)) : out) (l : object_loc) (Desc : descriptor)) y)

  | red_spec_to_descriptor_5c_ok :
      forall (S0 : state (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (l : object_loc (* input *)) (v : value (* input *)) (Desc : descriptor (* input *)) (Desc' : descriptor) (y : (specret descriptor)),
        (~ ((((is_callable S v) = false) : Prop) /\ ((v <> undef) : Prop))) ->
        (Desc' = ((descriptor_with_get Desc (Some v)) : descriptor)) ->
        (* ========================================== *)
        (red_spec S C (spec_to_descriptor_6a (l : object_loc) (Desc' : descriptor)) y) ->
        (* ------------------------------------------ *)
        (red_spec S0 C (spec_to_descriptor_5c ((out_ter (S : state) (v : res)) : out) (l : object_loc) (Desc : descriptor)) y)

  | red_spec_to_descriptor_6a :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (o1 : out) (l : object_loc (* input *)) (Desc : descriptor (* input *)) (y : (specret descriptor)),
        (* ========================================== *)
        (red_expr (S : state) (C : execution_ctx) ((spec_object_has_prop (l : object_loc) ((("set")%string) : prop_name)) : ext_expr) (o1 : out)) ->
        (red_spec S C (spec_to_descriptor_6b (o1 : out) (l : object_loc) (Desc : descriptor)) y) ->
        (* ------------------------------------------ *)
        (red_spec S C (spec_to_descriptor_6a (l : object_loc) (Desc : descriptor)) y)

  | red_spec_to_descriptor_6b_false :
      forall (S0 : state (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (l : object_loc (* input *)) (Desc : descriptor (* input *)) (y : (specret descriptor)),
        (* ========================================== *)
        (red_spec S C (spec_to_descriptor_7 (l : object_loc) (Desc : descriptor)) y) ->
        (* ------------------------------------------ *)
        (red_spec S0 C (spec_to_descriptor_6b ((out_ter (S : state) (false : res)) : out) (l : object_loc) (Desc : descriptor)) y)

  | red_spec_to_descriptor_6b_true :
      forall (S0 : state (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (o1 : out) (l : object_loc (* input *)) (Desc : descriptor (* input *)) (y : (specret descriptor)),
        (* ========================================== *)
        (red_expr (S : state) (C : execution_ctx) ((spec_object_get (l : value) ((("set")%string) : prop_name)) : ext_expr) (o1 : out)) ->
        (red_spec S C (spec_to_descriptor_6c (o1 : out) (l : object_loc) (Desc : descriptor)) y) ->
        (* ------------------------------------------ *)
        (red_spec S0 C (spec_to_descriptor_6b ((out_ter (S : state) (true : res)) : out) (l : object_loc) (Desc : descriptor)) y)

  | red_spec_to_descriptor_6c_error :
      forall (S0 : state (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (l : object_loc (* input *)) (v : value (* input *)) (Desc : descriptor (* input *)) (y : (specret descriptor)),
        ((((is_callable S v) = false) : Prop) /\ ((v <> undef) : Prop)) ->
        (* ========================================== *)
        (red_spec S C (spec_error_spec (native_error_type : native_error)) y) ->
        (* ------------------------------------------ *)
        (red_spec S0 C (spec_to_descriptor_6c ((out_ter (S : state) (v : res)) : out) (l : object_loc) (Desc : descriptor)) y)

  | red_spec_to_descriptor_6c_ok :
      forall (S0 : state (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (l : object_loc (* input *)) (v : value (* input *)) (Desc : descriptor (* input *)) (Desc' : descriptor) (y : (specret descriptor)),
        (~ ((((is_callable S v) = false) : Prop) /\ ((v <> undef) : Prop))) ->
        (Desc' = ((descriptor_with_set Desc (Some v)) : descriptor)) ->
        (* ========================================== *)
        (red_spec S C (spec_to_descriptor_7 (l : object_loc) (Desc' : descriptor)) y) ->
        (* ------------------------------------------ *)
        (red_spec S0 C (spec_to_descriptor_6c ((out_ter (S : state) (v : res)) : out) (l : object_loc) (Desc : descriptor)) y)

  | red_spec_to_descriptor_7_error :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (l : object_loc (* input *)) (Desc : descriptor (* input *)) (y : (specret descriptor)),
        (descriptor_inconsistent (Desc : descriptor)) ->
        (* ========================================== *)
        (red_spec S C (spec_error_spec (native_error_type : native_error)) y) ->
        (* ------------------------------------------ *)
        (red_spec S C (spec_to_descriptor_7 (l : object_loc) (Desc : descriptor)) y)

  | red_spec_to_descriptor_7_ok :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (l : object_loc (* input *)) (Desc : descriptor (* input *)),
        (~ (descriptor_inconsistent (Desc : descriptor))) ->
        (* ========================================== *)
        (* ------------------------------------------ *)
        (red_spec S C (spec_to_descriptor_7 (l : object_loc) (Desc : descriptor)) (ret S Desc))

  | red_spec_object_get_own_prop :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (l : object_loc (* input *)) (x : prop_name (* input *)) (B : builtin_get_own_prop) (y : (specret full_descriptor)),
        (object_method object_get_own_prop_ S l B) ->
        (* ========================================== *)
        (red_spec S C (spec_object_get_own_prop_1 (B : builtin_get_own_prop) (l : object_loc) (x : prop_name)) y) ->
        (* ------------------------------------------ *)
        (red_spec S C (spec_object_get_own_prop (l : object_loc) (x : prop_name)) y)

  | red_spec_object_get_own_prop_1_default :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (l : object_loc (* input *)) (x : prop_name (* input *)) (Ao : (option attributes)) (y : (specret full_descriptor)),
        (object_property S l x Ao) ->
        (* ========================================== *)
        (red_spec S C (spec_object_get_own_prop_2 (l : object_loc) (x : prop_name) (Ao : (option attributes))) y) ->
        (* ------------------------------------------ *)
        (red_spec S C (spec_object_get_own_prop_1 (builtin_get_own_prop_default : builtin_get_own_prop) (l : object_loc) (x : prop_name)) y)

  | red_spec_object_get_own_prop_2_none :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (l : object_loc (* input *)) (x : prop_name (* input *)),
        (* ========================================== *)
        (* ------------------------------------------ *)
        (red_spec S C (spec_object_get_own_prop_2 (l : object_loc) (x : prop_name) (None : (option attributes))) (dret (S : state) (full_descriptor_undef : full_descriptor)))

  | red_spec_object_get_own_prop_2_some_data :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (l : object_loc (* input *)) (x : prop_name (* input *)) (A : attributes (* input *)),
        (* ========================================== *)
        (* ------------------------------------------ *)
        (red_spec S C (spec_object_get_own_prop_2 (l : object_loc) (x : prop_name) ((Some A) : (option attributes))) (ret S (full_descriptor_some (A : attributes))))

  | red_spec_object_get_own_prop_args_obj :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (l : object_loc (* input *)) (x : prop_name (* input *)) (y : (specret full_descriptor)) (y1 : (specret full_descriptor)),
        (* ========================================== *)
        (red_spec S C (spec_object_get_own_prop_1 (builtin_get_own_prop_default : builtin_get_own_prop) (l : object_loc) (x : prop_name)) y1) ->
        (red_spec S C (spec_args_obj_get_own_prop_1 (l : object_loc) (x : prop_name) (y1 : (specret full_descriptor))) y) ->
        (* ------------------------------------------ *)
        (red_spec S C (spec_object_get_own_prop_1 (builtin_get_own_prop_args_obj : builtin_get_own_prop) (l : object_loc) (x : prop_name)) y)

  | red_spec_object_get_own_prop_args_obj_1_undef :
      forall (S0 : state (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (l : object_loc (* input *)) (x : prop_name (* input *)),
        (* ========================================== *)
        (* ------------------------------------------ *)
        (red_spec S0 C (spec_args_obj_get_own_prop_1 (l : object_loc) (x : prop_name) ((specret_val S full_descriptor_undef) : (specret full_descriptor))) (ret S full_descriptor_undef))

  | red_spec_object_get_own_prop_args_obj_1_attrs :
      forall (lmap : object_loc) (S0 : state (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (l : object_loc (* input *)) (x : prop_name (* input *)) (A : attributes (* input *)) (y : (specret full_descriptor)) (y1 : (specret full_descriptor)),
        (object_method object_parameter_map_ S l (Some lmap)) ->
        (* ========================================== *)
        (red_spec S C (spec_object_get_own_prop (lmap : object_loc) (x : prop_name)) y1) ->
        (red_spec S C (spec_args_obj_get_own_prop_2 (l : object_loc) (x : prop_name) (lmap : object_loc) (A : full_descriptor) (y1 : (specret full_descriptor))) y) ->
        (* ------------------------------------------ *)
        (red_spec S0 C (spec_args_obj_get_own_prop_1 (l : object_loc) (x : prop_name) ((specret_val S (full_descriptor_some (A : attributes))) : (specret full_descriptor))) y)

  | red_spec_object_get_own_prop_args_obj_2_attrs :
      forall (o1 : out) (S0 : state (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (l : object_loc (* input *)) (x : prop_name (* input *)) (lmap : object_loc (* input *)) (A : attributes (* input *)) (Amap : attributes (* input *)) (y : (specret full_descriptor)),
        (* ========================================== *)
        (red_expr (S0 : state) (C : execution_ctx) ((spec_object_get ((value_object (lmap : object_loc)) : value) (x : prop_name)) : ext_expr) (o1 : out)) ->
        (red_spec S0 C (spec_args_obj_get_own_prop_3 (A : full_descriptor) (o1 : out)) y) ->
        (* ------------------------------------------ *)
        (red_spec S C (spec_args_obj_get_own_prop_2 (l : object_loc) (x : prop_name) (lmap : object_loc) (A : full_descriptor) ((specret_val S0 (full_descriptor_some (Amap : attributes))) : (specret full_descriptor))) y)

  | red_spec_object_get_own_prop_args_obj_3 :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (Ad : attributes_data (* input *)) (S' : state (* input *)) (v : value (* input *)) (y : (specret full_descriptor)),
        (* ========================================== *)
        (red_spec S' C (spec_args_obj_get_own_prop_4 ((attributes_data_with_value Ad v) : full_descriptor)) y) ->
        (* ------------------------------------------ *)
        (red_spec S C (spec_args_obj_get_own_prop_3 ((attributes_data_of (Ad : attributes_data)) : full_descriptor) ((out_ter (S' : state) (v : res)) : out)) y)

  | red_spec_object_get_own_prop_args_obj_2_undef :
      forall (S0 : state (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (l : object_loc (* input *)) (x : prop_name (* input *)) (lmap : object_loc (* input *)) (A : attributes (* input *)) (y : (specret full_descriptor)),
        (* ========================================== *)
        (red_spec S0 C (spec_args_obj_get_own_prop_4 (A : full_descriptor)) y) ->
        (* ------------------------------------------ *)
        (red_spec S C (spec_args_obj_get_own_prop_2 (l : object_loc) (x : prop_name) (lmap : object_loc) (A : full_descriptor) ((specret_val S0 full_descriptor_undef) : (specret full_descriptor))) y)

  | red_spec_object_get_own_prop_args_obj_4 :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (A : attributes (* input *)),
        (* ========================================== *)
        (* ------------------------------------------ *)
        (red_spec S C (spec_args_obj_get_own_prop_4 (A : full_descriptor)) (ret S (full_descriptor_some (A : attributes))))

  | red_spec_object_get_own_prop_string :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (l : object_loc (* input *)) (x : prop_name (* input *)) (y : (specret full_descriptor)) (y1 : (specret full_descriptor)),
        (* ========================================== *)
        (red_spec S C (spec_object_get_own_prop_1 (builtin_get_own_prop_default : builtin_get_own_prop) (l : object_loc) (x : prop_name)) y1) ->
        (red_spec S C (spec_string_get_own_prop_1 (l : object_loc) (x : prop_name) (y1 : (specret full_descriptor))) y) ->
        (* ------------------------------------------ *)
        (red_spec S C (spec_object_get_own_prop_1 (builtin_get_own_prop_string : builtin_get_own_prop) (l : object_loc) (x : prop_name)) y)

  | red_spec_object_get_own_prop_string_1_attrs :
      forall (S0 : state (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (l : object_loc (* input *)) (x : prop_name (* input *)) (A : attributes (* input *)),
        (* ========================================== *)
        (* ------------------------------------------ *)
        (red_spec S0 C (spec_string_get_own_prop_1 (l : object_loc) (x : prop_name) ((specret_val S (full_descriptor_some (A : attributes))) : (specret full_descriptor))) (ret S (full_descriptor_some (A : attributes))))

  | red_spec_object_get_own_prop_string_1_undef :
      forall (S0 : state (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (l : object_loc (* input *)) (x : prop_name (* input *)) (y1 : (specret int)) (y : (specret full_descriptor)),
        (* ========================================== *)
        (red_spec S C (spec_to_int32 (x : value)) y1) ->
        (red_spec S C (spec_string_get_own_prop_2 (l : object_loc) (x : prop_name) (y1 : (specret int))) y) ->
        (* ------------------------------------------ *)
        (red_spec S0 C (spec_string_get_own_prop_1 (l : object_loc) (x : prop_name) ((specret_val S full_descriptor_undef) : (specret full_descriptor))) y)

  | red_spec_object_get_own_prop_string_2 :
      forall (S0 : state (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (l : object_loc (* input *)) (x : prop_name (* input *)) (k : int (* input *)) (o1 : out) (y : (specret full_descriptor)),
        (* ========================================== *)
        (red_expr (S : state) (C : execution_ctx) ((spec_to_string ((abs k) : value)) : ext_expr) (o1 : out)) ->
        (red_spec S C (spec_string_get_own_prop_3 (l : object_loc) (x : prop_name) (o1 : out)) y) ->
        (* ------------------------------------------ *)
        (red_spec S0 C (spec_string_get_own_prop_2 (l : object_loc) (x : prop_name) ((specret_val S k) : (specret int))) y)

  | red_spec_object_get_own_prop_string_3_different :
      forall (S0 : state (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (l : object_loc (* input *)) (x : prop_name (* input *)) (x' : prop_name (* input *)),
        (x <> (x' : prop_name)) ->
        (* ========================================== *)
        (* ------------------------------------------ *)
        (red_spec S0 C (spec_string_get_own_prop_3 (l : object_loc) (x : prop_name) ((out_ter (S : state) (x' : res)) : out)) (ret S full_descriptor_undef))

  | red_spec_object_get_own_prop_string_3_same :
      forall (S0 : state (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (l : object_loc (* input *)) (s : string) (x : prop_name (* input *)) (y : (specret full_descriptor)),
        (object_prim_value (S : state) (l : object_loc) (s : value)) ->
        (* ========================================== *)
        (red_spec S C (spec_string_get_own_prop_4 (x : prop_name) (s : string)) y) ->
        (* ------------------------------------------ *)
        (red_spec S0 C (spec_string_get_own_prop_3 (l : object_loc) (x : prop_name) ((out_ter (S : state) (x : res)) : out)) y)

  | red_spec_object_get_own_prop_string_4 :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (x : prop_name (* input *)) (s : string (* input *)) (y1 : (specret int)) (y : (specret full_descriptor)),
        (* ========================================== *)
        (red_spec S C (spec_to_int32 (x : value)) y1) ->
        (red_spec S C (spec_string_get_own_prop_5 (s : string) (y1 : (specret int))) y) ->
        (* ------------------------------------------ *)
        (red_spec S C (spec_string_get_own_prop_4 (x : prop_name) (s : string)) y)

  | red_spec_object_get_own_prop_string_5 :
      forall (S0 : state (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (s : string (* input *)) (idx : int (* input *)) (len : nat) (y : (specret full_descriptor)),
        ((len : nat) = (String.length s)) ->
        (* ========================================== *)
        (red_spec S C (spec_string_get_own_prop_6 (s : string) (idx : int) (len : int)) y) ->
        (* ------------------------------------------ *)
        (red_spec S0 C (spec_string_get_own_prop_5 (s : string) ((specret_val S idx) : (specret int))) y)

  | red_spec_object_get_own_prop_string_6_outofbounds :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (s : string (* input *)) (idx : int (* input *)) (len : int (* input *)),
        (len <= idx) ->
        (* ========================================== *)
        (* ------------------------------------------ *)
        (red_spec S C (spec_string_get_own_prop_6 (s : string) (idx : int) (len : int)) (ret S full_descriptor_undef))

  | red_spec_object_get_own_prop_string_6_inbounds :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (s : string (* input *)) (idx : int (* input *)) (len : int (* input *)),
        (len > idx) ->
        (* ========================================== *)
        (* ------------------------------------------ *)
        (red_spec S C (spec_string_get_own_prop_6 (s : string) (idx : int) (len : int)) (ret S (full_descriptor_some ((attributes_data_intro ((string_sub s idx (1%nat)) : value) (false : bool) (true : bool) (false : bool)) : attributes))))

  | red_spec_ref_get_value_value :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (v : value (* input *)),
        (* ========================================== *)
        (* ------------------------------------------ *)
        (red_spec S C (spec_get_value (v : resvalue)) (ret S v))

  | red_spec_ref_get_value_ref_a :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (r : ref (* input *)) (y : (specret value)),
        (ref_is_unresolvable (r : ref)) ->
        (* ========================================== *)
        (red_spec S C (spec_error_spec (native_error_ref : native_error)) y) ->
        (* ------------------------------------------ *)
        (red_spec S C (spec_get_value (r : resvalue)) y)

  | red_spec_ref_get_value_ref_b :
      forall (ext_get : (value -> (prop_name -> ext_expr))) (v : value) (S : state (* input *)) (C : execution_ctx (* input *)) (r : ref (* input *)) (o1 : out) (y : (specret value)),
        (ref_is_property (r : ref)) ->
        ((ref_base (r : ref)) = ((ref_base_type_value (v : value)) : ref_base_type)) ->
        ((ext_get : (value -> (prop_name -> ext_expr))) = (ifb (ref_has_primitive_base (r : ref)) then (spec_prim_value_get : (value -> (prop_name -> ext_expr))) else spec_object_get)) ->
        (* ========================================== *)
        (red_expr (S : state) (C : execution_ctx) ((ext_get v (ref_name (r : ref))) : ext_expr) (o1 : out)) ->
        (red_spec S C (spec_get_value_ref_b_1 (o1 : out)) y) ->
        (* ------------------------------------------ *)
        (red_spec S C (spec_get_value (r : resvalue)) y)

  | red_spec_ref_get_value_ref_b_1 :
      forall (S0 : state (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (v : value (* input *)),
        (* ========================================== *)
        (* ------------------------------------------ *)
        (red_spec S0 C (spec_get_value_ref_b_1 ((out_ter (S : state) (v : res)) : out)) (ret S v))

  | red_spec_ref_get_value_ref_c :
      forall (L : env_loc) (S : state (* input *)) (C : execution_ctx (* input *)) (r : ref (* input *)) (o1 : out) (y : (specret value)),
        ((ref_base (r : ref)) = ((ref_base_type_env_loc (L : env_loc)) : ref_base_type)) ->
        (* ========================================== *)
        (red_expr (S : state) (C : execution_ctx) ((spec_env_record_get_binding_value (L : env_loc) ((ref_name (r : ref)) : prop_name) ((ref_strict (r : ref)) : bool)) : ext_expr) (o1 : out)) ->
        (red_spec S C (spec_get_value_ref_c_1 (o1 : out)) y) ->
        (* ------------------------------------------ *)
        (red_spec S C (spec_get_value (r : resvalue)) y)

  | red_spec_ref_get_value_ref_c_1 :
      forall (S0 : state (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (v : value (* input *)),
        (* ========================================== *)
        (* ------------------------------------------ *)
        (red_spec S0 C (spec_get_value_ref_c_1 ((out_ter (S : state) (v : res)) : out)) (ret S v))

  | red_spec_expr_get_value :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (e : expr (* input *)) (o1 : out) (y : (specret value)),
        (* ========================================== *)
        (red_expr (S : state) (C : execution_ctx) (e : ext_expr) (o1 : out)) ->
        (red_spec S C (spec_expr_get_value_1 (o1 : out)) y) ->
        (* ------------------------------------------ *)
        (red_spec S C (spec_expr_get_value (e : expr)) y)

  | red_spec_expr_get_value_1 :
      forall (S0 : state (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (rv : resvalue (* input *)) (y : (specret value)),
        (* ========================================== *)
        (red_spec S C (spec_get_value (rv : resvalue)) y) ->
        (* ------------------------------------------ *)
        (red_spec S0 C (spec_expr_get_value_1 ((out_ter (S : state) (rv : res)) : out)) y)

  | red_spec_lexical_env_get_identifier_ref_nil :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (x : prop_name (* input *)) (str : strictness_flag (* input *)) (r : ref),
        (r = ((ref_create_value undef x str) : ref)) ->
        (* ========================================== *)
        (* ------------------------------------------ *)
        (red_spec S C (spec_lexical_env_get_identifier_ref (nil : lexical_env) (x : prop_name) (str : bool)) (ret S r))

  | red_spec_lexical_env_get_identifier_ref_cons :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (L : env_loc (* input *)) (lexs : (list env_loc) (* input *)) (x : prop_name (* input *)) (str : strictness_flag (* input *)) (y : (specret ref)),
        (* ========================================== *)
        (red_spec S C (spec_lexical_env_get_identifier_ref_1 (L : env_loc) (lexs : lexical_env) (x : prop_name) (str : bool)) y) ->
        (* ------------------------------------------ *)
        (red_spec S C (spec_lexical_env_get_identifier_ref ((L :: (lexs : (list env_loc))) : lexical_env) (x : prop_name) (str : bool)) y)

  | red_spec_lexical_env_get_identifier_ref_cons_1 :
      forall (o1 : out) (S : state (* input *)) (C : execution_ctx (* input *)) (L : env_loc (* input *)) (lexs : lexical_env (* input *)) (x : prop_name (* input *)) (str : strictness_flag (* input *)) (y : (specret ref)),
        (* ========================================== *)
        (red_expr (S : state) (C : execution_ctx) ((spec_env_record_has_binding (L : env_loc) (x : prop_name)) : ext_expr) (o1 : out)) ->
        (red_spec S C (spec_lexical_env_get_identifier_ref_2 (L : env_loc) (lexs : lexical_env) (x : prop_name) (str : bool) (o1 : out)) y) ->
        (* ------------------------------------------ *)
        (red_spec S C (spec_lexical_env_get_identifier_ref_1 (L : env_loc) (lexs : lexical_env) (x : prop_name) (str : bool)) y)

  | red_spec_lexical_env_get_identifier_ref_cons_2_true :
      forall (S0 : state (* input *)) (C : execution_ctx (* input *)) (L : env_loc (* input *)) (lexs : lexical_env (* input *)) (x : prop_name (* input *)) (str : strictness_flag (* input *)) (S : state (* input *)) (r : ref),
        (r = ((ref_create_env_loc L x str) : ref)) ->
        (* ========================================== *)
        (* ------------------------------------------ *)
        (red_spec S0 C (spec_lexical_env_get_identifier_ref_2 (L : env_loc) (lexs : lexical_env) (x : prop_name) (str : bool) ((out_ter (S : state) (true : res)) : out)) (ret S r))

  | red_spec_lexical_env_get_identifier_ref_cons_2_false :
      forall (S0 : state (* input *)) (C : execution_ctx (* input *)) (L : env_loc (* input *)) (lexs : lexical_env (* input *)) (x : prop_name (* input *)) (str : strictness_flag (* input *)) (S : state (* input *)) (y : (specret ref)),
        (* ========================================== *)
        (red_spec S C (spec_lexical_env_get_identifier_ref (lexs : lexical_env) (x : prop_name) (str : bool)) y) ->
        (* ------------------------------------------ *)
        (red_spec S0 C (spec_lexical_env_get_identifier_ref_2 (L : env_loc) (lexs : lexical_env) (x : prop_name) (str : bool) ((out_ter (S : state) (false : res)) : out)) y)

  | red_spec_error_spec :
      forall (T : _) (S : state (* input *)) (C : execution_ctx (* input *)) (ne : native_error (* input *)) (o1 : out) (y : (specret T)),
        (* ========================================== *)
        (red_expr (S : state) (C : execution_ctx) ((spec_error (ne : native_error)) : ext_expr) (o1 : out)) ->
        (red_spec S C (spec_error_spec_1 (o1 : out)) y) ->
        (* ------------------------------------------ *)
        (red_spec S C (spec_error_spec (ne : native_error)) y)

  | red_spec_object_get_prop :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (l : object_loc (* input *)) (x : prop_name (* input *)) (B : builtin_get_prop) (y : (specret full_descriptor)),
        (object_method object_get_prop_ S l B) ->
        (* ========================================== *)
        (red_spec S C (spec_object_get_prop_1 (B : builtin_get_prop) (l : object_loc) (x : prop_name)) y) ->
        (* ------------------------------------------ *)
        (red_spec S C (spec_object_get_prop (l : object_loc) (x : prop_name)) y)

  | red_spec_object_get_prop_1_default :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (l : object_loc (* input *)) (x : prop_name (* input *)) (y1 : (specret full_descriptor)) (y : (specret full_descriptor)),
        (* ========================================== *)
        (red_spec S C (spec_object_get_own_prop (l : object_loc) (x : prop_name)) y1) ->
        (red_spec S C (spec_object_get_prop_2 (l : object_loc) (x : prop_name) (y1 : (specret full_descriptor))) y) ->
        (* ------------------------------------------ *)
        (red_spec S C (spec_object_get_prop_1 (builtin_get_prop_default : builtin_get_prop) (l : object_loc) (x : prop_name)) y)

  | red_spec_object_get_prop_2_not_undef :
      forall (S0 : state (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (l : object_loc (* input *)) (x : prop_name (* input *)) (A : attributes (* input *)),
        (* ========================================== *)
        (* ------------------------------------------ *)
        (red_spec S0 C (spec_object_get_prop_2 (l : object_loc) (x : prop_name) ((specret_val S (full_descriptor_some (A : attributes))) : (specret full_descriptor))) (ret S (full_descriptor_some (A : attributes))))

  | red_spec_object_get_prop_2_undef :
      forall (S0 : state (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (l : object_loc (* input *)) (x : prop_name (* input *)) (vproto : value) (y : (specret full_descriptor)),
        (object_proto (S : state) (l : object_loc) (vproto : value)) ->
        (* ========================================== *)
        (red_spec S C (spec_object_get_prop_3 (l : object_loc) (x : prop_name) (vproto : value)) y) ->
        (* ------------------------------------------ *)
        (red_spec S0 C (spec_object_get_prop_2 (l : object_loc) (x : prop_name) ((specret_val S full_descriptor_undef) : (specret full_descriptor))) y)

  | red_spec_object_get_prop_3_null :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (l : object_loc (* input *)) (x : prop_name (* input *)),
        (* ========================================== *)
        (* ------------------------------------------ *)
        (red_spec S C (spec_object_get_prop_3 (l : object_loc) (x : prop_name) (null : value)) (dret (S : state) (full_descriptor_undef : full_descriptor)))

  | red_spec_object_get_prop_3_not_null :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (l : object_loc (* input *)) (x : prop_name (* input *)) (lproto : object_loc (* input *)) (y : (specret full_descriptor)),
        (* ========================================== *)
        (red_spec S C (spec_object_get_prop (lproto : object_loc) (x : prop_name)) y) ->
        (* ------------------------------------------ *)
        (red_spec S C (spec_object_get_prop_3 (l : object_loc) (x : prop_name) (lproto : value)) y)
  .


(******************************************)

