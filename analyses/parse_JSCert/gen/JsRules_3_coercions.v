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
Implicit Type ct : codetype.
Implicit Type vthis : value.
Implicit Type vp : value.
Implicit Type vi : value.
Implicit Type lp : object_loc.
Implicit Type pref : preftype.
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
Implicit Type o : out.
Implicit Type R : res.
Implicit Type labs : label_set.
Implicit Type lab : label.
Implicit Type rv : resvalue.
Implicit Type rt : restype.
Implicit Type ty : type.
Implicit Type r : ref.
Implicit Type v : value.
Implicit Type w : prim.
Implicit Type l : object_loc.
Implicit Type i : literal.
Implicit Type s : string.
Implicit Type k : int.
Implicit Type n : number.
Implicit Type b : bool.

(******************************************)

Inductive red_javascript : prog (* input *) -> out -> Prop :=

  | red_javascript_intro :
      forall (p : prog (* input *)) (o : out) (o1 : out),
        (* ========================================== *)
        (red_expr state_initial (execution_ctx_initial ((prog_intro_strictness ((add_infos_prog strictness_false p) : prog)) : strictness_flag)) (spec_binding_inst codetype_global (None : (option object_loc)) ((add_infos_prog strictness_false p) : prog) (nil : (list value))) o1) ->
        (red_prog state_initial (execution_ctx_initial ((prog_intro_strictness ((add_infos_prog strictness_false p) : prog)) : strictness_flag)) (javascript_1 o1 ((add_infos_prog strictness_false p) : prog)) o) ->
        (* ------------------------------------------ *)
        (red_javascript p o)


with red_prog : state (* input *) -> execution_ctx (* input *) -> ext_prog (* input *) -> out -> Prop :=

  | red_prog_abort :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (extp : ext_prog (* input *)) (o : out),
        ((out_of_ext_prog extp) = ((Some o) : (option out))) ->
        (abort o) ->
        (abort_intercepted_prog extp) ->
        (* ========================================== *)
        (* ------------------------------------------ *)
        (red_prog S C extp o)

  | red_javascript_intro_1 :
      forall (S : state (* input *)) (S' : state (* input *)) (C : execution_ctx (* input *)) (p : prog (* input *)) (o : out),
        (* ========================================== *)
        (red_prog S' C (prog_basic p) o) ->
        (* ------------------------------------------ *)
        (red_prog S C (javascript_1 (out_ter S' (res_intro restype_normal resvalue_empty label_empty)) p) o)

  | red_prog_nil :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (str : strictness_flag (* input *)),
        (* ========================================== *)
        (* ------------------------------------------ *)
        (red_prog S C (prog_basic (prog_intro str (nil : (list element)))) (out_ter S (resvalue_empty : res)))

  | red_prog_cons :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (str : strictness_flag (* input *)) (el : element (* input *)) (els : (list element) (* input *)) (o1 : out) (o : out),
        (* ========================================== *)
        (red_prog S C (prog_basic (prog_intro str els)) o1) ->
        (red_prog S C (prog_1 o1 el) o) ->
        (* ------------------------------------------ *)
        (red_prog S C (prog_basic (prog_intro str (els & el))) o)

  | red_prog_1_funcdecl :
      forall (S0 : state (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (rv : resvalue (* input *)) (name : string (* input *)) (args : (list string) (* input *)) (bd : funcbody (* input *)),
        (* ========================================== *)
        (* ------------------------------------------ *)
        (red_prog S0 C (prog_1 (out_ter S (rv : res)) (element_func_decl name args bd)) (out_ter S (rv : res)))

  | red_prog_1_stat :
      forall (S0 : state (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (t : stat (* input *)) (rv : resvalue (* input *)) (o1 : out) (o : out),
        (* ========================================== *)
        (red_stat S C (stat_basic t) o1) ->
        (red_prog S C (prog_2 rv o1) o) ->
        (* ------------------------------------------ *)
        (red_prog S0 C (prog_1 (out_ter S (rv : res)) (element_stat t)) o)

  | red_prog_2 :
      forall (S0 : state (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (R : res (* input *)) (rv : resvalue (* input *)),
        (* ========================================== *)
        (* ------------------------------------------ *)
        (red_prog S0 C (prog_2 rv (out_ter S R)) (out_ter S (res_overwrite_value_if_empty rv R)))


with red_stat : state (* input *) -> execution_ctx (* input *) -> ext_stat (* input *) -> out -> Prop :=

  | red_stat_abort :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (extt : ext_stat (* input *)) (o : out),
        ((out_of_ext_stat extt) = ((Some o) : (option out))) ->
        (abort o) ->
        (abort_intercepted_stat extt) ->
        (* ========================================== *)
        (* ------------------------------------------ *)
        (red_stat S C extt o)

  | red_stat_block_nil :
      forall (S : state (* input *)) (C : execution_ctx (* input *)),
        (* ========================================== *)
        (* ------------------------------------------ *)
        (red_stat S C (stat_basic (stat_block (nil : (list stat)))) (out_ter S (resvalue_empty : res)))

  | red_stat_block_cons :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (t : stat (* input *)) (ts : (list stat) (* input *)) (o1 : out) (o : out),
        (* ========================================== *)
        (red_stat S C (stat_basic (stat_block ts)) o1) ->
        (red_stat S C (stat_block_1 o1 t) o) ->
        (* ------------------------------------------ *)
        (red_stat S C (stat_basic (stat_block (ts ++ (t :: (nil : (list stat)))))) o)

  | red_stat_block_1 :
      forall (S0 : state (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (t : stat (* input *)) (rv : resvalue (* input *)) (o : out) (o1 : out),
        (* ========================================== *)
        (red_stat S C (stat_basic t) o1) ->
        (red_stat S C (stat_block_2 rv o1) o) ->
        (* ------------------------------------------ *)
        (red_stat S0 C (stat_block_1 (out_ter S (rv : res)) t) o)

  | red_stat_block_2_throw :
      forall (S0 : state (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (R : res (* input *)) (rv : resvalue (* input *)),
        ((res_type R) = restype_throw) ->
        (* ========================================== *)
        (* ------------------------------------------ *)
        (red_stat S0 C (stat_block_2 rv (out_ter S R)) (out_ter S R))

  | red_stat_block_2_not_throw :
      forall (S0 : state (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (R : res (* input *)) (rv : resvalue (* input *)),
        ((res_type R) <> restype_throw) ->
        (* ========================================== *)
        (* ------------------------------------------ *)
        (red_stat S0 C (stat_block_2 rv (out_ter S R)) (out_ter S (res_overwrite_value_if_empty rv R)))

  | red_stat_var_decl_nil :
      forall (S : state (* input *)) (C : execution_ctx (* input *)),
        (* ========================================== *)
        (* ------------------------------------------ *)
        (red_stat S C (stat_basic (stat_var_decl (nil : (list (string * (option expr)))))) (out_ter S res_empty))

  | red_stat_var_decl_cons :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (o : out) (o1 : out) (d : (string * (option expr)) (* input *)) (ds : (list (string * (option expr))) (* input *)),
        (* ========================================== *)
        (red_stat S C (stat_var_decl_item d) o1) ->
        (red_stat S C (stat_var_decl_1 o1 ds) o) ->
        (* ------------------------------------------ *)
        (red_stat S C (stat_basic (stat_var_decl (d :: ds))) o)

  | red_stat_var_decl_1 :
      forall (S : state (* input *)) (S0 : state (* input *)) (C : execution_ctx (* input *)) (ds : (list (string * (option expr))) (* input *)) (o : out) (rv : resvalue (* input *)),
        (* ========================================== *)
        (red_stat S C (stat_basic (stat_var_decl ds)) o) ->
        (* ------------------------------------------ *)
        (red_stat S0 C (stat_var_decl_1 (out_ter S (rv : res)) ds) o)

  | red_stat_var_decl_item_none :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (x : prop_name (* input *)),
        (* ========================================== *)
        (* ------------------------------------------ *)
        (red_stat S C (stat_var_decl_item ((x, None) : (string * (option expr)))) (out_ter S ((resvalue_value (value_prim (prim_string (x : string)))) : res)))

  | red_stat_var_decl_item_some :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (x : prop_name (* input *)) (e : expr (* input *)) (y1 : (specret ref)) (o : out),
        (* ========================================== *)
        (red_spec S C (spec_identifier_resolution C x) y1) ->
        (red_stat S C (stat_var_decl_item_1 (x : string) y1 e) o) ->
        (* ------------------------------------------ *)
        (red_stat S C (stat_var_decl_item ((x, (Some e)) : (string * (option expr)))) o)

  | red_stat_var_decl_item_1 :
      forall (S : state (* input *)) (S0 : state (* input *)) (C : execution_ctx (* input *)) (x : prop_name (* input *)) (e : expr (* input *)) (r : ref (* input *)) (y1 : (specret value)) (o : out),
        (* ========================================== *)
        (red_spec S C (spec_expr_get_value e) y1) ->
        (red_stat S C (stat_var_decl_item_2 (x : string) r y1) o) ->
        (* ------------------------------------------ *)
        (red_stat S0 C (stat_var_decl_item_1 (x : string) ((specret_val S r) : (specret ref)) e) o)

  | red_stat_var_decl_item_2 :
      forall (S : state (* input *)) (S0 : state (* input *)) (C : execution_ctx (* input *)) (r : ref (* input *)) (v : value (* input *)) (o : out) (o1 : out) (x : prop_name (* input *)),
        (* ========================================== *)
        (red_expr S C (spec_put_value (resvalue_ref r) v) o1) ->
        (red_stat S C (stat_var_decl_item_3 (x : string) o1) o) ->
        (* ------------------------------------------ *)
        (red_stat S0 C (stat_var_decl_item_2 (x : string) r ((specret_val S v) : (specret value))) o)

  | red_stat_var_decl_item_3 :
      forall (S : state (* input *)) (S0 : state (* input *)) (C : execution_ctx (* input *)) (x : prop_name (* input *)),
        (* ========================================== *)
        (* ------------------------------------------ *)
        (red_stat S0 C (stat_var_decl_item_3 (x : string) (out_ter S (res_intro restype_normal resvalue_empty label_empty))) (out_ter S ((resvalue_value (value_prim (prim_string (x : string)))) : res)))

  | red_stat_expr :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (e : expr (* input *)) (o : out) (y1 : (specret value)),
        (* ========================================== *)
        (red_spec S C (spec_expr_get_value e) y1) ->
        (red_stat S C (stat_expr_1 y1) o) ->
        (* ------------------------------------------ *)
        (red_stat S C (stat_basic (stat_expr e)) o)

  | red_stat_expr_1 :
      forall (S0 : state (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (v : value (* input *)),
        (* ========================================== *)
        (* ------------------------------------------ *)
        (red_stat S0 C (stat_expr_1 ((specret_val S v) : (specret value))) (out_ter S ((resvalue_value v) : res)))

  | red_stat_if :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (e1 : expr (* input *)) (t2 : stat (* input *)) (t3opt : (option stat) (* input *)) (y1 : (specret value)) (o : out),
        (* ========================================== *)
        (red_spec S C (spec_expr_get_value_conv spec_to_boolean e1) y1) ->
        (red_stat S C (stat_if_1 y1 t2 t3opt) o) ->
        (* ------------------------------------------ *)
        (red_stat S C (stat_basic (stat_if e1 t2 t3opt)) o)

  | red_stat_if_1_true :
      forall (S0 : state (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (t2 : stat (* input *)) (t3opt : (option stat) (* input *)) (o : out),
        (* ========================================== *)
        (red_stat S C (stat_basic t2) o) ->
        (* ------------------------------------------ *)
        (red_stat S0 C (stat_if_1 ((specret_val S (value_prim (prim_bool ((true : provide_this_flag) : bool)))) : (specret value)) t2 t3opt) o)

  | red_stat_if_1_false :
      forall (S0 : state (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (t2 : stat (* input *)) (t3 : stat (* input *)) (o : out),
        (* ========================================== *)
        (red_stat S C (stat_basic t3) o) ->
        (* ------------------------------------------ *)
        (red_stat S0 C (stat_if_1 ((specret_val S (value_prim (prim_bool ((false : provide_this_flag) : bool)))) : (specret value)) t2 ((Some t3) : (option stat))) o)

  | red_stat_if_1_false_implicit :
      forall (S0 : state (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (t2 : stat (* input *)),
        (* ========================================== *)
        (* ------------------------------------------ *)
        (red_stat S0 C (stat_if_1 ((specret_val S (value_prim (prim_bool ((false : provide_this_flag) : bool)))) : (specret value)) t2 (None : (option stat))) (out_ter S (resvalue_empty : res)))

  | red_stat_do_while :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (labs : label_set (* input *)) (t1 : stat (* input *)) (e2 : expr (* input *)) (o : out),
        (* ========================================== *)
        (red_stat S C (stat_do_while_1 labs t1 e2 resvalue_empty) o) ->
        (* ------------------------------------------ *)
        (red_stat S C (stat_basic (stat_do_while labs t1 e2)) o)

  | red_stat_do_while_1 :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (labs : label_set (* input *)) (t1 : stat (* input *)) (e2 : expr (* input *)) (rv : resvalue (* input *)) (o1 : out) (o : out),
        (* ========================================== *)
        (red_stat S C (stat_basic t1) o1) ->
        (red_stat S C (stat_do_while_2 labs t1 e2 rv o1) o) ->
        (* ------------------------------------------ *)
        (red_stat S C (stat_do_while_1 labs t1 e2 rv) o)

  | red_stat_do_while_2 :
      forall (S0 : state (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (labs : label_set (* input *)) (t1 : stat (* input *)) (e2 : expr (* input *)) (rv_old : resvalue (* input *)) (R : res (* input *)) (o : out),
        (* ========================================== *)
        (red_stat S C (stat_do_while_3 labs t1 e2 (ifb ((res_value R) = resvalue_empty) then rv_old else (res_value R)) R) o) ->
        (* ------------------------------------------ *)
        (red_stat S0 C (stat_do_while_2 labs t1 e2 rv_old (out_ter S R)) o)

  | red_stat_do_while_3_continue :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (labs : label_set (* input *)) (t1 : stat (* input *)) (e2 : expr (* input *)) (rv : resvalue (* input *)) (R : res (* input *)) (o : out),
        (((res_type R) = restype_continue) /\ ((res_label_in R labs) : Prop)) ->
        (* ========================================== *)
        (red_stat S C (stat_do_while_6 labs t1 e2 rv) o) ->
        (* ------------------------------------------ *)
        (red_stat S C (stat_do_while_3 labs t1 e2 rv R) o)

  | red_stat_do_while_3_not_continue :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (labs : label_set (* input *)) (t1 : stat (* input *)) (e2 : expr (* input *)) (rv : resvalue (* input *)) (R : res (* input *)) (o : out),
        (((res_type R) = restype_continue) /\ ((res_label_in R labs) : Prop)) ->
        (* ========================================== *)
        (red_stat S C (stat_do_while_4 labs t1 e2 rv R) o) ->
        (* ------------------------------------------ *)
        (red_stat S C (stat_do_while_3 labs t1 e2 rv R) o)

  | red_stat_do_while_4_break :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (labs : label_set (* input *)) (t1 : stat (* input *)) (e2 : expr (* input *)) (rv : resvalue (* input *)) (R : res (* input *)),
        (((res_type R) = restype_break) /\ ((res_label_in R labs) : Prop)) ->
        (* ========================================== *)
        (* ------------------------------------------ *)
        (red_stat S C (stat_do_while_4 labs t1 e2 rv R) (out_ter S (rv : res)))

  | red_stat_do_while_4_not_break :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (labs : label_set (* input *)) (t1 : stat (* input *)) (e2 : expr (* input *)) (rv : resvalue (* input *)) (R : res (* input *)) (o : out),
        (((res_type R) = restype_break) /\ ((res_label_in R labs) : Prop)) ->
        (* ========================================== *)
        (red_stat S C (stat_do_while_5 labs t1 e2 rv R) o) ->
        (* ------------------------------------------ *)
        (red_stat S C (stat_do_while_4 labs t1 e2 rv R) o)

  | red_stat_do_while_5_abort :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (labs : label_set (* input *)) (t1 : stat (* input *)) (e2 : expr (* input *)) (rv : resvalue (* input *)) (R : res (* input *)),
        ((res_type R) <> restype_normal) ->
        (* ========================================== *)
        (* ------------------------------------------ *)
        (red_stat S C (stat_do_while_5 labs t1 e2 rv R) (out_ter S R))

  | red_stat_do_while_5_normal :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (labs : label_set (* input *)) (t1 : stat (* input *)) (e2 : expr (* input *)) (rv : resvalue (* input *)) (R : res (* input *)) (o : out),
        ((res_type R) = restype_normal) ->
        (* ========================================== *)
        (red_stat S C (stat_do_while_6 labs t1 e2 rv) o) ->
        (* ------------------------------------------ *)
        (red_stat S C (stat_do_while_5 labs t1 e2 rv R) o)

  | red_stat_do_while_6 :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (labs : label_set (* input *)) (t1 : stat (* input *)) (e2 : expr (* input *)) (rv : resvalue (* input *)) (y1 : (specret value)) (o : out),
        (* ========================================== *)
        (red_spec S C (spec_expr_get_value_conv spec_to_boolean e2) y1) ->
        (red_stat S C (stat_do_while_7 labs t1 e2 rv y1) o) ->
        (* ------------------------------------------ *)
        (red_stat S C (stat_do_while_6 labs t1 e2 rv) o)

  | red_stat_do_while_7_false :
      forall (S0 : state (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (labs : label_set (* input *)) (t1 : stat (* input *)) (e2 : expr (* input *)) (rv : resvalue (* input *)),
        (* ========================================== *)
        (* ------------------------------------------ *)
        (red_stat S0 C (stat_do_while_7 labs t1 e2 rv ((specret_val S (value_prim (prim_bool ((false : provide_this_flag) : bool)))) : (specret value))) (out_ter S (rv : res)))

  | red_stat_do_while_7_true :
      forall (S0 : state (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (labs : label_set (* input *)) (t1 : stat (* input *)) (e2 : expr (* input *)) (rv : resvalue (* input *)) (o : out),
        (* ========================================== *)
        (red_stat S C (stat_do_while_1 labs t1 e2 rv) o) ->
        (* ------------------------------------------ *)
        (red_stat S0 C (stat_do_while_7 labs t1 e2 rv ((specret_val S (value_prim (prim_bool ((true : provide_this_flag) : bool)))) : (specret value))) o)

  | red_stat_while :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (labs : label_set (* input *)) (e1 : expr (* input *)) (t2 : stat (* input *)) (o : out),
        (* ========================================== *)
        (red_stat S C (stat_while_1 labs e1 t2 resvalue_empty) o) ->
        (* ------------------------------------------ *)
        (red_stat S C (stat_basic (stat_while labs e1 t2)) o)

  | red_stat_while_1 :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (labs : label_set (* input *)) (e1 : expr (* input *)) (t2 : stat (* input *)) (rv : resvalue (* input *)) (y1 : (specret value)) (o : out),
        (* ========================================== *)
        (red_spec S C (spec_expr_get_value_conv spec_to_boolean e1) y1) ->
        (red_stat S C (stat_while_2 labs e1 t2 rv y1) o) ->
        (* ------------------------------------------ *)
        (red_stat S C (stat_while_1 labs e1 t2 rv) o)

  | red_stat_while_2_false :
      forall (S0 : state (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (labs : label_set (* input *)) (e1 : expr (* input *)) (t2 : stat (* input *)) (rv : resvalue (* input *)),
        (* ========================================== *)
        (* ------------------------------------------ *)
        (red_stat S0 C (stat_while_2 labs e1 t2 rv ((specret_val S (value_prim (prim_bool ((false : provide_this_flag) : bool)))) : (specret value))) (out_ter S (rv : res)))

  | red_stat_while_2_true :
      forall (S0 : state (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (labs : label_set (* input *)) (e1 : expr (* input *)) (t2 : stat (* input *)) (rv : resvalue (* input *)) (o1 : out) (o : out),
        (* ========================================== *)
        (red_stat S C (stat_basic t2) o1) ->
        (red_stat S C (stat_while_3 labs e1 t2 rv o1) o) ->
        (* ------------------------------------------ *)
        (red_stat S0 C (stat_while_2 labs e1 t2 rv ((specret_val S (value_prim (prim_bool ((true : provide_this_flag) : bool)))) : (specret value))) o)

  | red_stat_while_3 :
      forall (rv : resvalue (* input *)) (S0 : state (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (labs : label_set (* input *)) (e1 : expr (* input *)) (t2 : stat (* input *)) (R : res (* input *)) (o : out),
        (* ========================================== *)
        (red_stat S C (stat_while_4 labs e1 t2 (ifb ((res_value R) <> resvalue_empty) then (res_value R) else rv) R) o) ->
        (* ------------------------------------------ *)
        (red_stat S0 C (stat_while_3 labs e1 t2 rv (out_ter S R)) o)

  | red_stat_while_4_continue :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (labs : label_set (* input *)) (e1 : expr (* input *)) (t2 : stat (* input *)) (rv : resvalue (* input *)) (R : res (* input *)) (o : out),
        (((res_type R) = restype_continue) /\ ((res_label_in R labs) : Prop)) ->
        (* ========================================== *)
        (red_stat S C (stat_while_1 labs e1 t2 rv) o) ->
        (* ------------------------------------------ *)
        (red_stat S C (stat_while_4 labs e1 t2 rv R) o)

  | red_stat_while_4_not_continue :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (labs : label_set (* input *)) (e1 : expr (* input *)) (t2 : stat (* input *)) (rv : resvalue (* input *)) (R : res (* input *)) (o : out),
        (((res_type R) = restype_continue) /\ ((res_label_in R labs) : Prop)) ->
        (* ========================================== *)
        (red_stat S C (stat_while_5 labs e1 t2 rv R) o) ->
        (* ------------------------------------------ *)
        (red_stat S C (stat_while_4 labs e1 t2 rv R) o)

  | red_stat_while_5_break :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (labs : label_set (* input *)) (e1 : expr (* input *)) (t2 : stat (* input *)) (rv : resvalue (* input *)) (R : res (* input *)),
        (((res_type R) = restype_break) /\ ((res_label_in R labs) : Prop)) ->
        (* ========================================== *)
        (* ------------------------------------------ *)
        (red_stat S C (stat_while_5 labs e1 t2 rv R) (out_ter S (rv : res)))

  | red_stat_while_5_not_break :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (labs : label_set (* input *)) (e1 : expr (* input *)) (t2 : stat (* input *)) (rv : resvalue (* input *)) (R : res (* input *)) (o : out),
        (((res_type R) = restype_break) /\ ((res_label_in R labs) : Prop)) ->
        (* ========================================== *)
        (red_stat S C (stat_while_6 labs e1 t2 rv R) o) ->
        (* ------------------------------------------ *)
        (red_stat S C (stat_while_5 labs e1 t2 rv R) o)

  | red_stat_while_6_abort :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (labs : label_set (* input *)) (e1 : expr (* input *)) (t2 : stat (* input *)) (rv : resvalue (* input *)) (R : res (* input *)),
        ((res_type R) <> restype_normal) ->
        (* ========================================== *)
        (* ------------------------------------------ *)
        (red_stat S C (stat_while_6 labs e1 t2 rv R) (out_ter S R))

  | red_stat_while_6_normal :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (labs : label_set (* input *)) (e1 : expr (* input *)) (t2 : stat (* input *)) (rv : resvalue (* input *)) (R : res (* input *)) (o : out),
        ((res_type R) = restype_normal) ->
        (* ========================================== *)
        (red_stat S C (stat_while_1 labs e1 t2 rv) o) ->
        (* ------------------------------------------ *)
        (red_stat S C (stat_while_6 labs e1 t2 rv R) o)

  | red_stat_for_none :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (labs : label_set (* input *)) (eo2 : (option expr) (* input *)) (eo3 : (option expr) (* input *)) (t : stat (* input *)) (o : out),
        (* ========================================== *)
        (red_stat S C (stat_for_2 labs resvalue_empty eo2 eo3 t) o) ->
        (* ------------------------------------------ *)
        (red_stat S C (stat_basic (stat_for labs (None : (option expr)) eo2 eo3 t)) o)

  | red_stat_for_some :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (labs : label_set (* input *)) (e1 : expr (* input *)) (eo2 : (option expr) (* input *)) (eo3 : (option expr) (* input *)) (t : stat (* input *)) (o : out) (y1 : (specret value)),
        (* ========================================== *)
        (red_spec S C (spec_expr_get_value e1) y1) ->
        (red_stat S C (stat_for_1 labs y1 eo2 eo3 t) o) ->
        (* ------------------------------------------ *)
        (red_stat S C (stat_basic (stat_for labs ((Some e1) : (option expr)) eo2 eo3 t)) o)

  | red_stat_for_1 :
      forall (S0 : state (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (labs : label_set (* input *)) (v : value (* input *)) (eo2 : (option expr) (* input *)) (eo3 : (option expr) (* input *)) (t : stat (* input *)) (o : out),
        (* ========================================== *)
        (red_stat S C (stat_for_2 labs resvalue_empty eo2 eo3 t) o) ->
        (* ------------------------------------------ *)
        (red_stat S0 C (stat_for_1 labs ((specret_val S v) : (specret value)) eo2 eo3 t) o)

  | red_stat_for_2_none :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (labs : label_set (* input *)) (rv : resvalue (* input *)) (eo3 : (option expr) (* input *)) (t : stat (* input *)) (o : out),
        (* ========================================== *)
        (red_stat S C (stat_for_4 labs rv (None : (option expr)) eo3 t) o) ->
        (* ------------------------------------------ *)
        (red_stat S C (stat_for_2 labs rv (None : (option expr)) eo3 t) o)

  | red_stat_for_2_some :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (labs : label_set (* input *)) (rv : resvalue (* input *)) (e2 : expr (* input *)) (eo3 : (option expr) (* input *)) (t : stat (* input *)) (o : out) (y1 : (specret value)),
        (* ========================================== *)
        (red_spec S C (spec_expr_get_value_conv spec_to_boolean e2) y1) ->
        (red_stat S C (stat_for_3 labs rv e2 y1 eo3 t) o) ->
        (* ------------------------------------------ *)
        (red_stat S C (stat_for_2 labs rv ((Some e2) : (option expr)) eo3 t) o)

  | red_stat_for_3_false :
      forall (S0 : state (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (labs : label_set (* input *)) (rv : resvalue (* input *)) (e2 : expr (* input *)) (eo3 : (option expr) (* input *)) (t : stat (* input *)),
        (* ========================================== *)
        (* ------------------------------------------ *)
        (red_stat S0 C (stat_for_3 labs rv e2 ((specret_val S (value_prim (prim_bool ((false : provide_this_flag) : bool)))) : (specret value)) eo3 t) (out_ter S (rv : res)))

  | red_stat_for_3_not_false :
      forall (S0 : state (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (labs : label_set (* input *)) (rv : resvalue (* input *)) (e2 : expr (* input *)) (v : value (* input *)) (eo3 : (option expr) (* input *)) (t : stat (* input *)) (o : out),
        (v <> (value_prim (prim_bool ((false : provide_this_flag) : bool)))) ->
        (* ========================================== *)
        (red_stat S C (stat_for_4 labs rv ((Some e2) : (option expr)) eo3 t) o) ->
        (* ------------------------------------------ *)
        (red_stat S0 C (stat_for_3 labs rv e2 ((specret_val S v) : (specret value)) eo3 t) o)

  | red_stat_for_4 :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (labs : label_set (* input *)) (rv : resvalue (* input *)) (eo2 : (option expr) (* input *)) (eo3 : (option expr) (* input *)) (t : stat (* input *)) (o : out) (o1 : out),
        (* ========================================== *)
        (red_stat S C (stat_basic t) o1) ->
        (red_stat S C (stat_for_5 labs rv eo2 o1 eo3 t) o) ->
        (* ------------------------------------------ *)
        (red_stat S C (stat_for_4 labs rv eo2 eo3 t) o)

  | red_stat_for_5 :
      forall (S0 : state (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (labs : label_set (* input *)) (rv : resvalue (* input *)) (R : res (* input *)) (eo2 : (option expr) (* input *)) (eo3 : (option expr) (* input *)) (t : stat (* input *)) (o : out),
        (* ========================================== *)
        (red_stat S C (stat_for_6 labs (ifb ((res_value R) <> resvalue_empty) then (res_value R) else rv) eo2 eo3 t R) o) ->
        (* ------------------------------------------ *)
        (red_stat S0 C (stat_for_5 labs rv eo2 (out_ter S R) eo3 t) o)

  | red_stat_for_6_break :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (labs : label_set (* input *)) (rv : resvalue (* input *)) (R : res (* input *)) (eo2 : (option expr) (* input *)) (eo3 : (option expr) (* input *)) (t : stat (* input *)),
        (((res_type R) = restype_break) /\ ((res_label_in R labs) : Prop)) ->
        (* ========================================== *)
        (* ------------------------------------------ *)
        (red_stat S C (stat_for_6 labs rv eo2 eo3 t R) (out_ter S (rv : res)))

  | red_stat_for_6_not_break :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (labs : label_set (* input *)) (rv : resvalue (* input *)) (R : res (* input *)) (eo2 : (option expr) (* input *)) (eo3 : (option expr) (* input *)) (t : stat (* input *)) (o : out),
        (((res_type R) <> restype_break) \/ (~ (res_label_in R labs))) ->
        (* ========================================== *)
        (red_stat S C (stat_for_7 labs rv eo2 eo3 t R) o) ->
        (* ------------------------------------------ *)
        (red_stat S C (stat_for_6 labs rv eo2 eo3 t R) o)

  | red_stat_for_7_abort :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (labs : label_set (* input *)) (rv : resvalue (* input *)) (R : res (* input *)) (eo2 : (option expr) (* input *)) (eo3 : (option expr) (* input *)) (t : stat (* input *)),
        ((res_type R) <> restype_normal) ->
        (((res_type R) <> restype_continue) \/ (~ (res_label_in R labs))) ->
        (* ========================================== *)
        (* ------------------------------------------ *)
        (red_stat S C (stat_for_7 labs rv eo2 eo3 t R) (out_ter S R))

  | red_stat_for_7_continue :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (labs : label_set (* input *)) (rv : resvalue (* input *)) (R : res (* input *)) (eo2 : (option expr) (* input *)) (eo3 : (option expr) (* input *)) (t : stat (* input *)) (o : out),
        (((res_type R) = restype_normal) \/ (((res_type R) = restype_continue) /\ (res_label_in R labs))) ->
        (* ========================================== *)
        (red_stat S C (stat_for_8 labs rv eo2 eo3 t) o) ->
        (* ------------------------------------------ *)
        (red_stat S C (stat_for_7 labs rv eo2 eo3 t R) o)

  | red_stat_for_8_none :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (labs : label_set (* input *)) (rv : resvalue (* input *)) (eo2 : (option expr) (* input *)) (t : stat (* input *)) (o : out),
        (* ========================================== *)
        (red_stat S C (stat_for_2 labs rv eo2 (None : (option expr)) t) o) ->
        (* ------------------------------------------ *)
        (red_stat S C (stat_for_8 labs rv eo2 (None : (option expr)) t) o)

  | red_stat_for_8_some :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (labs : label_set (* input *)) (rv : resvalue (* input *)) (eo2 : (option expr) (* input *)) (e3 : expr (* input *)) (t : stat (* input *)) (o : out) (y1 : (specret value)),
        (* ========================================== *)
        (red_spec S C (spec_expr_get_value e3) y1) ->
        (red_stat S C (stat_for_9 labs rv eo2 e3 y1 t) o) ->
        (* ------------------------------------------ *)
        (red_stat S C (stat_for_8 labs rv eo2 ((Some e3) : (option expr)) t) o)

  | red_stat_for_9 :
      forall (S0 : state (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (labs : label_set (* input *)) (rv : resvalue (* input *)) (v : value (* input *)) (eo2 : (option expr) (* input *)) (e3 : expr (* input *)) (t : stat (* input *)) (o : out),
        (* ========================================== *)
        (red_stat S C (stat_for_2 labs rv eo2 ((Some e3) : (option expr)) t) o) ->
        (* ------------------------------------------ *)
        (red_stat S0 C (stat_for_9 labs rv eo2 e3 ((specret_val S v) : (specret value)) t) o)

  | red_stat_for_var :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (labs : label_set (* input *)) (ds : (list (string * (option expr))) (* input *)) (eo2 : (option expr) (* input *)) (eo3 : (option expr) (* input *)) (t : stat (* input *)) (o : out) (o1 : out),
        (* ========================================== *)
        (red_stat S C (stat_basic (stat_var_decl ds)) o1) ->
        (red_stat S C (stat_for_var_1 o1 labs eo2 eo3 t) o) ->
        (* ------------------------------------------ *)
        (red_stat S C (stat_basic (stat_for_var labs ds eo2 eo3 t)) o)

  | red_stat_for_var_1 :
      forall (S0 : state (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (R : res (* input *)) (labs : label_set (* input *)) (eo2 : (option expr) (* input *)) (eo3 : (option expr) (* input *)) (t : stat (* input *)) (o : out),
        (* ========================================== *)
        (red_stat S C (stat_for_2 labs resvalue_empty eo2 eo3 t) o) ->
        (* ------------------------------------------ *)
        (red_stat S0 C (stat_for_var_1 (out_ter S R) labs eo2 eo3 t) o)

  | red_stat_continue :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (lab : label (* input *)),
        (* ========================================== *)
        (* ------------------------------------------ *)
        (red_stat S C (stat_basic (stat_continue lab)) (out_ter S (res_continue lab)))

  | red_stat_break :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (lab : label (* input *)),
        (* ========================================== *)
        (* ------------------------------------------ *)
        (red_stat S C (stat_basic (stat_break lab)) (out_ter S (res_break lab)))

  | red_stat_return_none :
      forall (S : state (* input *)) (C : execution_ctx (* input *)),
        (* ========================================== *)
        (* ------------------------------------------ *)
        (red_stat S C (stat_basic (stat_return (None : (option expr)))) (out_ter S (res_return (resvalue_value undef))))

  | red_stat_return_some :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (e : expr (* input *)) (o : out) (y1 : (specret value)),
        (* ========================================== *)
        (red_spec S C (spec_expr_get_value e) y1) ->
        (red_stat S C (stat_return_1 y1) o) ->
        (* ------------------------------------------ *)
        (red_stat S C (stat_basic (stat_return ((Some e) : (option expr)))) o)

  | red_stat_return_1 :
      forall (S0 : state (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (v : value (* input *)),
        (* ========================================== *)
        (* ------------------------------------------ *)
        (red_stat S0 C (stat_return_1 ((specret_val S v) : (specret value))) (out_ter S (res_return (resvalue_value v))))

  | red_stat_with :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (e1 : expr (* input *)) (t2 : stat (* input *)) (y1 : (specret value)) (o : out),
        (* ========================================== *)
        (red_spec S C (spec_expr_get_value_conv spec_to_object e1) y1) ->
        (red_stat S C (stat_with_1 t2 y1) o) ->
        (* ------------------------------------------ *)
        (red_stat S C (stat_basic (stat_with e1 t2)) o)

  | red_stat_with_1 :
      forall (S0 : state (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (t2 : stat (* input *)) (l : object_loc (* input *)) (o : out) (lex : lexical_env),
        (lex = (execution_ctx_lexical_env C)) ->
        (* ========================================== *)
        (red_stat ((snd (lexical_env_alloc_object S lex l provide_this_true)) : state) (execution_ctx_with_lex C ((fst (lexical_env_alloc_object S lex l provide_this_true)) : lexical_env)) (stat_basic t2) o) ->
        (* ------------------------------------------ *)
        (red_stat S0 C (stat_with_1 t2 ((specret_val S (value_object l)) : (specret value))) o)

  | red_stat_switch :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (e : expr (* input *)) (o : out) (sb : switchbody (* input *)) (labs : label_set (* input *)) (y1 : (specret value)),
        (* ========================================== *)
        (red_spec S C (spec_expr_get_value e) y1) ->
        (red_stat S C (stat_switch_1 y1 labs sb) o) ->
        (* ------------------------------------------ *)
        (red_stat S C (stat_basic (stat_switch labs e sb)) o)

  | red_stat_switch_1_nodefault :
      forall (S : state (* input *)) (S0 : state (* input *)) (C : execution_ctx (* input *)) (vi : value (* input *)) (o : out) (o1 : out) (scs : (list switchclause) (* input *)) (labs : label_set (* input *)),
        (* ========================================== *)
        (red_stat S C (stat_switch_nodefault_1 vi resvalue_empty scs) o1) ->
        (red_stat S C (stat_switch_2 o1 labs) o) ->
        (* ------------------------------------------ *)
        (red_stat S0 C (stat_switch_1 ((specret_val S vi) : (specret value)) labs (switchbody_nodefault scs)) o)

  | red_stat_switch_1_default :
      forall (S : state (* input *)) (S0 : state (* input *)) (C : execution_ctx (* input *)) (o : out) (o1 : out) (vi : value (* input *)) (scs1 : (list switchclause) (* input *)) (scs2 : (list switchclause) (* input *)) (ts1 : (list stat) (* input *)) (labs : label_set (* input *)),
        (* ========================================== *)
        (red_stat S C (stat_switch_default_A_1 false vi resvalue_empty scs1 ts1 scs2) o1) ->
        (red_stat S C (stat_switch_2 o1 labs) o) ->
        (* ------------------------------------------ *)
        (red_stat S0 C (stat_switch_1 ((specret_val S vi) : (specret value)) labs (switchbody_withdefault scs1 ts1 scs2)) o)

  | red_stat_switch_2_break :
      forall (S : state (* input *)) (S0 : state (* input *)) (C : execution_ctx (* input *)) (rv : resvalue) (lab : label) (labs : label_set (* input *)),
        (res_label_in (res_intro restype_break rv lab) labs) ->
        (* ========================================== *)
        (* ------------------------------------------ *)
        (red_stat S0 C (stat_switch_2 (out_ter S (res_intro restype_break rv lab)) labs) (out_ter S (res_normal rv)))

  | red_stat_switch_2_normal :
      forall (S0 : state (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (rv : resvalue (* input *)) (labs : label_set (* input *)),
        (* ========================================== *)
        (* ------------------------------------------ *)
        (red_stat S0 C (stat_switch_2 (out_ter S (rv : res)) labs) (out_ter S (rv : res)))

  | red_stat_switch_nodefault_1_nil :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (vi : value (* input *)) (rv : resvalue (* input *)) (o : out),
        (* ========================================== *)
        (red_stat S C (stat_switch_nodefault_5 rv (nil : (list switchclause))) o) ->
        (* ------------------------------------------ *)
        (red_stat S C (stat_switch_nodefault_1 vi rv (nil : (list switchclause))) o)

  | red_stat_switch_nodefault_1_cons :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (e : expr (* input *)) (vi : value (* input *)) (rv : resvalue (* input *)) (ts : (list stat) (* input *)) (scs : (list switchclause) (* input *)) (o : out) (y1 : (specret value)),
        (* ========================================== *)
        (red_spec S C (spec_expr_get_value e) y1) ->
        (red_stat S C (stat_switch_nodefault_2 y1 vi rv ts scs) o) ->
        (* ------------------------------------------ *)
        (red_stat S C (stat_switch_nodefault_1 vi rv ((switchclause_intro e ts) :: scs)) o)

  | red_stat_switch_nodefault_2 :
      forall (S0 : state (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (vi : value (* input *)) (v1 : value (* input *)) (rv : resvalue (* input *)) (ts : (list stat) (* input *)) (scs : (list switchclause) (* input *)) (o : out),
        (* ========================================== *)
        (red_stat S C (stat_switch_nodefault_3 (strict_equality_test v1 vi) vi rv ts scs) o) ->
        (* ------------------------------------------ *)
        (red_stat S0 C (stat_switch_nodefault_2 ((specret_val S v1) : (specret value)) vi rv ts scs) o)

  | red_stat_switch_nodefault_3_false :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (vi : value (* input *)) (rv : resvalue (* input *)) (scs : (list switchclause) (* input *)) (ts : (list stat) (* input *)) (o : out),
        (* ========================================== *)
        (red_stat S C (stat_switch_nodefault_1 vi rv scs) o) ->
        (* ------------------------------------------ *)
        (red_stat S C (stat_switch_nodefault_3 false vi rv ts scs) o)

  | red_stat_switch_nodefault_3_true :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (ts : (list stat) (* input *)) (o : out) (o1 : out) (scs : (list switchclause) (* input *)) (vi : value (* input *)) (rv : resvalue (* input *)),
        (* ========================================== *)
        (red_stat S C (stat_basic (stat_block ts)) o1) ->
        (red_stat S C (stat_switch_nodefault_4 o1 scs) o) ->
        (* ------------------------------------------ *)
        (red_stat S C (stat_switch_nodefault_3 true vi rv ts scs) o)

  | red_stat_switch_nodefault_4 :
      forall (S0 : state (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (rv : resvalue (* input *)) (scs : (list switchclause) (* input *)) (o : out),
        (* ========================================== *)
        (red_stat S C (stat_switch_nodefault_5 rv scs) o) ->
        (* ------------------------------------------ *)
        (red_stat S0 C (stat_switch_nodefault_4 (out_ter S (rv : res)) scs) o)

  | red_stat_switch_nodefault_5_nil :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (rv : resvalue (* input *)),
        (* ========================================== *)
        (* ------------------------------------------ *)
        (red_stat S C (stat_switch_nodefault_5 rv (nil : (list switchclause))) (out_ter S (rv : res)))

  | red_stat_switch_nodefault_5_cons :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (ts : (list stat) (* input *)) (o : out) (o1 : out) (scs : (list switchclause) (* input *)) (rv : resvalue (* input *)) (e : expr (* input *)),
        (* ========================================== *)
        (red_stat S C (stat_basic (stat_block ts)) o1) ->
        (red_stat S C (stat_switch_nodefault_6 rv o1 scs) o) ->
        (* ------------------------------------------ *)
        (red_stat S C (stat_switch_nodefault_5 rv ((switchclause_intro e ts) :: scs)) o)

  | red_stat_switch_nodefault_6_normal :
      forall (S0 : state (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (R : res (* input *)) (rv : resvalue (* input *)) (scs : (list switchclause) (* input *)) (o : out),
        (* ========================================== *)
        (red_stat S C (stat_switch_nodefault_5 (ifb ((res_value R) <> resvalue_empty) then (res_value R) else rv) scs) o) ->
        (* ------------------------------------------ *)
        (red_stat S0 C (stat_switch_nodefault_6 rv (out_ter S R) scs) o)

  | red_stat_switch_nodefault_6_abrupt :
      forall (S : state (* input *)) (S0 : state (* input *)) (C : execution_ctx (* input *)) (R : res (* input *)) (scs : (list switchclause) (* input *)) (rv : resvalue (* input *)),
        (res_is_normal R) ->
        ((res_type R) <> restype_throw) ->
        (* ========================================== *)
        (* ------------------------------------------ *)
        (red_stat S0 C (stat_switch_nodefault_6 rv (out_ter S R) scs) (out_ter S (res_overwrite_value_if_empty rv R)))

  | red_stat_switch_default_A_1_nil_true :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (vi : value (* input *)) (rv : resvalue (* input *)) (ts1 : (list stat) (* input *)) (scs2 : (list switchclause) (* input *)) (o : out),
        (* ========================================== *)
        (red_stat S C (stat_switch_default_5 vi rv ts1 scs2) o) ->
        (* ------------------------------------------ *)
        (red_stat S C (stat_switch_default_A_1 true vi rv (nil : (list switchclause)) ts1 scs2) o)

  | red_stat_switch_default_A_1_nil_false :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (vi : value (* input *)) (rv : resvalue (* input *)) (ts1 : (list stat) (* input *)) (scs2 : (list switchclause) (* input *)) (o : out),
        (* ========================================== *)
        (red_stat S C (stat_switch_default_B_1 vi rv ts1 scs2) o) ->
        (* ------------------------------------------ *)
        (red_stat S C (stat_switch_default_A_1 false vi rv (nil : (list switchclause)) ts1 scs2) o)

  | red_stat_switch_default_A_1_cons_true :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (e : expr (* input *)) (o : out) (vi : value (* input *)) (rv : resvalue (* input *)) (ts : (list stat) (* input *)) (ts1 : (list stat) (* input *)) (scs : (list switchclause) (* input *)) (scs2 : (list switchclause) (* input *)),
        (* ========================================== *)
        (red_stat S C (stat_switch_default_A_4 rv vi ts scs ts1 scs2) o) ->
        (* ------------------------------------------ *)
        (red_stat S C (stat_switch_default_A_1 true vi rv ((switchclause_intro e ts) :: scs) ts1 scs2) o)

  | red_stat_switch_default_A_1_cons_false :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (e : expr (* input *)) (vi : value (* input *)) (rv : resvalue (* input *)) (ts : (list stat) (* input *)) (ts1 : (list stat) (* input *)) (scs : (list switchclause) (* input *)) (scs2 : (list switchclause) (* input *)) (y1 : (specret value)) (o : out),
        (* ========================================== *)
        (red_spec S C (spec_expr_get_value e) y1) ->
        (red_stat S C (stat_switch_default_A_2 y1 vi rv ts scs ts1 scs2) o) ->
        (* ------------------------------------------ *)
        (red_stat S C (stat_switch_default_A_1 false vi rv ((switchclause_intro e ts) :: scs) ts1 scs2) o)

  | red_stat_switch_default_A_2 :
      forall (S0 : state (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (vi : value (* input *)) (v1 : value (* input *)) (rv : resvalue (* input *)) (ts : (list stat) (* input *)) (scs : (list switchclause) (* input *)) (ts1 : (list stat) (* input *)) (scs2 : (list switchclause) (* input *)) (o : out),
        (* ========================================== *)
        (red_stat S C (stat_switch_default_A_3 (strict_equality_test v1 vi) vi rv ts scs ts1 scs2) o) ->
        (* ------------------------------------------ *)
        (red_stat S0 C (stat_switch_default_A_2 ((specret_val S v1) : (specret value)) vi rv ts scs ts1 scs2) o)

  | red_stat_switch_default_A_3_false :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (vi : value (* input *)) (rv : resvalue (* input *)) (scs : (list switchclause) (* input *)) (ts : (list stat) (* input *)) (ts1 : (list stat) (* input *)) (scs2 : (list switchclause) (* input *)) (o : out),
        (* ========================================== *)
        (red_stat S C (stat_switch_default_A_1 false vi rv scs ts1 scs2) o) ->
        (* ------------------------------------------ *)
        (red_stat S C (stat_switch_default_A_3 false vi rv ts scs ts1 scs2) o)

  | red_stat_switch_default_A_3_true :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (vi : value (* input *)) (rv : resvalue (* input *)) (scs : (list switchclause) (* input *)) (ts : (list stat) (* input *)) (ts1 : (list stat) (* input *)) (scs2 : (list switchclause) (* input *)) (o : out),
        (* ========================================== *)
        (red_stat S C (stat_switch_default_A_4 rv vi ts scs ts1 scs2) o) ->
        (* ------------------------------------------ *)
        (red_stat S C (stat_switch_default_A_3 true vi rv ts scs ts1 scs2) o)

  | red_stat_switch_default_A_4 :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (o1 : out) (rv : resvalue (* input *)) (ts : (list stat) (* input *)) (scs : (list switchclause) (* input *)) (ts1 : (list stat) (* input *)) (scs2 : (list switchclause) (* input *)) (o : out) (vi : value (* input *)),
        (* ========================================== *)
        (red_stat S C (stat_basic (stat_block ts)) o1) ->
        (red_stat S C (stat_switch_default_A_5 rv o1 vi scs ts1 scs2) o) ->
        (* ------------------------------------------ *)
        (red_stat S C (stat_switch_default_A_4 rv vi ts scs ts1 scs2) o)

  | red_stat_switch_default_A_5 :
      forall (S : state (* input *)) (S0 : state (* input *)) (C : execution_ctx (* input *)) (vi : value (* input *)) (rv0 : resvalue (* input *)) (rv : resvalue (* input *)) (scs : (list switchclause) (* input *)) (scs2 : (list switchclause) (* input *)) (ts1 : (list stat) (* input *)) (o : out),
        (* ========================================== *)
        (red_stat S C (stat_switch_default_A_1 true vi (ifb (rv <> resvalue_empty) then rv else rv0) scs ts1 scs2) o) ->
        (* ------------------------------------------ *)
        (red_stat S0 C (stat_switch_default_A_5 rv0 (out_ter S (rv : res)) vi scs ts1 scs2) o)

  | red_stat_switch_default_A_5_abrupt :
      forall (S : state (* input *)) (S0 : state (* input *)) (C : execution_ctx (* input *)) (vi : value (* input *)) (rv : resvalue (* input *)) (R : res (* input *)) (scs : (list switchclause) (* input *)) (scs2 : (list switchclause) (* input *)) (ts1 : (list stat) (* input *)),
        (res_is_normal R) ->
        ((res_type R) <> restype_throw) ->
        (* ========================================== *)
        (* ------------------------------------------ *)
        (red_stat S0 C (stat_switch_default_A_5 rv (out_ter S R) vi scs ts1 scs2) (out_ter S (res_overwrite_value_if_empty rv R)))

  | red_stat_switch_default_B_1_nil :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (vi : value (* input *)) (rv : resvalue (* input *)) (ts1 : (list stat) (* input *)) (o : out),
        (* ========================================== *)
        (red_stat S C (stat_switch_default_5 vi rv ts1 (nil : (list switchclause))) o) ->
        (* ------------------------------------------ *)
        (red_stat S C (stat_switch_default_B_1 vi rv ts1 (nil : (list switchclause))) o)

  | red_stat_switch_default_B_1_cons :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (e : expr (* input *)) (o : out) (vi : value (* input *)) (rv : resvalue (* input *)) (ts : (list stat) (* input *)) (ts1 : (list stat) (* input *)) (scs : (list switchclause) (* input *)) (y1 : (specret value)),
        (* ========================================== *)
        (red_spec S C (spec_expr_get_value e) y1) ->
        (red_stat S C (stat_switch_default_B_2 y1 vi rv ts ts1 scs) o) ->
        (* ------------------------------------------ *)
        (red_stat S C (stat_switch_default_B_1 vi rv ts1 ((switchclause_intro e ts) :: scs)) o)

  | red_stat_switch_default_B_2 :
      forall (S : state (* input *)) (S0 : state (* input *)) (C : execution_ctx (* input *)) (vi : value (* input *)) (v1 : value (* input *)) (rv : resvalue (* input *)) (ts : (list stat) (* input *)) (scs : (list switchclause) (* input *)) (ts1 : (list stat) (* input *)) (o : out),
        (* ========================================== *)
        (red_stat S C (stat_switch_default_B_3 (strict_equality_test v1 vi) vi rv ts ts1 scs) o) ->
        (* ------------------------------------------ *)
        (red_stat S0 C (stat_switch_default_B_2 ((specret_val S v1) : (specret value)) vi rv ts ts1 scs) o)

  | red_stat_switch_default_B_3_false :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (vi : value (* input *)) (rv : resvalue (* input *)) (scs : (list switchclause) (* input *)) (ts : (list stat) (* input *)) (ts1 : (list stat) (* input *)) (o : out),
        (* ========================================== *)
        (red_stat S C (stat_switch_default_B_1 vi rv ts1 scs) o) ->
        (* ------------------------------------------ *)
        (red_stat S C (stat_switch_default_B_3 false vi rv ts ts1 scs) o)

  | red_stat_switch_default_B_3_true :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (o1 : out) (rv : resvalue (* input *)) (ts : (list stat) (* input *)) (scs : (list switchclause) (* input *)) (ts1 : (list stat) (* input *)) (o : out) (vi : value (* input *)),
        (* ========================================== *)
        (red_stat S C (stat_basic (stat_block ts)) o1) ->
        (red_stat S C (stat_switch_default_B_4 o1 ts1 scs) o) ->
        (* ------------------------------------------ *)
        (red_stat S C (stat_switch_default_B_3 true vi rv ts ts1 scs) o)

  | red_stat_switch_default_B_4 :
      forall (S : state (* input *)) (S0 : state (* input *)) (C : execution_ctx (* input *)) (rv : resvalue (* input *)) (scs : (list switchclause) (* input *)) (ts1 : (list stat) (* input *)) (o : out),
        (* ========================================== *)
        (red_stat S C (stat_switch_default_7 rv scs) o) ->
        (* ------------------------------------------ *)
        (red_stat S0 C (stat_switch_default_B_4 (out_ter S (rv : res)) ts1 scs) o)

  | red_stat_switch_default_5 :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (o : out) (o1 : out) (ts : (list stat) (* input *)) (vi : value (* input *)) (rv : resvalue (* input *)) (scs : (list switchclause) (* input *)),
        (* ========================================== *)
        (red_stat S C (stat_basic (stat_block ts)) o1) ->
        (red_stat S C (stat_switch_default_6 o1 scs) o) ->
        (* ------------------------------------------ *)
        (red_stat S C (stat_switch_default_5 vi rv ts scs) o)

  | red_stat_switch_default_6 :
      forall (S : state (* input *)) (S0 : state (* input *)) (C : execution_ctx (* input *)) (o : out) (rv : resvalue (* input *)) (scs : (list switchclause) (* input *)),
        (* ========================================== *)
        (red_stat S C (stat_switch_default_7 rv scs) o) ->
        (* ------------------------------------------ *)
        (red_stat S0 C (stat_switch_default_6 (out_ter S (rv : res)) scs) o)

  | red_stat_switch_default_7_nil :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (rv : resvalue (* input *)),
        (* ========================================== *)
        (* ------------------------------------------ *)
        (red_stat S C (stat_switch_default_7 rv (nil : (list switchclause))) (out_ter S (rv : res)))

  | red_stat_switch_default_7_cons :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (ts : (list stat) (* input *)) (rv : resvalue (* input *)) (o : out) (o1 : out) (scs : (list switchclause) (* input *)) (e : expr (* input *)),
        (* ========================================== *)
        (red_stat S C (stat_basic (stat_block ts)) o1) ->
        (red_stat S C (stat_switch_default_8 rv o1 scs) o) ->
        (* ------------------------------------------ *)
        (red_stat S C (stat_switch_default_7 rv ((switchclause_intro e ts) :: scs)) o)

  | red_stat_switch_default_8_normal :
      forall (S : state (* input *)) (S0 : state (* input *)) (C : execution_ctx (* input *)) (rv0 : resvalue (* input *)) (rv : resvalue (* input *)) (scs : (list switchclause) (* input *)) (o : out),
        (* ========================================== *)
        (red_stat S C (stat_switch_default_7 (ifb (rv <> resvalue_empty) then rv else rv0) scs) o) ->
        (* ------------------------------------------ *)
        (red_stat S0 C (stat_switch_default_8 rv0 (out_ter S (rv : res)) scs) o)

  | red_stat_switch_default_8_abrupt :
      forall (S : state (* input *)) (S0 : state (* input *)) (C : execution_ctx (* input *)) (R : res (* input *)) (scs : (list switchclause) (* input *)) (rv : resvalue (* input *)),
        (res_is_normal R) ->
        ((res_type R) <> restype_throw) ->
        (* ========================================== *)
        (* ------------------------------------------ *)
        (red_stat S0 C (stat_switch_default_8 rv (out_ter S R) scs) (out_ter S (res_overwrite_value_if_empty rv R)))

  | red_stat_label :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (slab : string (* input *)) (t : stat (* input *)) (o1 : out) (o : out),
        (* ========================================== *)
        (red_stat S C (stat_basic t) o1) ->
        (red_stat S C (stat_label_1 (label_string slab) o1) o) ->
        (* ------------------------------------------ *)
        (red_stat S C (stat_basic (stat_label slab t)) o)

  | red_stat_label_1_normal :
      forall (S0 : state (* input *)) (S : state (* input *)) (lab : label (* input *)) (C : execution_ctx (* input *)) (R : res (* input *)),
        ((res_type R) = restype_normal) ->
        (* ========================================== *)
        (* ------------------------------------------ *)
        (red_stat S0 C (stat_label_1 lab (out_ter S R)) (out_ter S R))

  | red_stat_label_1_break_eq :
      forall (S0 : state (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (rv : resvalue) (lab : label (* input *)),
        (* ========================================== *)
        (* ------------------------------------------ *)
        (red_stat S0 C (stat_label_1 lab (out_ter S (res_intro restype_break rv lab))) (out_ter S (res_normal rv)))

  | red_stat_throw :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (e : expr (* input *)) (o : out) (y1 : (specret value)),
        (* ========================================== *)
        (red_spec S C (spec_expr_get_value e) y1) ->
        (red_stat S C (stat_throw_1 y1) o) ->
        (* ------------------------------------------ *)
        (red_stat S C (stat_basic (stat_throw e)) o)

  | red_stat_throw_1 :
      forall (S0 : state (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (v : value (* input *)),
        (* ========================================== *)
        (* ------------------------------------------ *)
        (red_stat S0 C (stat_throw_1 ((specret_val S v) : (specret value))) (out_ter S (res_throw (resvalue_value v))))

  | red_stat_try :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (t : stat (* input *)) (co : (option (string * stat)) (* input *)) (fo : (option stat) (* input *)) (o : out) (o1 : out),
        (* ========================================== *)
        (red_stat S C (stat_basic t) o1) ->
        (red_stat S C (stat_try_1 o1 co fo) o) ->
        (* ------------------------------------------ *)
        (red_stat S C (stat_basic (stat_try t co fo)) o)

  | red_stat_try_1_no_throw :
      forall (S0 : state (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (R : res (* input *)) (co : (option (string * stat)) (* input *)) (fo : (option stat) (* input *)) (o : out),
        ((res_type R) <> restype_throw) ->
        (* ========================================== *)
        (red_stat S C (stat_try_4 R fo) o) ->
        (* ------------------------------------------ *)
        (red_stat S0 C (stat_try_1 (out_ter S R) co fo) o)

  | red_stat_try_1_throw_no_catch :
      forall (S0 : state (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (R : res (* input *)) (fo : (option stat) (* input *)) (o : out),
        ((res_type R) = restype_throw) ->
        (* ========================================== *)
        (red_stat S C (stat_try_4 R fo) o) ->
        (* ------------------------------------------ *)
        (red_stat S0 C (stat_try_1 (out_ter S R) (None : (option (string * stat))) fo) o)

  | red_stat_try_1_throw_catch :
      forall (v : value) (S0 : state (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (lex : lexical_env) (oldlex : (list env_loc)) (L : env_loc) (x : prop_name (* input *)) (R : res (* input *)) (t1 : stat (* input *)) (fo : (option stat) (* input *)) (o1 : out) (o : out),
        ((res_type R) = restype_throw) ->
        (lex = (execution_ctx_lexical_env C)) ->
        (((fst (lexical_env_alloc_decl S lex)) : (list env_loc)) = (L :: oldlex)) ->
        ((res_value R) = (resvalue_value v)) ->
        (* ========================================== *)
        (red_expr ((snd (lexical_env_alloc_decl S lex)) : state) C (spec_env_record_create_set_mutable_binding L x (None : (option bool)) v (throw_irrelevant : bool)) o1) ->
        (red_stat ((snd (lexical_env_alloc_decl S lex)) : state) C (stat_try_2 o1 ((fst (lexical_env_alloc_decl S lex)) : lexical_env) t1 fo) o) ->
        (* ------------------------------------------ *)
        (red_stat S0 C (stat_try_1 (out_ter S R) ((Some (x, t1)) : (option (string * stat))) fo) o)

  | red_stat_try_2_catch :
      forall (C : execution_ctx (* input *)) (S0 : state (* input *)) (S : state (* input *)) (lex' : lexical_env (* input *)) (t1 : stat (* input *)) (fo : (option stat) (* input *)) (o : out) (o1 : out),
        (* ========================================== *)
        (red_stat S (execution_ctx_with_lex C lex') (stat_basic t1) o1) ->
        (red_stat S C (stat_try_3 o1 fo) o) ->
        (* ------------------------------------------ *)
        (red_stat S0 C (stat_try_2 (out_ter S (res_intro restype_normal resvalue_empty label_empty)) lex' t1 fo) o)

  | red_stat_try_3_catch_result :
      forall (S0 : state (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (R : res (* input *)) (fo : (option stat) (* input *)) (o : out),
        (* ========================================== *)
        (red_stat S C (stat_try_4 R fo) o) ->
        (* ------------------------------------------ *)
        (red_stat S0 C (stat_try_3 (out_ter S R) fo) o)

  | red_stat_try_4_no_finally :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (R : res (* input *)),
        (* ========================================== *)
        (* ------------------------------------------ *)
        (red_stat S C (stat_try_4 R (None : (option stat))) (out_ter S R))

  | red_stat_try_4_finally :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (R : res (* input *)) (t1 : stat (* input *)) (o : out) (o1 : out),
        (* ========================================== *)
        (red_stat S C (stat_basic t1) o1) ->
        (red_stat S C (stat_try_5 R o1) o) ->
        (* ------------------------------------------ *)
        (red_stat S C (stat_try_4 R ((Some t1) : (option stat))) o)

  | red_stat_try_5_finally_result :
      forall (S0 : state (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (R : res (* input *)) (rv : resvalue (* input *)),
        (* ========================================== *)
        (* ------------------------------------------ *)
        (red_stat S0 C (stat_try_5 R (out_ter S (rv : res))) (out_ter S R))

  | red_stat_debugger :
      forall (S : state (* input *)) (C : execution_ctx (* input *)),
        (* ========================================== *)
        (* ------------------------------------------ *)
        (red_stat S C (stat_basic stat_debugger) (out_ter S res_empty))


with red_expr : state (* input *) -> execution_ctx (* input *) -> ext_expr (* input *) -> out -> Prop :=

  | red_expr_abort :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (exte : ext_expr (* input *)) (o : out),
        ((out_of_ext_expr exte) = ((Some o) : (option out))) ->
        (abort o) ->
        (abort_intercepted_expr exte) ->
        (* ========================================== *)
        (* ------------------------------------------ *)
        (red_expr S C exte o)

  | red_expr_this :
      forall (S : state (* input *)) (C : execution_ctx (* input *)),
        (* ========================================== *)
        (* ------------------------------------------ *)
        (red_expr S C (expr_basic expr_this) (out_ter S ((resvalue_value (execution_ctx_this_binding C)) : res)))

  | red_expr_identifier :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (x : prop_name (* input *)) (y1 : (specret ref)) (o : out),
        (* ========================================== *)
        (red_spec S C (spec_identifier_resolution C x) y1) ->
        (red_expr S C (expr_identifier_1 y1) o) ->
        (* ------------------------------------------ *)
        (red_expr S C (expr_basic (expr_identifier (x : string))) o)

  | red_expr_identifier_1 :
      forall (S0 : state (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (r : ref (* input *)),
        (* ========================================== *)
        (* ------------------------------------------ *)
        (red_expr S0 C (expr_identifier_1 ((specret_val S r) : (specret ref))) (out_ter S ((resvalue_ref r) : res)))

  | red_expr_literal :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (i : literal (* input *)),
        (* ========================================== *)
        (* ------------------------------------------ *)
        (red_expr S C (expr_basic (expr_literal i)) (out_ter S ((resvalue_value ((convert_literal_to_prim i) : value)) : res)))

  | red_expr_object :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (pds : (list (propname * propbody)) (* input *)) (o1 : out) (o : out),
        (* ========================================== *)
        (red_expr S C (spec_construct_prealloc prealloc_object (nil : (list value))) o1) ->
        (red_expr S C (expr_object_0 o1 (pds : propdefs)) o) ->
        (* ------------------------------------------ *)
        (red_expr S C (expr_basic (expr_object pds)) o)

  | red_expr_object_0 :
      forall (S0 : state (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (l : object_loc (* input *)) (pds : propdefs (* input *)) (o : out),
        (* ========================================== *)
        (red_expr S C (expr_object_1 l pds) o) ->
        (* ------------------------------------------ *)
        (red_expr S0 C (expr_object_0 (out_ter S ((resvalue_value (value_object l)) : res)) pds) o)

  | red_expr_object_1_nil :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (l : object_loc (* input *)),
        (* ========================================== *)
        (* ------------------------------------------ *)
        (red_expr S C (expr_object_1 l (nil : propdefs)) (out_ter S ((resvalue_value (value_object l)) : res)))

  | red_expr_object_1_cons :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (l : object_loc (* input *)) (pn : propname (* input *)) (pb : propbody (* input *)) (pds : propdefs (* input *)) (o : out),
        (* ========================================== *)
        (red_expr S C (expr_object_2 l ((string_of_propname pn) : string) pb pds) o) ->
        (* ------------------------------------------ *)
        (red_expr S C (expr_object_1 l (((pn, pb) :: pds) : propdefs)) o)

  | red_expr_object_2_val :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (e : expr (* input *)) (l : object_loc (* input *)) (x : prop_name (* input *)) (pds : propdefs (* input *)) (y1 : (specret value)) (o : out),
        (* ========================================== *)
        (red_spec S C (spec_expr_get_value e) y1) ->
        (red_expr S C (expr_object_3_val l (x : string) y1 pds) o) ->
        (* ------------------------------------------ *)
        (red_expr S C (expr_object_2 l (x : string) (propbody_val e) pds) o)

  | red_expr_object_3_val :
      forall (S : state (* input *)) (S0 : state (* input *)) (C : execution_ctx (* input *)) (l : object_loc (* input *)) (x : prop_name (* input *)) (v : value (* input *)) (o : out) (pds : propdefs (* input *)),
        (* ========================================== *)
        (red_expr S C (expr_object_4 l (x : string) (attributes_data_of (attributes_data_intro v true true true)) pds) o) ->
        (* ------------------------------------------ *)
        (red_expr S0 C (expr_object_3_val l (x : string) ((specret_val S v) : (specret value)) pds) o)

  | red_expr_object_2_get :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (bd : funcbody (* input *)) (l : object_loc (* input *)) (x : prop_name (* input *)) (o : out) (o1 : out) (pds : propdefs (* input *)),
        (* ========================================== *)
        (red_expr S C (spec_create_new_function_in C (nil : (list string)) bd) o1) ->
        (red_expr S C (expr_object_3_get l (x : string) o1 pds) o) ->
        (* ------------------------------------------ *)
        (red_expr S C (expr_object_2 l (x : string) (propbody_get bd) pds) o)

  | red_expr_object_3_get :
      forall (S : state (* input *)) (S0 : state (* input *)) (C : execution_ctx (* input *)) (l : object_loc (* input *)) (x : prop_name (* input *)) (v : value (* input *)) (pds : propdefs (* input *)) (o : out),
        (* ========================================== *)
        (red_expr S C (expr_object_4 l (x : string) (attributes_accessor_of (attributes_accessor_intro v undef true true)) pds) o) ->
        (* ------------------------------------------ *)
        (red_expr S0 C (expr_object_3_get l (x : string) (out_ter S ((resvalue_value v) : res)) pds) o)

  | red_expr_object_2_set :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (l : object_loc (* input *)) (x : prop_name (* input *)) (pds : propdefs (* input *)) (o : out) (o1 : out) (bd : funcbody (* input *)) (args : (list string) (* input *)),
        (* ========================================== *)
        (red_expr S C (spec_create_new_function_in C args bd) o1) ->
        (red_expr S C (expr_object_3_set l (x : string) o1 pds) o) ->
        (* ------------------------------------------ *)
        (red_expr S C (expr_object_2 l (x : string) (propbody_set args bd) pds) o)

  | red_expr_object_3_set :
      forall (S : state (* input *)) (S0 : state (* input *)) (C : execution_ctx (* input *)) (l : object_loc (* input *)) (x : prop_name (* input *)) (v : value (* input *)) (pds : propdefs (* input *)) (o : out),
        (* ========================================== *)
        (red_expr S C (expr_object_4 l (x : string) (attributes_accessor_of (attributes_accessor_intro undef v true true)) pds) o) ->
        (* ------------------------------------------ *)
        (red_expr S0 C (expr_object_3_set l (x : string) (out_ter S ((resvalue_value v) : res)) pds) o)

  | red_expr_object_4 :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (A : attributes (* input *)) (l : object_loc (* input *)) (x : prop_name (* input *)) (pds : propdefs (* input *)) (o : out) (o1 : out),
        (* ========================================== *)
        (red_expr S C (spec_object_define_own_prop l x (descriptor_of_attributes A) false) o1) ->
        (red_expr S C (expr_object_5 l pds o1) o) ->
        (* ------------------------------------------ *)
        (red_expr S C (expr_object_4 l (x : string) A pds) o)

  | red_expr_object_5 :
      forall (S : state (* input *)) (S0 : state (* input *)) (C : execution_ctx (* input *)) (rv : resvalue (* input *)) (l : object_loc (* input *)) (pds : propdefs (* input *)) (o : out),
        (* ========================================== *)
        (red_expr S C (expr_object_1 l pds) o) ->
        (* ------------------------------------------ *)
        (red_expr S0 C (expr_object_5 l pds (out_ter S (rv : res))) o)

  | red_expr_member :
      forall (x : prop_name (* input *)) (S0 : state (* input *)) (C : execution_ctx (* input *)) (e1 : expr (* input *)) (o : out),
        (* ========================================== *)
        (red_expr S0 C (expr_basic (expr_access e1 (expr_literal (literal_string (x : string))))) o) ->
        (* ------------------------------------------ *)
        (red_expr S0 C (expr_basic (expr_member e1 (x : string))) o)

  | red_expr_access :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (e1 : expr (* input *)) (e2 : expr (* input *)) (y1 : (specret value)) (o : out),
        (* ========================================== *)
        (red_spec S C (spec_expr_get_value e1) y1) ->
        (red_expr S C (expr_access_1 y1 e2) o) ->
        (* ------------------------------------------ *)
        (red_expr S C (expr_basic (expr_access e1 e2)) o)

  | red_expr_access_1 :
      forall (S0 : state (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (v1 : value (* input *)) (e2 : expr (* input *)) (y1 : (specret value)) (o : out),
        (* ========================================== *)
        (red_spec S C (spec_expr_get_value e2) y1) ->
        (red_expr S C (expr_access_2 v1 y1) o) ->
        (* ------------------------------------------ *)
        (red_expr S0 C (expr_access_1 ((specret_val S v1) : (specret value)) e2) o)

  | red_expr_access_2 :
      forall (S0 : state (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (v1 : value (* input *)) (v2 : value (* input *)) (o1 : out) (o : out),
        (* ========================================== *)
        (red_expr S C (spec_check_object_coercible v1) o1) ->
        (red_expr S C (expr_access_3 v1 o1 v2) o) ->
        (* ------------------------------------------ *)
        (red_expr S0 C (expr_access_2 v1 ((specret_val S v2) : (specret value))) o)

  | red_expr_access_3 :
      forall (S0 : state (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (v1 : value (* input *)) (v2 : value (* input *)) (o1 : out) (o : out),
        (* ========================================== *)
        (red_expr S C (spec_to_string v2) o1) ->
        (red_expr S C (expr_access_4 v1 o1) o) ->
        (* ------------------------------------------ *)
        (red_expr S0 C (expr_access_3 v1 (out_ter S (res_intro restype_normal resvalue_empty label_empty)) v2) o)

  | red_expr_access_4 :
      forall (S0 : state (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (v1 : value (* input *)) (x : prop_name (* input *)),
        (* ========================================== *)
        (* ------------------------------------------ *)
        (red_expr S0 C (expr_access_4 v1 (out_ter S ((resvalue_value (value_prim (prim_string (x : string)))) : res))) (out_ter S ((resvalue_ref ((ref_create_value v1 x (execution_ctx_strict C)) : ref)) : res)))

  | red_expr_new :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (e1 : expr (* input *)) (e2s : (list expr) (* input *)) (y1 : (specret value)) (o : out),
        (* ========================================== *)
        (red_spec S C (spec_expr_get_value e1) y1) ->
        (red_expr S C (expr_new_1 y1 e2s) o) ->
        (* ------------------------------------------ *)
        (red_expr S C (expr_basic (expr_new e1 e2s)) o)

  | red_expr_new_1 :
      forall (S0 : state (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (e2s : (list expr) (* input *)) (v : value (* input *)) (y1 : (specret (list value))) (o : out),
        (* ========================================== *)
        (red_spec S C (spec_list_expr e2s) y1) ->
        (red_expr S C (expr_new_2 v y1) o) ->
        (* ------------------------------------------ *)
        (red_expr S0 C (expr_new_1 ((specret_val S v) : (specret value)) e2s) o)

  | red_expr_new_2_type_error_not_object :
      forall (S : state (* input *)) (S0 : state (* input *)) (C : execution_ctx (* input *)) (o : out) (v : value (* input *)) (vs : (list value) (* input *)),
        (((type_of v) : type) <> type_object) ->
        (* ========================================== *)
        (red_expr S C (spec_error native_error_type) o) ->
        (* ------------------------------------------ *)
        (red_expr S0 C (expr_new_2 v ((specret_val S vs) : (specret (list value)))) o)

  | red_expr_new_2_type_error_no_construct :
      forall (S : state (* input *)) (S0 : state (* input *)) (C : execution_ctx (* input *)) (o : out) (l : object_loc (* input *)) (vs : (list value) (* input *)),
        (object_method object_construct_ S l None) ->
        (* ========================================== *)
        (red_expr S C (spec_error native_error_type) o) ->
        (* ------------------------------------------ *)
        (red_expr S0 C (expr_new_2 (value_object l) ((specret_val S vs) : (specret (list value)))) o)

  | red_expr_new_2_construct :
      forall (S : state (* input *)) (S0 : state (* input *)) (C : execution_ctx (* input *)) (l : object_loc (* input *)) (vs : (list value) (* input *)) (o : out),
        (* ========================================== *)
        (red_expr S C (spec_construct l vs) o) ->
        (* ------------------------------------------ *)
        (red_expr S0 C (expr_new_2 (value_object l) ((specret_val S vs) : (specret (list value)))) o)

  | red_expr_call :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (e1 : expr (* input *)) (e2s : (list expr) (* input *)) (o1 : out) (o2 : out),
        (* ========================================== *)
        (red_expr S C (expr_basic e1) o1) ->
        (red_expr S C (expr_call_1 o1 (is_syntactic_eval e1) e2s) o2) ->
        (* ------------------------------------------ *)
        (red_expr S C (expr_basic (expr_call e1 e2s)) o2)

  | red_expr_call_1 :
      forall (S0 : state (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (rv : resvalue (* input *)) (is_eval_direct : bool (* input *)) (e2s : (list expr) (* input *)) (y1 : (specret value)) (o : out),
        (* ========================================== *)
        (red_spec S C (spec_get_value rv) y1) ->
        (red_expr S C (expr_call_2 (rv : res) is_eval_direct e2s y1) o) ->
        (* ------------------------------------------ *)
        (red_expr S0 C (expr_call_1 (out_ter S (rv : res)) is_eval_direct e2s) o)

  | red_expr_call_2 :
      forall (S0 : state (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (rv : resvalue (* input *)) (v : value (* input *)) (e2s : (list expr) (* input *)) (is_eval_direct : bool (* input *)) (y1 : (specret (list value))) (o : out),
        (* ========================================== *)
        (red_spec S C (spec_list_expr e2s) y1) ->
        (red_expr S C (expr_call_3 (rv : res) v is_eval_direct y1) o) ->
        (* ------------------------------------------ *)
        (red_expr S0 C (expr_call_2 (rv : res) is_eval_direct e2s ((specret_val S v) : (specret value))) o)

  | red_expr_call_3 :
      forall (S0 : state (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (o : out) (rv : resvalue (* input *)) (v : value (* input *)) (is_eval_direct : bool (* input *)) (vs : (list value) (* input *)),
        (((type_of v) <> type_object) \/ (exists l, ((v = (value_object l)) /\ (~ (is_callable S l))))) ->
        (* ========================================== *)
        (red_expr S C (spec_error native_error_type) o) ->
        (* ------------------------------------------ *)
        (red_expr S0 C (expr_call_3 (rv : res) v is_eval_direct ((specret_val S vs) : (specret (list value)))) o)

  | red_expr_call_3_callable :
      forall (l : object_loc (* input *)) (S0 : state (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (o : out) (rv : resvalue (* input *)) (is_eval_direct : bool (* input *)) (vs : (list value) (* input *)),
        (is_callable S (value_object l)) ->
        (* ========================================== *)
        (red_expr S C (expr_call_4 (rv : res) l is_eval_direct vs) o) ->
        (* ------------------------------------------ *)
        (red_expr S0 C (expr_call_3 (rv : res) (value_object l) is_eval_direct ((specret_val S vs) : (specret (list value)))) o)

  | red_expr_call_4_prop :
      forall (v : value) (S : state (* input *)) (C : execution_ctx (* input *)) (o : out) (r : ref (* input *)) (l : object_loc (* input *)) (is_eval_direct : bool (* input *)) (vs : (list value) (* input *)),
        (ref_is_property r) ->
        (ref_is_value r v) ->
        (* ========================================== *)
        (red_expr S C (expr_call_5 l is_eval_direct vs (out_ter S ((resvalue_value v) : res))) o) ->
        (* ------------------------------------------ *)
        (red_expr S C (expr_call_4 ((resvalue_ref r) : res) l is_eval_direct vs) o)

  | red_expr_call_4_env :
      forall (L : env_loc) (o1 : out) (S : state (* input *)) (C : execution_ctx (* input *)) (o : out) (r : ref (* input *)) (l : object_loc (* input *)) (is_eval_direct : bool (* input *)) (vs : (list value) (* input *)),
        (ref_is_env_record r L) ->
        (* ========================================== *)
        (red_expr S C (spec_env_record_implicit_this_value L) o1) ->
        (red_expr S C (expr_call_5 l is_eval_direct vs o1) o) ->
        (* ------------------------------------------ *)
        (red_expr S C (expr_call_4 ((resvalue_ref r) : res) l is_eval_direct vs) o)

  | red_expr_call_4_not_ref :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (v : value (* input *)) (l : object_loc (* input *)) (is_eval_direct : bool (* input *)) (vs : (list value) (* input *)) (o : out),
        (* ========================================== *)
        (red_expr S C (expr_call_5 l is_eval_direct vs (out_ter S ((resvalue_value undef) : res))) o) ->
        (* ------------------------------------------ *)
        (red_expr S C (expr_call_4 ((resvalue_value v) : res) l is_eval_direct vs) o)

  | red_expr_call_5_eval :
      forall (S0 : state (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (is_eval_direct : bool (* input *)) (vs : (list value) (* input *)) (v : value (* input *)) (o : out),
        (* ========================================== *)
        (red_expr S C (spec_call_global_eval is_eval_direct vs) o) ->
        (* ------------------------------------------ *)
        (red_expr S0 C (expr_call_5 (object_loc_prealloc prealloc_global_eval) is_eval_direct vs (out_ter S ((resvalue_value v) : res))) o)

  | red_expr_call_5_not_eval :
      forall (S0 : state (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (l : object_loc (* input *)) (is_eval_direct : bool (* input *)) (vs : (list value) (* input *)) (v : value (* input *)) (o : out),
        (l <> (object_loc_prealloc prealloc_global_eval)) ->
        (* ========================================== *)
        (red_expr S C (spec_call l v vs) o) ->
        (* ------------------------------------------ *)
        (red_expr S0 C (expr_call_5 l is_eval_direct vs (out_ter S ((resvalue_value v) : res))) o)

  | red_expr_function_unnamed :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (args : (list string) (* input *)) (bd : funcbody (* input *)) (lex : lexical_env) (o : out),
        (lex = (execution_ctx_lexical_env C)) ->
        (* ========================================== *)
        (red_expr S C (spec_creating_function_object args bd lex ((funcbody_is_strict bd) : strictness_flag)) o) ->
        (* ------------------------------------------ *)
        (red_expr S C (expr_basic (expr_function (None : (option string)) args bd)) o)

  | red_expr_function_named :
      forall (L : env_loc) (lextail : (list env_loc)) (E : env_record) (o1 : out) (S : state (* input *)) (C : execution_ctx (* input *)) (s : string (* input *)) (args : (list string) (* input *)) (bd : funcbody (* input *)) (o : out),
        (((fst (lexical_env_alloc_decl S (execution_ctx_lexical_env C))) : (list env_loc)) = (L :: lextail)) ->
        (env_record_binds ((snd (lexical_env_alloc_decl S (execution_ctx_lexical_env C))) : state) L E) ->
        (* ========================================== *)
        (red_expr ((snd (lexical_env_alloc_decl S (execution_ctx_lexical_env C))) : state) C (spec_env_record_create_immutable_binding L (s : prop_name)) o1) ->
        (red_expr ((snd (lexical_env_alloc_decl S (execution_ctx_lexical_env C))) : state) C (expr_function_1 s args bd L ((fst (lexical_env_alloc_decl S (execution_ctx_lexical_env C))) : lexical_env) o1) o) ->
        (* ------------------------------------------ *)
        (red_expr S C (expr_basic (expr_function ((Some s) : (option string)) args bd)) o)

  | red_expr_function_named_1 :
      forall (o1 : out) (S0 : state (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (s : string (* input *)) (args : (list string) (* input *)) (bd : funcbody (* input *)) (L : env_loc (* input *)) (scope : lexical_env (* input *)) (o : out),
        (* ========================================== *)
        (red_expr S C (spec_creating_function_object args bd scope ((funcbody_is_strict bd) : strictness_flag)) o1) ->
        (red_expr S C (expr_function_2 s L o1) o) ->
        (* ------------------------------------------ *)
        (red_expr S0 C (expr_function_1 s args bd L scope (out_ter S (res_intro restype_normal resvalue_empty label_empty))) o)

  | red_expr_function_named_2 :
      forall (o1 : out) (S0 : state (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (s : string (* input *)) (L : env_loc (* input *)) (l : object_loc (* input *)) (o : out),
        (* ========================================== *)
        (red_expr S C (spec_env_record_initialize_immutable_binding L (s : prop_name) (value_object l)) o1) ->
        (red_expr S C (expr_function_3 l o1) o) ->
        (* ------------------------------------------ *)
        (red_expr S0 C (expr_function_2 s L (out_ter S ((resvalue_value (value_object l)) : res))) o)

  | red_expr_function_named_3 :
      forall (S0 : state (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (l : object_loc (* input *)),
        (* ========================================== *)
        (* ------------------------------------------ *)
        (red_expr S0 C (expr_function_3 l (out_ter S (res_intro restype_normal resvalue_empty label_empty))) (out_ter S ((resvalue_value (value_object l)) : res)))

  | red_expr_prepost :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (op : unary_op (* input *)) (e : expr (* input *)) (o1 : out) (o : out),
        (prepost_unary_op op) ->
        (* ========================================== *)
        (red_expr S C (expr_basic e) o1) ->
        (red_expr S C (expr_prepost_1 op o1) o) ->
        (* ------------------------------------------ *)
        (red_expr S C (expr_basic (expr_unary_op op e)) o)

  | red_expr_prepost_1_valid :
      forall (S0 : state (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (rv : resvalue (* input *)) (op : unary_op (* input *)) (y1 : (specret value)) (o : out),
        (* ========================================== *)
        (red_spec S C (spec_get_value rv) y1) ->
        (red_expr S C (expr_prepost_2 op (rv : res) y1) o) ->
        (* ------------------------------------------ *)
        (red_expr S0 C (expr_prepost_1 op (out_ter S (rv : res))) o)

  | red_expr_prepost_2 :
      forall (S0 : state (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (rv : resvalue (* input *)) (op : unary_op (* input *)) (v : value (* input *)) (o1 : out) (o : out),
        (* ========================================== *)
        (red_expr S C (spec_to_number v) o1) ->
        (red_expr S C (expr_prepost_3 op (rv : res) o1) o) ->
        (* ------------------------------------------ *)
        (red_expr S0 C (expr_prepost_2 op (rv : res) ((specret_val S v) : (specret value))) o)

  | red_expr_prepost_3 :
      forall (S0 : state (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (rv : resvalue (* input *)) (op : unary_op (* input *)) (number_op : (number -> number)) (is_pre : bool) (n1 : number (* input *)) (o1 : out) (o : out),
        (prepost_op op number_op is_pre) ->
        (* ========================================== *)
        (red_expr S C (spec_put_value rv (value_prim (prim_number (number_op n1)))) o1) ->
        (red_expr S C (expr_prepost_4 (value_prim (prim_number (ifb is_pre then (number_op n1) else n1))) o1) o) ->
        (* ------------------------------------------ *)
        (red_expr S0 C (expr_prepost_3 op (rv : res) (out_ter S ((resvalue_value (value_prim (prim_number n1))) : res))) o)

  | red_expr_prepost_4 :
      forall (S0 : state (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (v : value (* input *)),
        (* ========================================== *)
        (* ------------------------------------------ *)
        (red_expr S0 C (expr_prepost_4 v (out_ter S (res_intro restype_normal resvalue_empty label_empty))) (out_ter S ((resvalue_value v) : res)))

  | red_expr_unary_op :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (op : unary_op (* input *)) (e : expr (* input *)) (y1 : (specret value)) (o : out),
        (regular_unary_op op) ->
        (* ========================================== *)
        (red_spec S C (spec_expr_get_value e) y1) ->
        (red_expr S C (expr_unary_op_1 op y1) o) ->
        (* ------------------------------------------ *)
        (red_expr S C (expr_basic (expr_unary_op op e)) o)

  | red_expr_unary_op_1 :
      forall (S0 : state (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (op : unary_op (* input *)) (v : value (* input *)) (o : out),
        (* ========================================== *)
        (red_expr S C (expr_unary_op_2 op v) o) ->
        (* ------------------------------------------ *)
        (red_expr S0 C (expr_unary_op_1 op ((specret_val S v) : (specret value))) o)

  | red_expr_delete :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (e : expr (* input *)) (o1 : out) (o : out),
        (* ========================================== *)
        (red_expr S C (expr_basic e) o1) ->
        (red_expr S C (expr_delete_1 o1) o) ->
        (* ------------------------------------------ *)
        (red_expr S C (expr_basic (expr_unary_op unary_op_delete e)) o)

  | red_expr_delete_1_not_ref :
      forall (S0 : state (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (rv : resvalue (* input *)),
        (resvalue_is_ref rv) ->
        (* ========================================== *)
        (* ------------------------------------------ *)
        (red_expr S0 C (expr_delete_1 (out_ter S (rv : res))) (out_ter S ((resvalue_value (value_prim (prim_bool ((true : provide_this_flag) : bool)))) : res)))

  | red_expr_delete_1_ref_unresolvable :
      forall (S0 : state (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (r : ref (* input *)) (o : out),
        (ref_is_unresolvable r) ->
        (* ========================================== *)
        (red_expr S C (expr_delete_2 r) o) ->
        (* ------------------------------------------ *)
        (red_expr S0 C (expr_delete_1 (out_ter S ((resvalue_ref r) : res))) o)

  | red_expr_delete_2_strict :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (r : ref (* input *)) (o : out),
        ((ref_strict r) = true) ->
        (* ========================================== *)
        (red_expr S C (spec_error native_error_syntax) o) ->
        (* ------------------------------------------ *)
        (red_expr S C (expr_delete_2 r) o)

  | red_expr_delete_2_not_strict :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (r : ref (* input *)),
        ((ref_strict r) = false) ->
        (* ========================================== *)
        (* ------------------------------------------ *)
        (red_expr S C (expr_delete_2 r) (out_ter S ((resvalue_value (value_prim (prim_bool ((true : provide_this_flag) : bool)))) : res)))

  | red_expr_delete_1_ref_property :
      forall (S0 : state (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (r : ref (* input *)) (v : value) (o1 : out) (o : out),
        (ref_is_property r) ->
        ((ref_base r) = (ref_base_type_value v)) ->
        (* ========================================== *)
        (red_expr S C (spec_to_object v) o1) ->
        (red_expr S C (expr_delete_3 r o1) o) ->
        (* ------------------------------------------ *)
        (red_expr S0 C (expr_delete_1 (out_ter S ((resvalue_ref r) : res))) o)

  | red_expr_delete_3 :
      forall (S0 : state (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (r : ref (* input *)) (l : object_loc (* input *)) (o : out),
        (* ========================================== *)
        (red_expr S C (spec_object_delete l (ref_name r) (ref_strict r)) o) ->
        (* ------------------------------------------ *)
        (red_expr S0 C (expr_delete_3 r (out_ter S ((resvalue_value (value_object l)) : res))) o)

  | red_expr_delete_1_ref_env_record :
      forall (S0 : state (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (r : ref (* input *)) (L : env_loc) (o : out),
        (ref_is_env_record r L) ->
        (* ========================================== *)
        (red_expr S C (expr_delete_4 r L) o) ->
        (* ------------------------------------------ *)
        (red_expr S0 C (expr_delete_1 (out_ter S ((resvalue_ref r) : res))) o)

  | red_expr_delete_4_strict :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (r : ref (* input *)) (L : env_loc (* input *)) (o : out),
        ((ref_strict r) = true) ->
        (* ========================================== *)
        (red_expr S C (spec_error native_error_syntax) o) ->
        (* ------------------------------------------ *)
        (red_expr S C (expr_delete_4 r L) o)

  | red_expr_delete_4_not_strict :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (r : ref (* input *)) (L : env_loc (* input *)) (o : out),
        ((ref_strict r) = false) ->
        (* ========================================== *)
        (red_expr S C (spec_env_record_delete_binding L (ref_name r)) o) ->
        (* ------------------------------------------ *)
        (red_expr S C (expr_delete_4 r L) o)

  | red_expr_unary_op_void :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (v : value (* input *)),
        (* ========================================== *)
        (* ------------------------------------------ *)
        (red_expr S C (expr_unary_op_2 unary_op_void v) (out_ter S ((resvalue_value undef) : res)))

  | red_expr_typeof :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (e : expr (* input *)) (o1 : out) (o : out),
        (* ========================================== *)
        (red_expr S C (expr_basic e) o1) ->
        (red_expr S C (expr_typeof_1 o1) o) ->
        (* ------------------------------------------ *)
        (red_expr S C (expr_basic (expr_unary_op unary_op_typeof e)) o)

  | red_expr_typeof_1_value :
      forall (S0 : state (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (v : value (* input *)) (o : out),
        (* ========================================== *)
        (red_expr S C (expr_typeof_2 ((ret S v) : (specret value))) o) ->
        (* ------------------------------------------ *)
        (red_expr S0 C (expr_typeof_1 (out_ter S ((resvalue_value v) : res))) o)

  | red_expr_typeof_1_ref_unresolvable :
      forall (S0 : state (* input *)) (S : state (* input *)) (r : ref (* input *)) (C : execution_ctx (* input *)),
        (ref_is_unresolvable r) ->
        (* ========================================== *)
        (* ------------------------------------------ *)
        (red_expr S0 C (expr_typeof_1 (out_ter S ((resvalue_ref r) : res))) (out_ter S ((resvalue_value (value_prim (prim_string (("undefined")%string)))) : res)))

  | red_expr_typeof_1_ref_resolvable :
      forall (S0 : state (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (r : ref (* input *)) (y1 : (specret value)) (o : out),
        (ref_is_unresolvable r) ->
        (* ========================================== *)
        (red_spec S C (spec_get_value (resvalue_ref r)) y1) ->
        (red_expr S C (expr_typeof_2 y1) o) ->
        (* ------------------------------------------ *)
        (red_expr S0 C (expr_typeof_1 (out_ter S ((resvalue_ref r) : res))) o)

  | red_expr_typeof_2 :
      forall (S0 : state (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (v : value (* input *)),
        (* ========================================== *)
        (* ------------------------------------------ *)
        (red_expr S0 C (expr_typeof_2 ((specret_val S v) : (specret value))) (out_ter S ((resvalue_value (value_prim (prim_string ((typeof_value S v) : string)))) : res)))

  | red_expr_unary_op_add :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (v : value (* input *)) (o : out),
        (* ========================================== *)
        (red_expr S C (spec_to_number v) o) ->
        (* ------------------------------------------ *)
        (red_expr S C (expr_unary_op_2 unary_op_add v) o)

  | red_expr_unary_op_neg :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (v : value (* input *)) (o1 : out) (o : out),
        (* ========================================== *)
        (red_expr S C (spec_to_number v) o1) ->
        (red_expr S C (expr_unary_op_neg_1 o1) o) ->
        (* ------------------------------------------ *)
        (red_expr S C (expr_unary_op_2 unary_op_neg v) o)

  | red_expr_unary_op_neg_1 :
      forall (S0 : state (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (n : number (* input *)),
        (* ========================================== *)
        (* ------------------------------------------ *)
        (red_expr S0 C (expr_unary_op_neg_1 (out_ter S ((resvalue_value (value_prim (prim_number n))) : res))) (out_ter S ((JsNumber.neg n) : res)))

  | red_expr_unary_op_bitwise_not :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (v : value (* input *)) (y1 : (specret int)) (o : out),
        (* ========================================== *)
        (red_spec S C (spec_to_int32 v) y1) ->
        (red_expr S C (expr_unary_op_bitwise_not_1 y1) o) ->
        (* ------------------------------------------ *)
        (red_expr S C (expr_unary_op_2 unary_op_bitwise_not v) o)

  | red_expr_unary_op_bitwise_not_1 :
      forall (S0 : state (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (k : int (* input *)),
        (* ========================================== *)
        (* ------------------------------------------ *)
        (red_expr S0 C (expr_unary_op_bitwise_not_1 ((specret_val S k) : (specret int))) (out_ter S ((resvalue_value (value_prim (prim_number ((JsNumber.of_int (JsNumber.int32_bitwise_not k)) : number)))) : res)))

  | red_expr_unary_op_not :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (v : value (* input *)) (o1 : out) (o : out),
        (* ========================================== *)
        (red_expr S C (spec_to_boolean v) o1) ->
        (red_expr S C (expr_unary_op_not_1 o1) o) ->
        (* ------------------------------------------ *)
        (red_expr S C (expr_unary_op_2 unary_op_not v) o)

  | red_expr_unary_op_not_1 :
      forall (S0 : state (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (b : bool (* input *)),
        (* ========================================== *)
        (* ------------------------------------------ *)
        (red_expr S0 C (expr_unary_op_not_1 (out_ter S ((resvalue_value (value_prim (prim_bool ((b : provide_this_flag) : bool)))) : res))) (out_ter S ((neg b) : res)))

  | red_expr_binary_op :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (op : binary_op (* input *)) (e1 : expr (* input *)) (e2 : expr (* input *)) (y1 : (specret value)) (o : out),
        (regular_binary_op op) ->
        (* ========================================== *)
        (red_spec S C (spec_expr_get_value e1) y1) ->
        (red_expr S C (expr_binary_op_1 op y1 e2) o) ->
        (* ------------------------------------------ *)
        (red_expr S C (expr_basic (expr_binary_op e1 op e2)) o)

  | red_expr_binary_op_1 :
      forall (S0 : state (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (op : binary_op (* input *)) (v1 : value (* input *)) (e2 : expr (* input *)) (y1 : (specret value)) (o : out),
        (* ========================================== *)
        (red_spec S C (spec_expr_get_value e2) y1) ->
        (red_expr S C (expr_binary_op_2 op v1 y1) o) ->
        (* ------------------------------------------ *)
        (red_expr S0 C (expr_binary_op_1 op ((specret_val S v1) : (specret value)) e2) o)

  | red_expr_binary_op_2 :
      forall (S0 : state (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (op : binary_op (* input *)) (v1 : value (* input *)) (v2 : value (* input *)) (o : out),
        (* ========================================== *)
        (red_expr S C (expr_binary_op_3 op v1 v2) o) ->
        (* ------------------------------------------ *)
        (red_expr S0 C (expr_binary_op_2 op v1 ((specret_val S v2) : (specret value))) o)

  | red_expr_binary_op_add :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (v1 : value (* input *)) (v2 : value (* input *)) (y1 : (specret (value * value))) (o : out),
        (* ========================================== *)
        (red_spec S C (spec_convert_twice (spec_to_primitive_auto v1) (spec_to_primitive_auto v2)) y1) ->
        (red_expr S C (expr_binary_op_add_1 y1) o) ->
        (* ------------------------------------------ *)
        (red_expr S C (expr_binary_op_3 binary_op_add v1 v2) o)

  | red_expr_binary_op_add_1_string :
      forall (S0 : state (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (v1 : value (* input *)) (v2 : value (* input *)) (y1 : (specret (value * value))) (o : out),
        (((type_of v1) = type_string) \/ ((type_of v2) = type_string)) ->
        (* ========================================== *)
        (red_spec S C (spec_convert_twice (spec_to_string v1) (spec_to_string v2)) y1) ->
        (red_expr S C (expr_binary_op_add_string_1 y1) o) ->
        (* ------------------------------------------ *)
        (red_expr S0 C (expr_binary_op_add_1 ((specret_val S (v1, v2)) : (specret (value * value)))) o)

  | red_expr_binary_op_add_string_1 :
      forall (S0 : state (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (s1 : string (* input *)) (s2 : string (* input *)),
        (* ========================================== *)
        (* ------------------------------------------ *)
        (red_expr S0 C (expr_binary_op_add_string_1 ((specret_val S ((value_prim (prim_string s1)), (value_prim (prim_string s2)))) : (specret (value * value)))) (out_ter S ((resvalue_value (value_prim (prim_string ((String.append s1 s2) : string)))) : res)))

  | red_expr_binary_op_add_1_number :
      forall (S0 : state (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (v1 : value (* input *)) (v2 : value (* input *)) (y1 : (specret (value * value))) (o : out),
        (((type_of v1) = type_string) \/ ((type_of v2) = type_string)) ->
        (* ========================================== *)
        (red_spec S C (spec_convert_twice (spec_to_number v1) (spec_to_number v2)) y1) ->
        (red_expr S C (expr_puremath_op_1 JsNumber.add y1) o) ->
        (* ------------------------------------------ *)
        (red_expr S0 C (expr_binary_op_add_1 ((specret_val S (v1, v2)) : (specret (value * value)))) o)

  | red_expr_puremath_op :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (op : binary_op (* input *)) (F : (number -> (number -> number))) (v1 : value (* input *)) (v2 : value (* input *)) (y1 : (specret (value * value))) (o : out),
        (puremath_op op F) ->
        (* ========================================== *)
        (red_spec S C (spec_convert_twice (spec_to_number v1) (spec_to_number v2)) y1) ->
        (red_expr S C (expr_puremath_op_1 F y1) o) ->
        (* ------------------------------------------ *)
        (red_expr S C (expr_binary_op_3 op v1 v2) o)

  | red_expr_puremath_op_1 :
      forall (S0 : state (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (F : (number -> (number -> number)) (* input *)) (n1 : number (* input *)) (n2 : number (* input *)),
        (* ========================================== *)
        (* ------------------------------------------ *)
        (red_expr S0 C (expr_puremath_op_1 F ((specret_val S ((value_prim (prim_number n1)), (value_prim (prim_number n2)))) : (specret (value * value)))) (out_ter S ((resvalue_value (value_prim (prim_number (F n1 n2)))) : res)))

  | red_expr_shift_op :
      forall (b_unsigned : bool) (S : state (* input *)) (C : execution_ctx (* input *)) (op : binary_op (* input *)) (F : (int -> (int -> int))) (ext : (value -> ext_spec)) (v1 : value (* input *)) (v2 : value (* input *)) (y1 : (specret int)) (o : out),
        (shift_op op b_unsigned F) ->
        (ext = (ifb b_unsigned then spec_to_uint32 else spec_to_int32)) ->
        (* ========================================== *)
        (red_spec S C (ext v1) y1) ->
        (red_expr S C (expr_shift_op_1 F y1 v2) o) ->
        (* ------------------------------------------ *)
        (red_expr S C (expr_binary_op_3 op v1 v2) o)

  | red_expr_shift_op_1 :
      forall (S0 : state (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (F : (int -> (int -> int)) (* input *)) (k1 : int (* input *)) (v2 : value (* input *)) (y1 : (specret int)) (o : out),
        (* ========================================== *)
        (red_spec S C (spec_to_uint32 v2) y1) ->
        (red_expr S C (expr_shift_op_2 F k1 y1) o) ->
        (* ------------------------------------------ *)
        (red_expr S0 C (expr_shift_op_1 F ((specret_val S k1) : (specret int)) v2) o)

  | red_expr_shift_op_2 :
      forall (S0 : state (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (k1 : int (* input *)) (k2 : int (* input *)) (F : (int -> (int -> int)) (* input *)),
        (* ========================================== *)
        (* ------------------------------------------ *)
        (red_expr S0 C (expr_shift_op_2 F k1 ((specret_val S k2) : (specret int))) (out_ter S ((resvalue_value (value_prim (prim_number ((JsNumber.of_int (F k1 (JsNumber.modulo_32 k2))) : number)))) : res)))

  | red_expr_inequality_op :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (v1 : value (* input *)) (v2 : value (* input *)) (op : binary_op (* input *)) (b_swap : bool) (b_neg : bool) (o : out),
        (inequality_op op b_swap b_neg) ->
        (* ========================================== *)
        (red_expr S C (expr_inequality_op_1 b_swap b_neg v1 v2) o) ->
        (* ------------------------------------------ *)
        (red_expr S C (expr_binary_op_3 op v1 v2) o)

  | red_expr_inequality_op_1 :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (v1 : value (* input *)) (v2 : value (* input *)) (b_swap : bool (* input *)) (b_neg : bool (* input *)) (y1 : (specret (value * value))) (o : out),
        (* ========================================== *)
        (red_spec S C (spec_convert_twice (spec_to_primitive_auto v1) (spec_to_primitive_auto v2)) y1) ->
        (red_expr S C (expr_inequality_op_2 b_swap b_neg y1) o) ->
        (* ------------------------------------------ *)
        (red_expr S C (expr_inequality_op_1 b_swap b_neg v1 v2) o)

  | red_expr_inequality_op_2 :
      forall (S0 : state (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (w1 : prim (* input *)) (w2 : prim (* input *)) (b_swap : bool (* input *)) (b_neg : bool (* input *)),
        (* ========================================== *)
        (* ------------------------------------------ *)
        (red_expr S0 C (expr_inequality_op_2 b_swap b_neg ((specret_val S ((value_prim w1), (value_prim w2))) : (specret (value * value)))) (out_ter S ((resvalue_value (value_prim (ifb ((inequality_test_primitive ((fst (ifb b_swap then (w2, w1) else (w1, w2))) : prim) ((snd (ifb b_swap then (w2, w1) else (w1, w2))) : prim)) = prim_undef) then (prim_bool ((false : provide_this_flag) : bool)) else (ifb ((b_neg = true) /\ ((inequality_test_primitive ((fst (ifb b_swap then (w2, w1) else (w1, w2))) : prim) ((snd (ifb b_swap then (w2, w1) else (w1, w2))) : prim)) = true)) then (prim_bool ((false : provide_this_flag) : bool)) else (ifb ((b_neg = true) /\ ((inequality_test_primitive ((fst (ifb b_swap then (w2, w1) else (w1, w2))) : prim) ((snd (ifb b_swap then (w2, w1) else (w1, w2))) : prim)) = false)) then (prim_bool ((true : provide_this_flag) : bool)) else (inequality_test_primitive ((fst (ifb b_swap then (w2, w1) else (w1, w2))) : prim) ((snd (ifb b_swap then (w2, w1) else (w1, w2))) : prim))))))) : res)))

  | red_expr_binary_op_instanceof_non_object :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (v1 : value (* input *)) (v2 : value (* input *)) (o : out),
        (((type_of v2) : type) <> type_object) ->
        (* ========================================== *)
        (red_expr S C (spec_error native_error_type) o) ->
        (* ------------------------------------------ *)
        (red_expr S C (expr_binary_op_3 binary_op_instanceof v1 v2) o)

  | red_expr_binary_op_instanceof_non_instance :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (v1 : value (* input *)) (l : object_loc (* input *)) (o : out),
        (object_method object_has_instance_ S l None) ->
        (* ========================================== *)
        (red_expr S C (spec_error native_error_type) o) ->
        (* ------------------------------------------ *)
        (red_expr S C (expr_binary_op_3 binary_op_instanceof v1 (value_object l)) o)

  | red_expr_binary_op_instanceof_normal :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (v1 : value (* input *)) (l : object_loc (* input *)) (o : out),
        (* ========================================== *)
        (red_expr S C (spec_object_has_instance l v1) o) ->
        (* ------------------------------------------ *)
        (red_expr S C (expr_binary_op_3 binary_op_instanceof v1 (value_object l)) o)

  | red_expr_binary_op_in_non_object :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (v1 : value (* input *)) (v2 : value (* input *)) (o : out),
        (((type_of v2) : type) <> type_object) ->
        (* ========================================== *)
        (red_expr S C (spec_error native_error_type) o) ->
        (* ------------------------------------------ *)
        (red_expr S C (expr_binary_op_3 binary_op_in v1 v2) o)

  | red_expr_binary_op_in_object :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (v1 : value (* input *)) (l : object_loc (* input *)) (o1 : out) (o : out),
        (* ========================================== *)
        (red_expr S C (spec_to_string v1) o1) ->
        (red_expr S C (expr_binary_op_in_1 l o1) o) ->
        (* ------------------------------------------ *)
        (red_expr S C (expr_binary_op_3 binary_op_in v1 (value_object l)) o)

  | red_expr_binary_op_in_1 :
      forall (S0 : state (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (l : object_loc (* input *)) (x : prop_name (* input *)) (o : out),
        (* ========================================== *)
        (red_expr S C (spec_object_has_prop l x) o) ->
        (* ------------------------------------------ *)
        (red_expr S0 C (expr_binary_op_in_1 l (out_ter S ((resvalue_value (value_prim (prim_string (x : string)))) : res))) o)

  | red_expr_binary_op_equal :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (v1 : value (* input *)) (v2 : value (* input *)) (o : out),
        (* ========================================== *)
        (red_expr S C (spec_equal v1 v2) o) ->
        (* ------------------------------------------ *)
        (red_expr S C (expr_binary_op_3 binary_op_equal v1 v2) o)

  | red_expr_binary_op_disequal :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (v1 : value (* input *)) (v2 : value (* input *)) (o1 : out) (o : out),
        (* ========================================== *)
        (red_expr S C (spec_equal v1 v2) o1) ->
        (red_expr S C (expr_binary_op_disequal_1 o1) o) ->
        (* ------------------------------------------ *)
        (red_expr S C (expr_binary_op_3 binary_op_disequal v1 v2) o)

  | red_expr_binary_op_disequal_1 :
      forall (S0 : state (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (b : bool (* input *)),
        (* ========================================== *)
        (* ------------------------------------------ *)
        (red_expr S0 C (expr_binary_op_disequal_1 (out_ter S ((resvalue_value (value_prim (prim_bool ((b : provide_this_flag) : bool)))) : res))) (out_ter S ((negb b) : res)))

  | red_spec_equal :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (v1 : value (* input *)) (v2 : value (* input *)) (o : out),
        (* ========================================== *)
        (red_expr S C (spec_equal_1 ((type_of v1) : type) ((type_of v2) : type) v1 v2) o) ->
        (* ------------------------------------------ *)
        (red_expr S C (spec_equal v1 v2) o)

  | red_spec_equal_1_same_type :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (v1 : value (* input *)) (v2 : value (* input *)) (ty : type (* input *)),
        (* ========================================== *)
        (* ------------------------------------------ *)
        (red_expr S C (spec_equal_1 ty ty v1 v2) (out_ter S ((resvalue_value (value_prim (prim_bool (((equality_test_for_same_type ty v1 v2) : provide_this_flag) : bool)))) : res)))

  | red_spec_equal_1_diff_type :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (v1 : value (* input *)) (v2 : value (* input *)) (ty1 : type (* input *)) (ty2 : type (* input *)) (ext : ext_expr) (o : out),
        (ext = (ifb ((ty1 = type_null) /\ (ty2 = type_undef)) then (spec_equal_2 true) else (ifb ((ty1 = type_undef) /\ (ty2 = type_null)) then (spec_equal_2 true) else (ifb ((ty1 = type_number) /\ (ty2 = type_string)) then (spec_equal_3 v1 spec_to_number v2) else (ifb ((ty1 = type_string) /\ (ty2 = type_number)) then (spec_equal_3 v2 spec_to_number v1) else (ifb (ty1 = type_bool) then (spec_equal_3 v2 spec_to_number v1) else (ifb (ty2 = type_bool) then (spec_equal_3 v1 spec_to_number v2) else (ifb (((ty1 = type_string) \/ (ty1 = type_number)) /\ (ty2 = type_object)) then (spec_equal_3 v1 spec_to_primitive_auto v2) else (ifb ((ty1 = type_object) /\ ((ty2 = type_string) \/ (ty2 = type_number))) then (spec_equal_3 v2 spec_to_primitive_auto v1) else (spec_equal_2 false)))))))))) ->
        (* ========================================== *)
        (red_expr S C ext o) ->
        (* ------------------------------------------ *)
        (red_expr S C (spec_equal_1 ty1 ty2 v1 v2) o)

  | red_spec_equal_2_return :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (b : bool (* input *)),
        (* ========================================== *)
        (* ------------------------------------------ *)
        (red_expr S C (spec_equal_2 b) (out_ter S ((resvalue_value (value_prim (prim_bool ((b : provide_this_flag) : bool)))) : res)))

  | red_spec_equal_3_convert_and_recurse :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (v1 : value (* input *)) (v2 : value (* input *)) (K : (value -> ext_expr) (* input *)) (o2 : out) (o : out),
        (* ========================================== *)
        (red_expr S C (K v2) o2) ->
        (red_expr S C (spec_equal_4 v1 o2) o) ->
        (* ------------------------------------------ *)
        (red_expr S C (spec_equal_3 v1 K v2) o)

  | red_spec_equal_4_recurse :
      forall (S0 : state (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (v1 : value (* input *)) (v2 : value (* input *)) (o : out),
        (* ========================================== *)
        (red_expr S C (spec_equal v1 v2) o) ->
        (* ------------------------------------------ *)
        (red_expr S0 C (spec_equal_4 v1 (out_ter S ((resvalue_value v2) : res))) o)

  | red_expr_binary_op_strict_equal :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (v1 : value (* input *)) (v2 : value (* input *)),
        (* ========================================== *)
        (* ------------------------------------------ *)
        (red_expr S C (expr_binary_op_3 binary_op_strict_equal v1 v2) (out_ter S ((resvalue_value (value_prim (prim_bool (((strict_equality_test v1 v2) : provide_this_flag) : bool)))) : res)))

  | red_expr_binary_op_strict_disequal :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (v1 : value (* input *)) (v2 : value (* input *)),
        (* ========================================== *)
        (* ------------------------------------------ *)
        (red_expr S C (expr_binary_op_3 binary_op_strict_disequal v1 v2) (out_ter S ((resvalue_value (value_prim (prim_bool ((((negb (strict_equality_test v1 v2)) : bool) : provide_this_flag) : bool)))) : res)))

  | red_expr_bitwise_op :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (op : binary_op (* input *)) (F : (int -> (int -> int))) (v1 : value (* input *)) (v2 : value (* input *)) (y1 : (specret int)) (o : out),
        (bitwise_op op F) ->
        (* ========================================== *)
        (red_spec S C (spec_to_int32 v1) y1) ->
        (red_expr S C (expr_bitwise_op_1 F y1 v2) o) ->
        (* ------------------------------------------ *)
        (red_expr S C (expr_binary_op_3 op v1 v2) o)

  | red_expr_bitwise_op_1 :
      forall (S0 : state (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (F : (int -> (int -> int)) (* input *)) (k1 : int (* input *)) (v2 : value (* input *)) (y1 : (specret int)) (o : out),
        (* ========================================== *)
        (red_spec S C (spec_to_int32 v2) y1) ->
        (red_expr S C (expr_bitwise_op_2 F k1 y1) o) ->
        (* ------------------------------------------ *)
        (red_expr S0 C (expr_bitwise_op_1 F ((specret_val S k1) : (specret int)) v2) o)

  | red_expr_bitwise_op_2 :
      forall (S0 : state (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (F : (int -> (int -> int)) (* input *)) (k1 : int (* input *)) (k2 : int (* input *)),
        (* ========================================== *)
        (* ------------------------------------------ *)
        (red_expr S0 C (expr_bitwise_op_2 F k1 ((specret_val S k2) : (specret int))) (out_ter S ((resvalue_value (value_prim (prim_number ((JsNumber.of_int (F k1 k2)) : number)))) : res)))

  | red_expr_binary_op_lazy :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (op : binary_op (* input *)) (b_ret : bool) (e1 : expr (* input *)) (e2 : expr (* input *)) (y1 : (specret value)) (o : out),
        (lazy_op op b_ret) ->
        (* ========================================== *)
        (red_spec S C (spec_expr_get_value e1) y1) ->
        (red_expr S C (expr_lazy_op_1 b_ret y1 e2) o) ->
        (* ------------------------------------------ *)
        (red_expr S C (expr_basic (expr_binary_op e1 op e2)) o)

  | red_expr_lazy_op_1 :
      forall (S0 : state (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (b_ret : bool (* input *)) (e2 : expr (* input *)) (v1 : value (* input *)) (o1 : out) (o : out),
        (* ========================================== *)
        (red_expr S C (spec_to_boolean v1) o1) ->
        (red_expr S C (expr_lazy_op_2 b_ret v1 o1 e2) o) ->
        (* ------------------------------------------ *)
        (red_expr S0 C (expr_lazy_op_1 b_ret ((specret_val S v1) : (specret value)) e2) o)

  | red_expr_lazy_op_2_first :
      forall (S0 : state (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (b_ret : bool (* input *)) (e2 : expr (* input *)) (v1 : value (* input *)),
        (* ========================================== *)
        (* ------------------------------------------ *)
        (red_expr S0 C (expr_lazy_op_2 b_ret v1 (out_ter S ((resvalue_value (value_prim (prim_bool ((b_ret : provide_this_flag) : bool)))) : res)) e2) (out_ter S ((resvalue_value v1) : res)))

  | red_expr_lazy_op_2_second :
      forall (S0 : state (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (v1 : value (* input *)) (b_ret : bool (* input *)) (b1 : bool (* input *)) (e2 : expr (* input *)) (y1 : (specret value)) (o : out),
        (b1 <> b_ret) ->
        (* ========================================== *)
        (red_spec S C (spec_expr_get_value e2) y1) ->
        (red_expr S C (expr_lazy_op_2_1 y1) o) ->
        (* ------------------------------------------ *)
        (red_expr S0 C (expr_lazy_op_2 b_ret v1 (out_ter S ((resvalue_value (value_prim (prim_bool ((b1 : provide_this_flag) : bool)))) : res)) e2) o)

  | red_expr_lazy_op_2_second_1 :
      forall (S0 : state (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (v : value (* input *)),
        (* ========================================== *)
        (* ------------------------------------------ *)
        (red_expr S0 C (expr_lazy_op_2_1 ((specret_val S v) : (specret value))) (out_ter S ((resvalue_value v) : res)))

  | red_expr_conditional :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (e1 : expr (* input *)) (e2 : expr (* input *)) (e3 : expr (* input *)) (y1 : (specret value)) (o : out),
        (* ========================================== *)
        (red_spec S C (spec_expr_get_value_conv spec_to_boolean e1) y1) ->
        (red_expr S C (expr_conditional_1 y1 e2 e3) o) ->
        (* ------------------------------------------ *)
        (red_expr S C (expr_basic (expr_conditional e1 e2 e3)) o)

  | red_expr_conditional_1 :
      forall (S0 : state (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (b : bool (* input *)) (e2 : expr (* input *)) (e3 : expr (* input *)) (y1 : (specret value)) (o : out),
        (* ========================================== *)
        (red_spec S C (spec_expr_get_value (ifb (b = true) then e2 else e3)) y1) ->
        (red_expr S C (expr_conditional_2 y1) o) ->
        (* ------------------------------------------ *)
        (red_expr S0 C (expr_conditional_1 ((specret_val S (value_prim (prim_bool ((b : provide_this_flag) : bool)))) : (specret value)) e2 e3) o)

  | red_expr_conditional_2 :
      forall (S0 : state (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (v : value (* input *)),
        (* ========================================== *)
        (* ------------------------------------------ *)
        (red_expr S0 C (expr_conditional_2 ((specret_val S v) : (specret value))) (out_ter S ((resvalue_value v) : res)))

  | red_expr_assign :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (opo : (option binary_op) (* input *)) (e1 : expr (* input *)) (e2 : expr (* input *)) (o : out) (o1 : out),
        (* ========================================== *)
        (red_expr S C (expr_basic e1) o1) ->
        (red_expr S C (expr_assign_1 o1 opo e2) o) ->
        (* ------------------------------------------ *)
        (red_expr S C (expr_basic (expr_assign e1 opo e2)) o)

  | red_expr_assign_1_simple :
      forall (S0 : state (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (rv : resvalue (* input *)) (e2 : expr (* input *)) (y1 : (specret value)) (o : out),
        (* ========================================== *)
        (red_spec S C (spec_expr_get_value e2) y1) ->
        (red_expr S C (expr_assign_4 (rv : res) y1) o) ->
        (* ------------------------------------------ *)
        (red_expr S0 C (expr_assign_1 (out_ter S (rv : res)) (None : (option binary_op)) e2) o)

  | red_expr_assign_1_compound :
      forall (S0 : state (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (rv : resvalue (* input *)) (op : binary_op (* input *)) (e2 : expr (* input *)) (y1 : (specret value)) (o : out),
        (* ========================================== *)
        (red_spec S C (spec_get_value rv) y1) ->
        (red_expr S C (expr_assign_2 (rv : res) y1 op e2) o) ->
        (* ------------------------------------------ *)
        (red_expr S0 C (expr_assign_1 (out_ter S (rv : res)) ((Some op) : (option binary_op)) e2) o)

  | red_expr_assign_2_compound_get_value :
      forall (S0 : state (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (rv : resvalue (* input *)) (op : binary_op (* input *)) (v1 : value (* input *)) (e2 : expr (* input *)) (y1 : (specret value)) (o : out),
        (* ========================================== *)
        (red_spec S C (spec_expr_get_value e2) y1) ->
        (red_expr S C (expr_assign_3 (rv : res) v1 op y1) o) ->
        (* ------------------------------------------ *)
        (red_expr S0 C (expr_assign_2 (rv : res) ((specret_val S v1) : (specret value)) op e2) o)

  | red_expr_assign_3_compound_op :
      forall (S0 : state (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (rv : resvalue (* input *)) (op : binary_op (* input *)) (v1 : value (* input *)) (v2 : value (* input *)) (o1 : out) (o : out),
        (* ========================================== *)
        (red_expr S C (expr_binary_op_3 op v1 v2) o1) ->
        (red_expr S C (expr_assign_3' (rv : res) o1) o) ->
        (* ------------------------------------------ *)
        (red_expr S0 C (expr_assign_3 (rv : res) v1 op ((specret_val S v2) : (specret value))) o)

  | red_expr_assign_3' :
      forall (S0 : state (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (v : value (* input *)) (rv : resvalue (* input *)) (o : out),
        (* ========================================== *)
        (red_expr S C (expr_assign_4 (rv : res) ((ret S v) : (specret value))) o) ->
        (* ------------------------------------------ *)
        (red_expr S0 C (expr_assign_3' (rv : res) (out_ter S ((resvalue_value v) : res))) o)

  | red_expr_assign_4_put_value :
      forall (S0 : state (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (rv : resvalue (* input *)) (v : value (* input *)) (o1 : out) (o : out),
        (* ========================================== *)
        (red_expr S C (spec_put_value rv v) o1) ->
        (red_expr S C (expr_assign_5 v o1) o) ->
        (* ------------------------------------------ *)
        (red_expr S0 C (expr_assign_4 (rv : res) ((specret_val S v) : (specret value))) o)

  | red_expr_assign_5_return :
      forall (S0 : state (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (rv' : resvalue (* input *)) (v : value (* input *)),
        (* ========================================== *)
        (* ------------------------------------------ *)
        (red_expr S0 C (expr_assign_5 v (out_ter S (rv' : res))) (out_ter S ((resvalue_value v) : res)))

  | red_expr_binary_op_coma :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (v1 : value (* input *)) (v2 : value (* input *)),
        (* ========================================== *)
        (* ------------------------------------------ *)
        (red_expr S C (expr_binary_op_3 binary_op_coma v1 v2) (out_ter S ((resvalue_value v2) : res)))

  | red_spec_returns :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (o : out (* input *)),
        (* ========================================== *)
        (* ------------------------------------------ *)
        (red_expr S C (spec_returns o) o)

  | red_spec_prim_new_object_bool :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (b : bool (* input *)),
        (* ========================================== *)
        (* ------------------------------------------ *)
        (red_expr S C (spec_prim_new_object (prim_bool b)) (out_ter ((snd ((object_alloc S ((object_with_primitive_value ((object_new prealloc_bool_proto (("Boolean")%string)) : object) b) : object)) : (object_loc * state))) : state) ((fst ((object_alloc S ((object_with_primitive_value ((object_new prealloc_bool_proto (("Boolean")%string)) : object) b) : object)) : (object_loc * state))) : res)))

  | red_spec_prim_new_object_number :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (n : number (* input *)),
        (* ========================================== *)
        (* ------------------------------------------ *)
        (red_expr S C (spec_prim_new_object (prim_number n)) (out_ter ((snd ((object_alloc S ((object_with_primitive_value ((object_new prealloc_number_proto (("Number")%string)) : object) n) : object)) : (object_loc * state))) : state) ((fst ((object_alloc S ((object_with_primitive_value ((object_new prealloc_number_proto (("Number")%string)) : object) n) : object)) : (object_loc * state))) : res)))

  | red_spec_prim_new_object_string :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (s : string (* input *)),
        (* ========================================== *)
        (* ------------------------------------------ *)
        (red_expr S C (spec_prim_new_object (prim_string s)) (out_ter ((snd ((object_alloc S ((object_with_primitive_value ((object_with_get_own_property ((object_new prealloc_string_proto (("String")%string)) : object) builtin_get_own_prop_string) : object) s) : object)) : (object_loc * state))) : state) ((fst ((object_alloc S ((object_with_primitive_value ((object_with_get_own_property ((object_new prealloc_string_proto (("String")%string)) : object) builtin_get_own_prop_string) : object) s) : object)) : (object_loc * state))) : res)))

  | red_spec_to_primitive_pref_prim :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (w : prim (* input *)) (prefo : (option preftype) (* input *)),
        (* ========================================== *)
        (* ------------------------------------------ *)
        (red_expr S C (spec_to_primitive (value_prim w) prefo) (out_ter S ((resvalue_value (value_prim w)) : res)))

  | red_spec_to_primitive_pref_object :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (l : object_loc (* input *)) (prefo : (option preftype) (* input *)) (o : out),
        (* ========================================== *)
        (red_expr S C (spec_object_default_value l prefo) o) ->
        (* ------------------------------------------ *)
        (red_expr S C (spec_to_primitive (value_object l) prefo) o)

  | red_spec_to_boolean :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (v : value (* input *)),
        (* ========================================== *)
        (* ------------------------------------------ *)
        (red_expr S C (spec_to_boolean v) (out_ter S ((resvalue_value (value_prim (prim_bool (((convert_value_to_boolean v) : provide_this_flag) : bool)))) : res)))

  | red_spec_to_number_prim :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (w : prim (* input *)),
        (* ========================================== *)
        (* ------------------------------------------ *)
        (red_expr S C (spec_to_number (value_prim w)) (out_ter S ((resvalue_value (value_prim (prim_number (convert_prim_to_number w)))) : res)))

  | red_spec_to_number_object :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (l : object_loc (* input *)) (o1 : out) (o : out),
        (* ========================================== *)
        (red_expr S C (spec_to_primitive (value_object l) ((Some preftype_number) : (option preftype))) o1) ->
        (red_expr S C (spec_to_number_1 o1) o) ->
        (* ------------------------------------------ *)
        (red_expr S C (spec_to_number (value_object l)) o)

  | red_spec_to_number_1 :
      forall (S0 : state (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (w : prim (* input *)),
        (* ========================================== *)
        (* ------------------------------------------ *)
        (red_expr S0 C (spec_to_number_1 (out_ter S ((resvalue_value (value_prim w)) : res))) (out_ter S ((resvalue_value (value_prim (prim_number (convert_prim_to_number w)))) : res)))

  | red_spec_to_integer :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (v : value (* input *)) (o1 : out) (o : out),
        (* ========================================== *)
        (red_expr S C (spec_to_number v) o1) ->
        (red_expr S C (spec_to_integer_1 o1) o) ->
        (* ------------------------------------------ *)
        (red_expr S C (spec_to_integer v) o)

  | red_spec_to_integer_1 :
      forall (S0 : state (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (n : number (* input *)),
        (* ========================================== *)
        (* ------------------------------------------ *)
        (red_expr S0 C (spec_to_integer_1 (out_ter S ((resvalue_value (value_prim (prim_number n))) : res))) (out_ter S ((resvalue_value (value_prim (prim_number (convert_number_to_integer n)))) : res)))

  | red_spec_to_string_prim :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (w : prim (* input *)),
        (* ========================================== *)
        (* ------------------------------------------ *)
        (red_expr S C (spec_to_string (value_prim w)) (out_ter S ((resvalue_value (value_prim (prim_string ((convert_prim_to_string w) : string)))) : res)))

  | red_spec_to_string_object :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (l : object_loc (* input *)) (o1 : out) (o : out),
        (* ========================================== *)
        (red_expr S C (spec_to_primitive (value_object l) ((Some preftype_string) : (option preftype))) o1) ->
        (red_expr S C (spec_to_string_1 o1) o) ->
        (* ------------------------------------------ *)
        (red_expr S C (spec_to_string (value_object l)) o)

  | red_spec_to_string_1 :
      forall (S0 : state (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (w : prim (* input *)),
        (* ========================================== *)
        (* ------------------------------------------ *)
        (red_expr S0 C (spec_to_string_1 (out_ter S ((resvalue_value (value_prim w)) : res))) (out_ter S ((resvalue_value (value_prim (prim_string ((convert_prim_to_string w) : string)))) : res)))

  | red_spec_to_object_undef_or_null :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (v : value (* input *)) (o : out),
        ((v = prim_undef) \/ (v = prim_null)) ->
        (* ========================================== *)
        (red_expr S C (spec_error native_error_type) o) ->
        (* ------------------------------------------ *)
        (red_expr S C (spec_to_object v) o)

  | red_spec_to_object_prim :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (w : prim (* input *)) (o : out),
        ((w = prim_undef) \/ (w = prim_null)) ->
        (* ========================================== *)
        (red_expr S C (spec_prim_new_object w) o) ->
        (* ------------------------------------------ *)
        (red_expr S C (spec_to_object (value_prim w)) o)

  | red_spec_to_object_object :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (l : object_loc (* input *)),
        (* ========================================== *)
        (* ------------------------------------------ *)
        (red_expr S C (spec_to_object (value_object l)) (out_ter S ((resvalue_value (value_object l)) : res)))

  | red_spec_check_object_coercible_undef_or_null :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (v : value (* input *)) (o : out),
        ((v = prim_undef) \/ (v = prim_null)) ->
        (* ========================================== *)
        (red_expr S C (spec_error native_error_type) o) ->
        (* ------------------------------------------ *)
        (red_expr S C (spec_check_object_coercible v) o)

  | red_spec_check_object_coercible_return :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (v : value (* input *)),
        ((v = prim_undef) \/ (v = prim_null)) ->
        (* ========================================== *)
        (* ------------------------------------------ *)
        (red_expr S C (spec_check_object_coercible v) (out_void S))

  | red_spec_object_get :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (l : object_loc (* input *)) (x : prop_name (* input *)) (B : builtin_get) (o : out),
        (object_method object_get_ S l B) ->
        (* ========================================== *)
        (red_expr S C (spec_object_get_1 B (value_object l) l x) o) ->
        (* ------------------------------------------ *)
        (red_expr S C (spec_object_get (value_object l) x) o)

  | red_spec_object_put :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (l : object_loc (* input *)) (x : prop_name (* input *)) (v : value (* input *)) (throw : bool (* input *)) (B : builtin_put) (o : out),
        (object_method object_put_ S l B) ->
        (* ========================================== *)
        (red_expr S C (spec_object_put_1 B (value_object l) l x v throw) o) ->
        (* ------------------------------------------ *)
        (red_expr S C (spec_object_put (value_object l) x v throw) o)

  | red_spec_object_can_put :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (l : object_loc (* input *)) (x : prop_name (* input *)) (B : builtin_can_put) (o : out),
        (object_method object_can_put_ S l B) ->
        (* ========================================== *)
        (red_expr S C (spec_object_can_put_1 B l x) o) ->
        (* ------------------------------------------ *)
        (red_expr S C (spec_object_can_put l x) o)

  | red_spec_object_has_prop :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (l : object_loc (* input *)) (x : prop_name (* input *)) (B : builtin_has_prop) (o : out),
        (object_method object_has_prop_ S l B) ->
        (* ========================================== *)
        (red_expr S C (spec_object_has_prop_1 B l x) o) ->
        (* ------------------------------------------ *)
        (red_expr S C (spec_object_has_prop l x) o)

  | red_spec_object_delete :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (l : object_loc (* input *)) (x : prop_name (* input *)) (throw : bool (* input *)) (B : builtin_delete) (o : out),
        (object_method object_delete_ S l B) ->
        (* ========================================== *)
        (red_expr S C (spec_object_delete_1 B l x throw) o) ->
        (* ------------------------------------------ *)
        (red_expr S C (spec_object_delete l x throw) o)

  | red_spec_object_default_value :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (l : object_loc (* input *)) (prefo : (option preftype) (* input *)) (B : builtin_default_value) (o : out),
        (object_method object_default_value_ S l B) ->
        (* ========================================== *)
        (red_expr S C (spec_object_default_value_1 B l prefo) o) ->
        (* ------------------------------------------ *)
        (red_expr S C (spec_object_default_value l prefo) o)

  | red_spec_object_define_own_prop :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (l : object_loc (* input *)) (x : prop_name (* input *)) (Desc : descriptor (* input *)) (throw : bool (* input *)) (B : builtin_define_own_prop) (o : out),
        (object_method object_define_own_prop_ S l B) ->
        (* ========================================== *)
        (red_expr S C (spec_object_define_own_prop_1 B l x Desc throw) o) ->
        (* ------------------------------------------ *)
        (red_expr S C (spec_object_define_own_prop l x Desc throw) o)

  | red_spec_object_has_instance :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (l : object_loc (* input *)) (v : value (* input *)) (B : builtin_has_instance) (o : out),
        (object_method object_has_instance_ S l (Some B)) ->
        (* ========================================== *)
        (red_expr S C (spec_object_has_instance_1 B l v) o) ->
        (* ------------------------------------------ *)
        (red_expr S C (spec_object_has_instance l v) o)

  | red_spec_call :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (l : object_loc (* input *)) (B : call) (this : value (* input *)) (args : (list value) (* input *)) (o : out),
        (object_method object_call_ S l (Some B)) ->
        (* ========================================== *)
        (red_expr S C (spec_call_1 B l this args) o) ->
        (* ------------------------------------------ *)
        (red_expr S C (spec_call l this args) o)

  | red_spec_constructor :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (l : object_loc (* input *)) (B : construct) (args : (list value) (* input *)) (o : out),
        (object_method object_construct_ S l (Some B)) ->
        (* ========================================== *)
        (red_expr S C (spec_construct_1 B l args) o) ->
        (* ------------------------------------------ *)
        (red_expr S C (spec_construct l args) o)

  | red_spec_call_1_prealloc :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (B : prealloc (* input *)) (lo : object_loc (* input *)) (this : value (* input *)) (args : (list value) (* input *)) (o : out),
        (* ========================================== *)
        (red_expr S C (spec_call_prealloc B this args) o) ->
        (* ------------------------------------------ *)
        (red_expr S C (spec_call_1 (call_prealloc B) lo this args) o)

  | red_spec_construct_1_prealloc :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (B : prealloc (* input *)) (l : object_loc (* input *)) (args : (list value) (* input *)) (o : out),
        (* ========================================== *)
        (red_expr S C (spec_construct_prealloc B args) o) ->
        (* ------------------------------------------ *)
        (red_expr S C (spec_construct_1 (construct_prealloc B) l args) o)

  | red_spec_object_get_1_default :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (vthis : value (* input *)) (l : object_loc (* input *)) (x : prop_name (* input *)) (y1 : (specret full_descriptor)) (o : out),
        (* ========================================== *)
        (red_spec S C (spec_object_get_prop l x) y1) ->
        (red_expr S C (spec_object_get_2 vthis y1) o) ->
        (* ------------------------------------------ *)
        (red_expr S C (spec_object_get_1 builtin_get_default vthis l x) o)

  | red_spec_object_get_2_undef :
      forall (S0 : state (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (vthis : value (* input *)),
        (* ========================================== *)
        (* ------------------------------------------ *)
        (red_expr S0 C (spec_object_get_2 vthis ((specret_val S full_descriptor_undef) : (specret full_descriptor))) (out_ter S ((resvalue_value undef) : res)))

  | red_spec_object_get_2_data :
      forall (S0 : state (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (vthis : value (* input *)) (Ad : attributes_data (* input *)),
        (* ========================================== *)
        (* ------------------------------------------ *)
        (red_expr S0 C (spec_object_get_2 vthis ((specret_val S (full_descriptor_some (attributes_data_of Ad))) : (specret full_descriptor))) (out_ter S ((resvalue_value (attributes_data_value Ad)) : res)))

  | red_spec_object_get_2_accessor :
      forall (S0 : state (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (vthis : value (* input *)) (Aa : attributes_accessor (* input *)) (o : out),
        (* ========================================== *)
        (red_expr S C (spec_object_get_3 vthis (attributes_accessor_get Aa)) o) ->
        (* ------------------------------------------ *)
        (red_expr S0 C (spec_object_get_2 vthis ((specret_val S (full_descriptor_some (attributes_accessor_of Aa))) : (specret full_descriptor))) o)

  | red_spec_object_get_3_accessor_undef :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (vthis : value (* input *)),
        (* ========================================== *)
        (* ------------------------------------------ *)
        (red_expr S C (spec_object_get_3 vthis undef) (out_ter S ((resvalue_value undef) : res)))

  | red_spec_object_get_3_accessor_object :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (vthis : value (* input *)) (lf : object_loc (* input *)) (o : out),
        (* ========================================== *)
        (red_expr S C (spec_call lf vthis (nil : (list value))) o) ->
        (* ------------------------------------------ *)
        (red_expr S C (spec_object_get_3 vthis (value_object lf)) o)

  | red_spec_object_can_put_1_default :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (l : object_loc (* input *)) (x : prop_name (* input *)) (o : out) (y : (specret full_descriptor)),
        (* ========================================== *)
        (red_spec S C (spec_object_get_own_prop l x) y) ->
        (red_expr S C (spec_object_can_put_2 l x y) o) ->
        (* ------------------------------------------ *)
        (red_expr S C (spec_object_can_put_1 builtin_can_put_default l x) o)

  | red_spec_object_can_put_2_accessor :
      forall (S0 : state (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (l : object_loc (* input *)) (x : prop_name (* input *)) (Aa : attributes_accessor (* input *)),
        (* ========================================== *)
        (* ------------------------------------------ *)
        (red_expr S C (spec_object_can_put_2 l x ((specret_val S0 (full_descriptor_some (attributes_accessor_of Aa))) : (specret full_descriptor))) (out_ter S0 ((resvalue_value (value_prim (prim_bool (((ifb ((attributes_accessor_set Aa) = undef) then false else true) : provide_this_flag) : bool)))) : res)))

  | red_spec_object_can_put_2_data :
      forall (S0 : state (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (l : object_loc (* input *)) (x : prop_name (* input *)) (Ad : attributes_data (* input *)),
        (* ========================================== *)
        (* ------------------------------------------ *)
        (red_expr S C (spec_object_can_put_2 l x ((specret_val S0 (full_descriptor_some (attributes_data_of Ad))) : (specret full_descriptor))) (out_ter S0 ((resvalue_value (value_prim (prim_bool (((attributes_data_writable Ad) : provide_this_flag) : bool)))) : res)))

  | red_spec_object_can_put_2_undef :
      forall (S0 : state (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (l : object_loc (* input *)) (x : prop_name (* input *)) (o : out) (lproto : value),
        (object_proto S l lproto) ->
        (* ========================================== *)
        (red_expr S C (spec_object_can_put_4 l x lproto) o) ->
        (* ------------------------------------------ *)
        (red_expr S0 C (spec_object_can_put_2 l x ((specret_val S full_descriptor_undef) : (specret full_descriptor))) o)

  | red_spec_object_can_put_4_null :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (l : object_loc (* input *)) (x : prop_name (* input *)) (b : bool),
        (object_extensible S l b) ->
        (* ========================================== *)
        (* ------------------------------------------ *)
        (red_expr S C (spec_object_can_put_4 l x null) (out_ter S ((resvalue_value (value_prim (prim_bool ((b : provide_this_flag) : bool)))) : res)))

  | red_spec_object_can_put_4_not_null :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (l : object_loc (* input *)) (x : prop_name (* input *)) (lproto : object_loc (* input *)) (y1 : (specret full_descriptor)) (o : out),
        (* ========================================== *)
        (red_spec S C (spec_object_get_prop lproto x) y1) ->
        (red_expr S C (spec_object_can_put_5 l y1) o) ->
        (* ------------------------------------------ *)
        (red_expr S C (spec_object_can_put_4 l x (value_object lproto)) o)

  | red_spec_object_can_put_5_undef :
      forall (S0 : state (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (l : object_loc (* input *)) (b : bool),
        (object_extensible S l b) ->
        (* ========================================== *)
        (* ------------------------------------------ *)
        (red_expr S0 C (spec_object_can_put_5 l ((specret_val S full_descriptor_undef) : (specret full_descriptor))) (out_ter S ((resvalue_value (value_prim (prim_bool ((b : provide_this_flag) : bool)))) : res)))

  | red_spec_object_can_put_5_accessor :
      forall (S0 : state (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (l : object_loc (* input *)) (Aa : attributes_accessor (* input *)),
        (* ========================================== *)
        (* ------------------------------------------ *)
        (red_expr S0 C (spec_object_can_put_5 l ((specret_val S (full_descriptor_some (attributes_accessor_of Aa))) : (specret full_descriptor))) (out_ter S ((resvalue_value (value_prim (prim_bool (((ifb ((attributes_accessor_set Aa) = undef) then false else true) : provide_this_flag) : bool)))) : res)))

  | red_spec_object_can_put_5_data :
      forall (S0 : state (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (l : object_loc (* input *)) (Ad : attributes_data (* input *)) (bext : bool) (o : out),
        (object_extensible S l bext) ->
        (* ========================================== *)
        (red_expr S C (spec_object_can_put_6 Ad bext) o) ->
        (* ------------------------------------------ *)
        (red_expr S0 C (spec_object_can_put_5 l ((specret_val S (full_descriptor_some (attributes_data_of Ad))) : (specret full_descriptor))) o)

  | red_spec_object_can_put_6_extens_false :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (Ad : attributes_data (* input *)),
        (* ========================================== *)
        (* ------------------------------------------ *)
        (red_expr S C (spec_object_can_put_6 Ad false) (out_ter S ((resvalue_value (value_prim (prim_bool ((false : provide_this_flag) : bool)))) : res)))

  | red_spec_object_can_put_6_extens_true :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (Ad : attributes_data (* input *)),
        (* ========================================== *)
        (* ------------------------------------------ *)
        (red_expr S C (spec_object_can_put_6 Ad true) (out_ter S ((resvalue_value (value_prim (prim_bool (((attributes_data_writable Ad) : provide_this_flag) : bool)))) : res)))

  | red_spec_object_put_1_default :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (vthis : value (* input *)) (l : object_loc (* input *)) (x : prop_name (* input *)) (v : value (* input *)) (throw : bool (* input *)) (o1 : out) (o : out),
        (* ========================================== *)
        (red_expr S C (spec_object_can_put l x) o1) ->
        (red_expr S C (spec_object_put_2 vthis l x v throw o1) o) ->
        (* ------------------------------------------ *)
        (red_expr S C (spec_object_put_1 builtin_put_default vthis l x v throw) o)

  | red_spec_object_put_2_false :
      forall (S0 : state (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (vthis : value (* input *)) (l : object_loc (* input *)) (x : prop_name (* input *)) (v : value (* input *)) (throw : bool (* input *)) (o : out),
        (* ========================================== *)
        (red_expr S C (spec_error_or_void throw native_error_type) o) ->
        (* ------------------------------------------ *)
        (red_expr S0 C (spec_object_put_2 vthis l x v throw (out_ter S ((resvalue_value (value_prim (prim_bool ((false : provide_this_flag) : bool)))) : res))) o)

  | red_spec_object_put_2_true :
      forall (S0 : state (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (vthis : value (* input *)) (l : object_loc (* input *)) (x : prop_name (* input *)) (v : value (* input *)) (throw : bool (* input *)) (o : out) (y : (specret full_descriptor)),
        (* ========================================== *)
        (red_spec S C (spec_object_get_own_prop l x) y) ->
        (red_expr S C (spec_object_put_3 vthis l x v throw y) o) ->
        (* ------------------------------------------ *)
        (red_expr S0 C (spec_object_put_2 vthis l x v throw (out_ter S ((resvalue_value (value_prim (prim_bool ((true : provide_this_flag) : bool)))) : res))) o)

  | red_spec_object_put_3_data_object :
      forall (S0 : state (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (lthis : object_loc (* input *)) (l : object_loc (* input *)) (x : prop_name (* input *)) (v : value (* input *)) (throw : bool (* input *)) (Ad : attributes_data (* input *)) (o1 : out) (o : out),
        (* ========================================== *)
        (red_expr S C (spec_object_define_own_prop l x (descriptor_intro ((Some v) : (option value)) (None : (option bool)) (None : (option value)) (None : (option value)) (None : (option bool)) (None : (option bool))) throw) o1) ->
        (red_expr S C (spec_object_put_5 o1) o) ->
        (* ------------------------------------------ *)
        (red_expr S0 C (spec_object_put_3 (value_object lthis) l x v throw ((specret_val S (full_descriptor_some (attributes_data_of Ad))) : (specret full_descriptor))) o)

  | red_spec_object_put_3_data_prim :
      forall (S0 : state (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (wthis : prim (* input *)) (l : object_loc (* input *)) (x : prop_name (* input *)) (v : value (* input *)) (throw : bool (* input *)) (Ad : attributes_data (* input *)) (o : out),
        (* ========================================== *)
        (red_expr S C (spec_error_or_void throw native_error_type) o) ->
        (* ------------------------------------------ *)
        (red_expr S0 C (spec_object_put_3 (value_prim wthis) l x v throw ((specret_val S (full_descriptor_some (attributes_data_of Ad))) : (specret full_descriptor))) o)

  | red_spec_object_put_3_not_data :
      forall (S0 : state (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (vthis : value (* input *)) (l : object_loc (* input *)) (x : prop_name (* input *)) (v : value (* input *)) (throw : bool (* input *)) (Aa : attributes_accessor) (y1 : (specret full_descriptor)) (o : out) (D : full_descriptor (* input *)),
        ((D = full_descriptor_undef) \/ (D = (attributes_accessor_of Aa))) ->
        (* ========================================== *)
        (red_spec S C (spec_object_get_prop l x) y1) ->
        (red_expr S C (spec_object_put_4 vthis l x v throw y1) o) ->
        (* ------------------------------------------ *)
        (red_expr S0 C (spec_object_put_3 vthis l x v throw ((specret_val S D) : (specret full_descriptor))) o)

  | red_spec_object_put_4_accessor :
      forall (S0 : state (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (vsetter : value) (lfsetter : object_loc) (vthis : value (* input *)) (l : object_loc (* input *)) (x : prop_name (* input *)) (v : value (* input *)) (throw : bool (* input *)) (Aa : attributes_accessor (* input *)) (o1 : out) (o : out),
        (vsetter = (attributes_accessor_set Aa)) ->
        (vsetter <> undef) ->
        (vsetter = (value_object lfsetter)) ->
        (* ========================================== *)
        (red_expr S C (spec_call lfsetter vthis (v :: (nil : (list value)))) o1) ->
        (red_expr S C (spec_object_put_5 o1) o) ->
        (* ------------------------------------------ *)
        (red_expr S0 C (spec_object_put_4 vthis l x v throw ((specret_val S (full_descriptor_some (attributes_accessor_of Aa))) : (specret full_descriptor))) o)

  | red_spec_object_put_4_not_accessor_object :
      forall (S0 : state (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (D : full_descriptor (* input *)) (lthis : object_loc (* input *)) (l : object_loc (* input *)) (x : prop_name (* input *)) (v : value (* input *)) (throw : bool (* input *)) (Ad : attributes_data) (o1 : out) (o : out),
        ((D = full_descriptor_undef) \/ (D = (attributes_data_of Ad))) ->
        (* ========================================== *)
        (red_expr S C (spec_object_define_own_prop l x ((descriptor_intro_data v true true true) : descriptor) throw) o1) ->
        (red_expr S C (spec_object_put_5 o1) o) ->
        (* ------------------------------------------ *)
        (red_expr S0 C (spec_object_put_4 (value_object lthis) l x v throw ((specret_val S D) : (specret full_descriptor))) o)

  | red_spec_object_put_4_not_accessor_prim :
      forall (S0 : state (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (wthis : prim (* input *)) (D : full_descriptor (* input *)) (l : object_loc (* input *)) (x : prop_name (* input *)) (v : value (* input *)) (throw : bool (* input *)) (Ad : attributes_data) (o : out),
        ((D = full_descriptor_undef) \/ (D = (attributes_data_of Ad))) ->
        (* ========================================== *)
        (red_expr S C (spec_error_or_void throw native_error_type) o) ->
        (* ------------------------------------------ *)
        (red_expr S0 C (spec_object_put_4 (value_prim wthis) l x v throw ((specret_val S D) : (specret full_descriptor))) o)

  | red_spec_object_put_5_return :
      forall (S0 : state (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (rv : resvalue (* input *)),
        (* ========================================== *)
        (* ------------------------------------------ *)
        (red_expr S0 C (spec_object_put_5 (out_ter S (rv : res))) (out_void S))

  | red_spec_object_has_prop_1_default :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (l : object_loc (* input *)) (x : prop_name (* input *)) (y1 : (specret full_descriptor)) (o : out),
        (* ========================================== *)
        (red_spec S C (spec_object_get_prop l x) y1) ->
        (red_expr S C (spec_object_has_prop_2 y1) o) ->
        (* ------------------------------------------ *)
        (red_expr S C (spec_object_has_prop_1 builtin_has_prop_default l x) o)

  | red_spec_object_has_prop_2 :
      forall (S0 : state (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (D : full_descriptor (* input *)),
        (* ========================================== *)
        (* ------------------------------------------ *)
        (red_expr S0 C (spec_object_has_prop_2 ((specret_val S D) : (specret full_descriptor))) (out_ter S ((resvalue_value (value_prim (prim_bool (((ifb (D = full_descriptor_undef) then false else true) : provide_this_flag) : bool)))) : res)))

  | red_spec_object_delete_1_default :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (l : object_loc (* input *)) (x : prop_name (* input *)) (throw : bool (* input *)) (o : out) (y : (specret full_descriptor)),
        (* ========================================== *)
        (red_spec S C (spec_object_get_own_prop l x) y) ->
        (red_expr S C (spec_object_delete_2 l x throw y) o) ->
        (* ------------------------------------------ *)
        (red_expr S C (spec_object_delete_1 builtin_delete_default l x throw) o)

  | red_spec_object_delete_2_undef :
      forall (S0 : state (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (l : object_loc (* input *)) (x : prop_name (* input *)) (throw : bool (* input *)),
        (* ========================================== *)
        (* ------------------------------------------ *)
        (red_expr S0 C (spec_object_delete_2 l x throw ((specret_val S full_descriptor_undef) : (specret full_descriptor))) (out_ter S ((resvalue_value (value_prim (prim_bool ((true : provide_this_flag) : bool)))) : res)))

  | red_spec_object_delete_2_some_configurable :
      forall (S0 : state (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (l : object_loc (* input *)) (x : prop_name (* input *)) (throw : bool (* input *)) (A : attributes (* input *)) (S' : state),
        ((attributes_configurable A) = true) ->
        (object_rem_property S l x S') ->
        (* ========================================== *)
        (* ------------------------------------------ *)
        (red_expr S0 C (spec_object_delete_2 l x throw ((specret_val S (full_descriptor_some A)) : (specret full_descriptor))) (out_ter S' ((resvalue_value (value_prim (prim_bool ((true : provide_this_flag) : bool)))) : res)))

  | red_spec_object_delete_3_some_non_configurable :
      forall (S0 : state (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (l : object_loc (* input *)) (x : prop_name (* input *)) (throw : bool (* input *)) (A : attributes (* input *)) (o : out),
        ((attributes_configurable A) = false) ->
        (* ========================================== *)
        (red_expr S C (spec_error_or_cst throw native_error_type (value_prim (prim_bool ((false : provide_this_flag) : bool)))) o) ->
        (* ------------------------------------------ *)
        (red_expr S0 C (spec_object_delete_2 l x throw ((specret_val S (full_descriptor_some A)) : (specret full_descriptor))) o)

  | red_spec_object_default_value_1_default :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (l : object_loc (* input *)) (prefo : (option preftype) (* input *)) (o : out),
        (* ========================================== *)
        (red_expr S C (spec_object_default_value_2 l ((unsome_default preftype_number prefo) : preftype) ((other_preftypes ((unsome_default preftype_number prefo) : preftype)) : preftype)) o) ->
        (* ------------------------------------------ *)
        (red_expr S C (spec_object_default_value_1 builtin_default_value_default l prefo) o)

  | red_spec_object_default_value_2 :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (l : object_loc (* input *)) (pref1 : preftype (* input *)) (pref2 : preftype (* input *)) (o : out),
        (* ========================================== *)
        (red_expr S C (spec_object_default_value_sub_1 l ((method_of_preftype pref1) : string) (spec_object_default_value_3 l pref2)) o) ->
        (* ------------------------------------------ *)
        (red_expr S C (spec_object_default_value_2 l pref1 pref2) o)

  | red_spec_object_default_value_3 :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (l : object_loc (* input *)) (pref2 : preftype (* input *)) (o : out),
        (* ========================================== *)
        (red_expr S C (spec_object_default_value_sub_1 l ((method_of_preftype pref2) : string) spec_object_default_value_4) o) ->
        (* ------------------------------------------ *)
        (red_expr S C (spec_object_default_value_3 l pref2) o)

  | red_spec_object_default_value_4 :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (o : out),
        (* ========================================== *)
        (red_expr S C (spec_error native_error_type) o) ->
        (* ------------------------------------------ *)
        (red_expr S C spec_object_default_value_4 o)

  | red_spec_object_default_value_sub_1 :
      forall (o1 : out) (S : state (* input *)) (C : execution_ctx (* input *)) (l : object_loc (* input *)) (x : prop_name (* input *)) (K : ext_expr (* input *)) (o : out),
        (* ========================================== *)
        (red_expr S C (spec_object_get (value_object l) x) o1) ->
        (red_expr S C (spec_object_default_value_sub_2 l o1 K) o) ->
        (* ------------------------------------------ *)
        (red_expr S C (spec_object_default_value_sub_1 l (x : string) K) o)

  | red_spec_object_default_value_sub_2_not_callable :
      forall (S0 : state (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (l : object_loc (* input *)) (v : value (* input *)) (K : ext_expr (* input *)) (o : out),
        (callable S v None) ->
        (* ========================================== *)
        (red_expr S C K o) ->
        (* ------------------------------------------ *)
        (red_expr S0 C (spec_object_default_value_sub_2 l (out_ter S ((resvalue_value v) : res)) K) o)

  | red_spec_object_default_value_sub_2_callable :
      forall (S0 : state (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (lfunc : object_loc) (l : object_loc (* input *)) (K : ext_expr (* input *)) (o : out) (B : _) (o1 : out),
        (callable S (value_object lfunc) (Some B)) ->
        (* ========================================== *)
        (red_expr S C (spec_call lfunc (value_object l) (nil : (list value))) o1) ->
        (red_expr S C (spec_object_default_value_sub_3 o1 K) o) ->
        (* ------------------------------------------ *)
        (red_expr S0 C (spec_object_default_value_sub_2 l (out_ter S ((resvalue_value (value_object lfunc)) : res)) K) o)

  | red_spec_object_default_value_sub_3_prim :
      forall (S0 : state (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (K : ext_expr (* input *)) (w : prim (* input *)),
        (* ========================================== *)
        (* ------------------------------------------ *)
        (red_expr S0 C (spec_object_default_value_sub_3 (out_ter S ((resvalue_value (value_prim w)) : res)) K) (out_ter S ((resvalue_value (value_prim w)) : res)))

  | red_spec_object_default_value_sub_3_object :
      forall (S0 : state (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (l : object_loc (* input *)) (K : ext_expr (* input *)) (o : out),
        (* ========================================== *)
        (red_expr S C K o) ->
        (* ------------------------------------------ *)
        (red_expr S0 C (spec_object_default_value_sub_3 (out_ter S ((resvalue_value (value_object l)) : res)) K) o)

  | red_spec_object_define_own_prop_1_default :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (l : object_loc (* input *)) (x : prop_name (* input *)) (Desc : descriptor (* input *)) (throw : bool (* input *)) (o : out) (y : (specret full_descriptor)),
        (* ========================================== *)
        (red_spec S C (spec_object_get_own_prop l x) y) ->
        (red_expr S C (spec_object_define_own_prop_2 l x Desc throw y) o) ->
        (* ------------------------------------------ *)
        (red_expr S C (spec_object_define_own_prop_1 builtin_define_own_prop_default l x Desc throw) o)

  | red_spec_object_define_own_prop_2 :
      forall (S0 : state (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (l : object_loc (* input *)) (x : prop_name (* input *)) (Desc : descriptor (* input *)) (throw : bool (* input *)) (An : full_descriptor (* input *)) (bext : bool) (o : out),
        (object_extensible S l bext) ->
        (* ========================================== *)
        (red_expr S C (spec_object_define_own_prop_3 l x Desc throw An bext) o) ->
        (* ------------------------------------------ *)
        (red_expr S0 C (spec_object_define_own_prop_2 l x Desc throw ((specret_val S An) : (specret full_descriptor))) o)

  | red_spec_object_define_own_prop_3_undef_false :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (l : object_loc (* input *)) (x : prop_name (* input *)) (Desc : descriptor (* input *)) (throw : bool (* input *)) (o : out),
        (* ========================================== *)
        (red_expr S C (spec_object_define_own_prop_reject throw) o) ->
        (* ------------------------------------------ *)
        (red_expr S C (spec_object_define_own_prop_3 l x Desc throw full_descriptor_undef false) o)

  | red_spec_object_define_own_prop_3_undef_true :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (l : object_loc (* input *)) (x : prop_name (* input *)) (Desc : descriptor (* input *)) (throw : bool (* input *)) (S' : state),
        (object_set_property S l x (ifb ((descriptor_is_generic Desc) \/ (descriptor_is_data Desc)) then (attributes_data_of (attributes_data_of_descriptor Desc)) else (attributes_accessor_of (attributes_accessor_of_descriptor Desc))) S') ->
        (* ========================================== *)
        (* ------------------------------------------ *)
        (red_expr S C (spec_object_define_own_prop_3 l x Desc throw full_descriptor_undef true) (out_ter S' ((resvalue_value (value_prim (prim_bool ((true : provide_this_flag) : bool)))) : res)))

  | red_spec_object_define_own_prop_3_includes :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (l : object_loc (* input *)) (x : prop_name (* input *)) (A : attributes (* input *)) (Desc : descriptor (* input *)) (throw : bool (* input *)) (bext : bool (* input *)),
        (descriptor_contains A Desc) ->
        (* ========================================== *)
        (* ------------------------------------------ *)
        (red_expr S C (spec_object_define_own_prop_3 l x Desc throw (full_descriptor_some A) bext) (out_ter S ((resvalue_value (value_prim (prim_bool ((true : provide_this_flag) : bool)))) : res)))

  | red_spec_object_define_own_prop_3_not_include :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (l : object_loc (* input *)) (x : prop_name (* input *)) (A : attributes (* input *)) (Desc : descriptor (* input *)) (throw : bool (* input *)) (o : out) (bext : bool (* input *)),
        (descriptor_contains A Desc) ->
        (* ========================================== *)
        (red_expr S C (spec_object_define_own_prop_4 l x A Desc throw) o) ->
        (* ------------------------------------------ *)
        (red_expr S C (spec_object_define_own_prop_3 l x Desc throw (full_descriptor_some A) bext) o)

  | red_spec_object_define_own_prop_4_reject :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (l : object_loc (* input *)) (x : prop_name (* input *)) (A : attributes (* input *)) (Desc : descriptor (* input *)) (throw : bool (* input *)) (o : out),
        (attributes_change_enumerable_on_non_configurable A Desc) ->
        (* ========================================== *)
        (red_expr S C (spec_object_define_own_prop_reject throw) o) ->
        (* ------------------------------------------ *)
        (red_expr S C (spec_object_define_own_prop_4 l x A Desc throw) o)

  | red_spec_object_define_own_prop_4_not_reject :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (l : object_loc (* input *)) (x : prop_name (* input *)) (A : attributes (* input *)) (Desc : descriptor (* input *)) (throw : bool (* input *)) (o : out),
        (attributes_change_enumerable_on_non_configurable A Desc) ->
        (* ========================================== *)
        (red_expr S C (spec_object_define_own_prop_5 l x A Desc throw) o) ->
        (* ------------------------------------------ *)
        (red_expr S C (spec_object_define_own_prop_4 l x A Desc throw) o)

  | red_spec_object_define_own_prop_5_generic :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (l : object_loc (* input *)) (x : prop_name (* input *)) (A : attributes (* input *)) (Desc : descriptor (* input *)) (throw : bool (* input *)) (o : out),
        (descriptor_is_generic Desc) ->
        (* ========================================== *)
        (red_expr S C (spec_object_define_own_prop_write l x A Desc throw) o) ->
        (* ------------------------------------------ *)
        (red_expr S C (spec_object_define_own_prop_5 l x A Desc throw) o)

  | red_spec_object_define_own_prop_5_a :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (l : object_loc (* input *)) (x : prop_name (* input *)) (A : attributes (* input *)) (Desc : descriptor (* input *)) (throw : bool (* input *)) (o : out),
        ((attributes_is_data A) <> (descriptor_is_data Desc)) ->
        (* ========================================== *)
        (red_expr S C (spec_object_define_own_prop_6a l x A Desc throw) o) ->
        (* ------------------------------------------ *)
        (red_expr S C (spec_object_define_own_prop_5 l x A Desc throw) o)

  | red_spec_object_define_own_prop_6a_reject :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (l : object_loc (* input *)) (x : prop_name (* input *)) (A : attributes (* input *)) (Desc : descriptor (* input *)) (throw : bool (* input *)) (o : out),
        ((attributes_configurable A) = false) ->
        (* ========================================== *)
        (red_expr S C (spec_object_define_own_prop_reject throw) o) ->
        (* ------------------------------------------ *)
        (red_expr S C (spec_object_define_own_prop_6a l x A Desc throw) o)

  | red_spec_object_define_own_prop_6a_accept :
      forall (S : state (* input *)) (S' : state) (C : execution_ctx (* input *)) (l : object_loc (* input *)) (x : prop_name (* input *)) (A : attributes (* input *)) (Desc : descriptor (* input *)) (throw : bool (* input *)) (o : out),
        ((attributes_configurable A) = true) ->
        (object_set_property S l x match A with (attributes_data_of Ad) => (attributes_accessor_of_attributes_data (Ad : attributes_data)) | (attributes_accessor_of Aa) => (attributes_data_of_attributes_accessor (Aa : attributes_accessor)) end S') ->
        (* ========================================== *)
        (red_expr S' C (spec_object_define_own_prop_write l x match A with (attributes_data_of Ad) => (attributes_accessor_of_attributes_data (Ad : attributes_data)) | (attributes_accessor_of Aa) => (attributes_data_of_attributes_accessor (Aa : attributes_accessor)) end Desc throw) o) ->
        (* ------------------------------------------ *)
        (red_expr S C (spec_object_define_own_prop_6a l x A Desc throw) o)

  | red_spec_object_define_own_prop_5_b :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (l : object_loc (* input *)) (x : prop_name (* input *)) (Ad : attributes_data (* input *)) (Desc : descriptor (* input *)) (throw : bool (* input *)) (o : out),
        (descriptor_is_data Desc) ->
        (* ========================================== *)
        (red_expr S C (spec_object_define_own_prop_6b l x (attributes_data_of Ad) Desc throw) o) ->
        (* ------------------------------------------ *)
        (red_expr S C (spec_object_define_own_prop_5 l x (attributes_data_of Ad) Desc throw) o)

  | red_spec_object_define_own_prop_6b_false_reject :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (l : object_loc (* input *)) (x : prop_name (* input *)) (Ad : attributes_data (* input *)) (Desc : descriptor (* input *)) (throw : bool (* input *)) (o : out),
        (attributes_change_data_on_non_configurable Ad Desc) ->
        (* ========================================== *)
        (red_expr S C (spec_object_define_own_prop_reject throw) o) ->
        (* ------------------------------------------ *)
        (red_expr S C (spec_object_define_own_prop_6b l x (attributes_data_of Ad) Desc throw) o)

  | red_spec_object_define_own_prop_6b_false_accept :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (l : object_loc (* input *)) (x : prop_name (* input *)) (Ad : attributes_data (* input *)) (Desc : descriptor (* input *)) (throw : bool (* input *)) (o : out),
        (attributes_change_data_on_non_configurable Ad Desc) ->
        (* ========================================== *)
        (red_expr S C (spec_object_define_own_prop_write l x (attributes_data_of Ad) Desc throw) o) ->
        (* ------------------------------------------ *)
        (red_expr S C (spec_object_define_own_prop_6b l x (attributes_data_of Ad) Desc throw) o)

  | red_spec_object_define_own_prop_5_c :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (l : object_loc (* input *)) (x : prop_name (* input *)) (Aa : attributes_accessor (* input *)) (Desc : descriptor (* input *)) (throw : bool (* input *)) (o : out),
        (descriptor_is_accessor Desc) ->
        (* ========================================== *)
        (red_expr S C (spec_object_define_own_prop_6c l x (attributes_accessor_of Aa) Desc throw) o) ->
        (* ------------------------------------------ *)
        (red_expr S C (spec_object_define_own_prop_5 l x (attributes_accessor_of Aa) Desc throw) o)

  | red_spec_object_define_own_prop_6c_1 :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (l : object_loc (* input *)) (x : prop_name (* input *)) (Aa : attributes_accessor (* input *)) (Desc : descriptor (* input *)) (throw : bool (* input *)) (o : out),
        (attributes_change_accessor_on_non_configurable Aa Desc) ->
        (* ========================================== *)
        (red_expr S C (spec_object_define_own_prop_reject throw) o) ->
        (* ------------------------------------------ *)
        (red_expr S C (spec_object_define_own_prop_6c l x (attributes_accessor_of Aa) Desc throw) o)

  | red_spec_object_define_own_prop_6c_2 :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (l : object_loc (* input *)) (x : prop_name (* input *)) (Aa : attributes_accessor (* input *)) (Desc : descriptor (* input *)) (throw : bool (* input *)) (o : out),
        (attributes_change_accessor_on_non_configurable Aa Desc) ->
        (* ========================================== *)
        (red_expr S C (spec_object_define_own_prop_write l x (attributes_accessor_of Aa) Desc throw) o) ->
        (* ------------------------------------------ *)
        (red_expr S C (spec_object_define_own_prop_6c l x (attributes_accessor_of Aa) Desc throw) o)

  | red_spec_object_define_own_prop_write :
      forall (S : state (* input *)) (S' : state) (C : execution_ctx (* input *)) (l : object_loc (* input *)) (x : prop_name (* input *)) (A : attributes (* input *)) (Desc : descriptor (* input *)) (throw : bool (* input *)),
        (object_set_property S l x (attributes_update A Desc) S') ->
        (* ========================================== *)
        (* ------------------------------------------ *)
        (red_expr S C (spec_object_define_own_prop_write l x A Desc throw) (out_ter S' ((resvalue_value (value_prim (prim_bool ((true : provide_this_flag) : bool)))) : res)))

  | red_spec_object_define_own_prop_reject :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (throw : bool (* input *)) (o : out),
        (* ========================================== *)
        (red_expr S C (spec_error_or_cst throw native_error_type (value_prim (prim_bool ((false : provide_this_flag) : bool)))) o) ->
        (* ------------------------------------------ *)
        (red_expr S C (spec_object_define_own_prop_reject throw) o)

  | red_spec_prim_value_get :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (v : value (* input *)) (x : prop_name (* input *)) (o1 : out) (o : out),
        (* ========================================== *)
        (red_expr S C (spec_to_object v) o1) ->
        (red_expr S C (spec_prim_value_get_1 v x o1) o) ->
        (* ------------------------------------------ *)
        (red_expr S C (spec_prim_value_get v x) o)

  | red_spec_prim_value_get_1 :
      forall (S0 : state (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (v : value (* input *)) (x : prop_name (* input *)) (l : object_loc (* input *)) (o : out),
        (* ========================================== *)
        (red_expr S C (spec_object_get_1 builtin_get_default v l x) o) ->
        (* ------------------------------------------ *)
        (red_expr S0 C (spec_prim_value_get_1 v x (out_ter S ((resvalue_value (value_object l)) : res))) o)

  | red_spec_ref_put_value_value :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (v : value (* input *)) (vnew : value (* input *)) (o : out),
        (* ========================================== *)
        (red_expr S C (spec_error native_error_ref) o) ->
        (* ------------------------------------------ *)
        (red_expr S C (spec_put_value (resvalue_value v) vnew) o)

  | red_spec_ref_put_value_ref_a_1 :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (r : ref (* input *)) (vnew : value (* input *)) (o : out),
        (ref_is_unresolvable r) ->
        ((ref_strict r) = true) ->
        (* ========================================== *)
        (red_expr S C (spec_error native_error_ref) o) ->
        (* ------------------------------------------ *)
        (red_expr S C (spec_put_value (resvalue_ref r) vnew) o)

  | red_spec_ref_put_value_ref_a_2 :
      forall (o : out) (S : state (* input *)) (C : execution_ctx (* input *)) (r : ref (* input *)) (vnew : value (* input *)),
        (ref_is_unresolvable r) ->
        ((ref_strict r) = false) ->
        (* ========================================== *)
        (red_expr S C (spec_object_put (value_object (object_loc_prealloc prealloc_global)) (ref_name r) vnew (throw_false : bool)) o) ->
        (* ------------------------------------------ *)
        (red_expr S C (spec_put_value (resvalue_ref r) vnew) o)

  | red_spec_ref_put_value_ref_b :
      forall (v : value) (ext_put : (value -> (prop_name -> (value -> (bool -> ext_expr))))) (S : state (* input *)) (C : execution_ctx (* input *)) (r : ref (* input *)) (vnew : value (* input *)) (o : out),
        (ref_is_property r) ->
        ((ref_base r) = (ref_base_type_value v)) ->
        (ext_put = (ifb (ref_has_primitive_base r) then spec_prim_value_put else spec_object_put)) ->
        (* ========================================== *)
        (red_expr S C (ext_put v (ref_name r) vnew (ref_strict r)) o) ->
        (* ------------------------------------------ *)
        (red_expr S C (spec_put_value (resvalue_ref r) vnew) o)

  | red_spec_ref_put_value_ref_c :
      forall (L : env_loc) (S : state (* input *)) (C : execution_ctx (* input *)) (r : ref (* input *)) (vnew : value (* input *)) (o : out),
        ((ref_base r) = (ref_base_type_env_loc L)) ->
        (* ========================================== *)
        (red_expr S C (spec_env_record_set_mutable_binding L (ref_name r) vnew (ref_strict r)) o) ->
        (* ------------------------------------------ *)
        (red_expr S C (spec_put_value (resvalue_ref r) vnew) o)

  | red_spec_prim_value_put :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (w : prim (* input *)) (x : prop_name (* input *)) (v : value (* input *)) (throw : bool (* input *)) (o1 : out) (o : out),
        (* ========================================== *)
        (red_expr S C (spec_to_object (value_prim w)) o1) ->
        (red_expr S C (spec_prim_value_put_1 w x v throw o1) o) ->
        (* ------------------------------------------ *)
        (red_expr S C (spec_prim_value_put (value_prim w) x v throw) o)

  | red_spec_prim_value_put_1 :
      forall (S0 : state (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (w : prim (* input *)) (x : prop_name (* input *)) (v : value (* input *)) (throw : bool (* input *)) (l : object_loc (* input *)) (o : out),
        (* ========================================== *)
        (red_expr S C (spec_object_put_1 builtin_put_default (value_prim w) l x v throw) o) ->
        (* ------------------------------------------ *)
        (red_expr S0 C (spec_prim_value_put_1 w x v throw (out_ter S ((resvalue_value (value_object l)) : res))) o)

  | red_spec_env_record_has_binding :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (L : env_loc (* input *)) (x : prop_name (* input *)) (o : out) (E : env_record),
        (env_record_binds S L E) ->
        (* ========================================== *)
        (red_expr S C (spec_env_record_has_binding_1 L x E) o) ->
        (* ------------------------------------------ *)
        (red_expr S C (spec_env_record_has_binding L x) o)

  | red_spec_env_record_has_binding_1_decl :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (L : env_loc (* input *)) (x : prop_name (* input *)) (Ed : decl_env_record (* input *)),
        (* ========================================== *)
        (* ------------------------------------------ *)
        (red_expr S C (spec_env_record_has_binding_1 L x (env_record_decl Ed)) (out_ter S ((resvalue_value (value_prim (prim_bool (((ifb (decl_env_record_indom Ed (x : string)) then true else false) : provide_this_flag) : bool)))) : res)))

  | red_spec_env_record_has_binding_1_object :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (L : env_loc (* input *)) (x : prop_name (* input *)) (l : object_loc (* input *)) (pt : provide_this_flag (* input *)) (o : out),
        (* ========================================== *)
        (red_expr S C (spec_object_has_prop l x) o) ->
        (* ------------------------------------------ *)
        (red_expr S C (spec_env_record_has_binding_1 L x (env_record_object l pt)) o)

  | red_spec_env_record_create_mutable_binding :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (L : env_loc (* input *)) (x : prop_name (* input *)) (deletable_opt : (option bool) (* input *)) (o : out) (E : env_record),
        (env_record_binds S L E) ->
        (* ========================================== *)
        (red_expr S C (spec_env_record_create_mutable_binding_1 L x ((unsome_default false deletable_opt) : bool) E) o) ->
        (* ------------------------------------------ *)
        (red_expr S C (spec_env_record_create_mutable_binding L x deletable_opt) o)

  | red_spec_env_record_create_mutable_binding_1_decl_indom :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (L : env_loc (* input *)) (x : prop_name (* input *)) (deletable : bool (* input *)) (Ed : decl_env_record (* input *)),
        (decl_env_record_indom Ed (x : string)) ->
        (* ========================================== *)
        (* ------------------------------------------ *)
        (red_expr S C (spec_env_record_create_mutable_binding_1 L x deletable (env_record_decl Ed)) (out_void ((env_record_write_decl_env S L x (mutability_of_bool deletable) undef) : state)))

  | red_spec_env_record_create_mutable_binding_1_object :
      forall (o1 : out) (S : state (* input *)) (C : execution_ctx (* input *)) (L : env_loc (* input *)) (x : prop_name (* input *)) (deletable : bool (* input *)) (l : object_loc (* input *)) (pt : provide_this_flag (* input *)) (o : out),
        (* ========================================== *)
        (red_expr S C (spec_object_has_prop l x) o1) ->
        (red_expr S C (spec_env_record_create_mutable_binding_2 L x deletable l o1) o) ->
        (* ------------------------------------------ *)
        (red_expr S C (spec_env_record_create_mutable_binding_1 L x deletable (env_record_object l pt)) o)

  | red_spec_env_record_create_mutable_binding_obj_2 :
      forall (S0 : state (* input *)) (C : execution_ctx (* input *)) (L : env_loc (* input *)) (x : prop_name (* input *)) (deletable : bool (* input *)) (l : object_loc (* input *)) (S : state (* input *)) (o1 : out) (o : out),
        (* ========================================== *)
        (red_expr S C (spec_object_define_own_prop l x (descriptor_of_attributes (attributes_data_of (attributes_data_intro undef true true deletable))) (throw_true : bool)) o1) ->
        (red_expr S C (spec_env_record_create_mutable_binding_3 o1) o) ->
        (* ------------------------------------------ *)
        (red_expr S0 C (spec_env_record_create_mutable_binding_2 L x deletable l (out_ter S ((resvalue_value (value_prim (prim_bool ((false : provide_this_flag) : bool)))) : res))) o)

  | red_spec_env_record_create_mutable_binding_obj_3 :
      forall (S0 : state (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (rv : resvalue (* input *)),
        (* ========================================== *)
        (* ------------------------------------------ *)
        (red_expr S0 C (spec_env_record_create_mutable_binding_3 (out_ter S (rv : res))) (out_void S))

  | red_spec_env_record_set_mutable_binding :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (L : env_loc (* input *)) (x : prop_name (* input *)) (v : value (* input *)) (str : strictness_flag (* input *)) (o : out) (E : env_record),
        (env_record_binds S L E) ->
        (* ========================================== *)
        (red_expr S C (spec_env_record_set_mutable_binding_1 L x v (str : bool) E) o) ->
        (* ------------------------------------------ *)
        (red_expr S C (spec_env_record_set_mutable_binding L x v (str : bool)) o)

  | red_spec_env_record_set_mutable_binding_1_decl_mutable :
      forall (v_old : value) (mu : mutability) (S : state (* input *)) (C : execution_ctx (* input *)) (L : env_loc (* input *)) (x : prop_name (* input *)) (v : value (* input *)) (str : strictness_flag (* input *)) (Ed : decl_env_record (* input *)) (o : out),
        (decl_env_record_binds Ed (x : string) mu v_old) ->
        (mutability_is_mutable mu) ->
        (* ========================================== *)
        (red_expr S C (spec_returns (out_void ((env_record_write_decl_env S L x mu v) : state))) o) ->
        (* ------------------------------------------ *)
        (red_expr S C (spec_env_record_set_mutable_binding_1 L x v (str : bool) (env_record_decl Ed)) o)

  | red_spec_env_record_set_mutable_binding_1_decl_non_mutable :
      forall (v_old : value) (mu : mutability) (S : state (* input *)) (C : execution_ctx (* input *)) (L : env_loc (* input *)) (x : prop_name (* input *)) (v : value (* input *)) (str : strictness_flag (* input *)) (Ed : decl_env_record (* input *)) (o : out),
        (decl_env_record_binds Ed (x : string) mu v_old) ->
        (mutability_is_mutable mu) ->
        (* ========================================== *)
        (red_expr S C (spec_error_or_void (str : bool) native_error_type) o) ->
        (* ------------------------------------------ *)
        (red_expr S C (spec_env_record_set_mutable_binding_1 L x v (str : bool) (env_record_decl Ed)) o)

  | red_spec_env_record_set_mutable_binding_1_object :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (L : env_loc (* input *)) (x : prop_name (* input *)) (v : value (* input *)) (str : strictness_flag (* input *)) (l : object_loc (* input *)) (pt : provide_this_flag (* input *)) (o : out),
        (* ========================================== *)
        (red_expr S C (spec_object_put (value_object l) x v (str : bool)) o) ->
        (* ------------------------------------------ *)
        (red_expr S C (spec_env_record_set_mutable_binding_1 L x v (str : bool) (env_record_object l pt)) o)

  | red_spec_env_record_get_binding_value :
      forall (E : env_record) (S : state (* input *)) (C : execution_ctx (* input *)) (L : env_loc (* input *)) (x : prop_name (* input *)) (str : strictness_flag (* input *)) (o : out),
        (env_record_binds S L E) ->
        (* ========================================== *)
        (red_expr S C (spec_env_record_get_binding_value_1 L x (str : bool) E) o) ->
        (* ------------------------------------------ *)
        (red_expr S C (spec_env_record_get_binding_value L x (str : bool)) o)

  | red_spec_env_record_get_binding_value_1_decl_uninitialized :
      forall (mu : mutability) (v : value) (S : state (* input *)) (C : execution_ctx (* input *)) (L : env_loc (* input *)) (x : prop_name (* input *)) (str : strictness_flag (* input *)) (Ed : decl_env_record (* input *)) (o : out),
        (decl_env_record_binds Ed (x : string) mu v) ->
        (* ========================================== *)
        (red_expr S C (spec_error_or_cst (str : bool) native_error_ref undef) o) ->
        (* ------------------------------------------ *)
        (red_expr S C (spec_env_record_get_binding_value_1 L x (str : bool) (env_record_decl Ed)) o)

  | red_spec_env_record_get_binding_value_1_decl_initialized :
      forall (mu : mutability) (v : value) (S : state (* input *)) (C : execution_ctx (* input *)) (L : env_loc (* input *)) (x : prop_name (* input *)) (str : strictness_flag (* input *)) (Ed : decl_env_record (* input *)) (o : out),
        (decl_env_record_binds Ed (x : string) mu v) ->
        (mu <> mutability_uninitialized_immutable) ->
        (* ========================================== *)
        (red_expr S C (spec_returns (out_ter S ((resvalue_value v) : res))) o) ->
        (* ------------------------------------------ *)
        (red_expr S C (spec_env_record_get_binding_value_1 L x (str : bool) (env_record_decl Ed)) o)

  | red_spec_env_record_get_binding_value_1_object :
      forall (o1 : out) (S : state (* input *)) (C : execution_ctx (* input *)) (L : env_loc (* input *)) (x : prop_name (* input *)) (str : strictness_flag (* input *)) (l : object_loc (* input *)) (pt : provide_this_flag (* input *)) (o : out),
        (* ========================================== *)
        (red_expr S C (spec_object_has_prop l x) o1) ->
        (red_expr S C (spec_env_record_get_binding_value_2 x (str : bool) l o1) o) ->
        (* ------------------------------------------ *)
        (red_expr S C (spec_env_record_get_binding_value_1 L x (str : bool) (env_record_object l pt)) o)

  | red_spec_env_record_get_binding_value_obj_2_false :
      forall (S0 : state (* input *)) (C : execution_ctx (* input *)) (x : prop_name (* input *)) (str : strictness_flag (* input *)) (l : object_loc (* input *)) (S : state (* input *)) (o : out),
        (* ========================================== *)
        (red_expr S C (spec_error_or_cst (str : bool) native_error_ref undef) o) ->
        (* ------------------------------------------ *)
        (red_expr S0 C (spec_env_record_get_binding_value_2 x (str : bool) l (out_ter S ((resvalue_value (value_prim (prim_bool ((false : provide_this_flag) : bool)))) : res))) o)

  | red_spec_env_record_get_binding_value_obj_2_true :
      forall (S0 : state (* input *)) (C : execution_ctx (* input *)) (x : prop_name (* input *)) (str : strictness_flag (* input *)) (l : object_loc (* input *)) (S : state (* input *)) (o : out),
        (* ========================================== *)
        (red_expr S C (spec_object_get (value_object l) x) o) ->
        (* ------------------------------------------ *)
        (red_expr S0 C (spec_env_record_get_binding_value_2 x (str : bool) l (out_ter S ((resvalue_value (value_prim (prim_bool ((true : provide_this_flag) : bool)))) : res))) o)

  | red_spec_env_record_delete_binding :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (L : env_loc (* input *)) (x : prop_name (* input *)) (o : out) (E : env_record),
        (env_record_binds S L E) ->
        (* ========================================== *)
        (red_expr S C (spec_env_record_delete_binding_1 L x E) o) ->
        (* ------------------------------------------ *)
        (red_expr S C (spec_env_record_delete_binding L x) o)

  | red_spec_env_record_delete_binding_1_decl_indom :
      forall (mu : mutability) (v : value) (S : state (* input *)) (C : execution_ctx (* input *)) (L : env_loc (* input *)) (x : prop_name (* input *)) (Ed : decl_env_record (* input *)) (S' : state) (b : bool),
        (decl_env_record_binds Ed (x : string) mu v) ->
        (ifb (mu = mutability_deletable) then ((S' = (env_record_write S L (decl_env_record_rem Ed x))) /\ (b = true)) else ((S' = S) /\ (b = false))) ->
        (* ========================================== *)
        (* ------------------------------------------ *)
        (red_expr S C (spec_env_record_delete_binding_1 L x (env_record_decl Ed)) (out_ter S' ((resvalue_value (value_prim (prim_bool ((b : provide_this_flag) : bool)))) : res)))

  | red_spec_env_record_delete_binding_1_decl_not_indom :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (L : env_loc (* input *)) (x : prop_name (* input *)) (Ed : decl_env_record (* input *)),
        (decl_env_record_indom Ed (x : string)) ->
        (* ========================================== *)
        (* ------------------------------------------ *)
        (red_expr S C (spec_env_record_delete_binding_1 L x (env_record_decl Ed)) (out_ter S ((resvalue_value (value_prim (prim_bool ((true : provide_this_flag) : bool)))) : res)))

  | red_spec_env_record_delete_binding_1_object :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (L : env_loc (* input *)) (x : prop_name (* input *)) (l : object_loc (* input *)) (pt : provide_this_flag (* input *)) (o : out),
        (* ========================================== *)
        (red_expr S C (spec_object_delete l x (throw_false : bool)) o) ->
        (* ------------------------------------------ *)
        (red_expr S C (spec_env_record_delete_binding_1 L x (env_record_object l pt)) o)

  | red_spec_env_record_implicit_this_value :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (L : env_loc (* input *)) (o : out) (E : env_record),
        (env_record_binds S L E) ->
        (* ========================================== *)
        (red_expr S C (spec_env_record_implicit_this_value_1 L E) o) ->
        (* ------------------------------------------ *)
        (red_expr S C (spec_env_record_implicit_this_value L) o)

  | red_spec_env_record_implicit_this_value_1_decl :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (L : env_loc (* input *)) (Ed : decl_env_record (* input *)),
        (* ========================================== *)
        (* ------------------------------------------ *)
        (red_expr S C (spec_env_record_implicit_this_value_1 L (env_record_decl Ed)) (out_ter S ((resvalue_value undef) : res)))

  | red_spec_env_record_implicit_this_value_1_object :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (L : env_loc (* input *)) (l : object_loc (* input *)) (pt : bool (* input *)),
        (* ========================================== *)
        (* ------------------------------------------ *)
        (red_expr S C (spec_env_record_implicit_this_value_1 L (env_record_object l (pt : provide_this_flag))) (out_ter S ((resvalue_value (ifb pt then (value_object l) else undef)) : res)))

  | red_spec_env_record_create_immutable_binding :
      forall (Ed : decl_env_record) (S : state (* input *)) (C : execution_ctx (* input *)) (L : env_loc (* input *)) (x : prop_name (* input *)),
        (env_record_binds S L (env_record_decl Ed)) ->
        (decl_env_record_indom Ed (x : string)) ->
        (* ========================================== *)
        (* ------------------------------------------ *)
        (red_expr S C (spec_env_record_create_immutable_binding L x) (out_void ((env_record_write_decl_env S L x mutability_uninitialized_immutable undef) : state)))

  | red_spec_env_record_initialize_immutable_binding :
      forall (Ed : decl_env_record) (v_old : value) (S : state (* input *)) (C : execution_ctx (* input *)) (L : env_loc (* input *)) (x : prop_name (* input *)) (v : value (* input *)),
        (env_record_binds S L (env_record_decl Ed)) ->
        (decl_env_record_binds Ed (x : string) mutability_uninitialized_immutable v_old) ->
        (* ========================================== *)
        (* ------------------------------------------ *)
        (red_expr S C (spec_env_record_initialize_immutable_binding L x v) (out_void ((env_record_write_decl_env S L x mutability_immutable v) : state)))

  | red_spec_env_record_create_set_mutable_binding :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (L : env_loc (* input *)) (x : prop_name (* input *)) (deletable_opt : (option bool) (* input *)) (v : value (* input *)) (str : strictness_flag (* input *)) (o : out) (o1 : out),
        (* ========================================== *)
        (red_expr S C (spec_env_record_create_mutable_binding L x deletable_opt) o1) ->
        (red_expr S C (spec_env_record_create_set_mutable_binding_1 o1 L x v (str : bool)) o) ->
        (* ------------------------------------------ *)
        (red_expr S C (spec_env_record_create_set_mutable_binding L x deletable_opt v (str : bool)) o)

  | red_spec_env_record_create_set_mutable_binding_1 :
      forall (S : state (* input *)) (S0 : state (* input *)) (C : execution_ctx (* input *)) (L : env_loc (* input *)) (x : prop_name (* input *)) (v : value (* input *)) (str : strictness_flag (* input *)) (o : out),
        (* ========================================== *)
        (red_expr S C (spec_env_record_set_mutable_binding L x v (str : bool)) o) ->
        (* ------------------------------------------ *)
        (red_expr S0 C (spec_env_record_create_set_mutable_binding_1 (out_ter S (res_intro restype_normal resvalue_empty label_empty)) L x v (str : bool)) o)

  | red_spec_entering_eval_code :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (bdirect : bool (* input *)) (bd : funcbody (* input *)) (K : ext_expr (* input *)) (o : out),
        (* ========================================== *)
        (red_expr S (ifb bdirect then C else (execution_ctx_initial ((((((funcbody_is_strict bd) : bool) || (bdirect && (execution_ctx_strict C))) : provide_this_flag) : bool) : strictness_flag))) (spec_entering_eval_code_1 bd K (((((((funcbody_is_strict bd) : bool) || (bdirect && (execution_ctx_strict C))) : provide_this_flag) : bool) : strictness_flag) : bool)) o) ->
        (* ------------------------------------------ *)
        (red_expr S C (spec_entering_eval_code bdirect bd K) o)

  | red_spec_entering_eval_code_1 :
      forall (str : bool (* input *)) (lex : lexical_env) (S' : state) (o1 : out) (S : state (* input *)) (C : execution_ctx (* input *)) (bd : funcbody (* input *)) (K : ext_expr (* input *)) (o : out),
        ((lex, S') = (ifb str then ((lexical_env_alloc_decl S (execution_ctx_lexical_env C)) : (lexical_env * state)) else ((execution_ctx_lexical_env C), S))) ->
        (* ========================================== *)
        (red_expr S' (ifb str then (execution_ctx_with_lex_same C lex) else C) (spec_binding_inst codetype_eval (None : (option object_loc)) ((funcbody_prog bd) : prog) (nil : (list value))) o1) ->
        (red_expr S' (ifb str then (execution_ctx_with_lex_same C lex) else C) (spec_entering_eval_code_2 o1 K) o) ->
        (* ------------------------------------------ *)
        (red_expr S C (spec_entering_eval_code_1 bd K (str : bool)) o)

  | red_spec_entering_eval_code_2 :
      forall (S0 : state (* input *)) (C : execution_ctx (* input *)) (S : state (* input *)) (K : ext_expr (* input *)) (o : out),
        (* ========================================== *)
        (red_expr S C K o) ->
        (* ------------------------------------------ *)
        (red_expr S0 C (spec_entering_eval_code_2 (out_ter S (res_intro restype_normal resvalue_empty label_empty)) K) o)

  | red_spec_entering_func_code :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (lf : object_loc (* input *)) (vthis : value (* input *)) (args : (list value) (* input *)) (bd : funcbody) (K : ext_expr (* input *)) (o : out),
        (object_method object_code_ S lf (Some bd)) ->
        (* ========================================== *)
        (red_expr S C (spec_entering_func_code_1 lf args bd vthis ((funcbody_is_strict bd) : strictness_flag) K) o) ->
        (* ------------------------------------------ *)
        (red_expr S C (spec_entering_func_code lf vthis args K) o)

  | red_spec_entering_func_code_1_strict :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (lf : object_loc (* input *)) (args : (list value) (* input *)) (bd : funcbody (* input *)) (vthis : value (* input *)) (K : ext_expr (* input *)) (o : out),
        (* ========================================== *)
        (red_expr S C (spec_entering_func_code_3 lf args (((true : provide_this_flag) : bool) : strictness_flag) bd vthis K) o) ->
        (* ------------------------------------------ *)
        (red_expr S C (spec_entering_func_code_1 lf args bd vthis (((true : provide_this_flag) : bool) : strictness_flag) K) o)

  | red_spec_entering_func_code_1_null_or_undef :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (lf : object_loc (* input *)) (args : (list value) (* input *)) (bd : funcbody (* input *)) (vthis : value (* input *)) (K : ext_expr (* input *)) (o : out),
        ((vthis = null) \/ (vthis = undef)) ->
        (* ========================================== *)
        (red_expr S C (spec_entering_func_code_3 lf args (((false : provide_this_flag) : bool) : strictness_flag) bd (value_object (object_loc_prealloc prealloc_global)) K) o) ->
        (* ------------------------------------------ *)
        (red_expr S C (spec_entering_func_code_1 lf args bd vthis (((false : provide_this_flag) : bool) : strictness_flag) K) o)

  | red_spec_entering_func_code_1_not_object :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (lf : object_loc (* input *)) (args : (list value) (* input *)) (bd : funcbody (* input *)) (vthis : value (* input *)) (o1 : out) (K : ext_expr (* input *)) (o : out),
        (((vthis <> null) /\ (vthis <> undef)) /\ ((type_of vthis) <> type_object)) ->
        (* ========================================== *)
        (red_expr S C (spec_to_object vthis) o1) ->
        (red_expr S C (spec_entering_func_code_2 lf args bd o1 K) o) ->
        (* ------------------------------------------ *)
        (red_expr S C (spec_entering_func_code_1 lf args bd vthis (((false : provide_this_flag) : bool) : strictness_flag) K) o)

  | red_spec_entering_func_code_2 :
      forall (S : state (* input *)) (S0 : state (* input *)) (C : execution_ctx (* input *)) (lf : object_loc (* input *)) (args : (list value) (* input *)) (bd : funcbody (* input *)) (vthis : value (* input *)) (K : ext_expr (* input *)) (o : out),
        (* ========================================== *)
        (red_expr S C (spec_entering_func_code_3 lf args strictness_false bd vthis K) o) ->
        (* ------------------------------------------ *)
        (red_expr S0 C (spec_entering_func_code_2 lf args bd (out_ter S ((resvalue_value vthis) : res)) K) o)

  | red_spec_entering_func_code_1_object :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (lf : object_loc (* input *)) (args : (list value) (* input *)) (bd : funcbody (* input *)) (lthis : object_loc (* input *)) (K : ext_expr (* input *)) (o : out),
        (* ========================================== *)
        (red_expr S C (spec_entering_func_code_3 lf args strictness_false bd (value_object lthis) K) o) ->
        (* ------------------------------------------ *)
        (red_expr S C (spec_entering_func_code_1 lf args bd (value_object lthis) (((false : provide_this_flag) : bool) : strictness_flag) K) o)

  | red_spec_entering_func_code_3 :
      forall (o1 : out) (S : state (* input *)) (C : execution_ctx (* input *)) (lf : object_loc (* input *)) (args : (list value) (* input *)) (str : strictness_flag (* input *)) (bd : funcbody (* input *)) (vthis : value (* input *)) (lex : _) (K : ext_expr (* input *)) (o : out),
        (object_method object_scope_ S lf (Some lex)) ->
        (* ========================================== *)
        (red_expr ((snd (lexical_env_alloc_decl S lex)) : state) (execution_ctx_intro_same ((fst (lexical_env_alloc_decl S lex)) : lexical_env) vthis str) (spec_binding_inst codetype_func ((Some lf) : (option object_loc)) ((funcbody_prog bd) : prog) args) o1) ->
        (red_expr ((snd (lexical_env_alloc_decl S lex)) : state) (execution_ctx_intro_same ((fst (lexical_env_alloc_decl S lex)) : lexical_env) vthis str) (spec_entering_func_code_4 o1 K) o) ->
        (* ------------------------------------------ *)
        (red_expr S C (spec_entering_func_code_3 lf args str bd vthis K) o)

  | red_spec_entering_func_code_4 :
      forall (S0 : state (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (K : ext_expr (* input *)) (o : out),
        (* ========================================== *)
        (red_expr S C K o) ->
        (* ------------------------------------------ *)
        (red_expr S0 C (spec_entering_func_code_4 (out_ter S (res_intro restype_normal resvalue_empty label_empty)) K) o)

  | red_spec_binding_inst_formal_params_empty :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (args : (list value) (* input *)) (L : env_loc (* input *)) (str : strictness_flag (* input *)),
        (* ========================================== *)
        (* ------------------------------------------ *)
        (red_expr S C (spec_binding_inst_formal_params args L (nil : (list string)) str) (out_void S))

  | red_spec_binding_inst_formal_params_non_empty :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (args : (list value) (* input *)) (L : env_loc (* input *)) (x : prop_name (* input *)) (xs : (list prop_name) (* input *)) (str : strictness_flag (* input *)) (o1 : out) (o : out),
        (* ========================================== *)
        (red_expr S C (spec_env_record_has_binding L x) o1) ->
        (red_expr S C (spec_binding_inst_formal_params_1 ((snd match args with nil => (undef, nil) | (v :: args') => (v, args') end) : (list value)) L (x : string) (xs : (list string)) str ((fst match args with nil => (undef, nil) | (v :: args') => (v, args') end) : value) o1) o) ->
        (* ------------------------------------------ *)
        (red_expr S C (spec_binding_inst_formal_params args L ((x :: xs) : (list string)) str) o)

  | red_spec_binding_inst_formal_params_1_not_declared :
      forall (S0 : state (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (args : (list value) (* input *)) (L : env_loc (* input *)) (x : prop_name (* input *)) (xs : (list prop_name) (* input *)) (str : strictness_flag (* input *)) (v : value (* input *)) (o : out) (o1 : out),
        (* ========================================== *)
        (red_expr S C (spec_env_record_create_mutable_binding L x (None : (option bool))) o1) ->
        (red_expr S C (spec_binding_inst_formal_params_2 args L (x : string) (xs : (list string)) str v o1) o) ->
        (* ------------------------------------------ *)
        (red_expr S0 C (spec_binding_inst_formal_params_1 args L (x : string) (xs : (list string)) str v (out_ter S ((resvalue_value (value_prim (prim_bool ((false : provide_this_flag) : bool)))) : res))) o)

  | red_spec_binding_inst_formal_params_2 :
      forall (S0 : state (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (args : (list value) (* input *)) (L : env_loc (* input *)) (x : prop_name (* input *)) (xs : (list prop_name) (* input *)) (str : strictness_flag (* input *)) (v : value (* input *)) (o : out),
        (* ========================================== *)
        (red_expr S C (spec_binding_inst_formal_params_3 args L (x : string) (xs : (list string)) str v) o) ->
        (* ------------------------------------------ *)
        (red_expr S0 C (spec_binding_inst_formal_params_2 args L (x : string) (xs : (list string)) str v (out_ter S (res_intro restype_normal resvalue_empty label_empty))) o)

  | red_spec_binding_inst_formal_params_1_declared :
      forall (S0 : state (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (args : (list value) (* input *)) (L : env_loc (* input *)) (x : prop_name (* input *)) (xs : (list prop_name) (* input *)) (str : strictness_flag (* input *)) (v : value (* input *)) (o : out),
        (* ========================================== *)
        (red_expr S C (spec_binding_inst_formal_params_3 args L (x : string) (xs : (list string)) str v) o) ->
        (* ------------------------------------------ *)
        (red_expr S0 C (spec_binding_inst_formal_params_1 args L (x : string) (xs : (list string)) str v (out_ter S ((resvalue_value (value_prim (prim_bool ((true : provide_this_flag) : bool)))) : res))) o)

  | red_spec_binding_inst_formal_params_3 :
      forall (o1 : out) (S : state (* input *)) (C : execution_ctx (* input *)) (args : (list value) (* input *)) (L : env_loc (* input *)) (x : prop_name (* input *)) (xs : (list prop_name) (* input *)) (str : strictness_flag (* input *)) (v : value (* input *)) (o : out),
        (* ========================================== *)
        (red_expr S C (spec_env_record_set_mutable_binding L x v (str : bool)) o1) ->
        (red_expr S C (spec_binding_inst_formal_params_4 args L (xs : (list string)) str o1) o) ->
        (* ------------------------------------------ *)
        (red_expr S C (spec_binding_inst_formal_params_3 args L (x : string) (xs : (list string)) str v) o)

  | red_spec_binding_inst_formal_params_4 :
      forall (S0 : state (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (args : (list value) (* input *)) (L : env_loc (* input *)) (xs : (list prop_name) (* input *)) (str : strictness_flag (* input *)) (o : out),
        (* ========================================== *)
        (red_expr S C (spec_binding_inst_formal_params args L (xs : (list string)) str) o) ->
        (* ------------------------------------------ *)
        (red_expr S0 C (spec_binding_inst_formal_params_4 args L (xs : (list string)) str (out_ter S (res_intro restype_normal resvalue_empty label_empty))) o)

  | red_spec_binding_inst_function_decls_nil :
      forall (L : env_loc (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (args : (list value) (* input *)) (str : strictness_flag (* input *)) (bconfig : bool (* input *)),
        (* ========================================== *)
        (* ------------------------------------------ *)
        (red_expr S C (spec_binding_inst_function_decls args L (nil : (list funcdecl)) str bconfig) (out_void S))

  | red_spec_binding_inst_function_decls_cons :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (L : env_loc (* input *)) (args : (list value) (* input *)) (fd : funcdecl (* input *)) (fds : (list funcdecl) (* input *)) (str : strictness_flag (* input *)) (bconfig : bool (* input *)) (o1 : out) (o : out),
        (* ========================================== *)
        (red_expr S C (spec_creating_function_object (funcdecl_parameters fd) (funcdecl_body fd) (execution_ctx_variable_env C) ((funcbody_is_strict (funcdecl_body fd)) : strictness_flag)) o1) ->
        (red_expr S C (spec_binding_inst_function_decls_1 args L fd fds str bconfig o1) o) ->
        (* ------------------------------------------ *)
        (red_expr S C (spec_binding_inst_function_decls args L (fd :: fds) str bconfig) o)

  | red_spec_binding_inst_function_decls_1 :
      forall (o1 : out) (L : env_loc (* input *)) (S0 : state (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (args : (list value) (* input *)) (fd : funcdecl (* input *)) (fds : (list funcdecl) (* input *)) (str : strictness_flag (* input *)) (fo : object_loc (* input *)) (bconfig : bool (* input *)) (o : out),
        (* ========================================== *)
        (red_expr S C (spec_env_record_has_binding L ((funcdecl_name fd) : prop_name)) o1) ->
        (red_expr S C (spec_binding_inst_function_decls_2 args L fd fds str fo bconfig o1) o) ->
        (* ------------------------------------------ *)
        (red_expr S0 C (spec_binding_inst_function_decls_1 args L fd fds str bconfig (out_ter S ((resvalue_value (value_object fo)) : res))) o)

  | red_spec_binding_inst_function_decls_2_false :
      forall (o1 : out) (L : env_loc (* input *)) (S0 : state (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (args : (list value) (* input *)) (fd : funcdecl (* input *)) (fds : (list funcdecl) (* input *)) (str : strictness_flag (* input *)) (fo : object_loc (* input *)) (bconfig : bool (* input *)) (o : out),
        (* ========================================== *)
        (red_expr S C (spec_env_record_create_mutable_binding L ((funcdecl_name fd) : prop_name) ((Some bconfig) : (option bool))) o1) ->
        (red_expr S C (spec_binding_inst_function_decls_4 args L fd fds str fo bconfig o1) o) ->
        (* ------------------------------------------ *)
        (red_expr S0 C (spec_binding_inst_function_decls_2 args L fd fds str fo bconfig (out_ter S ((resvalue_value (value_prim (prim_bool ((false : provide_this_flag) : bool)))) : res))) o)

  | red_spec_binding_inst_function_decls_2_true_global :
      forall (S0 : state (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (args : (list value) (* input *)) (fd : funcdecl (* input *)) (fds : (list funcdecl) (* input *)) (str : strictness_flag (* input *)) (fo : object_loc (* input *)) (bconfig : bool (* input *)) (y1 : (specret full_descriptor)) (o : out),
        (* ========================================== *)
        (red_spec S C (spec_object_get_prop (object_loc_prealloc prealloc_global) ((funcdecl_name fd) : prop_name)) y1) ->
        (red_expr S C (spec_binding_inst_function_decls_3 args fd fds str fo bconfig y1) o) ->
        (* ------------------------------------------ *)
        (red_expr S0 C (spec_binding_inst_function_decls_2 args env_loc_global_env_record fd fds str fo bconfig (out_ter S ((resvalue_value (value_prim (prim_bool ((true : provide_this_flag) : bool)))) : res))) o)

  | red_spec_binding_inst_function_decls_3_true :
      forall (S0 : state (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (args : (list value) (* input *)) (fd : funcdecl (* input *)) (fds : (list funcdecl) (* input *)) (str : strictness_flag (* input *)) (fo : object_loc (* input *)) (bconfig : bool (* input *)) (A : attributes (* input *)) (Anew : attributes_data) (o1 : out) (o : out),
        ((attributes_configurable A) = true) ->
        (Anew = (attributes_data_intro undef true true bconfig)) ->
        (* ========================================== *)
        (red_expr S C (spec_object_define_own_prop (object_loc_prealloc prealloc_global) ((funcdecl_name fd) : prop_name) (descriptor_of_attributes (attributes_data_of Anew)) true) o1) ->
        (red_expr S C (spec_binding_inst_function_decls_4 args env_loc_global_env_record fd fds str fo bconfig o1) o) ->
        (* ------------------------------------------ *)
        (red_expr S0 C (spec_binding_inst_function_decls_3 args fd fds str fo bconfig ((specret_val S (full_descriptor_some A)) : (specret full_descriptor))) o)

  | red_spec_binding_inst_function_decls_4 :
      forall (S0 : state (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (args : (list value) (* input *)) (L : env_loc (* input *)) (fd : funcdecl (* input *)) (fds : (list funcdecl) (* input *)) (str : strictness_flag (* input *)) (fo : object_loc (* input *)) (bconfig : bool (* input *)) (rv : resvalue (* input *)) (o : out),
        (* ========================================== *)
        (red_expr S C (spec_binding_inst_function_decls_5 args L fd fds str fo bconfig) o) ->
        (* ------------------------------------------ *)
        (red_expr S0 C (spec_binding_inst_function_decls_4 args L fd fds str fo bconfig (out_ter S (rv : res))) o)

  | red_spec_binding_inst_function_decls_3_false :
      forall (S0 : state (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (args : (list value) (* input *)) (fd : funcdecl (* input *)) (fds : (list funcdecl) (* input *)) (str : strictness_flag (* input *)) (fo : object_loc (* input *)) (A : attributes (* input *)) (bconfig : bool (* input *)) (o : out),
        ((attributes_configurable A) = false) ->
        (* ========================================== *)
        (red_expr S C (spec_binding_inst_function_decls_3a args fd fds str fo bconfig (full_descriptor_some A)) o) ->
        (* ------------------------------------------ *)
        (red_expr S0 C (spec_binding_inst_function_decls_3 args fd fds str fo bconfig ((specret_val S (full_descriptor_some A)) : (specret full_descriptor))) o)

  | red_spec_binding_inst_function_decls_3a_type_error :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (args : (list value) (* input *)) (fd : funcdecl (* input *)) (fds : (list funcdecl) (* input *)) (str : strictness_flag (* input *)) (fo : object_loc (* input *)) (A : attributes (* input *)) (bconfig : bool (* input *)) (o : out),
        (((descriptor_is_accessor A) \/ ((attributes_writable A) = false)) \/ ((attributes_enumerable A) = false)) ->
        (* ========================================== *)
        (red_expr S C (spec_error native_error_type) o) ->
        (* ------------------------------------------ *)
        (red_expr S C (spec_binding_inst_function_decls_3a args fd fds str fo bconfig (full_descriptor_some A)) o)

  | red_spec_binding_inst_function_decls_3a_no_error :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (args : (list value) (* input *)) (fd : funcdecl (* input *)) (fds : (list funcdecl) (* input *)) (str : strictness_flag (* input *)) (fo : object_loc (* input *)) (A : attributes (* input *)) (bconfig : bool (* input *)) (o : out),
        (((descriptor_is_accessor A) \/ ((attributes_writable A) = false)) \/ ((attributes_enumerable A) = false)) ->
        (* ========================================== *)
        (red_expr S C (spec_binding_inst_function_decls_5 args env_loc_global_env_record fd fds str fo bconfig) o) ->
        (* ------------------------------------------ *)
        (red_expr S C (spec_binding_inst_function_decls_3a args fd fds str fo bconfig (full_descriptor_some A)) o)

  | red_spec_binding_inst_function_decls_2_true :
      forall (L : env_loc (* input *)) (S0 : state (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (args : (list value) (* input *)) (fd : funcdecl (* input *)) (fds : (list funcdecl) (* input *)) (str : strictness_flag (* input *)) (fo : object_loc (* input *)) (bconfig : bool (* input *)) (o : out),
        (L <> env_loc_global_env_record) ->
        (* ========================================== *)
        (red_expr S C (spec_binding_inst_function_decls_5 args L fd fds str fo bconfig) o) ->
        (* ------------------------------------------ *)
        (red_expr S0 C (spec_binding_inst_function_decls_2 args L fd fds str fo bconfig (out_ter S ((resvalue_value (value_prim (prim_bool ((true : provide_this_flag) : bool)))) : res))) o)

  | red_spec_binding_inst_function_decls_5 :
      forall (o1 : out) (L : env_loc (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (args : (list value) (* input *)) (fd : funcdecl (* input *)) (fds : (list funcdecl) (* input *)) (str : strictness_flag (* input *)) (fo : object_loc (* input *)) (bconfig : bool (* input *)) (o : out),
        (* ========================================== *)
        (red_expr S C (spec_env_record_set_mutable_binding L ((funcdecl_name fd) : prop_name) (value_object fo) (str : bool)) o1) ->
        (red_expr S C (spec_binding_inst_function_decls_6 args L fds str bconfig o1) o) ->
        (* ------------------------------------------ *)
        (red_expr S C (spec_binding_inst_function_decls_5 args L fd fds str fo bconfig) o)

  | red_spec_binding_inst_function_decls_6 :
      forall (L : env_loc (* input *)) (S0 : state (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (args : (list value) (* input *)) (fds : (list funcdecl) (* input *)) (str : strictness_flag (* input *)) (bconfig : bool (* input *)) (o : out),
        (* ========================================== *)
        (red_expr S C (spec_binding_inst_function_decls args L fds str bconfig) o) ->
        (* ------------------------------------------ *)
        (red_expr S0 C (spec_binding_inst_function_decls_6 args L fds str bconfig (out_ter S (res_intro restype_normal resvalue_empty label_empty))) o)

  | red_spec_binding_inst_arg_obj :
      forall (o1 : out) (L : env_loc (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (lf : object_loc (* input *)) (code : prog (* input *)) (xs : (list prop_name) (* input *)) (args : (list value) (* input *)) (o : out),
        (* ========================================== *)
        (red_expr S C (spec_create_arguments_object lf (xs : (list string)) args (execution_ctx_variable_env C) ((prog_intro_strictness code) : strictness_flag)) o1) ->
        (red_expr S C (spec_binding_inst_arg_obj_1 code L ((prog_intro_strictness code) : strictness_flag) o1) o) ->
        (* ------------------------------------------ *)
        (red_expr S C (spec_binding_inst_arg_obj lf code (xs : (list string)) args L) o)

  | red_spec_binding_inst_arg_obj_1_strict :
      forall (o1 : out) (L : env_loc (* input *)) (S0 : state (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (code : prog (* input *)) (largs : object_loc (* input *)) (o : out),
        (* ========================================== *)
        (red_expr S C (spec_env_record_create_immutable_binding L ((("arguments")%string) : prop_name)) o1) ->
        (red_expr S C (spec_binding_inst_arg_obj_2 code L largs o1) o) ->
        (* ------------------------------------------ *)
        (red_expr S0 C (spec_binding_inst_arg_obj_1 code L (((true : provide_this_flag) : bool) : strictness_flag) (out_ter S ((resvalue_value (value_object largs)) : res))) o)

  | red_spec_binding_inst_arg_obj_2 :
      forall (L : env_loc (* input *)) (S0 : state (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (code : prog (* input *)) (largs : object_loc (* input *)) (o : out),
        (* ========================================== *)
        (red_expr S C (spec_env_record_initialize_immutable_binding L ((("arguments")%string) : prop_name) (value_object largs)) o) ->
        (* ------------------------------------------ *)
        (red_expr S0 C (spec_binding_inst_arg_obj_2 code L largs (out_ter S (res_intro restype_normal resvalue_empty label_empty))) o)

  | red_spec_binding_inst_arg_obj_1_not_strict :
      forall (L : env_loc (* input *)) (S0 : state (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (code : prog (* input *)) (largs : value (* input *)) (o : out),
        (* ========================================== *)
        (red_expr S C (spec_env_record_create_set_mutable_binding L ((("arguments")%string) : prop_name) (None : (option bool)) largs false) o) ->
        (* ------------------------------------------ *)
        (red_expr S0 C (spec_binding_inst_arg_obj_1 code L (((false : provide_this_flag) : bool) : strictness_flag) (out_ter S ((resvalue_value largs) : res))) o)

  | red_spec_binding_inst_var_decls_nil :
      forall (L : env_loc (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (bconfig : bool (* input *)) (str : strictness_flag (* input *)),
        (* ========================================== *)
        (* ------------------------------------------ *)
        (red_expr S C (spec_binding_inst_var_decls L (nil : (list string)) bconfig str) (out_void S))

  | red_spec_binding_inst_var_decls_cons :
      forall (o1 : out) (L : env_loc (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (vd : string (* input *)) (vds : (list string) (* input *)) (bconfig : bool (* input *)) (str : strictness_flag (* input *)) (o : out),
        (* ========================================== *)
        (red_expr S C (spec_env_record_has_binding L (vd : prop_name)) o1) ->
        (red_expr S C (spec_binding_inst_var_decls_1 L vd vds bconfig str o1) o) ->
        (* ------------------------------------------ *)
        (red_expr S C (spec_binding_inst_var_decls L (vd :: vds) bconfig str) o)

  | red_spec_binding_inst_var_decls_1_true :
      forall (L : env_loc (* input *)) (S0 : state (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (vd : string (* input *)) (vds : (list string) (* input *)) (bconfig : bool (* input *)) (str : strictness_flag (* input *)) (o : out),
        (* ========================================== *)
        (red_expr S C (spec_binding_inst_var_decls L vds bconfig str) o) ->
        (* ------------------------------------------ *)
        (red_expr S0 C (spec_binding_inst_var_decls_1 L vd vds bconfig str (out_ter S ((resvalue_value (value_prim (prim_bool ((true : provide_this_flag) : bool)))) : res))) o)

  | red_spec_binding_inst_var_decls_1_false :
      forall (o1 : out) (L : env_loc (* input *)) (S0 : state (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (vd : string (* input *)) (vds : (list string) (* input *)) (bconfig : bool (* input *)) (str : strictness_flag (* input *)) (o : out),
        (* ========================================== *)
        (red_expr S C (spec_env_record_create_set_mutable_binding L (vd : prop_name) ((Some bconfig) : (option bool)) undef (str : bool)) o1) ->
        (red_expr S C (spec_binding_inst_var_decls_2 L vds bconfig str o1) o) ->
        (* ------------------------------------------ *)
        (red_expr S0 C (spec_binding_inst_var_decls_1 L vd vds bconfig str (out_ter S ((resvalue_value (value_prim (prim_bool ((false : provide_this_flag) : bool)))) : res))) o)

  | red_spec_binding_inst_var_decls_2 :
      forall (L : env_loc (* input *)) (S0 : state (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (vds : (list string) (* input *)) (bconfig : bool (* input *)) (str : strictness_flag (* input *)) (o : out),
        (* ========================================== *)
        (red_expr S C (spec_binding_inst_var_decls L vds bconfig str) o) ->
        (* ------------------------------------------ *)
        (red_expr S0 C (spec_binding_inst_var_decls_2 L vds bconfig str (out_ter S (res_intro restype_normal resvalue_empty label_empty))) o)

  | red_spec_binding_inst :
      forall (L : env_loc) (Ls : (list env_loc)) (S : state (* input *)) (C : execution_ctx (* input *)) (ct : codetype (* input *)) (olf : (option object_loc) (* input *)) (code : prog (* input *)) (args : (list value) (* input *)) (o : out),
        ((execution_ctx_variable_env C) = ((L :: Ls) : lexical_env)) ->
        (* ========================================== *)
        (red_expr S C (spec_binding_inst_1 ct olf code args L) o) ->
        (* ------------------------------------------ *)
        (red_expr S C (spec_binding_inst ct olf code args) o)

  | red_spec_binding_inst_1_function :
      forall (o1 : out) (xs : (list prop_name)) (S : state (* input *)) (C : execution_ctx (* input *)) (lf : object_loc (* input *)) (code : prog (* input *)) (args : (list value) (* input *)) (L : env_loc (* input *)) (o : out),
        (object_method object_formal_parameters_ S lf (Some xs)) ->
        (* ========================================== *)
        (red_expr S C (spec_binding_inst_formal_params args L (xs : (list string)) ((prog_intro_strictness code) : strictness_flag)) o1) ->
        (red_expr S C (spec_binding_inst_2 codetype_func lf code (xs : (list string)) args L o1) o) ->
        (* ------------------------------------------ *)
        (red_expr S C (spec_binding_inst_1 codetype_func ((Some lf) : (option object_loc)) code args L) o)

  | red_spec_binding_inst_2 :
      forall (S0 : state (* input *)) (xs : (list prop_name) (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (lf : object_loc (* input *)) (code : prog (* input *)) (args : (list value) (* input *)) (L : env_loc (* input *)) (o : out),
        (* ========================================== *)
        (red_expr S C (spec_binding_inst_3 codetype_func ((Some lf) : (option object_loc)) code (xs : (list string)) args L) o) ->
        (* ------------------------------------------ *)
        (red_expr S0 C (spec_binding_inst_2 codetype_func lf code (xs : (list string)) args L (out_ter S (res_intro restype_normal resvalue_empty label_empty))) o)

  | red_spec_binding_inst_1_not_function :
      forall (L : env_loc (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (ct : codetype (* input *)) (code : prog (* input *)) (args : (list value) (* input *)) (o : out),
        (ct <> codetype_func) ->
        (* ========================================== *)
        (red_expr S C (spec_binding_inst_3 ct (None : (option object_loc)) code (nil : (list string)) args L) o) ->
        (* ------------------------------------------ *)
        (red_expr S C (spec_binding_inst_1 ct (None : (option object_loc)) code args L) o)

  | red_spec_binding_inst_3 :
      forall (bconfig : bool) (L : env_loc (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (ct : codetype (* input *)) (olf : (option object_loc) (* input *)) (code : prog (* input *)) (fds : (list funcdecl)) (xs : (list prop_name) (* input *)) (args : (list value) (* input *)) (o1 : out) (o : out),
        (bconfig = (ifb (ct = codetype_eval) then true else false)) ->
        (fds = (prog_funcdecl code)) ->
        (* ========================================== *)
        (red_expr S C (spec_binding_inst_function_decls args L fds ((prog_intro_strictness code) : strictness_flag) bconfig) o1) ->
        (red_expr S C (spec_binding_inst_4 ct olf code (xs : (list string)) args bconfig L o1) o) ->
        (* ------------------------------------------ *)
        (red_expr S C (spec_binding_inst_3 ct olf code (xs : (list string)) args L) o)

  | red_spec_binding_inst_4 :
      forall (bconfig : bool (* input *)) (L : env_loc (* input *)) (S0 : state (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (ct : codetype (* input *)) (olf : (option object_loc) (* input *)) (code : prog (* input *)) (xs : (list prop_name) (* input *)) (args : (list value) (* input *)) (o : out),
        (* ========================================== *)
        (red_expr S C (spec_binding_inst_5 ct olf code (xs : (list string)) args bconfig L) o) ->
        (* ------------------------------------------ *)
        (red_expr S0 C (spec_binding_inst_4 ct olf code (xs : (list string)) args bconfig L (out_ter S (res_intro restype_normal resvalue_empty label_empty))) o)

  | red_spec_binding_inst_5 :
      forall (o1 : out) (L : env_loc (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (ct : codetype (* input *)) (olf : (option object_loc) (* input *)) (code : prog (* input *)) (xs : (list prop_name) (* input *)) (args : (list value) (* input *)) (bconfig : bool (* input *)) (o : out),
        (* ========================================== *)
        (red_expr S C (spec_env_record_has_binding L ((("arguments")%string) : prop_name)) o1) ->
        (red_expr S C (spec_binding_inst_6 ct olf code (xs : (list string)) args bconfig L o1) o) ->
        (* ------------------------------------------ *)
        (red_expr S C (spec_binding_inst_5 ct olf code (xs : (list string)) args bconfig L) o)

  | red_spec_binding_inst_6_arguments :
      forall (o1 : out) (L : env_loc (* input *)) (S0 : state (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (lf : object_loc (* input *)) (code : prog (* input *)) (xs : (list prop_name) (* input *)) (args : (list value) (* input *)) (bconfig : bool (* input *)) (o : out),
        (* ========================================== *)
        (red_expr S C (spec_binding_inst_arg_obj lf code (xs : (list string)) args L) o1) ->
        (red_expr S C (spec_binding_inst_7 code bconfig L o1) o) ->
        (* ------------------------------------------ *)
        (red_expr S0 C (spec_binding_inst_6 codetype_func ((Some lf) : (option object_loc)) code (xs : (list string)) args bconfig L (out_ter S ((resvalue_value (value_prim (prim_bool ((false : provide_this_flag) : bool)))) : res))) o)

  | red_spec_binding_inst_7 :
      forall (S0 : state (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (code : prog (* input *)) (bconfig : bool (* input *)) (L : env_loc (* input *)) (o : out),
        (* ========================================== *)
        (red_expr S C (spec_binding_inst_8 code bconfig L) o) ->
        (* ------------------------------------------ *)
        (red_expr S0 C (spec_binding_inst_7 code bconfig L (out_ter S (res_intro restype_normal resvalue_empty label_empty))) o)

  | red_spec_binding_inst_6_no_arguments :
      forall (L : env_loc (* input *)) (S0 : state (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (ct : codetype (* input *)) (olf : (option object_loc) (* input *)) (code : prog (* input *)) (xs : (list prop_name) (* input *)) (args : (list value) (* input *)) (bconfig : bool (* input *)) (bdefined : res (* input *)) (o : out),
        ((ct = codetype_func) /\ (bdefined = false)) ->
        (* ========================================== *)
        (red_expr S C (spec_binding_inst_8 code bconfig L) o) ->
        (* ------------------------------------------ *)
        (red_expr S0 C (spec_binding_inst_6 ct olf code (xs : (list string)) args bconfig L (out_ter S bdefined)) o)

  | red_spec_binding_inst_8 :
      forall (S0 : state (* input *)) (L : env_loc (* input *)) (S : state) (C : execution_ctx (* input *)) (code : prog (* input *)) (bconfig : bool (* input *)) (o : out),
        (* ========================================== *)
        (red_expr S C (spec_binding_inst_var_decls L (prog_vardecl code) bconfig ((prog_intro_strictness code) : strictness_flag)) o) ->
        (* ------------------------------------------ *)
        (red_expr S0 C (spec_binding_inst_8 code bconfig L) o)

  | red_spec_make_arg_getter :
      forall (xbd : string) (bd : funcbody) (S : state (* input *)) (C : execution_ctx (* input *)) (x : prop_name (* input *)) (X : lexical_env (* input *)) (o : out),
        (xbd = ((("return ")%string) ++ ((x ++ (((";")%string) : prop_name)) : string))) ->
        (bd = (funcbody_intro (prog_intro (((true : provide_this_flag) : bool) : strictness_flag) ((element_stat (stat_return ((Some (expr_identifier (x : string))) : (option expr)))) :: (nil : (list element)))) xbd)) ->
        (* ========================================== *)
        (red_expr S C (spec_creating_function_object (nil : (list string)) bd X (((true : provide_this_flag) : bool) : strictness_flag)) o) ->
        (* ------------------------------------------ *)
        (red_expr S C (spec_make_arg_getter (x : string) X) o)

  | red_spec_make_arg_setter :
      forall (xparam : string) (xbd : string) (bd : funcbody) (S : state (* input *)) (C : execution_ctx (* input *)) (x : prop_name (* input *)) (X : lexical_env (* input *)) (o : out),
        ((xparam : prop_name) = (x ++ ((("_arg")%string) : prop_name))) ->
        ((xbd : prop_name) = (x ++ ((((" = ")%string) ++ (xparam ++ ((";")%string))) : prop_name))) ->
        (bd = (funcbody_intro (prog_intro (((true : provide_this_flag) : bool) : strictness_flag) ((element_stat (stat_expr (expr_assign (expr_identifier (x : string)) (None : (option binary_op)) (expr_identifier xparam)))) :: (nil : (list element)))) xbd)) ->
        (* ========================================== *)
        (red_expr S C (spec_creating_function_object (xparam :: nil) bd X (((true : provide_this_flag) : bool) : strictness_flag)) o) ->
        (* ------------------------------------------ *)
        (red_expr S C (spec_make_arg_setter (x : string) X) o)

  | red_spec_object_get_args_obj :
      forall (lmap : object_loc) (S : state (* input *)) (C : execution_ctx (* input *)) (vthis : value (* input *)) (l : object_loc (* input *)) (x : prop_name (* input *)) (o : out) (y : (specret full_descriptor)),
        (object_method object_parameter_map_ S l (Some lmap)) ->
        (* ========================================== *)
        (red_spec S C (spec_object_get_own_prop lmap x) y) ->
        (red_expr S C (spec_args_obj_get_1 vthis l x lmap y) o) ->
        (* ------------------------------------------ *)
        (red_expr S C (spec_object_get_1 builtin_get_args_obj vthis l x) o)

  | red_spec_object_get_args_obj_1_undef :
      forall (S0 : state (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (vthis : value (* input *)) (l : object_loc (* input *)) (x : prop_name (* input *)) (lmap : object_loc (* input *)) (o : out),
        (* ========================================== *)
        (red_expr S0 C (spec_object_get_1 builtin_get_function vthis l x) o) ->
        (* ------------------------------------------ *)
        (red_expr S C (spec_args_obj_get_1 vthis l x lmap ((specret_val S0 full_descriptor_undef) : (specret full_descriptor))) o)

  | red_spec_object_get_args_obj_1_attrs :
      forall (S0 : state (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (vthis : value (* input *)) (l : object_loc (* input *)) (x : prop_name (* input *)) (lmap : object_loc (* input *)) (A : attributes (* input *)) (o : out),
        (* ========================================== *)
        (red_expr S0 C (spec_object_get (value_object lmap) x) o) ->
        (* ------------------------------------------ *)
        (red_expr S C (spec_args_obj_get_1 vthis l x lmap ((specret_val S0 (full_descriptor_some A)) : (specret full_descriptor))) o)

  | red_spec_object_define_own_prop_args_obj :
      forall (lmap : object_loc) (S : state (* input *)) (C : execution_ctx (* input *)) (l : object_loc (* input *)) (x : prop_name (* input *)) (Desc : descriptor (* input *)) (throw : bool (* input *)) (o : out) (y : (specret full_descriptor)),
        (object_method object_parameter_map_ S l (Some lmap)) ->
        (* ========================================== *)
        (red_spec S C (spec_object_get_own_prop lmap x) y) ->
        (red_expr S C (spec_args_obj_define_own_prop_1 l x Desc throw lmap y) o) ->
        (* ------------------------------------------ *)
        (red_expr S C (spec_object_define_own_prop_1 builtin_define_own_prop_args_obj l x Desc throw) o)

  | red_spec_object_define_own_prop_args_obj_1 :
      forall (o1 : out) (S0 : state (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (l : object_loc (* input *)) (x : prop_name (* input *)) (Desc : descriptor (* input *)) (throw : bool (* input *)) (lmap : object_loc (* input *)) (Dmap : full_descriptor (* input *)) (o : out),
        (* ========================================== *)
        (red_expr S0 C (spec_object_define_own_prop_1 builtin_define_own_prop_default l x Desc false) o1) ->
        (red_expr S0 C (spec_args_obj_define_own_prop_2 l x Desc throw lmap Dmap o1) o) ->
        (* ------------------------------------------ *)
        (red_expr S C (spec_args_obj_define_own_prop_1 l x Desc throw lmap ((specret_val S0 Dmap) : (specret full_descriptor))) o)

  | red_spec_object_define_own_prop_args_obj_2_false :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (l : object_loc (* input *)) (x : prop_name (* input *)) (Desc : descriptor (* input *)) (throw : bool (* input *)) (lmap : object_loc (* input *)) (Dmap : full_descriptor (* input *)) (S' : state (* input *)) (o : out),
        (* ========================================== *)
        (red_expr S' C (spec_object_define_own_prop_reject throw) o) ->
        (* ------------------------------------------ *)
        (red_expr S C (spec_args_obj_define_own_prop_2 l x Desc throw lmap Dmap (out_ter S' ((resvalue_value (value_prim (prim_bool ((false : provide_this_flag) : bool)))) : res))) o)

  | red_spec_object_define_own_prop_args_obj_2_true_acc :
      forall (o1 : out) (S : state (* input *)) (C : execution_ctx (* input *)) (l : object_loc (* input *)) (x : prop_name (* input *)) (Desc : descriptor (* input *)) (throw : bool (* input *)) (lmap : object_loc (* input *)) (A : attributes (* input *)) (S' : state (* input *)) (o : out),
        (descriptor_is_accessor Desc) ->
        (* ========================================== *)
        (red_expr S' C (spec_object_delete lmap x false) o1) ->
        (red_expr S' C (spec_args_obj_define_own_prop_5 o1) o) ->
        (* ------------------------------------------ *)
        (red_expr S C (spec_args_obj_define_own_prop_2 l x Desc throw lmap (full_descriptor_some A) (out_ter S' ((resvalue_value (value_prim (prim_bool ((true : provide_this_flag) : bool)))) : res))) o)

  | red_spec_object_define_own_prop_args_obj_2_true_not_acc_some :
      forall (v : value) (o1 : out) (S : state (* input *)) (C : execution_ctx (* input *)) (l : object_loc (* input *)) (x : prop_name (* input *)) (Desc : descriptor (* input *)) (throw : bool (* input *)) (lmap : object_loc (* input *)) (A : attributes (* input *)) (S' : state (* input *)) (o : out),
        (descriptor_is_accessor Desc) ->
        ((descriptor_value Desc) = ((Some v) : (option value))) ->
        (* ========================================== *)
        (red_expr S' C (spec_object_put (value_object lmap) x v throw) o1) ->
        (red_expr S' C (spec_args_obj_define_own_prop_3 l x Desc throw lmap o1) o) ->
        (* ------------------------------------------ *)
        (red_expr S C (spec_args_obj_define_own_prop_2 l x Desc throw lmap (full_descriptor_some A) (out_ter S' ((resvalue_value (value_prim (prim_bool ((true : provide_this_flag) : bool)))) : res))) o)

  | red_spec_object_define_own_prop_args_obj_3 :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (l : object_loc (* input *)) (x : prop_name (* input *)) (Desc : descriptor (* input *)) (throw : bool (* input *)) (lmap : object_loc (* input *)) (S' : state (* input *)) (o : out),
        (* ========================================== *)
        (red_expr S' C (spec_args_obj_define_own_prop_4 l x Desc throw lmap) o) ->
        (* ------------------------------------------ *)
        (red_expr S C (spec_args_obj_define_own_prop_3 l x Desc throw lmap (out_ter S' (res_intro restype_normal resvalue_empty label_empty))) o)

  | red_spec_object_define_own_prop_args_obj_2_true_not_acc_none :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (l : object_loc (* input *)) (x : prop_name (* input *)) (Desc : descriptor (* input *)) (throw : bool (* input *)) (lmap : object_loc (* input *)) (A : attributes (* input *)) (S' : state (* input *)) (o : out),
        (descriptor_is_accessor Desc) ->
        ((descriptor_value Desc) = (None : (option value))) ->
        (* ========================================== *)
        (red_expr S' C (spec_args_obj_define_own_prop_4 l x Desc throw lmap) o) ->
        (* ------------------------------------------ *)
        (red_expr S C (spec_args_obj_define_own_prop_2 l x Desc throw lmap (full_descriptor_some A) (out_ter S' ((resvalue_value (value_prim (prim_bool ((true : provide_this_flag) : bool)))) : res))) o)

  | red_spec_object_define_own_prop_args_obj_4_false :
      forall (o1 : out) (S : state (* input *)) (C : execution_ctx (* input *)) (l : object_loc (* input *)) (x : prop_name (* input *)) (Desc : descriptor (* input *)) (throw : bool (* input *)) (lmap : object_loc (* input *)) (o : out),
        ((descriptor_writable Desc) = ((Some false) : (option bool))) ->
        (* ========================================== *)
        (red_expr S C (spec_object_delete lmap x false) o1) ->
        (red_expr S C (spec_args_obj_define_own_prop_5 o1) o) ->
        (* ------------------------------------------ *)
        (red_expr S C (spec_args_obj_define_own_prop_4 l x Desc throw lmap) o)

  | red_spec_object_define_own_prop_args_obj_5 :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (S' : state (* input *)) (b : bool (* input *)) (o : out),
        (* ========================================== *)
        (red_expr S' C spec_args_obj_define_own_prop_6 o) ->
        (* ------------------------------------------ *)
        (red_expr S C (spec_args_obj_define_own_prop_5 (out_ter S' ((resvalue_value (value_prim (prim_bool ((b : provide_this_flag) : bool)))) : res))) o)

  | red_spec_object_define_own_prop_args_obj_4_not_false :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (l : object_loc (* input *)) (x : prop_name (* input *)) (Desc : descriptor (* input *)) (throw : bool (* input *)) (lmap : object_loc (* input *)) (o : out),
        ((descriptor_writable Desc) <> ((Some false) : (option bool))) ->
        (* ========================================== *)
        (red_expr S C spec_args_obj_define_own_prop_6 o) ->
        (* ------------------------------------------ *)
        (red_expr S C (spec_args_obj_define_own_prop_4 l x Desc throw lmap) o)

  | red_spec_object_define_own_prop_args_obj_2_true_undef :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (l : object_loc (* input *)) (x : prop_name (* input *)) (Desc : descriptor (* input *)) (throw : bool (* input *)) (lmap : object_loc (* input *)) (S' : state (* input *)) (o : out),
        (* ========================================== *)
        (red_expr S' C spec_args_obj_define_own_prop_6 o) ->
        (* ------------------------------------------ *)
        (red_expr S C (spec_args_obj_define_own_prop_2 l x Desc throw lmap full_descriptor_undef (out_ter S' ((resvalue_value (value_prim (prim_bool ((true : provide_this_flag) : bool)))) : res))) o)

  | red_spec_object_define_own_prop_args_obj_6 :
      forall (S : state (* input *)) (C : execution_ctx (* input *)),
        (* ========================================== *)
        (* ------------------------------------------ *)
        (red_expr S C spec_args_obj_define_own_prop_6 (out_ter S ((resvalue_value (value_prim (prim_bool ((true : provide_this_flag) : bool)))) : res)))

  | red_spec_object_delete_args_obj :
      forall (lmap : object_loc) (S : state (* input *)) (C : execution_ctx (* input *)) (l : object_loc (* input *)) (x : prop_name (* input *)) (throw : bool (* input *)) (o : out) (y : (specret full_descriptor)),
        (object_method object_parameter_map_ S l (Some lmap)) ->
        (* ========================================== *)
        (red_spec S C (spec_object_get_own_prop lmap x) y) ->
        (red_expr S C (spec_args_obj_delete_1 l x throw lmap y) o) ->
        (* ------------------------------------------ *)
        (red_expr S C (spec_object_delete_1 builtin_delete_args_obj l x throw) o)

  | red_spec_object_delete_args_obj_1 :
      forall (o1 : out) (S0 : state (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (l : object_loc (* input *)) (x : prop_name (* input *)) (throw : bool (* input *)) (lmap : object_loc (* input *)) (D : full_descriptor (* input *)) (o : out),
        (* ========================================== *)
        (red_expr S0 C (spec_object_delete_1 builtin_delete_default l x throw) o1) ->
        (red_expr S0 C (spec_args_obj_delete_2 l x throw lmap D o1) o) ->
        (* ------------------------------------------ *)
        (red_expr S C (spec_args_obj_delete_1 l x throw lmap ((specret_val S0 D) : (specret full_descriptor))) o)

  | red_spec_object_delete_args_obj_2_if :
      forall (o1 : out) (S : state (* input *)) (C : execution_ctx (* input *)) (l : object_loc (* input *)) (x : prop_name (* input *)) (throw : bool (* input *)) (lmap : object_loc (* input *)) (A : attributes (* input *)) (S' : state (* input *)) (o : out),
        (* ========================================== *)
        (red_expr S' C (spec_object_delete lmap x false) o1) ->
        (red_expr S' C (spec_args_obj_delete_3 o1) o) ->
        (* ------------------------------------------ *)
        (red_expr S C (spec_args_obj_delete_2 l x throw lmap (full_descriptor_some A) (out_ter S' ((resvalue_value (value_prim (prim_bool ((true : provide_this_flag) : bool)))) : res))) o)

  | red_spec_object_delete_args_obj_3 :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (S' : state (* input *)) (b : bool (* input *)) (o : out),
        (* ========================================== *)
        (red_expr S' C (spec_args_obj_delete_4 true) o) ->
        (* ------------------------------------------ *)
        (red_expr S C (spec_args_obj_delete_3 (out_ter S' ((resvalue_value (value_prim (prim_bool ((b : provide_this_flag) : bool)))) : res))) o)

  | red_spec_object_delete_args_obj_2_else :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (l : object_loc (* input *)) (x : prop_name (* input *)) (throw : bool (* input *)) (lmap : object_loc (* input *)) (D : full_descriptor (* input *)) (S' : state (* input *)) (b : bool (* input *)) (o : out),
        ((b = false) \/ (D = full_descriptor_undef)) ->
        (* ========================================== *)
        (red_expr S' C (spec_args_obj_delete_4 b) o) ->
        (* ------------------------------------------ *)
        (red_expr S C (spec_args_obj_delete_2 l x throw lmap D (out_ter S' ((resvalue_value (value_prim (prim_bool ((b : provide_this_flag) : bool)))) : res))) o)

  | red_spec_object_delete_args_obj_4 :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (b : bool (* input *)),
        (* ========================================== *)
        (* ------------------------------------------ *)
        (red_expr S C (spec_args_obj_delete_4 b) (out_ter S ((resvalue_value (value_prim (prim_bool ((b : provide_this_flag) : bool)))) : res)))

  | red_spec_arguments_object_map :
      forall (o1 : out) (S : state (* input *)) (C : execution_ctx (* input *)) (l : object_loc (* input *)) (xs : (list prop_name) (* input *)) (args : (list value) (* input *)) (X : lexical_env (* input *)) (str : strictness_flag (* input *)) (o : out),
        (* ========================================== *)
        (red_expr S C (spec_construct_prealloc prealloc_object (nil : (list value))) o1) ->
        (red_expr S C (spec_arguments_object_map_1 l (xs : (list string)) args X str o1) o) ->
        (* ------------------------------------------ *)
        (red_expr S C (spec_arguments_object_map l (xs : (list string)) args X str) o)

  | red_spec_arguments_object_map_1 :
      forall (S' : state (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (l : object_loc (* input *)) (xs : (list prop_name) (* input *)) (args : (list value) (* input *)) (X : lexical_env (* input *)) (str : strictness_flag (* input *)) (lmap : object_loc (* input *)) (o : out),
        (* ========================================== *)
        (red_expr S' C (spec_arguments_object_map_2 l (xs : (list string)) args X str lmap (nil : (list string)) (my_Z_of_nat ((length args) - (1%nat)))) o) ->
        (* ------------------------------------------ *)
        (red_expr S C (spec_arguments_object_map_1 l (xs : (list string)) args X str (out_ter S' ((resvalue_value (value_object lmap)) : res))) o)

  | red_spec_arguments_object_map_2_negative :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (l : object_loc (* input *)) (xs : (list prop_name) (* input *)) (args : (list value) (* input *)) (X : lexical_env (* input *)) (str : strictness_flag (* input *)) (lmap : object_loc (* input *)) (xsmap : (list string) (* input *)) (k : int (* input *)) (o : out),
        (k < (my_Z_of_nat (0%nat))) ->
        (* ========================================== *)
        (red_expr S C (spec_arguments_object_map_8 l lmap xsmap) o) ->
        (* ------------------------------------------ *)
        (red_expr S C (spec_arguments_object_map_2 l (xs : (list string)) args X str lmap xsmap k) o)

  | red_spec_arguments_object_map_2_positive :
      forall (o1 : out) (S : state (* input *)) (C : execution_ctx (* input *)) (l : object_loc (* input *)) (xs : (list prop_name) (* input *)) (args : (list value) (* input *)) (X : lexical_env (* input *)) (str : strictness_flag (* input *)) (lmap : object_loc (* input *)) (xsmap : (list string) (* input *)) (k : int (* input *)) (v : value) (o : out),
        (ZNth k args v) ->
        (* ========================================== *)
        (red_expr S C (spec_object_define_own_prop l (((convert_prim_to_string (prim_number (JsNumber.of_int k))) : string) : prop_name) (descriptor_of_attributes (attributes_data_of (attributes_data_intro_all_true v))) false) o1) ->
        (red_expr S C (spec_arguments_object_map_3 l (xs : (list string)) args X str lmap xsmap k o1) o) ->
        (* ------------------------------------------ *)
        (red_expr S C (spec_arguments_object_map_2 l (xs : (list string)) args X str lmap xsmap k) o)

  | red_spec_arguments_object_map_3_next :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (l : object_loc (* input *)) (xs : (list prop_name) (* input *)) (args : (list value) (* input *)) (X : lexical_env (* input *)) (str : strictness_flag (* input *)) (lmap : object_loc (* input *)) (xsmap : (list string) (* input *)) (k : int (* input *)) (S' : state (* input *)) (b : bool (* input *)) (o : out),
        (k >= (my_Z_of_nat (length xs))) ->
        (* ========================================== *)
        (red_expr S' C (spec_arguments_object_map_2 l (xs : (list string)) args X str lmap xsmap (k - (my_Z_of_nat (1%nat)))) o) ->
        (* ------------------------------------------ *)
        (red_expr S C (spec_arguments_object_map_3 l (xs : (list string)) args X str lmap xsmap k (out_ter S' ((resvalue_value (value_prim (prim_bool ((b : provide_this_flag) : bool)))) : res))) o)

  | red_spec_arguments_object_map_3_cont_next :
      forall (x : prop_name) (S : state (* input *)) (C : execution_ctx (* input *)) (l : object_loc (* input *)) (xs : (list prop_name) (* input *)) (args : (list value) (* input *)) (X : lexical_env (* input *)) (str : strictness_flag (* input *)) (lmap : object_loc (* input *)) (xsmap : (list string) (* input *)) (k : int (* input *)) (S' : state (* input *)) (b : bool (* input *)) (o : out),
        (ZNth k xs x) ->
        ((str = true) \/ ((Mem x xsmap) : Prop)) ->
        (* ========================================== *)
        (red_expr S' C (spec_arguments_object_map_2 l (xs : (list string)) args X str lmap xsmap (k - (my_Z_of_nat (1%nat)))) o) ->
        (* ------------------------------------------ *)
        (red_expr S C (spec_arguments_object_map_3 l (xs : (list string)) args X str lmap xsmap k (out_ter S' ((resvalue_value (value_prim (prim_bool ((b : provide_this_flag) : bool)))) : res))) o)

  | red_spec_arguments_object_map_3_cont_cont :
      forall (x : prop_name) (S : state (* input *)) (C : execution_ctx (* input *)) (l : object_loc (* input *)) (xs : (list prop_name) (* input *)) (args : (list value) (* input *)) (X : lexical_env (* input *)) (str : strictness_flag (* input *)) (lmap : object_loc (* input *)) (xsmap : (list string) (* input *)) (k : int (* input *)) (S' : state (* input *)) (b : bool (* input *)) (o : out),
        (ZNth k xs x) ->
        ((str = false) /\ (~ (Mem x xsmap))) ->
        (* ========================================== *)
        (red_expr S' C (spec_arguments_object_map_4 l (xs : (list string)) args X str lmap xsmap k (x : string)) o) ->
        (* ------------------------------------------ *)
        (red_expr S C (spec_arguments_object_map_3 l (xs : (list string)) args X str lmap xsmap k (out_ter S' ((resvalue_value (value_prim (prim_bool ((b : provide_this_flag) : bool)))) : res))) o)

  | red_spec_arguments_object_map_4 :
      forall (o1 : out) (S : state (* input *)) (C : execution_ctx (* input *)) (l : object_loc (* input *)) (xs : (list prop_name) (* input *)) (args : (list value) (* input *)) (X : lexical_env (* input *)) (str : strictness_flag (* input *)) (lmap : object_loc (* input *)) (xsmap : (list string) (* input *)) (k : int (* input *)) (x : prop_name (* input *)) (o : out),
        (* ========================================== *)
        (red_expr S C (spec_make_arg_getter (x : string) X) o1) ->
        (red_expr S C (spec_arguments_object_map_5 l (xs : (list string)) args X str lmap ((x :: (xsmap : (list prop_name))) : (list string)) k (x : string) o1) o) ->
        (* ------------------------------------------ *)
        (red_expr S C (spec_arguments_object_map_4 l (xs : (list string)) args X str lmap xsmap k (x : string)) o)

  | red_spec_arguments_object_map_5 :
      forall (o1 : out) (S : state (* input *)) (C : execution_ctx (* input *)) (l : object_loc (* input *)) (xs : (list prop_name) (* input *)) (args : (list value) (* input *)) (X : lexical_env (* input *)) (str : strictness_flag (* input *)) (lmap : object_loc (* input *)) (xsmap : (list string) (* input *)) (k : int (* input *)) (x : prop_name (* input *)) (S' : state (* input *)) (lgetter : object_loc (* input *)) (o : out),
        (* ========================================== *)
        (red_expr S' C (spec_make_arg_setter (x : string) X) o1) ->
        (red_expr S' C (spec_arguments_object_map_6 l (xs : (list string)) args X str lmap xsmap k lgetter o1) o) ->
        (* ------------------------------------------ *)
        (red_expr S C (spec_arguments_object_map_5 l (xs : (list string)) args X str lmap xsmap k (x : string) (out_ter S' ((resvalue_value (value_object lgetter)) : res))) o)

  | red_spec_arguments_object_map_6 :
      forall (o1 : out) (S : state (* input *)) (C : execution_ctx (* input *)) (l : object_loc (* input *)) (xs : (list prop_name) (* input *)) (args : (list value) (* input *)) (X : lexical_env (* input *)) (str : strictness_flag (* input *)) (lmap : object_loc (* input *)) (xsmap : (list string) (* input *)) (k : int (* input *)) (lgetter : object_loc (* input *)) (S' : state (* input *)) (lsetter : object_loc (* input *)) (o : out),
        (* ========================================== *)
        (red_expr S' C (spec_object_define_own_prop lmap (((convert_prim_to_string (prim_number (JsNumber.of_int k))) : string) : prop_name) (descriptor_of_attributes (attributes_accessor_of (attributes_accessor_intro (value_object lgetter) (value_object lsetter) false true))) false) o1) ->
        (red_expr S' C (spec_arguments_object_map_7 l (xs : (list string)) args X str lmap xsmap k o1) o) ->
        (* ------------------------------------------ *)
        (red_expr S C (spec_arguments_object_map_6 l (xs : (list string)) args X str lmap xsmap k lgetter (out_ter S' ((resvalue_value (value_object lsetter)) : res))) o)

  | red_spec_arguments_object_map_7 :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (l : object_loc (* input *)) (xs : (list prop_name) (* input *)) (args : (list value) (* input *)) (X : lexical_env (* input *)) (str : strictness_flag (* input *)) (lmap : object_loc (* input *)) (xsmap : (list string) (* input *)) (k : int (* input *)) (S' : state (* input *)) (b : bool (* input *)) (o : out),
        (* ========================================== *)
        (red_expr S' C (spec_arguments_object_map_2 l (xs : (list string)) args X str lmap xsmap (k - (my_Z_of_nat (1%nat)))) o) ->
        (* ------------------------------------------ *)
        (red_expr S C (spec_arguments_object_map_7 l (xs : (list string)) args X str lmap xsmap k (out_ter S' ((resvalue_value (value_prim (prim_bool ((b : provide_this_flag) : bool)))) : res))) o)

  | red_spec_arguments_object_map_8_cons :
      forall (O : object) (S : state (* input *)) (C : execution_ctx (* input *)) (l : object_loc (* input *)) (lmap : object_loc (* input *)) (xsmap : (list string) (* input *)),
        (xsmap <> nil) ->
        (object_binds S l O) ->
        (* ========================================== *)
        (* ------------------------------------------ *)
        (red_expr S C (spec_arguments_object_map_8 l lmap xsmap) (out_void ((object_write S l ((object_for_args_object O lmap builtin_get_args_obj builtin_get_own_prop_args_obj builtin_define_own_prop_args_obj builtin_delete_args_obj) : object)) : state)))

  | red_spec_arguments_object_map_8_nil :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (l : object_loc (* input *)) (lmap : object_loc (* input *)),
        (* ========================================== *)
        (* ------------------------------------------ *)
        (red_expr S C (spec_arguments_object_map_8 l lmap (nil : (list string))) (out_void S))

  | red_spec_create_arguments_object :
      forall (o1 : out) (S : state (* input *)) (C : execution_ctx (* input *)) (lf : object_loc (* input *)) (xs : (list prop_name) (* input *)) (args : (list value) (* input *)) (X : lexical_env (* input *)) (str : strictness_flag (* input *)) (o : out),
        (* ========================================== *)
        (red_expr ((snd ((object_alloc S ((object_new prealloc_object_proto (("Arguments")%string)) : object)) : (object_loc * state))) : state) C (spec_object_define_own_prop ((fst ((object_alloc S ((object_new prealloc_object_proto (("Arguments")%string)) : object)) : (object_loc * state))) : object_loc) ((("length")%string) : prop_name) (descriptor_of_attributes (attributes_data_of (attributes_data_intro ((JsNumber.of_int (length args)) : value) true false true))) false) o1) ->
        (red_expr ((snd ((object_alloc S ((object_new prealloc_object_proto (("Arguments")%string)) : object)) : (object_loc * state))) : state) C (spec_create_arguments_object_1 lf (xs : (list string)) args X str ((fst ((object_alloc S ((object_new prealloc_object_proto (("Arguments")%string)) : object)) : (object_loc * state))) : object_loc) o1) o) ->
        (* ------------------------------------------ *)
        (red_expr S C (spec_create_arguments_object lf (xs : (list string)) args X str) o)

  | red_spec_create_arguments_object_1 :
      forall (o1 : out) (S : state (* input *)) (C : execution_ctx (* input *)) (lf : object_loc (* input *)) (xs : (list prop_name) (* input *)) (args : (list value) (* input *)) (X : lexical_env (* input *)) (str : strictness_flag (* input *)) (l : object_loc (* input *)) (S' : state (* input *)) (b : bool (* input *)) (o : out),
        (* ========================================== *)
        (red_expr S' C (spec_arguments_object_map l (xs : (list string)) args X str) o1) ->
        (red_expr S' C (spec_create_arguments_object_2 lf str l o1) o) ->
        (* ------------------------------------------ *)
        (red_expr S C (spec_create_arguments_object_1 lf (xs : (list string)) args X str l (out_ter S' ((resvalue_value (value_prim (prim_bool ((b : provide_this_flag) : bool)))) : res))) o)

  | red_spec_create_arguments_object_2_non_strict :
      forall (o1 : out) (S : state (* input *)) (C : execution_ctx (* input *)) (lf : object_loc (* input *)) (l : object_loc (* input *)) (S' : state (* input *)) (o : out),
        (* ========================================== *)
        (red_expr S' C (spec_object_define_own_prop l ((("callee")%string) : prop_name) (descriptor_of_attributes (attributes_data_of (attributes_data_intro (value_object lf) true false true))) false) o1) ->
        (red_expr S' C (spec_create_arguments_object_4 l o1) o) ->
        (* ------------------------------------------ *)
        (red_expr S C (spec_create_arguments_object_2 lf (((false : provide_this_flag) : bool) : strictness_flag) l (out_ter S' (res_intro restype_normal resvalue_empty label_empty))) o)

  | red_spec_create_arguments_object_2_strict :
      forall (vthrower : value) (o1 : out) (S : state (* input *)) (C : execution_ctx (* input *)) (lf : object_loc (* input *)) (l : object_loc (* input *)) (S' : state (* input *)) (o : out),
        (vthrower = (value_object (object_loc_prealloc prealloc_throw_type_error))) ->
        (* ========================================== *)
        (red_expr S' C (spec_object_define_own_prop l ((("caller")%string) : prop_name) (descriptor_of_attributes (attributes_accessor_of (attributes_accessor_intro vthrower vthrower false false))) false) o1) ->
        (red_expr S' C (spec_create_arguments_object_3 l vthrower (attributes_accessor_of (attributes_accessor_intro vthrower vthrower false false)) o1) o) ->
        (* ------------------------------------------ *)
        (red_expr S C (spec_create_arguments_object_2 lf (((true : provide_this_flag) : bool) : strictness_flag) l (out_ter S' (res_intro restype_normal resvalue_empty label_empty))) o)

  | red_spec_create_arguments_object_3 :
      forall (o1 : out) (S : state (* input *)) (C : execution_ctx (* input *)) (l : object_loc (* input *)) (vthrower : value (* input *)) (A : attributes (* input *)) (S' : state (* input *)) (b : bool (* input *)) (o : out),
        (* ========================================== *)
        (red_expr S' C (spec_object_define_own_prop l ((("callee")%string) : prop_name) (descriptor_of_attributes A) false) o1) ->
        (red_expr S' C (spec_create_arguments_object_4 l o1) o) ->
        (* ------------------------------------------ *)
        (red_expr S C (spec_create_arguments_object_3 l vthrower A (out_ter S' ((resvalue_value (value_prim (prim_bool ((b : provide_this_flag) : bool)))) : res))) o)

  | red_spec_create_arguments_object_4 :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (l : object_loc (* input *)) (S' : state (* input *)) (b : bool (* input *)),
        (* ========================================== *)
        (* ------------------------------------------ *)
        (red_expr S C (spec_create_arguments_object_4 l (out_ter S' ((resvalue_value (value_prim (prim_bool ((b : provide_this_flag) : bool)))) : res))) (out_ter S' ((resvalue_value (value_object l)) : res)))

  | red_spec_creating_function_object_proto :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (l : object_loc (* input *)) (o1 : out) (o : out),
        (* ========================================== *)
        (red_expr S C (spec_construct_prealloc prealloc_object (nil : (list value))) o1) ->
        (red_expr S C (spec_creating_function_object_proto_1 l o1) o) ->
        (* ------------------------------------------ *)
        (red_expr S C (spec_creating_function_object_proto l) o)

  | red_spec_creating_function_object_proto_1 :
      forall (S0 : state (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (l : object_loc (* input *)) (lproto : object_loc (* input *)) (o1 : out) (o : out),
        (* ========================================== *)
        (red_expr S C (spec_object_define_own_prop lproto ((("constructor")%string) : prop_name) (descriptor_of_attributes (attributes_data_of (attributes_data_intro (value_object l) true false true))) false) o1) ->
        (red_expr S C (spec_creating_function_object_proto_2 l lproto o1) o) ->
        (* ------------------------------------------ *)
        (red_expr S0 C (spec_creating_function_object_proto_1 l (out_ter S ((resvalue_value (value_object lproto)) : res))) o)

  | red_spec_creating_function_object_proto_2 :
      forall (S0 : state (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (l : object_loc (* input *)) (lproto : object_loc (* input *)) (b : bool (* input *)) (o : out),
        (* ========================================== *)
        (red_expr S C (spec_object_define_own_prop l ((("prototype")%string) : prop_name) (descriptor_of_attributes (attributes_data_of (attributes_data_intro (value_object lproto) true false false))) false) o) ->
        (* ------------------------------------------ *)
        (red_expr S0 C (spec_creating_function_object_proto_2 l lproto (out_ter S ((resvalue_value (value_prim (prim_bool ((b : provide_this_flag) : bool)))) : res))) o)

  | red_spec_creating_function_object :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (names : (list string) (* input *)) (bd : funcbody (* input *)) (X : lexical_env (* input *)) (str : strictness_flag (* input *)) (o1 : out) (o : out),
        (* ========================================== *)
        (red_expr ((snd ((object_alloc S ((object_with_details ((object_with_invokation ((object_with_get ((object_new prealloc_function_proto (("Function")%string)) : object) builtin_get_function) : object) (Some construct_default) (Some call_default) (Some builtin_has_instance_function)) : object) (Some X) (Some names) (Some bd) None None None None) : object)) : (object_loc * state))) : state) C (spec_object_define_own_prop ((fst ((object_alloc S ((object_with_details ((object_with_invokation ((object_with_get ((object_new prealloc_function_proto (("Function")%string)) : object) builtin_get_function) : object) (Some construct_default) (Some call_default) (Some builtin_has_instance_function)) : object) (Some X) (Some names) (Some bd) None None None None) : object)) : (object_loc * state))) : object_loc) ((("length")%string) : prop_name) (descriptor_of_attributes (attributes_data_of (attributes_data_intro ((JsNumber.of_int (length names)) : value) false false false))) false) o1) ->
        (red_expr ((snd ((object_alloc S ((object_with_details ((object_with_invokation ((object_with_get ((object_new prealloc_function_proto (("Function")%string)) : object) builtin_get_function) : object) (Some construct_default) (Some call_default) (Some builtin_has_instance_function)) : object) (Some X) (Some names) (Some bd) None None None None) : object)) : (object_loc * state))) : state) C (spec_creating_function_object_1 str ((fst ((object_alloc S ((object_with_details ((object_with_invokation ((object_with_get ((object_new prealloc_function_proto (("Function")%string)) : object) builtin_get_function) : object) (Some construct_default) (Some call_default) (Some builtin_has_instance_function)) : object) (Some X) (Some names) (Some bd) None None None None) : object)) : (object_loc * state))) : object_loc) o1) o) ->
        (* ------------------------------------------ *)
        (red_expr S C (spec_creating_function_object names bd X str) o)

  | red_spec_creating_function_object_1 :
      forall (S0 : state (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (str : strictness_flag (* input *)) (l : object_loc (* input *)) (b : bool (* input *)) (o1 : out) (o : out),
        (* ========================================== *)
        (red_expr S C (spec_creating_function_object_proto l) o1) ->
        (red_expr S C (spec_creating_function_object_2 str l o1) o) ->
        (* ------------------------------------------ *)
        (red_expr S0 C (spec_creating_function_object_1 str l (out_ter S ((resvalue_value (value_prim (prim_bool ((b : provide_this_flag) : bool)))) : res))) o)

  | red_spec_creating_function_object_2_not_strict :
      forall (S0 : state (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (l : object_loc (* input *)) (b : bool (* input *)),
        (* ========================================== *)
        (* ------------------------------------------ *)
        (red_expr S0 C (spec_creating_function_object_2 (((false : provide_this_flag) : bool) : strictness_flag) l (out_ter S ((resvalue_value (value_prim (prim_bool ((b : provide_this_flag) : bool)))) : res))) (out_ter S ((resvalue_value (value_object l)) : res)))

  | red_spec_creating_function_object_2_strict :
      forall (S0 : state (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (vthrower : value) (l : object_loc (* input *)) (b : bool (* input *)) (o1 : out) (o : out),
        (vthrower = (value_object (object_loc_prealloc prealloc_throw_type_error))) ->
        (* ========================================== *)
        (red_expr S C (spec_object_define_own_prop l ((("caller")%string) : prop_name) (descriptor_of_attributes (attributes_accessor_of (attributes_accessor_intro vthrower vthrower false false))) false) o1) ->
        (red_expr S C (spec_creating_function_object_3 l o1) o) ->
        (* ------------------------------------------ *)
        (red_expr S0 C (spec_creating_function_object_2 (((true : provide_this_flag) : bool) : strictness_flag) l (out_ter S ((resvalue_value (value_prim (prim_bool ((b : provide_this_flag) : bool)))) : res))) o)

  | red_spec_creating_function_object_3 :
      forall (S0 : state (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (vthrower : value) (l : object_loc (* input *)) (b : bool (* input *)) (o1 : out) (o : out),
        (vthrower = (value_object (object_loc_prealloc prealloc_throw_type_error))) ->
        (* ========================================== *)
        (red_expr S C (spec_object_define_own_prop l ((("arguments")%string) : prop_name) (descriptor_of_attributes (attributes_accessor_of (attributes_accessor_intro vthrower vthrower false false))) false) o1) ->
        (red_expr S C (spec_creating_function_object_4 l o1) o) ->
        (* ------------------------------------------ *)
        (red_expr S0 C (spec_creating_function_object_3 l (out_ter S ((resvalue_value (value_prim (prim_bool ((b : provide_this_flag) : bool)))) : res))) o)

  | red_spec_creating_function_object_4 :
      forall (S0 : state (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (l : object_loc (* input *)) (b : bool (* input *)),
        (* ========================================== *)
        (* ------------------------------------------ *)
        (red_expr S0 C (spec_creating_function_object_4 l (out_ter S ((resvalue_value (value_prim (prim_bool ((b : provide_this_flag) : bool)))) : res))) (out_ter S ((resvalue_value (value_object l)) : res)))

  | red_spec_call_1_default :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (l : object_loc (* input *)) (this : value (* input *)) (args : (list value) (* input *)) (o : out),
        (* ========================================== *)
        (red_expr S C (spec_call_default l this args) o) ->
        (* ------------------------------------------ *)
        (red_expr S C (spec_call_1 call_default l this args) o)

  | red_spec_call_default :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (l : object_loc (* input *)) (this : value (* input *)) (args : (list value) (* input *)) (o : out),
        (* ========================================== *)
        (red_expr S C (spec_entering_func_code l this args (spec_call_default_1 l)) o) ->
        (* ------------------------------------------ *)
        (red_expr S C (spec_call_default l this args) o)

  | red_spec_call_default_1 :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (l : object_loc (* input *)) (bdo : (option funcbody)) (o : out),
        (object_method object_code_ S l bdo) ->
        (* ========================================== *)
        (red_expr S C (spec_call_default_2 bdo) o) ->
        (* ------------------------------------------ *)
        (red_expr S C (spec_call_default_1 l) o)

  | red_spec_call_default_2_body :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (bd : _ (* input *)) (o1 : out) (o : out),
        (funcbody_empty bd) ->
        (* ========================================== *)
        (red_prog S C ((funcbody_prog bd) : ext_prog) o1) ->
        (red_expr S C (spec_call_default_3 o1) o) ->
        (* ------------------------------------------ *)
        (red_expr S C (spec_call_default_2 ((Some bd) : (option funcbody))) o)

  | red_spec_call_default_2_empty_body :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (bdo : (option funcbody) (* input *)) (o : out),
        match bdo with None => True | (Some bd) => (funcbody_empty bd) end ->
        (* ========================================== *)
        (red_expr S C (spec_call_default_3 (out_ter S (res_normal (resvalue_value undef)))) o) ->
        (* ------------------------------------------ *)
        (red_expr S C (spec_call_default_2 bdo) o)

  | red_spec_call_default_3_return :
      forall (S0 : state (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (rv : resvalue (* input *)),
        (* ========================================== *)
        (* ------------------------------------------ *)
        (red_expr S0 C (spec_call_default_3 (out_ter S (res_intro restype_return rv label_empty))) (out_ter S (rv : res)))

  | red_spec_call_default_3_normal :
      forall (S0 : state (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (rv : resvalue (* input *)),
        (* ========================================== *)
        (* ------------------------------------------ *)
        (red_expr S0 C (spec_call_default_3 (out_ter S (res_intro restype_normal rv label_empty))) (out_ter S ((resvalue_value undef) : res)))

  | red_spec_construct_1_default :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (l : object_loc (* input *)) (args : (list value) (* input *)) (o : out),
        (* ========================================== *)
        (red_expr S C (spec_construct_default l args) o) ->
        (* ------------------------------------------ *)
        (red_expr S C (spec_construct_1 construct_default l args) o)

  | red_spec_construct_default :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (l : object_loc (* input *)) (args : (list value) (* input *)) (o1 : out) (o : out),
        (* ========================================== *)
        (red_expr S C (spec_object_get (value_object l) ((("prototype")%string) : prop_name)) o1) ->
        (red_expr S C (spec_construct_default_1 l args o1) o) ->
        (* ------------------------------------------ *)
        (red_expr S C (spec_construct_default l args) o)

  | red_spec_construct_default_1 :
      forall (S0 : state (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (vproto : value) (l : object_loc (* input *)) (args : (list value) (* input *)) (v : value (* input *)) (o1 : out) (o : out),
        (vproto = (ifb (((type_of v) : type) = type_object) then v else (value_object (object_loc_prealloc prealloc_object_proto)))) ->
        (* ========================================== *)
        (red_expr ((snd ((object_alloc S ((object_new vproto (("Object")%string)) : object)) : (object_loc * state))) : state) C (spec_call l (value_object ((fst ((object_alloc S ((object_new vproto (("Object")%string)) : object)) : (object_loc * state))) : object_loc)) args) o1) ->
        (red_expr ((snd ((object_alloc S ((object_new vproto (("Object")%string)) : object)) : (object_loc * state))) : state) C (spec_construct_default_2 ((fst ((object_alloc S ((object_new vproto (("Object")%string)) : object)) : (object_loc * state))) : object_loc) o1) o) ->
        (* ------------------------------------------ *)
        (red_expr S0 C (spec_construct_default_1 l args (out_ter S ((resvalue_value v) : res))) o)

  | red_spec_function_construct_2 :
      forall (S0 : state (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (l' : object_loc (* input *)) (v : value (* input *)),
        (* ========================================== *)
        (* ------------------------------------------ *)
        (red_expr S0 C (spec_construct_default_2 l' (out_ter S ((resvalue_value v) : res))) (out_ter S ((resvalue_value (ifb (((type_of v) : type) = type_object) then v else (value_object l'))) : res)))

  | red_spec_create_new_function_in :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (args : (list string) (* input *)) (bd : funcbody (* input *)) (o : out),
        (* ========================================== *)
        (red_expr S C (spec_creating_function_object args bd (execution_ctx_lexical_env C) (execution_ctx_strict C)) o) ->
        (* ------------------------------------------ *)
        (red_expr S C (spec_create_new_function_in C args bd) o)

  | red_spec_from_descriptor_undef :
      forall (S0 : state (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)),
        (* ========================================== *)
        (* ------------------------------------------ *)
        (red_expr S0 C (spec_from_descriptor ((specret_val S full_descriptor_undef) : (specret full_descriptor))) (out_ter S ((resvalue_value undef) : res)))

  | red_spec_from_descriptor_some :
      forall (S0 : state (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (A : attributes (* input *)) (o : out) (o1 : out),
        (* ========================================== *)
        (red_expr S C (spec_construct_prealloc prealloc_object (nil : (list value))) o1) ->
        (red_expr S C (spec_from_descriptor_1 A o1) o) ->
        (* ------------------------------------------ *)
        (red_expr S0 C (spec_from_descriptor ((specret_val S (full_descriptor_some A)) : (specret full_descriptor))) o)

  | red_spec_from_descriptor_1_data :
      forall (S0 : state (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (Ad : attributes_data (* input *)) (l : object_loc (* input *)) (o : out) (o1 : out),
        (* ========================================== *)
        (red_expr S C (spec_object_define_own_prop l ((("value")%string) : prop_name) ((descriptor_of_attributes (attributes_data_of (attributes_data_intro_all_true (attributes_data_value Ad)))) : descriptor) (throw_false : bool)) o1) ->
        (red_expr S C (spec_from_descriptor_2 l Ad o1) o) ->
        (* ------------------------------------------ *)
        (red_expr S0 C (spec_from_descriptor_1 (attributes_data_of Ad) (out_ter S ((resvalue_value (value_object l)) : res))) o)

  | red_spec_from_descriptor_2_data :
      forall (S0 : state (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (Ad : attributes_data (* input *)) (l : object_loc (* input *)) (b : bool (* input *)) (o : out) (o1 : out),
        (* ========================================== *)
        (red_expr S C (spec_object_define_own_prop l ((("writable")%string) : prop_name) ((descriptor_of_attributes (attributes_data_of (attributes_data_intro_all_true (value_prim (prim_bool (((attributes_data_writable Ad) : provide_this_flag) : bool)))))) : descriptor) (throw_false : bool)) o1) ->
        (red_expr S C (spec_from_descriptor_4 l (attributes_data_of Ad) o1) o) ->
        (* ------------------------------------------ *)
        (red_expr S0 C (spec_from_descriptor_2 l Ad (out_ter S ((resvalue_value (value_prim (prim_bool ((b : provide_this_flag) : bool)))) : res))) o)

  | red_spec_from_descriptor_1_accessor :
      forall (S0 : state (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (Aa : attributes_accessor (* input *)) (l : object_loc (* input *)) (o : out) (o1 : out),
        (* ========================================== *)
        (red_expr S C (spec_object_define_own_prop l ((("get")%string) : prop_name) ((descriptor_of_attributes (attributes_data_of (attributes_data_intro_all_true (attributes_accessor_get Aa)))) : descriptor) (throw_false : bool)) o1) ->
        (red_expr S C (spec_from_descriptor_3 l Aa o1) o) ->
        (* ------------------------------------------ *)
        (red_expr S0 C (spec_from_descriptor_1 (attributes_accessor_of Aa) (out_ter S ((resvalue_value (value_object l)) : res))) o)

  | red_spec_from_descriptor_3_accessor :
      forall (S0 : state (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (Aa : attributes_accessor (* input *)) (l : object_loc (* input *)) (b : bool (* input *)) (o : out) (o1 : out),
        (* ========================================== *)
        (red_expr S C (spec_object_define_own_prop l ((("set")%string) : prop_name) ((descriptor_of_attributes (attributes_data_of (attributes_data_intro_all_true (attributes_accessor_set Aa)))) : descriptor) (throw_false : bool)) o1) ->
        (red_expr S C (spec_from_descriptor_4 l (attributes_accessor_of Aa) o1) o) ->
        (* ------------------------------------------ *)
        (red_expr S0 C (spec_from_descriptor_3 l Aa (out_ter S ((resvalue_value (value_prim (prim_bool ((b : provide_this_flag) : bool)))) : res))) o)

  | red_spec_from_descriptor_4 :
      forall (S0 : state (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (A : attributes (* input *)) (l : object_loc (* input *)) (b : bool (* input *)) (o : out) (o1 : out),
        (* ========================================== *)
        (red_expr S C (spec_object_define_own_prop l ((("enumerable")%string) : prop_name) ((descriptor_of_attributes (attributes_data_of (attributes_data_intro_all_true (value_prim (prim_bool (((attributes_enumerable A) : provide_this_flag) : bool)))))) : descriptor) (throw_false : bool)) o1) ->
        (red_expr S C (spec_from_descriptor_5 l A o1) o) ->
        (* ------------------------------------------ *)
        (red_expr S0 C (spec_from_descriptor_4 l A (out_ter S ((resvalue_value (value_prim (prim_bool ((b : provide_this_flag) : bool)))) : res))) o)

  | red_spec_from_descriptor_5 :
      forall (S0 : state (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (A : attributes (* input *)) (l : object_loc (* input *)) (b : bool (* input *)) (o : out) (o1 : out),
        (* ========================================== *)
        (red_expr S C (spec_object_define_own_prop l ((("configurable")%string) : prop_name) ((descriptor_of_attributes (attributes_data_of (attributes_data_intro_all_true (value_prim (prim_bool (((attributes_configurable A) : provide_this_flag) : bool)))))) : descriptor) (throw_false : bool)) o1) ->
        (red_expr S C (spec_from_descriptor_6 l o1) o) ->
        (* ------------------------------------------ *)
        (red_expr S0 C (spec_from_descriptor_5 l A (out_ter S ((resvalue_value (value_prim (prim_bool ((b : provide_this_flag) : bool)))) : res))) o)

  | red_spec_from_descriptor_6 :
      forall (S0 : state (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (l : object_loc (* input *)) (b : bool (* input *)),
        (* ========================================== *)
        (* ------------------------------------------ *)
        (red_expr S0 C (spec_from_descriptor_6 l (out_ter S ((resvalue_value (value_prim (prim_bool ((b : provide_this_flag) : bool)))) : res))) (out_ter S ((resvalue_value (value_object l)) : res)))

  | red_spec_call_throw_type_error :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (o : out) (vthis : value (* input *)) (args : (list value) (* input *)),
        (* ========================================== *)
        (red_expr S C (spec_error native_error_type) o) ->
        (* ------------------------------------------ *)
        (red_expr S C (spec_call_prealloc prealloc_throw_type_error vthis args) o)

  | red_spec_call_global_eval :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (bdirect : bool (* input *)) (args : (list value) (* input *)) (v : value) (o : out),
        (arguments_from args (v :: (nil : (list value)))) ->
        (* ========================================== *)
        (red_expr S C (spec_call_global_eval_1 bdirect v) o) ->
        (* ------------------------------------------ *)
        (red_expr S C (spec_call_global_eval bdirect args) o)

  | red_spec_call_global_eval_1_not_string :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (bdirect : bool (* input *)) (v : value (* input *)),
        (((type_of v) : type) <> type_string) ->
        (* ========================================== *)
        (* ------------------------------------------ *)
        (red_expr S C (spec_call_global_eval_1 bdirect v) (out_ter S ((resvalue_value v) : res)))

  | red_spec_call_global_eval_1_string_not_parse :
      forall (s : string (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (bdirect : bool (* input *)) (o : out),
        (parse s (None : (option prog))) ->
        (* ========================================== *)
        (red_expr S C (spec_error native_error_syntax) o) ->
        (* ------------------------------------------ *)
        (red_expr S C (spec_call_global_eval_1 bdirect (value_prim (prim_string s))) o)

  | red_spec_call_global_eval_1_string_parse :
      forall (s : string (* input *)) (p : prog) (S : state (* input *)) (C : execution_ctx (* input *)) (bdirect : bool (* input *)) (o : out),
        (parse s ((Some p) : (option prog))) ->
        (* ========================================== *)
        (red_expr S C (spec_entering_eval_code bdirect (funcbody_intro p s) (spec_call_global_eval_2 p)) o) ->
        (* ------------------------------------------ *)
        (red_expr S C (spec_call_global_eval_1 bdirect (value_prim (prim_string s))) o)

  | red_spec_call_global_eval_2 :
      forall (o1 : out) (S : state (* input *)) (C : execution_ctx (* input *)) (p : prog (* input *)) (o : out),
        (* ========================================== *)
        (red_prog S C (prog_basic p) o1) ->
        (red_expr S C (spec_call_global_eval_3 o1) o) ->
        (* ------------------------------------------ *)
        (red_expr S C (spec_call_global_eval_2 p) o)

  | red_spec_call_global_eval_3_normal_value :
      forall (S0 : state (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (v : value (* input *)),
        (* ========================================== *)
        (* ------------------------------------------ *)
        (red_expr S0 C (spec_call_global_eval_3 (out_ter S ((resvalue_value v) : res))) (out_ter S ((resvalue_value v) : res)))

  | red_spec_call_global_eval_3_normal_empty :
      forall (S0 : state (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (R : res (* input *)),
        ((res_type R) = restype_normal) ->
        ((res_value R) = resvalue_empty) ->
        (* ========================================== *)
        (* ------------------------------------------ *)
        (red_expr S0 C (spec_call_global_eval_3 (out_ter S R)) (out_ter S ((resvalue_value undef) : res)))

  | red_spec_call_global_eval_3_throw :
      forall (S0 : state (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (R : res (* input *)),
        ((res_type R) = restype_throw) ->
        (* ========================================== *)
        (* ------------------------------------------ *)
        (red_expr S0 C (spec_call_global_eval_3 (out_ter S R)) (out_ter S (res_throw (res_value R))))

  | red_spec_call_global_is_nan :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (v : value) (o : out) (o1 : out) (vthis : value (* input *)) (args : (list value) (* input *)),
        (arguments_from args (v :: (nil : (list value)))) ->
        (* ========================================== *)
        (red_expr S C (spec_to_number v) o1) ->
        (red_expr S C (spec_call_global_is_nan_1 o1) o) ->
        (* ------------------------------------------ *)
        (red_expr S C (spec_call_prealloc prealloc_global_is_nan vthis args) o)

  | red_spec_call_global_is_nan_1 :
      forall (S : state (* input *)) (S0 : state (* input *)) (C : execution_ctx (* input *)) (n : number (* input *)),
        (* ========================================== *)
        (* ------------------------------------------ *)
        (red_expr S0 C (spec_call_global_is_nan_1 (out_ter S ((resvalue_value (value_prim (prim_number n))) : res))) (out_ter S ((resvalue_value (value_prim (prim_bool (((ifb (n = JsNumber.nan) then true else false) : provide_this_flag) : bool)))) : res)))

  | red_spec_call_global_is_finite :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (v : value) (o : out) (o1 : out) (vthis : value (* input *)) (args : (list value) (* input *)),
        (arguments_from args (v :: (nil : (list value)))) ->
        (* ========================================== *)
        (red_expr S C (spec_to_number v) o1) ->
        (red_expr S C (spec_call_global_is_finite_1 o1) o) ->
        (* ------------------------------------------ *)
        (red_expr S C (spec_call_prealloc prealloc_global_is_finite vthis args) o)

  | red_spec_call_global_is_finite_1 :
      forall (S : state (* input *)) (S0 : state (* input *)) (C : execution_ctx (* input *)) (n : number (* input *)),
        (* ========================================== *)
        (* ------------------------------------------ *)
        (red_expr S0 C (spec_call_global_is_finite_1 (out_ter S ((resvalue_value (value_prim (prim_number n))) : res))) (out_ter S ((resvalue_value (value_prim (prim_bool (((ifb (((n = JsNumber.nan) \/ (n = JsNumber.infinity)) \/ (n = JsNumber.neg_infinity)) then false else true) : provide_this_flag) : bool)))) : res)))

  | red_spec_call_object_call :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (vthis : value (* input *)) (args : (list value) (* input *)) (v : value) (o : out),
        (arguments_from args (v :: (nil : (list value)))) ->
        (* ========================================== *)
        (red_expr S C (spec_call_object_call_1 v) o) ->
        (* ------------------------------------------ *)
        (red_expr S C (spec_call_prealloc prealloc_object vthis args) o)

  | red_spec_call_object_call_1_null_or_undef :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (v : value (* input *)) (o : out),
        ((v = null) \/ (v = undef)) ->
        (* ========================================== *)
        (red_expr S C (spec_call_object_new_1 v) o) ->
        (* ------------------------------------------ *)
        (red_expr S C (spec_call_object_call_1 v) o)

  | red_spec_call_object_call_1_other :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (v : value (* input *)) (o : out),
        ((v <> null) /\ (v <> undef)) ->
        (* ========================================== *)
        (red_expr S C (spec_to_object v) o) ->
        (* ------------------------------------------ *)
        (red_expr S C (spec_call_object_call_1 v) o)

  | red_spec_call_object_new :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (args : (list value) (* input *)) (v : value) (o : out),
        (arguments_from args (v :: (nil : (list value)))) ->
        (* ========================================== *)
        (red_expr S C (spec_call_object_new_1 v) o) ->
        (* ------------------------------------------ *)
        (red_expr S C (spec_construct_prealloc prealloc_object args) o)

  | red_spec_call_object_new_1_object :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (v : value (* input *)),
        (* ========================================== *)
        (* ------------------------------------------ *)
        (red_expr S C (spec_call_object_new_1 v) (out_ter S ((resvalue_value v) : res)))

  | red_spec_call_object_new_1_prim :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (v : value (* input *)) (o : out),
        (((((type_of v) : type) = type_string) \/ (((type_of v) : type) = type_bool)) \/ (((type_of v) : type) = type_number)) ->
        (* ========================================== *)
        (red_expr S C (spec_to_object v) o) ->
        (* ------------------------------------------ *)
        (red_expr S C (spec_call_object_new_1 v) o)

  | red_spec_call_object_new_1_null_or_undef :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (v : value (* input *)),
        ((v = null) \/ (v = undef)) ->
        (* ========================================== *)
        (* ------------------------------------------ *)
        (red_expr S C (spec_call_object_new_1 v) (out_ter ((snd ((object_alloc S ((object_new prealloc_object_proto (("Object")%string)) : object)) : (object_loc * state))) : state) ((fst ((object_alloc S ((object_new prealloc_object_proto (("Object")%string)) : object)) : (object_loc * state))) : res)))

  | red_spec_call_object_get_proto_of :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (v : value) (vthis : value (* input *)) (args : (list value) (* input *)) (o : out),
        (arguments_from args (v :: (nil : (list value)))) ->
        (* ========================================== *)
        (red_expr S C (spec_call_object_get_proto_of_1 v) o) ->
        (* ------------------------------------------ *)
        (red_expr S C (spec_call_prealloc prealloc_object_get_proto_of vthis args) o)

  | red_spec_call_object_get_proto_of_1_not_object :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (w : prim (* input *)) (o : out),
        (* ========================================== *)
        (red_expr S C (spec_error native_error_type) o) ->
        (* ------------------------------------------ *)
        (red_expr S C (spec_call_object_get_proto_of_1 (value_prim w)) o)

  | red_spec_call_object_get_proto_of_1_object :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (l : object_loc (* input *)) (v : value),
        (object_proto S l v) ->
        (* ========================================== *)
        (* ------------------------------------------ *)
        (red_expr S C (spec_call_object_get_proto_of_1 (value_object l)) (out_ter S ((resvalue_value v) : res)))

  | red_spec_call_object_get_own_prop_descriptor :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (vo : value) (vx : value) (o : out) (vthis : value (* input *)) (args : (list value) (* input *)),
        (arguments_from args (vo :: (vx :: nil))) ->
        (* ========================================== *)
        (red_expr S C (spec_call_object_get_own_prop_descriptor_1 vo vx) o) ->
        (* ------------------------------------------ *)
        (red_expr S C (spec_call_prealloc prealloc_object_get_own_prop_descriptor vthis args) o)

  | red_spec_call_object_get_own_prop_descriptor_1_not_object :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (vo : value (* input *)) (vx : value (* input *)) (o : out),
        (((type_of vo) : type) <> type_object) ->
        (* ========================================== *)
        (red_expr S C (spec_error native_error_type) o) ->
        (* ------------------------------------------ *)
        (red_expr S C (spec_call_object_get_own_prop_descriptor_1 vo vx) o)

  | red_spec_call_object_get_own_prop_descriptor_1_object :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (l : object_loc (* input *)) (vx : value (* input *)) (o : out) (o1 : out),
        (* ========================================== *)
        (red_expr S C (spec_to_string vx) o1) ->
        (red_expr S C (spec_call_object_get_own_prop_descriptor_2 l o1) o) ->
        (* ------------------------------------------ *)
        (red_expr S C (spec_call_object_get_own_prop_descriptor_1 (value_object l) vx) o)

  | red_spec_call_object_get_own_prop_descriptor_2 :
      forall (S0 : state (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (l : object_loc (* input *)) (x : prop_name (* input *)) (o : out) (y : (specret full_descriptor)),
        (* ========================================== *)
        (red_spec S C (spec_object_get_own_prop l x) y) ->
        (red_expr S C (spec_from_descriptor y) o) ->
        (* ------------------------------------------ *)
        (red_expr S0 C (spec_call_object_get_own_prop_descriptor_2 l (out_ter S ((resvalue_value (value_prim (prim_string (x : string)))) : res))) o)

  | red_spec_call_object_object_create :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (vo : value) (vp : value) (vthis : value (* input *)) (args : (list value) (* input *)) (o : out),
        (arguments_from args (vo :: (vp :: (nil : (list value))))) ->
        (* ========================================== *)
        (red_expr S C (spec_call_object_create_1 vo vp) o) ->
        (* ------------------------------------------ *)
        (red_expr S C (spec_call_prealloc prealloc_object_create vthis args) o)

  | red_spec_call_object_object_create_1_not_object :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (vo : value (* input *)) (vp : value (* input *)) (o : out),
        (((type_of vo) : type) <> type_object) ->
        (((type_of vo) : type) <> type_null) ->
        (* ========================================== *)
        (red_expr S C (spec_error native_error_type) o) ->
        (* ------------------------------------------ *)
        (red_expr S C (spec_call_object_create_1 vo vp) o)

  | red_spec_call_object_object_create_1_object :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (vo : value (* input *)) (vp : value (* input *)) (o : out) (o1 : out),
        (* ========================================== *)
        (red_expr S C (spec_construct_prealloc prealloc_object (nil : (list value))) o1) ->
        (red_expr S C (spec_call_object_create_2 o1 vo vp) o) ->
        (* ------------------------------------------ *)
        (red_expr S C (spec_call_object_create_1 vo vp) o)

  | red_spec_call_object_object_create_2 :
      forall (S : state (* input *)) (S0 : state (* input *)) (C : execution_ctx (* input *)) (l : object_loc (* input *)) (O : object) (vo : value (* input *)) (vp : value (* input *)) (o : out),
        (object_binds S l O) ->
        (* ========================================== *)
        (red_expr ((object_write S l ((object_set_proto O vo) : object)) : state) C (spec_call_object_create_3 l vp) o) ->
        (* ------------------------------------------ *)
        (red_expr S0 C (spec_call_object_create_2 (out_ter S ((resvalue_value (value_object l)) : res)) vo vp) o)

  | red_spec_call_object_object_create_3_def :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (l : object_loc (* input *)) (vp : value (* input *)) (o : out),
        (vp <> undef) ->
        (* ========================================== *)
        (red_expr S C (spec_call_object_define_props_1 (value_object l) vp) o) ->
        (* ------------------------------------------ *)
        (red_expr S C (spec_call_object_create_3 l vp) o)

  | red_spec_call_object_object_create_3_undef :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (l : object_loc (* input *)),
        (* ========================================== *)
        (* ------------------------------------------ *)
        (red_expr S C (spec_call_object_create_3 l undef) (out_ter S ((resvalue_value (value_object l)) : res)))

  | red_spec_call_object_object_define_prop :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (vo : value) (vx : value) (va : value) (o : out) (vthis : value (* input *)) (args : (list value) (* input *)),
        (arguments_from args (vo :: (vx :: (va :: nil)))) ->
        (* ========================================== *)
        (red_expr S C (spec_call_object_define_prop_1 vo vx va) o) ->
        (* ------------------------------------------ *)
        (red_expr S C (spec_call_prealloc prealloc_object_define_prop vthis args) o)

  | red_spec_call_object_object_define_prop_1_not_object :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (vo : value (* input *)) (vx : value (* input *)) (va : value (* input *)) (o : out),
        (((type_of vo) : type) <> type_object) ->
        (* ========================================== *)
        (red_expr S C (spec_error native_error_type) o) ->
        (* ------------------------------------------ *)
        (red_expr S C (spec_call_object_define_prop_1 vo vx va) o)

  | red_spec_call_object_object_define_prop_1_object :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (l : object_loc (* input *)) (vx : value (* input *)) (va : value (* input *)) (o1 : out) (o : out),
        (* ========================================== *)
        (red_expr S C (spec_to_string vx) o1) ->
        (red_expr S C (spec_call_object_define_prop_2 l o1 va) o) ->
        (* ------------------------------------------ *)
        (red_expr S C (spec_call_object_define_prop_1 (value_object l) vx va) o)

  | red_spec_call_object_object_define_prop_2 :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (l : object_loc (* input *)) (x : prop_name (* input *)) (va : value (* input *)) (o : out) (y : (specret descriptor)),
        (* ========================================== *)
        (red_spec S C (spec_to_descriptor va) y) ->
        (red_expr S C (spec_call_object_define_prop_3 l (x : string) y) o) ->
        (* ------------------------------------------ *)
        (red_expr S C (spec_call_object_define_prop_2 l (out_ter S ((resvalue_value (value_prim (prim_string (x : string)))) : res)) va) o)

  | red_spec_call_object_object_define_prop_3 :
      forall (S : state (* input *)) (S0 : state (* input *)) (C : execution_ctx (* input *)) (l : object_loc (* input *)) (s : string (* input *)) (Desc : descriptor (* input *)) (o1 : out) (o : out),
        (* ========================================== *)
        (red_expr S C (spec_object_define_own_prop l (s : prop_name) Desc (throw_true : bool)) o1) ->
        (red_expr S C (spec_call_object_define_prop_4 l o1) o) ->
        (* ------------------------------------------ *)
        (red_expr S0 C (spec_call_object_define_prop_3 l s ((specret_val S Desc) : (specret descriptor))) o)

  | red_spec_call_object_object_define_prop_4 :
      forall (S0 : state (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (l : object_loc (* input *)),
        (* ========================================== *)
        (* ------------------------------------------ *)
        (red_expr S0 C (spec_call_object_define_prop_4 l (out_ter S (res_intro restype_normal resvalue_empty label_empty))) (out_ter S ((resvalue_value (value_object l)) : res)))

  | red_spec_call_object_object_define_props :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (vo : value) (vp : value) (o : out) (vthis : value (* input *)) (args : (list value) (* input *)),
        (arguments_from args (vo :: (vp :: (nil : (list value))))) ->
        (* ========================================== *)
        (red_expr S C (spec_call_object_define_props_1 vo vp) o) ->
        (* ------------------------------------------ *)
        (red_expr S C (spec_call_prealloc prealloc_object_define_props vthis args) o)

  | red_spec_call_object_object_define_props_1_not_object :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (vo : value (* input *)) (vp : value (* input *)) (o : out),
        (((type_of vo) : type) <> type_object) ->
        (* ========================================== *)
        (red_expr S C (spec_error native_error_type) o) ->
        (* ------------------------------------------ *)
        (red_expr S C (spec_call_object_define_props_1 vo vp) o)

  | red_spec_call_object_object_define_props_1_object :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (l : object_loc (* input *)) (vp : value (* input *)) (o : out) (o1 : out),
        (* ========================================== *)
        (red_expr S C (spec_to_object vp) o1) ->
        (red_expr S C (spec_call_object_define_props_2 o1 l) o) ->
        (* ------------------------------------------ *)
        (red_expr S C (spec_call_object_define_props_1 (value_object l) vp) o)

  | red_spec_call_object_object_define_props_2 :
      forall (S0 : state (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (l : object_loc (* input *)) (lp : object_loc (* input *)) (xs : (list prop_name)) (o : out),
        (object_properties_enumerable_keys_as_list S lp xs) ->
        (* ========================================== *)
        (red_expr S C (spec_call_object_define_props_3 l lp xs (nil : (list (prop_name * attributes)))) o) ->
        (* ------------------------------------------ *)
        (red_expr S0 C (spec_call_object_define_props_2 (out_ter S ((resvalue_value (value_object lp)) : res)) l) o)

  | red_spec_call_object_define_props_3_nil :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (l : object_loc (* input *)) (lp : object_loc (* input *)) (Descs : (list (prop_name * attributes)) (* input *)) (o : out),
        (* ========================================== *)
        (red_expr S C (spec_call_object_define_props_6 l Descs) o) ->
        (* ------------------------------------------ *)
        (red_expr S C (spec_call_object_define_props_3 l lp (nil : (list prop_name)) Descs) o)

  | red_spec_call_object_define_props_3_cons :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (l : object_loc (* input *)) (lp : object_loc (* input *)) (x : prop_name (* input *)) (xs : (list prop_name) (* input *)) (Descs : (list (prop_name * attributes)) (* input *)) (o : out) (o1 : out),
        (* ========================================== *)
        (red_expr S C (spec_object_get (value_object lp) x) o1) ->
        (red_expr S C (spec_call_object_define_props_4 o1 l lp x xs Descs) o) ->
        (* ------------------------------------------ *)
        (red_expr S C (spec_call_object_define_props_3 l lp (x :: xs) Descs) o)

  | red_spec_call_object_define_props_4 :
      forall (S0 : state (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (v : value (* input *)) (l : object_loc (* input *)) (lp : object_loc (* input *)) (o : out) (o1 : out) (x : prop_name (* input *)) (xs : (list prop_name) (* input *)) (Descs : (list (prop_name * attributes)) (* input *)) (y : (specret attributes)),
        (* ========================================== *)
        (red_spec S C (spec_to_descriptor v) y) ->
        (red_expr S C (spec_call_object_define_props_5 l lp x xs Descs y) o1) ->
        (* ------------------------------------------ *)
        (red_expr S0 C (spec_call_object_define_props_4 (out_ter S ((resvalue_value v) : res)) l lp x xs Descs) o)

  | red_spec_call_object_define_props_5 :
      forall (S : state (* input *)) (S0 : state (* input *)) (C : execution_ctx (* input *)) (A : attributes (* input *)) (l : object_loc (* input *)) (lp : object_loc (* input *)) (o : out) (x : prop_name (* input *)) (xs : (list prop_name) (* input *)) (xAs : (list (prop_name * attributes)) (* input *)),
        (* ========================================== *)
        (red_expr S C (spec_call_object_define_props_3 l lp xs (xAs ++ ((x, A) :: (nil : (list (prop_name * attributes)))))) o) ->
        (* ------------------------------------------ *)
        (red_expr S0 C (spec_call_object_define_props_5 l lp x xs xAs ((specret_val S A) : (specret attributes))) o)

  | red_spec_call_object_define_props_6_cons :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (l : object_loc (* input *)) (x : prop_name (* input *)) (A : attributes (* input *)) (xAs : (list (prop_name * attributes)) (* input *)) (o1 : out) (o : out),
        (* ========================================== *)
        (red_expr S C (spec_object_define_own_prop l x ((descriptor_of_attributes A) : descriptor) (throw_true : bool)) o1) ->
        (red_expr S C (spec_call_object_define_props_7 o1 l xAs) o) ->
        (* ------------------------------------------ *)
        (red_expr S C (spec_call_object_define_props_6 l ((x, A) :: xAs)) o)

  | red_spec_call_object_define_props_7 :
      forall (S0 : state (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (l : object_loc (* input *)) (xAs : (list (prop_name * attributes)) (* input *)) (b : bool (* input *)) (o : out),
        (* ========================================== *)
        (red_expr S C (spec_call_object_define_props_6 l xAs) o) ->
        (* ------------------------------------------ *)
        (red_expr S0 C (spec_call_object_define_props_7 (out_ter S ((resvalue_value (value_prim (prim_bool ((b : provide_this_flag) : bool)))) : res)) l xAs) o)

  | red_spec_call_object_define_props_6_nil :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (l : object_loc (* input *)),
        (* ========================================== *)
        (* ------------------------------------------ *)
        (red_expr S C (spec_call_object_define_props_6 l (nil : (list (prop_name * attributes)))) (out_ter S ((resvalue_value (value_object l)) : res)))

  | red_spec_call_object_seal :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (v : value) (o : out) (vthis : value (* input *)) (args : (list value) (* input *)),
        (arguments_from args (v :: (nil : (list value)))) ->
        (* ========================================== *)
        (red_expr S C (spec_call_object_seal_1 v) o) ->
        (* ------------------------------------------ *)
        (red_expr S C (spec_call_prealloc prealloc_object_seal vthis args) o)

  | red_spec_call_object_seal_1_not_object :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (v : value (* input *)) (o : out),
        (((type_of v) : type) <> type_object) ->
        (* ========================================== *)
        (red_expr S C (spec_error native_error_type) o) ->
        (* ------------------------------------------ *)
        (red_expr S C (spec_call_object_seal_1 v) o)

  | red_spec_call_object_seal_1_object :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (l : object_loc (* input *)) (xs : (list prop_name)) (o : out),
        (object_properties_keys_as_list S l xs) ->
        (* ========================================== *)
        (red_expr S C (spec_call_object_seal_2 l xs) o) ->
        (* ------------------------------------------ *)
        (red_expr S C (spec_call_object_seal_1 (value_object l)) o)

  | red_spec_call_object_seal_2_cons :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (l : object_loc (* input *)) (xs : (list prop_name) (* input *)) (x : prop_name (* input *)) (o : out) (y : (specret full_descriptor)),
        (* ========================================== *)
        (red_spec S C (spec_object_get_own_prop l x) y) ->
        (red_expr S C (spec_call_object_seal_3 l x xs y) o) ->
        (* ------------------------------------------ *)
        (red_expr S C (spec_call_object_seal_2 l (x :: xs)) o)

  | red_spec_call_object_seal_3 :
      forall (S0 : state (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (l : object_loc (* input *)) (xs : (list prop_name) (* input *)) (x : prop_name (* input *)) (A : attributes (* input *)) (o1 : out) (o : out),
        (* ========================================== *)
        (red_expr S C (spec_object_define_own_prop l x ((descriptor_of_attributes (ifb (attributes_configurable A) then ((attributes_with_configurable A false) : attributes) else A)) : descriptor) (throw_true : bool)) o1) ->
        (red_expr S C (spec_call_object_seal_4 l xs o1) o) ->
        (* ------------------------------------------ *)
        (red_expr S C (spec_call_object_seal_3 l x xs ((specret_val S0 (full_descriptor_some A)) : (specret full_descriptor))) (out_ter S ((resvalue_value (value_prim (prim_bool ((false : provide_this_flag) : bool)))) : res)))

  | red_spec_call_object_seal_4 :
      forall (S0 : state (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (l : object_loc (* input *)) (xs : (list prop_name) (* input *)) (b : bool (* input *)) (o : out),
        (* ========================================== *)
        (red_expr S C (spec_call_object_seal_2 l xs) o) ->
        (* ------------------------------------------ *)
        (red_expr S0 C (spec_call_object_seal_4 l xs (out_ter S ((resvalue_value (value_prim (prim_bool ((b : provide_this_flag) : bool)))) : res))) o)

  | red_spec_call_object_seal_2_nil :
      forall (S : state (* input *)) (S' : state) (C : execution_ctx (* input *)) (l : object_loc (* input *)),
        (object_heap_set_extensible false S l S') ->
        (* ========================================== *)
        (* ------------------------------------------ *)
        (red_expr S C (spec_call_object_seal_2 l (nil : (list prop_name))) (out_ter S' ((resvalue_value (value_object l)) : res)))

  | red_spec_call_object_freeze :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (v : value) (o : out) (vthis : value (* input *)) (args : (list value) (* input *)),
        (arguments_from args (v :: (nil : (list value)))) ->
        (* ========================================== *)
        (red_expr S C (spec_call_object_freeze_1 v) o) ->
        (* ------------------------------------------ *)
        (red_expr S C (spec_call_prealloc prealloc_object_freeze vthis args) o)

  | red_spec_call_object_freeze_1_not_object :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (v : value (* input *)) (o : out),
        (((type_of v) : type) <> type_object) ->
        (* ========================================== *)
        (red_expr S C (spec_error native_error_type) o) ->
        (* ------------------------------------------ *)
        (red_expr S C (spec_call_object_freeze_1 v) o)

  | red_spec_call_object_freeze_1_object :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (l : object_loc (* input *)) (xs : (list prop_name)) (o : out),
        (object_properties_keys_as_list S l xs) ->
        (* ========================================== *)
        (red_expr S C (spec_call_object_freeze_2 l xs) o) ->
        (* ------------------------------------------ *)
        (red_expr S C (spec_call_object_freeze_1 (value_object l)) o)

  | red_spec_call_object_freeze_2_cons :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (l : object_loc (* input *)) (xs : (list prop_name) (* input *)) (x : prop_name (* input *)) (o : out) (y : (specret full_descriptor)),
        (* ========================================== *)
        (red_spec S C (spec_object_get_own_prop l x) y) ->
        (red_expr S C (spec_call_object_freeze_3 l x xs y) o) ->
        (* ------------------------------------------ *)
        (red_expr S C (spec_call_object_freeze_2 l (x :: xs)) o)

  | red_spec_call_object_freeze_3 :
      forall (S0 : state (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (A : attributes (* input *)) (xs : (list prop_name) (* input *)) (l : object_loc (* input *)) (x : prop_name (* input *)) (o : out),
        (* ========================================== *)
        (red_expr S C (spec_call_object_freeze_4 l x xs (full_descriptor_some match A return attributes with (attributes_data_of Ad) => (attributes_data_of ((ifb (attributes_data_writable (Ad : attributes_data)) then ((attributes_data_with_writable Ad false) : attributes_data) else Ad) : attributes_data)) | (attributes_accessor_of Aa) => (attributes_accessor_of (Aa : attributes_accessor)) end)) o) ->
        (* ------------------------------------------ *)
        (red_expr S C (spec_call_object_freeze_3 l x xs ((specret_val S0 (full_descriptor_some A)) : (specret full_descriptor))) o)

  | red_spec_call_object_freeze_4 :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (A : attributes (* input *)) (xs : (list prop_name) (* input *)) (l : object_loc (* input *)) (x : prop_name (* input *)) (o1 : out) (o : out),
        (* ========================================== *)
        (red_expr S C (spec_object_define_own_prop l x ((descriptor_of_attributes (ifb (attributes_configurable A) then ((attributes_with_configurable A false) : attributes) else A)) : descriptor) (throw_true : bool)) o1) ->
        (red_expr S C (spec_call_object_freeze_5 l xs o1) o) ->
        (* ------------------------------------------ *)
        (red_expr S C (spec_call_object_freeze_4 l x xs (full_descriptor_some A)) o)

  | red_spec_call_object_freeze_5 :
      forall (S0 : state (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (xs : (list prop_name) (* input *)) (l : object_loc (* input *)) (b : bool (* input *)) (o : out),
        (* ========================================== *)
        (red_expr S C (spec_call_object_freeze_2 l xs) o) ->
        (* ------------------------------------------ *)
        (red_expr S0 C (spec_call_object_freeze_5 l xs (out_ter S ((resvalue_value (value_prim (prim_bool ((b : provide_this_flag) : bool)))) : res))) o)

  | red_spec_call_object_freeze_2_nil :
      forall (S : state (* input *)) (S' : state) (C : execution_ctx (* input *)) (l : object_loc (* input *)),
        (object_heap_set_extensible false S l S') ->
        (* ========================================== *)
        (* ------------------------------------------ *)
        (red_expr S C (spec_call_object_freeze_2 l (nil : (list prop_name))) (out_ter S' ((resvalue_value (value_object l)) : res)))

  | red_spec_call_object_prevent_extensions :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (v : value) (o : out) (vthis : value (* input *)) (args : (list value) (* input *)),
        (arguments_from args (v :: (nil : (list value)))) ->
        (* ========================================== *)
        (red_expr S C (spec_call_object_prevent_extensions_1 v) o) ->
        (* ------------------------------------------ *)
        (red_expr S C (spec_call_prealloc prealloc_object_prevent_extensions vthis args) o)

  | red_spec_call_object_prevent_extensions_not_object :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (v : value (* input *)) (o : out),
        (((type_of v) : type) <> type_object) ->
        (* ========================================== *)
        (red_expr S C (spec_error native_error_type) o) ->
        (* ------------------------------------------ *)
        (red_expr S C (spec_call_object_prevent_extensions_1 v) o)

  | red_spec_call_object_prevent_extensions_object :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (O : object) (l : object_loc (* input *)),
        (object_binds S l O) ->
        (* ========================================== *)
        (* ------------------------------------------ *)
        (red_expr S C (spec_call_object_prevent_extensions_1 (value_object l)) (out_ter ((object_write S l ((object_with_extension O false) : object)) : state) ((resvalue_value (value_object l)) : res)))

  | red_spec_call_object_is_sealed :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (v : value) (o : out) (vthis : value (* input *)) (args : (list value) (* input *)),
        (arguments_from args (v :: (nil : (list value)))) ->
        (* ========================================== *)
        (red_expr S C (spec_call_object_is_sealed_1 v) o) ->
        (* ------------------------------------------ *)
        (red_expr S C (spec_call_prealloc prealloc_object_is_sealed vthis args) o)

  | red_spec_call_object_is_sealed_1_not_object :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (v : value (* input *)) (o : out),
        (((type_of v) : type) <> type_object) ->
        (* ========================================== *)
        (red_expr S C (spec_error native_error_type) o) ->
        (* ------------------------------------------ *)
        (red_expr S C (spec_call_object_is_sealed_1 v) o)

  | red_spec_call_object_is_sealed_1_object :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (l : object_loc (* input *)) (xs : (list prop_name)) (o : out),
        (object_properties_keys_as_list S l xs) ->
        (* ========================================== *)
        (red_expr S C (spec_call_object_is_sealed_2 l xs) o) ->
        (* ------------------------------------------ *)
        (red_expr S C (spec_call_object_is_sealed_1 (value_object l)) o)

  | red_spec_call_object_is_sealed_2_cons :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (l : object_loc (* input *)) (xs : (list prop_name) (* input *)) (x : prop_name (* input *)) (o : out) (y : (specret full_descriptor)),
        (* ========================================== *)
        (red_spec S C (spec_object_get_own_prop l x) y) ->
        (red_expr S C (spec_call_object_is_sealed_3 l xs y) o) ->
        (* ------------------------------------------ *)
        (red_expr S C (spec_call_object_is_sealed_2 l (x :: xs)) o)

  | red_spec_call_object_is_sealed_3_prop_configurable :
      forall (S0 : state (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (A : attributes (* input *)) (xs : (list prop_name) (* input *)) (l : object_loc (* input *)),
        ((attributes_configurable A) = true) ->
        (* ========================================== *)
        (* ------------------------------------------ *)
        (red_expr S C (spec_call_object_is_sealed_3 l xs ((specret_val S0 (full_descriptor_some A)) : (specret full_descriptor))) (out_ter S ((resvalue_value (value_prim (prim_bool ((false : provide_this_flag) : bool)))) : res)))

  | red_spec_call_object_is_sealed_3_prop_not_configurable :
      forall (S0 : state (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (A : attributes (* input *)) (xs : (list prop_name) (* input *)) (l : object_loc (* input *)) (o : out),
        ((attributes_configurable A) = false) ->
        (* ========================================== *)
        (red_expr S C (spec_call_object_is_sealed_2 l xs) o) ->
        (* ------------------------------------------ *)
        (red_expr S C (spec_call_object_is_sealed_3 l xs ((specret_val S0 (full_descriptor_some A)) : (specret full_descriptor))) o)

  | red_spec_call_object_is_sealed_2_nil :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (l : object_loc (* input *)) (b : bool),
        (object_extensible S l b) ->
        (* ========================================== *)
        (* ------------------------------------------ *)
        (red_expr S C (spec_call_object_is_sealed_2 l (nil : (list prop_name))) (out_ter S ((negb b) : res)))

  | red_spec_call_object_is_frozen :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (v : value) (o : out) (vthis : value (* input *)) (args : (list value) (* input *)),
        (arguments_from args (v :: (nil : (list value)))) ->
        (* ========================================== *)
        (red_expr S C (spec_call_object_is_frozen_1 v) o) ->
        (* ------------------------------------------ *)
        (red_expr S C (spec_call_prealloc prealloc_object_is_frozen vthis args) o)

  | red_spec_call_object_is_frozen_1_not_object :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (v : value (* input *)) (o : out),
        (((type_of v) : type) <> type_object) ->
        (* ========================================== *)
        (red_expr S C (spec_error native_error_type) o) ->
        (* ------------------------------------------ *)
        (red_expr S C (spec_call_object_is_frozen_1 v) o)

  | red_spec_call_object_is_frozen_1_object :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (l : object_loc (* input *)) (xs : (list prop_name)) (o : out),
        (object_properties_keys_as_list S l xs) ->
        (* ========================================== *)
        (red_expr S C (spec_call_object_is_frozen_2 l xs) o) ->
        (* ------------------------------------------ *)
        (red_expr S C (spec_call_object_is_frozen_1 (value_object l)) o)

  | red_spec_call_object_is_frozen_2_cons :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (l : object_loc (* input *)) (xs : (list prop_name) (* input *)) (x : prop_name (* input *)) (o : out) (y : (specret full_descriptor)),
        (* ========================================== *)
        (red_spec S C (spec_object_get_own_prop l x) y) ->
        (red_expr S C (spec_call_object_is_frozen_3 l xs y) o) ->
        (* ------------------------------------------ *)
        (red_expr S C (spec_call_object_is_frozen_2 l (x :: xs)) o)

  | red_spec_call_object_is_frozen_3_desc_is_data :
      forall (S0 : state (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (A : attributes (* input *)) (xs : (list prop_name) (* input *)) (l : object_loc (* input *)) (o : out),
        ((attributes_is_data A) = (istrue ((((true : provide_this_flag) : bool) : strictness_flag) : bool))) ->
        (* ========================================== *)
        (red_expr S C (spec_call_object_is_frozen_4 l xs (full_descriptor_some A)) o) ->
        (* ------------------------------------------ *)
        (red_expr S C (spec_call_object_is_frozen_3 l xs ((specret_val S0 (full_descriptor_some A)) : (specret full_descriptor))) o)

  | red_spec_call_object_is_frozen_3_desc_is_not_data :
      forall (S0 : state (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (A : attributes (* input *)) (xs : (list prop_name) (* input *)) (l : object_loc (* input *)) (o : out),
        ((attributes_is_data A) = (istrue ((((false : provide_this_flag) : bool) : strictness_flag) : bool))) ->
        (* ========================================== *)
        (red_expr S C (spec_call_object_is_frozen_5 l xs (full_descriptor_some A)) o) ->
        (* ------------------------------------------ *)
        (red_expr S C (spec_call_object_is_frozen_3 l xs ((specret_val S0 (full_descriptor_some A)) : (specret full_descriptor))) o)

  | red_spec_call_object_is_frozen_4_prop_is_writable :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (A : attributes (* input *)) (xs : (list prop_name) (* input *)) (l : object_loc (* input *)),
        ((attributes_writable A) = true) ->
        (* ========================================== *)
        (* ------------------------------------------ *)
        (red_expr S C (spec_call_object_is_frozen_4 l xs (full_descriptor_some A)) (out_ter S ((resvalue_value (value_prim (prim_bool ((false : provide_this_flag) : bool)))) : res)))

  | red_spec_call_object_is_frozen_4_prop_is_not_writable :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (A : attributes (* input *)) (xs : (list prop_name) (* input *)) (l : object_loc (* input *)) (o : out),
        ((attributes_writable A) = false) ->
        (* ========================================== *)
        (red_expr S C (spec_call_object_is_frozen_5 l xs (full_descriptor_some A)) o) ->
        (* ------------------------------------------ *)
        (red_expr S C (spec_call_object_is_frozen_4 l xs (full_descriptor_some A)) o)

  | red_spec_call_object_is_frozen_5_prop_configurable :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (A : attributes (* input *)) (xs : (list prop_name) (* input *)) (l : object_loc (* input *)),
        ((attributes_configurable A) = true) ->
        (* ========================================== *)
        (* ------------------------------------------ *)
        (red_expr S C (spec_call_object_is_frozen_5 l xs (full_descriptor_some A)) (out_ter S ((resvalue_value (value_prim (prim_bool ((false : provide_this_flag) : bool)))) : res)))

  | red_spec_call_object_is_frozen_5_prop_not_configurable :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (A : attributes (* input *)) (xs : (list prop_name) (* input *)) (l : object_loc (* input *)) (o : out),
        ((attributes_configurable A) = false) ->
        (* ========================================== *)
        (red_expr S C (spec_call_object_is_frozen_2 l xs) o) ->
        (* ------------------------------------------ *)
        (red_expr S C (spec_call_object_is_frozen_5 l xs (full_descriptor_some A)) o)

  | red_spec_call_object_is_frozen_2_nil :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (l : object_loc (* input *)) (b : bool),
        (object_extensible S l b) ->
        (* ========================================== *)
        (* ------------------------------------------ *)
        (red_expr S C (spec_call_object_is_frozen_2 l (nil : (list prop_name))) (out_ter S ((negb b) : res)))

  | red_spec_call_object_is_extensible :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (v : value) (o : out) (vthis : value (* input *)) (args : (list value) (* input *)),
        (arguments_from args (v :: (nil : (list value)))) ->
        (* ========================================== *)
        (red_expr S C (spec_call_object_is_extensible_1 v) o) ->
        (* ------------------------------------------ *)
        (red_expr S C (spec_call_prealloc prealloc_object_is_extensible vthis args) o)

  | red_spec_call_object_is_extensible_1_not_object :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (v : value (* input *)) (o : out),
        (((type_of v) : type) <> type_object) ->
        (* ========================================== *)
        (red_expr S C (spec_error native_error_type) o) ->
        (* ------------------------------------------ *)
        (red_expr S C (spec_call_object_is_extensible_1 v) o)

  | red_spec_call_object_is_extensible_1_object :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (l : object_loc (* input *)) (b : bool),
        (object_extensible S l b) ->
        (* ========================================== *)
        (* ------------------------------------------ *)
        (red_expr S C (spec_call_object_is_extensible_1 (value_object l)) (out_ter S ((resvalue_value (value_prim (prim_bool ((b : provide_this_flag) : bool)))) : res)))

  | red_spec_call_object_proto_to_string :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (vthis : value (* input *)) (args : (list value) (* input *)) (o : out),
        (* ========================================== *)
        (red_expr S C (spec_call_object_proto_to_string_1 vthis) o) ->
        (* ------------------------------------------ *)
        (red_expr S C (spec_call_prealloc prealloc_object_proto_to_string vthis args) o)

  | red_spec_call_object_proto_to_string_1_undef :
      forall (S : state (* input *)) (C : execution_ctx (* input *)),
        (* ========================================== *)
        (* ------------------------------------------ *)
        (red_expr S C (spec_call_object_proto_to_string_1 undef) (out_ter S ((resvalue_value (value_prim (prim_string (("[object Undefined]")%string)))) : res)))

  | red_spec_call_object_proto_to_string_1_null :
      forall (S : state (* input *)) (C : execution_ctx (* input *)),
        (* ========================================== *)
        (* ------------------------------------------ *)
        (red_expr S C (spec_call_object_proto_to_string_1 null) (out_ter S ((resvalue_value (value_prim (prim_string (("[object Null]")%string)))) : res)))

  | red_spec_call_object_proto_to_string_1_other :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (v : value (* input *)) (o : out) (o1 : out),
        ((v = null) \/ (v = undef)) ->
        (* ========================================== *)
        (red_expr S C (spec_to_object v) o1) ->
        (red_expr S C (spec_call_object_proto_to_string_2 o1) o) ->
        (* ------------------------------------------ *)
        (red_expr S C (spec_call_object_proto_to_string_1 v) o)

  | red_spec_call_object_proto_to_string_2 :
      forall (S0 : state (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (l : object_loc (* input *)) (sclass : string),
        (object_class S l sclass) ->
        (* ========================================== *)
        (* ------------------------------------------ *)
        (red_expr S0 C (spec_call_object_proto_to_string_2 (out_ter S ((resvalue_value (value_object l)) : res))) (out_ter S ((resvalue_value (value_prim (prim_string ((("[object ")%string) ++ (sclass ++ (("]")%string)))))) : res)))

  | red_spec_call_object_proto_value_of :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (vthis : value (* input *)) (args : (list value) (* input *)) (o : out),
        (* ========================================== *)
        (red_expr S C (spec_to_object vthis) o) ->
        (* ------------------------------------------ *)
        (red_expr S C (spec_call_prealloc prealloc_object_proto_value_of vthis args) o)

  | red_spec_call_object_proto_has_own_prop :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (v : value) (vthis : value (* input *)) (args : (list value) (* input *)) (o : out) (o1 : out),
        (arguments_from args (v :: (nil : (list value)))) ->
        (* ========================================== *)
        (red_expr S C (spec_to_string v) o1) ->
        (red_expr S C (spec_call_object_proto_has_own_prop_1 o1 vthis) o) ->
        (* ------------------------------------------ *)
        (red_expr S C (spec_call_prealloc prealloc_object_proto_has_own_prop vthis args) o)

  | red_spec_call_object_proto_has_own_prop_1 :
      forall (S : state (* input *)) (S' : state (* input *)) (C : execution_ctx (* input *)) (vthis : value (* input *)) (s : string (* input *)) (o : out) (o1 : out),
        (* ========================================== *)
        (red_expr S' C (spec_to_object vthis) o1) ->
        (red_expr S' C (spec_call_object_proto_has_own_prop_2 o1 (s : prop_name)) o) ->
        (* ------------------------------------------ *)
        (red_expr S C (spec_call_object_proto_has_own_prop_1 (out_ter S' ((resvalue_value (value_prim (prim_string s))) : res)) vthis) o)

  | red_spec_call_object_proto_has_own_prop_2 :
      forall (S : state (* input *)) (S' : state (* input *)) (C : execution_ctx (* input *)) (l : object_loc (* input *)) (s : string (* input *)) (o : out) (y : (specret full_descriptor)),
        (* ========================================== *)
        (red_spec S' C (spec_object_get_own_prop l (s : prop_name)) y) ->
        (red_expr S' C (spec_call_object_proto_has_own_prop_3 y) o) ->
        (* ------------------------------------------ *)
        (red_expr S C (spec_call_object_proto_has_own_prop_2 (out_ter S' ((resvalue_value (value_object l)) : res)) (s : prop_name)) o)

  | red_spec_call_object_proto_has_own_prop_3_undef :
      forall (S : state (* input *)) (S' : state (* input *)) (C : execution_ctx (* input *)),
        (* ========================================== *)
        (* ------------------------------------------ *)
        (red_expr S C (spec_call_object_proto_has_own_prop_3 ((specret_val S' full_descriptor_undef) : (specret full_descriptor))) (out_ter S' ((resvalue_value (value_prim (prim_bool ((false : provide_this_flag) : bool)))) : res)))

  | red_spec_call_object_proto_has_own_prop_3_not_undef :
      forall (S : state (* input *)) (S' : state (* input *)) (C : execution_ctx (* input *)) (A : attributes (* input *)),
        (* ========================================== *)
        (* ------------------------------------------ *)
        (red_expr S C (spec_call_object_proto_has_own_prop_3 ((specret_val S' (full_descriptor_some A)) : (specret full_descriptor))) (out_ter S' ((resvalue_value (value_prim (prim_bool ((true : provide_this_flag) : bool)))) : res)))

  | red_spec_call_object_proto_is_prototype_of_not_object :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (vthis : value (* input *)) (args : (list value) (* input *)) (v : value) (o : out),
        (arguments_from args (v :: (nil : (list value)))) ->
        (* ========================================== *)
        (red_expr S C (spec_call_object_proto_is_prototype_of_2_1 v vthis) o) ->
        (* ------------------------------------------ *)
        (red_expr S C (spec_call_prealloc prealloc_object_proto_is_prototype_of vthis args) o)

  | red_spec_call_object_proto_is_prototype_of_1_not_object :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (v : value (* input *)) (vthis : value (* input *)),
        (((type_of v) : type) <> type_object) ->
        (* ========================================== *)
        (* ------------------------------------------ *)
        (red_expr S C (spec_call_object_proto_is_prototype_of_2_1 v vthis) (out_ter S ((resvalue_value (value_prim (prim_bool ((false : provide_this_flag) : bool)))) : res)))

  | red_spec_call_object_proto_is_prototype_of_1_object :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (l : object_loc (* input *)) (vthis : value (* input *)) (o1 : out) (o : out),
        (* ========================================== *)
        (red_expr S C (spec_to_object vthis) o1) ->
        (red_expr S C (spec_call_object_proto_is_prototype_of_2_2 o1 l) o) ->
        (* ------------------------------------------ *)
        (red_expr S C (spec_call_object_proto_is_prototype_of_2_1 (value_object l) vthis) o)

  | red_spec_call_object_proto_is_prototype_of_2 :
      forall (S0 : state (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (l : object_loc (* input *)) (lthis : object_loc (* input *)) (o : out),
        (* ========================================== *)
        (red_expr S C (spec_call_object_proto_is_prototype_of_2_3 lthis l) o) ->
        (* ------------------------------------------ *)
        (red_expr S0 C (spec_call_object_proto_is_prototype_of_2_2 (out_ter S ((resvalue_value (value_object lthis)) : res)) l) o)

  | red_spec_call_object_proto_is_prototype_of_3 :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (l : object_loc (* input *)) (lthis : object_loc (* input *)) (vproto : value) (o : out),
        (object_proto S l vproto) ->
        (* ========================================== *)
        (red_expr S C (spec_call_object_proto_is_prototype_of_2_4 lthis vproto) o) ->
        (* ------------------------------------------ *)
        (red_expr S C (spec_call_object_proto_is_prototype_of_2_3 lthis l) o)

  | red_spec_call_object_proto_is_prototype_of_4_null :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (lthis : object_loc (* input *)),
        (* ========================================== *)
        (* ------------------------------------------ *)
        (red_expr S C (spec_call_object_proto_is_prototype_of_2_4 lthis null) (out_ter S ((resvalue_value (value_prim (prim_bool ((false : provide_this_flag) : bool)))) : res)))

  | red_spec_call_object_proto_is_prototype_of_4_equal :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (lthis : object_loc (* input *)),
        (* ========================================== *)
        (* ------------------------------------------ *)
        (red_expr S C (spec_call_object_proto_is_prototype_of_2_4 lthis (value_object lthis)) (out_ter S ((resvalue_value (value_prim (prim_bool ((true : provide_this_flag) : bool)))) : res)))

  | red_spec_call_object_proto_is_prototype_of_4_not_equal :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (lthis : object_loc (* input *)) (lproto : object_loc (* input *)) (o : out),
        (lproto <> lthis) ->
        (* ========================================== *)
        (red_expr S C (spec_call_object_proto_is_prototype_of_2_3 lthis lproto) o) ->
        (* ------------------------------------------ *)
        (red_expr S C (spec_call_object_proto_is_prototype_of_2_4 lthis (value_object lproto)) o)

  | red_spec_call_object_proto_prop_is_enumerable :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (v : value) (o : out) (vthis : value (* input *)) (args : (list value) (* input *)),
        (arguments_from args (v :: (nil : (list value)))) ->
        (* ========================================== *)
        (red_expr S C (spec_call_object_proto_prop_is_enumerable_1 v vthis) o) ->
        (* ------------------------------------------ *)
        (red_expr S C (spec_call_prealloc prealloc_object_proto_prop_is_enumerable vthis args) o)

  | red_spec_call_object_proto_prop_is_enumerable_1 :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (v : value (* input *)) (vthis : value (* input *)) (o : out) (o1 : out),
        (* ========================================== *)
        (red_expr S C (spec_to_string v) o1) ->
        (red_expr S C (spec_call_object_proto_prop_is_enumerable_2 vthis o1) o) ->
        (* ------------------------------------------ *)
        (red_expr S C (spec_call_object_proto_prop_is_enumerable_1 v vthis) o)

  | red_spec_call_object_proto_prop_is_enumerable_2 :
      forall (S : state (* input *)) (S' : state (* input *)) (C : execution_ctx (* input *)) (vthis : value (* input *)) (s : string (* input *)) (o : out) (o1 : out),
        (* ========================================== *)
        (red_expr S' C (spec_to_object vthis) o1) ->
        (red_expr S' C (spec_call_object_proto_prop_is_enumerable_3 o1 s) o) ->
        (* ------------------------------------------ *)
        (red_expr S C (spec_call_object_proto_prop_is_enumerable_2 vthis (out_ter S' ((resvalue_value (value_prim (prim_string s))) : res))) o)

  | red_spec_call_object_proto_prop_is_enumerable_3 :
      forall (S : state (* input *)) (S' : state (* input *)) (C : execution_ctx (* input *)) (l : object_loc (* input *)) (x : prop_name (* input *)) (o : out) (y : (specret full_descriptor)),
        (* ========================================== *)
        (red_spec S' C (spec_object_get_own_prop l x) y) ->
        (red_expr S' C (spec_call_object_proto_prop_is_enumerable_4 y) o) ->
        (* ------------------------------------------ *)
        (red_expr S C (spec_call_object_proto_prop_is_enumerable_3 (out_ter S' ((resvalue_value (value_object l)) : res)) (x : string)) o)

  | red_spec_call_object_proto_prop_is_enumerable_4_undef :
      forall (S0 : state (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)),
        (* ========================================== *)
        (* ------------------------------------------ *)
        (red_expr S C (spec_call_object_proto_prop_is_enumerable_4 ((specret_val S0 full_descriptor_undef) : (specret full_descriptor))) (out_ter S0 ((resvalue_value (value_prim (prim_bool ((false : provide_this_flag) : bool)))) : res)))

  | red_spec_call_object_proto_prop_is_enumerable_4_not_undef :
      forall (S0 : state (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (A : attributes (* input *)),
        (* ========================================== *)
        (* ------------------------------------------ *)
        (red_expr S C (spec_call_object_proto_prop_is_enumerable_4 ((specret_val S0 (full_descriptor_some A)) : (specret full_descriptor))) (out_ter S0 ((resvalue_value (value_prim (prim_bool (((attributes_enumerable A) : provide_this_flag) : bool)))) : res)))

  | red_spec_call_function_proto_invoked :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (vthis : value (* input *)) (args : (list value) (* input *)),
        (* ========================================== *)
        (* ------------------------------------------ *)
        (red_expr S C (spec_call_prealloc prealloc_function_proto vthis args) (out_ter S ((resvalue_value undef) : res)))

  | red_spec_object_get_1_function :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (vthis : value (* input *)) (l : object_loc (* input *)) (x : prop_name (* input *)) (o1 : out) (o : out),
        (* ========================================== *)
        (red_expr S C (spec_object_get_1 builtin_get_default vthis l x) o1) ->
        (red_expr S C (spec_function_get_1 l x o1) o) ->
        (* ------------------------------------------ *)
        (red_expr S C (spec_object_get_1 builtin_get_function vthis l x) o)

  | red_spec_function_get_1_error :
      forall (S0 : state (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (l : object_loc (* input *)) (x : prop_name (* input *)) (v : value (* input *)) (o : out),
        (spec_function_get_error_case S x v) ->
        (* ========================================== *)
        (red_expr S C (spec_error native_error_type) o) ->
        (* ------------------------------------------ *)
        (red_expr S0 C (spec_function_get_1 l x (out_ter S ((resvalue_value v) : res))) o)

  | red_spec_function_get_1_normal :
      forall (S0 : state (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (l : object_loc (* input *)) (x : prop_name (* input *)) (v : value (* input *)),
        (spec_function_get_error_case S x v) ->
        (* ========================================== *)
        (* ------------------------------------------ *)
        (red_expr S0 C (spec_function_get_1 l x (out_ter S ((resvalue_value v) : res))) (out_ter S ((resvalue_value v) : res)))

  | red_spec_object_has_instance_1_function_prim :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (l : object_loc (* input *)) (w : prim (* input *)),
        (* ========================================== *)
        (* ------------------------------------------ *)
        (red_expr S C (spec_object_has_instance_1 builtin_has_instance_function l (value_prim w)) (out_ter S ((resvalue_value (value_prim (prim_bool ((false : provide_this_flag) : bool)))) : res)))

  | red_spec_object_has_instance_1_function_object :
      forall (o1 : out) (S : state (* input *)) (C : execution_ctx (* input *)) (l : object_loc (* input *)) (lv : object_loc (* input *)) (o : out),
        (* ========================================== *)
        (red_expr S C (spec_object_get (value_object l) ((("prototype")%string) : prop_name)) o1) ->
        (red_expr S C (spec_function_has_instance_1 lv o1) o) ->
        (* ------------------------------------------ *)
        (red_expr S C (spec_object_has_instance_1 builtin_has_instance_function l (value_object lv)) o)

  | red_spec_function_has_instance_1_prim :
      forall (S0 : state (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (lv : object_loc (* input *)) (v : value (* input *)) (o : out),
        (((type_of v) : type) <> type_object) ->
        (* ========================================== *)
        (red_expr S C (spec_error native_error_type) o) ->
        (* ------------------------------------------ *)
        (red_expr S0 C (spec_function_has_instance_1 lv (out_ter S ((resvalue_value v) : res))) o)

  | red_spec_function_has_instance_1_object :
      forall (S0 : state (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (lv : object_loc (* input *)) (lo : object_loc (* input *)) (o : out),
        (* ========================================== *)
        (red_expr S C (spec_function_has_instance_2 lo lv) o) ->
        (* ------------------------------------------ *)
        (red_expr S0 C (spec_function_has_instance_1 lv (out_ter S ((resvalue_value (value_object lo)) : res))) o)

  | red_spec_function_has_instance_2 :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (lo : object_loc (* input *)) (lv : object_loc (* input *)) (vproto : value) (o : out),
        (object_proto S lv vproto) ->
        (* ========================================== *)
        (red_expr S C (spec_function_has_instance_3 lo vproto) o) ->
        (* ------------------------------------------ *)
        (red_expr S C (spec_function_has_instance_2 lo lv) o)

  | red_spec_function_has_instance_3_null :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (lo : object_loc (* input *)),
        (* ========================================== *)
        (* ------------------------------------------ *)
        (red_expr S C (spec_function_has_instance_3 lo null) (out_ter S ((resvalue_value (value_prim (prim_bool ((false : provide_this_flag) : bool)))) : res)))

  | red_spec_function_has_instance_3_eq :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (lo : object_loc (* input *)),
        (* ========================================== *)
        (* ------------------------------------------ *)
        (red_expr S C (spec_function_has_instance_3 lo (value_object lo)) (out_ter S ((resvalue_value (value_prim (prim_bool ((true : provide_this_flag) : bool)))) : res)))

  | red_spec_function_has_instance_3_neq :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (lo : object_loc (* input *)) (lv : object_loc (* input *)) (o : out),
        (lv <> lo) ->
        (* ========================================== *)
        (red_expr S C (spec_function_has_instance_2 lo lv) o) ->
        (* ------------------------------------------ *)
        (red_expr S C (spec_function_has_instance_3 lo (value_object lv)) o)

  | red_spec_call_array_new_no_args :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (o : out),
        (* ========================================== *)
        (red_expr S C (spec_call_array_new_1 (nil : (list value))) o) ->
        (* ------------------------------------------ *)
        (red_expr S C (spec_construct_prealloc prealloc_array (nil : (list value))) o)

  | red_spec_call_array_new_multiple_args :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (args : (list value) (* input *)) (v1 : value) (v2 : value) (vs : (list value)) (o : out),
        (args = (v1 :: (v2 :: vs))) ->
        (* ========================================== *)
        (red_expr S C (spec_call_array_new_1 args) o) ->
        (* ------------------------------------------ *)
        (red_expr S C (spec_construct_prealloc prealloc_array args) o)

  | red_spec_call_array_new_1 :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (args : (list value) (* input *)) (o : out),
        (* ========================================== *)
        (red_expr ((snd ((object_alloc S ((object_new prealloc_array_proto (("Array")%string)) : object)) : (object_loc * state))) : state) C (spec_call_array_new_2 ((fst ((object_alloc S ((object_new prealloc_array_proto (("Array")%string)) : object)) : (object_loc * state))) : object_loc) args (my_Z_of_nat (0%nat))) o) ->
        (* ------------------------------------------ *)
        (red_expr S C (spec_call_array_new_1 args) o)

  | red_spec_call_array_new_2_nonempty :
      forall (S : state (* input *)) (S' : state) (C : execution_ctx (* input *)) (l : object_loc (* input *)) (v : value (* input *)) (vs : (list value) (* input *)) (ilen : nat (* input *)) (o : out),
        (object_set_property S l (JsNumber.to_string (JsNumber.of_int ilen)) (attributes_data_intro v true true true) S') ->
        (* ========================================== *)
        (red_expr S' C (spec_call_array_new_2 l vs (my_Z_of_nat (ilen + (1%nat)))) o) ->
        (* ------------------------------------------ *)
        (red_expr S C (spec_call_array_new_2 l (v :: vs) (my_Z_of_nat ilen)) o)

  | red_spec_call_array_new_2_empty :
      forall (S : state (* input *)) (S' : state) (C : execution_ctx (* input *)) (l : object_loc (* input *)) (ilen : int (* input *)),
        (object_set_property S l (("length")%string) (attributes_data_intro ((JsNumber.of_int ilen) : value) true true true) S') ->
        (* ========================================== *)
        (* ------------------------------------------ *)
        (red_expr S C (spec_call_array_new_2 l (nil : (list value)) ilen) (out_ter S' ((resvalue_value (value_object l)) : res)))

  | red_spec_call_array_proto_pop :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (vthis : value (* input *)) (o : out) (o1 : out) (args : (list value) (* input *)),
        (* ========================================== *)
        (red_expr S C (spec_to_object vthis) o1) ->
        (red_expr S C (spec_call_array_proto_pop_1 o1) o) ->
        (* ------------------------------------------ *)
        (red_expr S C (spec_call_prealloc prealloc_array_proto_pop vthis args) o)

  | red_spec_call_array_proto_pop_1 :
      forall (S0 : state (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (l : object_loc (* input *)) (o : out) (o1 : out),
        (* ========================================== *)
        (red_expr S C (spec_object_get (value_object l) ((("length")%string) : prop_name)) o1) ->
        (red_expr S C (spec_call_array_proto_pop_2 l o1) o) ->
        (* ------------------------------------------ *)
        (red_expr S0 C (spec_call_array_proto_pop_1 (out_ter S ((resvalue_value (value_object l)) : res))) o)

  | red_spec_call_array_proto_pop_2 :
      forall (S0 : state (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (l : object_loc (* input *)) (vlen : value (* input *)) (o : out) (y : (specret int)),
        (* ========================================== *)
        (red_spec S C (spec_to_uint32 vlen) y) ->
        (red_expr S C (spec_call_array_proto_pop_3 l y) o) ->
        (* ------------------------------------------ *)
        (red_expr S0 C (spec_call_array_proto_pop_2 l (out_ter S ((resvalue_value vlen) : res))) o)

  | red_spec_call_array_proto_pop_3_empty :
      forall (S0 : state (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (l : object_loc (* input *)) (o : out),
        (* ========================================== *)
        (red_expr S C (spec_call_array_proto_pop_3_empty_1 l) o) ->
        (* ------------------------------------------ *)
        (red_expr S0 C (spec_call_array_proto_pop_3 l ((specret_val S (0%Z)) : (specret int))) o)

  | red_spec_call_array_proto_pop_3_empty_1 :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (l : object_loc (* input *)) (o : out) (o1 : out),
        (* ========================================== *)
        (red_expr S C (spec_object_put (value_object l) ((("length")%string) : prop_name) (value_prim (prim_number (JsNumber.of_int (my_Z_of_nat (0%nat))))) (throw_true : bool)) o1) ->
        (red_expr S C (spec_call_array_proto_pop_3_empty_2 o1) o) ->
        (* ------------------------------------------ *)
        (red_expr S C (spec_call_array_proto_pop_3_empty_1 l) o)

  | red_spec_call_array_proto_pop_3_empty_2 :
      forall (S0 : state (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (r0 : ref (* input *)),
        (* ========================================== *)
        (* ------------------------------------------ *)
        (red_expr S0 C (spec_call_array_proto_pop_3_empty_2 (out_ter S ((resvalue_ref r0) : res))) (out_ter S ((resvalue_value undef) : res)))

  | red_spec_call_array_proto_pop_3_nonempty :
      forall (S0 : state (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (l : object_loc (* input *)) (lenuint32 : int (* input *)) (o : out),
        (lenuint32 > (my_Z_of_nat (0%nat))) ->
        (* ========================================== *)
        (red_expr S C (spec_call_array_proto_pop_3_nonempty_1 l lenuint32) o) ->
        (* ------------------------------------------ *)
        (red_expr S0 C (spec_call_array_proto_pop_3 l ((specret_val S lenuint32) : (specret int))) o)

  | red_spec_call_array_proto_pop_3_nonempty_1 :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (l : object_loc (* input *)) (lenuint32 : nat (* input *)) (o : out) (o1 : out),
        (* ========================================== *)
        (red_expr S C (spec_to_string (value_prim (prim_number (JsNumber.of_int (my_Z_of_nat (lenuint32 - (1%nat))))))) o1) ->
        (red_expr S C (spec_call_array_proto_pop_3_nonempty_2 l o1) o) ->
        (* ------------------------------------------ *)
        (red_expr S C (spec_call_array_proto_pop_3_nonempty_1 l (my_Z_of_nat lenuint32)) o)

  | red_spec_call_array_proto_pop_3_nonempty_2 :
      forall (S0 : state (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (l : object_loc (* input *)) (vindx : prop_name (* input *)) (velem : value) (o : out) (o1 : out),
        (* ========================================== *)
        (red_expr S C (spec_object_get (value_object l) vindx) o1) ->
        (red_expr S C (spec_call_array_proto_pop_3_nonempty_3 l (value_prim (prim_string (vindx : string))) o1) o) ->
        (* ------------------------------------------ *)
        (red_expr S0 C (spec_call_array_proto_pop_3_nonempty_2 l (out_ter S ((resvalue_value (value_prim (prim_string (vindx : string)))) : res))) o)

  | red_spec_call_array_proto_pop_3_nonempty_3 :
      forall (S0 : state (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (l : object_loc (* input *)) (vindx : prop_name (* input *)) (velem : value (* input *)) (o : out) (o1 : out),
        (* ========================================== *)
        (red_expr S C (spec_object_delete l vindx (throw_true : bool)) o1) ->
        (red_expr S C (spec_call_array_proto_pop_3_nonempty_4 l (value_prim (prim_string (vindx : string))) velem o1) o) ->
        (* ------------------------------------------ *)
        (red_expr S0 C (spec_call_array_proto_pop_3_nonempty_3 l (value_prim (prim_string (vindx : string))) (out_ter S ((resvalue_value velem) : res))) o)

  | red_spec_call_array_proto_pop_3_nonempty_4 :
      forall (S0 : state (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (l : object_loc (* input *)) (vindx : value (* input *)) (velem : value (* input *)) (o : out) (o1 : out) (r0 : ref (* input *)),
        (* ========================================== *)
        (red_expr S C (spec_object_put (value_object l) ((("length")%string) : prop_name) vindx (throw_true : bool)) o1) ->
        (red_expr S C (spec_call_array_proto_pop_3_nonempty_5 velem o1) o) ->
        (* ------------------------------------------ *)
        (red_expr S0 C (spec_call_array_proto_pop_3_nonempty_4 l vindx velem (out_ter S ((resvalue_ref r0) : res))) o)

  | red_spec_call_array_proto_pop_3_nonempty_5 :
      forall (S0 : state (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (velem : value (* input *)) (r0 : ref (* input *)),
        (* ========================================== *)
        (* ------------------------------------------ *)
        (red_expr S0 C (spec_call_array_proto_pop_3_nonempty_5 velem (out_ter S ((resvalue_ref r0) : res))) (out_ter S ((resvalue_value velem) : res)))

  | red_spec_call_array_proto_push :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (vthis : value (* input *)) (args : (list value) (* input *)) (o : out) (o1 : out),
        (* ========================================== *)
        (red_expr S C (spec_to_object vthis) o1) ->
        (red_expr S C (spec_call_array_proto_push_1 o1 args) o) ->
        (* ------------------------------------------ *)
        (red_expr S C (spec_call_prealloc prealloc_array_proto_push vthis args) o)

  | red_spec_call_array_proto_push_1 :
      forall (S0 : state (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (l : object_loc (* input *)) (args : (list value) (* input *)) (o : out) (o1 : out),
        (* ========================================== *)
        (red_expr S C (spec_object_get (value_object l) ((("length")%string) : prop_name)) o1) ->
        (red_expr S C (spec_call_array_proto_push_2 l args o1) o) ->
        (* ------------------------------------------ *)
        (red_expr S0 C (spec_call_array_proto_push_1 (out_ter S ((resvalue_value (value_object l)) : res)) args) o)

  | red_spec_call_array_proto_push_2 :
      forall (S0 : state (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (l : object_loc (* input *)) (args : (list value) (* input *)) (vlen : value (* input *)) (y : (specret int)) (o : out),
        (* ========================================== *)
        (red_spec S C (spec_to_uint32 vlen) y) ->
        (red_expr S C (spec_call_array_proto_push_3 l args y) o) ->
        (* ------------------------------------------ *)
        (red_expr S0 C (spec_call_array_proto_push_2 l args (out_ter S ((resvalue_value vlen) : res))) o)

  | red_spec_call_array_proto_push_3 :
      forall (S0 : state (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (l : object_loc (* input *)) (args : (list value) (* input *)) (lenuint32 : int (* input *)) (o : out),
        (* ========================================== *)
        (red_expr S C (spec_call_array_proto_push_4 l args lenuint32) o) ->
        (* ------------------------------------------ *)
        (red_expr S0 C (spec_call_array_proto_push_3 l args ((specret_val S lenuint32) : (specret int))) o)

  | red_spec_call_array_proto_push_4_empty :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (l : object_loc (* input *)) (lenuint32 : int (* input *)) (o : out),
        (* ========================================== *)
        (red_expr S C (spec_call_array_proto_push_5 l ((JsNumber.of_int lenuint32) : value)) o) ->
        (* ------------------------------------------ *)
        (red_expr S C (spec_call_array_proto_push_4 l (nil : (list value)) lenuint32) o)

  | red_spec_call_array_proto_push_4_nonempty :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (l : object_loc (* input *)) (v : value (* input *)) (vs : (list value) (* input *)) (lenuint32 : int (* input *)) (o : out),
        (* ========================================== *)
        (red_expr S C (spec_call_array_proto_push_4_nonempty_1 l vs lenuint32 v) o) ->
        (* ------------------------------------------ *)
        (red_expr S C (spec_call_array_proto_push_4 l (v :: vs) lenuint32) o)

  | red_spec_call_array_proto_push_4_nonempty_1 :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (l : object_loc (* input *)) (v : value (* input *)) (vs : (list value) (* input *)) (lenuint32 : int (* input *)) (o : out) (o1 : out),
        (* ========================================== *)
        (red_expr S C (spec_to_string ((JsNumber.of_int lenuint32) : value)) o1) ->
        (red_expr S C (spec_call_array_proto_push_4_nonempty_2 l vs lenuint32 v o1) o) ->
        (* ------------------------------------------ *)
        (red_expr S C (spec_call_array_proto_push_4_nonempty_1 l vs lenuint32 v) o)

  | red_spec_call_array_proto_push_4_nonempty_2 :
      forall (S0 : state (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (l : object_loc (* input *)) (vindx : prop_name (* input *)) (v : value (* input *)) (vs : (list value) (* input *)) (lenuint32 : int (* input *)) (o : out) (o1 : out),
        (* ========================================== *)
        (red_expr S C (spec_object_put (value_object l) vindx v (throw_true : bool)) o1) ->
        (red_expr S C (spec_call_array_proto_push_4_nonempty_3 l vs lenuint32 v o1) o) ->
        (* ------------------------------------------ *)
        (red_expr S0 C (spec_call_array_proto_push_4_nonempty_2 l vs lenuint32 v (out_ter S ((resvalue_value (value_prim (prim_string (vindx : string)))) : res))) o)

  | red_spec_call_array_proto_push_4_nonempty_3 :
      forall (S0 : state (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (l : object_loc (* input *)) (v : value (* input *)) (vs : (list value) (* input *)) (lenuint32 : nat (* input *)) (o : out) (r0 : ref (* input *)),
        (* ========================================== *)
        (red_expr S C (spec_call_array_proto_push_4 l vs (my_Z_of_nat (lenuint32 + (1%nat)))) o) ->
        (* ------------------------------------------ *)
        (red_expr S0 C (spec_call_array_proto_push_4_nonempty_3 l vs (my_Z_of_nat lenuint32) v (out_ter S ((resvalue_ref r0) : res))) o)

  | red_spec_call_array_proto_push_5 :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (l : object_loc (* input *)) (vlen : value (* input *)) (o : out) (o1 : out),
        (* ========================================== *)
        (red_expr S C (spec_object_put (value_object l) ((("length")%string) : prop_name) vlen (throw_true : bool)) o1) ->
        (red_expr S C (spec_call_array_proto_push_6 vlen o1) o) ->
        (* ------------------------------------------ *)
        (red_expr S C (spec_call_array_proto_push_5 l vlen) o)

  | red_spec_call_array_proto_push_6 :
      forall (S0 : state (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (vlen : value (* input *)) (r0 : ref (* input *)),
        (* ========================================== *)
        (* ------------------------------------------ *)
        (red_expr S0 C (spec_call_array_proto_push_6 vlen (out_ter S ((resvalue_ref r0) : res))) (out_ter S ((resvalue_value vlen) : res)))

  | red_spec_call_string_proto_to_string :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (vthis : value (* input *)) (args : (list value) (* input *)) (o : out),
        (* ========================================== *)
        (red_expr S C (spec_call_prealloc prealloc_string_proto_value_of vthis args) o) ->
        (* ------------------------------------------ *)
        (red_expr S C (spec_call_prealloc prealloc_string_proto_to_string vthis args) o)

  | red_spec_call_string_proto_value_of_prim_string :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (vthis : value (* input *)) (args : (list value) (* input *)),
        (* ========================================== *)
        (* ------------------------------------------ *)
        (red_expr S C (spec_call_prealloc prealloc_string_proto_value_of vthis args) (out_ter S ((resvalue_value vthis) : res)))

  | red_spec_call_string_proto_value_of_obj_string :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (l : object_loc (* input *)) (v : value) (args : (list value) (* input *)),
        (object_class S l (("String")%string)) ->
        (object_prim_value S l v) ->
        (* ========================================== *)
        (* ------------------------------------------ *)
        (red_expr S C (spec_call_prealloc prealloc_string_proto_value_of (value_object l) args) (out_ter S ((resvalue_value v) : res)))

  | red_spec_call_string_proto_value_of_obj_other :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (l : object_loc (* input *)) (args : (list value) (* input *)) (o : out),
        (object_class S l (("String")%string)) ->
        (* ========================================== *)
        (red_expr S C (spec_error native_error_type) o) ->
        (* ------------------------------------------ *)
        (red_expr S C (spec_call_prealloc prealloc_string_proto_value_of (value_object l) args) o)

  | red_spec_call_string_proto_value_of_bad_type :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (vthis : value (* input *)) (args : (list value) (* input *)) (o : out),
        (((type_of vthis) : type) <> type_string) ->
        (((type_of vthis) : type) <> type_object) ->
        (* ========================================== *)
        (red_expr S C (spec_error native_error_type) o) ->
        (* ------------------------------------------ *)
        (red_expr S C (spec_call_prealloc prealloc_string_proto_value_of vthis args) o)

  | red_spec_call_bool :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (v : value) (o : out) (vthis : value (* input *)) (args : (list value) (* input *)),
        (arguments_from args (v :: (nil : (list value)))) ->
        (* ========================================== *)
        (red_expr S C (spec_to_boolean v) o) ->
        (* ------------------------------------------ *)
        (red_expr S C (spec_call_prealloc prealloc_bool vthis args) o)

  | red_spec_construct_bool :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (v : value) (o : out) (o1 : out) (args : (list value) (* input *)),
        (arguments_from args (v :: (nil : (list value)))) ->
        (* ========================================== *)
        (red_expr S C (spec_to_boolean v) o1) ->
        (red_expr S C (spec_construct_bool_1 o1) o) ->
        (* ------------------------------------------ *)
        (red_expr S C (spec_construct_prealloc prealloc_bool args) o)

  | red_spec_construct_bool_1 :
      forall (O : object) (b : bool (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)),
        (* ========================================== *)
        (* ------------------------------------------ *)
        (red_expr S C (spec_construct_bool_1 (out_ter S ((resvalue_value (value_prim (prim_bool ((b : provide_this_flag) : bool)))) : res))) (out_ter ((snd ((object_alloc S ((object_with_primitive_value ((object_new prealloc_bool_proto (("Boolean")%string)) : object) b) : object)) : (object_loc * state))) : state) ((fst ((object_alloc S ((object_with_primitive_value ((object_new prealloc_bool_proto (("Boolean")%string)) : object) b) : object)) : (object_loc * state))) : res)))

  | red_spec_call_bool_proto_to_string :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (vthis : value (* input *)) (args : (list value) (* input *)) (o1 : out) (o : out),
        (* ========================================== *)
        (red_expr S C (spec_call_prealloc prealloc_bool_proto_value_of vthis args) o1) ->
        (red_expr S C (spec_call_bool_proto_to_string_1 o1) o) ->
        (* ------------------------------------------ *)
        (red_expr S C (spec_call_prealloc prealloc_bool_proto_to_string vthis args) o)

  | red_spec_call_bool_proto_to_string_1 :
      forall (S0 : state (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (b : bool (* input *)),
        (* ========================================== *)
        (* ------------------------------------------ *)
        (red_expr S0 C (spec_call_bool_proto_to_string_1 (out_ter S ((resvalue_value (value_prim (prim_bool ((b : provide_this_flag) : bool)))) : res))) (out_ter S ((resvalue_value (value_prim (prim_string (convert_bool_to_string b)))) : res)))

  | red_spec_call_bool_proto_value_of :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (o : out) (vthis : value (* input *)) (args : (list value) (* input *)),
        (* ========================================== *)
        (red_expr S C (spec_call_bool_proto_value_of_1 vthis) o) ->
        (* ------------------------------------------ *)
        (red_expr S C (spec_call_prealloc prealloc_bool_proto_value_of vthis args) o)

  | red_spec_call_bool_proto_value_of_1_bool :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (v : value (* input *)) (b : bool),
        (value_viewable_as (("Boolean")%string) S v (prim_bool ((b : provide_this_flag) : bool))) ->
        (* ========================================== *)
        (* ------------------------------------------ *)
        (red_expr S C (spec_call_bool_proto_value_of_1 v) (out_ter S ((resvalue_value (value_prim (prim_bool ((b : provide_this_flag) : bool)))) : res)))

  | red_spec_call_bool_proto_value_of_1_not_bool :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (v : value (* input *)) (o : out),
        (forall b, (~ (value_viewable_as (("Boolean")%string) S v b))) ->
        (* ========================================== *)
        (red_expr S C (spec_error native_error_type) o) ->
        (* ------------------------------------------ *)
        (red_expr S C (spec_call_bool_proto_value_of_1 v) o)

  | red_spec_call_number_nil :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (vthis : value (* input *)),
        (* ========================================== *)
        (* ------------------------------------------ *)
        (red_expr S C (spec_call_prealloc prealloc_number vthis (nil : (list value))) (out_ter S ((resvalue_value (value_prim (prim_number JsNumber.zero))) : res)))

  | red_spec_call_number_not_nil :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (v : value) (o : out) (vthis : value (* input *)) (args : (list value) (* input *)),
        (args <> nil) ->
        (arguments_from args (v :: (nil : (list value)))) ->
        (* ========================================== *)
        (red_expr S C (spec_to_number v) o) ->
        (* ------------------------------------------ *)
        (red_expr S C (spec_call_prealloc prealloc_number vthis args) o)

  | red_spec_construct_number_nil :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (o : out),
        (* ========================================== *)
        (red_expr S C (spec_construct_number_1 (out_ter S ((resvalue_value (value_prim (prim_number JsNumber.zero))) : res))) o) ->
        (* ------------------------------------------ *)
        (red_expr S C (spec_construct_prealloc prealloc_number (nil : (list value))) o)

  | red_spec_construct_number_not_nil :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (v : value) (o : out) (o1 : out) (args : (list value) (* input *)),
        (args <> nil) ->
        (arguments_from args (v :: (nil : (list value)))) ->
        (* ========================================== *)
        (red_expr S C (spec_to_number v) o1) ->
        (red_expr S C (spec_construct_number_1 o1) o) ->
        (* ------------------------------------------ *)
        (red_expr S C (spec_construct_prealloc prealloc_number args) o)

  | red_spec_construct_number_1 :
      forall (S0 : state (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (O : object) (v : value (* input *)),
        (* ========================================== *)
        (* ------------------------------------------ *)
        (red_expr S0 C (spec_construct_number_1 (out_ter S ((resvalue_value v) : res))) (out_ter ((snd ((object_alloc S ((object_with_primitive_value ((object_new prealloc_number_proto (("Number")%string)) : object) v) : object)) : (object_loc * state))) : state) ((fst ((object_alloc S ((object_with_primitive_value ((object_new prealloc_number_proto (("Number")%string)) : object) v) : object)) : (object_loc * state))) : res)))

  | red_spec_call_number_proto_value_of :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (o : out) (vthis : value (* input *)) (args : (list value) (* input *)),
        (* ========================================== *)
        (red_expr S C (spec_call_number_proto_value_of_1 vthis) o) ->
        (* ------------------------------------------ *)
        (red_expr S C (spec_call_prealloc prealloc_number_proto_value_of vthis args) o)

  | red_spec_call_number_proto_value_of_1_number :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (v : value (* input *)) (n : number),
        (value_viewable_as (("Number")%string) S v (prim_number n)) ->
        (* ========================================== *)
        (* ------------------------------------------ *)
        (red_expr S C (spec_call_number_proto_value_of_1 v) (out_ter S ((resvalue_value (value_prim (prim_number n))) : res)))

  | red_spec_call_number_proto_value_of_1_not_number :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (v : value (* input *)) (o : out),
        (forall n, (~ (value_viewable_as (("Number")%string) S v n))) ->
        (* ========================================== *)
        (red_expr S C (spec_error native_error_type) o) ->
        (* ------------------------------------------ *)
        (red_expr S C (spec_call_number_proto_value_of_1 v) o)

  | red_spec_error :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (ne : native_error (* input *)) (o1 : out) (o : out),
        (* ========================================== *)
        (red_expr S C (spec_build_error (value_object (object_loc_prealloc (prealloc_native_error_proto ne))) undef) o1) ->
        (red_expr S C (spec_error_1 o1) o) ->
        (* ------------------------------------------ *)
        (red_expr S C (spec_error ne) o)

  | red_spec_error_1 :
      forall (S0 : state (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (l : object_loc (* input *)),
        (* ========================================== *)
        (* ------------------------------------------ *)
        (red_expr S0 C (spec_error_1 (out_ter S ((resvalue_value (value_object l)) : res))) (out_ter S (res_throw (resvalue_value (value_object l)))))

  | red_spec_error_or_cst_true :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (ne : native_error (* input *)) (v : value (* input *)) (o : out),
        (* ========================================== *)
        (red_expr S C (spec_error ne) o) ->
        (* ------------------------------------------ *)
        (red_expr S C (spec_error_or_cst true ne v) o)

  | red_spec_error_or_cst_false :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (ne : native_error (* input *)) (v : value (* input *)),
        (* ========================================== *)
        (* ------------------------------------------ *)
        (red_expr S C (spec_error_or_cst false ne v) (out_ter S ((resvalue_value v) : res)))

  | red_spec_error_or_void_true :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (ne : native_error (* input *)) (o : out),
        (* ========================================== *)
        (red_expr S C (spec_error ne) o) ->
        (* ------------------------------------------ *)
        (red_expr S C (spec_error_or_void true ne) o)

  | red_spec_error_or_void_false :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (ne : native_error (* input *)),
        (* ========================================== *)
        (* ------------------------------------------ *)
        (red_expr S C (spec_error_or_void false ne) (out_void S))

  | red_spec_build_error :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (vproto : value (* input *)) (vmsg : value (* input *)) (o : out),
        (* ========================================== *)
        (red_expr ((snd ((object_alloc S ((object_new vproto (("Error")%string)) : object)) : (object_loc * state))) : state) C (spec_build_error_1 ((fst ((object_alloc S ((object_new vproto (("Error")%string)) : object)) : (object_loc * state))) : object_loc) vmsg) o) ->
        (* ------------------------------------------ *)
        (red_expr S C (spec_build_error vproto vmsg) o)

  | red_spec_build_error_1_no_msg :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (l : object_loc (* input *)) (vmsg : value (* input *)),
        (* ========================================== *)
        (* ------------------------------------------ *)
        (red_expr S C (spec_build_error_1 l vmsg) (out_ter S ((resvalue_value (value_object l)) : res)))

  | red_spec_build_error_1_msg :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (l : object_loc (* input *)) (vmsg : value (* input *)) (o1 : out) (o : out),
        (vmsg <> undef) ->
        (* ========================================== *)
        (red_expr S C (spec_to_string vmsg) o1) ->
        (red_expr S C (spec_build_error_2 l o1) o) ->
        (* ------------------------------------------ *)
        (red_expr S C (spec_build_error_1 l vmsg) o)

  | red_spec_build_error_2 :
      forall (S0 : state (* input *)) (S : state (* input *)) (S' : state) (C : execution_ctx (* input *)) (l : object_loc (* input *)) (smsg : value (* input *)),
        (object_set_property S l (("message")%string) (attributes_data_intro smsg true false true) S') ->
        (* ========================================== *)
        (* ------------------------------------------ *)
        (red_expr S0 C (spec_build_error_2 l (out_ter S ((resvalue_value smsg) : res))) (out_ter S' ((resvalue_value (value_object l)) : res)))

  | red_spec_call_error :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (v : value) (o : out) (vthis : value (* input *)) (args : (list value) (* input *)),
        (arguments_from args (v :: (nil : (list value)))) ->
        (* ========================================== *)
        (red_expr S C (spec_build_error (value_object (object_loc_prealloc prealloc_error_proto)) v) o) ->
        (* ------------------------------------------ *)
        (red_expr S C (spec_call_prealloc prealloc_error vthis args) o)

  | red_spec_construct_error :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (v : value) (o : out) (args : (list value) (* input *)),
        (arguments_from args (v :: (nil : (list value)))) ->
        (* ========================================== *)
        (red_expr S C (spec_build_error (value_object (object_loc_prealloc prealloc_error_proto)) v) o) ->
        (* ------------------------------------------ *)
        (red_expr S C (spec_construct_prealloc prealloc_error args) o)

  | red_spec_call_error_proto_to_string :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (args : (list value) (* input *)) (vthis : value (* input *)) (o : out),
        (* ========================================== *)
        (red_expr S C (spec_call_error_proto_to_string_1 vthis) o) ->
        (* ------------------------------------------ *)
        (red_expr S C (spec_call_prealloc prealloc_error_proto_to_string vthis args) o)

  | red_spec_call_error_proto_to_string_1_not_object :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (v : value (* input *)) (o : out),
        (((type_of v) : type) <> type_object) ->
        (* ========================================== *)
        (red_expr S C (spec_error native_error_type) o) ->
        (* ------------------------------------------ *)
        (red_expr S C (spec_call_error_proto_to_string_1 v) o)

  | red_spec_call_error_proto_to_string_1_object :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (l : object_loc (* input *)) (o1 : out) (o : out),
        (* ========================================== *)
        (red_expr S C (spec_object_get (value_object l) ((("name")%string) : prop_name)) o1) ->
        (red_expr S C (spec_call_error_proto_to_string_2 l o1) o) ->
        (* ------------------------------------------ *)
        (red_expr S C (spec_call_error_proto_to_string_1 (value_object l)) o)

  | red_spec_call_error_proto_to_string_2_undef :
      forall (S0 : state (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (l : object_loc (* input *)) (o : out),
        (* ========================================== *)
        (red_expr S C (spec_call_error_proto_to_string_3 l (out_ter S ((resvalue_value (value_prim (prim_string (("Error")%string)))) : res))) o) ->
        (* ------------------------------------------ *)
        (red_expr S0 C (spec_call_error_proto_to_string_2 l (out_ter S ((resvalue_value undef) : res))) o)

  | red_spec_call_error_proto_to_string_2_not_undef :
      forall (S0 : state (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (l : object_loc (* input *)) (v : value (* input *)) (o1 : out) (o : out),
        (v <> undef) ->
        (* ========================================== *)
        (red_expr S C (spec_to_string v) o1) ->
        (red_expr S C (spec_call_error_proto_to_string_3 l o1) o) ->
        (* ------------------------------------------ *)
        (red_expr S0 C (spec_call_error_proto_to_string_2 l (out_ter S ((resvalue_value v) : res))) o)

  | red_spec_call_error_proto_to_string_3 :
      forall (S0 : state (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (l : object_loc (* input *)) (sname : string (* input *)) (o1 : out) (o : out),
        (* ========================================== *)
        (red_expr S C (spec_object_get (value_object l) ((("message")%string) : prop_name)) o1) ->
        (red_expr S C (spec_call_error_proto_to_string_4 l sname o1) o) ->
        (* ------------------------------------------ *)
        (red_expr S0 C (spec_call_error_proto_to_string_3 l (out_ter S ((resvalue_value (value_prim (prim_string sname))) : res))) o)

  | red_spec_call_error_proto_to_string_4_undef :
      forall (S0 : state (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (l : object_loc (* input *)) (sname : string (* input *)) (o : out),
        (* ========================================== *)
        (red_expr S C (spec_call_error_proto_to_string_5 l sname (out_ter S ((resvalue_value (value_prim (prim_string (("")%string)))) : res))) o) ->
        (* ------------------------------------------ *)
        (red_expr S0 C (spec_call_error_proto_to_string_4 l sname (out_ter S ((resvalue_value undef) : res))) o)

  | red_spec_call_error_proto_to_string_4_not_undef :
      forall (S0 : state (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (l : object_loc (* input *)) (sname : string (* input *)) (v : value (* input *)) (o1 : out) (o : out),
        (v <> undef) ->
        (* ========================================== *)
        (red_expr S C (spec_to_string v) o1) ->
        (red_expr S C (spec_call_error_proto_to_string_5 l sname o1) o) ->
        (* ------------------------------------------ *)
        (red_expr S0 C (spec_call_error_proto_to_string_4 l sname (out_ter S ((resvalue_value v) : res))) o)

  | red_spec_call_error_proto_to_string_5_undef :
      forall (S0 : state (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (l : object_loc (* input *)) (sname : string (* input *)) (o : out),
        (* ========================================== *)
        (red_expr S C (spec_call_error_proto_to_string_6 l sname (out_ter S ((resvalue_value (value_prim (prim_string (("")%string)))) : res))) o) ->
        (* ------------------------------------------ *)
        (red_expr S0 C (spec_call_error_proto_to_string_5 l sname (out_ter S ((resvalue_value undef) : res))) o)

  | red_spec_call_error_proto_to_string_5_not_undef :
      forall (S0 : state (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (l : object_loc (* input *)) (sname : string (* input *)) (v : value (* input *)) (o1 : out) (o : out),
        (v <> undef) ->
        (* ========================================== *)
        (red_expr S C (spec_to_string v) o1) ->
        (red_expr S C (spec_call_error_proto_to_string_6 l sname o1) o) ->
        (* ------------------------------------------ *)
        (red_expr S0 C (spec_call_error_proto_to_string_5 l sname (out_ter S ((resvalue_value v) : res))) o)

  | red_spec_call_error_proto_to_string_6 :
      forall (S0 : state (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (l : object_loc (* input *)) (sname : string (* input *)) (smsg : string (* input *)),
        (* ========================================== *)
        (* ------------------------------------------ *)
        (red_expr S0 C (spec_call_error_proto_to_string_6 l sname (out_ter S ((resvalue_value (value_prim (prim_string smsg))) : res))) (out_ter S ((resvalue_value (value_prim (prim_string (ifb (sname = (("")%string)) then smsg else (ifb (smsg = (("")%string)) then sname else (string_concat (string_concat sname ((": ")%string)) smsg)))))) : res)))

  | red_spec_call_native_error :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (v : value) (o : out) (ne : native_error (* input *)) (vthis : value (* input *)) (args : (list value) (* input *)),
        (arguments_from args (v :: (nil : (list value)))) ->
        (* ========================================== *)
        (red_expr S C (spec_build_error (value_object (object_loc_prealloc (prealloc_native_error_proto ne))) v) o) ->
        (* ------------------------------------------ *)
        (red_expr S C (spec_call_prealloc (prealloc_native_error ne) vthis args) o)

  | red_spec_construct_native_error :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (v : value) (o : out) (ne : native_error (* input *)) (args : (list value) (* input *)),
        (arguments_from args (v :: (nil : (list value)))) ->
        (* ========================================== *)
        (red_expr S C (spec_build_error (value_object (object_loc_prealloc (prealloc_native_error_proto ne))) v) o) ->
        (* ------------------------------------------ *)
        (red_expr S C (spec_construct_prealloc (prealloc_native_error ne) args) o)


with red_spec : forall {T}, state (* input *) -> execution_ctx (* input *) -> ext_spec (* input *) -> (specret T) -> Prop :=

  | red_spec_abort :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (exts : ext_spec (* input *)) (T : _) (o : out),
        ((out_of_ext_spec exts) = ((Some o) : (option out))) ->
        (abort o) ->
        (abort_intercepted_spec exts) ->
        (* ========================================== *)
        (* ------------------------------------------ *)
        (red_spec S C exts (@specret_out T o))

  | red_spec_to_int32 :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (v : value (* input *)) (o1 : out) (y : (specret int)),
        (* ========================================== *)
        (red_expr S C (spec_to_number v) o1) ->
        (red_spec S C (spec_to_int32_1 o1) y) ->
        (* ------------------------------------------ *)
        (red_spec S C (spec_to_int32 v) y)

  | red_spec_to_int32_1 :
      forall (S0 : state (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (n : number (* input *)),
        (* ========================================== *)
        (* ------------------------------------------ *)
        (red_spec S0 C (spec_to_int32_1 (out_ter S ((resvalue_value (value_prim (prim_number n))) : res))) (ret S (JsNumber.to_int32 n)))

  | red_spec_to_uint32 :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (v : value (* input *)) (o1 : out) (y : (specret int)),
        (* ========================================== *)
        (red_expr S C (spec_to_number v) o1) ->
        (red_spec S C (spec_to_uint32_1 o1) y) ->
        (* ------------------------------------------ *)
        (red_spec S C (spec_to_uint32 v) y)

  | red_spec_to_uint32_1 :
      forall (S0 : state (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (n : number (* input *)),
        (* ========================================== *)
        (* ------------------------------------------ *)
        (red_spec S0 C (spec_to_uint32_1 (out_ter S ((resvalue_value (value_prim (prim_number n))) : res))) (ret S (JsNumber.to_uint32 n)))

  | red_spec_convert_twice :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (ex1 : ext_expr (* input *)) (ex2 : ext_expr (* input *)) (o1 : out) (y : (specret (value * value))),
        (* ========================================== *)
        (red_expr S C ex1 o1) ->
        (red_spec S C (spec_convert_twice_1 o1 ex2) y) ->
        (* ------------------------------------------ *)
        (red_spec S C (spec_convert_twice ex1 ex2) y)

  | red_spec_convert_twice_1 :
      forall (S0 : state (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (v1 : value (* input *)) (ex2 : ext_expr (* input *)) (o2 : out) (y : (specret (value * value))),
        (* ========================================== *)
        (red_expr S C ex2 o2) ->
        (red_spec S C (spec_convert_twice_2 v1 o2) y) ->
        (* ------------------------------------------ *)
        (red_spec S0 C (spec_convert_twice_1 (out_ter S ((resvalue_value v1) : res)) ex2) y)

  | red_spec_convert_twice_2 :
      forall (S0 : state (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (v1 : value (* input *)) (v2 : value (* input *)),
        (* ========================================== *)
        (* ------------------------------------------ *)
        (red_spec S0 C (spec_convert_twice_2 v1 (out_ter S ((resvalue_value v2) : res))) (ret S (v1, v2)))

  | red_spec_expr_get_value_conv :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (e : expr (* input *)) (K : (value -> ext_expr) (* input *)) (y : (specret value)) (y1 : (specret value)),
        (* ========================================== *)
        (red_spec S C (spec_expr_get_value e) y1) ->
        (red_spec S C (spec_expr_get_value_conv_1 K y1) y) ->
        (* ------------------------------------------ *)
        (red_spec S C (spec_expr_get_value_conv K e) y)

  | red_spec_expr_get_value_conv_1 :
      forall (S0 : state (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (K : (value -> ext_expr) (* input *)) (v : value (* input *)) (o1 : out) (y : (specret value)),
        (* ========================================== *)
        (red_expr S C (K v) o1) ->
        (red_spec S0 C (spec_expr_get_value_conv_2 o1) y) ->
        (* ------------------------------------------ *)
        (red_spec S0 C (spec_expr_get_value_conv_1 K ((specret_val S v) : (specret value))) y)

  | red_spec_expr_get_value_conv_2 :
      forall (S0 : state (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (v : value (* input *)),
        (* ========================================== *)
        (* ------------------------------------------ *)
        (red_spec S0 C (spec_expr_get_value_conv_2 (out_ter S ((resvalue_value v) : res))) (vret S v))

  | red_spec_list_expr :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (es : (list expr) (* input *)) (y : (specret (list value))),
        (* ========================================== *)
        (red_spec S C (spec_list_expr_1 (nil : (list value)) es) y) ->
        (* ------------------------------------------ *)
        (red_spec S C (spec_list_expr es) y)

  | red_spec_list_expr_1_nil :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (vs : (list value) (* input *)),
        (* ========================================== *)
        (* ------------------------------------------ *)
        (red_spec S C (spec_list_expr_1 vs (nil : (list expr))) (ret S vs))

  | red_spec_list_expr_1_cons :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (vs : (list value) (* input *)) (es : (list expr) (* input *)) (e : expr (* input *)) (y1 : (specret value)) (y : (specret (list value))),
        (* ========================================== *)
        (red_spec S C (spec_expr_get_value e) y1) ->
        (red_spec S C (spec_list_expr_2 vs y1 es) y) ->
        (* ------------------------------------------ *)
        (red_spec S C (spec_list_expr_1 vs (e :: es)) y)

  | red_spec_list_expr_2 :
      forall (S0 : state (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (v : value (* input *)) (vs : (list value) (* input *)) (es : (list expr) (* input *)) (y : (specret (list value))),
        (* ========================================== *)
        (red_spec S C (spec_list_expr_1 (vs & v) es) y) ->
        (* ------------------------------------------ *)
        (red_spec S0 C (spec_list_expr_2 vs ((specret_val S v) : (specret value)) es) y)

  | red_spec_to_descriptor_not_object :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (v : value (* input *)) (y : (specret descriptor)),
        (((type_of v) : type) <> type_object) ->
        (* ========================================== *)
        (red_spec S C (spec_error_spec native_error_type) y) ->
        (* ------------------------------------------ *)
        (red_spec S C (spec_to_descriptor v) y)

  | red_spec_to_descriptor_object :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (l : object_loc (* input *)) (y : (specret descriptor)),
        (* ========================================== *)
        (red_spec S C (spec_to_descriptor_1a l descriptor_intro_empty) y) ->
        (* ------------------------------------------ *)
        (red_spec S C (spec_to_descriptor (value_object l)) y)

  | red_spec_to_descriptor_1a :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (o1 : out) (l : object_loc (* input *)) (Desc : descriptor (* input *)) (y : (specret descriptor)),
        (* ========================================== *)
        (red_expr S C (spec_object_has_prop l ((("enumerable")%string) : prop_name)) o1) ->
        (red_spec S C (spec_to_descriptor_1b o1 l Desc) y) ->
        (* ------------------------------------------ *)
        (red_spec S C (spec_to_descriptor_1a l Desc) y)

  | red_spec_to_descriptor_1b_false :
      forall (S0 : state (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (l : object_loc (* input *)) (Desc : descriptor (* input *)) (y : (specret descriptor)),
        (* ========================================== *)
        (red_spec S C (spec_to_descriptor_2a l Desc) y) ->
        (* ------------------------------------------ *)
        (red_spec S0 C (spec_to_descriptor_1b (out_ter S ((resvalue_value (value_prim (prim_bool ((false : provide_this_flag) : bool)))) : res)) l Desc) y)

  | red_spec_to_descriptor_1b_true :
      forall (S0 : state (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (o1 : out) (l : object_loc (* input *)) (Desc : descriptor (* input *)) (y : (specret descriptor)),
        (* ========================================== *)
        (red_expr S C (spec_object_get (value_object l) ((("enumerable")%string) : prop_name)) o1) ->
        (red_spec S C (spec_to_descriptor_1c o1 l Desc) y) ->
        (* ------------------------------------------ *)
        (red_spec S0 C (spec_to_descriptor_1b (out_ter S ((resvalue_value (value_prim (prim_bool ((true : provide_this_flag) : bool)))) : res)) l Desc) y)

  | red_spec_to_descriptor_1c :
      forall (S0 : state (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (l : object_loc (* input *)) (v : value (* input *)) (Desc : descriptor (* input *)) (y : (specret descriptor)),
        (* ========================================== *)
        (red_spec S C (spec_to_descriptor_2a l ((descriptor_with_enumerable Desc (Some (convert_value_to_boolean v))) : descriptor)) y) ->
        (* ------------------------------------------ *)
        (red_spec S0 C (spec_to_descriptor_1c (out_ter S ((resvalue_value v) : res)) l Desc) y)

  | red_spec_to_descriptor_2a :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (o1 : out) (l : object_loc (* input *)) (Desc : descriptor (* input *)) (y : (specret descriptor)),
        (* ========================================== *)
        (red_expr S C (spec_object_has_prop l ((("configurable")%string) : prop_name)) o1) ->
        (red_spec S C (spec_to_descriptor_2b o1 l Desc) y) ->
        (* ------------------------------------------ *)
        (red_spec S C (spec_to_descriptor_2a l Desc) y)

  | red_spec_to_descriptor_2b_false :
      forall (S0 : state (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (l : object_loc (* input *)) (Desc : descriptor (* input *)) (y : (specret descriptor)),
        (* ========================================== *)
        (red_spec S C (spec_to_descriptor_3a l Desc) y) ->
        (* ------------------------------------------ *)
        (red_spec S0 C (spec_to_descriptor_2b (out_ter S ((resvalue_value (value_prim (prim_bool ((false : provide_this_flag) : bool)))) : res)) l Desc) y)

  | red_spec_to_descriptor_2b_true :
      forall (S0 : state (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (o1 : out) (l : object_loc (* input *)) (Desc : descriptor (* input *)) (y : (specret descriptor)),
        (* ========================================== *)
        (red_expr S C (spec_object_get (value_object l) ((("configurable")%string) : prop_name)) o1) ->
        (red_spec S C (spec_to_descriptor_2c o1 l Desc) y) ->
        (* ------------------------------------------ *)
        (red_spec S0 C (spec_to_descriptor_2b (out_ter S ((resvalue_value (value_prim (prim_bool ((true : provide_this_flag) : bool)))) : res)) l Desc) y)

  | red_spec_to_descriptor_2c :
      forall (S0 : state (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (l : object_loc (* input *)) (v : value (* input *)) (Desc : descriptor (* input *)) (y : (specret descriptor)),
        (* ========================================== *)
        (red_spec S C (spec_to_descriptor_3a l ((descriptor_with_configurable Desc (Some (convert_value_to_boolean v))) : descriptor)) y) ->
        (* ------------------------------------------ *)
        (red_spec S0 C (spec_to_descriptor_2c (out_ter S ((resvalue_value v) : res)) l Desc) y)

  | red_spec_to_descriptor_3a :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (o1 : out) (l : object_loc (* input *)) (Desc : descriptor (* input *)) (y : (specret descriptor)),
        (* ========================================== *)
        (red_expr S C (spec_object_has_prop l ((("value")%string) : prop_name)) o1) ->
        (red_spec S C (spec_to_descriptor_3b o1 l Desc) y) ->
        (* ------------------------------------------ *)
        (red_spec S C (spec_to_descriptor_3a l Desc) y)

  | red_spec_to_descriptor_3b_false :
      forall (S0 : state (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (l : object_loc (* input *)) (Desc : descriptor (* input *)) (y : (specret descriptor)),
        (* ========================================== *)
        (red_spec S C (spec_to_descriptor_4a l Desc) y) ->
        (* ------------------------------------------ *)
        (red_spec S0 C (spec_to_descriptor_3b (out_ter S ((resvalue_value (value_prim (prim_bool ((false : provide_this_flag) : bool)))) : res)) l Desc) y)

  | red_spec_to_descriptor_3b_true :
      forall (S0 : state (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (o1 : out) (l : object_loc (* input *)) (Desc : descriptor (* input *)) (y : (specret descriptor)),
        (* ========================================== *)
        (red_expr S C (spec_object_get (value_object l) ((("value")%string) : prop_name)) o1) ->
        (red_spec S C (spec_to_descriptor_3c o1 l Desc) y) ->
        (* ------------------------------------------ *)
        (red_spec S0 C (spec_to_descriptor_3b (out_ter S ((resvalue_value (value_prim (prim_bool ((true : provide_this_flag) : bool)))) : res)) l Desc) y)

  | red_spec_to_descriptor_3c :
      forall (S0 : state (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (l : object_loc (* input *)) (v : value (* input *)) (Desc : descriptor (* input *)) (y : (specret descriptor)),
        (* ========================================== *)
        (red_spec S C (spec_to_descriptor_4a l ((descriptor_with_value Desc (Some v)) : descriptor)) y) ->
        (* ------------------------------------------ *)
        (red_spec S0 C (spec_to_descriptor_3c (out_ter S ((resvalue_value v) : res)) l Desc) y)

  | red_spec_to_descriptor_4a :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (o1 : out) (l : object_loc (* input *)) (Desc : descriptor (* input *)) (y : (specret descriptor)),
        (* ========================================== *)
        (red_expr S C (spec_object_has_prop l ((("writable")%string) : prop_name)) o1) ->
        (red_spec S C (spec_to_descriptor_4b o1 l Desc) y) ->
        (* ------------------------------------------ *)
        (red_spec S C (spec_to_descriptor_4a l Desc) y)

  | red_spec_to_descriptor_4b_false :
      forall (S0 : state (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (l : object_loc (* input *)) (Desc : descriptor (* input *)) (y : (specret descriptor)),
        (* ========================================== *)
        (red_spec S C (spec_to_descriptor_5a l Desc) y) ->
        (* ------------------------------------------ *)
        (red_spec S0 C (spec_to_descriptor_4b (out_ter S ((resvalue_value (value_prim (prim_bool ((false : provide_this_flag) : bool)))) : res)) l Desc) y)

  | red_spec_to_descriptor_4b_true :
      forall (S0 : state (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (o1 : out) (l : object_loc (* input *)) (Desc : descriptor (* input *)) (y : (specret descriptor)),
        (* ========================================== *)
        (red_expr S C (spec_object_get (value_object l) ((("writable")%string) : prop_name)) o1) ->
        (red_spec S C (spec_to_descriptor_4c o1 l Desc) y) ->
        (* ------------------------------------------ *)
        (red_spec S0 C (spec_to_descriptor_4b (out_ter S ((resvalue_value (value_prim (prim_bool ((true : provide_this_flag) : bool)))) : res)) l Desc) y)

  | red_spec_to_descriptor_4c :
      forall (S0 : state (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (l : object_loc (* input *)) (v : value (* input *)) (Desc : descriptor (* input *)) (y : (specret descriptor)),
        (* ========================================== *)
        (red_spec S C (spec_to_descriptor_5a l ((descriptor_with_writable Desc (Some (convert_value_to_boolean v))) : descriptor)) y) ->
        (* ------------------------------------------ *)
        (red_spec S0 C (spec_to_descriptor_4c (out_ter S ((resvalue_value v) : res)) l Desc) y)

  | red_spec_to_descriptor_5a :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (o1 : out) (l : object_loc (* input *)) (Desc : descriptor (* input *)) (y : (specret descriptor)),
        (* ========================================== *)
        (red_expr S C (spec_object_has_prop l ((("get")%string) : prop_name)) o1) ->
        (red_spec S C (spec_to_descriptor_5b o1 l Desc) y) ->
        (* ------------------------------------------ *)
        (red_spec S C (spec_to_descriptor_5a l Desc) y)

  | red_spec_to_descriptor_5b_false :
      forall (S0 : state (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (l : object_loc (* input *)) (Desc : descriptor (* input *)) (y : (specret descriptor)),
        (* ========================================== *)
        (red_spec S C (spec_to_descriptor_6a l Desc) y) ->
        (* ------------------------------------------ *)
        (red_spec S0 C (spec_to_descriptor_5b (out_ter S ((resvalue_value (value_prim (prim_bool ((false : provide_this_flag) : bool)))) : res)) l Desc) y)

  | red_spec_to_descriptor_5b_true :
      forall (S0 : state (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (o1 : out) (l : object_loc (* input *)) (Desc : descriptor (* input *)) (y : (specret descriptor)),
        (* ========================================== *)
        (red_expr S C (spec_object_get (value_object l) ((("get")%string) : prop_name)) o1) ->
        (red_spec S C (spec_to_descriptor_5c o1 l Desc) y) ->
        (* ------------------------------------------ *)
        (red_spec S0 C (spec_to_descriptor_5b (out_ter S ((resvalue_value (value_prim (prim_bool ((true : provide_this_flag) : bool)))) : res)) l Desc) y)

  | red_spec_to_descriptor_5c_error :
      forall (S0 : state (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (l : object_loc (* input *)) (v : value (* input *)) (Desc : descriptor (* input *)) (y : (specret descriptor)),
        (((is_callable S v) = false) /\ (v <> undef)) ->
        (* ========================================== *)
        (red_spec S C (spec_error_spec native_error_type) y) ->
        (* ------------------------------------------ *)
        (red_spec S0 C (spec_to_descriptor_5c (out_ter S ((resvalue_value v) : res)) l Desc) y)

  | red_spec_to_descriptor_5c_ok :
      forall (S0 : state (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (l : object_loc (* input *)) (v : value (* input *)) (Desc : descriptor (* input *)) (y : (specret descriptor)),
        (((is_callable S v) = false) /\ (v <> undef)) ->
        (* ========================================== *)
        (red_spec S C (spec_to_descriptor_6a l ((descriptor_with_get Desc (Some v)) : descriptor)) y) ->
        (* ------------------------------------------ *)
        (red_spec S0 C (spec_to_descriptor_5c (out_ter S ((resvalue_value v) : res)) l Desc) y)

  | red_spec_to_descriptor_6a :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (o1 : out) (l : object_loc (* input *)) (Desc : descriptor (* input *)) (y : (specret descriptor)),
        (* ========================================== *)
        (red_expr S C (spec_object_has_prop l ((("set")%string) : prop_name)) o1) ->
        (red_spec S C (spec_to_descriptor_6b o1 l Desc) y) ->
        (* ------------------------------------------ *)
        (red_spec S C (spec_to_descriptor_6a l Desc) y)

  | red_spec_to_descriptor_6b_false :
      forall (S0 : state (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (l : object_loc (* input *)) (Desc : descriptor (* input *)) (y : (specret descriptor)),
        (* ========================================== *)
        (red_spec S C (spec_to_descriptor_7 l Desc) y) ->
        (* ------------------------------------------ *)
        (red_spec S0 C (spec_to_descriptor_6b (out_ter S ((resvalue_value (value_prim (prim_bool ((false : provide_this_flag) : bool)))) : res)) l Desc) y)

  | red_spec_to_descriptor_6b_true :
      forall (S0 : state (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (o1 : out) (l : object_loc (* input *)) (Desc : descriptor (* input *)) (y : (specret descriptor)),
        (* ========================================== *)
        (red_expr S C (spec_object_get (value_object l) ((("set")%string) : prop_name)) o1) ->
        (red_spec S C (spec_to_descriptor_6c o1 l Desc) y) ->
        (* ------------------------------------------ *)
        (red_spec S0 C (spec_to_descriptor_6b (out_ter S ((resvalue_value (value_prim (prim_bool ((true : provide_this_flag) : bool)))) : res)) l Desc) y)

  | red_spec_to_descriptor_6c_error :
      forall (S0 : state (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (l : object_loc (* input *)) (v : value (* input *)) (Desc : descriptor (* input *)) (y : (specret descriptor)),
        (((is_callable S v) = false) /\ (v <> undef)) ->
        (* ========================================== *)
        (red_spec S C (spec_error_spec native_error_type) y) ->
        (* ------------------------------------------ *)
        (red_spec S0 C (spec_to_descriptor_6c (out_ter S ((resvalue_value v) : res)) l Desc) y)

  | red_spec_to_descriptor_6c_ok :
      forall (S0 : state (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (l : object_loc (* input *)) (v : value (* input *)) (Desc : descriptor (* input *)) (y : (specret descriptor)),
        (((is_callable S v) = false) /\ (v <> undef)) ->
        (* ========================================== *)
        (red_spec S C (spec_to_descriptor_7 l ((descriptor_with_set Desc (Some v)) : descriptor)) y) ->
        (* ------------------------------------------ *)
        (red_spec S0 C (spec_to_descriptor_6c (out_ter S ((resvalue_value v) : res)) l Desc) y)

  | red_spec_to_descriptor_7_error :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (l : object_loc (* input *)) (Desc : descriptor (* input *)) (y : (specret descriptor)),
        (descriptor_inconsistent Desc) ->
        (* ========================================== *)
        (red_spec S C (spec_error_spec native_error_type) y) ->
        (* ------------------------------------------ *)
        (red_spec S C (spec_to_descriptor_7 l Desc) y)

  | red_spec_to_descriptor_7_ok :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (l : object_loc (* input *)) (Desc : descriptor (* input *)),
        (descriptor_inconsistent Desc) ->
        (* ========================================== *)
        (* ------------------------------------------ *)
        (red_spec S C (spec_to_descriptor_7 l Desc) (ret S Desc))

  | red_spec_object_get_own_prop :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (l : object_loc (* input *)) (x : prop_name (* input *)) (B : builtin_get_own_prop) (y : (specret full_descriptor)),
        (object_method object_get_own_prop_ S l B) ->
        (* ========================================== *)
        (red_spec S C (spec_object_get_own_prop_1 B l x) y) ->
        (* ------------------------------------------ *)
        (red_spec S C (spec_object_get_own_prop l x) y)

  | red_spec_object_get_own_prop_1_default :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (l : object_loc (* input *)) (x : prop_name (* input *)) (Ao : (option attributes)) (y : (specret full_descriptor)),
        (object_property S l x Ao) ->
        (* ========================================== *)
        (red_spec S C (spec_object_get_own_prop_2 l x Ao) y) ->
        (* ------------------------------------------ *)
        (red_spec S C (spec_object_get_own_prop_1 builtin_get_own_prop_default l x) y)

  | red_spec_object_get_own_prop_2_none :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (l : object_loc (* input *)) (x : prop_name (* input *)),
        (* ========================================== *)
        (* ------------------------------------------ *)
        (red_spec S C (spec_object_get_own_prop_2 l x (None : (option attributes))) (dret S full_descriptor_undef))

  | red_spec_object_get_own_prop_2_some_data :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (l : object_loc (* input *)) (x : prop_name (* input *)) (A : attributes (* input *)),
        (* ========================================== *)
        (* ------------------------------------------ *)
        (red_spec S C (spec_object_get_own_prop_2 l x ((Some A) : (option attributes))) (ret S (full_descriptor_some A)))

  | red_spec_object_get_own_prop_args_obj :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (l : object_loc (* input *)) (x : prop_name (* input *)) (y : (specret full_descriptor)) (y1 : (specret full_descriptor)),
        (* ========================================== *)
        (red_spec S C (spec_object_get_own_prop_1 builtin_get_own_prop_default l x) y1) ->
        (red_spec S C (spec_args_obj_get_own_prop_1 l x y1) y) ->
        (* ------------------------------------------ *)
        (red_spec S C (spec_object_get_own_prop_1 builtin_get_own_prop_args_obj l x) y)

  | red_spec_object_get_own_prop_args_obj_1_undef :
      forall (S0 : state (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (l : object_loc (* input *)) (x : prop_name (* input *)),
        (* ========================================== *)
        (* ------------------------------------------ *)
        (red_spec S0 C (spec_args_obj_get_own_prop_1 l x ((specret_val S full_descriptor_undef) : (specret full_descriptor))) (ret S full_descriptor_undef))

  | red_spec_object_get_own_prop_args_obj_1_attrs :
      forall (lmap : object_loc) (S0 : state (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (l : object_loc (* input *)) (x : prop_name (* input *)) (A : attributes (* input *)) (y : (specret full_descriptor)) (y1 : (specret full_descriptor)),
        (object_method object_parameter_map_ S l (Some lmap)) ->
        (* ========================================== *)
        (red_spec S C (spec_object_get_own_prop lmap x) y1) ->
        (red_spec S C (spec_args_obj_get_own_prop_2 l x lmap (full_descriptor_some A) y1) y) ->
        (* ------------------------------------------ *)
        (red_spec S0 C (spec_args_obj_get_own_prop_1 l x ((specret_val S (full_descriptor_some A)) : (specret full_descriptor))) y)

  | red_spec_object_get_own_prop_args_obj_2_attrs :
      forall (o1 : out) (S0 : state (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (l : object_loc (* input *)) (x : prop_name (* input *)) (lmap : object_loc (* input *)) (A : attributes (* input *)) (Amap : attributes (* input *)) (y : (specret full_descriptor)),
        (* ========================================== *)
        (red_expr S0 C (spec_object_get (value_object lmap) x) o1) ->
        (red_spec S0 C (spec_args_obj_get_own_prop_3 (full_descriptor_some A) o1) y) ->
        (* ------------------------------------------ *)
        (red_spec S C (spec_args_obj_get_own_prop_2 l x lmap (full_descriptor_some A) ((specret_val S0 (full_descriptor_some Amap)) : (specret full_descriptor))) y)

  | red_spec_object_get_own_prop_args_obj_3 :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (Ad : attributes_data (* input *)) (S' : state (* input *)) (v : value (* input *)) (y : (specret full_descriptor)),
        (* ========================================== *)
        (red_spec S' C (spec_args_obj_get_own_prop_4 ((attributes_data_with_value Ad v) : full_descriptor)) y) ->
        (* ------------------------------------------ *)
        (red_spec S C (spec_args_obj_get_own_prop_3 (full_descriptor_some (attributes_data_of Ad)) (out_ter S' ((resvalue_value v) : res))) y)

  | red_spec_object_get_own_prop_args_obj_2_undef :
      forall (S0 : state (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (l : object_loc (* input *)) (x : prop_name (* input *)) (lmap : object_loc (* input *)) (A : attributes (* input *)) (y : (specret full_descriptor)),
        (* ========================================== *)
        (red_spec S0 C (spec_args_obj_get_own_prop_4 (full_descriptor_some A)) y) ->
        (* ------------------------------------------ *)
        (red_spec S C (spec_args_obj_get_own_prop_2 l x lmap (full_descriptor_some A) ((specret_val S0 full_descriptor_undef) : (specret full_descriptor))) y)

  | red_spec_object_get_own_prop_args_obj_4 :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (A : attributes (* input *)),
        (* ========================================== *)
        (* ------------------------------------------ *)
        (red_spec S C (spec_args_obj_get_own_prop_4 (full_descriptor_some A)) (ret S (full_descriptor_some A)))

  | red_spec_object_get_own_prop_string :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (l : object_loc (* input *)) (x : prop_name (* input *)) (y : (specret full_descriptor)) (y1 : (specret full_descriptor)),
        (* ========================================== *)
        (red_spec S C (spec_object_get_own_prop_1 builtin_get_own_prop_default l x) y1) ->
        (red_spec S C (spec_string_get_own_prop_1 l x y1) y) ->
        (* ------------------------------------------ *)
        (red_spec S C (spec_object_get_own_prop_1 builtin_get_own_prop_string l x) y)

  | red_spec_object_get_own_prop_string_1_attrs :
      forall (S0 : state (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (l : object_loc (* input *)) (x : prop_name (* input *)) (A : attributes (* input *)),
        (* ========================================== *)
        (* ------------------------------------------ *)
        (red_spec S0 C (spec_string_get_own_prop_1 l x ((specret_val S (full_descriptor_some A)) : (specret full_descriptor))) (ret S (full_descriptor_some A)))

  | red_spec_object_get_own_prop_string_1_undef :
      forall (S0 : state (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (l : object_loc (* input *)) (x : prop_name (* input *)) (y1 : (specret int)) (y : (specret full_descriptor)),
        (* ========================================== *)
        (red_spec S C (spec_to_int32 (value_prim (prim_string (x : string)))) y1) ->
        (red_spec S C (spec_string_get_own_prop_2 l x y1) y) ->
        (* ------------------------------------------ *)
        (red_spec S0 C (spec_string_get_own_prop_1 l x ((specret_val S full_descriptor_undef) : (specret full_descriptor))) y)

  | red_spec_object_get_own_prop_string_2 :
      forall (S0 : state (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (l : object_loc (* input *)) (x : prop_name (* input *)) (k : int (* input *)) (o1 : out) (y : (specret full_descriptor)),
        (* ========================================== *)
        (red_expr S C (spec_to_string ((abs k) : value)) o1) ->
        (red_spec S C (spec_string_get_own_prop_3 l x o1) y) ->
        (* ------------------------------------------ *)
        (red_spec S0 C (spec_string_get_own_prop_2 l x ((specret_val S k) : (specret int))) y)

  | red_spec_object_get_own_prop_string_3_different :
      forall (S0 : state (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (l : object_loc (* input *)) (x : prop_name (* input *)) (x' : prop_name (* input *)),
        (x <> x') ->
        (* ========================================== *)
        (* ------------------------------------------ *)
        (red_spec S0 C (spec_string_get_own_prop_3 l x (out_ter S ((resvalue_value (value_prim (prim_string (x' : string)))) : res))) (ret S full_descriptor_undef))

  | red_spec_object_get_own_prop_string_3_same :
      forall (S0 : state (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (l : object_loc (* input *)) (s : string) (x : prop_name (* input *)) (y : (specret full_descriptor)),
        (object_prim_value S l (value_prim (prim_string s))) ->
        (* ========================================== *)
        (red_spec S C (spec_string_get_own_prop_4 x s) y) ->
        (* ------------------------------------------ *)
        (red_spec S0 C (spec_string_get_own_prop_3 l x (out_ter S ((resvalue_value (value_prim (prim_string (x : string)))) : res))) y)

  | red_spec_object_get_own_prop_string_4 :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (x : prop_name (* input *)) (s : string (* input *)) (y1 : (specret int)) (y : (specret full_descriptor)),
        (* ========================================== *)
        (red_spec S C (spec_to_int32 (value_prim (prim_string (x : string)))) y1) ->
        (red_spec S C (spec_string_get_own_prop_5 s y1) y) ->
        (* ------------------------------------------ *)
        (red_spec S C (spec_string_get_own_prop_4 x s) y)

  | red_spec_object_get_own_prop_string_5 :
      forall (S0 : state (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (s : string (* input *)) (idx : int (* input *)) (len : nat) (y : (specret full_descriptor)),
        (len = (String.length s)) ->
        (* ========================================== *)
        (red_spec S C (spec_string_get_own_prop_6 s idx (my_Z_of_nat len)) y) ->
        (* ------------------------------------------ *)
        (red_spec S0 C (spec_string_get_own_prop_5 s ((specret_val S idx) : (specret int))) y)

  | red_spec_object_get_own_prop_string_6_outofbounds :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (s : string (* input *)) (idx : int (* input *)) (len : int (* input *)),
        (len <= idx) ->
        (* ========================================== *)
        (* ------------------------------------------ *)
        (red_spec S C (spec_string_get_own_prop_6 s idx len) (ret S full_descriptor_undef))

  | red_spec_object_get_own_prop_string_6_inbounds :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (s : string (* input *)) (idx : int (* input *)) (len : int (* input *)),
        (len > idx) ->
        (* ========================================== *)
        (* ------------------------------------------ *)
        (red_spec S C (spec_string_get_own_prop_6 s idx len) (ret S (full_descriptor_some (attributes_data_of (attributes_data_intro ((string_sub s idx (1%nat)) : value) false true false)))))

  | red_spec_ref_get_value_value :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (v : value (* input *)),
        (* ========================================== *)
        (* ------------------------------------------ *)
        (red_spec S C (spec_get_value (resvalue_value v)) (ret S v))

  | red_spec_ref_get_value_ref_a :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (r : ref (* input *)) (y : (specret value)),
        (ref_is_unresolvable r) ->
        (* ========================================== *)
        (red_spec S C (spec_error_spec native_error_ref) y) ->
        (* ------------------------------------------ *)
        (red_spec S C (spec_get_value (resvalue_ref r)) y)

  | red_spec_ref_get_value_ref_b :
      forall (ext_get : (value -> (prop_name -> ext_expr))) (v : value) (S : state (* input *)) (C : execution_ctx (* input *)) (r : ref (* input *)) (o1 : out) (y : (specret value)),
        (ref_is_property r) ->
        ((ref_base r) = (ref_base_type_value v)) ->
        (ext_get = (ifb (ref_has_primitive_base r) then spec_prim_value_get else spec_object_get)) ->
        (* ========================================== *)
        (red_expr S C (ext_get v (ref_name r)) o1) ->
        (red_spec S C (spec_get_value_ref_b_1 o1) y) ->
        (* ------------------------------------------ *)
        (red_spec S C (spec_get_value (resvalue_ref r)) y)

  | red_spec_ref_get_value_ref_b_1 :
      forall (S0 : state (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (v : value (* input *)),
        (* ========================================== *)
        (* ------------------------------------------ *)
        (red_spec S0 C (spec_get_value_ref_b_1 (out_ter S ((resvalue_value v) : res))) (ret S v))

  | red_spec_ref_get_value_ref_c :
      forall (L : env_loc) (S : state (* input *)) (C : execution_ctx (* input *)) (r : ref (* input *)) (o1 : out) (y : (specret value)),
        ((ref_base r) = (ref_base_type_env_loc L)) ->
        (* ========================================== *)
        (red_expr S C (spec_env_record_get_binding_value L (ref_name r) (ref_strict r)) o1) ->
        (red_spec S C (spec_get_value_ref_c_1 o1) y) ->
        (* ------------------------------------------ *)
        (red_spec S C (spec_get_value (resvalue_ref r)) y)

  | red_spec_ref_get_value_ref_c_1 :
      forall (S0 : state (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (v : value (* input *)),
        (* ========================================== *)
        (* ------------------------------------------ *)
        (red_spec S0 C (spec_get_value_ref_c_1 (out_ter S ((resvalue_value v) : res))) (ret S v))

  | red_spec_expr_get_value :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (e : expr (* input *)) (o1 : out) (y : (specret value)),
        (* ========================================== *)
        (red_expr S C (expr_basic e) o1) ->
        (red_spec S C (spec_expr_get_value_1 o1) y) ->
        (* ------------------------------------------ *)
        (red_spec S C (spec_expr_get_value e) y)

  | red_spec_expr_get_value_1 :
      forall (S0 : state (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (rv : resvalue (* input *)) (y : (specret value)),
        (* ========================================== *)
        (red_spec S C (spec_get_value rv) y) ->
        (* ------------------------------------------ *)
        (red_spec S0 C (spec_expr_get_value_1 (out_ter S (rv : res))) y)

  | red_spec_lexical_env_get_identifier_ref_nil :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (x : prop_name (* input *)) (str : strictness_flag (* input *)),
        (* ========================================== *)
        (* ------------------------------------------ *)
        (red_spec S C (spec_lexical_env_get_identifier_ref (nil : lexical_env) x (str : bool)) (ret S ((ref_create_value undef x str) : ref)))

  | red_spec_lexical_env_get_identifier_ref_cons :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (L : env_loc (* input *)) (lexs : (list env_loc) (* input *)) (x : prop_name (* input *)) (str : strictness_flag (* input *)) (y : (specret ref)),
        (* ========================================== *)
        (red_spec S C (spec_lexical_env_get_identifier_ref_1 L (lexs : lexical_env) x (str : bool)) y) ->
        (* ------------------------------------------ *)
        (red_spec S C (spec_lexical_env_get_identifier_ref ((L :: lexs) : lexical_env) x (str : bool)) y)

  | red_spec_lexical_env_get_identifier_ref_cons_1 :
      forall (o1 : out) (S : state (* input *)) (C : execution_ctx (* input *)) (L : env_loc (* input *)) (lexs : lexical_env (* input *)) (x : prop_name (* input *)) (str : strictness_flag (* input *)) (y : (specret ref)),
        (* ========================================== *)
        (red_expr S C (spec_env_record_has_binding L x) o1) ->
        (red_spec S C (spec_lexical_env_get_identifier_ref_2 L lexs x (str : bool) o1) y) ->
        (* ------------------------------------------ *)
        (red_spec S C (spec_lexical_env_get_identifier_ref_1 L lexs x (str : bool)) y)

  | red_spec_lexical_env_get_identifier_ref_cons_2_true :
      forall (S0 : state (* input *)) (C : execution_ctx (* input *)) (L : env_loc (* input *)) (lexs : lexical_env (* input *)) (x : prop_name (* input *)) (str : strictness_flag (* input *)) (S : state (* input *)),
        (* ========================================== *)
        (* ------------------------------------------ *)
        (red_spec S0 C (spec_lexical_env_get_identifier_ref_2 L lexs x (str : bool) (out_ter S ((resvalue_value (value_prim (prim_bool ((true : provide_this_flag) : bool)))) : res))) (ret S ((ref_create_env_loc L x str) : ref)))

  | red_spec_lexical_env_get_identifier_ref_cons_2_false :
      forall (S0 : state (* input *)) (C : execution_ctx (* input *)) (L : env_loc (* input *)) (lexs : lexical_env (* input *)) (x : prop_name (* input *)) (str : strictness_flag (* input *)) (S : state (* input *)) (y : (specret ref)),
        (* ========================================== *)
        (red_spec S C (spec_lexical_env_get_identifier_ref lexs x (str : bool)) y) ->
        (* ------------------------------------------ *)
        (red_spec S0 C (spec_lexical_env_get_identifier_ref_2 L lexs x (str : bool) (out_ter S ((resvalue_value (value_prim (prim_bool ((false : provide_this_flag) : bool)))) : res))) y)

  | red_spec_error_spec :
      forall (T : _) (S : state (* input *)) (C : execution_ctx (* input *)) (ne : native_error (* input *)) (o1 : out) (y : (specret T)),
        (* ========================================== *)
        (red_expr S C (spec_error ne) o1) ->
        (red_spec S C (spec_error_spec_1 o1) y) ->
        (* ------------------------------------------ *)
        (red_spec S C (spec_error_spec ne) y)

  | red_spec_object_get_prop :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (l : object_loc (* input *)) (x : prop_name (* input *)) (B : builtin_get_prop) (y : (specret full_descriptor)),
        (object_method object_get_prop_ S l B) ->
        (* ========================================== *)
        (red_spec S C (spec_object_get_prop_1 B l x) y) ->
        (* ------------------------------------------ *)
        (red_spec S C (spec_object_get_prop l x) y)

  | red_spec_object_get_prop_1_default :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (l : object_loc (* input *)) (x : prop_name (* input *)) (y1 : (specret full_descriptor)) (y : (specret full_descriptor)),
        (* ========================================== *)
        (red_spec S C (spec_object_get_own_prop l x) y1) ->
        (red_spec S C (spec_object_get_prop_2 l x y1) y) ->
        (* ------------------------------------------ *)
        (red_spec S C (spec_object_get_prop_1 builtin_get_prop_default l x) y)

  | red_spec_object_get_prop_2_not_undef :
      forall (S0 : state (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (l : object_loc (* input *)) (x : prop_name (* input *)) (A : attributes (* input *)),
        (* ========================================== *)
        (* ------------------------------------------ *)
        (red_spec S0 C (spec_object_get_prop_2 l x ((specret_val S (full_descriptor_some A)) : (specret full_descriptor))) (ret S (full_descriptor_some A)))

  | red_spec_object_get_prop_2_undef :
      forall (S0 : state (* input *)) (S : state (* input *)) (C : execution_ctx (* input *)) (l : object_loc (* input *)) (x : prop_name (* input *)) (vproto : value) (y : (specret full_descriptor)),
        (object_proto S l vproto) ->
        (* ========================================== *)
        (red_spec S C (spec_object_get_prop_3 l x vproto) y) ->
        (* ------------------------------------------ *)
        (red_spec S0 C (spec_object_get_prop_2 l x ((specret_val S full_descriptor_undef) : (specret full_descriptor))) y)

  | red_spec_object_get_prop_3_null :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (l : object_loc (* input *)) (x : prop_name (* input *)),
        (* ========================================== *)
        (* ------------------------------------------ *)
        (red_spec S C (spec_object_get_prop_3 l x null) (dret S full_descriptor_undef))

  | red_spec_object_get_prop_3_not_null :
      forall (S : state (* input *)) (C : execution_ctx (* input *)) (l : object_loc (* input *)) (x : prop_name (* input *)) (lproto : object_loc (* input *)) (y : (specret full_descriptor)),
        (* ========================================== *)
        (red_spec S C (spec_object_get_prop lproto x) y) ->
        (* ------------------------------------------ *)
        (red_spec S C (spec_object_get_prop_3 l x (value_object lproto)) y)
  .


(******************************************)

