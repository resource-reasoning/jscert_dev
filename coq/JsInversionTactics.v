Set Implicit Arguments.
Require Import Shared.
Require Import JsSyntax JsSyntaxAux JsCommon JsCommonAux JsPreliminary.
Require Import JsPrettyInterm JsPrettyRules.
Require Export JsInversionPrinciplesSpec (* JsInversionPrinciplesExpr *) JsInversionPrinciplesStat JsInversionPrinciplesProg.

(**************************************************************)
(** ** Speeding up inversion                                  *)

Ltac inverts_tactic_general T H :=
  let rec go :=
    match goal with
     | H : ?x = ?x |- _ => clear H; go
     | |- (ltac_Mark -> _) => intros _
     | |- (existT ?P ?p ?x = existT ?P ?p ?y -> _) =>
         let H := fresh in intro H;
         generalize (@inj_pair2 _ P p x y H);
         clear H; go 
     | |- (?x = ?y -> _) => let H := fresh in intro H;
                           first [ subst x | subst y | injects H ];
                           go 
     | |- (?P -> ?Q) => intro; go 
     | |- (forall _, _) => intro; go      
    end in
  generalize ltac_mark; T H; go;
  unfold eq' in *.

(**************************************************************)
(** ** HNF for extended expressions                           *)

Ltac red_spec_hnf e := 
match (eval hnf in e) with
  | ?e1 => constr:e1
end.

Ltac red_expr_hnf e := 
match (eval hnf in e) with
  | expr_basic ?e1 =>
      let e1' := (eval hnf in e1) in
      constr:(expr_basic e1')
  | ?e1 => constr:e1
end.

Ltac red_stat_hnf e := 
match (eval hnf in e) with
  | stat_basic ?e1 =>
      let e1' := (eval hnf in e1) in
      constr:(stat_basic e1')
  | ?e1 => constr:e1
end.

Ltac red_prog_hnf e := 
match (eval hnf in e) with
  | prog_basic ?e1 =>
      let e1' := (eval hnf in e1) in
      constr:(prog_basic e1')
  | ?e1 => constr:e1
end.

(**************************************************************)
(** ** Inversion for specs                                    *)

Tactic Notation "invert" "keep" "red_spec" hyp(H) := 
match type of H with
  | red_spec ?S ?C (?e) ?oo => 
    let eh := red_spec_hnf e in
    try (asserts_rewrite (e = eh) in H; [reflexivity | idtac]); 
    match eh with
      | spec_to_int32 _ => inversion H using inv_red_spec_spec_to_int32
      | spec_to_int32_1 _ => inversion H using inv_red_spec_spec_to_int32_1
      | spec_to_uint32 _ => inversion H using inv_red_spec_spec_to_uint32
      | spec_to_uint32_1 _ => inversion H using inv_red_spec_spec_to_uint32_1
      | spec_expr_get_value_conv _ _ => inversion H using inv_red_spec_spec_expr_get_value_conv
      | spec_expr_get_value_conv_1 _ _ => inversion H using inv_red_spec_spec_expr_get_value_conv_1
      | spec_expr_get_value_conv_2 _ => inversion H using inv_red_spec_spec_expr_get_value_conv_2
      | spec_convert_twice _ _ => inversion H using inv_red_spec_spec_convert_twice
      | spec_convert_twice_1 _ _ => inversion H using inv_red_spec_spec_convert_twice_1
      | spec_convert_twice_2 _ _ => inversion H using inv_red_spec_spec_convert_twice_2
      | spec_list_expr _ => inversion H using inv_red_spec_spec_list_expr
      | spec_list_expr_1 _ _ => inversion H using inv_red_spec_spec_list_expr_1
      | spec_list_expr_2 _ _ _ => inversion H using inv_red_spec_spec_list_expr_2
      | spec_to_descriptor _ => inversion H using inv_red_spec_spec_to_descriptor
      | spec_to_descriptor_1a _ _ => inversion H using inv_red_spec_spec_to_descriptor_1a
      | spec_to_descriptor_1b _ _ _ => inversion H using inv_red_spec_spec_to_descriptor_1b
      | spec_to_descriptor_1c _ _ _ => inversion H using inv_red_spec_spec_to_descriptor_1c
      | spec_to_descriptor_2a _ _ => inversion H using inv_red_spec_spec_to_descriptor_2a
      | spec_to_descriptor_2b _ _ _ => inversion H using inv_red_spec_spec_to_descriptor_2b
      | spec_to_descriptor_2c _ _ _ => inversion H using inv_red_spec_spec_to_descriptor_2c
      | spec_to_descriptor_3a _ _ => inversion H using inv_red_spec_spec_to_descriptor_3a
      | spec_to_descriptor_3b _ _ _ => inversion H using inv_red_spec_spec_to_descriptor_3b
      | spec_to_descriptor_3c _ _ _ => inversion H using inv_red_spec_spec_to_descriptor_3c
      | spec_to_descriptor_4a _ _ => inversion H using inv_red_spec_spec_to_descriptor_4a
      | spec_to_descriptor_4b _ _ _ => inversion H using inv_red_spec_spec_to_descriptor_4b
      | spec_to_descriptor_4c _ _ _ => inversion H using inv_red_spec_spec_to_descriptor_4c
      | spec_to_descriptor_5a _ _ => inversion H using inv_red_spec_spec_to_descriptor_5a
      | spec_to_descriptor_5b _ _ _ => inversion H using inv_red_spec_spec_to_descriptor_5b
      | spec_to_descriptor_5c _ _ _ => inversion H using inv_red_spec_spec_to_descriptor_5c
      | spec_to_descriptor_6a _ _ => inversion H using inv_red_spec_spec_to_descriptor_6a
      | spec_to_descriptor_6b _ _ _=> inversion H using inv_red_spec_spec_to_descriptor_6b
      | spec_to_descriptor_6c _ _ _ => inversion H using inv_red_spec_spec_to_descriptor_6c
      | spec_to_descriptor_7 _ _ => inversion H using inv_red_spec_spec_to_descriptor_7
      | spec_object_get_own_prop _ _ => inversion H using inv_red_spec_spec_object_get_own_prop
      | spec_object_get_own_prop_1 _ _ _ => inversion H using inv_red_spec_spec_object_get_own_prop_1
      | spec_object_get_own_prop_2 _ _ _ => inversion H using inv_red_spec_spec_object_get_own_prop_2
      | spec_object_get_prop _ _ => inversion H using inv_red_spec_spec_object_get_prop
      | spec_object_get_prop_1 _ _ _ => inversion H using inv_red_spec_spec_object_get_prop_1
      | spec_object_get_prop_2 _ _ _ => inversion H using inv_red_spec_spec_object_get_prop_2
      | spec_object_get_prop_3 _ _ _ => inversion H using inv_red_spec_spec_object_get_prop_3
      | spec_get_value _ => inversion H using inv_red_spec_spec_get_value
      | spec_get_value_ref_b_1 _ => inversion H using inv_red_spec_spec_get_value_ref_b_1
      | spec_get_value_ref_c_1 _ => inversion H using inv_red_spec_spec_get_value_ref_c_1
      | spec_expr_get_value _ => inversion H using inv_red_spec_spec_expr_get_value
      | spec_expr_get_value_1 _ => inversion H using inv_red_spec_spec_expr_get_value_1
      | spec_lexical_env_get_identifier_ref _ _ _ => inversion H using inv_red_spec_spec_lexical_env_get_identifier_ref
      | spec_lexical_env_get_identifier_ref_1 _ _ _ _ => inversion H using inv_red_spec_spec_lexical_env_get_identifier_ref_1
      | spec_lexical_env_get_identifier_ref_2 _ _ _ _ _ => inversion H using inv_red_spec_spec_lexical_env_get_identifier_ref_2
      | spec_error_spec _ => inversion H using inv_red_spec_spec_error_spec
      | spec_error_spec_1 _ => inversion H using inv_red_spec_spec_error_spec_1
      | spec_args_obj_get_own_prop_1 _ _ _ => inversion H using inv_red_spec_spec_args_obj_get_own_prop_1
      | spec_args_obj_get_own_prop_2 _ _ _ _ _ => inversion H using inv_red_spec_spec_args_obj_get_own_prop_2
      | spec_args_obj_get_own_prop_3 _ _ => inversion H using inv_red_spec_spec_args_obj_get_own_prop_3
      | spec_args_obj_get_own_prop_4 _ => inversion H using inv_red_spec_spec_args_obj_get_own_prop_4
      | spec_string_get_own_prop_1 _ _ _ => inversion H using inv_red_spec_spec_string_get_own_prop_1
      | spec_string_get_own_prop_2 _ _ _ => inversion H using inv_red_spec_spec_string_get_own_prop_2
      | spec_string_get_own_prop_3 _ _ _ => inversion H using inv_red_spec_spec_string_get_own_prop_3
      | spec_string_get_own_prop_4 _ _ => inversion H using inv_red_spec_spec_string_get_own_prop_4
      | spec_string_get_own_prop_5 _ _ => inversion H using inv_red_spec_spec_string_get_own_prop_5
      | spec_string_get_own_prop_6 _ _ _ => inversion H using inv_red_spec_spec_string_get_own_prop_6
      | spec_function_proto_apply_get_args _ _ _ => inversion H using inv_red_spec_spec_function_proto_apply_get_args
      | spec_function_proto_apply_get_args_1 _ _ _ _ => inversion H using inv_red_spec_spec_function_proto_apply_get_args_1
      | spec_function_proto_apply_get_args_2 _ _ _ _ => inversion H using inv_red_spec_spec_function_proto_apply_get_args_2
      | spec_function_proto_apply_get_args_3 _ _ => inversion H using inv_red_spec_spec_function_proto_apply_get_args_3
      | spec_function_proto_bind_length _ _ => inversion H using inv_red_spec_spec_function_proto_bind_length
      | spec_function_proto_bind_length_1 _ _ => inversion H using inv_red_spec_spec_function_proto_bind_length_1
      | spec_function_proto_bind_length_2 _ _ => inversion H using inv_red_spec_spec_function_proto_bind_length_2
      | spec_function_proto_bind_length_3 _ _ => inversion H using inv_red_spec_spec_function_proto_bind_length_3
      | spec_call_array_proto_join_vtsfj _ _ => inversion H using inv_red_spec_spec_call_array_proto_join_vtsfj
      | spec_call_array_proto_join_vtsfj_1 _ _ => inversion H using inv_red_spec_spec_call_array_proto_join_vtsfj_1
      | spec_call_array_proto_join_vtsfj_2 _ _ => inversion H using inv_red_spec_spec_call_array_proto_join_vtsfj_2
      | spec_call_array_proto_join_vtsfj_3 _ => inversion H using inv_red_spec_spec_call_array_proto_join_vtsfj_3
    end
end; tryfalse; clear H; intro H.

Tactic Notation "inverts" "keep" "red_spec" hyp(H) := 
  inverts_tactic_general ltac:(fun H => invert keep red_spec H) H. 

Tactic Notation "inverts" "red_spec" hyp(H) := 
  inverts keep red_spec H; clear H.

(**************************************************************)
(** ** Inversion for programs                                 *)

Tactic Notation "invert" "keep" "red_stat" hyp(H) := 
match type of H with
  | red_stat ?S ?C (?e) ?oo => 
    let eh := red_stat_hnf e in
    try (asserts_rewrite (e = eh) in H; [reflexivity | idtac]); 
    match eh with
      | stat_basic (stat_expr _) => inversion H using inv_red_stat_expr
      | stat_basic (stat_label _ _) => inversion H using inv_red_stat_label
      | stat_basic (stat_block _) => inversion H using inv_red_stat_block
      | stat_basic (stat_var_decl _) => inversion H using inv_red_stat_var_decl
      | stat_basic (stat_if _ _ _) => inversion H using inv_red_stat_if
      | stat_basic (stat_do_while _ _ _) => inversion H using inv_red_stat_do_while
      | stat_basic (stat_with _ _) => inversion H using inv_red_stat_with
      | stat_basic (stat_throw _) => inversion H using inv_red_stat_throw
      | stat_basic (stat_return _) => inversion H using inv_red_stat_return
      | stat_basic (stat_break _) => inversion H using inv_red_stat_break
      | stat_basic (stat_continue _) => inversion H using inv_red_stat_continue
      | stat_basic (stat_try _ _ _) => inversion H using inv_red_stat_try
      | stat_basic (stat_for _ _ _ _ _) => inversion H using inv_red_stat_for
      | stat_basic (stat_for_var _ _ _ _ _) => inversion H using inv_red_stat_for_var
      | stat_basic (stat_for_in _ _ _ _) => inversion H using inv_red_stat_for_in
      | stat_basic (stat_for_in_var _ _ _ _ _) => inversion H using inv_red_stat_for_in_var
      | stat_basic (stat_debugger) => inversion H using inv_red_stat_debugger
      | stat_basic (stat_switch _ _ _) => inversion H using inv_red_stat_switch
      | stat_expr_1 _ => inversion H using inv_red_stat_stat_expr_1
      | stat_block_1 _ _ => inversion H using inv_red_stat_stat_block_1
      | stat_block_2 _ _ => inversion H using inv_red_stat_stat_block_2
      | stat_label_1 _ _ => inversion H using inv_red_stat_stat_label_1
      | stat_var_decl_1 _ _ => inversion H using inv_red_stat_stat_var_decl_1
      | stat_var_decl_item _ => inversion H using inv_red_stat_stat_var_decl_item
      | stat_var_decl_item_1 _ _ _ => inversion H using inv_red_stat_stat_var_decl_item_1
      | stat_var_decl_item_2 _ _ _ => inversion H using inv_red_stat_stat_var_decl_item_2
      | stat_var_decl_item_3 _ _ => inversion H using inv_red_stat_stat_var_decl_item_3
      | stat_if_1 _ _ _ => inversion H using inv_red_stat_stat_if_1
      | stat_while_1 _ _ _ _ => inversion H using inv_red_stat_stat_while_1
      | stat_while_2 _ _ _ _ _ => inversion H using inv_red_stat_stat_while_2
      | stat_while_3 _ _ _ _ _ => inversion H using inv_red_stat_stat_while_3
      | stat_while_4 _ _ _ _ _ => inversion H using inv_red_stat_stat_while_4
      | stat_while_5 _ _ _ _ _ => inversion H using inv_red_stat_stat_while_5
      | stat_while_6 _ _ _ _ _ => inversion H using inv_red_stat_stat_while_6
      | stat_do_while_1 _ _ _ _ => inversion H using inv_red_stat_stat_do_while_1
      | stat_do_while_2 _ _ _ _ _ => inversion H using inv_red_stat_stat_do_while_2
      | stat_do_while_3 _ _ _ _ _ => inversion H using inv_red_stat_stat_do_while_3
      | stat_do_while_4 _ _ _ _ _ => inversion H using inv_red_stat_stat_do_while_4
      | stat_do_while_5 _ _ _ _ _ => inversion H using inv_red_stat_stat_do_while_5
      | stat_do_while_6 _ _ _ _ => inversion H using inv_red_stat_stat_do_while_6
      | stat_do_while_7 _ _ _ _ _ => inversion H using inv_red_stat_stat_do_while_7
      | stat_for_1 _ _ _ _ _ => inversion H using inv_red_stat_stat_for_1
      | stat_for_2 _ _ _ _ _ => inversion H using inv_red_stat_stat_for_2
      | stat_for_3 _ _ _ _ _ _ => inversion H using inv_red_stat_stat_for_3
      | stat_for_4 _ _ _ _ _ => inversion H using inv_red_stat_stat_for_4
      | stat_for_5 _ _ _ _ _ _ => inversion H using inv_red_stat_stat_for_5
      | stat_for_6 _ _ _ _ _ _ => inversion H using inv_red_stat_stat_for_6
      | stat_for_7 _ _ _ _ _ _ => inversion H using inv_red_stat_stat_for_7
      | stat_for_8 _ _ _ _ _ => inversion H using inv_red_stat_stat_for_8
      | stat_for_9 _ _ _ _ _ _ => inversion H using inv_red_stat_stat_for_9
      | stat_for_var_1 _ _ _ _ _ => inversion H using inv_red_stat_stat_for_var_1
      | stat_with_1 _ _ => inversion H using inv_red_stat_stat_with_1
      | stat_throw_1 _ => inversion H using inv_red_stat_stat_throw_1
      | stat_return_1 _ => inversion H using inv_red_stat_stat_return_1
      | stat_try_1 _ _ _ => inversion H using inv_red_stat_stat_try_1
      | stat_try_2 _ _ _ _ => inversion H using inv_red_stat_stat_try_2
      | stat_try_3 _ _ => inversion H using inv_red_stat_stat_try_3
      | stat_try_4 _ _ => inversion H using inv_red_stat_stat_try_4
      | stat_try_5 _ _ => inversion H using inv_red_stat_stat_try_5
      | stat_switch_1 _ _ _ => inversion H using inv_red_stat_stat_switch_1
      | stat_switch_2 _ _ => inversion H using inv_red_stat_stat_switch_2
      | stat_switch_nodefault_1 _ _ _=> inversion H using inv_red_stat_stat_switch_nodefault_1
      | stat_switch_nodefault_2 _ _ _ _ _  => inversion H using inv_red_stat_stat_switch_nodefault_2
      | stat_switch_nodefault_3 _ _ _ _ _ => inversion H using inv_red_stat_stat_switch_nodefault_3
      | stat_switch_nodefault_4 _ _ => inversion H using inv_red_stat_stat_switch_nodefault_4
      | stat_switch_nodefault_5 _ _ => inversion H using inv_red_stat_stat_switch_nodefault_5
      | stat_switch_nodefault_6 _ _ _ => inversion H using inv_red_stat_stat_switch_nodefault_6
      | stat_switch_default_1 _ _ _ _ _ => inversion H using inv_red_stat_stat_switch_default_1
      | stat_switch_default_A_1 _ _ _ _ _ _ => inversion H using inv_red_stat_stat_switch_default_A_1
      | stat_switch_default_A_2 _ _ _ _ _ _ _ => inversion H using inv_red_stat_stat_switch_default_A_2
      | stat_switch_default_A_3 _ _ _ _ _ _ _  => inversion H using inv_red_stat_stat_switch_default_A_3
      | stat_switch_default_A_4 _ _ _ _ _ _ => inversion H using inv_red_stat_stat_switch_default_A_4
      | stat_switch_default_A_5 _ _ _ _ _ _ => inversion H using inv_red_stat_stat_switch_default_A_5
      | stat_switch_default_B_1 _ _ _ _ => inversion H using inv_red_stat_stat_switch_default_B_1
      | stat_switch_default_B_2 _ _ _ _ _ _ => inversion H using inv_red_stat_stat_switch_default_B_2
      | stat_switch_default_B_3 _ _ _ _ _ _ => inversion H using inv_red_stat_stat_switch_default_B_3
      | stat_switch_default_B_4 _ _ _ => inversion H using inv_red_stat_stat_switch_default_B_4
      | stat_switch_default_5 _ _ _ _ => inversion H using inv_red_stat_stat_switch_default_5
      | stat_switch_default_6 _ _ => inversion H using inv_red_stat_stat_switch_default_6
      | stat_switch_default_7 _ _  => inversion H using inv_red_stat_stat_switch_default_7
      | stat_switch_default_8 _ _ _ => inversion H using inv_red_stat_stat_switch_default_8
    end
end; tryfalse; clear H; intro H.

Tactic Notation "inverts" "keep" "red_stat" hyp(H) := 
  inverts_tactic_general ltac:(fun H => invert keep red_stat H) H.

Tactic Notation "inverts" "red_stat" hyp(H) := 
  inverts keep red_stat H; clear H.

(**************************************************************)
(** ** Inversion for programs                                 *)

Tactic Notation "invert" "keep" "red_prog" hyp(H) := 
match type of H with
  | red_prog ?S ?C (?e) ?oo => 
    let eh := red_prog_hnf e in
    try (asserts_rewrite (e = eh) in H; [reflexivity | idtac]); 
    match eh with
      | prog_basic (prog_intro _ _) => inversion H using inv_red_prog_intro
      | javascript_1 _ _ => inversion H using inv_red_prog_javascript
      | prog_1 _ _ => inversion H using inv_red_prog_prog_1
      | prog_2 _ _ => inversion H using inv_red_prog_prog_2
    end
end; tryfalse; clear H; intro H.

Tactic Notation "inverts" "keep" "red_prog" hyp(H) := 
  inverts_tactic_general ltac:(fun H => invert keep red_prog H) H.

Tactic Notation "inverts" "red_prog" hyp(H) := 
  inverts keep red_prog H; clear H.

(**************************************************************)
(** ** Inversion for expressions                              *)

(* 
Tactic Notation "invert" "keep" "red_expr" hyp(H) := 
match type of H with
  | red_expr ?S ?C (?e) ?oo => 
    let eh := red_expr_hnf e in
    try (asserts_rewrite (e = eh) in H; [reflexivity | idtac]); 
    match eh with
      | expr_basic expr_this => inversion H using inv_red_expr_this
      | expr_basic (expr_identifier _) => inversion H using inv_red_expr_identifier
      | expr_basic (expr_literal _) => inversion H using inv_red_expr_literal
      | expr_basic (expr_object _) => inversion H using inv_red_expr_object
      | expr_basic (expr_array _) => inversion H using inv_red_expr_array
      | expr_basic (expr_function _ _ _) => inversion H using inv_red_expr_function
      | expr_basic (expr_access _ _) => inversion H using inv_red_expr_access
      | expr_basic (expr_member _ _) => inversion H using inv_red_expr_member
      | expr_basic (expr_new _ _) => inversion H using inv_red_expr_new
      | expr_basic (expr_call _ _) => inversion H using inv_red_expr_call
      | expr_basic (expr_unary_op _ _) => inversion H using inv_red_expr_unary_op
      | expr_basic (expr_binary_op _ _ _) => inversion H using inv_red_expr_binary_op
      | expr_basic (expr_conditional _ _ _) => inversion H using inv_red_expr_conditional
      | expr_basic (expr_assign _ _ _) => inversion H using inv_red_expr_assign
      | expr_identifier_1 _ => inversion H using inv_red_expr_expr_identifier_1
      | expr_object_0 _ _ => inversion H using inv_red_expr_expr_object_0
      | expr_object_1 _ _ => inversion H using inv_red_expr_expr_object_1
      | expr_object_2 _ _ _ _ => inversion H using inv_red_expr_expr_object_2
      | expr_object_3_val _ _ _ _ => inversion H using inv_red_expr_expr_object_3_val
      | expr_object_3_get _ _ _ _ => inversion H using inv_red_expr_expr_object_3_get
      | expr_object_3_set _ _ _ _ => inversion H using inv_red_expr_expr_object_3_set
      | expr_object_4 _ _ _ _ => inversion H using inv_red_expr_expr_object_4
      | expr_object_5 _ _ _ => inversion H using inv_red_expr_expr_object_5
      | expr_array_0 _ _ => inversion H using inv_red_expr_expr_array_0
      | expr_array_1 _ _ => inversion H using inv_red_expr_expr_array_1
      | expr_array_2 _ _ _ => inversion H using inv_red_expr_expr_array_2
      | expr_array_3 _ _ _ => inversion H using inv_red_expr_expr_array_3
      | expr_array_3_1 _ _ _ _ => inversion H using inv_red_expr_expr_array_3_1
      | expr_array_3_2 _ _ _ _ _ => inversion H using inv_red_expr_expr_array_3_2
      | expr_array_3_3 _ _ _ _ _ => inversion H using inv_red_expr_expr_array_3_3
      | expr_array_3_4 _ _ _ _ => inversion H using inv_red_expr_expr_array_3_4
      | expr_array_3_5 _ _ _ => inversion H using inv_red_expr_expr_array_3_5
      | expr_array_add_length   _ _ _ => inversion H using inv_red_expr_expr_array_add_length
      | expr_array_add_length_0 _ _ => inversion H using inv_red_expr_expr_array_add_length_0
      | expr_array_add_length_1 _ _ _ => inversion H using inv_red_expr_expr_array_add_length_1
      | expr_array_add_length_2 _ _ _ => inversion H using inv_red_expr_expr_array_add_length_2
      | expr_array_add_length_3 _ _ => inversion H using inv_red_expr_expr_array_add_length_3
      | expr_array_add_length_4 _ _ => inversion H using inv_red_expr_expr_array_add_length_4
      | expr_function_1 _ _ _ _ _ _ => inversion H using inv_red_expr_expr_function_1
      | expr_function_2 _ _ _ => inversion H using inv_red_expr_expr_function_2
      | expr_function_3 _ _ => inversion H using inv_red_expr_expr_function_3
      | expr_access_1 _ _ => inversion H using inv_red_expr_expr_access_1
      | expr_access_2 _ _ => inversion H using inv_red_expr_expr_access_2
      | expr_access_3 _ _ _ => inversion H using inv_red_expr_expr_access_3
      | expr_access_4 _ _ => inversion H using inv_red_expr_expr_access_4
      | expr_new_1 _ _ => inversion H using inv_red_expr_expr_new_1
      | expr_new_2 _ _ => inversion H using inv_red_expr_expr_new_2
      | expr_call_1 _ _ _ => inversion H using inv_red_expr_expr_call_1
      | expr_call_2 _ _ _ _ => inversion H using inv_red_expr_expr_call_2
      | expr_call_3 _ _ _ _ => inversion H using inv_red_expr_expr_call_3
      | expr_call_4 _ _ _ _ => inversion H using inv_red_expr_expr_call_4
      | expr_call_5 _ _ _ _ => inversion H using inv_red_expr_expr_call_5
      | spec_eval _ _ _ => inversion H using inv_red_expr_spec_eval
      | expr_unary_op_1 _ _ => inversion H using inv_red_expr_expr_unary_op_1
      | expr_unary_op_2 _ _ => inversion H using inv_red_expr_expr_unary_op_2
      | expr_delete_1 _ => inversion H using inv_red_expr_expr_delete_1
      | expr_delete_2 _ => inversion H using inv_red_expr_expr_delete_2
      | expr_delete_3 _ _ => inversion H using inv_red_expr_expr_delete_3
      | expr_delete_4 _ _ => inversion H using inv_red_expr_expr_delete_4
      | expr_typeof_1 _ => inversion H using inv_red_expr_expr_typeof_1
      | expr_typeof_2 _ => inversion H using inv_red_expr_expr_typeof_2
      | expr_prepost_1 _ _ => inversion H using inv_red_expr_expr_prepost_1
      | expr_prepost_2 _ _ _ => inversion H using inv_red_expr_expr_prepost_2
      | expr_prepost_3 _ _ _ => inversion H using inv_red_expr_expr_prepost_3
      | expr_prepost_4 _ _ => inversion H using inv_red_expr_expr_prepost_4
      | expr_unary_op_neg_1 _ => inversion H using inv_red_expr_expr_unary_op_neg_1
      | expr_unary_op_bitwise_not_1 _ => inversion H using inv_red_expr_expr_unary_op_bitwise_not_1
      | expr_unary_op_not_1 _ => inversion H using inv_red_expr_expr_unary_op_not_1
      | expr_conditional_1 _ _ _ => inversion H using inv_red_expr_expr_conditional_1
      | expr_conditional_1' _ _ _ => inversion H using inv_red_expr_expr_conditional_1
      | expr_conditional_2 _ => inversion H using inv_red_expr_expr_conditional_2
      | expr_binary_op_1 _ _ _ => inversion H using inv_red_expr_expr_binary_op_1
      | expr_binary_op_2 _ _ _ => inversion H using inv_red_expr_expr_binary_op_2
      | expr_binary_op_3 _ _ _ => inversion H using inv_red_expr_expr_binary_op_3
      | expr_binary_op_add_1 _ => inversion H using inv_red_expr_expr_binary_op_add_1
      | expr_binary_op_add_string_1 _ => inversion H using inv_red_expr_expr_binary_op_add_string_1
      | expr_puremath_op_1 _ _ => inversion H using inv_red_expr_expr_puremath_op_1
      | expr_shift_op_1 _ _ _ => inversion H using inv_red_expr_expr_shift_op_1
      | expr_shift_op_2 _ _ _ => inversion H using inv_red_expr_expr_shift_op_2
      | expr_inequality_op_1 _ _ _ _ => inversion H using inv_red_expr_expr_inequality_op_1
      | expr_inequality_op_2 _ _ _ => inversion H using inv_red_expr_expr_inequality_op_2
      | expr_binary_op_in_1 _ _ => inversion H using inv_red_expr_expr_binary_op_in_1
      | expr_binary_op_disequal_1 _ => inversion H using inv_red_expr_expr_binary_op_disequal_1
      | spec_equal _ _ => inversion H using inv_red_expr_spec_equal
      | spec_equal_1 _ _ _ _ => inversion H using inv_red_expr_spec_equal_1
      | spec_equal_2 _ => inversion H using inv_red_expr_spec_equal_2
      | spec_equal_3 _ _ _ => inversion H using inv_red_expr_spec_equal_3
      | spec_equal_4 _ _ => inversion H using inv_red_expr_spec_equal_4
      | expr_bitwise_op_1 _ _ _ => inversion H using inv_red_expr_expr_bitwise_op_1
      | expr_bitwise_op_2 _ _ _ => inversion H using inv_red_expr_expr_bitwise_op_2
      | expr_lazy_op_1 _ _ _ => inversion H using inv_red_expr_expr_lazy_op_1
      | expr_lazy_op_2 _ _ _ _ => inversion H using inv_red_expr_expr_lazy_op_2
      | expr_lazy_op_2_1 _ => inversion H using inv_red_expr_expr_lazy_op_2_1
      | expr_assign_1 _ _ _ => inversion H using inv_red_expr_expr_assign_1
      | expr_assign_2 _ _ _ _ => inversion H using inv_red_expr_expr_assign_2
      | expr_assign_3 _ _ _ _ => inversion H using inv_red_expr_expr_assign_3
      | expr_assign_3' _ _ => inversion H using inv_red_expr_expr_assign_3
      | expr_assign_4 _ _ => inversion H using inv_red_expr_expr_assign_4
      | expr_assign_5 _ _ => inversion H using inv_red_expr_expr_assign_5
      | spec_to_primitive _ _ => inversion H using inv_red_expr_spec_to_primitive
      | spec_to_boolean _ => inversion H using inv_red_expr_spec_to_boolean
      | spec_to_number _ => inversion H using inv_red_expr_spec_to_number
      | spec_to_number_1 _ => inversion H using inv_red_expr_spec_to_number_1
      | spec_to_integer _ => inversion H using inv_red_expr_spec_to_integer
      | spec_to_integer_1 _ => inversion H using inv_red_expr_spec_to_integer_1
      | spec_to_string _ => inversion H using inv_red_expr_spec_to_string
      | spec_to_string_1 _ => inversion H using inv_red_expr_spec_to_string_1
      | spec_to_object _ => inversion H using inv_red_expr_spec_to_object
      | spec_check_object_coercible _ => inversion H using inv_red_expr_spec_check_object_coercible
      | spec_eq _ _ => inversion H using inv_red_expr_spec_eq
      | spec_eq0 _ _ => inversion H using inv_red_expr_spec_eq0
      | spec_eq1 _ _ => inversion H using inv_red_expr_spec_eq1
      | spec_eq2 _ _ _ => inversion H using inv_red_expr_spec_eq2
      | spec_object_get _ _ => inversion H using inv_red_expr_spec_object_get
      | spec_object_get_1 _ _ _ _ => inversion H using inv_red_expr_spec_object_get_1
      | spec_object_get_2 _ _ => inversion H using inv_red_expr_spec_object_get_2
      | spec_object_get_3 _ _ => inversion H using inv_red_expr_spec_object_get_3
      | spec_object_can_put _ _ => inversion H using inv_red_expr_spec_object_can_put
      | spec_object_can_put_1 _ _ _ => inversion H using inv_red_expr_spec_object_can_put_1
      | spec_object_can_put_2 _ _ _ => inversion H using inv_red_expr_spec_object_can_put_2
      | spec_object_can_put_4 _ _ _ => inversion H using inv_red_expr_spec_object_can_put_4
      | spec_object_can_put_5 _ _ => inversion H using inv_red_expr_spec_object_can_put_5
      | spec_object_can_put_6 _ _ => inversion H using inv_red_expr_spec_object_can_put_6
      | spec_object_put _ _ _ _ => inversion H using inv_red_expr_spec_object_put
      | spec_object_put_1 _ _ _ _ _ _ => inversion H using inv_red_expr_spec_object_put_1
      | spec_object_put_2 _ _ _ _ _ _ => inversion H using inv_red_expr_spec_object_put_2
      | spec_object_put_3 _ _ _ _ _ _ => inversion H using inv_red_expr_spec_object_put_3
      | spec_object_put_4 _ _ _ _ _ _ => inversion H using inv_red_expr_spec_object_put_4
      | spec_object_put_5 _ => inversion H using inv_red_expr_spec_object_put_5
      | spec_object_has_prop _ _ => inversion H using inv_red_expr_spec_object_has_prop
      | spec_object_has_prop_1 _ _ _ => inversion H using inv_red_expr_spec_object_has_prop_1
      | spec_object_has_prop_2 _ => inversion H using inv_red_expr_spec_object_has_prop_2
      | spec_object_delete _ _ _ => inversion H using inv_red_expr_spec_object_delete
      | spec_object_delete_1 _ _ _ _ => inversion H using inv_red_expr_spec_object_delete_1
      | spec_object_delete_2 _ _ _ _ => inversion H using inv_red_expr_spec_object_delete_2
      | spec_object_delete_3 _ _ _ _ => inversion H using inv_red_expr_spec_object_delete_3
      | spec_object_default_value _ _ => inversion H using inv_red_expr_spec_object_default_value
      | spec_object_default_value_1 _ _ _ => inversion H using inv_red_expr_spec_object_default_value_1
      | spec_object_default_value_2 _ _ _ => inversion H using inv_red_expr_spec_object_default_value_2
      | spec_object_default_value_3 _ _ => inversion H using inv_red_expr_spec_object_default_value_3
      | spec_object_default_value_4 => inversion H using inv_red_expr_spec_object_default_value_4
      | spec_object_default_value_sub_1 _ _ _ => inversion H using inv_red_expr_spec_object_default_value_sub_1
      | spec_object_default_value_sub_2 _ _ _ => inversion H using inv_red_expr_spec_object_default_value_sub_2
      | spec_object_default_value_sub_3 _ _ => inversion H using inv_red_expr_spec_object_default_value_sub_3
      | spec_object_define_own_prop _ _ _ _ => inversion H using inv_red_expr_spec_object_define_own_prop
      | spec_object_define_own_prop_1 _ _ _ _ _ => inversion H using inv_red_expr_spec_object_define_own_prop_1
      | spec_object_define_own_prop_2 _ _ _ _ _ => inversion H using inv_red_expr_spec_object_define_own_prop_2
      | spec_object_define_own_prop_3 _ _ _ _ _ _ => inversion H using inv_red_expr_spec_object_define_own_prop_3
      | spec_object_define_own_prop_4 _ _ _ _ _ => inversion H using inv_red_expr_spec_object_define_own_prop_4
      | spec_object_define_own_prop_5 _ _ _ _ _ => inversion H using inv_red_expr_spec_object_define_own_prop_5
      | spec_object_define_own_prop_6a _ _ _ _ _ => inversion H using inv_red_expr_spec_object_define_own_prop_6a
      | spec_object_define_own_prop_6b _ _ _ _ _ => inversion H using inv_red_expr_spec_object_define_own_prop_6b
      | spec_object_define_own_prop_6c _ _ _ _ _ => inversion H using inv_red_expr_spec_object_define_own_prop_6c
      | spec_object_define_own_prop_reject _ => inversion H using inv_red_expr_spec_object_define_own_prop_reject
      | spec_object_define_own_prop_write _ _ _ _ _ => inversion H using inv_red_expr_spec_object_define_own_prop_write
      | spec_object_define_own_prop_array_2 _ _ _ _ _ => inversion H using inv_red_expr_spec_object_define_own_prop_array_2
      | spec_object_define_own_prop_array_2_1 _ _ _ _ _ _ => inversion H using inv_red_expr_spec_object_define_own_prop_array_2_1
      | spec_object_define_own_prop_array_branch_3_4 _ _ _ _ _ _ => inversion H using inv_red_expr_spec_object_define_own_prop_array_branch_3_4
      | spec_object_define_own_prop_array_branch_4_5 _ _ _ _ _ _ => inversion H using inv_red_expr_spec_object_define_own_prop_array_branch_4_5
      | spec_object_define_own_prop_array_branch_4_5_a _ _ _ _ _ _ _ => inversion H using inv_red_expr_spec_object_define_own_prop_array_branch_4_5_a
      | spec_object_define_own_prop_array_branch_4_5_b _ _ _ _ _ _ _ _ => inversion H using inv_red_expr_spec_object_define_own_prop_array_branch_4_5_b
      | spec_object_define_own_prop_array_4a _ _ _ _ _ _ => inversion H using inv_red_expr_spec_object_define_own_prop_array_4a
      | spec_object_define_own_prop_array_4b _ _ _ _ _ _ _ => inversion H using inv_red_expr_spec_object_define_own_prop_array_4b
      | spec_object_define_own_prop_array_4c _ _ _ _ _ _ _ => inversion H using inv_red_expr_spec_object_define_own_prop_array_4c
      | spec_object_define_own_prop_array_5 _ _ _ _ => inversion H using inv_red_expr_spec_object_define_own_prop_array_5
      | spec_object_define_own_prop_array_3 _ _ _ _ _ => inversion H using inv_red_expr_spec_object_define_own_prop_array_3
      | spec_object_define_own_prop_array_3c _ _ _ _ _ _ _ => inversion H using inv_red_expr_spec_object_define_own_prop_array_3c
      | spec_object_define_own_prop_array_3d_e _ _ _ _ _ _ _ => inversion H using inv_red_expr_spec_object_define_own_prop_array_3d_e
      | spec_object_define_own_prop_array_3f_g _ _ _ _ _ _ => inversion H using inv_red_expr_spec_object_define_own_prop_array_3f_g
      | spec_object_define_own_prop_array_3h_i _ _ _ _ _ _ => inversion H using inv_red_expr_spec_object_define_own_prop_array_3h_i
      | spec_object_define_own_prop_array_3j _ _ _ _ _ _ _ => inversion H using inv_red_expr_spec_object_define_own_prop_array_3j
      | spec_object_define_own_prop_array_3k_l _ _ _ _ _ _ _ _ => inversion H using inv_red_expr_spec_object_define_own_prop_array_3k_l
      | spec_object_define_own_prop_array_3l _ _ _ _ _ _ => inversion H using inv_red_expr_spec_object_define_own_prop_array_3l
      | spec_object_define_own_prop_array_3l_ii _ _ _ _ _ _ => inversion H using inv_red_expr_spec_object_define_own_prop_array_3l_ii
      | spec_object_define_own_prop_array_3l_ii_1 _ _ _ _ _ _ _ => inversion H using inv_red_expr_spec_object_define_own_prop_array_3l_ii_1
      | spec_object_define_own_prop_array_3l_ii_2 _ _ _ _ _ _ _ => inversion H using inv_red_expr_spec_object_define_own_prop_array_3l_ii_2
      | spec_object_define_own_prop_array_3l_iii_1 _ _ _ _ _ => inversion H using inv_red_expr_spec_object_define_own_prop_array_3l_iii_1
      | spec_object_define_own_prop_array_3l_iii_2 _ _ _ _ => inversion H using inv_red_expr_spec_object_define_own_prop_array_3l_iii_2
      | spec_object_define_own_prop_array_3l_iii_3 _ _ _ => inversion H using inv_red_expr_spec_object_define_own_prop_array_3l_iii_3
      | spec_object_define_own_prop_array_3l_iii_4 _ _ _ => inversion H using inv_red_expr_spec_object_define_own_prop_array_3l_iii_4
      | spec_object_define_own_prop_array_3m_n _ _ => inversion H using inv_red_expr_spec_object_define_own_prop_array_3m_n
      | spec_prim_value_get _ _ => inversion H using inv_red_expr_spec_prim_value_get
      | spec_prim_value_get_1 _ _ _ => inversion H using inv_red_expr_spec_prim_value_get_1
      | spec_prim_value_put _ _ _ _ => inversion H using inv_red_expr_spec_prim_value_put
      | spec_prim_value_put_1 _ _ _ _ _ => inversion H using inv_red_expr_spec_prim_value_put_1
      | spec_put_value _ _ => inversion H using inv_red_expr_spec_put_value
      | spec_env_record_has_binding _ _ => inversion H using inv_red_expr_spec_env_record_has_binding
      | spec_env_record_has_binding_1 _ _ _ => inversion H using inv_red_expr_spec_env_record_has_binding_1
      | spec_env_record_get_binding_value _ _ _ => inversion H using inv_red_expr_spec_env_record_get_binding_value
      | spec_env_record_get_binding_value_1 _ _ _ _ => inversion H using inv_red_expr_spec_env_record_get_binding_value_1
      | spec_env_record_get_binding_value_2 _ _ _ _ => inversion H using inv_red_expr_spec_env_record_get_binding_value_2
      | spec_env_record_create_immutable_binding _ _ => inversion H using inv_red_expr_spec_env_record_create_immutable_binding
      | spec_env_record_initialize_immutable_binding _ _ _ => inversion H using inv_red_expr_spec_env_record_initialize_immutable_binding
      | spec_env_record_create_mutable_binding _ _ _ => inversion H using inv_red_expr_spec_env_record_create_mutable_binding
      | spec_env_record_create_mutable_binding_1 _ _ _ _ => inversion H using inv_red_expr_spec_env_record_create_mutable_binding_1
      | spec_env_record_create_mutable_binding_2 _ _ _ _ _ => inversion H using inv_red_expr_spec_env_record_create_mutable_binding_2
      | spec_env_record_create_mutable_binding_3 _ => inversion H using inv_red_expr_spec_env_record_create_mutable_binding_3
      | spec_env_record_set_mutable_binding _ _ _ _ => inversion H using inv_red_expr_spec_env_record_set_mutable_binding
      | spec_env_record_set_mutable_binding_1 _ _ _ _ _ => inversion H using inv_red_expr_spec_env_record_set_mutable_binding_1
      | spec_env_record_delete_binding _ _ => inversion H using inv_red_expr_spec_env_record_delete_binding
      | spec_env_record_delete_binding_1 _ _ _ => inversion H using inv_red_expr_spec_env_record_delete_binding_1
      | spec_env_record_create_set_mutable_binding _ _ _ _ _ => inversion H using inv_red_expr_spec_env_record_create_set_mutable_binding
      | spec_env_record_create_set_mutable_binding_1 _ _ _ _ _ => inversion H using inv_red_expr_spec_env_record_create_set_mutable_binding_1
      | spec_env_record_implicit_this_value _ => inversion H using inv_red_expr_spec_env_record_implicit_this_value
      | spec_env_record_implicit_this_value_1 _ _ => inversion H using inv_red_expr_spec_env_record_implicit_this_value_1
      | spec_from_descriptor _ => inversion H using inv_red_expr_spec_from_descriptor
      | spec_from_descriptor_1 _ _ => inversion H using inv_red_expr_spec_from_descriptor_1
      | spec_from_descriptor_2 _ _ _ => inversion H using inv_red_expr_spec_from_descriptor_2
      | spec_from_descriptor_3 _ _ _ => inversion H using inv_red_expr_spec_from_descriptor_3
      | spec_from_descriptor_4 _ _ _ => inversion H using inv_red_expr_spec_from_descriptor_4
      | spec_from_descriptor_5 _ _ _ => inversion H using inv_red_expr_spec_from_descriptor_5
      | spec_from_descriptor_6 _ _ => inversion H using inv_red_expr_spec_from_descriptor_6
      | spec_entering_eval_code _ _ _ => inversion H using inv_red_expr_spec_entering_eval_code
      | spec_entering_eval_code_1 _ _ _ => inversion H using inv_red_expr_spec_entering_eval_code_1
      | spec_entering_eval_code_2 _ _ => inversion H using inv_red_expr_spec_entering_eval_code_2
      | spec_call_global_eval _ _ => inversion H using inv_red_expr_spec_call_global_eval
      | spec_call_global_eval_1 _ _ => inversion H using inv_red_expr_spec_call_global_eval_1
      | spec_call_global_eval_2 _ => inversion H using inv_red_expr_spec_call_global_eval_2
      | spec_call_global_eval_3 _ => inversion H using inv_red_expr_spec_call_global_eval_3
      | spec_entering_func_code _ _ _ _ => inversion H using inv_red_expr_spec_entering_func_code
      | spec_entering_func_code_1 _ _ _ _ _ _ => inversion H using inv_red_expr_spec_entering_func_code_1
      | spec_entering_func_code_2 _ _ _ _ _ => inversion H using inv_red_expr_spec_entering_func_code_2
      | spec_entering_func_code_3 _ _ _ _ _ _ => inversion H using inv_red_expr_spec_entering_func_code_3
      | spec_entering_func_code_4 _ _ => inversion H using inv_red_expr_spec_entering_func_code_4
      | spec_binding_inst_formal_params _ _ _ _ => inversion H using inv_red_expr_spec_binding_inst_formal_params
      | spec_binding_inst_formal_params_1 _ _ _ _ _ _ _ => inversion H using inv_red_expr_spec_binding_inst_formal_params_1
      | spec_binding_inst_formal_params_2 _ _ _ _ _ _ _ => inversion H using inv_red_expr_spec_binding_inst_formal_params_2
      | spec_binding_inst_formal_params_3 _ _ _ _ _ _ => inversion H using inv_red_expr_spec_binding_inst_formal_params_3
      | spec_binding_inst_formal_params_4 _ _ _ _ _ => inversion H using inv_red_expr_spec_binding_inst_formal_params_4
      | spec_binding_inst_function_decls _ _ _ _ => inversion H using inv_red_expr_spec_binding_inst_function_decls
      | spec_binding_inst_function_decls_1 _ _ _ _ _ _ => inversion H using inv_red_expr_spec_binding_inst_function_decls_1
      | spec_binding_inst_function_decls_2 _ _ _ _ _ _ _ => inversion H using inv_red_expr_spec_binding_inst_function_decls_2
      | spec_binding_inst_function_decls_3 _ _ _ _ _ _ => inversion H using inv_red_expr_spec_binding_inst_function_decls_3
      | spec_binding_inst_function_decls_3a _ _ _ _ _ _ => inversion H using inv_red_expr_spec_binding_inst_function_decls_3a
      | spec_binding_inst_function_decls_4 _ _ _ _ _ _ _ => inversion H using inv_red_expr_spec_binding_inst_function_decls_4
      | spec_binding_inst_function_decls_5 _ _ _ _ _ _ => inversion H using inv_red_expr_spec_binding_inst_function_decls_5
      | spec_binding_inst_function_decls_6 _ _ _ _ _ => inversion H using inv_red_expr_spec_binding_inst_function_decls_6
      | spec_binding_inst_arg_obj   object_loc _ _ _ _ => inversion H using inv_red_expr_spec_binding_inst_arg_obj
      | spec_binding_inst_arg_obj_1 _ _ _ => inversion H using inv_red_expr_spec_binding_inst_arg_obj_1
      | spec_binding_inst_arg_obj_2 _ _ _ => inversion H using inv_red_expr_spec_binding_inst_arg_obj_2
      | spec_binding_inst_var_decls _ _ _ _ => inversion H using inv_red_expr_spec_binding_inst_var_decls
      | spec_binding_inst_var_decls_1 _ _ _ _ _ _ => inversion H using inv_red_expr_spec_binding_inst_var_decls_1
      | spec_binding_inst_var_decls_2 _ _ _ _ _ => inversion H using inv_red_expr_spec_binding_inst_var_decls_2
      | spec_binding_inst _ _ _ _ => inversion H using inv_red_expr_spec_binding_inst
      | spec_binding_inst_1 _ _ _ _ _ => inversion H using inv_red_expr_spec_binding_inst_1
      | spec_binding_inst_2 _ _ _ _ _ _ _ => inversion H using inv_red_expr_spec_binding_inst_2
      | spec_binding_inst_3 _ _ _ _ _ _ => inversion H using inv_red_expr_spec_binding_inst_3
      | spec_binding_inst_4 _ _ _ _ _ _ _ _ => inversion H using inv_red_expr_spec_binding_inst_4
      | spec_binding_inst_5 _ _ _ _ _ _ _ => inversion H using inv_red_expr_spec_binding_inst_5
      | spec_binding_inst_6 _ _ _ _ _ _ _ _ => inversion H using inv_red_expr_spec_binding_inst_6
      | spec_binding_inst_7 _ _ _ _ => inversion H using inv_red_expr_spec_binding_inst_7
      | spec_binding_inst_8 _ _ _ => inversion H using inv_red_expr_spec_binding_inst_8
      | spec_make_arg_getter _ _ => inversion H using inv_red_expr_spec_make_arg_getter
      | spec_make_arg_setter _ _ => inversion H using inv_red_expr_spec_make_arg_setter
      | spec_args_obj_get_1 _ _ _ _ _ => inversion H using inv_red_expr_spec_args_obj_get_1
      | spec_args_obj_define_own_prop_1 _ _ _ _ _ _ => inversion H using inv_red_expr_spec_args_obj_define_own_prop_1
      | spec_args_obj_define_own_prop_2 _ _ _ _ _ _ _ => inversion H using inv_red_expr_spec_args_obj_define_own_prop_2
      | spec_args_obj_define_own_prop_3 _ _ _ _ _ _ => inversion H using inv_red_expr_spec_args_obj_define_own_prop_3
      | spec_args_obj_define_own_prop_4 _ _ _ _ _ => inversion H using inv_red_expr_spec_args_obj_define_own_prop_4
      | spec_args_obj_define_own_prop_5 _ => inversion H using inv_red_expr_spec_args_obj_define_own_prop_5
      | spec_args_obj_define_own_prop_6 => inversion H using inv_red_expr_spec_args_obj_define_own_prop_6
      | spec_args_obj_delete_1 _ _ _ _ _ => inversion H using inv_red_expr_spec_args_obj_delete_1
      | spec_args_obj_delete_2 _ _ _ _ _ _ => inversion H using inv_red_expr_spec_args_obj_delete_2
      | spec_args_obj_delete_3 _ => inversion H using inv_red_expr_spec_args_obj_delete_3
      | spec_args_obj_delete_4 _ => inversion H using inv_red_expr_spec_args_obj_delete_4
      | spec_arguments_object_map _ _ _ _ _ => inversion H using inv_red_expr_spec_arguments_object_map
      | spec_arguments_object_map_1 _ _ _ _ _ _ => inversion H using inv_red_expr_spec_arguments_object_map_1
      | spec_arguments_object_map_2 _ _ _ _ _ _ _ _ => inversion H using inv_red_expr_spec_arguments_object_map_2
      | spec_arguments_object_map_3 _ _ _ _ _ _ _ _ _ => inversion H using inv_red_expr_spec_arguments_object_map_3
      | spec_arguments_object_map_4 _ _ _ _ _ _ _ _ _ => inversion H using inv_red_expr_spec_arguments_object_map_4
      | spec_arguments_object_map_5 _ _ _ _ _ _ _ _ _ _ => inversion H using inv_red_expr_spec_arguments_object_map_5
      | spec_arguments_object_map_6 _ _ _ _ _ _ _ _ _ _ => inversion H using inv_red_expr_spec_arguments_object_map_6
      | spec_arguments_object_map_7 _ _ _ _ _ _ _ _ _ => inversion H using inv_red_expr_spec_arguments_object_map_7
      | spec_arguments_object_map_8 _ _ _  => inversion H using inv_red_expr_spec_arguments_object_map_8
      | spec_create_arguments_object _ _ _ _ _ => inversion H using inv_red_expr_spec_create_arguments_object
      | spec_create_arguments_object_1 _ _ _ _ _ _ _ => inversion H using inv_red_expr_spec_create_arguments_object_1
      | spec_create_arguments_object_2 _ _ _ _ => inversion H using inv_red_expr_spec_create_arguments_object_2
      | spec_create_arguments_object_3 _ _ _ _ => inversion H using inv_red_expr_spec_create_arguments_object_3
      | spec_create_arguments_object_4 _ _ => inversion H using inv_red_expr_spec_create_arguments_object_4
      | spec_object_has_instance _ _ => inversion H using inv_red_expr_spec_object_has_instance
      | spec_object_has_instance_1 _ _ _ => inversion H using inv_red_expr_spec_object_has_instance_1
      | spec_function_has_instance_1 _ _ => inversion H using inv_red_expr_spec_function_has_instance_1
      | spec_function_has_instance_2 _ _ => inversion H using inv_red_expr_spec_function_has_instance_2
      | spec_function_has_instance_3 _ _ => inversion H using inv_red_expr_spec_function_has_instance_3
      | spec_function_has_instance_after_bind_1 _ _ => inversion H using inv_red_expr_spec_function_has_instance_after_bind_1
      | spec_function_has_instance_after_bind_2 _ _ => inversion H using inv_red_expr_spec_function_has_instance_after_bind_2
      | spec_function_get_1 _ _ _ => inversion H using inv_red_expr_spec_function_get_1
      | spec_error _ => inversion H using inv_red_expr_spec_error
      | spec_error_1 _ => inversion H using inv_red_expr_spec_error_1
      | spec_error_or_cst _ _ _ => inversion H using inv_red_expr_spec_error_or_cst
      | spec_error_or_void _ _ => inversion H using inv_red_expr_spec_error_or_void
      | spec_init_throw_type_error => inversion H using inv_red_expr_spec_init_throw_type_error
      | spec_init_throw_type_error_1 _ => inversion H using inv_red_expr_spec_init_throw_type_error_1
      | spec_build_error _ _ => inversion H using inv_red_expr_spec_build_error
      | spec_build_error_1 _ _ => inversion H using inv_red_expr_spec_build_error_1
      | spec_build_error_2 _ _ => inversion H using inv_red_expr_spec_build_error_2
      | spec_new_object _ => inversion H using inv_red_expr_spec_new_object
      | spec_new_object_1 _ _ => inversion H using inv_red_expr_spec_new_object_1
      | spec_prim_new_object _ => inversion H using inv_red_expr_spec_prim_new_object
      | spec_creating_function_object_proto _ => inversion H using inv_red_expr_spec_creating_function_object_proto
      | spec_creating_function_object_proto_1 _ _ => inversion H using inv_red_expr_spec_creating_function_object_proto_1
      | spec_creating_function_object_proto_2 _ _ _ => inversion H using inv_red_expr_spec_creating_function_object_proto_2
      | spec_creating_function_object _ _ _ _ => inversion H using inv_red_expr_spec_creating_function_object
      | spec_creating_function_object_1 _ _ _ => inversion H using inv_red_expr_spec_creating_function_object_1
      | spec_creating_function_object_2 _ _ _ => inversion H using inv_red_expr_spec_creating_function_object_2
      | spec_creating_function_object_3 _ _ => inversion H using inv_red_expr_spec_creating_function_object_3
      | spec_creating_function_object_4 _ _ => inversion H using inv_red_expr_spec_creating_function_object_4
      | spec_function_proto_apply _ _ _ => inversion H using inv_red_expr_spec_function_proto_apply
      | spec_function_proto_apply_1 _ _ _ _ => inversion H using inv_red_expr_spec_function_proto_apply_1
      | spec_function_proto_apply_2 _ _ _ _ => inversion H using inv_red_expr_spec_function_proto_apply_2
      | spec_function_proto_apply_3 _ _ _ => inversion H using inv_red_expr_spec_function_proto_apply_3
      | spec_function_proto_bind_1 _ _ _ => inversion H using inv_red_expr_spec_function_proto_bind_1
      | spec_function_proto_bind_2 _ _ _ => inversion H using inv_red_expr_spec_function_proto_bind_2
      | spec_function_proto_bind_3 _ _ => inversion H using inv_red_expr_spec_function_proto_bind_3
      | spec_function_proto_bind_4 _ _ => inversion H using inv_red_expr_spec_function_proto_bind_4
      | spec_function_proto_bind_5 _ => inversion H using inv_red_expr_spec_function_proto_bind_5
      | spec_function_proto_bind_6 _ _ => inversion H using inv_red_expr_spec_function_proto_bind_6
      | spec_function_proto_bind_7 _ _ => inversion H using inv_red_expr_spec_function_proto_bind_7
      | spec_create_new_function_in _ _ _ => inversion H using inv_red_expr_spec_create_new_function_in
      | spec_call _ _ _ => inversion H using inv_red_expr_spec_call
      | spec_call_1 _ _ _ _ => inversion H using inv_red_expr_spec_call_1
      | spec_call_prealloc _ _ _ => inversion H using inv_red_expr_spec_call_prealloc
      | spec_call_default _ _ _ => inversion H using inv_red_expr_spec_call_default
      | spec_call_default_1 _ => inversion H using inv_red_expr_spec_call_default_1
      | spec_call_default_2 _ => inversion H using inv_red_expr_spec_call_default_2
      | spec_call_default_3 _ => inversion H using inv_red_expr_spec_call_default_3
      | spec_construct _ _ => inversion H using inv_red_expr_spec_construct
      | spec_construct_1 _ _ _ => inversion H using inv_red_expr_spec_construct_1
      | spec_construct_prealloc _ _ => inversion H using inv_red_expr_spec_construct_prealloc
      | spec_construct_default _ _ => inversion H using inv_red_expr_spec_construct_default
      | spec_construct_default_1 _ _ _ => inversion H using inv_red_expr_spec_construct_default_1
      | spec_construct_default_2 _ _ => inversion H using inv_red_expr_spec_construct_default_2
      | spec_construct_1_after_bind _ _ _ => inversion H using inv_red_expr_spec_construct_1_after_bind
      | spec_construct_bool_1 _ => inversion H using inv_red_expr_spec_construct_bool_1
      | spec_construct_number_1 _ => inversion H using inv_red_expr_spec_construct_number_1
      | spec_call_global_is_nan_1 _ => inversion H using inv_red_expr_spec_call_global_is_nan_1
      | spec_call_global_is_finite_1 _ => inversion H using inv_red_expr_spec_call_global_is_finite_1
      | spec_call_object_call_1 _ _ => inversion H using inv_red_expr_spec_call_object_call_1
      | spec_call_object_new_1 _ => inversion H using inv_red_expr_spec_call_object_new_1
      | spec_call_object_get_proto_of_1 _ => inversion H using inv_red_expr_spec_call_object_get_proto_of_1
      | spec_call_object_is_extensible_1 _ => inversion H using inv_red_expr_spec_call_object_is_extensible_1
      | spec_call_object_define_props_1 _ _ => inversion H using inv_red_expr_spec_call_object_define_props_1
      | spec_call_object_define_props_2 _ _ => inversion H using inv_red_expr_spec_call_object_define_props_2
      | spec_call_object_define_props_3 _ _ _ _ => inversion H using inv_red_expr_spec_call_object_define_props_3
      | spec_call_object_define_props_4 _ _ _ _ _ _ => inversion H using inv_red_expr_spec_call_object_define_props_4
      | spec_call_object_define_props_5 _ _ _ _ _ _ => inversion H using inv_red_expr_spec_call_object_define_props_5
      | spec_call_object_define_props_6 _ _ => inversion H using inv_red_expr_spec_call_object_define_props_6
      | spec_call_object_define_props_7 _ _ _ => inversion H using inv_red_expr_spec_call_object_define_props_7
      | spec_call_object_create_1 _ _ => inversion H using inv_red_expr_spec_call_object_create_1
      | spec_call_object_create_2 _ _ _ => inversion H using inv_red_expr_spec_call_object_create_2
      | spec_call_object_create_3 _ _ => inversion H using inv_red_expr_spec_call_object_create_3
      | spec_call_object_seal_1 _ => inversion H using inv_red_expr_spec_call_object_seal_1
      | spec_call_object_seal_2 _ _ => inversion H using inv_red_expr_spec_call_object_seal_2
      | spec_call_object_seal_3 _ _ _ _ => inversion H using inv_red_expr_spec_call_object_seal_3
      | spec_call_object_seal_4 _ _ _ => inversion H using inv_red_expr_spec_call_object_seal_4
      | spec_call_object_is_sealed_1 _ => inversion H using inv_red_expr_spec_call_object_is_sealed_1
      | spec_call_object_is_sealed_2 _ _ => inversion H using inv_red_expr_spec_call_object_is_sealed_2
      | spec_call_object_is_sealed_3 _ _ _ => inversion H using inv_red_expr_spec_call_object_is_sealed_3
      | spec_call_object_freeze_1 _ => inversion H using inv_red_expr_spec_call_object_freeze_1
      | spec_call_object_freeze_2 _ _ => inversion H using inv_red_expr_spec_call_object_freeze_2
      | spec_call_object_freeze_3 _ _ _ _ => inversion H using inv_red_expr_spec_call_object_freeze_3
      | spec_call_object_freeze_4 _ _ _ _ => inversion H using inv_red_expr_spec_call_object_freeze_4
      | spec_call_object_freeze_5 _ _ _ => inversion H using inv_red_expr_spec_call_object_freeze_5
      | spec_call_object_is_frozen_1 _ => inversion H using inv_red_expr_spec_call_object_is_frozen_1
      | spec_call_object_is_frozen_2 _ _ => inversion H using inv_red_expr_spec_call_object_is_frozen_2
      | spec_call_object_is_frozen_3 _ _ _ => inversion H using inv_red_expr_spec_call_object_is_frozen_3
      | spec_call_object_is_frozen_4 _ _ _ => inversion H using inv_red_expr_spec_call_object_is_frozen_4
      | spec_call_object_is_frozen_5 _ _ _ => inversion H using inv_red_expr_spec_call_object_is_frozen_5
      | spec_call_object_prevent_extensions_1 _ => inversion H using inv_red_expr_spec_call_object_prevent_extensions_1
      | spec_call_object_define_prop_1 _ _ _ => inversion H using inv_red_expr_spec_call_object_define_prop_1
      | spec_call_object_define_prop_2 _ _ _ => inversion H using inv_red_expr_spec_call_object_define_prop_2
      | spec_call_object_define_prop_3 _ _ _ => inversion H using inv_red_expr_spec_call_object_define_prop_3
      | spec_call_object_define_prop_4 _ _ => inversion H using inv_red_expr_spec_call_object_define_prop_4
      | spec_call_object_get_own_prop_descriptor_1 _ _ => inversion H using inv_red_expr_spec_call_object_get_own_prop_descriptor_1
      | spec_call_object_get_own_prop_descriptor_2 _ _ => inversion H using inv_red_expr_spec_call_object_get_own_prop_descriptor_2
      | spec_call_object_proto_to_string_1 _ => inversion H using inv_red_expr_spec_call_object_proto_to_string_1
      | spec_call_object_proto_to_string_2 _ => inversion H using inv_red_expr_spec_call_object_proto_to_string_2
      | spec_call_object_proto_has_own_prop_1 _ _ => inversion H using inv_red_expr_spec_call_object_proto_has_own_prop_1
      | spec_call_object_proto_has_own_prop_2 _ _ => inversion H using inv_red_expr_spec_call_object_proto_has_own_prop_2
      | spec_call_object_proto_has_own_prop_3 _ => inversion H using inv_red_expr_spec_call_object_proto_has_own_prop_3
      | spec_call_object_proto_is_prototype_of_2_1 _ _ => inversion H using inv_red_expr_spec_call_object_proto_is_prototype_of_2_1
      | spec_call_object_proto_is_prototype_of_2_2 _ _ => inversion H using inv_red_expr_spec_call_object_proto_is_prototype_of_2_2
      | spec_call_object_proto_is_prototype_of_2_3 _ _ => inversion H using inv_red_expr_spec_call_object_proto_is_prototype_of_2_3
      | spec_call_object_proto_is_prototype_of_2_4 _ _ => inversion H using inv_red_expr_spec_call_object_proto_is_prototype_of_2_4
      | spec_call_object_proto_prop_is_enumerable_1 _ _ => inversion H using inv_red_expr_spec_call_object_proto_prop_is_enumerable_1
      | spec_call_object_proto_prop_is_enumerable_2 _ _ => inversion H using inv_red_expr_spec_call_object_proto_prop_is_enumerable_2
      | spec_call_object_proto_prop_is_enumerable_3 _ _ => inversion H using inv_red_expr_spec_call_object_proto_prop_is_enumerable_3
      | spec_call_object_proto_prop_is_enumerable_4 _ => inversion H using inv_red_expr_spec_call_object_proto_prop_is_enumerable_4
      | spec_call_array_new_1 _ => inversion H using inv_red_expr_spec_call_array_new_1
      | spec_call_array_new_2 _ _ => inversion H using inv_red_expr_spec_call_array_new_2
      | spec_call_array_new_3 _ _ _ => inversion H using inv_red_expr_spec_call_array_new_3
      | spec_call_array_new_single_1 _ => inversion H using inv_red_expr_spec_call_array_new_single_1
      | spec_call_array_new_single_2 _ _ => inversion H using inv_red_expr_spec_call_array_new_single_2
      | spec_call_array_new_single_3 _ _ _ => inversion H using inv_red_expr_spec_call_array_new_single_3
      | spec_call_array_new_single_4 _ _ => inversion H using inv_red_expr_spec_call_array_new_single_4
      | spec_call_array_is_array_1 _ => inversion H using inv_red_expr_spec_call_array_is_array_1
      | spec_call_array_is_array_2_3 _ => inversion H using inv_red_expr_spec_call_array_is_array_2_3
      | spec_call_array_proto_join   _ _ => inversion H using inv_red_expr_spec_call_array_proto_join
      | spec_call_array_proto_join_1 _ _ _ => inversion H using inv_red_expr_spec_call_array_proto_join_1
      | spec_call_array_proto_join_2 _ _ _ => inversion H using inv_red_expr_spec_call_array_proto_join_2
      | spec_call_array_proto_join_3 _ _ _ => inversion H using inv_red_expr_spec_call_array_proto_join_3
      | spec_call_array_proto_join_4 _ _ _ => inversion H using inv_red_expr_spec_call_array_proto_join_4
      | spec_call_array_proto_join_5 _ _ _ _ => inversion H using inv_red_expr_spec_call_array_proto_join_5
      | spec_call_array_proto_join_elements _ _ _ _ _ => inversion H using inv_red_expr_spec_call_array_proto_join_elements
      | spec_call_array_proto_join_elements_1 _ _ _ _ _ => inversion H using inv_red_expr_spec_call_array_proto_join_elements_1
      | spec_call_array_proto_join_elements_2 _ _ _ _ _ _ => inversion H using inv_red_expr_spec_call_array_proto_join_elements_2
      | spec_call_array_proto_to_string _ => inversion H using inv_red_expr_spec_call_array_proto_to_string
      | spec_call_array_proto_to_string_1 _ _ => inversion H using inv_red_expr_spec_call_array_proto_to_string_1
      | spec_call_array_proto_pop_1 _ => inversion H using inv_red_expr_spec_call_array_proto_pop_1
      | spec_call_array_proto_pop_2 _ _ => inversion H using inv_red_expr_spec_call_array_proto_pop_2
      | spec_call_array_proto_pop_3 _ _  => inversion H using inv_red_expr_spec_call_array_proto_pop_3
      | spec_call_array_proto_pop_3_empty_1 _ => inversion H using inv_red_expr_spec_call_array_proto_pop_3_empty_1
      | spec_call_array_proto_pop_3_empty_2 _ => inversion H using inv_red_expr_spec_call_array_proto_pop_3_empty_2
      | spec_call_array_proto_pop_3_nonempty_1 _ _ => inversion H using inv_red_expr_spec_call_array_proto_pop_3_nonempty_1
      | spec_call_array_proto_pop_3_nonempty_2 _ _ => inversion H using inv_red_expr_spec_call_array_proto_pop_3_nonempty_2
      | spec_call_array_proto_pop_3_nonempty_3 _ _ _ => inversion H using inv_red_expr_spec_call_array_proto_pop_3_nonempty_3
      | spec_call_array_proto_pop_3_nonempty_4 _ _ _ _ => inversion H using inv_red_expr_spec_call_array_proto_pop_3_nonempty_4
      | spec_call_array_proto_pop_3_nonempty_5 _ _ => inversion H using inv_red_expr_spec_call_array_proto_pop_3_nonempty_5
      | spec_call_array_proto_push_1 _ _ => inversion H using inv_red_expr_spec_call_array_proto_push_1
      | spec_call_array_proto_push_2 _ _ _ => inversion H using inv_red_expr_spec_call_array_proto_push_2
      | spec_call_array_proto_push_3 _ _ _ => inversion H using inv_red_expr_spec_call_array_proto_push_3
      | spec_call_array_proto_push_4 _ _ _ => inversion H using inv_red_expr_spec_call_array_proto_push_4
      | spec_call_array_proto_push_4_nonempty_1 _ _ _ _ => inversion H using inv_red_expr_spec_call_array_proto_push_4_nonempty_1
      | spec_call_array_proto_push_4_nonempty_2 _ _ _ _ _ => inversion H using inv_red_expr_spec_call_array_proto_push_4_nonempty_2
      | spec_call_array_proto_push_4_nonempty_3 _ _ _ _ _ => inversion H using inv_red_expr_spec_call_array_proto_push_4_nonempty_3
      | spec_call_array_proto_push_5 _ _ => inversion H using inv_red_expr_spec_call_array_proto_push_5
      | spec_call_array_proto_push_6 _ _ => inversion H using inv_red_expr_spec_call_array_proto_push_6
      | spec_call_string_non_empty _ => inversion H using inv_red_expr_spec_call_string_non_empty
      | spec_construct_string_1 _ => inversion H using inv_red_expr_spec_construct_string_1
      | spec_construct_string_2 _ => inversion H using inv_red_expr_spec_construct_string_2
      | spec_call_bool_proto_to_string_1 _ => inversion H using inv_red_expr_spec_call_bool_proto_to_string_1
      | spec_call_bool_proto_value_of_1 _ => inversion H using inv_red_expr_spec_call_bool_proto_value_of_1
      | spec_call_bool_proto_value_of_2 _ => inversion H using inv_red_expr_spec_call_bool_proto_value_of_2
      | spec_call_number_proto_to_string_1 _ _ => inversion H using inv_red_expr_spec_call_number_proto_to_string_1
      | spec_call_number_proto_to_string_2 _ _ => inversion H using inv_red_expr_spec_call_number_proto_to_string_2
      | spec_call_number_proto_value_of_1 _ => inversion H using inv_red_expr_spec_call_number_proto_value_of_1
      | spec_call_error_proto_to_string_1 _ => inversion H using inv_red_expr_spec_call_error_proto_to_string_1
      | spec_call_error_proto_to_string_2 _ _ => inversion H using inv_red_expr_spec_call_error_proto_to_string_2
      | spec_call_error_proto_to_string_3 _ _ => inversion H using inv_red_expr_spec_call_error_proto_to_string_3
      | spec_call_error_proto_to_string_4 _ _ _ => inversion H using inv_red_expr_spec_call_error_proto_to_string_4
      | spec_call_error_proto_to_string_5 _ _ _ => inversion H using inv_red_expr_spec_call_error_proto_to_string_5
      | spec_call_error_proto_to_string_6 _ _ _ => inversion H using inv_red_expr_spec_call_error_proto_to_string_6
      | spec_returns _ => inversion H using inv_red_expr_spec_returns
    end
end; tryfalse; clear H; intro H.

Tactic Notation "inverts" "keep" "red_expr" hyp(H) := 
  inverts_tactic_general ltac:(fun H => invert keep red_expr H) H. 

Tactic Notation "inverts" "red_expr" hyp(H) := 
  inverts keep red_expr H; clear H. *)

(**************************************************************)
(** ** Discharging exception difficulties                     *)

Ltac false_exception := 
try match goal with 
 | H : out_of_ext_prog _ = _ |- _ => 
   try solve [simpls; inverts* H]; 
   try solve [simpls; inverts H; try match goal with
                                  | H : abort _ |- _ => inverts H; false*
                                 end]
 | H : out_of_ext_stat _ = _ |- _ => 
   try solve [simpls; inverts* H];
   try solve [simpls; inverts H; try match goal with
                                  | H : abort _ |- _ => inverts H; false*
                                 end]

 | H : out_of_ext_spec _ = _ |- _ => 
   try solve [simpls; inverts* H];
   try solve [simpls; inverts H; try match goal with
                                  | H : abort _ |- _ => inverts H; false*
                                 end]

 | H : out_of_ext_expr _ = _ |- _ => 
   try solve [simpls; inverts* H];
   try solve [simpls; inverts H; try match goal with
                                  | H : abort _ |- _ => inverts H; false*
                                 end]

 | H : abort (out_ter _ _) |- _ => try solve [inverts H; false*]
end.

(**************************************************************)
(** ** Additional automation tactics                          *)

(* Discharging goals with types of binary operators *)
Ltac clear_binop :=
repeat match goal with
 | H : regular_binary_op _     |- _ => inverts H
 | H : lazy_op           _ _   |- _ => inverts H
 | H : puremath_op       _ _   |- _ => inverts H
 | H : shift_op          _ _ _ |- _ => inverts H
 | H : inequality_op     _ _ _ |- _ => inverts H
 | H : bitwise_op        _ _   |- _ => inverts H
end.

Ltac clear_nonsense :=
try match goal with
 | r : ref |- _ => match goal with
                    | H : (resvalue_ref r) = _ |- _ => try solve [inverts* H]
                   end
 | H : context[type_of _ = _] |- _ => try solve [inverts H; tryfalse]
end.

Ltac clean_up := false_exception; clear_binop; clear_nonsense.

(**************************************************************)
(** ** Auxiliary inversions on the semantics                  *)

Lemma red_stat_expr_literal : forall S C (l : literal) o,
  red_stat S C (expr_literal l) o -> o = out_ter S (convert_literal_to_prim l).
Proof with clean_up; auto.
  introv Hr. 
  inverts red_stat Hr...
  inverts red_spec H1... 
  inverts* H6...
  inverts red_spec H7...
  inverts red_spec H5... 
  inverts red_stat H4... 
Admitted.

Lemma red_expr_expr_literal : forall S C (l : literal) o,
  red_expr S C (expr_literal l) o -> o = out_ter S (convert_literal_to_prim l).
Proof with clean_up.
  introv Hr. inverts~ Hr...
Admitted. (* Faster *)

Lemma red_spec_spec_to_primitive_auto_prim : forall S C (p : prim) o,
  red_expr S C (spec_to_primitive_auto p) o -> o = out_ter S p.
Proof with clean_up.
  introv Hr; inverts~ Hr...
Admitted. (* Faster *)

Lemma red_expr_spec_to_number_number : forall S C n o,
  red_expr S C (spec_to_number n) o -> o = out_ter S n.
Proof with clean_up.
  introv Hr. inverts~ Hr...
Admitted. (* Faster *)

(**************************************************************)
(** ** Final automation tactics                               *)

(* Auxiliary inversions *)
Ltac invert_jscert :=
match goal with
 | H : red_stat _ _ (stat_basic (stat_expr (expr_literal _))) ?o |- _ => 
   lets Hsubst : red_stat_expr_literal (rm H); subst o
 | H : red_expr _ _ (expr_basic (expr_literal _)) ?o |- _ => 
   lets Hsubst : red_expr_expr_literal (rm H); subst o
 | H : red_expr _ _ (spec_to_primitive_auto (value_prim _)) ?o |- _ => 
   lets Hsubst : red_spec_spec_to_primitive_auto_prim (rm H); subst o
 | H : red_expr _ _ (spec_to_number (value_prim (prim_number _))) ?o |- _ => 
   lets Hsubst : red_expr_spec_to_number_number (rm H); subst o
end.

(* Main inversion tactic *)
Ltac invert_jscert_on Hyp :=
match type of Hyp with
 | red_spec _ _ _ _ => inverts red_spec Hyp
 | red_expr _ _ _ _ => inverts* Hyp
 | red_stat _ _ _ _ => inverts red_stat Hyp
 | red_prog _ _ _ _ => inverts red_prog Hyp
end; jauto; clean_up; repeat invert_jscert.

(* Wrap-up *)
Ltac inversion_jscert :=
try match goal with 
 | H : red_spec _ _ _ _ |- _ => (invert_jscert_on H; [idtac]; inversion_jscert) || (invert_jscert_on H; fail)
 | H : red_expr _ _ _ _ |- _ => (invert_jscert_on H; [idtac]; inversion_jscert) || (invert_jscert_on H; fail)
 | H : red_stat _ _ _ _ |- _ => (invert_jscert_on H; [idtac]; inversion_jscert) || (invert_jscert_on H; fail)
 | H : red_prog _ _ _ _ |- _ => (invert_jscert_on H; [idtac]; inversion_jscert) || (invert_jscert_on H; fail)
end.