Set Implicit Arguments.
Require Import Shared.
Require Import JsSyntax JsSyntaxAux JsCommon JsCommonAux JsPreliminary.
Require Import JsPrettyInterm JsPrettyRules.

(**************************************************************)
(** ** Inversion principles for expressions                   *)

Derive Inversion inv_red_expr_this with (forall S C oo, red_expr S C expr_this oo) Sort Prop. 
Derive Inversion inv_red_expr_identifier with (forall S C a1 oo, red_expr S C (expr_identifier a1) oo) Sort Prop. 
Derive Inversion inv_red_expr_literal with (forall S C a1 oo, red_expr S C (expr_literal a1) oo) Sort Prop. 
Derive Inversion inv_red_expr_object with (forall S C a1 oo, red_expr S C (expr_object a1) oo) Sort Prop. 
Derive Inversion inv_red_expr_array with (forall S C a1 oo, red_expr S C (expr_array a1) oo) Sort Prop. 
Derive Inversion inv_red_expr_function with (forall S C a1 a2 a3 oo, red_expr S C (expr_function a1 a2 a3) oo) Sort Prop. 
Derive Inversion inv_red_expr_access with (forall S C a1 a2 oo, red_expr S C (expr_access a1 a2) oo) Sort Prop. 
Derive Inversion inv_red_expr_member with (forall S C a1 a2 oo, red_expr S C (expr_member a1 a2) oo) Sort Prop. 
Derive Inversion inv_red_expr_new with (forall S C a1 a2 oo, red_expr S C (expr_new a1 a2) oo) Sort Prop. 
Derive Inversion inv_red_expr_call with (forall S C a1 a2 oo, red_expr S C (expr_call a1 a2) oo) Sort Prop. 
Derive Inversion inv_red_expr_unary_op with (forall S C a1 a2 oo, red_expr S C (expr_unary_op a1 a2) oo) Sort Prop. 
Derive Inversion inv_red_expr_binary_op with (forall S C a1 a2 a3 oo, red_expr S C (expr_binary_op a1 a2 a3) oo) Sort Prop. 
Derive Inversion inv_red_expr_conditional with (forall S C a1 a2 a3 oo, red_expr S C (expr_conditional a1 a2 a3) oo) Sort Prop. 
Derive Inversion inv_red_expr_assign with (forall S C a1 a2 a3 oo, red_expr S C (expr_assign a1 a2 a3) oo) Sort Prop. 
Derive Inversion inv_red_expr_expr_identifier_1 with (forall S C a1 oo, red_expr S C (expr_identifier_1 a1) oo) Sort Prop. 
Derive Inversion inv_red_expr_expr_object_0 with (forall S C a1 a2 oo, red_expr S C (expr_object_0 a1 a2) oo) Sort Prop. 
Derive Inversion inv_red_expr_expr_object_1 with (forall S C a1 a2 oo, red_expr S C (expr_object_1 a1 a2) oo) Sort Prop. 
Derive Inversion inv_red_expr_expr_object_2 with (forall S C a1 a2 a3 a4 oo, red_expr S C (expr_object_2 a1 a2 a3 a4) oo) Sort Prop. 
Derive Inversion inv_red_expr_expr_object_3_val with (forall S C a1 a2 a3 a4 oo, red_expr S C (expr_object_3_val a1 a2 a3 a4) oo) Sort Prop. 
Derive Inversion inv_red_expr_expr_object_3_get with (forall S C a1 a2 a3 a4 oo, red_expr S C (expr_object_3_get a1 a2 a3 a4) oo) Sort Prop. 
Derive Inversion inv_red_expr_expr_object_3_set with (forall S C a1 a2 a3 a4 oo, red_expr S C (expr_object_3_set a1 a2 a3 a4) oo) Sort Prop. 
Derive Inversion inv_red_expr_expr_object_4 with (forall S C a1 a2 a3 a4 oo, red_expr S C (expr_object_4 a1 a2 a3 a4) oo) Sort Prop. 
Derive Inversion inv_red_expr_expr_object_5 with (forall S C a1 a2 a3 oo, red_expr S C (expr_object_5 a1 a2 a3) oo) Sort Prop. 
Derive Inversion inv_red_expr_expr_array_0 with (forall S C a1 a2 oo, red_expr S C (expr_array_0 a1 a2) oo) Sort Prop. 
Derive Inversion inv_red_expr_expr_array_1 with (forall S C a1 a2 oo, red_expr S C (expr_array_1 a1 a2) oo) Sort Prop. 
Derive Inversion inv_red_expr_expr_array_2 with (forall S C a1 a2 a3 oo, red_expr S C (expr_array_2 a1 a2 a3) oo) Sort Prop. 
Derive Inversion inv_red_expr_expr_array_3 with (forall S C a1 a2 a3 oo, red_expr S C (expr_array_3 a1 a2 a3) oo) Sort Prop. 
Derive Inversion inv_red_expr_expr_array_3_1 with (forall S C a1 a2 a3 a4 oo, red_expr S C (expr_array_3_1 a1 a2 a3 a4) oo) Sort Prop. 
Derive Inversion inv_red_expr_expr_array_3_2 with (forall S C a1 a2 a3 a4 a5 oo, red_expr S C (expr_array_3_2 a1 a2 a3 a4 a5) oo) Sort Prop. 
Derive Inversion inv_red_expr_expr_array_3_3 with (forall S C a1 a2 a3 a4 a5 oo, red_expr S C (expr_array_3_3 a1 a2 a3 a4 a5) oo) Sort Prop. 
Derive Inversion inv_red_expr_expr_array_3_4 with (forall S C a1 a2 a3 a4 oo, red_expr S C (expr_array_3_4 a1 a2 a3 a4) oo) Sort Prop. 
Derive Inversion inv_red_expr_expr_array_3_5 with (forall S C a1 a2 a3 oo, red_expr S C (expr_array_3_5 a1 a2 a3) oo) Sort Prop. 
Derive Inversion inv_red_expr_expr_array_add_length with (forall S C a1 a2 a3 oo, red_expr S C (expr_array_add_length a1 a2 a3) oo) Sort Prop. 
Derive Inversion inv_red_expr_expr_array_add_length_0 with (forall S C a1 a2 oo, red_expr S C (expr_array_add_length_0 a1 a2) oo) Sort Prop. 
Derive Inversion inv_red_expr_expr_array_add_length_1 with (forall S C a1 a2 a3 oo, red_expr S C (expr_array_add_length_1 a1 a2 a3) oo) Sort Prop. 
Derive Inversion inv_red_expr_expr_array_add_length_2 with (forall S C a1 a2 a3 oo, red_expr S C (expr_array_add_length_2 a1 a2 a3) oo) Sort Prop. 
Derive Inversion inv_red_expr_expr_array_add_length_3 with (forall S C a1 a2 oo, red_expr S C (expr_array_add_length_3 a1 a2) oo) Sort Prop. 
Derive Inversion inv_red_expr_expr_array_add_length_4 with (forall S C a1 a2 oo, red_expr S C (expr_array_add_length_4 a1 a2) oo) Sort Prop. 
Derive Inversion inv_red_expr_expr_function_1 with (forall S C a1 a2 a3 a4 a5 a6 oo, red_expr S C (expr_function_1 a1 a2 a3 a4 a5 a6) oo) Sort Prop. 
Derive Inversion inv_red_expr_expr_function_2 with (forall S C a1 a2 a3 oo, red_expr S C (expr_function_2 a1 a2 a3) oo) Sort Prop. 
Derive Inversion inv_red_expr_expr_function_3 with (forall S C a1 a2 oo, red_expr S C (expr_function_3 a1 a2) oo) Sort Prop. 
Derive Inversion inv_red_expr_expr_access_1 with (forall S C a1 a2 oo, red_expr S C (expr_access_1 a1 a2) oo) Sort Prop. 
Derive Inversion inv_red_expr_expr_access_2 with (forall S C a1 a2 oo, red_expr S C (expr_access_2 a1 a2) oo) Sort Prop. 
Derive Inversion inv_red_expr_expr_access_3 with (forall S C a1 a2 a3 oo, red_expr S C (expr_access_3 a1 a2 a3) oo) Sort Prop. 
Derive Inversion inv_red_expr_expr_access_4 with (forall S C a1 a2 oo, red_expr S C (expr_access_4 a1 a2) oo) Sort Prop. 
Derive Inversion inv_red_expr_expr_new_1 with (forall S C a1 a2 oo, red_expr S C (expr_new_1 a1 a2) oo) Sort Prop. 
Derive Inversion inv_red_expr_expr_new_2 with (forall S C a1 a2 oo, red_expr S C (expr_new_2 a1 a2) oo) Sort Prop. 
Derive Inversion inv_red_expr_expr_call_1 with (forall S C a1 a2 a3 oo, red_expr S C (expr_call_1 a1 a2 a3) oo) Sort Prop. 
Derive Inversion inv_red_expr_expr_call_2 with (forall S C a1 a2 a3 a4 oo, red_expr S C (expr_call_2 a1 a2 a3 a4) oo) Sort Prop. 
Derive Inversion inv_red_expr_expr_call_3 with (forall S C a1 a2 a3 a4 oo, red_expr S C (expr_call_3 a1 a2 a3 a4) oo) Sort Prop. 
Derive Inversion inv_red_expr_expr_call_4 with (forall S C a1 a2 a3 a4 oo, red_expr S C (expr_call_4 a1 a2 a3 a4) oo) Sort Prop. 
Derive Inversion inv_red_expr_expr_call_5 with (forall S C a1 a2 a3 a4 oo, red_expr S C (expr_call_5 a1 a2 a3 a4) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_eval with (forall S C a1 a2 a3 oo, red_expr S C (spec_eval a1 a2 a3) oo) Sort Prop. 
Derive Inversion inv_red_expr_expr_unary_op_1 with (forall S C a1 a2 oo, red_expr S C (expr_unary_op_1 a1 a2) oo) Sort Prop. 
Derive Inversion inv_red_expr_expr_unary_op_2 with (forall S C a1 a2 oo, red_expr S C (expr_unary_op_2 a1 a2) oo) Sort Prop. 
Derive Inversion inv_red_expr_expr_delete_1 with (forall S C a1 oo, red_expr S C (expr_delete_1 a1) oo) Sort Prop. 
Derive Inversion inv_red_expr_expr_delete_2 with (forall S C a1 oo, red_expr S C (expr_delete_2 a1) oo) Sort Prop. 
Derive Inversion inv_red_expr_expr_delete_3 with (forall S C a1 a2 oo, red_expr S C (expr_delete_3 a1 a2) oo) Sort Prop. 
Derive Inversion inv_red_expr_expr_delete_4 with (forall S C a1 a2 oo, red_expr S C (expr_delete_4 a1 a2) oo) Sort Prop. 
Derive Inversion inv_red_expr_expr_typeof_1 with (forall S C a1 oo, red_expr S C (expr_typeof_1 a1) oo) Sort Prop. 
Derive Inversion inv_red_expr_expr_typeof_2 with (forall S C a1 oo, red_expr S C (expr_typeof_2 a1) oo) Sort Prop. 
Derive Inversion inv_red_expr_expr_prepost_1 with (forall S C a1 a2 oo, red_expr S C (expr_prepost_1 a1 a2) oo) Sort Prop. 
Derive Inversion inv_red_expr_expr_prepost_2 with (forall S C a1 a2 a3 oo, red_expr S C (expr_prepost_2 a1 a2 a3) oo) Sort Prop. 
Derive Inversion inv_red_expr_expr_prepost_3 with (forall S C a1 a2 a3 oo, red_expr S C (expr_prepost_3 a1 a2 a3) oo) Sort Prop. 
Derive Inversion inv_red_expr_expr_prepost_4 with (forall S C a1 a2 oo, red_expr S C (expr_prepost_4 a1 a2) oo) Sort Prop. 
Derive Inversion inv_red_expr_expr_unary_op_neg_1 with (forall S C a1 oo, red_expr S C (expr_unary_op_neg_1 a1) oo) Sort Prop. 
Derive Inversion inv_red_expr_expr_unary_op_bitwise_not_1 with (forall S C a1 oo, red_expr S C (expr_unary_op_bitwise_not_1 a1) oo) Sort Prop. 
Derive Inversion inv_red_expr_expr_unary_op_not_1 with (forall S C a1 oo, red_expr S C (expr_unary_op_not_1 a1) oo) Sort Prop. 
Derive Inversion inv_red_expr_expr_conditional_1 with (forall S C a1 a2 a3 oo, red_expr S C (expr_conditional_1 a1 a2 a3) oo) Sort Prop. 
Derive Inversion inv_red_expr_expr_conditional_1' with (forall S C a1 a2 a3 oo, red_expr S C (expr_conditional_1' a1 a2 a3) oo) Sort Prop. 
Derive Inversion inv_red_expr_expr_conditional_2 with (forall S C a1 oo, red_expr S C (expr_conditional_2 a1) oo) Sort Prop. 
Derive Inversion inv_red_expr_expr_binary_op_1 with (forall S C a1 a2 a3 oo, red_expr S C (expr_binary_op_1 a1 a2 a3) oo) Sort Prop. 
Derive Inversion inv_red_expr_expr_binary_op_2 with (forall S C a1 a2 a3 oo, red_expr S C (expr_binary_op_2 a1 a2 a3) oo) Sort Prop. 
Derive Inversion inv_red_expr_expr_binary_op_3 with (forall S C a1 a2 a3 oo, red_expr S C (expr_binary_op_3 a1 a2 a3) oo) Sort Prop. 
Derive Inversion inv_red_expr_expr_binary_op_add_1 with (forall S C a1 oo, red_expr S C (expr_binary_op_add_1 a1) oo) Sort Prop. 
Derive Inversion inv_red_expr_expr_binary_op_add_string_1 with (forall S C a1 oo, red_expr S C (expr_binary_op_add_string_1 a1) oo) Sort Prop. 
Derive Inversion inv_red_expr_expr_puremath_op_1 with (forall S C a1 a2 oo, red_expr S C (expr_puremath_op_1 a1 a2) oo) Sort Prop. 
Derive Inversion inv_red_expr_expr_shift_op_1 with (forall S C a1 a2 a3 oo, red_expr S C (expr_shift_op_1 a1 a2 a3) oo) Sort Prop. 
Derive Inversion inv_red_expr_expr_shift_op_2 with (forall S C a1 a2 a3 oo, red_expr S C (expr_shift_op_2 a1 a2 a3) oo) Sort Prop. 
Derive Inversion inv_red_expr_expr_inequality_op_1 with (forall S C a1 a2 a3 a4 oo, red_expr S C (expr_inequality_op_1 a1 a2 a3 a4) oo) Sort Prop. 
Derive Inversion inv_red_expr_expr_inequality_op_2 with (forall S C a1 a2 a3 oo, red_expr S C (expr_inequality_op_2 a1 a2 a3) oo) Sort Prop. 
Derive Inversion inv_red_expr_expr_binary_op_in_1 with (forall S C a1 a2 oo, red_expr S C (expr_binary_op_in_1 a1 a2) oo) Sort Prop. 
Derive Inversion inv_red_expr_expr_binary_op_disequal_1 with (forall S C a1 oo, red_expr S C (expr_binary_op_disequal_1 a1) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_equal with (forall S C a1 a2 oo, red_expr S C (spec_equal a1 a2) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_equal_1 with (forall S C a1 a2 a3 a4 oo, red_expr S C (spec_equal_1 a1 a2 a3 a4) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_equal_2 with (forall S C a1 oo, red_expr S C (spec_equal_2 a1) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_equal_3 with (forall S C a1 a2 a3 oo, red_expr S C (spec_equal_3 a1 a2 a3) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_equal_4 with (forall S C a1 a2 oo, red_expr S C (spec_equal_4 a1 a2) oo) Sort Prop. 
Derive Inversion inv_red_expr_expr_bitwise_op_1 with (forall S C a1 a2 a3 oo, red_expr S C (expr_bitwise_op_1 a1 a2 a3) oo) Sort Prop. 
Derive Inversion inv_red_expr_expr_bitwise_op_2 with (forall S C a1 a2 a3 oo, red_expr S C (expr_bitwise_op_2 a1 a2 a3) oo) Sort Prop. 
Derive Inversion inv_red_expr_expr_lazy_op_1 with (forall S C a1 a2 a3 oo, red_expr S C (expr_lazy_op_1 a1 a2 a3) oo) Sort Prop. 
Derive Inversion inv_red_expr_expr_lazy_op_2 with (forall S C a1 a2 a3 a4 oo, red_expr S C (expr_lazy_op_2 a1 a2 a3 a4) oo) Sort Prop. 
Derive Inversion inv_red_expr_expr_lazy_op_2_1 with (forall S C a1 oo, red_expr S C (expr_lazy_op_2_1 a1) oo) Sort Prop. 
Derive Inversion inv_red_expr_expr_assign_1 with (forall S C a1 a2 a3 oo, red_expr S C (expr_assign_1 a1 a2 a3) oo) Sort Prop. 
Derive Inversion inv_red_expr_expr_assign_2 with (forall S C a1 a2 a3 a4 oo, red_expr S C (expr_assign_2 a1 a2 a3 a4) oo) Sort Prop. 
Derive Inversion inv_red_expr_expr_assign_3 with (forall S C a1 a2 a3 a4 oo, red_expr S C (expr_assign_3 a1 a2 a3 a4) oo) Sort Prop. 
Derive Inversion inv_red_expr_expr_assign_3' with (forall S C a1 a2 oo, red_expr S C (expr_assign_3' a1 a2) oo) Sort Prop. 
Derive Inversion inv_red_expr_expr_assign_4 with (forall S C a1 a2 oo, red_expr S C (expr_assign_4 a1 a2) oo) Sort Prop. 
Derive Inversion inv_red_expr_expr_assign_5 with (forall S C a1 a2 oo, red_expr S C (expr_assign_5 a1 a2) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_to_primitive with (forall S C a1 a2 oo, red_expr S C (spec_to_primitive a1 a2) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_to_boolean with (forall S C a1 oo, red_expr S C (spec_to_boolean a1) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_to_number with (forall S C a1 oo, red_expr S C (spec_to_number a1) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_to_number_1 with (forall S C a1 oo, red_expr S C (spec_to_number_1 a1) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_to_integer with (forall S C a1 oo, red_expr S C (spec_to_integer a1) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_to_integer_1 with (forall S C a1 oo, red_expr S C (spec_to_integer_1 a1) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_to_string with (forall S C a1 oo, red_expr S C (spec_to_string a1) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_to_string_1 with (forall S C a1 oo, red_expr S C (spec_to_string_1 a1) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_to_object with (forall S C a1 oo, red_expr S C (spec_to_object a1) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_check_object_coercible with (forall S C a1 oo, red_expr S C (spec_check_object_coercible a1) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_eq with (forall S C a1 a2 oo, red_expr S C (spec_eq a1 a2) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_eq0 with (forall S C a1 a2 oo, red_expr S C (spec_eq0 a1 a2) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_eq1 with (forall S C a1 a2 oo, red_expr S C (spec_eq1 a1 a2) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_eq2 with (forall S C a1 a2 a3 oo, red_expr S C (spec_eq2 a1 a2 a3) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_object_get with (forall S C a1 a2 oo, red_expr S C (spec_object_get a1 a2) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_object_get_1 with (forall S C a1 a2 a3 a4 oo, red_expr S C (spec_object_get_1 a1 a2 a3 a4) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_object_get_2 with (forall S C a1 a2 oo, red_expr S C (spec_object_get_2 a1 a2) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_object_get_3 with (forall S C a1 a2 oo, red_expr S C (spec_object_get_3 a1 a2) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_object_can_put with (forall S C a1 a2 oo, red_expr S C (spec_object_can_put a1 a2) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_object_can_put_1 with (forall S C a1 a2 a3 oo, red_expr S C (spec_object_can_put_1 a1 a2 a3) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_object_can_put_2 with (forall S C a1 a2 a3 oo, red_expr S C (spec_object_can_put_2 a1 a2 a3) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_object_can_put_4 with (forall S C a1 a2 a3 oo, red_expr S C (spec_object_can_put_4 a1 a2 a3) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_object_can_put_5 with (forall S C a1 a2 oo, red_expr S C (spec_object_can_put_5 a1 a2) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_object_can_put_6 with (forall S C a1 a2 oo, red_expr S C (spec_object_can_put_6 a1 a2) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_object_put with (forall S C a1 a2 a3 a4 oo, red_expr S C (spec_object_put a1 a2 a3 a4) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_object_put_1 with (forall S C a1 a2 a3 a4 a5 a6 oo, red_expr S C (spec_object_put_1 a1 a2 a3 a4 a5 a6) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_object_put_2 with (forall S C a1 a2 a3 a4 a5 a6 oo, red_expr S C (spec_object_put_2 a1 a2 a3 a4 a5 a6) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_object_put_3 with (forall S C a1 a2 a3 a4 a5 a6 oo, red_expr S C (spec_object_put_3 a1 a2 a3 a4 a5 a6) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_object_put_4 with (forall S C a1 a2 a3 a4 a5 a6 oo, red_expr S C (spec_object_put_4 a1 a2 a3 a4 a5 a6) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_object_put_5 with (forall S C a1 oo, red_expr S C (spec_object_put_5 a1) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_object_has_prop with (forall S C a1 a2 oo, red_expr S C (spec_object_has_prop a1 a2) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_object_has_prop_1 with (forall S C a1 a2 a3 oo, red_expr S C (spec_object_has_prop_1 a1 a2 a3) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_object_has_prop_2 with (forall S C a1 oo, red_expr S C (spec_object_has_prop_2 a1) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_object_delete with (forall S C a1 a2 a3 oo, red_expr S C (spec_object_delete a1 a2 a3) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_object_delete_1 with (forall S C a1 a2 a3 a4 oo, red_expr S C (spec_object_delete_1 a1 a2 a3 a4) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_object_delete_2 with (forall S C a1 a2 a3 a4 oo, red_expr S C (spec_object_delete_2 a1 a2 a3 a4) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_object_delete_3 with (forall S C a1 a2 a3 a4 oo, red_expr S C (spec_object_delete_3 a1 a2 a3 a4) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_object_default_value with (forall S C a1 a2 oo, red_expr S C (spec_object_default_value a1 a2) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_object_default_value_1 with (forall S C a1 a2 a3 oo, red_expr S C (spec_object_default_value_1 a1 a2 a3) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_object_default_value_2 with (forall S C a1 a2 a3 oo, red_expr S C (spec_object_default_value_2 a1 a2 a3) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_object_default_value_3 with (forall S C a1 a2 oo, red_expr S C (spec_object_default_value_3 a1 a2) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_object_default_value_4 with (forall S C oo, red_expr S C spec_object_default_value_4 oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_object_default_value_sub_1 with (forall S C a1 a2 a3 oo, red_expr S C (spec_object_default_value_sub_1 a1 a2 a3) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_object_default_value_sub_2 with (forall S C a1 a2 a3 oo, red_expr S C (spec_object_default_value_sub_2 a1 a2 a3) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_object_default_value_sub_3 with (forall S C a1 a2 oo, red_expr S C (spec_object_default_value_sub_3 a1 a2) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_object_define_own_prop with (forall S C a1 a2 a3 a4 oo, red_expr S C (spec_object_define_own_prop a1 a2 a3 a4) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_object_define_own_prop_1 with (forall S C a1 a2 a3 a4 a5 oo, red_expr S C (spec_object_define_own_prop_1 a1 a2 a3 a4 a5) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_object_define_own_prop_2 with (forall S C a1 a2 a3 a4 a5 oo, red_expr S C (spec_object_define_own_prop_2 a1 a2 a3 a4 a5) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_object_define_own_prop_3 with (forall S C a1 a2 a3 a4 a5 a6 oo, red_expr S C (spec_object_define_own_prop_3 a1 a2 a3 a4 a5 a6) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_object_define_own_prop_4 with (forall S C a1 a2 a3 a4 a5 oo, red_expr S C (spec_object_define_own_prop_4 a1 a2 a3 a4 a5) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_object_define_own_prop_5 with (forall S C a1 a2 a3 a4 a5 oo, red_expr S C (spec_object_define_own_prop_5 a1 a2 a3 a4 a5) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_object_define_own_prop_6a with (forall S C a1 a2 a3 a4 a5 oo, red_expr S C (spec_object_define_own_prop_6a a1 a2 a3 a4 a5) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_object_define_own_prop_6b with (forall S C a1 a2 a3 a4 a5 oo, red_expr S C (spec_object_define_own_prop_6b a1 a2 a3 a4 a5) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_object_define_own_prop_6c with (forall S C a1 a2 a3 a4 a5 oo, red_expr S C (spec_object_define_own_prop_6c a1 a2 a3 a4 a5) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_object_define_own_prop_reject with (forall S C a1 oo, red_expr S C (spec_object_define_own_prop_reject a1) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_object_define_own_prop_write with (forall S C a1 a2 a3 a4 a5 oo, red_expr S C (spec_object_define_own_prop_write a1 a2 a3 a4 a5) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_object_define_own_prop_array_2 with (forall S C a1 a2 a3 a4 a5 oo, red_expr S C (spec_object_define_own_prop_array_2 a1 a2 a3 a4 a5) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_object_define_own_prop_array_2_1 with (forall S C a1 a2 a3 a4 a5 a6 oo, red_expr S C (spec_object_define_own_prop_array_2_1 a1 a2 a3 a4 a5 a6) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_object_define_own_prop_array_branch_3_4 with (forall S C a1 a2 a3 a4 a5 a6 oo, red_expr S C (spec_object_define_own_prop_array_branch_3_4 a1 a2 a3 a4 a5 a6) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_object_define_own_prop_array_branch_4_5 with (forall S C a1 a2 a3 a4 a5 a6 oo, red_expr S C (spec_object_define_own_prop_array_branch_4_5 a1 a2 a3 a4 a5 a6) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_object_define_own_prop_array_branch_4_5_a with (forall S C a1 a2 a3 a4 a5 a6 a7 oo, red_expr S C (spec_object_define_own_prop_array_branch_4_5_a a1 a2 a3 a4 a5 a6 a7) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_object_define_own_prop_array_branch_4_5_b with (forall S C a1 a2 a3 a4 a5 a6 a7 a8 oo, red_expr S C (spec_object_define_own_prop_array_branch_4_5_b a1 a2 a3 a4 a5 a6 a7 a8) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_object_define_own_prop_array_4a with (forall S C a1 a2 a3 a4 a5 a6 oo, red_expr S C (spec_object_define_own_prop_array_4a a1 a2 a3 a4 a5 a6) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_object_define_own_prop_array_4b with (forall S C a1 a2 a3 a4 a5 a6 a7 oo, red_expr S C (spec_object_define_own_prop_array_4b a1 a2 a3 a4 a5 a6 a7) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_object_define_own_prop_array_4c with (forall S C a1 a2 a3 a4 a5 a6 a7 oo, red_expr S C (spec_object_define_own_prop_array_4c a1 a2 a3 a4 a5 a6 a7) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_object_define_own_prop_array_5 with (forall S C a1 a2 a3 a4 oo, red_expr S C (spec_object_define_own_prop_array_5 a1 a2 a3 a4) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_object_define_own_prop_array_3 with (forall S C a1 a2 a3 a4 a5 oo, red_expr S C (spec_object_define_own_prop_array_3 a1 a2 a3 a4 a5) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_object_define_own_prop_array_3c with (forall S C a1 a2 a3 a4 a5 a6 a7 oo, red_expr S C (spec_object_define_own_prop_array_3c a1 a2 a3 a4 a5 a6 a7) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_object_define_own_prop_array_3d_e with (forall S C a1 a2 a3 a4 a5 a6 a7 oo, red_expr S C (spec_object_define_own_prop_array_3d_e a1 a2 a3 a4 a5 a6 a7) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_object_define_own_prop_array_3f_g with (forall S C a1 a2 a3 a4 a5 a6 oo, red_expr S C (spec_object_define_own_prop_array_3f_g a1 a2 a3 a4 a5 a6) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_object_define_own_prop_array_3h_i with (forall S C a1 a2 a3 a4 a5 a6 oo, red_expr S C (spec_object_define_own_prop_array_3h_i a1 a2 a3 a4 a5 a6) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_object_define_own_prop_array_3j with (forall S C a1 a2 a3 a4 a5 a6 a7 oo, red_expr S C (spec_object_define_own_prop_array_3j a1 a2 a3 a4 a5 a6 a7) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_object_define_own_prop_array_3k_l with (forall S C a1 a2 a3 a4 a5 a6 a7 a8 oo, red_expr S C (spec_object_define_own_prop_array_3k_l a1 a2 a3 a4 a5 a6 a7 a8) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_object_define_own_prop_array_3l with (forall S C a1 a2 a3 a4 a5 a6 oo, red_expr S C (spec_object_define_own_prop_array_3l a1 a2 a3 a4 a5 a6) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_object_define_own_prop_array_3l_ii with (forall S C a1 a2 a3 a4 a5 a6 oo, red_expr S C (spec_object_define_own_prop_array_3l_ii a1 a2 a3 a4 a5 a6) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_object_define_own_prop_array_3l_ii_1 with (forall S C a1 a2 a3 a4 a5 a6 a7 oo, red_expr S C (spec_object_define_own_prop_array_3l_ii_1 a1 a2 a3 a4 a5 a6 a7) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_object_define_own_prop_array_3l_ii_2 with (forall S C a1 a2 a3 a4 a5 a6 a7 oo, red_expr S C (spec_object_define_own_prop_array_3l_ii_2 a1 a2 a3 a4 a5 a6 a7) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_object_define_own_prop_array_3l_iii_1 with (forall S C a1 a2 a3 a4 a5 oo, red_expr S C (spec_object_define_own_prop_array_3l_iii_1 a1 a2 a3 a4 a5) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_object_define_own_prop_array_3l_iii_2 with (forall S C a1 a2 a3 a4 oo, red_expr S C (spec_object_define_own_prop_array_3l_iii_2 a1 a2 a3 a4) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_object_define_own_prop_array_3l_iii_3 with (forall S C a1 a2 a3 oo, red_expr S C (spec_object_define_own_prop_array_3l_iii_3 a1 a2 a3) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_object_define_own_prop_array_3l_iii_4 with (forall S C a1 a2 a3 oo, red_expr S C (spec_object_define_own_prop_array_3l_iii_4 a1 a2 a3) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_object_define_own_prop_array_3m_n with (forall S C a1 a2 oo, red_expr S C (spec_object_define_own_prop_array_3m_n a1 a2) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_prim_value_get with (forall S C a1 a2 oo, red_expr S C (spec_prim_value_get a1 a2) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_prim_value_get_1 with (forall S C a1 a2 a3 oo, red_expr S C (spec_prim_value_get_1 a1 a2 a3) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_prim_value_put with (forall S C a1 a2 a3 a4 oo, red_expr S C (spec_prim_value_put a1 a2 a3 a4) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_prim_value_put_1 with (forall S C a1 a2 a3 a4 a5 oo, red_expr S C (spec_prim_value_put_1 a1 a2 a3 a4 a5) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_put_value with (forall S C a1 a2 oo, red_expr S C (spec_put_value a1 a2) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_env_record_has_binding with (forall S C a1 a2 oo, red_expr S C (spec_env_record_has_binding a1 a2) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_env_record_has_binding_1 with (forall S C a1 a2 a3 oo, red_expr S C (spec_env_record_has_binding_1 a1 a2 a3) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_env_record_get_binding_value with (forall S C a1 a2 a3 oo, red_expr S C (spec_env_record_get_binding_value a1 a2 a3) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_env_record_get_binding_value_1 with (forall S C a1 a2 a3 a4 oo, red_expr S C (spec_env_record_get_binding_value_1 a1 a2 a3 a4) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_env_record_get_binding_value_2 with (forall S C a1 a2 a3 a4 oo, red_expr S C (spec_env_record_get_binding_value_2 a1 a2 a3 a4) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_env_record_create_immutable_binding with (forall S C a1 a2 oo, red_expr S C (spec_env_record_create_immutable_binding a1 a2) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_env_record_initialize_immutable_binding with (forall S C a1 a2 a3 oo, red_expr S C (spec_env_record_initialize_immutable_binding a1 a2 a3) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_env_record_create_mutable_binding with (forall S C a1 a2 a3 oo, red_expr S C (spec_env_record_create_mutable_binding a1 a2 a3) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_env_record_create_mutable_binding_1 with (forall S C a1 a2 a3 a4 oo, red_expr S C (spec_env_record_create_mutable_binding_1 a1 a2 a3 a4) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_env_record_create_mutable_binding_2 with (forall S C a1 a2 a3 a4 a5 oo, red_expr S C (spec_env_record_create_mutable_binding_2 a1 a2 a3 a4 a5) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_env_record_create_mutable_binding_3 with (forall S C a1 oo, red_expr S C (spec_env_record_create_mutable_binding_3 a1) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_env_record_set_mutable_binding with (forall S C a1 a2 a3 a4 oo, red_expr S C (spec_env_record_set_mutable_binding a1 a2 a3 a4) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_env_record_set_mutable_binding_1 with (forall S C a1 a2 a3 a4 a5 oo, red_expr S C (spec_env_record_set_mutable_binding_1 a1 a2 a3 a4 a5) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_env_record_delete_binding with (forall S C a1 a2 oo, red_expr S C (spec_env_record_delete_binding a1 a2) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_env_record_delete_binding_1 with (forall S C a1 a2 a3 oo, red_expr S C (spec_env_record_delete_binding_1 a1 a2 a3) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_env_record_create_set_mutable_binding with (forall S C a1 a2 a3 a4 a5 oo, red_expr S C (spec_env_record_create_set_mutable_binding a1 a2 a3 a4 a5) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_env_record_create_set_mutable_binding_1 with (forall S C a1 a2 a3 a4 a5 oo, red_expr S C (spec_env_record_create_set_mutable_binding_1 a1 a2 a3 a4 a5) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_env_record_implicit_this_value with (forall S C a1 oo, red_expr S C (spec_env_record_implicit_this_value a1) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_env_record_implicit_this_value_1 with (forall S C a1 a2 oo, red_expr S C (spec_env_record_implicit_this_value_1 a1 a2) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_from_descriptor with (forall S C a1 oo, red_expr S C (spec_from_descriptor a1) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_from_descriptor_1 with (forall S C a1 a2 oo, red_expr S C (spec_from_descriptor_1 a1 a2) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_from_descriptor_2 with (forall S C a1 a2 a3 oo, red_expr S C (spec_from_descriptor_2 a1 a2 a3) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_from_descriptor_3 with (forall S C a1 a2 a3 oo, red_expr S C (spec_from_descriptor_3 a1 a2 a3) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_from_descriptor_4 with (forall S C a1 a2 a3 oo, red_expr S C (spec_from_descriptor_4 a1 a2 a3) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_from_descriptor_5 with (forall S C a1 a2 a3 oo, red_expr S C (spec_from_descriptor_5 a1 a2 a3) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_from_descriptor_6 with (forall S C a1 a2 oo, red_expr S C (spec_from_descriptor_6 a1 a2) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_entering_eval_code with (forall S C a1 a2 a3 oo, red_expr S C (spec_entering_eval_code a1 a2 a3) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_entering_eval_code_1 with (forall S C a1 a2 a3 oo, red_expr S C (spec_entering_eval_code_1 a1 a2 a3) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_entering_eval_code_2 with (forall S C a1 a2 oo, red_expr S C (spec_entering_eval_code_2 a1 a2) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_call_global_eval with (forall S C a1 a2 oo, red_expr S C (spec_call_global_eval a1 a2) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_call_global_eval_1 with (forall S C a1 a2 oo, red_expr S C (spec_call_global_eval_1 a1 a2) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_call_global_eval_2 with (forall S C a1 oo, red_expr S C (spec_call_global_eval_2 a1) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_call_global_eval_3 with (forall S C a1 oo, red_expr S C (spec_call_global_eval_3 a1) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_entering_func_code with (forall S C a1 a2 a3 a4 oo, red_expr S C (spec_entering_func_code a1 a2 a3 a4) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_entering_func_code_1 with (forall S C a1 a2 a3 a4 a5 a6 oo, red_expr S C (spec_entering_func_code_1 a1 a2 a3 a4 a5 a6) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_entering_func_code_2 with (forall S C a1 a2 a3 a4 a5 oo, red_expr S C (spec_entering_func_code_2 a1 a2 a3 a4 a5) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_entering_func_code_3 with (forall S C a1 a2 a3 a4 a5 a6 oo, red_expr S C (spec_entering_func_code_3 a1 a2 a3 a4 a5 a6) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_entering_func_code_4 with (forall S C a1 a2 oo, red_expr S C (spec_entering_func_code_4 a1 a2) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_binding_inst_formal_params with (forall S C a1 a2 a3 a4 oo, red_expr S C (spec_binding_inst_formal_params a1 a2 a3 a4) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_binding_inst_formal_params_1 with (forall S C a1 a2 a3 a4 a5 a6 a7 oo, red_expr S C (spec_binding_inst_formal_params_1 a1 a2 a3 a4 a5 a6 a7) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_binding_inst_formal_params_2 with (forall S C a1 a2 a3 a4 a5 a6 a7 oo, red_expr S C (spec_binding_inst_formal_params_2 a1 a2 a3 a4 a5 a6 a7) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_binding_inst_formal_params_3 with (forall S C a1 a2 a3 a4 a5 a6 oo, red_expr S C (spec_binding_inst_formal_params_3 a1 a2 a3 a4 a5 a6) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_binding_inst_formal_params_4 with (forall S C a1 a2 a3 a4 a5 oo, red_expr S C (spec_binding_inst_formal_params_4 a1 a2 a3 a4 a5) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_binding_inst_function_decls with (forall S C a1 a2 a3 a4 oo, red_expr S C (spec_binding_inst_function_decls a1 a2 a3 a4) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_binding_inst_function_decls_1 with (forall S C a1 a2 a3 a4 a5 a6 oo, red_expr S C (spec_binding_inst_function_decls_1 a1 a2 a3 a4 a5 a6) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_binding_inst_function_decls_2 with (forall S C a1 a2 a3 a4 a5 a6 a7 oo, red_expr S C (spec_binding_inst_function_decls_2 a1 a2 a3 a4 a5 a6 a7) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_binding_inst_function_decls_3 with (forall S C a1 a2 a3 a4 a5 a6 oo, red_expr S C (spec_binding_inst_function_decls_3 a1 a2 a3 a4 a5 a6) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_binding_inst_function_decls_3a with (forall S C a1 a2 a3 a4 a5 a6 oo, red_expr S C (spec_binding_inst_function_decls_3a a1 a2 a3 a4 a5 a6) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_binding_inst_function_decls_4 with (forall S C a1 a2 a3 a4 a5 a6 a7 oo, red_expr S C (spec_binding_inst_function_decls_4 a1 a2 a3 a4 a5 a6 a7) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_binding_inst_function_decls_5 with (forall S C a1 a2 a3 a4 a5 a6 oo, red_expr S C (spec_binding_inst_function_decls_5 a1 a2 a3 a4 a5 a6) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_binding_inst_function_decls_6 with (forall S C a1 a2 a3 a4 a5 oo, red_expr S C (spec_binding_inst_function_decls_6 a1 a2 a3 a4 a5) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_binding_inst_arg_obj with (forall S C a1 a2 a3 a4 a5 oo, red_expr S C (spec_binding_inst_arg_obj a1 a2 a3 a4 a5) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_binding_inst_arg_obj_1 with (forall S C a1 a2 a3 oo, red_expr S C (spec_binding_inst_arg_obj_1 a1 a2 a3) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_binding_inst_arg_obj_2 with (forall S C a1 a2 a3 oo, red_expr S C (spec_binding_inst_arg_obj_2 a1 a2 a3) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_binding_inst_var_decls with (forall S C a1 a2 a3 a4 oo, red_expr S C (spec_binding_inst_var_decls a1 a2 a3 a4) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_binding_inst_var_decls_1 with (forall S C a1 a2 a3 a4 a5 a6 oo, red_expr S C (spec_binding_inst_var_decls_1 a1 a2 a3 a4 a5 a6) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_binding_inst_var_decls_2 with (forall S C a1 a2 a3 a4 a5 oo, red_expr S C (spec_binding_inst_var_decls_2 a1 a2 a3 a4 a5) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_binding_inst with (forall S C a1 a2 a3 a4 oo, red_expr S C (spec_binding_inst a1 a2 a3 a4) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_binding_inst_1 with (forall S C a1 a2 a3 a4 a5 oo, red_expr S C (spec_binding_inst_1 a1 a2 a3 a4 a5) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_binding_inst_2 with (forall S C a1 a2 a3 a4 a5 a6 a7 oo, red_expr S C (spec_binding_inst_2 a1 a2 a3 a4 a5 a6 a7) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_binding_inst_3 with (forall S C a1 a2 a3 a4 a5 a6 oo, red_expr S C (spec_binding_inst_3 a1 a2 a3 a4 a5 a6) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_binding_inst_4 with (forall S C a1 a2 a3 a4 a5 a6 a7 a8 oo, red_expr S C (spec_binding_inst_4 a1 a2 a3 a4 a5 a6 a7 a8) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_binding_inst_5 with (forall S C a1 a2 a3 a4 a5 a6 a7 oo, red_expr S C (spec_binding_inst_5 a1 a2 a3 a4 a5 a6 a7) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_binding_inst_6 with (forall S C a1 a2 a3 a4 a5 a6 a7 a8 oo, red_expr S C (spec_binding_inst_6 a1 a2 a3 a4 a5 a6 a7 a8) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_binding_inst_7 with (forall S C a1 a2 a3 a4 oo, red_expr S C (spec_binding_inst_7 a1 a2 a3 a4) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_binding_inst_8 with (forall S C a1 a2 a3 oo, red_expr S C (spec_binding_inst_8 a1 a2 a3) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_make_arg_getter with (forall S C a1 a2 oo, red_expr S C (spec_make_arg_getter a1 a2) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_make_arg_setter with (forall S C a1 a2 oo, red_expr S C (spec_make_arg_setter a1 a2) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_args_obj_get_1 with (forall S C a1 a2 a3 a4 a5 oo, red_expr S C (spec_args_obj_get_1 a1 a2 a3 a4 a5) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_args_obj_define_own_prop_1 with (forall S C a1 a2 a3 a4 a5 a6 oo, red_expr S C (spec_args_obj_define_own_prop_1 a1 a2 a3 a4 a5 a6) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_args_obj_define_own_prop_2 with (forall S C a1 a2 a3 a4 a5 a6 a7 oo, red_expr S C (spec_args_obj_define_own_prop_2 a1 a2 a3 a4 a5 a6 a7) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_args_obj_define_own_prop_3 with (forall S C a1 a2 a3 a4 a5 a6 oo, red_expr S C (spec_args_obj_define_own_prop_3 a1 a2 a3 a4 a5 a6) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_args_obj_define_own_prop_4 with (forall S C a1 a2 a3 a4 a5 oo, red_expr S C (spec_args_obj_define_own_prop_4 a1 a2 a3 a4 a5) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_args_obj_define_own_prop_5 with (forall S C a1 oo, red_expr S C (spec_args_obj_define_own_prop_5 a1) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_args_obj_define_own_prop_6 with (forall S C oo, red_expr S C spec_args_obj_define_own_prop_6 oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_args_obj_delete_1 with (forall S C a1 a2 a3 a4 a5 oo, red_expr S C (spec_args_obj_delete_1 a1 a2 a3 a4 a5) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_args_obj_delete_2 with (forall S C a1 a2 a3 a4 a5 a6 oo, red_expr S C (spec_args_obj_delete_2 a1 a2 a3 a4 a5 a6) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_args_obj_delete_3 with (forall S C a1 oo, red_expr S C (spec_args_obj_delete_3 a1) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_args_obj_delete_4 with (forall S C a1 oo, red_expr S C (spec_args_obj_delete_4 a1) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_arguments_object_map with (forall S C a1 a2 a3 a4 a5 oo, red_expr S C (spec_arguments_object_map a1 a2 a3 a4 a5) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_arguments_object_map_1 with (forall S C a1 a2 a3 a4 a5 a6 oo, red_expr S C (spec_arguments_object_map_1 a1 a2 a3 a4 a5 a6) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_arguments_object_map_2 with (forall S C a1 a2 a3 a4 a5 a6 a7 a8 oo, red_expr S C (spec_arguments_object_map_2 a1 a2 a3 a4 a5 a6 a7 a8) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_arguments_object_map_3 with (forall S C a1 a2 a3 a4 a5 a6 a7 a8 a9 oo, red_expr S C (spec_arguments_object_map_3 a1 a2 a3 a4 a5 a6 a7 a8 a9) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_arguments_object_map_4 with (forall S C a1 a2 a3 a4 a5 a6 a7 a8 a9 oo, red_expr S C (spec_arguments_object_map_4 a1 a2 a3 a4 a5 a6 a7 a8 a9) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_arguments_object_map_5 with (forall S C a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 oo, red_expr S C (spec_arguments_object_map_5 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_arguments_object_map_6 with (forall S C a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 oo, red_expr S C (spec_arguments_object_map_6 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_arguments_object_map_7 with (forall S C a1 a2 a3 a4 a5 a6 a7 a8 a9 oo, red_expr S C (spec_arguments_object_map_7 a1 a2 a3 a4 a5 a6 a7 a8 a9) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_arguments_object_map_8 with (forall S C a1 a2 a3 oo, red_expr S C (spec_arguments_object_map_8 a1 a2 a3) oo) Sort Prop.  
Derive Inversion inv_red_expr_spec_create_arguments_object with (forall S C a1 a2 a3 a4 a5 oo, red_expr S C (spec_create_arguments_object a1 a2 a3 a4 a5) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_create_arguments_object_1 with (forall S C a1 a2 a3 a4 a5 a6 a7 oo, red_expr S C (spec_create_arguments_object_1 a1 a2 a3 a4 a5 a6 a7) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_create_arguments_object_2 with (forall S C a1 a2 a3 a4 oo, red_expr S C (spec_create_arguments_object_2 a1 a2 a3 a4) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_create_arguments_object_3 with (forall S C a1 a2 a3 a4 oo, red_expr S C (spec_create_arguments_object_3 a1 a2 a3 a4) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_create_arguments_object_4 with (forall S C a1 a2 oo, red_expr S C (spec_create_arguments_object_4 a1 a2) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_object_has_instance with (forall S C a1 a2 oo, red_expr S C (spec_object_has_instance a1 a2) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_object_has_instance_1 with (forall S C a1 a2 a3 oo, red_expr S C (spec_object_has_instance_1 a1 a2 a3) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_function_has_instance_1 with (forall S C a1 a2 oo, red_expr S C (spec_function_has_instance_1 a1 a2) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_function_has_instance_2 with (forall S C a1 a2 oo, red_expr S C (spec_function_has_instance_2 a1 a2) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_function_has_instance_3 with (forall S C a1 a2 oo, red_expr S C (spec_function_has_instance_3 a1 a2) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_function_has_instance_after_bind_1 with (forall S C a1 a2 oo, red_expr S C (spec_function_has_instance_after_bind_1 a1 a2) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_function_has_instance_after_bind_2 with (forall S C a1 a2 oo, red_expr S C (spec_function_has_instance_after_bind_2 a1 a2) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_function_get_1 with (forall S C a1 a2 a3 oo, red_expr S C (spec_function_get_1 a1 a2 a3) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_error with (forall S C a1 oo, red_expr S C (spec_error a1) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_error_1 with (forall S C a1 oo, red_expr S C (spec_error_1 a1) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_error_or_cst with (forall S C a1 a2 a3 oo, red_expr S C (spec_error_or_cst a1 a2 a3) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_error_or_void with (forall S C a1 a2 oo, red_expr S C (spec_error_or_void a1 a2) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_init_throw_type_error with (forall S C oo, red_expr S C spec_init_throw_type_error oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_init_throw_type_error_1 with (forall S C a1 oo, red_expr S C (spec_init_throw_type_error_1 a1) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_build_error with (forall S C a1 a2 oo, red_expr S C (spec_build_error a1 a2) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_build_error_1 with (forall S C a1 a2 oo, red_expr S C (spec_build_error_1 a1 a2) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_build_error_2 with (forall S C a1 a2 oo, red_expr S C (spec_build_error_2 a1 a2) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_new_object with (forall S C a1 oo, red_expr S C (spec_new_object a1) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_new_object_1 with (forall S C a1 a2 oo, red_expr S C (spec_new_object_1 a1 a2) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_prim_new_object with (forall S C a1 oo, red_expr S C (spec_prim_new_object a1) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_creating_function_object_proto with (forall S C a1 oo, red_expr S C (spec_creating_function_object_proto a1) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_creating_function_object_proto_1 with (forall S C a1 a2 oo, red_expr S C (spec_creating_function_object_proto_1 a1 a2) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_creating_function_object_proto_2 with (forall S C a1 a2 a3 oo, red_expr S C (spec_creating_function_object_proto_2 a1 a2 a3) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_creating_function_object with (forall S C a1 a2 a3 a4 oo, red_expr S C (spec_creating_function_object a1 a2 a3 a4) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_creating_function_object_1 with (forall S C a1 a2 a3 oo, red_expr S C (spec_creating_function_object_1 a1 a2 a3) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_creating_function_object_2 with (forall S C a1 a2 a3 oo, red_expr S C (spec_creating_function_object_2 a1 a2 a3) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_creating_function_object_3 with (forall S C a1 a2 oo, red_expr S C (spec_creating_function_object_3 a1 a2) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_creating_function_object_4 with (forall S C a1 a2 oo, red_expr S C (spec_creating_function_object_4 a1 a2) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_function_proto_apply with (forall S C a1 a2 a3 oo, red_expr S C (spec_function_proto_apply a1 a2 a3) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_function_proto_apply_1 with (forall S C a1 a2 a3 a4 oo, red_expr S C (spec_function_proto_apply_1 a1 a2 a3 a4) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_function_proto_apply_2 with (forall S C a1 a2 a3 a4 oo, red_expr S C (spec_function_proto_apply_2 a1 a2 a3 a4) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_function_proto_apply_3 with (forall S C a1 a2 a3 oo, red_expr S C (spec_function_proto_apply_3 a1 a2 a3) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_function_proto_bind_1 with (forall S C a1 a2 a3 oo, red_expr S C (spec_function_proto_bind_1 a1 a2 a3) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_function_proto_bind_2 with (forall S C a1 a2 a3 oo, red_expr S C (spec_function_proto_bind_2 a1 a2 a3) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_function_proto_bind_3 with (forall S C a1 a2 oo, red_expr S C (spec_function_proto_bind_3 a1 a2) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_function_proto_bind_4 with (forall S C a1 a2 oo, red_expr S C (spec_function_proto_bind_4 a1 a2) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_function_proto_bind_5 with (forall S C a1 oo, red_expr S C (spec_function_proto_bind_5 a1) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_function_proto_bind_6 with (forall S C a1 a2 oo, red_expr S C (spec_function_proto_bind_6 a1 a2) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_function_proto_bind_7 with (forall S C a1 a2 oo, red_expr S C (spec_function_proto_bind_7 a1 a2) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_create_new_function_in with (forall S C a1 a2 a3 oo, red_expr S C (spec_create_new_function_in a1 a2 a3) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_call with (forall S C a1 a2 a3 oo, red_expr S C (spec_call a1 a2 a3) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_call_1 with (forall S C a1 a2 a3 a4 oo, red_expr S C (spec_call_1 a1 a2 a3 a4) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_call_prealloc with (forall S C a1 a2 a3 oo, red_expr S C (spec_call_prealloc a1 a2 a3) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_call_default with (forall S C a1 a2 a3 oo, red_expr S C (spec_call_default a1 a2 a3) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_call_default_1 with (forall S C a1 oo, red_expr S C (spec_call_default_1 a1) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_call_default_2 with (forall S C a1 oo, red_expr S C (spec_call_default_2 a1) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_call_default_3 with (forall S C a1 oo, red_expr S C (spec_call_default_3 a1) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_construct with (forall S C a1 a2 oo, red_expr S C (spec_construct a1 a2) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_construct_1 with (forall S C a1 a2 a3 oo, red_expr S C (spec_construct_1 a1 a2 a3) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_construct_prealloc with (forall S C a1 a2 oo, red_expr S C (spec_construct_prealloc a1 a2) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_construct_default with (forall S C a1 a2 oo, red_expr S C (spec_construct_default a1 a2) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_construct_default_1 with (forall S C a1 a2 a3 oo, red_expr S C (spec_construct_default_1 a1 a2 a3) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_construct_default_2 with (forall S C a1 a2 oo, red_expr S C (spec_construct_default_2 a1 a2) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_construct_1_after_bind with (forall S C a1 a2 a3 oo, red_expr S C (spec_construct_1_after_bind a1 a2 a3) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_construct_bool_1 with (forall S C a1 oo, red_expr S C (spec_construct_bool_1 a1) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_construct_number_1 with (forall S C a1 oo, red_expr S C (spec_construct_number_1 a1) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_call_global_is_nan_1 with (forall S C a1 oo, red_expr S C (spec_call_global_is_nan_1 a1) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_call_global_is_finite_1 with (forall S C a1 oo, red_expr S C (spec_call_global_is_finite_1 a1) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_call_object_call_1 with (forall S C a1 a2 oo, red_expr S C (spec_call_object_call_1 a1 a2) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_call_object_new_1 with (forall S C a1 oo, red_expr S C (spec_call_object_new_1 a1) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_call_object_get_proto_of_1 with (forall S C a1 oo, red_expr S C (spec_call_object_get_proto_of_1 a1) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_call_object_is_extensible_1 with (forall S C a1 oo, red_expr S C (spec_call_object_is_extensible_1 a1) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_call_object_define_props_1 with (forall S C a1 a2 oo, red_expr S C (spec_call_object_define_props_1 a1 a2) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_call_object_define_props_2 with (forall S C a1 a2 oo, red_expr S C (spec_call_object_define_props_2 a1 a2) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_call_object_define_props_3 with (forall S C a1 a2 a3 a4 oo, red_expr S C (spec_call_object_define_props_3 a1 a2 a3 a4) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_call_object_define_props_4 with (forall S C a1 a2 a3 a4 a5 a6 oo, red_expr S C (spec_call_object_define_props_4 a1 a2 a3 a4 a5 a6) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_call_object_define_props_5 with (forall S C a1 a2 a3 a4 a5 a6 oo, red_expr S C (spec_call_object_define_props_5 a1 a2 a3 a4 a5 a6) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_call_object_define_props_6 with (forall S C a1 a2 oo, red_expr S C (spec_call_object_define_props_6 a1 a2) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_call_object_define_props_7 with (forall S C a1 a2 a3 oo, red_expr S C (spec_call_object_define_props_7 a1 a2 a3) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_call_object_create_1 with (forall S C a1 a2 oo, red_expr S C (spec_call_object_create_1 a1 a2) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_call_object_create_2 with (forall S C a1 a2 a3 oo, red_expr S C (spec_call_object_create_2 a1 a2 a3) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_call_object_create_3 with (forall S C a1 a2 oo, red_expr S C (spec_call_object_create_3 a1 a2) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_call_object_seal_1 with (forall S C a1 oo, red_expr S C (spec_call_object_seal_1 a1) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_call_object_seal_2 with (forall S C a1 a2 oo, red_expr S C (spec_call_object_seal_2 a1 a2) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_call_object_seal_3 with (forall S C a1 a2 a3 a4 oo, red_expr S C (spec_call_object_seal_3 a1 a2 a3 a4) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_call_object_seal_4 with (forall S C a1 a2 a3 oo, red_expr S C (spec_call_object_seal_4 a1 a2 a3) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_call_object_is_sealed_1 with (forall S C a1 oo, red_expr S C (spec_call_object_is_sealed_1 a1) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_call_object_is_sealed_2 with (forall S C a1 a2 oo, red_expr S C (spec_call_object_is_sealed_2 a1 a2) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_call_object_is_sealed_3 with (forall S C a1 a2 a3 oo, red_expr S C (spec_call_object_is_sealed_3 a1 a2 a3) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_call_object_freeze_1 with (forall S C a1 oo, red_expr S C (spec_call_object_freeze_1 a1) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_call_object_freeze_2 with (forall S C a1 a2 oo, red_expr S C (spec_call_object_freeze_2 a1 a2) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_call_object_freeze_3 with (forall S C a1 a2 a3 a4 oo, red_expr S C (spec_call_object_freeze_3 a1 a2 a3 a4) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_call_object_freeze_4 with (forall S C a1 a2 a3 a4 oo, red_expr S C (spec_call_object_freeze_4 a1 a2 a3 a4) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_call_object_freeze_5 with (forall S C a1 a2 a3 oo, red_expr S C (spec_call_object_freeze_5 a1 a2 a3) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_call_object_is_frozen_1 with (forall S C a1 oo, red_expr S C (spec_call_object_is_frozen_1 a1) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_call_object_is_frozen_2 with (forall S C a1 a2 oo, red_expr S C (spec_call_object_is_frozen_2 a1 a2) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_call_object_is_frozen_3 with (forall S C a1 a2 a3 oo, red_expr S C (spec_call_object_is_frozen_3 a1 a2 a3) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_call_object_is_frozen_4 with (forall S C a1 a2 a3 oo, red_expr S C (spec_call_object_is_frozen_4 a1 a2 a3) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_call_object_is_frozen_5 with (forall S C a1 a2 a3 oo, red_expr S C (spec_call_object_is_frozen_5 a1 a2 a3) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_call_object_prevent_extensions_1 with (forall S C a1 oo, red_expr S C (spec_call_object_prevent_extensions_1 a1) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_call_object_define_prop_1 with (forall S C a1 a2 a3 oo, red_expr S C (spec_call_object_define_prop_1 a1 a2 a3) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_call_object_define_prop_2 with (forall S C a1 a2 a3 oo, red_expr S C (spec_call_object_define_prop_2 a1 a2 a3) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_call_object_define_prop_3 with (forall S C a1 a2 a3 oo, red_expr S C (spec_call_object_define_prop_3 a1 a2 a3) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_call_object_define_prop_4 with (forall S C a1 a2 oo, red_expr S C (spec_call_object_define_prop_4 a1 a2) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_call_object_get_own_prop_descriptor_1 with (forall S C a1 a2 oo, red_expr S C (spec_call_object_get_own_prop_descriptor_1 a1 a2) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_call_object_get_own_prop_descriptor_2 with (forall S C a1 a2 oo, red_expr S C (spec_call_object_get_own_prop_descriptor_2 a1 a2) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_call_object_proto_to_string_1 with (forall S C a1 oo, red_expr S C (spec_call_object_proto_to_string_1 a1) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_call_object_proto_to_string_2 with (forall S C a1 oo, red_expr S C (spec_call_object_proto_to_string_2 a1) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_call_object_proto_has_own_prop_1 with (forall S C a1 a2 oo, red_expr S C (spec_call_object_proto_has_own_prop_1 a1 a2) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_call_object_proto_has_own_prop_2 with (forall S C a1 a2 oo, red_expr S C (spec_call_object_proto_has_own_prop_2 a1 a2) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_call_object_proto_has_own_prop_3 with (forall S C a1 oo, red_expr S C (spec_call_object_proto_has_own_prop_3 a1) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_call_object_proto_is_prototype_of_2_1 with (forall S C a1 a2 oo, red_expr S C (spec_call_object_proto_is_prototype_of_2_1 a1 a2) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_call_object_proto_is_prototype_of_2_2 with (forall S C a1 a2 oo, red_expr S C (spec_call_object_proto_is_prototype_of_2_2 a1 a2) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_call_object_proto_is_prototype_of_2_3 with (forall S C a1 a2 oo, red_expr S C (spec_call_object_proto_is_prototype_of_2_3 a1 a2) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_call_object_proto_is_prototype_of_2_4 with (forall S C a1 a2 oo, red_expr S C (spec_call_object_proto_is_prototype_of_2_4 a1 a2) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_call_object_proto_prop_is_enumerable_1 with (forall S C a1 a2 oo, red_expr S C (spec_call_object_proto_prop_is_enumerable_1 a1 a2) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_call_object_proto_prop_is_enumerable_2 with (forall S C a1 a2 oo, red_expr S C (spec_call_object_proto_prop_is_enumerable_2 a1 a2) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_call_object_proto_prop_is_enumerable_3 with (forall S C a1 a2 oo, red_expr S C (spec_call_object_proto_prop_is_enumerable_3 a1 a2) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_call_object_proto_prop_is_enumerable_4 with (forall S C a1 oo, red_expr S C (spec_call_object_proto_prop_is_enumerable_4 a1) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_call_array_new_1 with (forall S C a1 oo, red_expr S C (spec_call_array_new_1 a1) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_call_array_new_2 with (forall S C a1 a2 oo, red_expr S C (spec_call_array_new_2 a1 a2) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_call_array_new_3 with (forall S C a1 a2 a3 oo, red_expr S C (spec_call_array_new_3 a1 a2 a3) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_call_array_new_single_1 with (forall S C a1 oo, red_expr S C (spec_call_array_new_single_1 a1) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_call_array_new_single_2 with (forall S C a1 a2 oo, red_expr S C (spec_call_array_new_single_2 a1 a2) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_call_array_new_single_3 with (forall S C a1 a2 a3 oo, red_expr S C (spec_call_array_new_single_3 a1 a2 a3) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_call_array_new_single_4 with (forall S C a1 a2 oo, red_expr S C (spec_call_array_new_single_4 a1 a2) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_call_array_is_array_1 with (forall S C a1 oo, red_expr S C (spec_call_array_is_array_1 a1) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_call_array_is_array_2_3 with (forall S C a1 oo, red_expr S C (spec_call_array_is_array_2_3 a1) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_call_array_proto_join with (forall S C a1 a2 oo, red_expr S C (spec_call_array_proto_join a1 a2) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_call_array_proto_join_1 with (forall S C a1 a2 a3 oo, red_expr S C (spec_call_array_proto_join_1 a1 a2 a3) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_call_array_proto_join_2 with (forall S C a1 a2 a3 oo, red_expr S C (spec_call_array_proto_join_2 a1 a2 a3) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_call_array_proto_join_3 with (forall S C a1 a2 a3 oo, red_expr S C (spec_call_array_proto_join_3 a1 a2 a3) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_call_array_proto_join_4 with (forall S C a1 a2 a3 oo, red_expr S C (spec_call_array_proto_join_4 a1 a2 a3) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_call_array_proto_join_5 with (forall S C a1 a2 a3 a4 oo, red_expr S C (spec_call_array_proto_join_5 a1 a2 a3 a4) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_call_array_proto_join_elements with (forall S C a1 a2 a3 a4 a5 oo, red_expr S C (spec_call_array_proto_join_elements a1 a2 a3 a4 a5) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_call_array_proto_join_elements_1 with (forall S C a1 a2 a3 a4 a5 oo, red_expr S C (spec_call_array_proto_join_elements_1 a1 a2 a3 a4 a5) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_call_array_proto_join_elements_2 with (forall S C a1 a2 a3 a4 a5 a6 oo, red_expr S C (spec_call_array_proto_join_elements_2 a1 a2 a3 a4 a5 a6) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_call_array_proto_to_string with (forall S C a1 oo, red_expr S C (spec_call_array_proto_to_string a1) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_call_array_proto_to_string_1 with (forall S C a1 a2 oo, red_expr S C (spec_call_array_proto_to_string_1 a1 a2) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_call_array_proto_pop_1 with (forall S C a1 oo, red_expr S C (spec_call_array_proto_pop_1 a1) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_call_array_proto_pop_2 with (forall S C a1 a2 oo, red_expr S C (spec_call_array_proto_pop_2 a1 a2) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_call_array_proto_pop_3 with (forall S C a1 a2 oo, red_expr S C (spec_call_array_proto_pop_3 a1 a2) oo) Sort Prop.  
Derive Inversion inv_red_expr_spec_call_array_proto_pop_3_empty_1 with (forall S C a1 oo, red_expr S C (spec_call_array_proto_pop_3_empty_1 a1) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_call_array_proto_pop_3_empty_2 with (forall S C a1 oo, red_expr S C (spec_call_array_proto_pop_3_empty_2 a1) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_call_array_proto_pop_3_nonempty_1 with (forall S C a1 a2 oo, red_expr S C (spec_call_array_proto_pop_3_nonempty_1 a1 a2) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_call_array_proto_pop_3_nonempty_2 with (forall S C a1 a2 oo, red_expr S C (spec_call_array_proto_pop_3_nonempty_2 a1 a2) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_call_array_proto_pop_3_nonempty_3 with (forall S C a1 a2 a3 oo, red_expr S C (spec_call_array_proto_pop_3_nonempty_3 a1 a2 a3) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_call_array_proto_pop_3_nonempty_4 with (forall S C a1 a2 a3 a4 oo, red_expr S C (spec_call_array_proto_pop_3_nonempty_4 a1 a2 a3 a4) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_call_array_proto_pop_3_nonempty_5 with (forall S C a1 a2 oo, red_expr S C (spec_call_array_proto_pop_3_nonempty_5 a1 a2) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_call_array_proto_push_1 with (forall S C a1 a2 oo, red_expr S C (spec_call_array_proto_push_1 a1 a2) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_call_array_proto_push_2 with (forall S C a1 a2 a3 oo, red_expr S C (spec_call_array_proto_push_2 a1 a2 a3) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_call_array_proto_push_3 with (forall S C a1 a2 a3 oo, red_expr S C (spec_call_array_proto_push_3 a1 a2 a3) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_call_array_proto_push_4 with (forall S C a1 a2 a3 oo, red_expr S C (spec_call_array_proto_push_4 a1 a2 a3) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_call_array_proto_push_4_nonempty_1 with (forall S C a1 a2 a3 a4 oo, red_expr S C (spec_call_array_proto_push_4_nonempty_1 a1 a2 a3 a4) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_call_array_proto_push_4_nonempty_2 with (forall S C a1 a2 a3 a4 a5 oo, red_expr S C (spec_call_array_proto_push_4_nonempty_2 a1 a2 a3 a4 a5) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_call_array_proto_push_4_nonempty_3 with (forall S C a1 a2 a3 a4 a5 oo, red_expr S C (spec_call_array_proto_push_4_nonempty_3 a1 a2 a3 a4 a5) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_call_array_proto_push_5 with (forall S C a1 a2 oo, red_expr S C (spec_call_array_proto_push_5 a1 a2) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_call_array_proto_push_6 with (forall S C a1 a2 oo, red_expr S C (spec_call_array_proto_push_6 a1 a2) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_call_string_non_empty with (forall S C a1 oo, red_expr S C (spec_call_string_non_empty a1) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_construct_string_1 with (forall S C a1 oo, red_expr S C (spec_construct_string_1 a1) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_construct_string_2 with (forall S C a1 oo, red_expr S C (spec_construct_string_2 a1) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_call_bool_proto_to_string_1 with (forall S C a1 oo, red_expr S C (spec_call_bool_proto_to_string_1 a1) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_call_bool_proto_value_of_1 with (forall S C a1 oo, red_expr S C (spec_call_bool_proto_value_of_1 a1) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_call_bool_proto_value_of_2 with (forall S C a1 oo, red_expr S C (spec_call_bool_proto_value_of_2 a1) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_call_number_proto_to_string_1 with (forall S C a1 a2 oo, red_expr S C (spec_call_number_proto_to_string_1 a1 a2) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_call_number_proto_to_string_2 with (forall S C a1 a2 oo, red_expr S C (spec_call_number_proto_to_string_2 a1 a2) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_call_number_proto_value_of_1 with (forall S C a1 oo, red_expr S C (spec_call_number_proto_value_of_1 a1) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_call_error_proto_to_string_1 with (forall S C a1 oo, red_expr S C (spec_call_error_proto_to_string_1 a1) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_call_error_proto_to_string_2 with (forall S C a1 a2 oo, red_expr S C (spec_call_error_proto_to_string_2 a1 a2) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_call_error_proto_to_string_3 with (forall S C a1 a2 oo, red_expr S C (spec_call_error_proto_to_string_3 a1 a2) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_call_error_proto_to_string_4 with (forall S C a1 a2 a3 oo, red_expr S C (spec_call_error_proto_to_string_4 a1 a2 a3) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_call_error_proto_to_string_5 with (forall S C a1 a2 a3 oo, red_expr S C (spec_call_error_proto_to_string_5 a1 a2 a3) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_call_error_proto_to_string_6 with (forall S C a1 a2 a3 oo, red_expr S C (spec_call_error_proto_to_string_6 a1 a2 a3) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_returns with (forall S C a1 oo, red_expr S C (spec_returns a1) oo) Sort Prop. 