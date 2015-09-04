Set Implicit Arguments.
Require Import Shared.
Require Import JsSyntax JsSyntaxAux JsCommon JsCommonAux JsPreliminary.
Require Import JsPrettyInterm JsPrettyRules.

(**************************************************************)
(** ** Inversion principles for programs                      *)

Derive Inversion inv_red_spec_spec_to_int32 with (forall T S C a1 oo, (@red_spec T S C (spec_to_int32 a1) oo)) Sort Prop.
Derive Inversion inv_red_spec_spec_to_int32_1 with (forall T S C a1 oo, (@red_spec T S C (spec_to_int32_1 a1) oo)) Sort Prop.
Derive Inversion inv_red_spec_spec_to_uint32 with (forall T S C a1 oo, (@red_spec T S C (spec_to_uint32 a1) oo)) Sort Prop.
Derive Inversion inv_red_spec_spec_to_uint32_1 with (forall T S C a1 oo, (@red_spec T S C (spec_to_uint32_1 a1) oo)) Sort Prop.
Derive Inversion inv_red_spec_spec_expr_get_value_conv with (forall T S C a1 a2 oo, (@red_spec T S C (spec_expr_get_value_conv a1 a2) oo)) Sort Prop.
Derive Inversion inv_red_spec_spec_expr_get_value_conv_1 with (forall T S C a1 a2 oo, (@red_spec T S C (spec_expr_get_value_conv_1 a1 a2) oo)) Sort Prop.
Derive Inversion inv_red_spec_spec_expr_get_value_conv_2 with (forall T S C a1 oo, (@red_spec T S C (spec_expr_get_value_conv_2 a1) oo)) Sort Prop.
Derive Inversion inv_red_spec_spec_convert_twice with (forall T S C a1 a2 oo, (@red_spec T S C (spec_convert_twice a1 a2) oo)) Sort Prop.
Derive Inversion inv_red_spec_spec_convert_twice_1 with (forall T S C a1 a2 oo, (@red_spec T S C (spec_convert_twice_1 a1 a2) oo)) Sort Prop.
Derive Inversion inv_red_spec_spec_convert_twice_2 with (forall T S C a1 a2 oo, (@red_spec T S C (spec_convert_twice_2 a1 a2) oo)) Sort Prop.
Derive Inversion inv_red_spec_spec_list_expr with (forall T S C a1 oo, (@red_spec T S C (spec_list_expr a1) oo)) Sort Prop.
Derive Inversion inv_red_spec_spec_list_expr_1 with (forall T S C a1 a2 oo, (@red_spec T S C (spec_list_expr_1 a1 a2) oo)) Sort Prop.
Derive Inversion inv_red_spec_spec_list_expr_2 with (forall T S C a1 a2 a3 oo, (@red_spec T S C (spec_list_expr_2 a1 a2 a3) oo)) Sort Prop.
Derive Inversion inv_red_spec_spec_to_descriptor with (forall T S C a1 oo, (@red_spec T S C (spec_to_descriptor a1) oo)) Sort Prop.
Derive Inversion inv_red_spec_spec_to_descriptor_1a with (forall T S C a1 a2 oo, (@red_spec T S C (spec_to_descriptor_1a a1 a2) oo)) Sort Prop.
Derive Inversion inv_red_spec_spec_to_descriptor_1b with (forall T S C a1 a2 a3 oo, (@red_spec T S C (spec_to_descriptor_1b a1 a2 a3) oo)) Sort Prop.
Derive Inversion inv_red_spec_spec_to_descriptor_1c with (forall T S C a1 a2 a3 oo, (@red_spec T S C (spec_to_descriptor_1c a1 a2 a3) oo)) Sort Prop.
Derive Inversion inv_red_spec_spec_to_descriptor_2a with (forall T S C a1 a2 oo, (@red_spec T S C (spec_to_descriptor_2a a1 a2) oo)) Sort Prop.
Derive Inversion inv_red_spec_spec_to_descriptor_2b with (forall T S C a1 a2 a3 oo, (@red_spec T S C (spec_to_descriptor_2b a1 a2 a3) oo)) Sort Prop.
Derive Inversion inv_red_spec_spec_to_descriptor_2c with (forall T S C a1 a2 a3 oo, (@red_spec T S C (spec_to_descriptor_2c a1 a2 a3) oo)) Sort Prop.
Derive Inversion inv_red_spec_spec_to_descriptor_3a with (forall T S C a1 a2 oo, (@red_spec T S C (spec_to_descriptor_3a a1 a2) oo)) Sort Prop.
Derive Inversion inv_red_spec_spec_to_descriptor_3b with (forall T S C a1 a2 a3 oo, (@red_spec T S C (spec_to_descriptor_3b a1 a2 a3) oo)) Sort Prop.
Derive Inversion inv_red_spec_spec_to_descriptor_3c with (forall T S C a1 a2 a3 oo, (@red_spec T S C (spec_to_descriptor_3c a1 a2 a3) oo)) Sort Prop.
Derive Inversion inv_red_spec_spec_to_descriptor_4a with (forall T S C a1 a2 oo, (@red_spec T S C (spec_to_descriptor_4a a1 a2) oo)) Sort Prop.
Derive Inversion inv_red_spec_spec_to_descriptor_4b with (forall T S C a1 a2 a3 oo, (@red_spec T S C (spec_to_descriptor_4b a1 a2 a3) oo)) Sort Prop.
Derive Inversion inv_red_spec_spec_to_descriptor_4c with (forall T S C a1 a2 a3 oo, (@red_spec T S C (spec_to_descriptor_4c a1 a2 a3) oo)) Sort Prop.
Derive Inversion inv_red_spec_spec_to_descriptor_5a with (forall T S C a1 a2 oo, (@red_spec T S C (spec_to_descriptor_5a a1 a2) oo)) Sort Prop.
Derive Inversion inv_red_spec_spec_to_descriptor_5b with (forall T S C a1 a2 a3 oo, (@red_spec T S C (spec_to_descriptor_5b a1 a2 a3) oo)) Sort Prop.
Derive Inversion inv_red_spec_spec_to_descriptor_5c with (forall T S C a1 a2 a3 oo, (@red_spec T S C (spec_to_descriptor_5c a1 a2 a3) oo)) Sort Prop.
Derive Inversion inv_red_spec_spec_to_descriptor_6a with (forall T S C a1 a2 oo, (@red_spec T S C (spec_to_descriptor_6a a1 a2) oo)) Sort Prop.
Derive Inversion inv_red_spec_spec_to_descriptor_6b with (forall T S C a1 a2 a3 oo, (@red_spec T S C (spec_to_descriptor_6b a1 a2 a3) oo)) Sort Prop.
Derive Inversion inv_red_spec_spec_to_descriptor_6c with (forall T S C a1 a2 a3 oo, (@red_spec T S C (spec_to_descriptor_6c a1 a2 a3) oo)) Sort Prop.
Derive Inversion inv_red_spec_spec_to_descriptor_7 with (forall T S C a1 a2 oo, (@red_spec T S C (spec_to_descriptor_7 a1 a2) oo)) Sort Prop.
Derive Inversion inv_red_spec_spec_object_get_own_prop with (forall T S C a1 a2 oo, (@red_spec T S C (spec_object_get_own_prop a1 a2) oo)) Sort Prop.
Derive Inversion inv_red_spec_spec_object_get_own_prop_1 with (forall T S C a1 a2 a3 oo, (@red_spec T S C (spec_object_get_own_prop_1 a1 a2 a3) oo)) Sort Prop.
Derive Inversion inv_red_spec_spec_object_get_own_prop_2 with (forall T S C a1 a2 a3 oo, (@red_spec T S C (spec_object_get_own_prop_2 a1 a2 a3) oo)) Sort Prop.
Derive Inversion inv_red_spec_spec_object_get_prop with (forall T S C a1 a2 oo, (@red_spec T S C (spec_object_get_prop a1 a2) oo)) Sort Prop.
Derive Inversion inv_red_spec_spec_object_get_prop_1 with (forall T S C a1 a2 a3 oo, (@red_spec T S C (spec_object_get_prop_1 a1 a2 a3) oo)) Sort Prop.
Derive Inversion inv_red_spec_spec_object_get_prop_2 with (forall T S C a1 a2 a3 oo, (@red_spec T S C (spec_object_get_prop_2 a1 a2 a3) oo)) Sort Prop.
Derive Inversion inv_red_spec_spec_object_get_prop_3 with (forall T S C a1 a2 a3 oo, (@red_spec T S C (spec_object_get_prop_3 a1 a2 a3) oo)) Sort Prop.
Derive Inversion inv_red_spec_spec_get_value with (forall T S C a1 oo, (@red_spec T S C (spec_get_value a1) oo)) Sort Prop.
Derive Inversion inv_red_spec_spec_get_value_ref_b_1 with (forall T S C a1 oo, (@red_spec T S C (spec_get_value_ref_b_1 a1) oo)) Sort Prop.
Derive Inversion inv_red_spec_spec_get_value_ref_c_1 with (forall T S C a1 oo, (@red_spec T S C (spec_get_value_ref_c_1 a1) oo)) Sort Prop.
Derive Inversion inv_red_spec_spec_expr_get_value with (forall T S C a1 oo, (@red_spec T S C (spec_expr_get_value a1) oo)) Sort Prop.
Derive Inversion inv_red_spec_spec_expr_get_value_1 with (forall T S C a1 oo, (@red_spec T S C (spec_expr_get_value_1 a1) oo)) Sort Prop.
Derive Inversion inv_red_spec_spec_lexical_env_get_identifier_ref with (forall T S C a1 a2 a3 oo, (@red_spec T S C (spec_lexical_env_get_identifier_ref a1 a2 a3) oo)) Sort Prop.
Derive Inversion inv_red_spec_spec_lexical_env_get_identifier_ref_1 with (forall T S C a1 a2 a3 a4 oo, (@red_spec T S C (spec_lexical_env_get_identifier_ref_1 a1 a2 a3 a4) oo)) Sort Prop.
Derive Inversion inv_red_spec_spec_lexical_env_get_identifier_ref_2 with (forall T S C a1 a2 a3 a4 a5 oo, (@red_spec T S C (spec_lexical_env_get_identifier_ref_2 a1 a2 a3 a4 a5) oo)) Sort Prop.
Derive Inversion inv_red_spec_spec_error_spec with (forall T S C a1 oo, (@red_spec T S C (spec_error_spec a1) oo)) Sort Prop.
Derive Inversion inv_red_spec_spec_error_spec_1 with (forall T S C a1 oo, (@red_spec T S C (spec_error_spec_1 a1) oo)) Sort Prop.
Derive Inversion inv_red_spec_spec_args_obj_get_own_prop_1 with (forall T S C a1 a2 a3 oo, (@red_spec T S C (spec_args_obj_get_own_prop_1 a1 a2 a3) oo)) Sort Prop.
Derive Inversion inv_red_spec_spec_args_obj_get_own_prop_2 with (forall T S C a1 a2 a3 a4 a5 oo, (@red_spec T S C (spec_args_obj_get_own_prop_2 a1 a2 a3 a4 a5) oo)) Sort Prop.
Derive Inversion inv_red_spec_spec_args_obj_get_own_prop_3 with (forall T S C a1 a2 oo, (@red_spec T S C (spec_args_obj_get_own_prop_3 a1 a2) oo)) Sort Prop.
Derive Inversion inv_red_spec_spec_args_obj_get_own_prop_4 with (forall T S C a1 oo, (@red_spec T S C (spec_args_obj_get_own_prop_4 a1) oo)) Sort Prop.
Derive Inversion inv_red_spec_spec_string_get_own_prop_1 with (forall T S C a1 a2 a3 oo, (@red_spec T S C (spec_string_get_own_prop_1 a1 a2 a3) oo)) Sort Prop.
Derive Inversion inv_red_spec_spec_string_get_own_prop_2 with (forall T S C a1 a2 a3 oo, (@red_spec T S C (spec_string_get_own_prop_2 a1 a2 a3) oo)) Sort Prop.
Derive Inversion inv_red_spec_spec_string_get_own_prop_3 with (forall T S C a1 a2 a3 oo, (@red_spec T S C (spec_string_get_own_prop_3 a1 a2 a3) oo)) Sort Prop.
Derive Inversion inv_red_spec_spec_string_get_own_prop_4 with (forall T S C a1 a2 oo, (@red_spec T S C (spec_string_get_own_prop_4 a1 a2) oo)) Sort Prop.
Derive Inversion inv_red_spec_spec_string_get_own_prop_5 with (forall T S C a1 a2 oo, (@red_spec T S C (spec_string_get_own_prop_5 a1 a2) oo)) Sort Prop.
Derive Inversion inv_red_spec_spec_string_get_own_prop_6 with (forall T S C a1 a2 a3 oo, (@red_spec T S C (spec_string_get_own_prop_6 a1 a2 a3) oo)) Sort Prop.
Derive Inversion inv_red_spec_spec_function_proto_apply_get_args with (forall T S C a1 a2 a3 oo, (@red_spec T S C (spec_function_proto_apply_get_args a1 a2 a3) oo)) Sort Prop.
Derive Inversion inv_red_spec_spec_function_proto_apply_get_args_1 with (forall T S C a1 a2 a3 a4 oo, (@red_spec T S C (spec_function_proto_apply_get_args_1 a1 a2 a3 a4) oo)) Sort Prop.
Derive Inversion inv_red_spec_spec_function_proto_apply_get_args_2 with (forall T S C a1 a2 a3 a4 oo, (@red_spec T S C (spec_function_proto_apply_get_args_2 a1 a2 a3 a4) oo)) Sort Prop.
Derive Inversion inv_red_spec_spec_function_proto_apply_get_args_3 with (forall T S C a1 a2 oo, (@red_spec T S C (spec_function_proto_apply_get_args_3 a1 a2) oo)) Sort Prop.
Derive Inversion inv_red_spec_spec_function_proto_bind_length with (forall T S C a1 a2 oo, (@red_spec T S C (spec_function_proto_bind_length a1 a2) oo)) Sort Prop.
Derive Inversion inv_red_spec_spec_function_proto_bind_length_1 with (forall T S C a1 a2 oo, (@red_spec T S C (spec_function_proto_bind_length_1 a1 a2) oo)) Sort Prop.
Derive Inversion inv_red_spec_spec_function_proto_bind_length_2 with (forall T S C a1 a2 oo, (@red_spec T S C (spec_function_proto_bind_length_2 a1 a2) oo)) Sort Prop.
Derive Inversion inv_red_spec_spec_function_proto_bind_length_3 with (forall T S C a1 a2 oo, (@red_spec T S C (spec_function_proto_bind_length_3 a1 a2) oo)) Sort Prop.
Derive Inversion inv_red_spec_spec_call_array_proto_join_vtsfj with (forall T S C a1 a2 oo, (@red_spec T S C (spec_call_array_proto_join_vtsfj a1 a2) oo)) Sort Prop.
Derive Inversion inv_red_spec_spec_call_array_proto_join_vtsfj_1 with (forall T S C a1 a2 oo, (@red_spec T S C (spec_call_array_proto_join_vtsfj_1 a1 a2) oo)) Sort Prop.
Derive Inversion inv_red_spec_spec_call_array_proto_join_vtsfj_2 with (forall T S C a1 a2 oo, (@red_spec T S C (spec_call_array_proto_join_vtsfj_2 a1 a2) oo)) Sort Prop.
Derive Inversion inv_red_spec_spec_call_array_proto_join_vtsfj_3 with (forall T S C a1 oo, (@red_spec T S C (spec_call_array_proto_join_vtsfj_3 a1) oo)) Sort Prop.