Set Implicit Arguments.
Require Import JsPrettyInterm JsPrettyRules.

(**************************************************************)
(** ** Inversion principles for expressions, Part 18          *)

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