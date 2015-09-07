Set Implicit Arguments.
Require Import JsPrettyInterm JsPrettyRules.

(**************************************************************)
(** ** Inversion principles for expressions, Part 17          *)

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