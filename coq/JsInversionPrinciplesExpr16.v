Set Implicit Arguments.
Require Import JsPrettyInterm JsPrettyRules.

(**************************************************************)
(** ** Inversion principles for expressions, Part 16          *)

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