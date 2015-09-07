Set Implicit Arguments.
Require Import JsPrettyInterm JsPrettyRules.

(**************************************************************)
(** ** Inversion principles for expressions, Part 02          *)

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