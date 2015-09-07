Set Implicit Arguments.
Require Import JsPrettyInterm JsPrettyRules.

(**************************************************************)
(** ** Inversion principles for expressions, Part 01          *)

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