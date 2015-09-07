Set Implicit Arguments.
Require Import JsPrettyInterm JsPrettyRules.

(**************************************************************)
(** ** Inversion principles for expressions, Part 03          *)

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