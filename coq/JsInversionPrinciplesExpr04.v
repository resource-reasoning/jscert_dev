Set Implicit Arguments.
Require Import JsPrettyInterm JsPrettyRules.

(**************************************************************)
(** ** Inversion principles for expressions, Part 04          *)

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