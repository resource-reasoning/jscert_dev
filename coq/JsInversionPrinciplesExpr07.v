Set Implicit Arguments.
Require Import JsPrettyInterm JsPrettyRules.

(**************************************************************)
(** ** Inversion principles for expressions, Part 07          *)

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