Set Implicit Arguments.
Require Import JsPrettyInterm JsPrettyRules.

(**************************************************************)
(** ** Inversion principles for expressions, Part 06          *)

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