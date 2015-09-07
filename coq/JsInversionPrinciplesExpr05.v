Set Implicit Arguments.
Require Import JsPrettyInterm JsPrettyRules.

(**************************************************************)
(** ** Inversion principles for expressions, Part 05          *)

Derive Inversion inv_red_expr_spec_to_boolean with (forall S C a1 oo, red_expr S C (spec_to_boolean a1) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_to_number with (forall S C a1 oo, red_expr S C (spec_to_number a1) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_to_number_1 with (forall S C a1 oo, red_expr S C (spec_to_number_1 a1) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_to_integer with (forall S C a1 oo, red_expr S C (spec_to_integer a1) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_to_integer_1 with (forall S C a1 oo, red_expr S C (spec_to_integer_1 a1) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_to_string with (forall S C a1 oo, red_expr S C (spec_to_string a1) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_to_string_1 with (forall S C a1 oo, red_expr S C (spec_to_string_1 a1) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_to_object with (forall S C a1 oo, red_expr S C (spec_to_object a1) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_check_object_coercible with (forall S C a1 oo, red_expr S C (spec_check_object_coercible a1) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_eq with (forall S C a1 a2 oo, red_expr S C (spec_eq a1 a2) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_eq0 with (forall S C a1 a2 oo, red_expr S C (spec_eq0 a1 a2) oo) Sort Prop.
Derive Inversion inv_red_expr_spec_eq1 with (forall S C a1 a2 oo, red_expr S C (spec_eq1 a1 a2) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_eq2 with (forall S C a1 a2 a3 oo, red_expr S C (spec_eq2 a1 a2 a3) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_object_get with (forall S C a1 a2 oo, red_expr S C (spec_object_get a1 a2) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_object_get_1 with (forall S C a1 a2 a3 a4 oo, red_expr S C (spec_object_get_1 a1 a2 a3 a4) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_object_get_2 with (forall S C a1 a2 oo, red_expr S C (spec_object_get_2 a1 a2) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_object_get_3 with (forall S C a1 a2 oo, red_expr S C (spec_object_get_3 a1 a2) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_object_can_put with (forall S C a1 a2 oo, red_expr S C (spec_object_can_put a1 a2) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_object_can_put_1 with (forall S C a1 a2 a3 oo, red_expr S C (spec_object_can_put_1 a1 a2 a3) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_object_can_put_2 with (forall S C a1 a2 a3 oo, red_expr S C (spec_object_can_put_2 a1 a2 a3) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_object_can_put_4 with (forall S C a1 a2 a3 oo, red_expr S C (spec_object_can_put_4 a1 a2 a3) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_object_can_put_5 with (forall S C a1 a2 oo, red_expr S C (spec_object_can_put_5 a1 a2) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_object_can_put_6 with (forall S C a1 a2 oo, red_expr S C (spec_object_can_put_6 a1 a2) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_object_put with (forall S C a1 a2 a3 a4 oo, red_expr S C (spec_object_put a1 a2 a3 a4) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_object_put_1 with (forall S C a1 a2 a3 a4 a5 a6 oo, red_expr S C (spec_object_put_1 a1 a2 a3 a4 a5 a6) oo) Sort Prop.