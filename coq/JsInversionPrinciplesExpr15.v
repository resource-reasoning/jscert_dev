Set Implicit Arguments.
Require Import JsPrettyInterm JsPrettyRules.

(**************************************************************)
(** ** Inversion principles for expressions, Part 15          *)

Derive Inversion inv_red_expr_spec_call_object_create_3 with (forall S C a1 a2 oo, red_expr S C (spec_call_object_create_3 a1 a2) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_call_object_seal_1 with (forall S C a1 oo, red_expr S C (spec_call_object_seal_1 a1) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_call_object_seal_2 with (forall S C a1 a2 oo, red_expr S C (spec_call_object_seal_2 a1 a2) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_call_object_seal_3 with (forall S C a1 a2 a3 a4 oo, red_expr S C (spec_call_object_seal_3 a1 a2 a3 a4) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_call_object_seal_4 with (forall S C a1 a2 a3 oo, red_expr S C (spec_call_object_seal_4 a1 a2 a3) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_call_object_is_sealed_1 with (forall S C a1 oo, red_expr S C (spec_call_object_is_sealed_1 a1) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_call_object_is_sealed_2 with (forall S C a1 a2 oo, red_expr S C (spec_call_object_is_sealed_2 a1 a2) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_call_object_is_sealed_3 with (forall S C a1 a2 a3 oo, red_expr S C (spec_call_object_is_sealed_3 a1 a2 a3) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_call_object_freeze_1 with (forall S C a1 oo, red_expr S C (spec_call_object_freeze_1 a1) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_call_object_freeze_2 with (forall S C a1 a2 oo, red_expr S C (spec_call_object_freeze_2 a1 a2) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_call_object_freeze_3 with (forall S C a1 a2 a3 a4 oo, red_expr S C (spec_call_object_freeze_3 a1 a2 a3 a4) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_call_object_freeze_4 with (forall S C a1 a2 a3 a4 oo, red_expr S C (spec_call_object_freeze_4 a1 a2 a3 a4) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_call_object_freeze_5 with (forall S C a1 a2 a3 oo, red_expr S C (spec_call_object_freeze_5 a1 a2 a3) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_call_object_is_frozen_1 with (forall S C a1 oo, red_expr S C (spec_call_object_is_frozen_1 a1) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_call_object_is_frozen_2 with (forall S C a1 a2 oo, red_expr S C (spec_call_object_is_frozen_2 a1 a2) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_call_object_is_frozen_3 with (forall S C a1 a2 a3 oo, red_expr S C (spec_call_object_is_frozen_3 a1 a2 a3) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_call_object_is_frozen_4 with (forall S C a1 a2 a3 oo, red_expr S C (spec_call_object_is_frozen_4 a1 a2 a3) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_call_object_is_frozen_5 with (forall S C a1 a2 a3 oo, red_expr S C (spec_call_object_is_frozen_5 a1 a2 a3) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_call_object_prevent_extensions_1 with (forall S C a1 oo, red_expr S C (spec_call_object_prevent_extensions_1 a1) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_call_object_define_prop_1 with (forall S C a1 a2 a3 oo, red_expr S C (spec_call_object_define_prop_1 a1 a2 a3) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_call_object_define_prop_2 with (forall S C a1 a2 a3 oo, red_expr S C (spec_call_object_define_prop_2 a1 a2 a3) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_call_object_define_prop_3 with (forall S C a1 a2 a3 oo, red_expr S C (spec_call_object_define_prop_3 a1 a2 a3) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_call_object_define_prop_4 with (forall S C a1 a2 oo, red_expr S C (spec_call_object_define_prop_4 a1 a2) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_call_object_get_own_prop_descriptor_1 with (forall S C a1 a2 oo, red_expr S C (spec_call_object_get_own_prop_descriptor_1 a1 a2) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_call_object_get_own_prop_descriptor_2 with (forall S C a1 a2 oo, red_expr S C (spec_call_object_get_own_prop_descriptor_2 a1 a2) oo) Sort Prop. 