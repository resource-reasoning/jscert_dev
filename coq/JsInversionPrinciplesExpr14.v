Set Implicit Arguments.
Require Import JsPrettyInterm JsPrettyRules.

(**************************************************************)
(** ** Inversion principles for expressions, Part 14          *)

Derive Inversion inv_red_expr_spec_call_default_3 with (forall S C a1 oo, red_expr S C (spec_call_default_3 a1) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_construct with (forall S C a1 a2 oo, red_expr S C (spec_construct a1 a2) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_construct_1 with (forall S C a1 a2 a3 oo, red_expr S C (spec_construct_1 a1 a2 a3) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_construct_prealloc with (forall S C a1 a2 oo, red_expr S C (spec_construct_prealloc a1 a2) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_construct_default with (forall S C a1 a2 oo, red_expr S C (spec_construct_default a1 a2) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_construct_default_1 with (forall S C a1 a2 a3 oo, red_expr S C (spec_construct_default_1 a1 a2 a3) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_construct_default_2 with (forall S C a1 a2 oo, red_expr S C (spec_construct_default_2 a1 a2) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_construct_1_after_bind with (forall S C a1 a2 a3 oo, red_expr S C (spec_construct_1_after_bind a1 a2 a3) oo) Sort Prop. 
(* Derive Inversion inv_red_expr_spec_construct_bool_1 with (forall S C a1 oo, red_expr S C (spec_construct_bool_1 a1) oo) Sort Prop. *)
(* Derive Inversion inv_red_expr_spec_construct_number_1 with (forall S C a1 oo, red_expr S C (spec_construct_number_1 a1) oo) Sort Prop. *) 
Derive Inversion inv_red_expr_spec_call_global_is_nan_1 with (forall S C a1 oo, red_expr S C (spec_call_global_is_nan_1 a1) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_call_global_is_finite_1 with (forall S C a1 oo, red_expr S C (spec_call_global_is_finite_1 a1) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_call_object_call_1 with (forall S C a1 a2 oo, red_expr S C (spec_call_object_call_1 a1 a2) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_call_object_new_1 with (forall S C a1 oo, red_expr S C (spec_call_object_new_1 a1) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_call_object_get_proto_of_1 with (forall S C a1 oo, red_expr S C (spec_call_object_get_proto_of_1 a1) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_call_object_is_extensible_1 with (forall S C a1 oo, red_expr S C (spec_call_object_is_extensible_1 a1) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_call_object_define_props_1 with (forall S C a1 a2 oo, red_expr S C (spec_call_object_define_props_1 a1 a2) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_call_object_define_props_2 with (forall S C a1 a2 oo, red_expr S C (spec_call_object_define_props_2 a1 a2) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_call_object_define_props_3 with (forall S C a1 a2 a3 a4 oo, red_expr S C (spec_call_object_define_props_3 a1 a2 a3 a4) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_call_object_define_props_4 with (forall S C a1 a2 a3 a4 a5 a6 oo, red_expr S C (spec_call_object_define_props_4 a1 a2 a3 a4 a5 a6) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_call_object_define_props_5 with (forall S C a1 a2 a3 a4 a5 a6 oo, red_expr S C (spec_call_object_define_props_5 a1 a2 a3 a4 a5 a6) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_call_object_define_props_6 with (forall S C a1 a2 oo, red_expr S C (spec_call_object_define_props_6 a1 a2) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_call_object_define_props_7 with (forall S C a1 a2 a3 oo, red_expr S C (spec_call_object_define_props_7 a1 a2 a3) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_call_object_create_1 with (forall S C a1 a2 oo, red_expr S C (spec_call_object_create_1 a1 a2) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_call_object_create_2 with (forall S C a1 a2 a3 oo, red_expr S C (spec_call_object_create_2 a1 a2 a3) oo) Sort Prop. 