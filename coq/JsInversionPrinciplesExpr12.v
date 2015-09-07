Set Implicit Arguments.
Require Import JsPrettyInterm JsPrettyRules.

(**************************************************************)
(** ** Inversion principles for expressions, Part 12          *)

Derive Inversion inv_red_expr_spec_create_arguments_object_1 with (forall S C a1 a2 a3 a4 a5 a6 a7 oo, red_expr S C (spec_create_arguments_object_1 a1 a2 a3 a4 a5 a6 a7) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_create_arguments_object_2 with (forall S C a1 a2 a3 a4 oo, red_expr S C (spec_create_arguments_object_2 a1 a2 a3 a4) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_create_arguments_object_3 with (forall S C a1 a2 a3 a4 oo, red_expr S C (spec_create_arguments_object_3 a1 a2 a3 a4) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_create_arguments_object_4 with (forall S C a1 a2 oo, red_expr S C (spec_create_arguments_object_4 a1 a2) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_object_has_instance with (forall S C a1 a2 oo, red_expr S C (spec_object_has_instance a1 a2) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_object_has_instance_1 with (forall S C a1 a2 a3 oo, red_expr S C (spec_object_has_instance_1 a1 a2 a3) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_function_has_instance_1 with (forall S C a1 a2 oo, red_expr S C (spec_function_has_instance_1 a1 a2) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_function_has_instance_2 with (forall S C a1 a2 oo, red_expr S C (spec_function_has_instance_2 a1 a2) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_function_has_instance_3 with (forall S C a1 a2 oo, red_expr S C (spec_function_has_instance_3 a1 a2) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_function_has_instance_after_bind_1 with (forall S C a1 a2 oo, red_expr S C (spec_function_has_instance_after_bind_1 a1 a2) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_function_has_instance_after_bind_2 with (forall S C a1 a2 oo, red_expr S C (spec_function_has_instance_after_bind_2 a1 a2) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_function_get_1 with (forall S C a1 a2 a3 oo, red_expr S C (spec_function_get_1 a1 a2 a3) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_error with (forall S C a1 oo, red_expr S C (spec_error a1) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_error_1 with (forall S C a1 oo, red_expr S C (spec_error_1 a1) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_error_or_cst with (forall S C a1 a2 a3 oo, red_expr S C (spec_error_or_cst a1 a2 a3) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_error_or_void with (forall S C a1 a2 oo, red_expr S C (spec_error_or_void a1 a2) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_init_throw_type_error with (forall S C oo, red_expr S C spec_init_throw_type_error oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_init_throw_type_error_1 with (forall S C a1 oo, red_expr S C (spec_init_throw_type_error_1 a1) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_build_error with (forall S C a1 a2 oo, red_expr S C (spec_build_error a1 a2) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_build_error_1 with (forall S C a1 a2 oo, red_expr S C (spec_build_error_1 a1 a2) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_build_error_2 with (forall S C a1 a2 oo, red_expr S C (spec_build_error_2 a1 a2) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_new_object with (forall S C a1 oo, red_expr S C (spec_new_object a1) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_new_object_1 with (forall S C a1 a2 oo, red_expr S C (spec_new_object_1 a1 a2) oo) Sort Prop. 
(* Derive Inversion inv_red_expr_spec_prim_new_object with (forall S C a1 oo, red_expr S C (spec_prim_new_object a1) oo) Sort Prop. *)
Derive Inversion inv_red_expr_spec_creating_function_object_proto with (forall S C a1 oo, red_expr S C (spec_creating_function_object_proto a1) oo) Sort Prop.