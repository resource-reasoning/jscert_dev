Set Implicit Arguments.
Require Import JsPrettyInterm JsPrettyRules.

(**************************************************************)
(** ** Inversion principles for expressions, Part 11          *)

Derive Inversion inv_red_expr_spec_binding_inst_7 with (forall S C a1 a2 a3 a4 oo, red_expr S C (spec_binding_inst_7 a1 a2 a3 a4) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_binding_inst_8 with (forall S C a1 a2 a3 oo, red_expr S C (spec_binding_inst_8 a1 a2 a3) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_make_arg_getter with (forall S C a1 a2 oo, red_expr S C (spec_make_arg_getter a1 a2) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_make_arg_setter with (forall S C a1 a2 oo, red_expr S C (spec_make_arg_setter a1 a2) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_args_obj_get_1 with (forall S C a1 a2 a3 a4 a5 oo, red_expr S C (spec_args_obj_get_1 a1 a2 a3 a4 a5) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_args_obj_define_own_prop_1 with (forall S C a1 a2 a3 a4 a5 a6 oo, red_expr S C (spec_args_obj_define_own_prop_1 a1 a2 a3 a4 a5 a6) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_args_obj_define_own_prop_2 with (forall S C a1 a2 a3 a4 a5 a6 a7 oo, red_expr S C (spec_args_obj_define_own_prop_2 a1 a2 a3 a4 a5 a6 a7) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_args_obj_define_own_prop_3 with (forall S C a1 a2 a3 a4 a5 a6 oo, red_expr S C (spec_args_obj_define_own_prop_3 a1 a2 a3 a4 a5 a6) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_args_obj_define_own_prop_4 with (forall S C a1 a2 a3 a4 a5 oo, red_expr S C (spec_args_obj_define_own_prop_4 a1 a2 a3 a4 a5) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_args_obj_define_own_prop_5 with (forall S C a1 oo, red_expr S C (spec_args_obj_define_own_prop_5 a1) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_args_obj_define_own_prop_6 with (forall S C oo, red_expr S C spec_args_obj_define_own_prop_6 oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_args_obj_delete_1 with (forall S C a1 a2 a3 a4 a5 oo, red_expr S C (spec_args_obj_delete_1 a1 a2 a3 a4 a5) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_args_obj_delete_2 with (forall S C a1 a2 a3 a4 a5 a6 oo, red_expr S C (spec_args_obj_delete_2 a1 a2 a3 a4 a5 a6) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_args_obj_delete_3 with (forall S C a1 oo, red_expr S C (spec_args_obj_delete_3 a1) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_args_obj_delete_4 with (forall S C a1 oo, red_expr S C (spec_args_obj_delete_4 a1) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_arguments_object_map with (forall S C a1 a2 a3 a4 a5 oo, red_expr S C (spec_arguments_object_map a1 a2 a3 a4 a5) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_arguments_object_map_1 with (forall S C a1 a2 a3 a4 a5 a6 oo, red_expr S C (spec_arguments_object_map_1 a1 a2 a3 a4 a5 a6) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_arguments_object_map_2 with (forall S C a1 a2 a3 a4 a5 a6 a7 a8 oo, red_expr S C (spec_arguments_object_map_2 a1 a2 a3 a4 a5 a6 a7 a8) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_arguments_object_map_3 with (forall S C a1 a2 a3 a4 a5 a6 a7 a8 a9 oo, red_expr S C (spec_arguments_object_map_3 a1 a2 a3 a4 a5 a6 a7 a8 a9) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_arguments_object_map_4 with (forall S C a1 a2 a3 a4 a5 a6 a7 a8 a9 oo, red_expr S C (spec_arguments_object_map_4 a1 a2 a3 a4 a5 a6 a7 a8 a9) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_arguments_object_map_5 with (forall S C a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 oo, red_expr S C (spec_arguments_object_map_5 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_arguments_object_map_6 with (forall S C a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 oo, red_expr S C (spec_arguments_object_map_6 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_arguments_object_map_7 with (forall S C a1 a2 a3 a4 a5 a6 a7 a8 a9 oo, red_expr S C (spec_arguments_object_map_7 a1 a2 a3 a4 a5 a6 a7 a8 a9) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_arguments_object_map_8 with (forall S C a1 a2 a3 oo, red_expr S C (spec_arguments_object_map_8 a1 a2 a3) oo) Sort Prop.  
Derive Inversion inv_red_expr_spec_create_arguments_object with (forall S C a1 a2 a3 a4 a5 oo, red_expr S C (spec_create_arguments_object a1 a2 a3 a4 a5) oo) Sort Prop. 