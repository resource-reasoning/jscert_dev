Set Implicit Arguments.
Require Import JsPrettyInterm JsPrettyRules.

(**************************************************************)
(** ** Inversion principles for expressions, Part 08          *)

Derive Inversion inv_red_expr_spec_object_define_own_prop_array_3l_ii_2 with (forall S C a1 a2 a3 a4 a5 a6 a7 oo, red_expr S C (spec_object_define_own_prop_array_3l_ii_2 a1 a2 a3 a4 a5 a6 a7) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_object_define_own_prop_array_3l_iii_1 with (forall S C a1 a2 a3 a4 a5 oo, red_expr S C (spec_object_define_own_prop_array_3l_iii_1 a1 a2 a3 a4 a5) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_object_define_own_prop_array_3l_iii_2 with (forall S C a1 a2 a3 a4 oo, red_expr S C (spec_object_define_own_prop_array_3l_iii_2 a1 a2 a3 a4) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_object_define_own_prop_array_3l_iii_3 with (forall S C a1 a2 a3 oo, red_expr S C (spec_object_define_own_prop_array_3l_iii_3 a1 a2 a3) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_object_define_own_prop_array_3l_iii_4 with (forall S C a1 a2 a3 oo, red_expr S C (spec_object_define_own_prop_array_3l_iii_4 a1 a2 a3) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_object_define_own_prop_array_3m_n with (forall S C a1 a2 oo, red_expr S C (spec_object_define_own_prop_array_3m_n a1 a2) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_prim_value_get with (forall S C a1 a2 oo, red_expr S C (spec_prim_value_get a1 a2) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_prim_value_get_1 with (forall S C a1 a2 a3 oo, red_expr S C (spec_prim_value_get_1 a1 a2 a3) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_prim_value_put with (forall S C a1 a2 a3 a4 oo, red_expr S C (spec_prim_value_put a1 a2 a3 a4) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_prim_value_put_1 with (forall S C a1 a2 a3 a4 a5 oo, red_expr S C (spec_prim_value_put_1 a1 a2 a3 a4 a5) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_put_value with (forall S C a1 a2 oo, red_expr S C (spec_put_value a1 a2) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_env_record_has_binding with (forall S C a1 a2 oo, red_expr S C (spec_env_record_has_binding a1 a2) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_env_record_has_binding_1 with (forall S C a1 a2 a3 oo, red_expr S C (spec_env_record_has_binding_1 a1 a2 a3) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_env_record_get_binding_value with (forall S C a1 a2 a3 oo, red_expr S C (spec_env_record_get_binding_value a1 a2 a3) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_env_record_get_binding_value_1 with (forall S C a1 a2 a3 a4 oo, red_expr S C (spec_env_record_get_binding_value_1 a1 a2 a3 a4) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_env_record_get_binding_value_2 with (forall S C a1 a2 a3 a4 oo, red_expr S C (spec_env_record_get_binding_value_2 a1 a2 a3 a4) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_env_record_create_immutable_binding with (forall S C a1 a2 oo, red_expr S C (spec_env_record_create_immutable_binding a1 a2) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_env_record_initialize_immutable_binding with (forall S C a1 a2 a3 oo, red_expr S C (spec_env_record_initialize_immutable_binding a1 a2 a3) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_env_record_create_mutable_binding with (forall S C a1 a2 a3 oo, red_expr S C (spec_env_record_create_mutable_binding a1 a2 a3) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_env_record_create_mutable_binding_1 with (forall S C a1 a2 a3 a4 oo, red_expr S C (spec_env_record_create_mutable_binding_1 a1 a2 a3 a4) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_env_record_create_mutable_binding_2 with (forall S C a1 a2 a3 a4 a5 oo, red_expr S C (spec_env_record_create_mutable_binding_2 a1 a2 a3 a4 a5) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_env_record_create_mutable_binding_3 with (forall S C a1 oo, red_expr S C (spec_env_record_create_mutable_binding_3 a1) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_env_record_set_mutable_binding with (forall S C a1 a2 a3 a4 oo, red_expr S C (spec_env_record_set_mutable_binding a1 a2 a3 a4) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_env_record_set_mutable_binding_1 with (forall S C a1 a2 a3 a4 a5 oo, red_expr S C (spec_env_record_set_mutable_binding_1 a1 a2 a3 a4 a5) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_env_record_delete_binding with (forall S C a1 a2 oo, red_expr S C (spec_env_record_delete_binding a1 a2) oo) Sort Prop.