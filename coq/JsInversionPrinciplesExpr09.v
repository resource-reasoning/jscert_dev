Set Implicit Arguments.
Require Import JsPrettyInterm JsPrettyRules.

(**************************************************************)
(** ** Inversion principles for expressions, Part 09          *)

Derive Inversion inv_red_expr_spec_env_record_delete_binding_1 with (forall S C a1 a2 a3 oo, red_expr S C (spec_env_record_delete_binding_1 a1 a2 a3) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_env_record_create_set_mutable_binding with (forall S C a1 a2 a3 a4 a5 oo, red_expr S C (spec_env_record_create_set_mutable_binding a1 a2 a3 a4 a5) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_env_record_create_set_mutable_binding_1 with (forall S C a1 a2 a3 a4 a5 oo, red_expr S C (spec_env_record_create_set_mutable_binding_1 a1 a2 a3 a4 a5) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_env_record_implicit_this_value with (forall S C a1 oo, red_expr S C (spec_env_record_implicit_this_value a1) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_env_record_implicit_this_value_1 with (forall S C a1 a2 oo, red_expr S C (spec_env_record_implicit_this_value_1 a1 a2) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_from_descriptor with (forall S C a1 oo, red_expr S C (spec_from_descriptor a1) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_from_descriptor_1 with (forall S C a1 a2 oo, red_expr S C (spec_from_descriptor_1 a1 a2) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_from_descriptor_2 with (forall S C a1 a2 a3 oo, red_expr S C (spec_from_descriptor_2 a1 a2 a3) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_from_descriptor_3 with (forall S C a1 a2 a3 oo, red_expr S C (spec_from_descriptor_3 a1 a2 a3) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_from_descriptor_4 with (forall S C a1 a2 a3 oo, red_expr S C (spec_from_descriptor_4 a1 a2 a3) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_from_descriptor_5 with (forall S C a1 a2 a3 oo, red_expr S C (spec_from_descriptor_5 a1 a2 a3) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_from_descriptor_6 with (forall S C a1 a2 oo, red_expr S C (spec_from_descriptor_6 a1 a2) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_entering_eval_code with (forall S C a1 a2 a3 oo, red_expr S C (spec_entering_eval_code a1 a2 a3) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_entering_eval_code_1 with (forall S C a1 a2 a3 oo, red_expr S C (spec_entering_eval_code_1 a1 a2 a3) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_entering_eval_code_2 with (forall S C a1 a2 oo, red_expr S C (spec_entering_eval_code_2 a1 a2) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_call_global_eval with (forall S C a1 a2 oo, red_expr S C (spec_call_global_eval a1 a2) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_call_global_eval_1 with (forall S C a1 a2 oo, red_expr S C (spec_call_global_eval_1 a1 a2) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_call_global_eval_2 with (forall S C a1 oo, red_expr S C (spec_call_global_eval_2 a1) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_call_global_eval_3 with (forall S C a1 oo, red_expr S C (spec_call_global_eval_3 a1) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_entering_func_code with (forall S C a1 a2 a3 a4 oo, red_expr S C (spec_entering_func_code a1 a2 a3 a4) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_entering_func_code_1 with (forall S C a1 a2 a3 a4 a5 a6 oo, red_expr S C (spec_entering_func_code_1 a1 a2 a3 a4 a5 a6) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_entering_func_code_2 with (forall S C a1 a2 a3 a4 a5 oo, red_expr S C (spec_entering_func_code_2 a1 a2 a3 a4 a5) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_entering_func_code_3 with (forall S C a1 a2 a3 a4 a5 a6 oo, red_expr S C (spec_entering_func_code_3 a1 a2 a3 a4 a5 a6) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_entering_func_code_4 with (forall S C a1 a2 oo, red_expr S C (spec_entering_func_code_4 a1 a2) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_binding_inst_formal_params with (forall S C a1 a2 a3 a4 oo, red_expr S C (spec_binding_inst_formal_params a1 a2 a3 a4) oo) Sort Prop. 