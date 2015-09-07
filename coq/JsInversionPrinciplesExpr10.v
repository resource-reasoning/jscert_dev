Set Implicit Arguments.
Require Import JsPrettyInterm JsPrettyRules.

(**************************************************************)
(** ** Inversion principles for expressions, Part 10          *)

Derive Inversion inv_red_expr_spec_binding_inst_formal_params_1 with (forall S C a1 a2 a3 a4 a5 a6 a7 oo, red_expr S C (spec_binding_inst_formal_params_1 a1 a2 a3 a4 a5 a6 a7) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_binding_inst_formal_params_2 with (forall S C a1 a2 a3 a4 a5 a6 a7 oo, red_expr S C (spec_binding_inst_formal_params_2 a1 a2 a3 a4 a5 a6 a7) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_binding_inst_formal_params_3 with (forall S C a1 a2 a3 a4 a5 a6 oo, red_expr S C (spec_binding_inst_formal_params_3 a1 a2 a3 a4 a5 a6) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_binding_inst_formal_params_4 with (forall S C a1 a2 a3 a4 a5 oo, red_expr S C (spec_binding_inst_formal_params_4 a1 a2 a3 a4 a5) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_binding_inst_function_decls with (forall S C a1 a2 a3 a4 oo, red_expr S C (spec_binding_inst_function_decls a1 a2 a3 a4) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_binding_inst_function_decls_1 with (forall S C a1 a2 a3 a4 a5 a6 oo, red_expr S C (spec_binding_inst_function_decls_1 a1 a2 a3 a4 a5 a6) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_binding_inst_function_decls_2 with (forall S C a1 a2 a3 a4 a5 a6 a7 oo, red_expr S C (spec_binding_inst_function_decls_2 a1 a2 a3 a4 a5 a6 a7) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_binding_inst_function_decls_3 with (forall S C a1 a2 a3 a4 a5 a6 oo, red_expr S C (spec_binding_inst_function_decls_3 a1 a2 a3 a4 a5 a6) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_binding_inst_function_decls_3a with (forall S C a1 a2 a3 a4 a5 a6 oo, red_expr S C (spec_binding_inst_function_decls_3a a1 a2 a3 a4 a5 a6) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_binding_inst_function_decls_4 with (forall S C a1 a2 a3 a4 a5 a6 a7 oo, red_expr S C (spec_binding_inst_function_decls_4 a1 a2 a3 a4 a5 a6 a7) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_binding_inst_function_decls_5 with (forall S C a1 a2 a3 a4 a5 a6 oo, red_expr S C (spec_binding_inst_function_decls_5 a1 a2 a3 a4 a5 a6) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_binding_inst_function_decls_6 with (forall S C a1 a2 a3 a4 a5 oo, red_expr S C (spec_binding_inst_function_decls_6 a1 a2 a3 a4 a5) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_binding_inst_arg_obj with (forall S C a1 a2 a3 a4 a5 oo, red_expr S C (spec_binding_inst_arg_obj a1 a2 a3 a4 a5) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_binding_inst_arg_obj_1 with (forall S C a1 a2 a3 oo, red_expr S C (spec_binding_inst_arg_obj_1 a1 a2 a3) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_binding_inst_arg_obj_2 with (forall S C a1 a2 a3 oo, red_expr S C (spec_binding_inst_arg_obj_2 a1 a2 a3) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_binding_inst_var_decls with (forall S C a1 a2 a3 a4 oo, red_expr S C (spec_binding_inst_var_decls a1 a2 a3 a4) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_binding_inst_var_decls_1 with (forall S C a1 a2 a3 a4 a5 a6 oo, red_expr S C (spec_binding_inst_var_decls_1 a1 a2 a3 a4 a5 a6) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_binding_inst_var_decls_2 with (forall S C a1 a2 a3 a4 a5 oo, red_expr S C (spec_binding_inst_var_decls_2 a1 a2 a3 a4 a5) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_binding_inst with (forall S C a1 a2 a3 a4 oo, red_expr S C (spec_binding_inst a1 a2 a3 a4) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_binding_inst_1 with (forall S C a1 a2 a3 a4 a5 oo, red_expr S C (spec_binding_inst_1 a1 a2 a3 a4 a5) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_binding_inst_2 with (forall S C a1 a2 a3 a4 a5 a6 a7 oo, red_expr S C (spec_binding_inst_2 a1 a2 a3 a4 a5 a6 a7) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_binding_inst_3 with (forall S C a1 a2 a3 a4 a5 a6 oo, red_expr S C (spec_binding_inst_3 a1 a2 a3 a4 a5 a6) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_binding_inst_4 with (forall S C a1 a2 a3 a4 a5 a6 a7 a8 oo, red_expr S C (spec_binding_inst_4 a1 a2 a3 a4 a5 a6 a7 a8) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_binding_inst_5 with (forall S C a1 a2 a3 a4 a5 a6 a7 oo, red_expr S C (spec_binding_inst_5 a1 a2 a3 a4 a5 a6 a7) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_binding_inst_6 with (forall S C a1 a2 a3 a4 a5 a6 a7 a8 oo, red_expr S C (spec_binding_inst_6 a1 a2 a3 a4 a5 a6 a7 a8) oo) Sort Prop. 