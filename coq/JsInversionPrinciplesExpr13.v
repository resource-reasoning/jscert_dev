Set Implicit Arguments.
Require Import JsPrettyInterm JsPrettyRules.

(**************************************************************)
(** ** Inversion principles for expressions, Part 13          *)

(* Derive Inversion inv_red_expr_spec_creating_function_object_proto_1 with (forall S C a1 a2 oo, red_expr S C (spec_creating_function_object_proto_1 a1 a2) oo) Sort Prop. *)
(* Derive Inversion inv_red_expr_spec_creating_function_object_proto_2 with (forall S C a1 a2 a3 oo, red_expr S C (spec_creating_function_object_proto_2 a1 a2 a3) oo) Sort Prop. *)
Derive Inversion inv_red_expr_spec_creating_function_object with (forall S C a1 a2 a3 a4 oo, red_expr S C (spec_creating_function_object a1 a2 a3 a4) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_creating_function_object_1 with (forall S C a1 a2 a3 oo, red_expr S C (spec_creating_function_object_1 a1 a2 a3) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_creating_function_object_2 with (forall S C a1 a2 a3 oo, red_expr S C (spec_creating_function_object_2 a1 a2 a3) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_creating_function_object_3 with (forall S C a1 a2 oo, red_expr S C (spec_creating_function_object_3 a1 a2) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_creating_function_object_4 with (forall S C a1 a2 oo, red_expr S C (spec_creating_function_object_4 a1 a2) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_function_proto_apply with (forall S C a1 a2 a3 oo, red_expr S C (spec_function_proto_apply a1 a2 a3) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_function_proto_apply_1 with (forall S C a1 a2 a3 a4 oo, red_expr S C (spec_function_proto_apply_1 a1 a2 a3 a4) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_function_proto_apply_2 with (forall S C a1 a2 a3 a4 oo, red_expr S C (spec_function_proto_apply_2 a1 a2 a3 a4) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_function_proto_apply_3 with (forall S C a1 a2 a3 oo, red_expr S C (spec_function_proto_apply_3 a1 a2 a3) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_function_proto_bind_1 with (forall S C a1 a2 a3 oo, red_expr S C (spec_function_proto_bind_1 a1 a2 a3) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_function_proto_bind_2 with (forall S C a1 a2 a3 oo, red_expr S C (spec_function_proto_bind_2 a1 a2 a3) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_function_proto_bind_3 with (forall S C a1 a2 oo, red_expr S C (spec_function_proto_bind_3 a1 a2) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_function_proto_bind_4 with (forall S C a1 a2 oo, red_expr S C (spec_function_proto_bind_4 a1 a2) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_function_proto_bind_5 with (forall S C a1 oo, red_expr S C (spec_function_proto_bind_5 a1) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_function_proto_bind_6 with (forall S C a1 a2 oo, red_expr S C (spec_function_proto_bind_6 a1 a2) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_function_proto_bind_7 with (forall S C a1 a2 oo, red_expr S C (spec_function_proto_bind_7 a1 a2) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_create_new_function_in with (forall S C a1 a2 a3 oo, red_expr S C (spec_create_new_function_in a1 a2 a3) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_call with (forall S C a1 a2 a3 oo, red_expr S C (spec_call a1 a2 a3) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_call_1 with (forall S C a1 a2 a3 a4 oo, red_expr S C (spec_call_1 a1 a2 a3 a4) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_call_prealloc with (forall S C a1 a2 a3 oo, red_expr S C (spec_call_prealloc a1 a2 a3) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_call_default with (forall S C a1 a2 a3 oo, red_expr S C (spec_call_default a1 a2 a3) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_call_default_1 with (forall S C a1 oo, red_expr S C (spec_call_default_1 a1) oo) Sort Prop. 
Derive Inversion inv_red_expr_spec_call_default_2 with (forall S C a1 oo, red_expr S C (spec_call_default_2 a1) oo) Sort Prop. 