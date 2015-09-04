Set Implicit Arguments.
Require Import Shared.
Require Import JsSyntax JsSyntaxAux JsCommon JsCommonAux JsPreliminary.
Require Import JsPrettyInterm JsPrettyRules.

(**************************************************************)
(** ** Inversion principles for expressions                   *)

Derive Inversion inv_red_stat_expr with (forall S C a1 oo, red_stat S C (stat_expr a1) oo) Sort Prop.
Derive Inversion inv_red_stat_label with (forall S C a1 a2 oo, red_stat S C (stat_label a1 a2) oo) Sort Prop.
Derive Inversion inv_red_stat_block with (forall S C a1 oo, red_stat S C (stat_block a1) oo) Sort Prop.
Derive Inversion inv_red_stat_var_decl with (forall S C a1 oo, red_stat S C (stat_var_decl a1) oo) Sort Prop.
Derive Inversion inv_red_stat_if with (forall S C a1 a2 a3 oo, red_stat S C (stat_if a1 a2 a3) oo) Sort Prop.
Derive Inversion inv_red_stat_do_while with (forall S C a1 a2 a3 oo, red_stat S C (stat_do_while a1 a2 a3) oo) Sort Prop.
Derive Inversion inv_red_stat_with with (forall S C a1 a2 oo, red_stat S C (stat_with a1 a2) oo) Sort Prop.
Derive Inversion inv_red_stat_throw with (forall S C a1 oo, red_stat S C (stat_throw a1) oo) Sort Prop.
Derive Inversion inv_red_stat_return with (forall S C a1 oo, red_stat S C (stat_return a1) oo) Sort Prop.
Derive Inversion inv_red_stat_break with (forall S C a1 oo, red_stat S C (stat_break a1) oo) Sort Prop.
Derive Inversion inv_red_stat_continue with (forall S C a1 oo, red_stat S C (stat_continue a1) oo) Sort Prop.
Derive Inversion inv_red_stat_try with (forall S C a1 a2 a3 oo, red_stat S C (stat_try a1 a2 a3) oo) Sort Prop.
Derive Inversion inv_red_stat_for with (forall S C a1 a2 a3 a4 a5 oo, red_stat S C (stat_for a1 a2 a3 a4 a5) oo) Sort Prop.
Derive Inversion inv_red_stat_for_var with (forall S C a1 a2 a3 a4 a5 oo, red_stat S C (stat_for_var a1 a2 a3 a4 a5) oo) Sort Prop.
Derive Inversion inv_red_stat_for_in with (forall S C a1 a2 a3 a4 oo, red_stat S C (stat_for_in a1 a2 a3 a4) oo) Sort Prop.
Derive Inversion inv_red_stat_for_in_var with (forall S C a1 a2 a3 a4 a5 oo, red_stat S C (stat_for_in_var a1 a2 a3 a4 a5) oo) Sort Prop.
Derive Inversion inv_red_stat_debugger with (forall S C oo, red_stat S C stat_debugger oo) Sort Prop.
Derive Inversion inv_red_stat_switch with (forall S C a1 a2 a3 oo, red_stat S C (stat_switch a1 a2 a3) oo) Sort Prop.
Derive Inversion inv_red_stat_stat_expr_1 with (forall S C a1 oo, red_stat S C (stat_expr_1 a1) oo) Sort Prop.
Derive Inversion inv_red_stat_stat_block_1 with (forall S C a1 a2 oo, red_stat S C (stat_block_1 a1 a2) oo) Sort Prop.
Derive Inversion inv_red_stat_stat_block_2 with (forall S C a1 a2 oo, red_stat S C (stat_block_2 a1 a2) oo) Sort Prop.
Derive Inversion inv_red_stat_stat_label_1 with (forall S C a1 a2 oo, red_stat S C (stat_label_1 a1 a2) oo) Sort Prop.
Derive Inversion inv_red_stat_stat_var_decl_1 with (forall S C a1 a2 oo, red_stat S C (stat_var_decl_1 a1 a2) oo) Sort Prop.
Derive Inversion inv_red_stat_stat_var_decl_item with (forall S C a1 oo, red_stat S C (stat_var_decl_item a1) oo) Sort Prop.
Derive Inversion inv_red_stat_stat_var_decl_item_1 with (forall S C a1 a2 a3 oo, red_stat S C (stat_var_decl_item_1 a1 a2 a3) oo) Sort Prop.
Derive Inversion inv_red_stat_stat_var_decl_item_2 with (forall S C a1 a2 a3 oo, red_stat S C (stat_var_decl_item_2 a1 a2 a3) oo) Sort Prop.
Derive Inversion inv_red_stat_stat_var_decl_item_3 with (forall S C a1 a2 oo, red_stat S C (stat_var_decl_item_3 a1 a2) oo) Sort Prop.
Derive Inversion inv_red_stat_stat_if_1 with (forall S C a1 a2 a3 oo, red_stat S C (stat_if_1 a1 a2 a3) oo) Sort Prop.
Derive Inversion inv_red_stat_stat_while_1 with (forall S C a1 a2 a3 a4 oo, red_stat S C (stat_while_1 a1 a2 a3 a4) oo) Sort Prop.
Derive Inversion inv_red_stat_stat_while_2 with (forall S C a1 a2 a3 a4 a5 oo, red_stat S C (stat_while_2 a1 a2 a3 a4 a5) oo) Sort Prop.
Derive Inversion inv_red_stat_stat_while_3 with (forall S C a1 a2 a3 a4 a5 oo, red_stat S C (stat_while_3 a1 a2 a3 a4 a5) oo) Sort Prop.
Derive Inversion inv_red_stat_stat_while_4 with (forall S C a1 a2 a3 a4 a5 oo, red_stat S C (stat_while_4 a1 a2 a3 a4 a5) oo) Sort Prop.
Derive Inversion inv_red_stat_stat_while_5 with (forall S C a1 a2 a3 a4 a5 oo, red_stat S C (stat_while_5 a1 a2 a3 a4 a5) oo) Sort Prop.
Derive Inversion inv_red_stat_stat_while_6 with (forall S C a1 a2 a3 a4 a5 oo, red_stat S C (stat_while_6 a1 a2 a3 a4 a5) oo) Sort Prop.
Derive Inversion inv_red_stat_stat_do_while_1 with (forall S C a1 a2 a3 a4 oo, red_stat S C (stat_do_while_1 a1 a2 a3 a4) oo) Sort Prop.
Derive Inversion inv_red_stat_stat_do_while_2 with (forall S C a1 a2 a3 a4 a5 oo, red_stat S C (stat_do_while_2 a1 a2 a3 a4 a5) oo) Sort Prop.
Derive Inversion inv_red_stat_stat_do_while_3 with (forall S C a1 a2 a3 a4 a5 oo, red_stat S C (stat_do_while_3 a1 a2 a3 a4 a5) oo) Sort Prop.
Derive Inversion inv_red_stat_stat_do_while_4 with (forall S C a1 a2 a3 a4 a5 oo, red_stat S C (stat_do_while_4 a1 a2 a3 a4 a5) oo) Sort Prop.
Derive Inversion inv_red_stat_stat_do_while_5 with (forall S C a1 a2 a3 a4 a5 oo, red_stat S C (stat_do_while_5 a1 a2 a3 a4 a5) oo) Sort Prop.
Derive Inversion inv_red_stat_stat_do_while_6 with (forall S C a1 a2 a3 a4 oo, red_stat S C (stat_do_while_6 a1 a2 a3 a4) oo) Sort Prop.
Derive Inversion inv_red_stat_stat_do_while_7 with (forall S C a1 a2 a3 a4 a5 oo, red_stat S C (stat_do_while_7 a1 a2 a3 a4 a5) oo) Sort Prop.
Derive Inversion inv_red_stat_stat_for_1 with (forall S C a1 a2 a3 a4 a5 oo, red_stat S C (stat_for_1 a1 a2 a3 a4 a5) oo) Sort Prop.
Derive Inversion inv_red_stat_stat_for_2 with (forall S C a1 a2 a3 a4 a5 oo, red_stat S C (stat_for_2 a1 a2 a3 a4 a5) oo) Sort Prop.
Derive Inversion inv_red_stat_stat_for_3 with (forall S C a1 a2 a3 a4 a5 a6 oo, red_stat S C (stat_for_3 a1 a2 a3 a4 a5 a6) oo) Sort Prop.
Derive Inversion inv_red_stat_stat_for_4 with (forall S C a1 a2 a3 a4 a5 oo, red_stat S C (stat_for_4 a1 a2 a3 a4 a5) oo) Sort Prop.
Derive Inversion inv_red_stat_stat_for_5 with (forall S C a1 a2 a3 a4 a5 a6 oo, red_stat S C (stat_for_5 a1 a2 a3 a4 a5 a6) oo) Sort Prop.
Derive Inversion inv_red_stat_stat_for_6 with (forall S C a1 a2 a3 a4 a5 a6 oo, red_stat S C (stat_for_6 a1 a2 a3 a4 a5 a6) oo) Sort Prop.
Derive Inversion inv_red_stat_stat_for_7 with (forall S C a1 a2 a3 a4 a5 a6 oo, red_stat S C (stat_for_7 a1 a2 a3 a4 a5 a6) oo) Sort Prop.
Derive Inversion inv_red_stat_stat_for_8 with (forall S C a1 a2 a3 a4 a5 oo, red_stat S C (stat_for_8 a1 a2 a3 a4 a5) oo) Sort Prop.
Derive Inversion inv_red_stat_stat_for_9 with (forall S C a1 a2 a3 a4 a5 a6 oo, red_stat S C (stat_for_9 a1 a2 a3 a4 a5 a6) oo) Sort Prop.
Derive Inversion inv_red_stat_stat_for_var_1 with (forall S C a1 a2 a3 a4 a5 oo, red_stat S C (stat_for_var_1 a1 a2 a3 a4 a5) oo) Sort Prop.
Derive Inversion inv_red_stat_stat_with_1 with (forall S C a1 a2 oo, red_stat S C (stat_with_1 a1 a2) oo) Sort Prop.
Derive Inversion inv_red_stat_stat_throw_1 with (forall S C a1 oo, red_stat S C (stat_throw_1 a1) oo) Sort Prop.
Derive Inversion inv_red_stat_stat_return_1 with (forall S C a1 oo, red_stat S C (stat_return_1 a1) oo) Sort Prop.
Derive Inversion inv_red_stat_stat_try_1 with (forall S C a1 a2 a3 oo, red_stat S C (stat_try_1 a1 a2 a3) oo) Sort Prop.
Derive Inversion inv_red_stat_stat_try_2 with (forall S C a1 a2 a3 a4 oo, red_stat S C (stat_try_2 a1 a2 a3 a4) oo) Sort Prop.
Derive Inversion inv_red_stat_stat_try_3 with (forall S C a1 a2 oo, red_stat S C (stat_try_3 a1 a2) oo) Sort Prop.
Derive Inversion inv_red_stat_stat_try_4 with (forall S C a1 a2 oo, red_stat S C (stat_try_4 a1 a2) oo) Sort Prop.
Derive Inversion inv_red_stat_stat_try_5 with (forall S C a1 a2 oo, red_stat S C (stat_try_5 a1 a2) oo) Sort Prop.
Derive Inversion inv_red_stat_stat_switch_1 with (forall S C a1 a2 a3 oo, red_stat S C (stat_switch_1 a1 a2 a3) oo) Sort Prop.
Derive Inversion inv_red_stat_stat_switch_2 with (forall S C a1 a2 oo, red_stat S C (stat_switch_2 a1 a2) oo) Sort Prop.
Derive Inversion inv_red_stat_stat_switch_nodefault_1 with (forall S C a1 a2 a3 oo, red_stat S C (stat_switch_nodefault_1 a1 a2 a3) oo) Sort Prop.
Derive Inversion inv_red_stat_stat_switch_nodefault_2 with (forall S C a1 a2 a3 a4 a5 oo, red_stat S C (stat_switch_nodefault_2 a1 a2 a3 a4 a5) oo) Sort Prop. 
Derive Inversion inv_red_stat_stat_switch_nodefault_3 with (forall S C a1 a2 a3 a4 a5 oo, red_stat S C (stat_switch_nodefault_3 a1 a2 a3 a4 a5) oo) Sort Prop.
Derive Inversion inv_red_stat_stat_switch_nodefault_4 with (forall S C a1 a2 oo, red_stat S C (stat_switch_nodefault_4 a1 a2) oo) Sort Prop.
Derive Inversion inv_red_stat_stat_switch_nodefault_5 with (forall S C a1 a2 oo, red_stat S C (stat_switch_nodefault_5 a1 a2) oo) Sort Prop.
Derive Inversion inv_red_stat_stat_switch_nodefault_6 with (forall S C a1 a2 a3 oo, red_stat S C (stat_switch_nodefault_6 a1 a2 a3) oo) Sort Prop.
Derive Inversion inv_red_stat_stat_switch_default_1 with (forall S C a1 a2 a3 a4 a5 oo, red_stat S C (stat_switch_default_1 a1 a2 a3 a4 a5) oo) Sort Prop.
Derive Inversion inv_red_stat_stat_switch_default_A_1 with (forall S C a1 a2 a3 a4 a5 a6 oo, red_stat S C (stat_switch_default_A_1 a1 a2 a3 a4 a5 a6) oo) Sort Prop.
Derive Inversion inv_red_stat_stat_switch_default_A_2 with (forall S C a1 a2 a3 a4 a5 a6 a7 oo, red_stat S C (stat_switch_default_A_2 a1 a2 a3 a4 a5 a6 a7) oo) Sort Prop.
Derive Inversion inv_red_stat_stat_switch_default_A_3 with (forall S C a1 a2 a3 a4 a5 a6 a7 oo, red_stat S C (stat_switch_default_A_3 a1 a2 a3 a4 a5 a6 a7) oo) Sort Prop. 
Derive Inversion inv_red_stat_stat_switch_default_A_4 with (forall S C a1 a2 a3 a4 a5 a6 oo, red_stat S C (stat_switch_default_A_4 a1 a2 a3 a4 a5 a6) oo) Sort Prop.
Derive Inversion inv_red_stat_stat_switch_default_A_5 with (forall S C a1 a2 a3 a4 a5 a6 oo, red_stat S C (stat_switch_default_A_5 a1 a2 a3 a4 a5 a6) oo) Sort Prop.
Derive Inversion inv_red_stat_stat_switch_default_B_1 with (forall S C a1 a2 a3 a4 oo, red_stat S C (stat_switch_default_B_1 a1 a2 a3 a4) oo) Sort Prop.
Derive Inversion inv_red_stat_stat_switch_default_B_2 with (forall S C a1 a2 a3 a4 a5 a6 oo, red_stat S C (stat_switch_default_B_2 a1 a2 a3 a4 a5 a6) oo) Sort Prop.
Derive Inversion inv_red_stat_stat_switch_default_B_3 with (forall S C a1 a2 a3 a4 a5 a6 oo, red_stat S C (stat_switch_default_B_3 a1 a2 a3 a4 a5 a6) oo) Sort Prop.
Derive Inversion inv_red_stat_stat_switch_default_B_4 with (forall S C a1 a2 a3 oo, red_stat S C (stat_switch_default_B_4 a1 a2 a3) oo) Sort Prop.
Derive Inversion inv_red_stat_stat_switch_default_5 with (forall S C a1 a2 a3 a4 oo, red_stat S C (stat_switch_default_5 a1 a2 a3 a4) oo) Sort Prop.
Derive Inversion inv_red_stat_stat_switch_default_6 with (forall S C a1 a2 oo, red_stat S C (stat_switch_default_6 a1 a2) oo) Sort Prop.
Derive Inversion inv_red_stat_stat_switch_default_7 with (forall S C a1 a2 oo, red_stat S C (stat_switch_default_7 a1 a2) oo) Sort Prop. 
Derive Inversion inv_red_stat_stat_switch_default_8 with (forall S C a1 a2 a3 oo, red_stat S C (stat_switch_default_8 a1 a2 a3) oo) Sort Prop.