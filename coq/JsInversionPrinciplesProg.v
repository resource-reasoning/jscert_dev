Set Implicit Arguments.
Require Import Shared.
Require Import JsSyntax JsSyntaxAux JsCommon JsCommonAux JsPreliminary.
Require Import JsPrettyInterm JsPrettyRules.

(**************************************************************)
(** ** Inversion principles for programs                      *)

Derive Inversion inv_red_prog_intro      with (forall S C str els oo, red_prog S C (prog_intro str els) oo) Sort Prop.
Derive Inversion inv_red_prog_javascript with (forall S C o1  p   oo, red_prog S C (javascript_1 o1 p)  oo) Sort Prop.
Derive Inversion inv_red_prog_prog_1     with (forall S C o1  el  oo, red_prog S C (prog_1 o1 el)       oo) Sort Prop.
Derive Inversion inv_red_prog_prog_2     with (forall S C o1  rv  oo, red_prog S C (prog_2 rv o1)       oo) Sort Prop.