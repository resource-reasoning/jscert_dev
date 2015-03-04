(* Monkey-patch LibTactics to use tracejs logging commands *)
Require Export LibTactics.
Require Export Tracejs.

(* We cannot redefine the apply tactic -- avoid using it to apply red_ rules if tracing required
 * (the required grammar is not representable using the Tactic Notation command) *)

Tactic Notation "apply" "~" constr(H) :=
  tracejs H; tracejs_code; apply~ H.

Tactic Notation "apply" "*" constr(H) :=
  tracejs H; tracejs_code; apply* H.

Tactic Notation "applys" constr(H) :=
  tracejs H; tracejs_code; applys H.

Tactic Notation "applys" "*" constr(H) :=
  tracejs H; tracejs_code; applys* H.

Tactic Notation "applys" "~" constr(H) :=
  tracejs H; tracejs_code; applys~ H.

Tactic Notation "sapply" constr(H) :=
  tracejs H; tracejs_code; sapply H.

(* applys_and uses applys~ and is defined after this module is loaded *)
(* run tactics use applys and are defined after this module is loaded *)

(* Tactics that are applied to red_* rules:
  apply*
  apply~
  applys
  applys~
  applys*
  applys_and
  run
  run*
  run~
*)
