open Names
open Tacmach
open Pp

let tracejs (pp : std_ppcmds) : tactic =
  Tacticals.tclIDTAC_MESSAGE (str "tracejs: " ++ pp ++ fnl ())

let print (h : identifier) : tactic = fun gl ->
  let hyp = pf_get_hyp gl h in
  tracejs (Printer.pr_var_decl (Global.env()) hyp) gl

TACTIC EXTEND tracejs
  | ["tracejs" string(s)] -> [tracejs (str s)]
  | ["tracejs_hyp" hyp(h)] -> [print h]
END;;
