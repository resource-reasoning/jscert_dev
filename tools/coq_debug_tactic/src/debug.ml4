open Tacmach

(* debug : tactic *)
let debug = fun gl ->
  let pp = pr_gls gl in
  Refiner.tclIDTAC_MESSAGE pp gl

TACTIC EXTEND debug
  | ["debug"] -> [debug]
END;;
