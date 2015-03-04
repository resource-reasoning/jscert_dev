open Names
open Tacmach
open Pp

(* Base string output tactic *)
let tracejs (pp : std_ppcmds) : tactic =
  let pfname = Pfedit.get_current_proof_name () in
  Tacticals.tclIDTAC_MESSAGE (str "tracejs (" ++ str (string_of_id pfname) ++ str "): " ++ pp ++ fnl ())

let idtac = Tacticals.tclIDTAC

open Printer
open Ppconstr
open Term
open Util

let rec my_pr_constr constr =
  let env = Global.env () in
  match kind_of_term constr with
    | Rel  n -> str "Rel " ++ int n
    | Var  i -> str "Var " ++ pr_id i
    | Meta m -> str "Meta " ++ int m
    | Evar _ -> str "Evar _" (* of 'constr pexistential *)
    | Sort _ -> str "Sort _" (* of sorts *)
    | Cast (c,_,_) -> str "Cast (" ++ pr_constr c ++ str ") _ _" (* of 'constr * cast_kind * 'types *)
    | Prod (_,_,_) -> str "Prod _" (* of name * 'types * 'types *)
    | Lambda (_,_,c) -> str "Lambda _ _ (" ++ pr_constr c ++ str ")" (* of name * 'types * 'constr *)
    | LetIn  (_,c1,_,c2) -> str "LetIn _ (" ++ pr_constr c1 ++ str ") _ (" ++ pr_constr c2 ++ str ")" (* of name * 'constr * 'types * 'constr *)
    | App    (c, arrc) -> str "App (" ++ pr_constr c ++ str ") " ++ pr_constr_arr arrc (*  of 'constr * 'constr array *)
    | Const  c -> str "Const (" ++ pr_constant env c ++ str ")"
    | Ind    i -> str "Ind (" ++ pr_inductive env i ++ str ")"
    | Construct c -> str "Construct (" ++ pr_constructor env c ++ str ")"
    | Case (_,c1,c2,arrc) -> str "Case _ (" ++ pr_constr c1 ++ str ") (" ++ pr_constr c2 ++ str ") _" (*  of case_info * 'constr * 'constr * 'constr array *)
    | Fix    _ -> str "Fix _" (* of ('constr, 'types) pfixpoint *)
    | CoFix  _ -> str "CoFix _" (* of ('constr, 'types) pcofixpoint *)

and pr_constr_arr arr =
  str "[" ++ hv 2 (prlist_with_sep pr_semicolon pr_constr (Array.to_list arr)) ++ str "]"

TACTIC EXTEND tracejs
  | ["tracejs" string(s)] -> [tracejs (str s)]
  | ["tracejs" constr(s)] -> [tracejs (my_pr_constr s)]
END


let my_pr_var_decl env (id,c,typ) =
  pr_id id ++ str " :: " ++ my_pr_constr typ

(* Debug tactic so I can see the structure of the term without sugar *)
let print_hyp (h : identifier) : tactic = fun gl ->
  let hyp = pf_get_hyp gl h in
  tracejs (my_pr_var_decl (Global.env()) hyp) gl

TACTIC EXTEND tracejs_hyp
  | ["tracejs_hyp" hyp(h)] -> [print_hyp h]
END

(* Print given pp_cmds to string, without newlines *)
let flat_string_formatter =
  let b = Format.formatter_of_buffer Format.stdbuf in
  let f : Format.formatter_out_functions = Format.pp_get_formatter_out_functions b () in
  let newline () = (f.Format.out_spaces 0) in
  let spaces _ = (f.Format.out_spaces 1) in
  Format.pp_set_formatter_out_functions b { f with Format.out_newline = newline; Format.out_spaces = spaces };
  b

(* Unbox a pp stream into single line *)
let pp_flat (pp : Pp.std_ppcmds) : Pp.std_ppcmds =
  Pp.msg_with flat_string_formatter pp;
  str (Format.flush_str_formatter ())

(* Print the term from a given side of an equality *)
let print_hyp_code (h : identifier) (dir : bool) : tactic = fun gl ->
  try
    let hyp = pf_get_hyp_typ gl h in
    let i = if dir then 2 else 1 in
    match Hipattern.match_with_equality_type hyp with
      | Some (_, args) -> tracejs (str "CODE: " ++ pp_flat (pr_constr (List.nth args i))) gl
      | None           -> error "NO CODE FOUND"
  with UserError (_,str) -> tracejs str gl

open Extraargs (* for orient *)
TACTIC EXTEND tracejs_code
  | ["tracejs_code" orient(dir)] -> [print_hyp_code (id_of_string "HR") dir]
  | ["tracejs_code" orient(dir) hyp(h)] -> [print_hyp_code h dir]
END
