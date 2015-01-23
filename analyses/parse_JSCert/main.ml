
open Coq_repr

let rec variable_used x = function
    | Ident (i, m, y) ->
        m = None && y = x
    | App (e1, internal, e2) ->
        variable_used x e1 || variable_used x e2
    | Binop (op, e1, e2) ->
        variable_used x e1 || variable_used x e2
    | Unop (op, e) ->
        variable_used x e
    | Couple (e1, e2) ->
        variable_used x e1 || variable_used x e2
    | String s ->
        false
    | Int i ->
        false
    | Forall (l, e) ->
        not (List.exists (fun (y, _) -> x = y) l) && variable_used x e
    | Match (e, l) ->
        variable_used x e
            || List.exists (fun (p, e) ->
                    not (variable_used x p) && variable_used x e) l

let _ =
    print_endline "Reading rules." ;
    let lexbuf = Lexing.from_channel (open_in "../../coq/JsPrettyRules.v") in
    let f = Parser.main Lexer.token lexbuf in
    print_endline "Basic checks on rules." ;
    let check = function
        | File_reductions rl ->
            let checkred r =
                let checkrule r =
                    List.iter (fun (x, _) ->
                        if not (List.exists (variable_used x) r.rule_statement_list)
                        then prerr_endline ("Warning: parameter " ^ x ^ " seems to be unused in Rule " ^ r.rule_name ^ ".")) r.rule_params
                in
                List.iter checkrule r.rules
            in
            List.iter checkred rl
        | _ -> () in
    List.iter check f ;
    ()

