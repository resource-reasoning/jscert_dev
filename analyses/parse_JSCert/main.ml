
open Coq_repr
open Coq_repr_aux
open Utils


let _ =
    (*****************************************)
    print_endline "Reading rules." ;
    let parse_file file =
        print_endline ("Reading file " ^ file ^ ".") ;
        let lexbuf = Lexing.from_channel (open_in file) in
        Parser.main Lexer.token lexbuf in
    let jssyntax = parse_file "../../coq/JsSyntax.v" in
    let jsprettyrulesfile = parse_file "../../coq/JsPrettyRules.v" in
    (*****************************************)
    print_endline "Basic checks on rules." ;
    let all_reds : red list =
        List.concat (select_map
            (function File_reductions l -> Some l | _ -> None) jsprettyrulesfile) in
    let all_rules : rule list =
        List.concat (List.map (fun r -> r.rules) all_reds) in
    let checkrule r =
        List.iter (fun (x, _) ->
            let var_used =
                List.exists (variable_used x) r.rule_statement_list in
            let var_used_in_types =
                List.exists (function
                    | (_, None) -> false
                    | (_, Some t) -> variable_used_type x t) r.rule_params in
            if not (var_used || var_used_in_types)
            then prerr_endline ("Warning: parameter " ^ x ^ " seems to be unused in Rule " ^ r.rule_name ^ ".") ;
            if count (fun (y, _) -> x = y) r.rule_params > 1
            then prerr_endline ("Warning: parameter " ^ x ^ " seems to be defined more than once in Rule " ^ r.rule_name ^ ".") ;
            ()) r.rule_params in
    List.iter checkrule all_rules ;
    (*****************************************)
    let imports =
        List.rev (select_map (function File_import s -> Some s | _ -> None) jsprettyrulesfile) in
    let scopes =
        List.rev (select_map (function File_scope s -> Some s | _ -> None) jsprettyrulesfile) in
    let implicit_types : (string * ctype) list =
        List.rev (select_map (function File_implicit_type im -> Some im | _ -> None) jsprettyrulesfile) in
    let coq_file name =
        let f = open_out_coq name in
        print_endline ("File " ^ name ^ " created and being written.") ;
        List.iter (fun s -> output_endline f ("Require Import " ^ s ^ ".")) imports ;
        List.iter (fun s -> output_endline f ("Open Scope " ^ s ^ ".")) scopes ;
        List.iter (fun (x, t) -> output_endline f ("Implicit Type " ^ x ^ " : " ^ string_of_type t ^ ".")) implicit_types ;
        flush f ;
        f in
    (*****************************************)
    print_endline "Normalising the rules." ;
    let all_preds : red_pred list =
        let inputoutput = [
            "red_javascript", [true; false] ;
            "red_prog", [true; true; true; false] ;
            "red_stat", [true; true; true; false] ;
            "red_expr", [true; true; true; false] ;
            "red_spec", [(*true;*) true; true; true; false] ;
        ] in
        List.map (fun r ->
            match assoc_option r.red_name inputoutput with
            | None ->
                prerr_endline ("Predicate " ^ r.red_name ^ " not found in inputoutput (see main.ml). Aborting.") ;
                exit 0
            | Some l -> {
                red_pred_name = r.red_name ;
                red_pred_types =
                    let rt =
                        match r.red_type with
                        | Some t -> t
                        | None ->
                            prerr_endline ("The reduction " ^ r.red_name ^ " has no declared type. Aborting.") ;
                            exit 0 in
                    let ts =
                        let rec aux = function
                            | Fun_type (t, Prop) -> [t]
                            | Fun_type (t1, t2) -> t1 :: aux t2
                            | t ->
                                prerr_endline ("I don't understand the subtype " ^ string_of_type t ^ " of " ^ string_of_type rt ^ " of the reduction " ^ r.red_name ^ ". Aborting.") ;
                                exit 0
                        in aux rt
                    in try List.map2 (fun t i -> (t, i)) ts l
                    with Invalid_argument _ -> (
                        prerr_endline ("Predicate " ^ r.red_name ^ " doesn't match its status in inputoutput (see main.ml, " ^ string_of_int (List.length ts) ^ " versus " ^ string_of_int (List.length l) ^ "). Aborting.") ;
                        exit 0
                    )
            }) all_reds
    in
    let is_pred p = List.exists (fun r -> p = r.red_pred_name) all_preds in
    let var_type x = assoc_option (normalise_var_name x) implicit_types in
    let all_rule1 =
        List.map (fun r ->
            let (prems, conclusion) = cut_last r.rule_statement_list in
            let (premisses, conditions) = separate (fun e ->
                match get_pred e with
                | None -> false
                | Some p -> is_pred p) prems in
            let p = get_pred conclusion in
            let inputs = [] (* TODO *) in
            let types_params =
                List.map (function
                    | (x, Some t) -> (x, t)
                    | (x, None) ->
                        match var_type x with
                        | Some t -> (x, t)
                        | None ->
                            prerr_endline ("Warning: Unable to detect the type of " ^ x ^ " in Rule " ^ r.rule_name ^ ".") ;
                            (x, Basic_type (None, "_" (* Hack! *)))) r.rule_params in
            {
                rule1_name = r.rule_name ;
                rule1_params =
                    List.map (fun (x, t) -> (x, t, List.mem x inputs)) types_params ;
                rule1_conditions = conditions ;
                rule1_premisses = premisses ;
                rule1_conclusion = conclusion
            }) all_rules in
    (*****************************************)
    print_endline "Extracting the reductions." ;
    let namesf = coq_file "gen/JsNames.v" in
    output_endline namesf "Inductive js_names :=" ;
    ()

