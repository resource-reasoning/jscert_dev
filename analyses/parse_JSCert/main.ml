
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
    let jssyntaxfile = parse_file "../../coq/JsSyntax.v" in
    let jssyntaxauxfile = parse_file "../../coq/JsSyntaxAux.v" in
    let jscommonfile = parse_file "../../coq/JsCommon.v" in
    let jspreliminaryfile = parse_file "../../coq/JsPreliminary.v" in
    let jsprettyintermfile = parse_file "../../coq/JsPrettyInterm.v" in
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
    print_endline "Typing things." ;
    List.iter Typing.fetchcoerciondefs jssyntaxfile ;
    (*List.iter Typing.fetchcoerciondefs jssyntaxauxfile ;*) (* I assume two much about the naming convention for this file... *)
    List.iter Typing.fetchcoerciondefs jscommonfile ;
    List.iter Typing.fetchcoerciondefs jspreliminaryfile ;
    List.iter Typing.fetchcoerciondefs jsprettyintermfile ;
    List.iter Typing.fetchcoerciondefs jsprettyrulesfile ;
    (*****************************************)
    let imports =
        List.rev (select_map (function File_import s -> Some s | _ -> None) jsprettyrulesfile) in
    let scopes =
        List.rev (select_map (function File_scope s -> Some s | _ -> None) jsprettyrulesfile) in
    let coq_file name =
        let f = open_out_coq name in
        print_endline ("File " ^ name ^ " created and being written.") ;
        List.iter (fun s -> output_endline f ("Require Import " ^ s ^ ".")) imports ;
        separate_coq f ;
        List.iter (fun s -> output_endline f ("Open Scope " ^ s ^ ".")) scopes ;
        separate_coq f ;
        List.iter (fun (x, t) -> output_endline f ("Implicit Type " ^ x ^ " : " ^ string_of_type t ^ ".")) (Typing.all_implicit_types ()) ;
        separate_coq f ;
        flush f ;
        f in
    (*****************************************)
    print_endline "Normalising the rules." ;
    let inputoutput = [
        "red_javascript", [true; false] ;
        "red_prog", [true; true; true; false] ;
        "red_stat", [true; true; true; false] ;
        "red_expr", [true; true; true; false] ;
        "red_spec", [(*true;*) true; true; true; false] ;
    ] in
    let all_preds : red_pred list =
        List.map (fun r ->
            match assoc_option r.red_name inputoutput with
            | None ->
                prerr_endline ("Predicate " ^ r.red_name ^ " not found in inputoutput (see main.ml). Aborting.") ;
                exit 0
            | Some l -> {
                red_pred_name = r.red_name ;
                red_forall_params = r.red_params ; (* In practise, this is just for red_spec and its “forall {T},”. *)
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
    let all_rule1 : rule1 list =
        List.map (fun r ->
            let local = r.rule_params in
            Typing.reset_loc_types () ;
            let local_defs =
                List.map (fun (x, e) ->
                    let location = " in the local definition of " ^ x ^ " in Rule " ^ r.rule_name in
                    match Typing.type_expr location local e with
                    | e, Some t -> (x, e, t)
                    | e, None ->
                        match Typing.var_type x with
                        | Some t ->
                            Typing.learn_type location local e t ;
                            (x, e, t)
                        | None ->
                            prerr_endline ("Warning: Unable to get a type for " ^ x ^ " in the local definitions of Rule " ^ r.rule_name) ;
                            (x, e, Basic_type (None, "_" (* Hack! *)))) r.rule_localdefs in
            let local = List.map (fun (x, e, t) -> (x, Some t)) local_defs @ local in
            let (prems, conclusion) =
                cut_last (List.map (fun e ->
                    fst (Typing.type_expr (" in the premisses of Rule " ^ r.rule_name) local e)) r.rule_statement_list) in
            let (premisses, conditions) = List.partition (fun e ->
                match get_pred e with
                | None -> false
                | Some p -> is_pred p) prems in
            match get_pred conclusion with
            | None ->
                prerr_endline ("Unable to parse the conclusion of Rule " ^ r.rule_name ^ ". Aborting.") ;
                exit 0
            | Some p ->
                match assoc_option p inputoutput with
                | None ->
                    prerr_endline ("Predicate " ^ p ^ " of the conclusion of Rule " ^ r.rule_name ^ " not found in inputoutput (see main.ml). Aborting.") ;
                    exit 0
                | Some input_spec ->
                    let rec get_inputs = function
                        | [true], e -> [e]
                        | [false], _ -> []
                        | true :: input_spec, App (e, None, arg) ->
                            arg :: get_inputs (input_spec, e)
                        | false :: input_spec, App (e, None, arg) ->
                            get_inputs (input_spec, e)
                        | _ ->
                            prerr_endline ("Rule " ^ r.rule_name ^ " doesn't match its status in inputoutput (see main.ml). Aborting.") ;
                            exit 0 in
                    let inputs : expr list =
                        List.rev (get_inputs (List.rev input_spec, conclusion)) in
                    let types_params =
                        let unable x =
                            prerr_endline ("Warning: Unable to detect the type of " ^ x ^ " in Rule " ^ r.rule_name ^ ".") ;
                            (x, Basic_type (None, "_" (* Hack! *)))
                        in
                        List.map (function
                            | (x, Some t) -> (x, t)
                            | (x, None) ->
                                match Typing.var_type x with
                                | Some t -> (x, t)
                                | None ->
                                    match Typing.get_loc_type x with
                                    | Some t -> (x, t)
                                    | None -> (* A last chance try... *)
                                        match List.rev (char_list_of_string (normalise_var_name x)) with
                                        | 's' :: l -> (
                                            let x' = string_of_char_list (List.rev l) in
                                            match Typing.var_type x' with
                                            | Some t -> (x, App_type (Basic_type (None, "list"), t))
                                            | None -> unable x)
                                        | _ -> unable x) r.rule_params in
                    {
                        rule1_name = r.rule_name ;
                        rule1_params =
                            List.map (fun (x, t) -> (x, t, List.exists (variable_used x) inputs)) types_params ;
                        rule1_localdefs = local_defs ;
                        rule1_conditions = conditions ;
                        rule1_premisses = premisses ;
                        rule1_conclusion = conclusion
                    }) all_rules in
    let rule1f = coq_file "gen/JsRules_1_typed.v" in
    output_rule1 rule1f all_preds all_rule1 ;
    separate_coq rule1f ;
    close_out rule1f ;
    (*****************************************)
    print_endline "Unfolding definitions." ;
    (*****************************************)
    ()

