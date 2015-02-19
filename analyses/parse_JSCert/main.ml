
open Coq_repr
open Coq_repr_aux
open Utils

(*****************************************)

let inputoutput = [
        "red_javascript", [true; false] ;
        "red_prog", [true; true; true; false] ;
        "red_stat", [true; true; true; false] ;
        "red_expr", [true; true; true; false] ;
        "red_spec", [(*true;*) true; true; true; false] ;
    ]

let pred_from_red r =
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
                    | Fun_type (t, Type) -> [t]
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
    }

(*****************************************)

let typing_rule is_pred r =
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
            let rec unfold_inputs = function
                | [true], e -> Typing.unfold e
                | [false], e -> e
                | true :: input_spec, App (e, None, arg) ->
                    App (unfold_inputs (input_spec, e), None, Typing.unfold arg)
                | false :: input_spec, App (e, None, arg) ->
                    App (unfold_inputs (input_spec, e), None, arg)
                | _ ->
                    prerr_endline ("Rule " ^ r.rule_name ^ " doesn't match its status in inputoutput or contain some internal call assignments in its conclusion (see main.ml). Aborting.") ;
                    exit 0 in
            let new_conclusion =
                unfold_inputs (List.rev input_spec, conclusion) in
            {
                rule1_name = r.rule_name ;
                rule1_params =
                    List.map (fun (x, t) -> (x, t, List.exists (variable_used x) inputs)) types_params ;
                rule1_localdefs = local_defs ;
                rule1_conditions = conditions ;
                rule1_premisses = premisses ;
                rule1_conclusion = new_conclusion
            }

(*****************************************)

let unfold_defs r =
    Typing.reset_loc_types () ;
    let (eqs, cond') = List.partition (function
        | Binop (Eq, Ident (false, None, x), _) -> true
        | Binop (Eq, _, Ident (false, None, x)) -> true
        | Binop (Eq, Couple (Ident (false, None, x), Ident (false, None, y)), _) -> true
        | _ -> false) r.rule1_conditions in
    let eqsn =
        List.concat (List.map (function
            | Binop (Eq, Ident (false, None, x), e) -> [x, e]
            | Binop (Eq, e, Ident (false, None, x)) -> [x, e]
            | Binop (Eq, Couple (Ident (false, None, x), Ident (false, None, y)), e) ->
                [x, App (Ident (false, None, "fst"), None, e)] @
                [y, App (Ident (false, None, "snd"), None, e)]
            | _ -> prerr_endline "Should not happen!" ; exit 0) eqs) in
    let unfold_local e =
        let rec aux e = function
            | [] -> e
            | (x, ex) :: l ->
                let e = replace_ident x ex e in
                aux e (List.map (fun (y, ey) ->
                    (y, replace_ident x ex ey)) l)
        in let lcls =
            List.map (fun (x, ex, tx) -> (x, Cast (ex, tx))) r.rule1_localdefs
        in aux e (lcls @ eqsn)
    in { r with
        rule1_params =
            List.filter (fun (x, _, _) ->
                not (List.exists (fun (y, _) -> x = y) eqsn)) r.rule1_params ;
        rule1_localdefs = [] ;
        rule1_conditions = List.map unfold_local cond' ;
        rule1_premisses = List.map unfold_local r.rule1_premisses ;
        rule1_conclusion = unfold_local r.rule1_conclusion
    }

(*****************************************)

let unfold_coercions r =
    Typing.reset_loc_types () ;
    let location =
        " while unfolding coercions in Rule " ^ r.rule1_name in
    let local =
        List.map (fun (x, t, input) -> (x, Some t)) r.rule1_params in
    let display = Typing.display_coercions location local in
    { r with
        rule1_conditions = List.map display r.rule1_conditions ;
        rule1_premisses = List.map display r.rule1_premisses ;
        rule1_conclusion = display r.rule1_conclusion
    }

(*****************************************)

let red_name = "red"
let red_in_name = red_name ^ "_in"
let red_out_name = red_name ^ "_out"
let prefix_types = "pbs_"
let excn_prefix x =
    List.mem x [ "list" ; "heap" ; "T" (* Hack! *) ]

let rule_merging all_preds r =
    let prefixing = prefix_to_type excn_prefix prefix_types in
    let all_outputtypes =
        List.concat (List.map (fun r ->
            List.concat (List.map (fun (t, b) ->
                if b then [] else [t]) r.red_pred_types)) all_preds) in
    let definition_contains_pbs t = true (* TODO *) in
    let pbsify t =
        if List.mem t all_outputtypes
        then Basic_type (None, red_out_name)
        else if definition_contains_pbs t
        then prefixing t
        else t in
    let merge e =
        match get_pred e with
        | None -> prerr_endline "Should not happen." ; exit 0
        | Some p ->
            match assoc_option p inputoutput with
            | None -> prerr_endline "Should not happen." ; exit 0
            | Some input_spec ->
                let rec get_inputs = function
                    | [], _ -> []
                    | true :: input_spec, App (e, None, arg) ->
                        arg :: get_inputs (input_spec, e)
                    | false :: input_spec, App (e, None, arg) ->
                        get_inputs (input_spec, e)
                    | _ ->
                        prerr_endline ("Rule " ^ r.rule1_name ^ " doesn't match its status in inputoutput (see main.ml). Aborting.") ;
                        exit 0 in
                let inputs : expr list =
                    List.rev (get_inputs (List.rev input_spec, e)) in
                let input_expr =
                    List.fold_left (fun e e' ->
                        App (e, None, e')) (Ident (false, None, red_in_name ^ "_" ^ p)) inputs
                in
                let outputs : expr list = (* TODO: Like this we are filtering the output of recursive call! This is wrong! *)
                    List.rev (get_inputs (List.rev (List.map not input_spec), e)) in
                let output_expr =
                    List.fold_left (fun e e' ->
                        App (e, None, e')) (Ident (false, None, red_out_name ^ "_" ^ p)) outputs
                in
                App (App (Ident (false, None, red_name), None, input_expr), None, output_expr)
    in
    { r with
        rule1_premisses = List.map merge r.rule1_premisses ;
        rule1_conclusion = merge r.rule1_conclusion
    }

(*****************************************)

let print_defs f all_defs =
    List.iter (output_definition f) (List.map fst (List.filter snd all_defs))

let _ =
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
    Typing.clear_implicit_types () ;
    List.iter Typing.fetchcoerciondefs jssyntaxfile ;
    Typing.clear_implicit_types () ;
    (* List.iter Typing.fetchcoerciondefs jssyntaxauxfile ;*) (* I assume two much about the naming convention for this file... *)
    Typing.clear_implicit_types () ;
    List.iter Typing.fetchcoerciondefs jscommonfile ;
    Typing.clear_implicit_types () ;
    List.iter Typing.fetchcoerciondefs jspreliminaryfile ;
    Typing.clear_implicit_types () ;
    List.iter Typing.fetchcoerciondefs jsprettyintermfile ;
    Typing.clear_implicit_types () ;
    List.iter Typing.fetchcoerciondefs jsprettyrulesfile ;
    let all_defs =
        List.map (fun d -> (d, false)) (Typing.get_all_defs ()) in
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
    let all_preds : red_pred list =
        List.map pred_from_red all_reds in
    let is_pred p = List.exists (fun r -> p = r.red_pred_name) all_preds in
    let all_rule1 : rule1 list =
        List.map (typing_rule is_pred) all_rules in
    let rule1f = coq_file "gen/JsRules_1_typed.v" in
    output_rule1 rule1f all_preds all_rule1 ;
    separate_coq rule1f ;
    close_out rule1f ;
    (*****************************************)
    print_endline "Unfolding definitions." ;
    let all_rule2 =
        List.map unfold_defs all_rule1 in
    let rule2f = coq_file "gen/JsRules_2_unfolding.v" in
    output_rule1 rule2f all_preds all_rule2 ;
    separate_coq rule2f ;
    close_out rule2f ;
    let all_rule3 =
        List.map unfold_coercions all_rule2 in
    let rule3f = coq_file "gen/JsRules_3_coercions.v" in
    output_rule1 rule3f all_preds all_rule3 ;
    separate_coq rule3f ;
    close_out rule3f ;
    (*****************************************)
    print_endline "Merging inductive rules." ;
    let (all_defs, name_changes) =
        Domains.change_def_type prefix_types
            ["out" (* TODO *), red_out_name] all_defs in
    let output_red_in_out f = (* TODO
        let print_ind pbsify name accept =
            output_endline f ("Inductive " ^ name ^ " :=") ;
            List.iter (fun r ->
                output_endline f ("  | " ^ name ^ "_" ^ r.red_pred_name ^ " : " ^
                    let used_params =
                        List.filter (fun (x, _, _) ->
                            List.exists (fun (e, b) ->
                                accept b && variable_used_type x e) r.red_pred_types) r.red_forall_params in
                    (if used_params = [] then ""
                    else ("forall " ^ String.concat " " (List.map (function
                        | (x, None, false) -> x
                        | (x, None, true) -> "{" ^ x ^ "}"
                        | (x, Some t, false) -> par (x ^ " : " ^ string_of_type (pbsify t))
                        | (x, Some t, true) -> "{" ^ x ^ " : " ^ string_of_type (pbsify t) ^ "}") used_params) ^ ", ")) ^
                        String.concat "" (List.map (fun (t, b) -> if accept b then (string_of_type (pbsify t) ^ " -> ") else "") r.red_pred_types) ^ name
                )) all_preds ;
            output_endline f "  ." ;
        in
        print_ind pbsify red_in_name (fun b -> b) ;
        separate_coq f ;
        print_ind prefixing red_out_name not ; (* TODO: Should only depend on the type. The reduction does not change! *)
        separate_coq f *) () in
    let red_pred = {
        red_pred_name = red_name ;
        red_forall_params = [] ;
        red_pred_types = [
            Basic_type (None, red_in_name), true ;
            Basic_type (None, red_out_name), false ]
    } in
    let all_rule4 =
        List.map (rule_merging all_preds) all_rule3 in
    let rule4f = coq_file "gen/JsRules_4_merging.v" in
    print_defs rule4f all_defs ;
    separate_coq rule4f ;
    (*output_red_in_out rule4f ;*)
    output_rule1 rule4f [red_pred] all_rule4 ;
    separate_coq rule4f ;
    close_out rule4f ;
    (*****************************************)
    ()

