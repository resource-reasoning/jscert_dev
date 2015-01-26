
open Coq_repr
open Coq_repr_aux

let _ =
    (*****************************************)
    print_endline "Reading rules." ;
    let lexbuf = Lexing.from_channel (open_in "../../coq/JsPrettyRules.v") in
    let jsprettyrulesfile = Parser.main Lexer.token lexbuf in
    (*****************************************)
    print_endline "Basic checks on rules." ;
    let check = function
        | File_reductions rl ->
            let checkred r =
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
                        if Utils.count (fun (y, _) -> x = y) r.rule_params > 1
                        then prerr_endline ("Warning: parameter " ^ x ^ " seems to be defined more than once in Rule " ^ r.rule_name ^ ".") ;
                        ()) r.rule_params
                in
                List.iter checkrule r.rules
            in
            List.iter checkred rl
        | _ -> () in
    List.iter check jsprettyrulesfile ;
    (*****************************************)
    let imports =
        List.concat
            (List.map (function File_import s -> [s] | _ -> []) jsprettyrulesfile) in
    let scopes =
        List.concat
            (List.map (function File_scope s -> [s] | _ -> []) jsprettyrulesfile) in
    let implicit_types =
        List.concat
            (List.map (function File_implicit_type im -> [im] | _ -> []) jsprettyrulesfile) in
    let coq_file name =
        let f = Utils.open_out_coq name in
        print_endline ("File " ^ name ^ " created and being writen.") ;
        List.iter (fun s -> Utils.output_endline f ("Require Import " ^ s ^ ".")) imports ;
        List.iter (fun s -> Utils.output_endline f ("Open Scope " ^ s ^ ".")) scopes ;
        List.iter (fun (x, t) -> Utils.output_endline f ("Implicit Type " ^ x ^ " : " ^ string_of_type t ^ ".")) implicit_types ;
        flush f ;
        f in
    (*****************************************)
    print_endline "Extracting rule names." ;
    let names = coq_file "gen/JsNames.v" in
    ()

