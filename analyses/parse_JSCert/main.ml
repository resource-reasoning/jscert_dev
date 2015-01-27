
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
    print_endline "Typing things." ;
    let var_type x = assoc_option (normalise_var_name x) implicit_types in
    let coercions : (ctype *(* >-> *) ctype) list ref =
        ref [ Basic_type (None, "bool"), Prop ] in
    let add_coercion t1 t2 =
        coercions := (t1, t2) :: !coercions in
    let def_types : ((string option * string) * ctype) list ref = ref [] in
    let loc_types (* Ugly *) : (string * ctype) list ref = ref [] in
    let add_def_type local mx t =
        let add () =
            match assoc_option mx !def_types with
            | None ->
                def_types := (mx, t) :: !def_types
            | Some t' ->
                if not (t = t') (* TODO: Deal with coercions. *) then
                    prerr_endline ("Warning: The two types " ^ string_of_type t ^ " and " ^ string_of_type t' ^ " have been assumed to be the same.")
        in match mx with
        | (None, x) ->
            if assoc_option x local = None then add ()
            else (match assoc_option x !loc_types with
                | None -> loc_types := (x, t) :: !loc_types
                | Some t' ->
                    if not (t = t') (* TODO: Deal with coercions. *) then
                        prerr_endline ("Warning: The two types " ^ string_of_type t ^ " and " ^ string_of_type t' ^ " have been assumed to be the same."))
        | _ -> add () in
    let rec learn_type local e t =
        match e, t with
        | Ident (_, m, x), _ ->
            add_def_type local (m, x) t
        | Couple (e1, e2), Prod_type (t1, t2) ->
            learn_type local e1 t1 ;
            learn_type local e2 t2
        | _ -> () (* This is just a script, it hasn't to be complete :-) *)
    in
    let rec type_expr local = function
        | Ident (_, m, x) ->
            (match if m = None then var_type x else None with
            | Some t -> Some t
            | None ->
                match if m = None then assoc_option x local else None with
                | Some (Some t) -> Some t
                | Some None -> None
                | None -> assoc_option (m, x) !def_types)
        | App (e1, _, e2) ->
            (match type_expr local e1 with
            | Some (App_type (t1, t2)) ->
                learn_type local e2 t1 ;
                Some t2
            | _ -> None)
        | Binop ((Add | Sub | Mult), e1, e2) ->
            learn_type local e1 (Basic_type (None, "int")) ;
            learn_type local e2 (Basic_type (None, "int")) ;
            Some (Basic_type (None, "int"))
        | Binop ((And | Or), e1, e2) ->
            learn_type local e1 Prop ;
            learn_type local e2 Prop ;
            Some Prop
        | Binop ((Band | Bor), e1, e2) ->
            learn_type local e1 (Basic_type (None, "bool")) ;
            learn_type local e2 (Basic_type (None, "bool")) ;
            Some (Basic_type (None, "bool"))
        | Binop ((Inf | Infeq | Sup | Supeq | Eq | Neq), e1, e2) ->
            (match type_expr local e1, type_expr local e2 with
            | Some t, _ -> learn_type local e2 t
            | _, Some t -> learn_type local e1 t
            | _ -> ()) ;
            Some Prop
        | Binop (Lcons, e1, e2) ->
            (match type_expr local e1, type_expr local e2 with
            | Some t, _ ->
                let tl = App_type (Basic_type (None, "list"), t) in
                learn_type local e2 tl ;
                Some tl
            | _, Some (App_type (Basic_type (None, "list"), t) as tl) ->
                learn_type local e1 t ;
                Some tl
            | _ -> None)
        | Binop (Lapp, e1, e2) ->
            (match type_expr local e1, type_expr local e2 with
            | Some t, _ -> learn_type local e2 t ; Some t
            | _, Some t -> learn_type local e1 t ; Some t
            | _ -> None)
        | Binop (Llast, e1, e2) ->
            (match type_expr local e2, type_expr local e1 with
            | Some t, _ ->
                let tl = App_type (Basic_type (None, "list"), t) in
                learn_type local e2 tl ;
                Some tl
            | _, Some (App_type (Basic_type (None, "list"), t) as tl) ->
                learn_type local e1 t ;
                Some tl
            | _ -> None)
        | Unop (Not, e) ->
            learn_type local e Prop ; Some Prop
        | Couple (e1, e2) ->
            (match type_expr local e1, type_expr local e2 with
            | Some t1, Some t2 -> Some (Prod_type (t1, t2))
            | _ -> None)
        | String _ -> Some (Basic_type (None, "string"))
        | Int _ -> Some (Basic_type (None, "int"))
        | Forall _ -> Some Prop
        | Expr_type _ -> Some Prop
        | Wildcard -> None
        | Match _ -> None (* This is just a script, it hasn't to be complete :-) *)
    in
    let add_argument_types resulttype =
        List.fold_left (fun rt (x, top, i) ->
            match rt with
            | None -> None
            | Some rt ->
                if i then Some rt
                else match top with
                     | Some t -> Some (Fun_type (t, rt))
                     | None ->
                        match var_type x with
                        | Some t -> Some (Fun_type (t, rt))
                        | None -> None) (Some resulttype) in
    let get_local =
        List.fold_left (fun l (x, top, i) ->
            if i then l
            else (x, top) :: l) [] in
    let rec complete_local : (string * ctype option) list -> (string * ctype) list option = function
        | [] -> Some []
        | (x, Some t) :: l ->
            (match complete_local l with
            | None -> None
            | Some l -> Some ((x, t) :: l))
        | (x, None) :: l ->
            match assoc_option x !loc_types with
            | None -> None
            | Some t ->
                match complete_local l with
                | None -> None
                | Some l -> Some ((x, t) :: l) in
    let type_from_complete_local =
        List.fold_left (fun rt (x, t) ->
            Fun_type (t, rt)) in
    let fetchcoerciondefs = function
        | File_hypothesis h ->
            (match add_argument_types h.hyp_type h.hyp_arguments with
            | None -> ()
            | Some t -> learn_type [] (Ident (false, None, h.hyp_name)) t)
        | File_definition d ->
            let local = get_local d.arguments in
            loc_types := [] ;
            let add t =
                match complete_local local with
                | Some l ->
                    let t = type_from_complete_local t l in
                    learn_type [] (Ident (false, None, d.def_name)) t ;
                    if d.is_coercion then (
                        match t with
                        | Prod_type (t1, t2) -> add_coercion t1 t2
                        | _ -> ())
                | None -> () in
            (match d.def_type with
            | Some t -> learn_type local d.body t ; add t
            | None ->
                match type_expr local d.body with
                | Some t -> add t
                | None -> ())
        | File_coercion c ->
            add_coercion c.coercion_from c.coercion_to
        | File_record r ->
            List.iter (fun (x, t) ->
                learn_type [] (Ident (false, None, x))
                    (Fun_type (Basic_type (None, r.record_name), t))) r.record_inner
        | File_reductions rl ->
            let fetchrule red_name (r : rule) =
                if r.rule_params = [] && r.rule_localdefs = [] then ((* We only want simple inductive constructors. *)
                    let rec get_type = function
                        | Ident (false, m, x) ->
                            Some (Basic_type (m, x))
                        | App (e1, None, e2) ->
                            (match get_type e1, get_type e2 with
                            | Some t1, Some t2 -> Some (App_type (t1, t2))
                            | _ -> None)
                        | Binop (Mult, e1, e2) ->
                            (match get_type e1, get_type e2 with
                            | Some t1, Some t2 -> Some (Prod_type (t1, t2))
                            | _ -> None)
                        | Expr_type t -> Some t
                        | _ -> None in
                    let rec get_type_list = function
                        | [] -> None
                        | [a] -> get_type a
                        | a :: l ->
                            match get_type a, get_type_list l with
                            | Some ta, Some tl -> Some (Fun_type (ta, tl))
                            | _, _ -> None
                    in
                    match get_type_list r.rule_statement_list with
                    | None ->
                        if r.rule_statement_list = [] then (* See parser *)
                            learn_type [] (Ident (false, None, r.rule_name))
                                (Basic_type (None, red_name))
                    | Some t ->
                        learn_type [] (Ident (false, None, r.rule_name)) t)
            in
            List.iter (fun (r : red) ->
                if r.red_params = [] then
                    (match r.red_type with
                    | Some t ->
                        learn_type [] (Ident (false, None, r.red_name)) t
                    | None -> ()) ;
                List.iter (fetchrule r.red_name) r.rules) rl
        | _ -> ()
    in
    List.iter fetchcoerciondefs jssyntaxfile ;
    List.iter fetchcoerciondefs jsprettyintermfile ;
    List.iter fetchcoerciondefs jsprettyrulesfile ;
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
    let all_rule1 =
        List.map (fun r ->
            let local = r.rule_params in
            loc_types := [] ;
            List.iter (fun e -> ignore (type_expr local e)) r.rule_statement_list ;
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
                            match assoc_option x !loc_types with
                            | Some t -> (x, t)
                            | None ->
                                    if x = "extp" then List.iter (fun e -> prerr_endline ("DEBUG: " ^ string_of_expr e)) r.rule_statement_list ;
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

