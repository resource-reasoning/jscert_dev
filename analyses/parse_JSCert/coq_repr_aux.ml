
open Coq_repr
open Utils

let rec variable_used_type x = function
    | Prop ->
        false
    | Basic_type (m, y) ->
        m = None && x = y
    | Prod_type (t1, t2) ->
        variable_used_type x t1 || variable_used_type x t2
    | Fun_type (t1, t2) ->
        variable_used_type x t1 || variable_used_type x t2
    | App_type (t1, t2) ->
        variable_used_type x t1 || variable_used_type x t2

let rec variable_used x = function
    | Wildcard ->
        false
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
    | Exists (l, e) ->
        not (List.exists (fun (y, _) -> x = y) l) && variable_used x e
    | Expr_type t ->
        variable_used_type x t
    | Match (e, l) ->
        variable_used x e
            || List.exists (fun (p, e) ->
                    not (variable_used x p) && variable_used x e) l
    | Ifthenelse (e1, e2, e3) ->
        variable_used x e1 || variable_used x e2 || variable_used x e3

let rec get_pred = function
    | Ident (_, None, x) -> Some x
    | App (e, _, _) -> get_pred e
    | _ -> None


let rec string_of_type = function
    | Prop ->
        "Prop"
    | Basic_type (None, s) -> s
    | Basic_type (Some m, s) -> m ^ "." ^ s
    | Prod_type (t1, t2) ->
        par (string_of_type t1 ^ " * " ^ string_of_type t2)
    | Fun_type (t1, t2) ->
        par (string_of_type t1 ^ " -> " ^ string_of_type t2)
    | App_type (t1, t2) ->
        par (string_of_type t1 ^ " " ^ string_of_type t2)

let rec string_of_expr = function
    | Wildcard -> "_"
    | Ident (i, m, x) ->
        (if i then "@" else "") ^
        (match m with Some m -> m ^ "." | None -> "") ^ x
    | App (e1, internal, e2) ->
        par (string_of_expr e1 ^
            match internal with
            | Some x -> " (" ^ x ^ " := " ^ string_of_expr e2 ^ ")"
            | None -> " " ^ string_of_expr e2)
    | Binop (op, e1, e2) ->
        let b = match op with
            | Add -> "+"
            | Sub -> "-"
            | Mult -> "*"
            | And -> "/\\"
            | Or -> "\\/"
            | Band -> "&&"
            | Bor -> "||"
            | Inf -> "<"
            | Infeq -> "<="
            | Sup -> ">"
            | Supeq -> ">="
            | Lcons -> "::"
            | Lapp -> "++"
            | Llast -> "&"
            | Eq -> "="
            | Neq -> "<>" in
        par (string_of_expr e1 ^ " " ^ b ^ " " ^ string_of_expr e2)
    | Unop (op, e) ->
        let b = match op with
            | Not -> "~" in
        par (b ^ " " ^ string_of_expr e)
    | Couple (e1, e2) ->
        par (string_of_expr e1 ^ ", " ^ string_of_expr e2)
    | String s -> par ("(\"" ^ s ^ "\")%string")
    | Int i -> par (par (string_of_int i) ^ "%Z")
    | Forall (l, e) ->
        "forall " ^ String.concat " "
            (List.map (function
                | (x, None) -> x
                | (x, Some t) -> par (x ^ " : " ^ string_of_type t)) l) ^
        ", " ^ string_of_expr e
    | Exists (l, e) ->
        "exists " ^ String.concat " "
            (List.map (function
                | (x, None) -> x
                | (x, Some t) -> par (x ^ " : " ^ string_of_type t)) l) ^
        ", " ^ string_of_expr e
    | Expr_type t ->
        string_of_type t
    | Match (e, l) ->
        "NYI"
    | Ifthenelse (e1, e2, e3) ->
        par ("ifb " ^ string_of_expr e1 ^ " then " ^ string_of_expr e2 ^ " else " ^ string_of_expr e3)

let output_rule1 f preds rules =
    let print_start_pred start p =
        let forall_params =
            if p.red_forall_params = [] then ""
            else (
                "forall " ^ String.concat " " (List.map (function
                    | (x, Some t, false) ->
                        par (x ^ " : " ^ string_of_type t)
                    | (x, Some t, true) ->
                        "{" ^ x ^ " : " ^ string_of_type t ^ "}"
                    | (x, None, true) ->
                        "{" ^ x ^ "}"
                    | (x, None, false) -> x) p.red_forall_params) ^ ", "
            ) in
        output_endline f (start ^ p.red_pred_name ^ " : " ^ forall_params ^
            String.concat " -> " (List.map (fun (t, i) ->
                string_of_type t ^ if i then " (* input *)" else "") p.red_pred_types) ^
            " -> Prop :=") in
    let rec aux preds current_pred = function
        | [] ->
            output_endline f "  .\n"
        | r :: rules ->
            let (preds, current_pred) =
                match get_pred r.rule1_conclusion with
                | None ->
                    prerr_endline "Should not happen. Aborting." ;
                    exit 0
                | Some conclusion ->
                    if current_pred conclusion
                    then (preds, current_pred)
                    else match preds with
                        | [] ->
                            prerr_endline ("Unknown predicate " ^ conclusion ^ " in Rule " ^ r.rule1_name ^ ". Aborting.") ;
                            exit 0
                        | p :: l ->
                            print_start_pred "\n\nwith " p ;
                            (l, fun p' -> p.red_pred_name = p')
            in
            output_endline f ("\n  | " ^ r.rule1_name ^ " :");
            output_endline f ("    forall " ^
                String.concat " " (List.map (fun (x, t, i) ->
                    par (x ^ " : " ^ string_of_type t ^
                    if i then " (* input *)" else "")) r.rule1_params) ^ ",") ;
            List.iter (fun e -> output_endline f ("      " ^ string_of_expr e ^ " ->")) r.rule1_conditions ;
            output_endline f ("      (* " ^ String.make 42 '=' ^ " *)") ;
            List.iter (fun e -> output_endline f ("      " ^ string_of_expr e ^ " ->")) r.rule1_premisses ;
            output_endline f ("      (* " ^ String.make 42 '-' ^ " *)") ;
            output_endline f ("      " ^ string_of_expr r.rule1_conclusion) ;
            aux preds current_pred rules
    in match preds with
    | [] ->
        prerr_endline "No reduction defined! Aborting." ;
        exit 0
    | p :: preds ->
        print_start_pred "Inductive " p ;
        aux preds (fun p' -> p.red_pred_name = p') rules


