
open Coq_repr
open Utils


let rec variable_used_type x = function
    | Prop | Type ->
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
    | Int i | Nat i ->
        false
    | Forall (l, e) ->
        not (List.exists (fun (y, _) -> x = y) l) && variable_used x e
    | Exists (l, e) ->
        not (List.exists (fun (y, _) -> x = y) l) && variable_used x e
    | Expr_type t ->
        variable_used_type x t
    | Match (es, l) ->
        List.exists (variable_used x) es
            || List.exists (fun (ps, e) ->
                    not (List.exists (variable_used x) ps) && variable_used x e) l
    | Ifthenelse (e1, e2, e3) ->
        variable_used x e1 || variable_used x e2 || variable_used x e3
    | Expr_record l ->
        List.exists (fun (_, e) -> variable_used x e) l
    | Function (l, e) ->
        not (List.exists (fun (y, _) -> x = y) l) && variable_used x e
    | Cast (e, t) ->
        variable_used x e || variable_used_type x t

let variable_unused e =
    let rec aux x =
        if variable_used x e then aux (x ^ "'")
        else x
    in aux "internal_variable"

let rec get_pred = function
    | Ident (_, None, x) -> Some x
    | App (e, _, _) -> get_pred e
    | _ -> None

let rec convert_to_type = function (* In Coq, we never know what is meant to be a type and what is meant to be a term. *)
    | Ident (false, m, x) -> Some (Basic_type (m, x))
    | App (e1, None, e2) ->
        (match convert_to_type e1, convert_to_type e2 with
        | Some t1, Some t2 -> Some (App_type (t1, t2))
        | _ -> None)
    | Binop (Mult, e1, e2) ->
        (match convert_to_type e1, convert_to_type e2 with
        | Some t1, Some t2 -> Some (Prod_type (t1, t2))
        | _ -> None)
    | Expr_type t -> Some t
    | _ -> None

let rec replace_ident_type x t = function
    | (Prop | Type) as t0 -> t0
    | Basic_type (m, y) as t0 ->
        if m = None && y = x
        then t
        else t0
    | Prod_type (t1, t2) ->
        Prod_type (replace_ident_type x t t1, replace_ident_type x t t2)
    | Fun_type (t1, t2) ->
        Fun_type (replace_ident_type x t t1, replace_ident_type x t t2)
    | App_type (t1, t2) ->
        App_type (replace_ident_type x t t1, replace_ident_type x t t2)

let rec replace_ident x e =
    let replace_in_type =
        match convert_to_type e with
        | None -> fun t -> t
        | Some t' ->
            fun t -> replace_ident_type x t' t
    in let replace_in_args =
        List.map (function
            | (x, None) -> (x, None)
            | (x, Some t) -> (x, Some (replace_in_type t)))
    in function
    | (Wildcard | String _ | Int _ | Nat _) as e0 -> e0
    | Expr_type t ->
        Expr_type (replace_in_type t)
    | Ident (_, _, y) as e0 ->
        if x = y then e else e0
    | App (e1, internal, e2) ->
        App (replace_ident x e e1, internal, replace_ident x e e2)
    | Binop (op, e1, e2) ->
        Binop (op, replace_ident x e e1, replace_ident x e e2)
    | Unop (op, e0) ->
        Unop (op, replace_ident x e e0)
    | Couple (e1, e2) ->
        Couple (replace_ident x e e1, replace_ident x e e2)
    | Forall (l, e0) ->
        if List.exists (fun (y, _) -> y = x) l then Forall (l, e0)
        else Forall (replace_in_args l, replace_ident x e e0)
    | Exists (l, e0) ->
        if List.exists (fun (y, _) -> y = x) l then Exists (l, e0)
        else Exists (replace_in_args l, replace_ident x e e0)
    | Match (es, pes) ->
        Match (List.map (replace_ident x e) es,
            List.map (fun (ps, e0) ->
                if List.exists (variable_used x) ps then (ps, e0)
                else (ps, replace_ident x e e0)) pes)
    | Ifthenelse (e0, e1, e2) ->
        Ifthenelse (replace_ident x e e0, replace_ident x e e1, replace_ident x e e2)
    | Expr_record l ->
        Expr_record (List.map (fun (y, e0) -> (y, replace_ident x e e0)) l)
    | Function (l, e0) ->
        if List.exists (fun (y, _) -> y = x) l then Function (l, e0)
        else Function (replace_in_args l, replace_ident x e e0)
    | Cast (e0, t) ->
        Cast (replace_ident x e e0, replace_in_type t)


let rec prefix_to_type excn prefix = function
    | (Prop | Type) as t -> t
    | Basic_type (_, s) as t when excn s -> t
    | Basic_type (None, s) -> Basic_type (None, prefix ^ s)
    | Basic_type (Some m, s) as t -> t
    | Prod_type (t1, t2) ->
        Prod_type (prefix_to_type excn prefix t1, prefix_to_type excn prefix t2)
    | Fun_type (t1, t2) ->
        Fun_type (prefix_to_type excn prefix t1, prefix_to_type excn prefix t2)
    | App_type (t1, t2) ->
        App_type (prefix_to_type excn prefix t1, prefix_to_type excn prefix t2)


let rec string_of_type = function
    | Prop ->
        "Prop"
    | Type ->
        "Type"
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
    | App (e1, internal, e2) as e ->
        let rec string_expr_app = function
            | App (e1, Some x, e2) -> string_expr_app e1 ^ " (" ^ x ^ " := " ^ string_of_expr e2 ^ ")"
            | App (e1, None, e2) -> string_expr_app e1 ^ " " ^ string_of_expr e2
            | e -> string_of_expr e in
        par (string_expr_app e)
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
            | Scons -> ":::"
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
    | Int i -> par (string_of_int i ^ "%Z")
    | Nat i -> par (string_of_int i ^ "%nat")
    | Forall (l, e) ->
        par ("forall " ^ String.concat " "
            (List.map (function
                | (x, None) -> x
                | (x, Some t) -> par (x ^ " : " ^ string_of_type t)) l) ^
        ", " ^ string_of_expr e)
    | Exists (l, e) ->
        par ("exists " ^ String.concat " "
            (List.map (function
                | (x, None) -> x
                | (x, Some t) -> par (x ^ " : " ^ string_of_type t)) l) ^
        ", " ^ string_of_expr e)
    | Expr_type t ->
        string_of_type t
    | Match (es, l) ->
        "match " ^ String.concat ", " (List.map string_of_expr es) ^ " with " ^
        String.concat " | " (List.map (fun (patterns, e) ->
            String.concat ", " (List.map string_of_expr patterns) ^ " => " ^ string_of_expr e) l) ^ " end"
    | Cast (Match (es, l), t) ->
        "match " ^ String.concat ", " (List.map string_of_expr es) ^ " return " ^ string_of_type t ^ " with " ^
        String.concat " | " (List.map (fun (patterns, e) ->
            String.concat ", " (List.map string_of_expr patterns) ^ " => " ^ string_of_expr e) l) ^ " end"
    | Ifthenelse (e1, e2, e3) ->
        par ("ifb " ^ string_of_expr e1 ^ " then " ^ string_of_expr e2 ^ " else " ^ string_of_expr e3)
    | Expr_record l ->
        "{| " ^ String.concat " ; " (List.map (fun (x, e) ->
            x ^ " := " ^ string_of_expr e) l) ^ " |}"
    | Function (l, e) ->
        par ("fun " ^ String.concat " "
            (List.map (function
                | (x, None) -> x
                | (x, Some t) -> par (x ^ " : " ^ string_of_type t)) l) ^
        " => " ^ string_of_expr e)
    | Cast (e, t) ->
        par (string_of_expr e ^ " : " ^ string_of_type t)

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
            output_endline f ("      forall " ^
                String.concat " " (List.map (fun (x, t, i) ->
                    par (x ^ " : " ^ string_of_type t ^
                    if i then " (* input *)" else "")) r.rule1_params) ^ ",") ;
            List.iter (fun (x, e, t) -> output_endline f ("        let " ^ x ^ " : " ^ string_of_type t ^ " := " ^ string_of_expr e ^ " in")) r.rule1_localdefs ;
            List.iter (fun e -> output_endline f ("        " ^ string_of_expr e ^ " ->")) r.rule1_conditions ;
            output_endline f ("        (* " ^ String.make 42 '=' ^ " *)") ;
            List.iter (fun e -> output_endline f ("        " ^ string_of_expr e ^ " ->")) r.rule1_premisses ;
            output_endline f ("        (* " ^ String.make 42 '-' ^ " *)") ;
            output_endline f ("        " ^ string_of_expr r.rule1_conclusion) ;
            aux preds current_pred rules
    in match preds with
    | [] ->
        prerr_endline "No reduction defined! Aborting." ;
        exit 0
    | p :: preds ->
        print_start_pred "Inductive " p ;
        aux preds (fun p' -> p.red_pred_name = p') rules


