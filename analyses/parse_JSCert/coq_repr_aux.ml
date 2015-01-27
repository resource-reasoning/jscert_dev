
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
    | Expr_type t ->
        variable_used_type x t
    | Match (e, l) ->
        variable_used x e
            || List.exists (fun (p, e) ->
                    not (variable_used x p) && variable_used x e) l

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
    | String s -> "\"" ^ s ^ "\"%string"
    | Int i -> string_of_int i ^ "%int"
    | Forall (l, e) ->
        "forall " ^ String.concat " "
            (List.map (function
                | (x, None) -> x
                | (x, Some t) -> par (x ^ " : " ^ string_of_type t)) l) ^
        ", " ^ string_of_expr e
    | Expr_type t ->
        string_of_type t
    | Match (e, l) ->
        "NYI"

