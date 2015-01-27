
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
        Utils.par (string_of_type t1 ^ " * " ^ string_of_type t2)
    | Fun_type (t1, t2) ->
        Utils.par (string_of_type t1 ^ " -> " ^ string_of_type t2)
    | App_type (t1, t2) ->
        Utils.par (string_of_type t1 ^ " " ^ string_of_type t2)

