
open Coq_repr
open Coq_repr_aux
open Utils

let coercions : (ctype *(* >-> *) ctype) list ref =
    ref [ Basic_type (None, "bool"), Prop ]

let rec coercable t1 t2 =
    t1 = t2 || List.mem (t1, t2) !coercions ||
        match t1, t2 with
        | Prod_type (t1a, t1b), Prod_type (t2a, t2b) ->
            coercable t1a t2a && coercable t1b t2b
        | Fun_type (t1a, t1b), Fun_type (t2a, t2b) ->
            coercable t1a t2a && coercable t1b t2b
        | App_type (t1a, t1b), App_type (t2a, t2b) ->
            coercable t1a t2a && coercable t1b t2b
        | _ -> false

let rec simpl_coercion t1 t2 =
    match t1, t2 with
    | Prod_type (t1a, t1b), Prod_type (t2a, t2b) when coercable t1a t2a ->
        simpl_coercion t1b t2b
    | Prod_type (t1a, t1b), Prod_type (t2a, t2b) when coercable t1b t2b ->
        simpl_coercion t1a t2a
    | Fun_type (t1a, t1b), Fun_type (t2a, t2b) when coercable t1a t2a ->
        simpl_coercion t1b t2b
    | Fun_type (t1a, t1b), Fun_type (t2a, t2b) when coercable t1b t2b ->
        simpl_coercion t1a t2a
    | App_type (t1a, t1b), App_type (t2a, t2b) when coercable t1a t2a ->
        simpl_coercion t1b t2b
    | App_type (t1a, t1b), App_type (t2a, t2b) when coercable t1b t2b ->
        simpl_coercion t1a t2a
    | _ -> (t1, t2)

let add_coercion t1 t2 =
    coercions := (t1, t2) ::
        List.fold_left (fun l (t3, t4) ->
            (t3, t4) :: if t3 = t2 then (t1, t4) :: l else l) [] !coercions

let def_types : ((string option * string) * ctype) list ref = ref []

let loc_types (* Ugly *) : (string * ctype) list ref = ref []
let reset_loc_types () = loc_types := []
let get_loc_type x = assoc_option x !loc_types

let add_def_type local mx t =
    let shouldbesame t1 t2 =
        if not (coercable t1 t2) then (
            let t1, t2 = simpl_coercion t1 t2 in
            add_coercion t1 t2 ;
            prerr_endline ("Warning: The type " ^ string_of_type t1 ^ " have been assumed to be coercable to " ^ string_of_type t2 ^ ".")
        ) in
    let add () =
        match assoc_option mx !def_types with
        | None ->
            def_types := (mx, t) :: !def_types
        | Some t' ->
            shouldbesame t t'
    in match mx with
    | (None, x) ->
        if assoc_option x local = None then add ()
        else (match get_loc_type x with
            | None -> loc_types := (x, t) :: !loc_types
            | Some t' ->
                shouldbesame t t')
    | _ -> add ()

let rec learn_type local e t =
    match e, t with
    | Ident (_, m, x), _ ->
        add_def_type local (m, x) t
    | Couple (e1, e2), Prod_type (t1, t2) ->
        learn_type local e1 t1 ;
        learn_type local e2 t2
    | _ -> () (* This is just a script, it hasn't to be complete :-) *)

let rec type_expr local var_type = function
    | Ident (_, m, x) ->
        (match if m = None then var_type x else None with
        | Some t -> Some t
        | None ->
            match if m = None then assoc_option x local else None with
            | Some (Some t) -> Some t
            | Some None -> None
            | None -> assoc_option (m, x) !def_types)
    | App (e1, _, e2) ->
        ignore (type_expr local var_type e2) ;
        (match type_expr local var_type e1 with
        | Some (Fun_type (t1, t2)) ->
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
        (match type_expr local var_type e1, type_expr local var_type e2 with
        | Some t, _ -> learn_type local e2 t
        | _, Some t -> learn_type local e1 t
        | _ -> ()) ;
        Some Prop
    | Binop (Lcons, e1, e2) ->
        (match type_expr local var_type e1, type_expr local var_type e2 with
        | Some t, _ ->
            let tl = App_type (Basic_type (None, "list"), t) in
            learn_type local e2 tl ;
            Some tl
        | _, Some (App_type (Basic_type (None, "list"), t) as tl) ->
            learn_type local e1 t ;
            Some tl
        | _ -> None)
    | Binop (Lapp, e1, e2) ->
        (match type_expr local var_type e1, type_expr local var_type e2 with
        | Some t, _ -> learn_type local e2 t ; Some t
        | _, Some t -> learn_type local e1 t ; Some t
        | _ -> None)
    | Binop (Llast, e1, e2) ->
        (match type_expr local var_type e2, type_expr local var_type e1 with
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
        (match type_expr local var_type e1, type_expr local var_type e2 with
        | Some t1, Some t2 -> Some (Prod_type (t1, t2))
        | _ -> None)
    | String _ -> Some (Basic_type (None, "string"))
    | Int _ -> Some (Basic_type (None, "int"))
    | Forall _ -> Some Prop
    | Expr_type _ -> Some Prop
    | Wildcard -> None
    | Match _ -> None (* This is just a script, it hasn't to be complete :-) *)

let add_argument_types var_type resulttype =
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
                    | None -> None) (Some resulttype)

let get_local =
    List.fold_left (fun l (x, top, i) ->
        if i then l
        else (x, top) :: l) []

let rec complete_local : (string * ctype option) list -> (string * ctype) list option = function
    | [] -> Some []
    | (x, Some t) :: l ->
        (match complete_local l with
        | None -> None
        | Some l -> Some ((x, t) :: l))
    | (x, None) :: l ->
        match get_loc_type x with
        | None -> None
        | Some t ->
            match complete_local l with
            | None -> None
            | Some l -> Some ((x, t) :: l)

let type_from_complete_local =
    List.fold_left (fun rt (x, t) ->
        Fun_type (t, rt))

let fetchcoerciondefs var_type = function
    | File_hypothesis h ->
        (match add_argument_types var_type h.hyp_type h.hyp_arguments with
        | None -> ()
        | Some t -> learn_type [] (Ident (false, None, h.hyp_name)) t)
    | File_definition d ->
        let local = get_local d.arguments in
        reset_loc_types () ;
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
            match type_expr local var_type d.body with
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

