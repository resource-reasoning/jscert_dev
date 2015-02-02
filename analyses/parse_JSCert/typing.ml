
open Coq_repr
open Coq_repr_aux
open Utils

let implicit_types : (string * ctype) list ref = ref []
let all_implicit_types () = !implicit_types

let var_type x = assoc_option (normalise_var_name x) !implicit_types

let coercions : (ctype *(* >-> *) ctype *(* := *) (expr -> expr)) list ref =
    ref [
        Basic_type (None, "bool"), Prop, (fun e -> App (Ident(false, None, "istrue"), None, e)) ;
        Basic_type (None, "nat"), Basic_type (None, "int"), (fun e -> App (Ident(false, None, "my_Z_of_nat"), None, e))
    ]

let direct_coercable t1 t2 =
    List.exists (fun (t1', t2', _) -> t1' = t1 && t2' = t2) !coercions

let rec coercable t1 t2 =
    t1 = t2 || direct_coercable t1 t2 ||
        match t1, t2 with
        | Prod_type (t1a, t1b), Prod_type (t2a, t2b) ->
            coercable t1a t2a && coercable t1b t2b
        | Fun_type (t1a, t1b), Fun_type (t2a, t2b) ->
            coercable t2a t1a && coercable t1b t2b
        | App_type (t1a, t1b), App_type (t2a, t2b) ->
            coercable t1a t2a && coercable t1b t2b
        | _ -> false

let get_direct_coercion t1 t2 =
    let rec aux = function
        | [] -> None
        | (t1', t2', f) :: l ->
            if t1' = t1 && t2' = t2 then Some f else aux l
    in aux !coercions

let rec get_coercion t1 t2 =
    if t1 = t2 then Some (fun e -> e)
    else
       match get_direct_coercion t1 t2 with
       | Some f -> Some f
       | None ->
            match t1, t2 with
            | Prod_type (t1a, t1b), Prod_type (t2a, t2b) ->
                (match get_coercion t1a t2a, get_coercion t1b t2b with
                | Some f1, Some f2 ->
                    Some (fun e ->
                        let x = Ident (false, None, variable_unused e) in
                        let y = Ident (false, None, variable_unused (Couple (x, e))) in
                        Match ([e], [[Couple (x, y)], Couple (f1 x, f2 y)]))
                | _ -> None)
            | Fun_type (t1a, t1b), Fun_type (t2a, t2b) ->
                (match get_coercion t2a t1a, get_coercion t1b t2b with
                | Some f1, Some f2 ->
                    Some (fun e ->
                        let x = variable_unused e in
                        Function ([x, Some t2a],
                            f2 (App (e, None, f1 (Ident (false, None, x))))))
                | _ -> None)
            | App_type (t1a, t1b), App_type (t2a, t2b) ->
                None
            | _ -> None

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

let research_common t1 t2 =
    let get_greater t =
        List.map (fun (_, tr, _) -> tr)
            (List.filter (fun (ta, tb, _) -> ta = t) !coercions) in
    let l1 = get_greater t1 in
    let l2 = get_greater t2 in
    let rec aux = function
    | [] -> None
    | t :: l ->
        if List.exists (fun t' -> coercable t' t) l then aux l
        else Some t
    in aux (List.filter (fun t -> List.mem t l1) l2)

let add_coercion t1 t2 convert =
    coercions := (t1, t2, convert) ::
        List.fold_left (fun l (t3, t4, convert') ->
            let l' = if t4 = t1 then (t3, t2, compose convert convert') :: l else l in
            (t3, t4, convert') :: if t3 = t2 then (t1, t4, compose convert' convert) :: l' else l') [] !coercions

let def_types : ((string option * string) * ctype) list ref =
    ref [
            (None, "undef"), Basic_type (None, "value") ;
            (None, "true"), Basic_type (None, "bool") ;
            (None, "false"), Basic_type (None, "bool")
        ]

let loc_types (* Ugly *) : (string * ctype) list ref = ref []
let reset_loc_types () = loc_types := []
let get_loc_type x = assoc_option x !loc_types

let add_def_type location (local : (string * ctype option) list) mx t =
    let shouldbecoercable t1 t2 =
        if not (coercable t1 t2) then (
            let t1, t2 = simpl_coercion t1 t2 in
            add_coercion t1 t2 (fun e -> Cast (e, t2)) ;
            prerr_endline ("Warning: The type " ^ string_of_type t1 ^ " have been assumed to be coercable to " ^ string_of_type t2 ^ location ^ ".")
        ) in
    let add () =
        match assoc_option mx !def_types with
        | None ->
            def_types := (mx, t) :: !def_types
        | Some t' ->
            shouldbecoercable t' t
    in match mx with
    | (None, x) ->
        if assoc_option x local = None then add ()
        else (match get_loc_type x with
            | None ->
                loc_types := (x, t) :: !loc_types
            | Some t' ->
                if t <> t' && coercable t t' then (* We were probably wrong in the first time to guess such a big type. Let's get to something closer. *)
                    loc_types := (x, t) :: List.remove_assoc x !loc_types
                else shouldbecoercable t' t)
    | _ -> add ()

let rec learn_type location local e t =
    let identifer_to_avoid = [
            "Some" ; "None" ;
            "nil" ; "length" ;
            "binds" ; "indom" ; "empty" ; "write"
    ] in
    match e, t with
    | Ident (_, m, x), _ ->
        if not (List.mem x identifer_to_avoid) then
            add_def_type (location ^ " (while typing " ^ string_of_expr e ^ ")") local (m, x) t
    | Couple (e1, e2), Prod_type (t1, t2) ->
        learn_type location local e1 t1 ;
        learn_type location local e2 t2
    | _ -> () (* This is just a script, it hasn't to be complete :-) *)

let rec type_expr location local : expr -> expr * ctype option = function
    | Ident (true, m, x) as e ->
        (e, None) (* At least for now. *)
    | Ident (false, m, x) as e ->
        (e, match if m = None then var_type x else None with
        | Some t -> Some t
        | None ->
            match
              match if m = None then assoc_option x local else None with
              | Some (Some t) -> Some t
              | Some None -> None
              | None -> assoc_option (m, x) !def_types with
            | Some t -> Some t
            | None -> (* A last chance try... *)
                match List.rev (char_list_of_string (normalise_var_name x)) with
                | 's' :: l -> (
                    let x' = string_of_char_list (List.rev l) in
                    match var_type x' with
                    | Some t -> Some (App_type (Basic_type (None, "list"), t))
                    | None -> None)
                | _ -> None)
    | App (Ident (false, m, "length"), None, e2) ->
        let (e2, t) = type_expr location local e2 in
        (App (Ident (false, m, "length"), None, e2),
            Some (Basic_type (None, "nat")))
    | App (Ident (false, m, "binds"), None, e2) ->
        let (e2, t) = type_expr location local e2 in
        (App (Ident (false, m, "binds"), None, e2),
            match t with
            | Some (App_type (App_type (Basic_type (Some "Heap", "heap"), t1), t2)) ->
                Some (Fun_type (t1, Fun_type (t2, Prop)))
            | Some (Basic_type (None, "decl_env_record")) ->
                Some (Fun_type (Basic_type (None, "string"),
                    Fun_type (Prod_type (Basic_type (None, "mutability"), Basic_type (None, "value")), Prop)))
            | Some (Basic_type (None, "object_properties_type")) ->
                Some (Fun_type (Basic_type (None, "prop_name"),
                    Fun_type (Basic_type (None, "attributes"), Prop)))
            | Some t -> None
            | None -> None)
    | App (Ident (false, m, "indom"), None, e2) ->
        let (e2, t) = type_expr location local e2 in
        (App (Ident (false, m, "indom"), None, e2),
            match t with
            | Some (App_type (App_type (Basic_type (Some "Heap", "heap"), t1), t2)) ->
                Some (Fun_type (t1, Prop))
            | Some (Basic_type (None, "decl_env_record")) ->
                Some (Fun_type (Basic_type (None, "string"), Prop))
            | Some (Basic_type (None, "object_properties_type")) ->
                Some (Fun_type (Basic_type (None, "prop_name"), Prop))
            | Some t -> None
            | None -> None)
    | App (Ident (false, m, "write"), None, e2) ->
        let (e2, t) = type_expr location local e2 in
        (App (Ident (false, m, "write"), None, e2),
            match t with
            | Some (App_type (App_type (Basic_type (Some "Heap", "heap"), t1), t2) as th) ->
                Some (Fun_type (t1, Fun_type (t2, th)))
            | Some (Basic_type (None, "decl_env_record") as th) ->
                Some (Fun_type (Basic_type (None, "string"),
                    Fun_type (Prod_type (Basic_type (None, "mutability"), Basic_type (None, "value")), th)))
            | Some (Basic_type (None, "object_properties_type") as th) ->
                Some (Fun_type (Basic_type (None, "prop_name"),
                    Fun_type (Basic_type (None, "attributes"), th)))
            | Some t -> None
            | None -> None)
    | App (e1, internal, e2) ->
        let (e1, t1) = type_expr location local e1 in
        let (e2, _) = type_expr location local e2 in
        (match t1 with
        | Some (Fun_type (t1, t2)) ->
            learn_type location local e2 t1 ;
            (App (e1, internal, Cast (e2, t1)), Some t2)
        | _ -> (App (e1, internal, e2), None))
    | Binop ((Add | Sub | Mult) as op, e1, e2) ->
        (match type_expr location local e1, type_expr location local e2 with
        | (e1, Some t), (e2, _) ->
            learn_type location local e2 t ;
            (Binop (op, e1, Cast (e2, t)), Some t)
        | (e1, _), (e2, Some t) ->
            learn_type location local e1 t ;
            (Binop (op, Cast (e1, t), e2), Some t)
        | (e1, _), (e2, _) ->
            (Binop (op, e1, e2), None))
    | Binop ((And | Or) as op, e1, e2) ->
        learn_type location local e1 Prop ;
        learn_type location local e2 Prop ;
        (Binop (op, Cast (e1, Prop), Cast (e2, Prop)), Some Prop)
    | Binop ((Band | Bor) as op, e1, e2) ->
        let boolt = Basic_type (None, "bool") in
        learn_type location local e1 boolt ;
        learn_type location local e2 boolt ;
        (Binop (op, Cast (e1, boolt), Cast (e2, boolt)), Some boolt)
    | Binop ((Inf | Infeq | Sup | Supeq | Eq | Neq) as op, e1, e2) ->
        (match type_expr location local e1, type_expr location local e2 with
        | (e1, Some t), (e2, _) ->
            learn_type location local e2 t ;
            (Binop (op, e1, Cast (e2, t)), Some Prop)
        | (e1, _), (e2, Some t) ->
            learn_type location local e1 t ;
            (Binop (op, Cast (e1, t), e2), Some Prop)
        | (e1, _), (e2, _) ->
            (Binop (op, e1, e2), Some Prop))
    | Binop (Lcons, e1, e2) ->
        (match type_expr location local e1, type_expr location local e2 with
        | (e1, Some t), (e2, _) ->
            let tl = App_type (Basic_type (None, "list"), t) in
            learn_type location local e2 tl ;
            (Binop (Lcons, e1, Cast (e2, tl)), Some tl)
        | (e1, _), (e2, Some (App_type (Basic_type (None, "list"), t) as tl)) ->
            learn_type location local e1 t ;
            (Binop (Lcons, Cast (e1, t), e2), Some tl)
        | (e1, _), (e2, _) ->
            (Binop (Lcons, e1, e2), None))
    | Binop (Scons, e1, e2) ->
        (match type_expr location local e1, type_expr location local e2 with
        | (e1, Some t), (e2, _) ->
            let tl = App_type (Basic_type (None, "stream"), t) in
            learn_type location local e2 tl ;
            (Binop (Scons, e1, Cast (e2, tl)), Some tl)
        | (e1, _), (e2, Some (App_type (Basic_type (None, "stream"), t) as tl)) ->
            learn_type location local e1 t ;
            (Binop (Scons, Cast (e1, t), e2), Some tl)
        | (e1, _), (e2, _) ->
            (Binop (Scons, e1, e2), None))
    | Binop (Lapp, e1, e2) ->
        (match type_expr location local e1, type_expr location local e2 with
        | (e1, Some t), (e2, _) ->
            learn_type location local e2 t ;
            (Binop (Lapp, e1, Cast (e2, t)), Some t)
        | (e1, _), (e2, Some t) ->
            learn_type location local e1 t ;
            (Binop (Lapp, Cast (e1, t), e2), Some t)
        | (e1, _), (e2, _) ->
            (Binop (Lapp, e1, e2), None))
    | Binop (Llast, e1, e2) ->
        (match type_expr location local e2, type_expr location local e1 with
        | (e2, Some t), (e1, _) ->
            let tl = App_type (Basic_type (None, "list"), t) in
            learn_type location local e1 tl ;
            (Binop (Llast, Cast (e1, tl), e2), Some tl)
        | (e2, _), (e1, Some (App_type (Basic_type (None, "list"), t) as tl)) ->
            learn_type location local e2 t ;
            (Binop (Llast, e1, Cast (e2, t)), Some tl)
        | (e2, _), (e1, _) ->
            (Binop (Llast, e1, e2), None))
    | Unop (Not, e) ->
        let (e, _) = type_expr location local e in
        learn_type location local e Prop ;
        (e, Some Prop)
    | Couple (e1, e2) ->
        (match type_expr location local e1, type_expr location local e2 with
        | (e1, Some t1), (e2, Some t2) ->
            (Couple (e1, e2), Some (Prod_type (t1, t2)))
        | _ -> (Couple (e1, e2), None))
    | String _ as e -> e, Some (Basic_type (None, "string"))
    | Int _ as e -> e, Some (Basic_type (None, "int"))
    | Nat _ as e -> e, Some (Basic_type (None, "nat"))
    | Forall _ as e -> e, Some Prop
    | Exists _ as e -> e, Some Prop
    | Expr_type _ as e -> e, Some Prop
    | Wildcard -> Wildcard, None
    | Match (e, l) -> (* This is just a script, it hasn't to be complete :-) *)
        let l =
            List.map (fun (p, e) -> p, fst (type_expr location local e)) l in
        (Match (e, l),
            match l with
            | [] -> None
            | (_, e) :: _ -> snd (type_expr location local e))
    | Ifthenelse (e1, e2, e3) as e ->
        let e1 = fst (type_expr location local e1) in
        (match type_expr location local e2, type_expr location local e3 with
        | (e2, Some t1), (e3, Some t2) ->
            if coercable t1 t2
            then (Ifthenelse (e1, Cast (e2, t2), e3), Some t2)
            else if coercable t2 t1
            then (Ifthenelse (e1, e2, Cast (e3, t1)), Some t1)
            else (match research_common t1 t2 with
                 | Some t ->
                    (Ifthenelse (e1, Cast (e2, t), Cast (e3, t)), Some t)
                 | None ->
                    prerr_endline ("Warning: Unable to infer the return type of " ^ string_of_expr e ^ location ^ ". It will be supposed to be " ^ string_of_type t1 ^ " and the type " ^ string_of_type t2 ^ " will be assumed to be coercable to it.") ;
                    add_coercion t2 t1 (fun e -> Cast (e, t1)) ;
                    (Ifthenelse (e1, e2, Cast (e3, t1)), Some t1))
        | (e2, Some t), (e3, _) ->
            learn_type location local e3 t ;
            Ifthenelse (e1, e2, Cast (e3, t)), Some t
        | (e2, _), (e3, Some t) ->
            learn_type location local e2 t ;
            Ifthenelse (e1, Cast (e2, t), e3), Some t
        | (e2, _), (e3, _) ->
            Ifthenelse (e1, e2, e3), None)
    | Expr_record l ->
        let l =
            List.map (fun (x, e) ->
                (x, fst (type_expr location local e))) l
        in
        (Expr_record l, match l with
        | [] -> None
        | (x, _) :: _ ->
            match type_expr location local (Ident (false, None, x)) with
            | _, Some (Fun_type (t1, t2)) -> Some t1
            | _ -> None)
    | Function (l, e) ->
        let rec aux local = function
        | [] -> type_expr location local e
        | (x, Some t) :: l ->
            (match aux ((x, Some t) :: local) l with
            | e, None -> e, None
            | e, Some t' -> e, Some (Fun_type (t, t')))
        | (x, None) :: l ->
            match var_type x with
            | None -> e, None
            | Some t -> aux local ((x, Some t) :: l)
        in aux local l
    | Cast (e, t) as e0 ->
        learn_type location local e t ;
        e0, Some t

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
        match complete_local l with
        | None -> None
        | Some l ->
            match get_loc_type x with
            | None ->
                (match var_type x with
                | None -> None
                | Some t -> Some ((x, t) :: l))
            | Some t -> Some ((x, t) :: l)

let type_from_complete_local =
    List.fold_left (fun rt (x, t) ->
        Fun_type (t, rt))

let fetchcoerciondefs = function
    | File_hypothesis h ->
        (match add_argument_types h.hyp_type h.hyp_arguments with
        | None -> ()
        | Some t -> learn_type (" in Hypothesis " ^ h.hyp_name) [] (Ident (false, None, h.hyp_name)) t)
    | File_definition d ->
        let local = get_local d.arguments in
        reset_loc_types () ;
        let add t =
            match complete_local local with
            | Some l ->
                let t = type_from_complete_local t l in
                learn_type (" in Definition " ^ d.def_name) [] (Ident (false, None, d.def_name)) t ;
                if d.is_coercion then (
                    match t with
                    | Prod_type (t1, t2) ->
                        let convert =
                            let rec aux = function
                                | [] -> fun e -> App (d.body, None, e)
                                | (_, _, true) :: l -> aux l
                                | (x, _, false) :: _ ->
                                    fun e -> replace_ident x e d.body
                            in aux d.arguments
                        in add_coercion t1 t2 convert
                    | _ -> ())
            | None -> () in
        (match d.def_type with
        | Some t ->
            learn_type (" in Definition " ^ d.def_name) local d.body t ;
            add t
        | None ->
            match type_expr (" in Definition " ^ d.def_name) local d.body with
            | e, Some t -> add t
            | e, None -> ()) ;
        (match convert_to_type d.body with (* Maybe it's just a shortcut for a type. *)
        | Some t ->
            let t0 = Basic_type (None, d.def_name) in
            if d.arguments = [] && d.def_type = None then (
                add_coercion t0 t (fun e -> Cast (e, t)) ;
                add_coercion t t0 (fun e -> Cast (e, t0)))
        | None -> ())
    | File_coercion c ->
        add_coercion c.coercion_from c.coercion_to
            (fun e -> App (Ident (false, None, c.coercion_name), None, e))
    | File_record r ->
        reset_loc_types () ;
        List.iter (fun (x, t) ->
            learn_type (" in Record " ^ r.record_name) [] (Ident (false, None, x))
                (Fun_type (Basic_type (None, r.record_name), t))) r.record_inner ;
        (match r.record_make with
        | Some make ->
            let t =
                List.fold_left (fun t0 (x, t) ->
                        Fun_type (t, t0))
                    (Basic_type (None, r.record_name)) (List.rev r.record_inner) in
            learn_type (" in Record " ^ r.record_name) [] (Ident (false, None, make)) t
        | None -> ())
    | File_reductions rl ->
        let fetchrule red_name (r : rule) =
            reset_loc_types () ;
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
                        learn_type (" in Rule " ^ r.rule_name) [] (Ident (false, None, r.rule_name))
                            (Basic_type (None, red_name))
                | Some t ->
                    learn_type (" in Rule " ^ r.rule_name) [] (Ident (false, None, r.rule_name)) t)
        in
        reset_loc_types () ;
        List.iter (fun (r : red) ->
            if r.red_params = [] then
                (match r.red_type with
                | Some t ->
                    learn_type (" in Reduction " ^ r.red_name) [] (Ident (false, None, r.red_name)) t
                | None -> ()) ;
            List.iter (fetchrule r.red_name) r.rules) rl
    | File_implicit_type (x, t) ->
        (match assoc_option x !implicit_types with
        | None -> implicit_types := (x, t) :: !implicit_types
        | Some t' ->
            if not (coercable t t' && coercable t' t) then (
                prerr_endline ("Warning: The implicit type for " ^ x ^ " has been declared as both " ^ string_of_type t ^ " and " ^ string_of_type t' ^ ". Assuming these two types are equals.") ;
                add_coercion t t' (fun e -> Cast (e, t')) ;
                add_coercion t' t (fun e -> Cast (e, t))
            ))
    | _ -> ()

