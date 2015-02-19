
open Coq_repr
open Coq_repr_aux
open Utils


type defchange =
    definition * bool (* Definition has changed from original Coq files. *)


let rec change_def_type prefix (name_changes : (string * string) list) : defchange list -> defchange list * (string * string) list =
    let (@@) d (r, l) =
        (d :: r, l) in
    let update_type_names name_changes e =
        List.fold_left (fun e (oldname, newname) ->
            replace_ident oldname (Ident (false, None, newname)) e) e name_changes
    in let update_type_names_type name_changes t =
        List.fold_left (fun t (oldname, newname) ->
            replace_ident_type oldname (Basic_type (None, newname)) t) t name_changes
    in function
    | [] -> ([], [])
    | (d, b) :: dc ->
        match d with
        | Definition_def (x, e) ->
            let e' = update_type_names name_changes e in
            let x' = if b then x else prefix ^ x in
            let name_changes' =
                if e = e' && not b then name_changes else (x, x') :: name_changes in
            (if e = e' then (d, b)
            else (Definition_def (x', e'), true)) @@ change_def_type prefix name_changes' dc
        | Definition_inductive l ->
            let l' =
                List.map (fun i -> { i with
                    inductive_type_constructors =
                        List.map (fun (c, ts) ->
                            (c, List.map (update_type_names_type name_changes) ts)) i.inductive_type_constructors
                }) l in
            let local_changes =
                if l = l' then []
                else List.map (fun i ->
                    (i.inductive_type_name, prefix ^ i.inductive_type_name)) l' in
            let (l', new_changes) =
                if l = l' then (l, [])
                else List.split (List.map (fun i ->
                    ({ i with
                        inductive_type_name = prefix ^ i.inductive_type_name ;
                        inductive_type_constructors =
                            List.map (fun (c, ts) ->
                                (prefix ^ c,
                                    List.map (update_type_names_type local_changes) ts)) i.inductive_type_constructors
                    }, List.map (fun (c, _) -> (c, prefix ^ c)) i.inductive_type_constructors)) l') in
            let name_changes' = local_changes @ List.concat new_changes @ name_changes in
            (Definition_inductive l', l <> l') @@ change_def_type prefix name_changes' dc
        | Definition_record r ->
            let ri' =
                List.map (fun (x, t) ->
                    (x, update_type_names_type name_changes t)) r.record_inner in
            if ri' = r.record_inner
            then (d, b) @@ change_def_type prefix name_changes dc
            else let r' = {
                record_name = prefix ^ r.record_name ;
                record_make =
                    (match r.record_make with
                    | None -> None
                    | Some x -> Some (prefix ^ x)) ;
                record_inner = List.map (fun (x, t) -> (prefix ^ x, t)) ri'
            } in let name_changes' =
                let l = List.map (fun (x, t) -> (x, prefix ^ x)) r.record_inner in
                (r.record_name, prefix ^ r.record_name) ::
                match r.record_make with
                | None -> l
                | Some x -> (x, prefix ^ x) :: l
            in (Definition_record r', true) @@ change_def_type prefix name_changes' dc

