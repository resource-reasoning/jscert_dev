
open Coq_repr
open Coq_repr_aux
open Utils


type defchange =
    definition * bool (* Definition has changed from original Coq files. *)


let change_def_type oldname newname : defchange list -> defchange list =
    List.map (fun (d, b) ->
        match d with
        | Definition_def (x, e) ->
            let e' = replace_ident oldname (Ident (false, None, newname)) e in
            if e = e' then d
            else (Definition_def (x, e'), true) (* TODO: Also update its name to avoid conflicts (add the prefix things...) *)
        | Definition_inductive l ->
            let l'
                )

