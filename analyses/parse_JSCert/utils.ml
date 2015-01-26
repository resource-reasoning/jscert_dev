
let count f =
    List.fold_left (fun i x -> if f x then i + 1 else i) 0


open Pervasives

(** Input/outputs functions **)

let par s = "(" ^ s ^ ")"

let output_endline f s =
    output_string f s ;
    output_string f "\n"

let open_out_coq name =
    let f = open_out name in
    output_endline f "(* This file has been generated automatically by some OCaml scripts. *)" ;
    output_endline f "(* Please do not edit it, or your changes will probably be erased later. *)" ;
    flush f ;
    f

