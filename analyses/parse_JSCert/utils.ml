
let count f =
    List.fold_left (fun i x -> if f x then i + 1 else i) 0

let select_map f =
    List.fold_left (fun l x ->
        match f x with
        | Some r -> r :: l
        | None -> l) []

let find_option f l =
    try Some (List.find f l)
    with Not_found -> None

let assoc_option a l =
    try Some (List.assoc a l)
    with Not_found -> None

let rec cut_last = function
    | [] -> raise Not_found
    | [a] -> ([], a)
    | a :: l ->
        let (l, b) = cut_last l in
        (a :: l, b)


(** Some string manipulations **)

let string_of_char_list cl =
    let s = String.create (List.length cl) in
    let rec set_str n = function
        | [] -> ()
        | c :: tl -> s.[n] <- c; set_str (n+1) tl
    in set_str 0 cl; s

let char_list_of_string s =
    let rec acc_ch acc n =
        if n < 0 then acc else acc_ch ((String.get s n)::acc) (n-1)
    in
    acc_ch [] ((String.length s) - 1)

let normalise_var_name x =
    let rem_char =
        ['0' ; '1' ; '2' ; '3' ; '4' ; '5' ; '6' ; '7' ; '8' ; '9' ; '\'' ; '_'] in
    string_of_char_list (List.filter (fun c -> not (List.mem c rem_char))
        (char_list_of_string x))


let compose f1 f2 x = f1 (f2 x)

let compose_option (f1 : ('b -> 'c) option) (f2 : ('a -> 'b) option) =
    match f1, f2 with
    | Some f1, Some f2 ->
        Some (compose f1 f2)
    | _ -> None


open Pervasives

(** Input/outputs functions **)

let par s = "(" ^ s ^ ")"

let output_endline f s =
    output_string f s ;
    output_string f "\n"

let separate_coq f =
    output_endline f ("\n(" ^ String.make 42 '*' ^ ")\n")

let open_out_coq name =
    let f = open_out name in
    output_endline f "(* This file has been generated automatically by some OCaml scripts. *)" ;
    output_endline f "(* Please do not edit it, or your changes will probably be erased later. *)" ;
    separate_coq f ;
    flush f ;
    f

