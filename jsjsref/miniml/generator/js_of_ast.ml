open Misc
open Asttypes
open Types
open Typedtree
open Longident
open Format
open Print_type
open Location
open Lexing
open Mytools
open Attributes

let hashtlb_size = 256
let type_tbl = Hashtbl.create hashtlb_size;;

let print_tbl () =
  let rec print_str_list = function
    | [] -> ""
    | x :: [] -> (Format.sprintf {|"%s"|} x)
    | x :: xs -> (Format.sprintf {|"%s", |} x) ^ print_str_list xs
  in Hashtbl.iter (fun cstr elems -> Printf.printf ({|%s -> [%s]|} ^^ "\n") cstr (print_str_list elems)) type_tbl; ()

let show_list_f f sep l = l
  |> List.map f
  |> List.fold_left (fun acc x -> acc ^ (if acc = "" then "" else sep) ^ x) ""

let show_list sep l =
  List.fold_left (fun acc x -> acc ^ (if acc = "" then "" else sep) ^ x) "" l

let js_of_constant = function
  | Const_int n -> string_of_int n
  | Const_char c -> String.make 1 c
  | Const_string (s, _) -> "\"" ^ s ^ "\""
  | Const_float f -> f
  | Const_int32 n -> Int32.to_string n
  | Const_int64 n -> Int64.to_string n
  | Const_nativeint n -> Nativeint.to_string n

let js_of_longident loc =
  let res = String.concat "." @@ Longident.flatten loc.txt in
  if res = "()" then "" else res

let ident_of_pat pat = match pat.pat_desc with
  | Tpat_var (id, _) -> Ident.name id
  | _ -> error "functions can't deconstruct values"

let rec js_of_let_pattern pat expr = 
  let expr_type pat expr = match expr.exp_desc with
    | Texp_construct (loc, cd, el) ->
       let value = js_of_longident loc in
       if el = [] then
         if value = "true" || value = "false" then value else Format.sprintf "{type: \"%s}\"" value
       else
         let rec expand_constructor_list fields exprs = match fields, exprs with
           | [], [] -> []
           | [], x :: xs | x :: xs , [] -> failwith "argument lists should have the same length."
           | x :: xs, y :: ys -> Format.sprintf "@[%s:@,%s@]" x y :: expand_constructor_list xs ys in
         let names = Hashtbl.find type_tbl value
         in Format.sprintf "{type: \"%s\",@, %s}" value (show_list ", " (expand_constructor_list names (List.map js_of_expression el)))
    | _ -> string_of_type_exp pat.pat_type in
  let sexpr = js_of_expression expr in
  match pat.pat_desc with
  | Tpat_var (id, _) ->
     Format.sprintf "@[<v 0>var %s = %s;@,@]" (Ident.name id) sexpr
  | Tpat_tuple (pat_l)
  | Tpat_array (pat_l) ->
     let l = List.map (function pat -> match pat.pat_desc with
                                       | Tpat_var (id, _) -> (Ident.name id, string_of_type_exp pat.pat_type)
                                       | _ -> out_of_scope "pattern-matching in arrays") pat_l in
     Format.sprintf "@[<v 0>var __%s = %s;@,@]" "array" sexpr ^
       List.fold_left2 (fun acc (name, exp_type) y -> acc ^ Format.sprintf "@[<v 0>var %s = __%s[%d];@,@]" name "array" y)
                       "" l @@ range 0 (List.length l - 1)
  | _ -> error "let can't deconstruct values"

and js_of_pattern pat obj = match pat.pat_desc with
  | Tpat_any -> "default", ""
  | Tpat_constant c -> js_of_constant c, ""
  | Tpat_var (id, _) -> Ident.name id, ""
  | Tpat_alias (_,_,_) -> out_of_scope "alias-pattern"
  | Tpat_tuple (_) -> out_of_scope "tuple matching"
  | Tpat_construct (loc, cd, el) ->
     let c = js_of_longident loc in
     let spat = Format.sprintf "%s" ("case \"" ^ c ^ "\"") in
     let params = Hashtbl.find type_tbl c in
     let binders =
       if List.length el = 0 then Format.sprintf ""
       else Format.sprintf "%s@," ("var " ^ show_list ", " (List.map2 (fun x y -> x ^ " = " ^ obj ^ "." ^ y) (List.map (fun x -> fst (js_of_pattern x obj)) el) params) ^ ";") in
     spat, binders
  | Tpat_variant (_,_,_) -> out_of_scope "polymorphic variants in pattern matching"
  | Tpat_array (_) -> out_of_scope "array-match"
  | Tpat_record (_,_) -> out_of_scope "record"
  | Tpat_or (_,_,_) -> failwith "not implemented yet"
  | Tpat_lazy (_) -> out_of_scope "lazy-pattern"

and js_of_expression (e:expression) =
  let js_of_branch b obj =
    let spat, binders = js_of_pattern b.c_lhs obj in
    let se = js_of_expression b.c_rhs in
    Format.sprintf "@[<v 2>%s: @[<v 4>%s@,return %s;@]@,@]" spat binders se in
  match e.exp_desc with
  | Texp_ident (_, loc, _) -> js_of_longident loc
  | Texp_constant c -> js_of_constant c
  | Texp_let (_, vb_l, e) ->
     let show_val vb = js_of_let_pattern vb.vb_pat vb.vb_expr in
     let sd = String.concat "\n" @@ List.map show_val @@ vb_l in
     let se = js_of_expression e in
     Format.sprintf
       "@[<v 0>(function () {@,@[<v 4>@,%s@,@,return %s;@,@]@,})()@]" sd se
  | Texp_function (_, c :: [], Total) ->
      let rec explore pats e = match e.exp_desc with
        | Texp_function (_, c :: [], Total) ->
            let p = c.c_lhs
            and e = c.c_rhs in
            explore (p :: pats) e
        | _ -> String.concat ", " @@ List.map ident_of_pat @@ List.rev @@ pats,
               js_of_expression e in
      let names, body = explore [c.c_lhs] c.c_rhs in
      Format.sprintf
        "@[function (%s) {@,@[<v 4>@,return %s;@,@]@,}@]" names body
  | Texp_function (_, _, _) -> out_of_scope "powered-up functions"
  | Texp_apply (f, exp_l) ->
     let sl = exp_l
          |> List.map (fun (_, eo, _) -> match eo with None -> out_of_scope "optional apply arguments" | Some ei -> js_of_expression ei)
          |> String.concat ", " in
     let se = js_of_expression f in
     Format.sprintf "@[<v 0>%s(%s)@]" se sl
  | Texp_match (exp, l, [], Total) ->
     let se = js_of_expression exp in
     let sb = List.fold_left (fun acc x -> acc ^ js_of_branch x se) "" l in
    Format.sprintf "@[<v 0>(function () {@,@[<v 4>@,switch (%s.type) {@,@[<v 4>@,%s@,@]@,}@]@,})()@]" se sb
  | Texp_match (_, _, _, Partial) -> out_of_scope "partial matching"
  | Texp_match (_,_,_,_) -> out_of_scope "matching with exception branches"
  | Texp_try (_, _) -> out_of_scope "exceptions"
  | Texp_tuple (tl) ->
      "["  ^ show_list_f js_of_expression ", " tl ^ "]"
  | Texp_construct (loc, cd, el) -> (*TODO: Modifs*)
        let value = js_of_longident loc in
        if el = [] then
            if value = "true" || value = "false" then value else Format.sprintf "{type: \"%s\"}" value
        else let rec expand_constructor_list fields exprs = match fields, exprs with
          | [], [] -> []
          | [], x :: xs | x :: xs , [] -> failwith "argument lists should have the same length."
          | x :: xs, y :: ys -> (if y = "" then Format.sprintf "%s" x else Format.sprintf "%s: %s" x y) :: expand_constructor_list xs ys
        in let names = Hashtbl.find type_tbl value
        in Format.sprintf "{type: \"%s\", %s}" value (show_list ", " (expand_constructor_list names (List.map js_of_expression el)))
  | Texp_variant (_,_) -> out_of_scope "polymorphic variant"
  | Texp_record (_, _) -> failwith "not implemented yet"
  | Texp_field (_,_,_) -> failwith "not implemented yet"
  | Texp_setfield (_,_,_,_) -> failwith "not implemented yet"
  | Texp_array (exp_l) ->
      "["  ^ show_list_f js_of_expression ", " exp_l ^ "]"
  | Texp_ifthenelse (e1, e2, None) -> Format.sprintf
      "@[<v 0>(function () {@,@[<v 4>@,if (%s) {@,@[<v 4>@,return  %s;@]@,}@]@,})()@]" (js_of_expression e1) (js_of_expression e2)
  | Texp_ifthenelse (e1, e2, Some e3) -> Format.sprintf
     "@[<v 0>(function () {@,@[<v 4>@,if (%s) {@,@[<v 4>@,return  %s;@]@,} else {@,@[<v 4>@,return  %s;@]@,}@]@]@,})()@]"
      (js_of_expression e1) (js_of_expression e2) (js_of_expression e3)
  | Texp_sequence (_, _) -> unsupported "sequences"
  | Texp_while (_, _) -> unsupported "while loops"
  | Texp_for (_,_,_,_,_,_) -> unsupported "for loops"
  | Texp_send (_, _, _) -> out_of_scope "objects"
  | Texp_new (_, _, _) -> out_of_scope "objects"
  | Texp_instvar (_,_,_) -> out_of_scope "objects"
  | Texp_setinstvar (_,_,_,_) -> out_of_scope "objects"
  | Texp_override (_,_) -> out_of_scope "objects"
  | Texp_letmodule (_,_,_,_) -> out_of_scope "local modules"
  | Texp_assert _ -> out_of_scope "assert"
  | Texp_lazy _ -> out_of_scope "lazy expressions"
  | Texp_object (_, _) -> out_of_scope "objects"
  | Texp_pack _ -> out_of_scope "packing"
let rec js_of_structure s = show_list_f js_of_structure_item "\n\n" s.str_items
and js_of_structure_item s = match s.str_desc with
  | Tstr_eval (e, _) -> Format.sprintf "%s" @@ js_of_expression e
  | Tstr_value (_, vb_l)  ->
    let show_val vb = js_of_let_pattern vb.vb_pat vb.vb_expr in
    String.concat "\n\n" @@ List.map show_val @@ vb_l
  | Tstr_type tl ->
   let explore_type = function
      | [] -> ()
      | x :: xs -> (match x.typ_kind with
        | Ttype_variant cdl ->
          let cl = List.map (fun cstr -> extract_cstr_attrs cstr) cdl in
          List.iter (fun (name, cstrs_name) -> Hashtbl.add type_tbl name cstrs_name) cl
        | _ -> unsupported "open types, record and abstract type")
   in explore_type tl; print_tbl (); ""
  | Tstr_primitive _    -> out_of_scope "primitive functions"
  | Tstr_typext _       -> out_of_scope "type extensions"
  | Tstr_exception _    -> out_of_scope "exceptions"
  | Tstr_module _       -> out_of_scope "modules"
  | Tstr_recmodule _    -> out_of_scope "recursive modules"
  | Tstr_modtype _      -> out_of_scope "module type"
  | Tstr_open _         -> out_of_scope "open statements"
  | Tstr_class _        -> out_of_scope "objects"
  | Tstr_class_type _   -> out_of_scope "class types"
  | Tstr_include _      -> out_of_scope "includes"
  | Tstr_attribute _    -> out_of_scope "attributes"
