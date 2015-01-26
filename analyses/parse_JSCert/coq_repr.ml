
type ctype =
    | Prop
    | Basic_type of string
    | Prod_type of ctype * ctype
    | Fun_type of ctype * ctype
    | App_type of ctype * ctype

type binop =
      Add | Sub | Mult
    | And | Or
    | Band | Bor
    | Inf | Infeq | Sup | Supeq
    | Lcons | Lapp | Llast
    | Eq | Neq
type unop = Not

type expr =
    | Ident of bool (* Disable implicit type, like @f *) * string option (* Modules *) * string
    | App of expr * (string option (* Internal arguments, like (T:=value) *)) * expr
    | Binop of binop * expr * expr
    | Unop of unop * expr
    | Couple of expr * expr
    | String of string
    | Int of int
    | Forall of (string * ctype option) list * expr
    | Match of expr (* matched expression *) * (expr (* pattern *) * expr (* result *)) list

type def = {
    def_name : string ;
    arguments : (string * ctype option * bool (* This boolean states that it is marked implicit, like {T} *)) list ;
    body : expr
}

type rule = {
    rule_name : string ;
    rule_params : (string * ctype option) list ;
    rule_localdefs : (string * expr) list (* local let-bindings *) ;
    rule_statement_list : expr list
}

type red = {
    red_name : string ;
    red_params : (string * ctype option * bool) list ;
    red_type : ctype ;
    rules : rule list
}

type file_item =
    | File_import of string (* A file imported from the file. *)
    | File_scope of string (* A scope openned. *)
    | File_implicit_type of (string * ctype) (* An implicit type declared *)
    | File_definition of def (* Every definition of the file *)
    | File_reductions of red list (* Mutually recursive reductions defined in the file. *)


(** Some intermediate forms. **)

type red_pred = {
    red_pred_name : string ;
    red_pred_types : (ctype * bool (* It is an input *)) list
}

let make_red_pred name l = {
    red_pred_name = name ;
    red_pred_types = l
}

type rule1 = {
    rule1_name : string ;
    rule1_params : (string * ctype * bool (* It is an input *)) list ;
    rule1_conditions : expr list ;
    rule1_premisses : expr list ;
    rule1_conclusion : expr
}

