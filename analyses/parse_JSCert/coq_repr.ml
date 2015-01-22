
type ctype =
    | Basic_type of string
    | Prod_type of ctype * ctype
    | Fun_type of ctype * ctype

type binop = Add | Sub | Mult | And | Or | Band | Bor | Inf | Infeq | Lcons | Lapp | Llast | Eq
type unop = Not

type expr =
    | Ident of string
    | App of bool (* Disable implicit type, like @fun *) * expr * (string * expr) list (* Internal arguments, like (T:=value) *) * expr
    | Binop of binop * expr * expr
    | Unop of unop * expr

type def = {
    def_name : string ;
    arguments : (string * ctype option * bool (* This boolean states that it is marked implicit, like {T} *)) list ;
    body : expr
}

type rule = {
    rule_name : string ;
    rule_params : string list ;
    rule_preconditions : expr list ;
    rule_conclusion : expr
}

type red = {
    red_name : string ;
    red_args : ctype list (* Without the final Prop *) ;
    rules : rule list
}

type file = {
    imports : string list (* Every file imported from the file. *) ;
    implicit_types : (string * ctype) list (* Every implicit type declared *) ;
    definitions : def list (* Every definition of the file *) ;
    reductions : red list (* Every reduction defined in the file (maybe be mutually recursive) *)
}

