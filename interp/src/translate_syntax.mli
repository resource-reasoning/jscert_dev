exception CoqSyntaxDoesNotSupport of string
exception Empty_list

val string_to_coq : string -> char list

(* Parser ast into coq ast *)
val exp_to_prog : Parser_syntax.exp -> JsSyntax.prog

(* Call into parser then translate into Coq ast *)
val coq_syntax_from_file : string -> JsSyntax.prog
val coq_syntax_from_string : string -> JsSyntax.prog

