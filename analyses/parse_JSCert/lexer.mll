{
    open Parser

    let add_pos lexbuf =
        let s = Lexing.lexeme_start lexbuf in
        let e = Lexing.lexeme_end lexbuf in
        " from character " ^ string_of_int s ^ " to character " ^ string_of_int e
}

let blank = [ ' ' '\t' '\n' ]
let letter = [ 'a'-'z' 'A'-'Z' ]
let ident = letter (letter | '_' | ['0'-'9'] | '\'')*

rule token = parse

  (* Ignored parts *)
  | blank+                                      { token lexbuf }
  | "(*"                                        { comment lexbuf ; token lexbuf }
  | "Set Implicit Arguments."                   { token lexbuf }
  | "Implicit Arguments" [^ '.']* '.'           { token lexbuf }
  | ("Lemma" | "Theorem" | "Corollary")         { proof lexbuf ; token lexbuf }

  | "."                                         { DOT }
  | ":"                                         { COLON }
  | "|"                                         { PIPE }
  | "@"                                         { AT }
  | ";"                                         { SEMICOLON }

  | "*"                                         { STAR }
  | "+"                                         { ADD }
  | "-"                                         { SUB }
  | "="                                         { EQ }
  | ("<>"|"≠")                                  { NEQ }
  | "<"                                         { INF }
  | ("<="|"≤")                                  { INFEQ }
  | ">"                                         { SUP }
  | (">="|"≥")                                  { SUPEQ }

  | "::"                                        { LISTCONS }
  | "++"                                        { LISTAPP }
  | "&"                                         { LISTLAST }
  | ":::"                                       { STREAMCONS }

  | ("~"|"¬")                                   { NOT }
  | ("/\\"|"∧")                                 { AND }
  | ("\\/"|"∨")                                 { OR }
  | "&&"                                        { BAND }
  | "||"                                        { BOR }

  | "\"" ([^'"']* as s) "\"" ("%string")?       { STRING s }
  | ['0'-'9']+ as s (blank+ ":" blank+ "int")   { INT (int_of_string s) }
  | ['0'-'9']+ as s                             { NAT (int_of_string s) }

  | "Type"                                      { TYPE }
  | "Prop"                                      { PROP }

  | "("                                         { LPAR }
  | ")"                                         { RPAR }
  | "{"                                         { LBRACK }
  | "}"                                         { RBRACK }

  | ":="                                        { COLONEQ }
  | ("->"|"→")                                  { ARROW }
  | "=>"                                        { FUNARROW }

  | "let"                                       { LET }
  | "in"                                        { IN }
  | "match"                                     { MATCH }
  | "end"                                       { END }
  | "_"                                         { WILDCARD }

  | ("If" | "if" | "ifb")                       { IF }
  | "then"                                      { THEN }
  | "else"                                      { ELSE }

  | "forall"                                    { FORALL }
  | "exists"                                    { EXISTS }
  | "fun"                                       { FUN }
  | ","                                         { COMMA }

  | "Open Scope"                                { OPENSCOPE }
  | "Require"                                   { REQUIRE }
  | ("Export" | "Import")                       { IMEXPORT }

  | "Coercion"                                  { COERCION }
  | ">->"                                       { COERCIONARROW }

  | "Implicit" (blank+) "Type"                  { IMPLICITTYPE }

  | ("Definition" | "Fixpoint")                 { DEFINITION }
  | "Record"                                    { RECORD }
  | "Module"                                    { MODULE }
  | "Notation"                                  { NOTATION }
  | ("Hypothesis" | "Parameter" | "Axiom")      { HYPOTHESIS }
  | "Inductive"                                 { INDUCTIVE }
  | "with"                                      { WITH }

  | (ident as m) "." (ident as x)               { MODULEIDENT (m, x) }
  | ident as s                                  { IDENT s }

  | eof                                         { EOF }

  | _ as s                                      { failwith ("Unrecognized token: “" ^ String.make 1 s ^ "”" ^ add_pos lexbuf ^ ".") }

and comment = shortest
  | _* "(*"        { comment lexbuf ; comment lexbuf }
  | _* "*)"        { () }
  | _* eof         { failwith ("Unfinished comment" ^ add_pos lexbuf ^ ".") }

and proof = shortest
  | _* "Qed."       { () }
  | _* "Admitted."  { () }
  | _* eof          { failwith ("Unfinished proof" ^ add_pos lexbuf ^ ".") }

