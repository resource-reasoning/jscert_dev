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

  | "."                                         { DOT }
  | ":"                                         { COLON }
  | "|"                                         { PIPE }
  | "@"                                         { AT }

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

  | ("~"|"¬")                                   { NOT }
  | ("/\\"|"∧")                                 { AND }
  | ("\\/"|"∨")                                 { OR }
  | "&&"                                        { BAND }
  | "||"                                        { BOR }

  | "\"" ([^'"']* as s) "\"" ("%string")?       { STRING s }
  | ['0'-'9']+ as s ("%int" | "%Z")?            { INT (int_of_string s) }

  | "("                                         { LPAR }
  | ")"                                         { RPAR }
  | "{"                                         { LBRACK }
  | "}"                                         { RBRACK }

  | ":="                                        { COLONEQ }
  | ("->"|"→")                                  { ARROW }
  | "=>"                                        { FUNARROW }

  | "forall"                                    { FORALL }
  | "fun"                                       { FUN }
  | ","                                         { COMMA }

  | "Require"                                   { REQUIRE }
  | "Export"                                    { EXPORT }
  | "Import"                                    { IMPORT }

  | "Implicit" (blank+) "Type"                  { IMPLICITTYPE }

  | "Inductive"                                 { INDUCTIVE }
  | "with"                                      { WITH }

  | ident as s                                  { IDENT s }

  | eof                                         { EOF }

  | _ as s                                      { failwith ("Unrecognized token: “" ^ String.make 1 s ^ "”" ^ add_pos lexbuf ^ ".") }

and comment = shortest
  | _* "(*"        { comment lexbuf ; comment lexbuf }
  | _* "*)"        { () }
  | _* eof         { failwith ("Unfinished comment" ^ add_pos lexbuf ^ ".") }

