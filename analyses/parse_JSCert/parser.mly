%{
    open Coq_repr
%}

%token <string> IDENT
%token DOT COLON PIPE AT
%token STAR ADD SUB EQ NEQ
%token NOT AND OR BAND BOR INF INFEQ SUP SUPEQ
%token LISTCONS LISTAPP LISTLAST
%token <string> STRING
%token <int> INT
%token TYPE PROP
%token LPAR RPAR LBRACK RBRACK
%token COLONEQ ARROW FUNARROW
%token FORALL FUN COMMA
%token REQUIRE IMEXPORT
%token IMPLICITTYPE
%token DEFINITION INDUCTIVE WITH
%token EOF

%left     AND OR
%nonassoc NOT
%nonassoc EQ NEQ
%right    LISTCONS LISTAPP LISTLAST
%left     ADD SUB
%left     STAR

%start main lex_list
%type <string list> lex_list
%type <Coq_repr.file> main

%%

main:
      /* empty */
      { {
        imports = [] ;
        implicit_types = [] ;
        definitions = [] ;
        reductions = []
      } }
    | REQUIRE IMEXPORT identlist DOT main
      {
          let f = $5 in
          { f with imports = $3 @ f.imports }
      }
    | IMPLICITTYPE identlist COLON ctype DOT main
      {
          let f = $6 in
          let t = $4 in
          let lt = List.map (fun s -> (s, t)) $2 in
          { f with implicit_types = lt @ f.implicit_types }
      }
    /* TODO: Definitions and reductions. */
    ;

ctype:
    | IDENT                 { Basic_type $1 }
    | ctype STAR ctype      { Prod_type ($1, $3) }
    | ctype ARROW ctype     { Fun_type ($1, $3) }
    ;

identlist:
      /* empty */       { [] }
    | IDENT identlist   { $1 :: $2 }
    ;


token:
    | DOT                       { "." }
    | COLON                     { ":" }
    | PIPE                      { "|" }
    | AT                        { "@" }

    | STAR                      { "*" }
    | ADD                       { "+" }
    | SUB                       { "-" }
    | EQ                        { "=" }
    | NEQ                       { "<>" }
    | INF                       { "<" }
    | INFEQ                     { "<=" }
    | SUP                       { ">" }
    | SUPEQ                     { ">=" }

    | LISTCONS                  { "::" }
    | LISTAPP                   { "++" }
    | LISTLAST                  { "&" }

    | NOT                       { "~" }
    | AND                       { "/\\" }
    | OR                        { "\\/" }
    | BAND                      { "&&" }
    | BOR                       { "||" }

    | STRING                    { "\"" ^ $1 ^ "\"%string" }
    | INT                       { "(" ^ string_of_int $1 ^ ")%Z" }

    | TYPE                      { "Type" }
    | PROP                      { "Prop" }

    | LPAR                      { "(" }
    | RPAR                      { ")" }
    | LBRACK                    { "{" }
    | RBRACK                    { "}" }

    | COLONEQ                   { ":=" }
    | ARROW                     { "->" }
    | FUNARROW                  { "=>" }

    | FORALL                    { "forall" }
    | FUN                       { "fun" }
    | COMMA                     { "," }

    | REQUIRE                   { "Require" }
    | IMEXPORT                  { "Export" }

    | IMPLICITTYPE              { "Implicit Type" }

    | DEFINITION                { "Definition" }
    | INDUCTIVE                 { "Inductive" }
    | WITH                      { "with" }

    | IDENT                     { $1 }
    ;

/* For debug purposes */
lex_list:
    | token lex_list            { $1 :: $2 }
    | EOF                       { [] }
    ;

