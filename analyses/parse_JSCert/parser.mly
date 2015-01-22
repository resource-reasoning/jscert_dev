%{

%}

%token <string> IDENT
%token DOT COLON PIPE AT
%token STAR ADD SUB EQ NEQ
%token NOT AND OR BAND BOR INF INFEQ SUP SUPEQ
%token LISTCONS LISTAPP LISTLAST
%token <string> STRING
%token <int> INT
%token LPAR RPAR LBRACK RBRACK
%token COLONEQ ARROW FUNARROW
%token FORALL FUN COMMA
%token REQUIRE EXPORT IMPORT
%token IMPLICITTYPE
%token INDUCTIVE WITH
%token EOF

%start lex_list
%type <string list> lex_list

%%

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

    | STRING                    { "String: " ^ $1 }
    | INT                       { "INT: " ^ string_of_int $1 }

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
    | EXPORT                    { "Export" }
    | IMPORT                    { "Import" }

    | IMPLICITTYPE              { "Implicit Type" }

    | INDUCTIVE                 { "Inductive" }
    | WITH                      { "with" }

    | IDENT                     { "Ident: " ^ $1 }
    ;

lex_list:
    | token lex_list            { $1 :: $2 }
    | EOF                       { [] }
    ;

