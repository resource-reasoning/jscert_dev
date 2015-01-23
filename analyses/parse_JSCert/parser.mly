%{
    open Coq_repr
%}

%token <string> IDENT
%token <string * string> MODULEIDENT
%token DOT COLON PIPE AT
%token STAR ADD SUB EQ NEQ
%token NOT AND OR BAND BOR INF INFEQ SUP SUPEQ
%token LISTCONS LISTAPP LISTLAST
%token <string> STRING
%token <int> INT
%token TYPE PROP
%token LPAR RPAR LBRACK RBRACK
%token COLONEQ ARROW FUNARROW
%token LET IN MATCH END
%token FORALL FUN COMMA
%token OPENSCOPE
%token REQUIRE IMEXPORT
%token IMPLICITTYPE
%token DEFINITION INDUCTIVE WITH
%token EOF

%left     PIPE
%right    ARROW
%left     AND OR
%nonassoc NOT
%nonassoc EQ NEQ
%right    LISTCONS LISTAPP LISTLAST
%left     ADD SUB
%left     STAR
%left     prec_app

%start main lex_list
%type <string list> lex_list
%type <Coq_repr.file_item list> main

%%

main:
      /* empty */
      { [] }
    | REQUIRE IMEXPORT identlist DOT main
      {
          List.map (fun f -> File_import f) $3
          @ $5
      }
    | OPENSCOPE identlist DOT main
      {
          List.map (fun f -> File_scope f) $2
          @ $4
      }
    | IMPLICITTYPE identlist COLON ctype DOT main
      {
          let t = $4 in
          let lt = List.map (fun s -> File_implicit_type (s, t)) $2 in
          lt @ $6
      }
    | DEFINITION IDENT arglist COLONEQ expr DOT main
      {
          let d = {
              def_name = $2 ;
              arguments = $3 ;
              body = $5
          } in
          File_definition d :: $7
      }
    | INDUCTIVE red_list DOT main
      {
          File_reductions $2
          :: $4
      }
    ;

maybe_red_list:
      /* empty */   { [] }
    | WITH red_list { $2 }
    ;

red_list:
    | IDENT COLON ctype COLONEQ rules maybe_red_list
        {
            {
                red_name = $1 ;
                red_params = [] ;
                red_type = $3 ;
                rules = $5
            } :: $6
        }
    | IDENT COLON FORALL arglist COMMA ctype COLONEQ rules maybe_red_list
        {
            {
                red_name = $1 ;
                red_params = $4 ;
                red_type = $6 ;
                rules = $8
            } :: $9
        }
    ;

rules:
      /* empty */   { [] }
    | PIPE IDENT COLON FORALL arglist COMMA lets statement_list rules
      {
          {
              rule_name = $2 ;
              rule_params = List.map (fun (x, t, _) -> (x, t)) $5 ;
              rule_localdefs = $7 ;
              rule_statement_list = $8
          } :: $9
      }
    ;

lets:
      /* empty */                       { [] }
    | LET IDENT COLONEQ expr IN lets    { ($2, $4) :: $6 }
    ;

statement_list:
      expr                      { [$1] }
    | expr ARROW statement_list { $1 :: $3 }
    ;

expr:
    | ident                                                 { let (a, l, x) = $1 in Ident (a, l, x) }
    | LPAR expr RPAR                                        { $2 }
    | LPAR expr COMMA expr RPAR                             { Couple ($2, $4) }
    | expr LPAR IDENT COLONEQ expr RPAR %prec prec_app      { App ($1, Some $3, $5) }
    | expr expr %prec prec_app                              { App ($1, None, $2) }
    | expr binop expr                                       { Binop ($2, $1, $3) }
    | unop expr                                             { Unop ($1, $2) }
    | STRING                                                { String $1 }
    | INT                                                   { Int $1 }
    | LPAR FORALL arglist COMMA expr RPAR                   { Forall (List.map (fun (x, t, _) -> (x, t)) $3, $5) }
    | MATCH expr WITH pattern_list END                      { Match ($2, $4) }
    | MATCH expr WITH expr FUNARROW expr pattern_list END   { Match ($2, ($4, $6) :: $7) }
    ;

pattern_list:
      /* empty */                           { [] }
    | PIPE expr FUNARROW expr pattern_list  { ($2, $4) :: $5 }
    ;

ident:
    | IDENT             { (false, None, $1) }
    | MODULEIDENT       { let (m, x) = $1 in (false, Some m, x) }
    | AT ident          { let (_, l, x) = $2 in (true, l, x) }
    ;

binop:
    | ADD       { Add }
    | SUB       { Sub }
    | STAR      { Mult }
    | AND       { And }
    | OR        { Or }
    | BAND      { Band }
    | BOR       { Bor }
    | INF       { Inf }
    | INFEQ     { Infeq }
    | SUP       { Sup }
    | SUPEQ     { Supeq }
    | LISTCONS  { Lcons }
    | LISTAPP   { Lapp }
    | LISTLAST  { Llast }
    | EQ        { Eq }
    | NEQ       { Neq }
    ;

unop:
    | NOT   { Not }
    ;

arglist:
      /* empty */                               { [] }
    | IDENT arglist                             { ($1, None, false) :: $2 }
    | LPAR identlist COLON ctype RPAR arglist   { List.map (fun x -> (x, Some $4, false)) $2 @ $6 }
    | LBRACK IDENT RBRACK arglist               { ($2, None, true) :: $4 }
    | LBRACK IDENT COLON ctype RBRACK arglist   { ($2, Some $4, true) :: $6 }
    ;

ctype:
    | LPAR ctype RPAR               { $2 }
    | PROP                          { Prop }
    | TYPE                          { Prop }
    | IDENT                         { Basic_type $1 }
    | ctype STAR ctype              { Prod_type ($1, $3) }
    | ctype ARROW ctype             { Fun_type ($1, $3) }
    | ctype ctype %prec prec_app    { App_type ($1, $2) }
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

    | MODULEIDENT               { let (m, x) = $1 in m ^ "." ^ x }
    | IDENT                     { $1 }
    ;

/* For debug purposes */
lex_list:
    | token lex_list            { $1 :: $2 }
    | EOF                       { [] }
    ;

