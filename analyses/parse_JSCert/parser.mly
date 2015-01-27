%{
    open Coq_repr

    let parse_error s =
        prerr_endline ("Parsing error: " ^ s)

    let unrecognized_items l =
        prerr_endline ("Parsing error at character " ^ (string_of_int (symbol_start ()))) ;
        prerr_endline "Here follows what I got from the lexer:" ;
        prerr_endline ("[ " ^ String.concat "; " l ^ " ]") ;
        exit 0
%}

%token <string> IDENT
%token <string * string> MODULEIDENT
%token DOT COLON PIPE AT SEMICOLON
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
%token COERCION COERCIONARROW
%token REQUIRE IMEXPORT
%token IMPLICITTYPE
%token DEFINITION RECORD MODULE NOTATION HYPOTHESIS INDUCTIVE WITH
%token EOF

%nonassoc prec_error
%left     SEMICOLON
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
    | EOF
      { [] }
    | REQUIRE maybeexport identlist DOT main
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
    | DEFINITION IDENT arglist maybetype COLONEQ expr DOT main
      {
          let d = {
              def_name = $2 ;
              arguments = $3 ;
              def_type = $4 ;
              body = $6 ;
              is_coercion = false
          } in
          File_definition d :: $8
      }
    | HYPOTHESIS IDENT arglist COLON ctype DOT main
      {
          let h = {
              hyp_name = $2 ;
              hyp_arguments = $3 ;
              hyp_type = $5
          } in
          File_hypothesis h :: $7
      }
    | COERCION IDENT COLON ctype COERCIONARROW ctype DOT main
      {
          let c = {
              coercion_from = $4 ;
              coercion_to = $6
          } in
          File_coercion c :: $8
      }
    | COERCION IDENT arglist maybetype COLONEQ expr DOT main
      {
          let d = {
              def_name = $2 ;
              arguments = $3 ;
              def_type = $4 ;
              body = $6 ;
              is_coercion = true
          } in
          File_definition d :: $8
      }
    | MODULE IDENT COLONEQ expr DOT main
      { $6 }
    | NOTATION expr COLONEQ expr DOT main
      { $6 }
    | RECORD IDENT COLONEQ maybeident LBRACK record RBRACK DOT main
      {
          let r = {
              record_name = $2 ;
              record_make = $4 ;
              record_inner = $6
          } in
          File_record r :: $9
      }
    | INDUCTIVE red_list DOT main
      {
          File_reductions $2
          :: $4
      }
    | lex_list %prec prec_error     { unrecognized_items $1 }
    ;

maybetype:
      /* empty */       { None }
    | COLON ctype       { Some $2 }
    ;

maybeident:
      /* empty */   { None }
    | IDENT         { Some $1 }
    ;

record:
      /* empty */                           { [] }
    | IDENT COLON ctype                     { [$1, $3] }
    | IDENT COLON ctype SEMICOLON record    { ($1, $3) :: $5 }
    ;

maybeexport:
      /* empty */   { }
    | IMEXPORT      { }
    ;

maybe_red_list:
      /* empty */   { [] }
    | WITH red_list { $2 }
    ;

red_list:
    | IDENT arglist COLON ctype COLONEQ rules maybe_red_list
        {
            {
                red_name = $1 ;
                red_params = $2 ;
                red_type = Some $4 ;
                rules = $6
            } :: $7
        }
    | IDENT arglist COLON FORALL arglist COMMA ctype COLONEQ rules maybe_red_list
        {
            {
                red_name = $1 ;
                red_params = $2 @ $5 ;
                red_type = Some $7 ;
                rules = $9
            } :: $10
        }
    | IDENT arglist COLONEQ rules maybe_red_list
        {
            {
                red_name = $1 ;
                red_params = $2 ;
                red_type = None ;
                rules = $4
            } :: $5
        }
    ;

rules:
    | rulesnopipe       { $1 }
    | rulespipe         { $1 }
    ;

rulespipe:
      /* empty */   { [] }
    | PIPE rulesnopipe  { $2 }
    ;

rulesnopipe:
      /* empty */   { [] }
    | IDENT COLON FORALL arglist COMMA lets statement_list rulespipe
      {
          {
              rule_name = $1 ;
              rule_params = List.map (fun (x, t, _) -> (x, t)) $4 ;
              rule_localdefs = $6 ;
              rule_statement_list = $7
          } :: $8
      }
    | IDENT COLON statement_list rulespipe
      {
          {
              rule_name = $1 ;
              rule_params = [] ;
              rule_localdefs = [] ;
              rule_statement_list = $3
          } :: $4
      }
    | IDENT rulespipe
      {
          {
              rule_name = $1 ;
              rule_params = [] ;
              rule_localdefs = [] ;
              rule_statement_list = []
          } :: $2
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
    | IDENT                         { Basic_type (None, $1) }
    | MODULEIDENT                   { let (m, x) = $1 in Basic_type (Some m, x) }
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
    | SEMICOLON                 { ";" }

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

    | LET                       { "let" }
    | IN                        { "in" }
    | MATCH                     { "match" }
    | END                       { "end" }

    | FORALL                    { "forall" }
    | FUN                       { "fun" }
    | COMMA                     { "," }

    | OPENSCOPE                 { "Open Scope" }
    | REQUIRE                   { "Require" }
    | IMEXPORT                  { "Export" }

    | COERCION                  { "Coercion" }
    | COERCIONARROW             { ">->" }

    | IMPLICITTYPE              { "Implicit Type" }

    | DEFINITION                { "Definition" }
    | RECORD                    { "Record" }
    | MODULE                    { "Module" }
    | NOTATION                  { "Notation" }
    | HYPOTHESIS                { "Hypothesis" }
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

