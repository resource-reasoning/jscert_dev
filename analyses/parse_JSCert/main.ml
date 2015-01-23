
let _ =
    let lexbuf = Lexing.from_channel (open_in "test.v"(*"../../coq/JsPrettyRules.v"*)) in
    (*let l = Parser.lex_list Lexer.token lexbuf in
    List.iter print_endline l ;*)
    let f = Parser.main Lexer.token lexbuf in
    ignore f

