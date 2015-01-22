

let _ =
    let lexbuf = Lexing.from_channel (open_in "../../coq/JsPrettyRules.v") in
    let l = Parser.lex_list Lexer.token lexbuf in
    List.iter print_endline l

