{
  open Parser

  exception Error of string
    
  let keyword_table = Hashtbl.create 72
  let _ =
      List.iter (fun (kwd, tok) -> Hashtbl.add keyword_table kwd tok)
        [ 
            ("for", FOR); ("let", LET);
            ("done", DONE); ("do", DO);
            ("to", TO); ("if", IF);
            ("then", THEN); ("else", ELSE);
            ("rec", REC); ("fun", FUN);
            ("in", IN)
        ]
}

rule token = parse
| "(*" { comments 0 lexbuf }
| [' ' '\t' '\n' '\r']
    { token lexbuf }
| ['0'-'9']+ '.' ['0'-'9']* as f
    { FLOAT (float_of_string f) }
| ['0'-'9']+ as i { INT (int_of_string i) }
| "->" { ARROW }
| "<-" { LEFTARROW }
| '+' { PLUS }
| '-' { MINUS }
| '*' { TIMES }
| '/' { DIV }
| '{' { LACCO }
| '^' { POW }
| '}' { RACCO }
| '(' { LPAREN }
| ')' { RPAREN }
| '[' { LBRACKET }
| ']' { RBRACKET }
| '|' { PIPE }
| ',' { COMMA }
| ':' { COLON }
| ';' { SEMICOLON }
| '=' { EQUALS }
| ['a'-'z' 'A' - 'Z' '_'] ['0'-'9' 'a'-'z' 'A' - 'Z' '_']* as s
    { try Hashtbl.find keyword_table s
      with Not_found -> ID s }
| eof { EOF }
| _
    { raise (Error (Printf.sprintf "At offset %d: unexpected character.\n" (Lexing.lexeme_start lexbuf))) }
and comments level = parse
| "*)" { if level = 0 then token lexbuf else comments (level-1) lexbuf }
| "(*" { comments (level+1) lexbuf }
| _ { comments level lexbuf }
| eof { raise (Error "Non-terminated comment") }
