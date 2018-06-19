exception Quit
let _ =
    Printf.printf "Chameau - a caml light light interpreter\nEnter a Caml expression on ONE line\nenter quit for quitting\n";
    try
        while true do
            print_string "# ";
            let s = read_line () in
            if s = "quit" then raise Quit;
            let t = Term.from_naked (Parser.main Lexer.token (Lexing.from_string s)) in
            Printf.printf "%s : %s\n%s\n" 
                (Term.pp_term [] t) (Term.pp_ty (Term.typer t))
                (Term.pp_term [] (Term.reduce [] t))
        done
    with Quit -> () 
