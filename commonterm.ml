type unop = OUMinus
type binop = OPlus | OMinus

let string_of_binop op = 
    match op with
    | OPlus -> "+"
    | OMinus -> "-"
