type t = TmVar of string
    | TmAbs of string * t
    | TmApp of t * t
    | TmInt of int
    | TmLet of string * t * t
    | TmBinOp of Commonterm.binop * t * t
    | TmUnOp of Commonterm.unop * t 
    | TmTuple of t list
    | TmBase of string
