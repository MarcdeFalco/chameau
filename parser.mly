%token <int> INT
%token <string> ID
%token <float> FLOAT
%token UMINUS
%token PLUS MINUS TIMES DIV POW PIPE SQRT
%token LPAREN RPAREN LBRACKET RBRACKET LACCO RACCO COMMA SEMICOLON COLON
%token FOR TO DO DONE LET EQUALS IF THEN ELSE REC FUN ARROW LEFTARROW IN
%token EOF

%left PLUS MINUS        /* lowest precedence */
%left TIMES DIV         /* medium precedence */
%left POW
%nonassoc UMINUS        /* highest precedence */

%{
open Nakedterm

exception ParserInconsistency

let rec appize l = match l with
    | [] -> raise ParserInconsistency
    | [x] -> x
    | t::q -> TmApp(appize q, t)
%}

%start <Nakedterm.t> main
%%

main: t = stmt EOF { t }

stmt: t = term { t }

term: 
| t = base_term PLUS s = base_term { TmBinOp (Commonterm.OPlus, t, s) }
(* | t = base_term COLON COLON q = base_term { TmCons("Cons", [t;q]) } *)
| l = nonempty_list(base_term) { appize(List.rev l) }
| l = separated_nonempty_list(COMMA, base_term) { TmTuple l }

base_term : v = ID { TmVar v }
| LPAREN t = term RPAREN { t }
| FUN v = ID ARROW t = term { TmAbs (v,t) }
(*| FUN v = ID COLON ty = typ ARROW t = term { TmAbs (v,Some ty,t) }*)
| n = INT { TmInt n }
| LET v = ID EQUALS tv = term IN t = term { TmLet(v,tv,t) }
| LBRACKET RBRACKET { TmBase "Nil" }

(*
stmt: 
| LET i = ID arg = list(prpattern) EQUALS body = expr { SLet(i,arg,body) }
| LET REC i = ID arg = list(prpattern) EQUALS body = expr { SLetRec(i,arg,body) }
| e = expr { SEval(e) }

prpattern:
| var = ID { PVar var }
| LPAREN p = pattern RPAREN { p }

pattern:
| l = separated_nonempty_list(COMMA, prpattern) { PTuple l }

expr:
| LPAREN e = expr RPAREN { e }
| var = ID { EVar var }
| i = INT { EInt i }
| f= FLOAT { EFloat f }
| FUN var = ID ARROW e = expr { ELambda (var, e) }
| ef = expr ea = expr { EApp (ef, ea) }
*)
