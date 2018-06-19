type ty = TInt 
    | TArr of ty * ty
    | TVar of int
    | TTuple of ty list
    | TRec of (ty -> (string * ty) list)

type info = {
    mutable typ : ty
    }

type t = TmVar of int
    | TmAbs of string * ty option * t
    | TmApp of t * t
    | TmInt of int
    | TmLet of string * t * t
    | TmBinOp of Commonterm.binop * t * t
    | TmUnOp of Commonterm.unop * t 
    | TmTuple of t list
    | TmBase of string
    | TmCApp of string * t

let rec index l x = match l with
      [] -> raise Not_found
    | t::q -> if t = x then 0 else 1 + index q x

let protect b s = if not b then "("^s^")" else s

let simple_ty t = match t with
    | TArr (_,_) -> false
    | TTuple _ -> false
    | _ -> true

let string_of_letter n = "'" ^ String.make 1 (char_of_int (n+int_of_char 'a'))

let rec pp_ty t = match t with
    TInt -> "int"
    | TArr (t1,t2) -> protect (simple_ty t1) (pp_ty t1) ^ " -> " ^ pp_ty t2
    | TVar n -> string_of_letter n
    | TTuple l -> String.concat " * " 
        (List.map (fun t -> protect (simple_ty t) (pp_ty t)) l)

let simple_term t = match t with
    | TmApp (_,_) -> false
    | TmAbs (_,_,_) -> false
    | TmTuple l -> false
    | _ -> true

let rec pp_term gam t = match t with
    | TmVar n -> (try List.nth gam n with Failure _ -> "?")
    | TmAbs (s,None ,t) -> "fun " ^ s ^ " -> " ^ pp_term (s::gam) t
    | TmAbs (s,Some typ,t) -> "fun " ^ s ^ ":" ^ pp_ty typ ^ " -> " ^ pp_term (s::gam) t
    | TmApp (e1,e2) -> protect (simple_term e1) (pp_term gam e1) ^ " "  
        ^ protect (simple_term e2) (pp_term gam e2)
    | TmInt n -> string_of_int n
    | TmBinOp(op,s,t) -> pp_term gam s ^ Commonterm.string_of_binop op ^ pp_term gam t
    | TmLet (s,t1,t2) -> "let " ^ s ^ " = " ^ pp_term gam t1 ^ " in " ^ pp_term (s::gam) t2
    | TmTuple l -> String.concat ", " 
        (List.map (fun t -> protect (simple_term t) (pp_term gam t)) l)
    (*
    | TmCons ("Nil",[]) -> "[]"
    | TmCons ("Cons", [t;q]) -> pp_term gam t ^ "::" ^ pp_term gam q
    *)

let rec ty_max_fv t = match t with
    | TVar n -> n
    | TArr(t1,t2) -> max (ty_max_fv t1) (ty_max_fv t2)
    | TTuple l -> List.fold_left max (-1) (List.map ty_max_fv l)
    | _ -> -1

let rec max_fv t = match t with
    | TmAbs(_,Some typ,t) -> max (ty_max_fv typ) (max_fv t)
    | TmAbs(_,_,t) -> max_fv t
    | TmApp(t1,t2) -> max (max_fv t1) (max_fv t2)
    | TmLet(s,t1,t2) -> max (max_fv t1) (max_fv t2)
    | TmTuple l -> List.fold_left max (-1) (List.map max_fv l)
    | _ -> -1

let from_naked t = 
    let tvar = ref (-1) in
    let rec aux gam t  =
        match t with
        | Nakedterm.TmVar s -> TmVar (index gam s)
        | Nakedterm.TmAbs (s,t) -> 
            (* let nt = incr tvar; !tvar in *)
            TmAbs (s, None, aux (s::gam) t)
        | Nakedterm.TmLet (s,t1,t2) -> 
            TmLet (s,aux gam t1,aux (s::gam) t2)
        | Nakedterm.TmApp (e1,e2) -> TmApp (aux gam e1, aux gam e2)
        | Nakedterm.TmInt n -> TmInt n
        | Nakedterm.TmBinOp (op,s,t) -> TmBinOp(op,aux gam s, aux gam t)
        | Nakedterm.TmUnOp (op,s) -> TmUnOp(op,aux gam s)
        | Nakedterm.TmTuple l -> TmTuple (List.map (aux gam) l)
    in aux [] t
    
let shift t d =
    let rec aux t c = match t with
    | TmVar n -> TmVar (if n < c then n else n+d)
    | TmAbs (s,typ,t) -> TmAbs(s, typ,aux t (c+1))
    | TmApp (t1,t2) -> TmApp(aux t1 c, aux t2 c)
    | TmInt n -> TmInt n
    | TmBinOp(op,s,t) -> TmBinOp(op,aux s c, aux t c)
    | TmLet(s,t1,t2) -> TmLet(s,aux t1 c,aux t2 (c+1))
    | TmTuple l -> TmTuple (List.map (fun t -> aux t c) l)
    in aux t 0

let rec subst t j v = 
    let ts = match t with
    | TmVar k -> if j = k then v else t
    | TmAbs (s,typ,t) -> TmAbs(s, typ, subst t (j+1) (shift v 1))
    | TmApp (t1,t2) -> TmApp(subst t1 j v, subst t2 j v)
    | TmInt n -> TmInt n
    | TmBinOp(op,s,t) -> TmBinOp(op,subst s j v, subst t j v)
    | TmLet(s,t1,t2) -> TmLet(s,subst t1 j v,subst t2 (j+1) (shift v 1))
    | TmTuple l -> TmTuple (List.map (fun t -> subst t j v) l)
    in 
    (* Printf.printf "[%d <- %s]%s -> %s\n" j (pp_term [] v) (pp_term [] t) (pp_term [] ts); *)
    ts

let rec isval ctx t = match t with
    | TmAbs(_,_,_) -> true
    | TmInt _ -> true
    (*| TmCons(_,_) -> true*)
    | TmTuple _ -> true
    | _ -> false

exception HeadNormalForm

let subst_top s t = shift (subst t 0 (shift s 1)) (-1)

let rec one_step_reduce ctx t = match t with
    | TmApp(TmAbs(_, _, t), v) when isval ctx v ->
        subst_top v t 
    | TmApp(t1,t2) when isval ctx t1 -> let t2p = one_step_reduce ctx t2 in
        TmApp(t1, t2p)
    | TmApp(t1,t2) -> let t1p = one_step_reduce ctx t1 in
        TmApp(t1p, t2)
    | TmLet(s,t1,t2) when isval ctx t1 -> subst_top t1 t2
    | TmLet(s,t1,t2) -> let t1p = one_step_reduce ctx t1 in TmLet(s,t1p,t2)
    | TmBinOp(Commonterm.OPlus,TmInt n1, TmInt n2) -> TmInt (n1+n2)
    | TmBinOp(op,t1,t2) when isval ctx t1 -> let t2p = one_step_reduce ctx t2 in
        TmBinOp(op,t1,t2p)
    | TmBinOp(op,t1,t2) -> let t1p = one_step_reduce ctx t1 in
        TmBinOp(op,t1p,t2)
    | _ -> raise HeadNormalForm

let rec reduce ctx t =
    try
        let tp = one_step_reduce ctx t in
        (*Printf.printf "%s ==> %s\n" (pp_term [] t) (pp_term [] tp);*)
        reduce ctx tp
    with HeadNormalForm -> t

exception UnificationFailure

let typer t =
    let fvar = ref (max_fv t) in
    let rec synth ctx t = match t with
        | TmVar n -> (List.nth ctx n, [])
        | TmInt _ -> (TInt, [])
        | TmAbs(s,None,t) -> 
                let nt = incr fvar; !fvar in
                let typt, c = synth (TVar nt::ctx) t in
                Printf.printf "[%s] for %s\n" 
                    (pp_ty (TArr (TVar nt, typt)))
                    (pp_term [] (TmAbs(s,None,t)));
                (TArr (TVar nt,typt), c)
        | TmAbs(s,Some typ,t) -> 
                let typt, c = synth (typ::ctx) t in
                (TArr (typ,typt), c)
        | TmLet(s,t1,t2) -> synth ctx (subst_top t1 t2)
        | TmApp(t1,t2) ->
            let tp1, c1 = synth ctx t1 in
            let tp2, c2 = synth ctx t2 in
            incr fvar;
            Printf.printf "[%s] %s=%s->%s for %s\n" 
                (string_of_letter !fvar)
                (pp_ty tp1)
                (string_of_letter !fvar)
                (pp_ty tp2)
                (pp_term [] (TmApp(t1,t2)));
            (TVar (!fvar), ((tp1,TArr (tp2,TVar (!fvar)))::c1)@c2 )
        | TmBinOp(Commonterm.OPlus,t1,t2) ->
            let tp1, c1 = synth ctx t1 in
            let tp2, c2 = synth ctx t2 in
            (TInt, ((tp1,TInt)::(tp2,TInt)::c1)@c2)
        | TmTuple l ->
            let tpl, cl = List.split (List.map (synth ctx) l) in
            (TTuple tpl, List.fold_left (@) [] cl)
    in let rec fv ty = match ty with
        | TArr(t1,t2) -> (fv t1) @ (fv t2)
        | TVar n -> [n]
        | TTuple l -> List.fold_left (@) [] (List.map fv l)
        | _ -> []
    in let rec t_subst n t ty = match ty with
        | TVar m when n = m -> t
        | TArr (t1,t2) -> TArr (t_subst n t t1, t_subst n t t2)
        | TTuple l -> TTuple (List.map (t_subst n t) l)
        | _ -> ty
    in let rec c_subst n t c = match c with
        | (t1,t2)::cp -> (t_subst n t t1, t_subst n t t2)::(c_subst n t cp)
        | [] -> []
    in let rec unify c = match c with
        | [] -> []
        | (s,t)::cp when s=t -> unify cp
        | (TVar n,t)::cp when not (List.mem n (fv t)) ->
            (n,t)::unify (c_subst n t cp)
        | (s, TVar n)::cp when not (List.mem n (fv s)) ->
            (n,s)::unify (c_subst n s cp)
        | (TArr (s1,s2), TArr(t1,t2))::cp -> unify ((s1,t1)::(s2,t2)::cp)
        | (TTuple l, TTuple q)::cp when List.length l = List.length q ->
            unify ((List.combine l q) @ cp)
        | (s1,s2)::cp -> 
                Printf.printf "UnificationError when processing %s = %s\n"
                    (pp_ty s1) (pp_ty s2);
                raise UnificationFailure
    in
    let tp, c = synth [] t in
    Printf.printf "Typing %s\n" (pp_term [] t);
    Printf.printf "Constraint : %s\n" 
        (String.concat "\n" (List.map (fun (t1,t2) -> pp_ty t1 ^ "\t=\t"^ pp_ty t2) c));
    let l = unify c in
    Printf.printf "Unifier : %s\n" 
        (String.concat "\n" (List.map (fun (n,t) -> string_of_letter n ^ "<-"^ pp_ty t) l));
    let rec apply_unifier t =
        match t with
        | TVar n when List.mem_assoc n l -> apply_unifier (List.assoc n l)
        | TArr (t1,t2) -> TArr (apply_unifier t1, apply_unifier t2)
        | TTuple l -> TTuple (List.map apply_unifier l)
        | _ -> t
    in
    let shorten t =
        let rec once l = match l with
            | [] -> []
            | [x] -> [x]
            | x::y::t -> if x = y then once (x::t) else x :: once (y::t)
        in 
        let fvars = once (List.sort compare (fv t)) in
        let rec aux t = match t with
            | TVar n -> TVar (index fvars n)
            | TArr(t1,t2) -> TArr(aux t1, aux t2)
            | TTuple l -> TTuple (List.map aux l)
            | _ -> t
        in aux t
    in
    shorten (apply_unifier tp)
