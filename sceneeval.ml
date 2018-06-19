open Geometry
open Abstractscene

type valeur = Int of int | Float of float | Float3 of float3 

exception TypeError

let foi = float_of_int

let rec eval_expr t e = 
    match e with
    | ConstantInt n -> Int n
    | ConstantFloat f -> Float f
    | EFloat3 (x,y,z) -> 
        Float3 { x = floatize t x; y = floatize t y; z = floatize t z }
    | Id s -> Hashtbl.find t s
    | Norme e -> let v = floatize3 t e in Float (sqrt (v *|* v))
    | Sqrt e -> Float (sqrt (floatize t e))
    | Exp e -> Float (exp (floatize t e))
    | Cos e -> Float (cos (floatize t e))
    | Sin e -> Float (sin (floatize t e))
    | Tan e -> Float (tan (floatize t e))
    | Moins (e1,e2) -> begin
            let ev1 = eval_expr t e1 in
            let ev2 = eval_expr t e2 in
            match ev1, ev2 with
            | Int i1, Int i2 -> Int (i1-i2)
            | Int i, Float f -> Float (foi i-.f)
            | Float f, Int i -> Float (foi i-.f)
            | Float f1, Float f2 -> Float (f1-.f2)
            | Float3 v1, Float3 v2 -> Float3 (v1 -$ v2)
            | _ -> raise TypeError
        end
    | Add (e1,e2) -> begin
            let ev1 = eval_expr t e1 in
            let ev2 = eval_expr t e2 in
            match ev1, ev2 with
            | Int i1, Int i2 -> Int (i1+i2)
            | Int i, Float f -> Float (foi i+.f)
            | Float f, Int i -> Float (foi i+.f)
            | Float f1, Float f2 -> Float (f1+.f2)
            | Float3 v1, Float3 v2 -> Float3 (v1 +$ v2)
            | _ -> raise TypeError
        end
    | Pow (e1,e2) -> begin
            let f1 = floatize t e1 in
            let f2 = floatize t e2 in
            Float (f1 ** f2)
        end
    | Mult (e1,e2) -> begin
            let ev1 = eval_expr t e1 in
            let ev2 = eval_expr t e2 in
            match ev1, ev2 with
            | Int i1, Int i2 -> Int (i1*i2)
            | Int i, Float f -> Float (foi i*.f)
            | Float f, Int i -> Float (foi i*.f)
            | Float f1, Float f2 -> Float (f1*.f2)
            | Float f, Float3 v -> Float3 (f *% v)
            | Float3 v, Float f -> Float3 (f *% v)
            | _ -> raise TypeError
        end
    | Div (e1,e2) -> begin
            let ev1 = eval_expr t e1 in
            let ev2 = eval_expr t e2 in
            match ev1, ev2 with
            | Int i1, Int i2 -> Int (i1/i2)
            | Int i, Float f -> Float (foi i/.f)
            | Float f, Int i -> Float (f/. foi i)
            | Float f1, Float f2 -> Float (f1/.f2)
            | Float3 v, Float f -> Float3 ((1.0/.f) *% v)
            | _ -> raise TypeError
        end
    | Oppose e -> begin
        let ev = eval_expr t e in
        match ev with
        | Int i -> Int (-i)
        | Float f -> Float (-.f)
        | Float3 v -> Float3 { x = -.v.x; y = -.v.y; z = -.v.z }
    end
   and intize t e =
       match eval_expr t e with
       Int i -> i
       | _ -> raise TypeError
   and floatize t e =
    match eval_expr t e with
    Int i -> foi i
    | Float f -> f
    | _ -> raise TypeError
   and floatize3 t e =
    match eval_expr t e with
    | Float3 v -> v
    | Float f -> { x = f; y = f; z = f }
    | Int i -> let f = foi i in
        { x = f; y = f; z = f }

let eval_options t oil =
    let objet_id = ref false in
    let normale = ref false in
    let bvh = ref (-1) in
    List.iter (fun oi ->
        match oi with
        ObjetID -> objet_id := true
        | NormaleMap -> normale := true
        | Bvh k -> bvh := k) oil;
    { Scene.objet_id = !objet_id;
      Scene.normale_map = !normale;
      Scene.bvh_debug = !bvh }

let eval_camera t cil =
    let o = ref { x = 0.0; y = 0.0; z = -100.0 } in
    let d = ref { x = 0.0; y = 0.0; z = 1.0 } in
    let h = ref { x = 0.0; y = 1.0; z = 0.0 } in
    let l = ref (21.6 *. 2.0) in
    let aspect = ref (3.0 /. 4.0) in
    let champ_de_vision = ref (40.0 *. 3.1415 /. 180. ) in
    let anticrenelage = ref 0 in
    let pixels = ref 128 in

    List.iter (fun ci ->
        match ci with
        CIOrigine e -> o := floatize3 t e
        | CIDirection e -> d := floatize3 t e
        | CIRegarde e -> d := (floatize3 t e) -$ !o
        | CIHaut e -> h := floatize3 t e
        | CIChampDeVision e -> 
            champ_de_vision := (floatize t e) *. 3.1415 /. 180.
        | CIAspect e -> aspect := 1.0 /. (floatize t e)
        | CIPixels e -> pixels := intize t e
        | CILargeur e -> l := floatize t e
        | CIAnticrenelage e -> anticrenelage := intize t e)
        cil;

    Camera.cree !o !d !h !aspect !l !champ_de_vision
        !pixels !anticrenelage

let eval_matiere_fonction t f =
    match f with
    Bois (c1,c2,a,f) ->
        Matiere.Bois (floatize3 t c1,
            floatize3 t c2, floatize t a,
            floatize t f)
    | Echiquier (c1,c2,f) ->
        Matiere.Echiquier (floatize3 t c1,
            floatize3 t c2,
            floatize t f)


let eval_matiere_declare t mel = 
    let rd = ref (Matiere.Constante { x = 1.0; y = 1.0; z = 1.0 }) in
    let ra = ref { x = 0.2; y = 0.2; z = 0.2 } in
    let ambiante_definie = ref false in
    let rs = ref ({ x = 1.0; y = 1.0; z = 1.0 }, 10.0) in
    let rr = ref 0.0 in
    let rt = ref 0.0 in

    List.iter (fun me ->
        match me with
        Diffuse d -> rd := Matiere.Constante (floatize3 t d)
        | DiffuseFunc f -> rd := eval_matiere_fonction t f
        | Ambiante a -> ra := floatize3 t a; ambiante_definie := true
        | Speculaire (s,k) -> rs := (floatize3 t s, floatize t k)
        | Reflectivite r -> rr := floatize t r
        | Transparence tr -> rt := floatize t tr) mel;

    {
        Matiere.diffuse = !rd;
        Matiere.ambiante = !ra;
        Matiere.speculaire = !rs;
        Matiere.reflectivite = !rr;
        Matiere.transparence = !rt
    }

let rec reifie f t p =
    match f with
    | Id "x" -> p.x
    | Id "y" -> p.y
    | Id "z" -> p.z
    | Id "t" -> t
    | ConstantFloat v -> v
    | ConstantInt v -> float_of_int v
    | Add (f1,f2) -> reifie f1 t p +. reifie f2 t p
    | Mult (f1,f2) -> reifie f1 t p *. reifie f2 t p
    | Div (f1,f2) -> reifie f1 t p /. reifie f2 t p
    | Moins (f1, f2) ->  reifie f1 t p -. reifie f2 t p
    | Pow (f1, f2) ->  reifie f1 t p ** reifie f2 t p
    | Sqrt f1 -> sqrt (reifie f1 t p)
    | Cos f1 -> cos (reifie f1 t p)
    | Sin f1 -> sin (reifie f1 t p)
    | Tan f1 -> tan (reifie f1 t p)
    | Norme (Id "p")  -> sqrt (p *|* p)
    | Oppose f1 -> -. (reifie f1 t p)
    | _ -> raise TypeError

let eval stmts t_param =
    let t = Hashtbl.create 123 in
    Hashtbl.add t "t" (Float t_param);
    let mt = Hashtbl.create 123 in
    let matiere_defaut = ref (eval_matiere_declare t []) in

    let matierize m = match m with
        None -> !matiere_defaut
        | Some (MatiereDeclaree mel) -> eval_matiere_declare t mel
        | Some (MatiereNommee s) -> Hashtbl.find mt s
    in

    let camera = ref (eval_camera t []) in
    let options = ref (eval_options t []) in

    let rec aux ol ll sl = match sl with
        [] -> (ol,ll)
        | Assign(id,e)::q ->
                let ev = eval_expr t e in
                Hashtbl.add t id ev;
                aux ol ll q
        | AssignMatiere(id,e)::q ->
                let m = eval_matiere_declare t e in
                if id = "defaut"
                then matiere_defaut := m
                else Hashtbl.add mt id m;
                aux ol ll q
        | Lumiere (e,c)::q -> 
            let e = floatize3 t e in
            let c = floatize3 t c in
            aux ol ({ Scene.position = e; Scene.couleur = c } :: ll) q
        | Aabb(xlow,xhigh,ylow,yhigh,zlow,zhigh)::q  ->
            let aabb = {
                Objet.primitive = Primitive.Aabb {
                    Aabb.xlow = xlow;
                    Aabb.xhigh = xhigh;
                    Aabb.ylow = ylow;
                    Aabb.yhigh = yhigh;
                    Aabb.zlow = zlow;
                    Aabb.zhigh = zhigh
                }; 
                Objet.matiere = !matiere_defaut
            } 
            in aux (aabb::ol) ll q

        | Mandelbulb(p,low,high,m)::q ->
            let m = matierize m in
            let low = floatize3 t low in
            let high = floatize3 t high in
            let p = intize t p in
            let aabb = {
                    Aabb.xlow = low.x;
                    Aabb.xhigh = high.x;
                    Aabb.ylow = low.y;
                    Aabb.yhigh = high.y;
                    Aabb.zlow = low.z;
                    Aabb.zhigh = high.z
                } in
            let cdd = { Objet.primitive = Primitive.ChampDeDistance {
                Champdedistance.aabb = aabb;
                Champdedistance.fonction = Mandelbulb.champdedistance p
                };  Objet.matiere = m } in
            aux (cdd::ol) ll q

        | ChampDeDistance(f,low,high,m)::q ->
            let m = matierize m in
            let low = floatize3 t low in
            let high = floatize3 t high in
            let aabb = {
                    Aabb.xlow = low.x;
                    Aabb.xhigh = high.x;
                    Aabb.ylow = low.y;
                    Aabb.yhigh = high.y;
                    Aabb.zlow = low.z;
                    Aabb.zhigh = high.z
                } in
            let cdd = { Objet.primitive = Primitive.ChampDeDistance {
                Champdedistance.aabb = aabb;
                Champdedistance.fonction = reifie f t_param
                };  Objet.matiere = m } in
            aux (cdd::ol) ll q

        | Implicite(f,low,high,m)::q ->
            let m = matierize m in
            let low = floatize3 t low in
            let high = floatize3 t high in
            let aabb = {
                    Aabb.xlow = low.x;
                    Aabb.xhigh = high.x;
                    Aabb.ylow = low.y;
                    Aabb.yhigh = high.y;
                    Aabb.zlow = low.z;
                    Aabb.zhigh = high.z
                } in
            let imp = { Objet.primitive = Primitive.Implicite {
                Implicite.aabb = aabb;
                Implicite.fonction = reifie f t_param
                };  Objet.matiere = m } in
            aux (imp::ol) ll q
        | Triangle(pl,nlo,m)::q ->
            let l3t3 l = match l with
                [x;y;z] -> (x,y,z)
                | _ -> raise TypeError in
            let (a,b,c) = l3t3 pl in
            let a = floatize3 t a in
            let b = floatize3 t b in
            let c = floatize3 t c in
            let na,nb,nc = match nlo with
                None -> let n = normalize ((b -$ a) ^$ (c -$ a)) in
                    (n,n,n)
                | Some l -> 
                        l3t3 (List.map 
                            (fun n -> normalize (floatize3 t n)) l) in
            let m = matierize m in
            let triangle = {
                Objet.primitive = Primitive.Triangle {
                    Triangle.p1 = a;
                    Triangle.p2 = b;
                    Triangle.p3 = c;
                    Triangle.n1 = na;
                    Triangle.n2 = nb;
                    Triangle.n3 = nc
                };
                Objet.matiere = m
            }
            in aux (triangle::ol) ll q
        | Plan(o,n,m)::q -> begin
            let o = floatize3 t o in
            let n = floatize3 t n in
            let m = matierize m in
            let plan = {
                Objet.primitive = Primitive.Plan {
                    Plan.origine = o;
                    Plan.normale = normalize n
                };
                Objet.matiere = m
            }
            in aux (plan::ol) ll q
        end
        | Sphere(c,r,m)::q -> begin
            let c = floatize3 t c in
            let rf = floatize t r in
            let m = matierize m in
            let sph = {
                Objet.primitive = Primitive.Sphere {
                    Sphere.centre = c;
                    Sphere.rayon = rf
                };
                Objet.matiere = m
            }
            in aux (sph::ol) ll q
        end
        | Mesh(o,tx,tz,n,hf,hmax,m)::q -> begin
            let o = floatize3 t o in
            let tx = floatize t tx in
            let tz = floatize t tz in
            let n = intize t n in
            let hf = reifie hf t_param in
            let hmax = floatize t hmax in
            let m = matierize m in
            let msh = {
                Objet.primitive = Primitive.Mesh {
                    Mesh.origine = o;
                    Mesh.taillex = tx;
                    Mesh.taillez = tz;
                    Mesh.pas = n;
                    Mesh.hauteur = hf;
                    Mesh.hmax = hmax
                };
                Objet.matiere = m
            }
            in aux (msh::ol) ll q
        end
        | For(i,is,ie,sl)::q -> begin
            let isv, iev = eval_expr t is, eval_expr t ie in
            match isv, iev with
            Int is, Int ie ->
                let nol = ref [] in
                let nll = ref [] in
                Hashtbl.add t i (Int 0);
                for compteur = is to ie do
                    Hashtbl.replace t i (Int compteur);
                    let col, cll = aux [] [] sl in
                    nol := col @ !nol;
                    nll := cll @ !nll
                done;
                Hashtbl.remove t i;
                aux (!nol @ ol) (!nll @ ll) q
            | _ -> raise TypeError
        end
        | Camera cil::q -> camera := eval_camera t cil;
                aux ol ll q
        | Options oil::q -> options := eval_options t oil;
                aux ol ll q
    in let ol,ll = aux [] [] stmts in
    Scene.cree !options ol ll !camera

let from_string s t_param =
    let stmts = Parser.main Lexer.token (Lexing.from_string s) in
    eval stmts t_param

