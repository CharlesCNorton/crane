(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(*s Conversion functions from Miniml to Minicpp types *)

open Common
open Miniml
open Minicpp
open Names
open Mlutil
open Table
open Str

exception TODO

let contains s1 s2 =
  let re = Str.regexp_string s2 in
  try ignore (Str.search_forward re s1 0); true
  with Not_found -> false

let last : 'a list -> 'a = fun l ->
  let rec aux a l =
    match l with
    | [] -> a
    | b :: l' -> aux b l'
  in
  match l with
  | a :: l' -> aux a l'
  | _ -> raise TODO (* TODO: GET BETTER EXCEPTION *)

let last_two : 'a list -> 'a * 'a = fun l ->
  let rec aux (a, b) l =
    match l with
    | [] -> (a, b)
    | c :: l -> aux (b, c) l
  in
  match l with
  | a :: b :: l' -> aux (a, b) l'
  | _ -> raise TODO (* TODO: GET BETTER EXCEPTION *)

let ml_type_is_void : ml_type -> bool = function
| Tglob (r, _, _) -> is_void r
| _ -> false

let rec convert_ml_type_to_cpp_type env (ns : GlobRef.t list) (tvars : Id.t list) (ml_t : ml_type) : cpp_type =
  match ml_t with
  | Tarr (t1, t2) -> (* FIX *)
        let t1c = convert_ml_type_to_cpp_type env ns tvars t1 in
        let t2c = convert_ml_type_to_cpp_type env ns tvars t2 in
        if isTdummy t1 then t2c else
        (match t2c with
        | Tfun (l, t) -> Tfun (t1c::l, t)
        | _ -> Tfun (t1c::[], t2c))
  | Tglob (g, _, _) when is_void g -> Tvoid
  | Tglob (g, ts, args) when is_custom g ->
    Tglob (g, List.map (convert_ml_type_to_cpp_type env ns tvars) ts, List.map (gen_expr env) args)
  | Tglob (g, ts, _) ->
      let core = Tglob (g, List.map (convert_ml_type_to_cpp_type env ns tvars) ts, []) in
      (match g with
      | GlobRef.IndRef _ -> if List.exists (Environ.QGlobRef.equal Environ.empty_env g) ns then Tshared_ptr core
      else if not (get_record_fields g == []) then Tshared_ptr core
      else Tshared_ptr (Tnamespace (g, core))
      | _ -> core)
  | Tvar i -> (try Tvar (i, Some (List.nth tvars (pred i)))       (* TODO: probs fix/cleanup *)
                              with Failure _ -> Tvar (i, None))
  | Tvar' i ->  (try Tvar (i, Some (List.nth tvars (pred i)))       (* TODO: probs fix/cleanup *)
                              with Failure _ -> Tvar (i, None))
  | Tstring -> assert false (* TODO: get rid of Tstring in both ASTs *)
  | Tmeta {contents = Some t} -> convert_ml_type_to_cpp_type env ns tvars t
  (* | _ -> Tunknown *)
  | Tmeta {id = i} -> Tglob (GlobRef.VarRef (Id.of_string ("meta" ^ string_of_int i)), [], [])
  | Tdummy Ktype -> Tglob (GlobRef.VarRef (Id.of_string ("dummy_type")), [], [])
  | Tdummy Kprop -> Tglob (GlobRef.VarRef (Id.of_string ("dummy_prop")), [], [])
  | Tdummy (Kimplicit _) -> Tglob (GlobRef.VarRef (Id.of_string ("dummy_implicit")), [], [])
  | Tunknown -> Tglob (GlobRef.VarRef (Id.of_string "unknown"), [], [])
  | Taxiom -> Tglob (GlobRef.VarRef (Id.of_string ("axiom")), [], [])
  (*
      let _ = print_endline "TODO: TMETA OR TDUMMY OR TUNKNOWN OR TAXIOM"  in
      assert false *)

(* TODO: when an MLGlob has monadic type, needs to be funcall *)
and gen_expr env (ml_e : ml_ast) : cpp_expr =
  match ml_e with
  | MLrel i -> (try (CPPvar (get_db_name i env)) with Failure _ -> CPPvar' i)
  | MLapp (MLmagic t, args) -> gen_expr env (MLapp (t, args))
  | MLapp (MLglob (r, _), a1 :: l) when is_ret r ->
    let t = last (a1 :: l) in
    gen_expr env t
  (* | MLapp (MLglob (h, _), a1 :: a2 :: l) when is_hoist h ->
    gen_expr env (MLapp (a1, a2::[])) *)
  | MLapp (f, args) ->
    eta_fun env f args
  | MLlam _ as a ->
      let args,a = collect_lams a in
      let args,env = push_vars' (List.map (fun (x, y) -> (id_of_mlid x, y)) args) env in
      let args = List.filter (fun (_,ty) -> not (isTdummy ty)) args in (* TODO: this could cause issues. TEST. *)
      let args = List.map (fun (id, ty) -> (convert_ml_type_to_cpp_type env [] [] ty, Some id)) args in
      let f = CPPlambda (args, None, gen_stmts env (fun x -> Sreturn x) a) in
      (match args with
      | [] -> CPPfun_call (f, [])
      | _ -> f)
  | MLglob (x, tys) when is_inline_custom x ->
      let ty = find_type x in
      let ty = convert_ml_type_to_cpp_type env [] [] ty in
      (match ty with
      | Tfun (dom, cod) -> eta_fun env (MLglob (x, tys)) [] (* TODO: cound be only if contains '%' *)
      | _ -> CPPglob (x, List.map (convert_ml_type_to_cpp_type env [] []) tys))
  | MLglob (x, tys) -> CPPglob (x, List.map (convert_ml_type_to_cpp_type env [] []) tys)
  | MLcons (ty, r, ts) when is_custom r ->
    let args = List.rev_map (gen_expr env) ts in
    let app x = (match args with
      | [] -> x
      | _ -> CPPfun_call(x, args)) in
    (match ty with
    | Tglob (n, tys, _) ->
      let temps = List.map (convert_ml_type_to_cpp_type env [] []) tys in
      app (CPPglob (r, temps))
    | _ -> app (CPPglob (r, [])))
  | MLcons (ty, r, ts) ->
    let fds = record_fields_of_type ty in
    (match fds with
      | [] ->
      let nstempmod args = (match ty with
      | Tglob (n, tys, _) ->
        let temps = List.map (convert_ml_type_to_cpp_type env [] []) tys in
        CPPnamespace (n, (CPPstructmk (r, temps, args)))
      | _ -> CPPstructmk (r, [], args)) in
      nstempmod (List.map (gen_expr env) ts)
    | _ ->
      let nstempmod args = (match ty with
      | Tglob (n, tys, _) ->
        let temps = List.map (convert_ml_type_to_cpp_type env [] []) tys in
        CPPfun_call (CPPmk_shared (Tglob (n, temps, [])), [CPPstruct (n, temps, args)])
      | _ -> assert false) in
      nstempmod (List.map (gen_expr env) ts))
  | MLcase (typ, t, pv) when is_custom_match pv ->
    let cexp = gen_custom_cpp_case env (fun x -> Sreturn x) typ t pv in
    CPPfun_call (CPPlambda([], None, [cexp]), [])
  (* TODO: SLOPPY and incomplete *)
  | MLcase (typ, t, pv) when not (record_fields_of_type typ == []) && Array.length pv == 1 ->
    let (ids,r,pat,body) = pv.(0) in
    let n = List.length ids in
    (match body with
    | MLrel i when i <= n ->
      let fld = List.nth (record_fields_of_type typ) (n - i) in
      (match fld with
      | Some fld -> CPPget' (gen_expr env t, fld)
      | _ -> CPPstring (Pstring.unsafe_of_string "TODOrecordProj"))
    | MLapp (MLrel i, args) when i <= n ->
      let fld = List.nth (record_fields_of_type typ) (n - i) in
      let _,env' = push_vars' (List.rev_map (fun (x, ty) -> (remove_prime_id (id_of_mlid x), ty)) ids) env in
      (match fld with
      | Some fld -> CPPfun_call (CPPget' (gen_expr env t, fld), List.map (gen_expr env') args)
      | _ -> CPPstring (Pstring.unsafe_of_string "TODOrecordProj"))
    | _ ->
      let _,env' = push_vars' (List.rev_map (fun (x, ty) -> (remove_prime_id (id_of_mlid x), ty)) ids) env in
      let asgns = List.mapi (fun i (id, ty) ->
        let fld = List.nth (record_fields_of_type typ) i in
        let e = (match fld with
          | Some fld -> CPPget' (gen_expr env t, fld)
          | _ -> CPPstring (Pstring.unsafe_of_string "TODOrecordProj")) in
        Sasgn (remove_prime_id (id_of_mlid id), Some (convert_ml_type_to_cpp_type env [] [] ty), e)) ids in
      CPPfun_call (CPPlambda([], None, asgns @ gen_stmts env' (fun x -> Sreturn x) body), []))
      (* TODO: ugly. should better attempt when generating statements! *)
      (* TODO: we don't currently support the fancy thing of pattern matching on record fields at the same time *)
  | MLcase (typ, t, pv) when lang () == Cpp -> gen_cpp_case typ t env pv
  (* | MLcase (typ, t, pv) when lang () == Rust -> gen_rust_case typ t env pv *)
  | MLletin (_, ty, _, _) as a -> CPPfun_call (CPPlambda([], None, gen_stmts env (fun x -> Sreturn x) a), [])
  (*| MLfix _ -> CPPvar (Id.of_string "FIX")*)
  | MLstring s -> CPPstring s
  | MLuint x -> CPPuint x
  | MLparray (elems, def) ->
    let elems = Array.map (gen_expr env) elems in
    let def = gen_expr env def in
    CPPparray (elems, def)
  | MLmagic t -> gen_expr env t
  | MLdummy _ ->
    CPPstring (Pstring.unsafe_of_string "dummy")
  | _ -> raise TODO

and eta_fun env f args =
  let rec get_eta_args dom args =
    match (dom, args) with
    | _::dom, _::args -> get_eta_args dom args
    | _ , _ -> dom in
  match f with
  | MLglob (id , tys) ->
    let args = List.map (gen_expr env) args in
    let ty = find_type id in
    let ty = try (type_subst_list tys ty) with _ -> ty in (* TODO : make less hacky; do a type_subst that can't fail *)
    let ty = convert_ml_type_to_cpp_type env [] [] ty in
    let cglob = CPPglob (id, List.map (convert_ml_type_to_cpp_type env [] []) tys) in
    (match ty with
    | Tfun (dom, cod) ->
      let missing_args = get_eta_args dom args in
      if missing_args == [] then CPPfun_call (cglob, List.rev args) else
      let eta_args = List.mapi (fun i ty -> (Tmod (TMconst, ty), Some (Id.of_string ("_x" ^ string_of_int i)))) missing_args in
      let call_args = args @
         List.mapi (fun i _ -> (CPPvar (Id.of_string ("_x" ^ string_of_int i)))) eta_args in
      CPPlambda (List.rev eta_args, None,[Sreturn (CPPfun_call (cglob, List.rev call_args))])
    | _ ->
      (* print_endline ("NOT A FUN" ^ Pp.string_of_ppcmds (GlobRef.print id) ^ string_of_int (List.length args)) ; *)
      CPPfun_call (cglob, args))
  | _ ->
    let args = List.map (fun x -> (gen_expr env x)) args in
    CPPfun_call (gen_expr env f, List.rev args)

and gen_cpp_pat_lambda env (typ : ml_type) rty cname ids dummies body =
  let constr = match typ with
  | Tglob (r, tys, _) ->
    let temps = List.map (convert_ml_type_to_cpp_type env [] []) tys in
    Tnamespace (r, (Tstruct (cname, temps)))
  | _ -> Tstruct (cname, []) in
  let sname = Id.of_string "_args" in
  let ret = convert_ml_type_to_cpp_type env [] [] rty in
  let asgns =  List.mapi (fun i x ->
      let id = Id.of_string ("_a" ^ string_of_int i) in
      Sasgn (fst x, Some (convert_ml_type_to_cpp_type env [] [] (snd x)), CPPget (CPPglob (GlobRef.VarRef sname, []), id))) (List.rev ids) in
  let asgns = List.filteri (fun i _ -> List.nth dummies i) asgns in
  CPPlambda(
        [(Tmod (TMconst, constr), Some sname)],
        Some ret,
        asgns @ gen_stmts env (fun x -> Sreturn x) body)

and gen_cpp_case (typ : ml_type) t env pv =
  let outer cases x = (CPPfun_call (CPPvisit, CPPderef x :: [CPPoverloaded cases])) in
  let rec gen_cases = function
  | [] -> []
  | (ids,rty,p,t) :: cs ->
    (match p with
    | Pusual r ->
      let ids',env' = push_vars' (List.rev_map (fun (x, ty) -> (remove_prime_id (id_of_mlid x), ty)) ids) env in
      let dummies = List.map (fun (x,_) ->
        match x with
        | Dummy -> false
        | _ -> true) ids in
      (gen_cpp_pat_lambda env' typ rty r ids' dummies t) :: (gen_cases cs)
    | _ -> raise TODO) in
  outer (gen_cases (Array.to_list pv)) (gen_expr env t)

and gen_rust_case (typ : ml_type) t env pv =
  let outer cases x = (CPPmatch (x, cases)) in
  let rec gen_cases = function
  | [] -> []
  | (ids,rty,p,t) :: cs ->
    (match p with
    | Pusual r ->
      let ids',env' = push_vars' (List.rev_map (fun (x, ty) -> (remove_prime_id (id_of_mlid x), ty)) ids) env in
      let temps = begin match typ with
        | Tglob (r, tys, _) -> List.map (convert_ml_type_to_cpp_type env [] []) tys
        | _ -> []
        end in
      let c = begin match ids' with
       | [] -> CPPglob (r, temps)
       | _ -> CPPfun_call(CPPglob (r, temps), List.map (fun (x, _) -> CPPvar x) ids')
       end in
      (c, gen_expr env' t) :: (gen_cases cs)
    | _ -> raise TODO) in
  outer (gen_cases (Array.to_list pv)) (gen_expr env t)

and gen_cpp_custom_body env k rty ids body =
  let ret = convert_ml_type_to_cpp_type env [] [] rty in
  let ids =  List.map (fun (x, ty) -> (x, convert_ml_type_to_cpp_type env [] [] ty)) (List.rev ids) in
  let body = gen_stmts env k body in
  (ids, ret, body)

and gen_custom_cpp_case env k (typ : ml_type) t pv =
  let temps = match typ with
  | Tglob (r, tys, _) ->
    List.map (convert_ml_type_to_cpp_type env [] []) tys
  | _ -> [] in
  let typ = convert_ml_type_to_cpp_type env [] [] typ in
  let t = gen_expr env t in
  let rec gen_cases = function
  | [] -> []
  | (ids,rty,p,t) :: cs ->
    (match p with
    | Pusual r ->
      let ids',env' = push_vars' (List.rev_map (fun (x, ty) -> (remove_prime_id (id_of_mlid x), ty)) ids) env in
      (gen_cpp_custom_body env' k rty ids' t) :: (gen_cases cs)
    | _ -> raise TODO) in
  let cmatch = find_custom_match pv in
  Scustom_case (typ, t, temps, gen_cases (Array.to_list pv), cmatch)

and gen_stmts env (k : cpp_expr -> cpp_stmt) = function
| MLletin (x, t, a, b) ->
  let x' = remove_prime_id (id_of_mlid x) in
  let _,env' = push_vars' [x', t] env in
  if x == Dummy then gen_stmts env' k b else
  let afun v = Sasgn (x', None, v) in
  (* Sasgn (x', Some (convert_ml_type_to_cpp_type env [] [] t), (gen_expr env a)) :: gen_stmts env' k b *)
  let asgn = gen_stmts env afun a in
  begin match asgn with
  | [ Sasgn (x', None, e) ] -> Sasgn (x', Some (convert_ml_type_to_cpp_type env [] [] t), e) :: gen_stmts env' k b
  | _ ->
    Sdecl (x', convert_ml_type_to_cpp_type env [] [] t) :: asgn @ gen_stmts env' k b
  end
| MLapp (MLfix (x, ids, funs), args) ->
  let funs = Array.to_list (Array.map2 (gen_fix env) ids funs) in
  let ids = Array.to_list ids in
  let decls = List.map (fun (id, ty) -> Sdecl (id, convert_ml_type_to_cpp_type env [] [] ty)) ids in
  let ret_ty ty = (match convert_ml_type_to_cpp_type env [] [] ty with
    | Tfun (_,t) -> Some t
    | _ -> None) in
  let defs = List.map2 (fun (id, fty) (args, body) -> Sasgn (id, None, CPPlambda (List.map (fun (id, ty) -> convert_ml_type_to_cpp_type env [] [] ty, Some id) args, ret_ty fty, body))) ids funs in
  let args = List.rev_map (gen_expr env) args in
  decls @ defs @ [k (CPPfun_call (CPPvar (fst (List.nth ids x)), args))]
(* | MLapp (MLglob (h, _), a1 :: a2 :: l) when is_hoist h ->
  gen_stmts env k (MLapp (a1, a2::[])) *)
| MLapp (MLglob (r, _), a1 :: a2 :: l) when is_bind r ->
  let (a, f) = last_two (a1 :: a2 :: l) in
  let a = gen_expr env a in
  let ids',f = collect_lams f in
  let ids,env = push_vars' (List.map (fun (x, ty) -> (remove_prime_id (id_of_mlid x), ty)) ids') env in
  (match ids with
  | (x, ty) :: _ ->
    let ty = convert_ml_type_to_cpp_type env [] [] ty in
    if ty == Tvoid || ty == Tunknown then
      Sexpr a :: gen_stmts env k f
    else
      Sasgn (x, Some ty, a) :: gen_stmts env k f
  | _ -> Sexpr a :: gen_stmts env k f)
| MLapp (MLglob (r, _), a1 :: l) when is_ret r ->
  let t = last (a1 :: l) in
  [k (gen_expr env t)]
| MLcase (typ, t, pv) when is_custom_match pv ->
    [gen_custom_cpp_case env k typ t pv]
| MLglob (r, _) when is_ghost r ->
  [SreturnVoid]
| t -> [k (gen_expr env t)]

and gen_fix env (n,ty) f =
  let ids, f = collect_lams f in
  let ids,_ = push_vars' (List.map (fun (x, ty) -> (remove_prime_id (id_of_mlid x), ty)) ids) env in
  let _,env = push_vars' (ids @ [(n,ty)]) env in
  let ids = List.filter (fun (_,ty) -> not (ml_type_is_void ty)) ids in
  ids, gen_stmts env (fun x -> Sreturn x) f

(* TODO: REDO NAMESPACE AS PART OF NAMES!!! *)

let gen_ind_cpp vars name cnames tys =
  let constrdecl = List.map snd (List.filter fst (Array.to_list (Array.mapi
    (fun i tys ->
      let c = cnames.(i) in
      (* eventually incorporate given names when they exist *)
      let constr = List.mapi (fun i x -> (Id.of_string ("_a" ^ string_of_int i) , convert_ml_type_to_cpp_type (empty_env ()) [name] vars x)) tys in
      let make_args = List.map(fun (x,_) -> CPPglob (GlobRef.VarRef x, [])) constr in
      let ty_vars = List.mapi (fun i x -> Tvar (i, Some x)) vars in
      let make = Dfundef ([c, []; GlobRef.VarRef (Id.of_string "make"), []], Tshared_ptr (Tglob (name, ty_vars, [])), List.rev constr,
        [Sreturn (CPPfun_call (CPPmk_shared (Tglob (name, ty_vars, [])), [CPPstruct (c, ty_vars, make_args)]))]) in
      (ty_vars == [], make))
    tys))) in
  Dnspace (Some name, constrdecl)

let gen_record_cpp name fields ind =
  let l = List.combine fields ind.ip_types.(0) in
  let l = List.mapi (fun i (x, t) ->
    let n = match x with
    | Some n -> n
    | None -> GlobRef.VarRef (Id.of_string ("_field" ^ (string_of_int i))) in
    (Fvar' (n, convert_ml_type_to_cpp_type (empty_env ()) [] ind.ip_vars t), true)) l in
  let ty_vars = List.map (fun x -> (TTtypename, x)) ind.ip_vars in
  match ty_vars with
  | [] -> Dstruct (name, l)
  | _ -> Dtemplate (ty_vars, None, Dstruct (name, l))

(* order by index! *)
let get_tvars t =
  let get_name i n =
    match n with
    | None -> Id.of_string ("T" ^ string_of_int i)
    | Some n -> n in
  let rec aux l = function
    | Tvar (i, n) -> if List.exists (fun (x, _) -> i == x) l
                  then l
                  else (i, get_name i n) :: l
    | Tglob (_, tys, _) -> List.fold_left aux l tys
    | Tfun (tys, ty) -> List.fold_left aux l (ty :: tys)
    | Tmod (_, ty) -> aux l ty
    | Tnamespace (_, ty) -> aux l ty
    | Tstruct (_, tys) -> List.fold_left aux l tys
    | Tref ty -> aux l ty
    | Tvariant tys -> List.fold_left aux l tys
    | Tshared_ptr ty -> aux l ty
    | _ -> l in
  let l = List.sort (fun (x,_) (y,_) -> Int.compare x y) (aux [] t) in
  List.map snd l

let rec glob_subst_expr (id : GlobRef.t) (e1 : cpp_expr) (e2 : cpp_expr) =
match e2 with
  | CPPglob (id', _) ->
    if Environ.QGlobRef.equal Environ.empty_env id id' then e1 else e2
  | CPPnamespace (id', e') -> CPPnamespace (id', glob_subst_expr id e1 e')
  | CPPfun_call (f, args) -> CPPfun_call (glob_subst_expr id e1 f, List.map (glob_subst_expr id e1) args)
  | CPPderef e' -> CPPderef (glob_subst_expr id e1 e')
  | CPPmove e' -> CPPmove (glob_subst_expr id e1 e')
  | CPPlambda (args, ty, b) -> CPPlambda (args, ty, List.map (glob_subst_stmt id e1) b)
  | CPPoverloaded cases -> CPPoverloaded (List.map (glob_subst_expr id e1) cases)
  | CPPstructmk (id', tys, args) -> CPPstructmk (id', tys, List.map (glob_subst_expr id e1) args)
  | CPPstruct (id', tys, args) -> CPPstruct (id', tys, List.map (glob_subst_expr id e1) args)
  | CPPget (e', id') -> CPPget (glob_subst_expr id e1 e', id')
  | CPPget' (e', id') -> CPPget' (glob_subst_expr id e1 e', id')
  | CPPparray (args, e') -> CPPparray (Array.map (glob_subst_expr id e1) args, glob_subst_expr id e1 e')
  | _ -> e2 (* lambda needs to be covered *)

and glob_subst_stmt (id : GlobRef.t) (e : cpp_expr) (s : cpp_stmt) =
match s with
  | Sreturn e' -> Sreturn (glob_subst_expr id e e')
  | Sasgn (id', ty, e') -> Sasgn (id', ty, glob_subst_expr id e e')
  | Sexpr e' -> Sexpr (glob_subst_expr id e e')
  | Scustom_case (ty, e', tys, brs, str) -> Scustom_case (ty, glob_subst_expr id e e', tys,
    List.map (fun (args, ty, stmts) -> (args, ty, List.map (glob_subst_stmt id e) stmts)) brs, str)
  | _ -> s

let rec var_subst_expr (id : Id.t) (e1 : cpp_expr) (e2 : cpp_expr) =
match e2 with
  | CPPvar id' -> if Id.equal id id' then e1 else e2
  | CPPnamespace (id', e') -> CPPnamespace (id', var_subst_expr id e1 e')
  | CPPfun_call (f, args) -> CPPfun_call (var_subst_expr id e1 f, List.map (var_subst_expr id e1) args)
  | CPPderef e' -> CPPderef (var_subst_expr id e1 e')
  | CPPmove e' -> CPPmove (var_subst_expr id e1 e')
  | CPPlambda (args, ty, b) -> CPPlambda (args, ty, List.map (var_subst_stmt id e1) b)
  | CPPoverloaded cases -> CPPoverloaded (List.map (var_subst_expr id e1) cases)
  | CPPstructmk (id', tys, args) -> CPPstructmk (id', tys, List.map (var_subst_expr id e1) args)
  | CPPstruct (id', tys, args) -> CPPstruct (id', tys, List.map (var_subst_expr id e1) args)
  | CPPget (e', id') -> CPPget (var_subst_expr id e1 e', id')
  | CPPget' (e', id') -> CPPget' (var_subst_expr id e1 e', id')
  | CPPparray (args, e') -> CPPparray (Array.map (var_subst_expr id e1) args, var_subst_expr id e1 e')
  | _ -> e2 (* lambda needs to be covered *)

and var_subst_stmt (id : Id.t) (e : cpp_expr) (s : cpp_stmt) =
match s with
  | Sreturn e' -> Sreturn (var_subst_expr id e e')
  | Sasgn (id', ty, e') -> Sasgn (id', ty, var_subst_expr id e e')
  | Sexpr e' -> Sexpr (var_subst_expr id e e')
  | Scustom_case (ty, e', tys, brs, str) -> Scustom_case (ty, var_subst_expr id e e', tys,
    List.map (fun (args, ty, stmts) -> (args, ty, List.map (var_subst_stmt id e) stmts)) brs, str)
  | _ -> s

(* TODO: CLEANUP: dom and cod are redundant with ty *)
let gen_dfun n b dom cod ty temps =
  let ids,b = collect_lams b in
  let rec get_dom l ty = match ty with
    | Tarr (t1, t2) -> get_dom (t1 :: l) t2
    | _ -> l in
  let mldom = get_dom [] ty in
  let rec get_missing d a = match (d , a) with
    | t1 :: d' , t2 :: a' -> get_missing d' a'
    | _ , _ -> d in
  let missing = List.rev (List.mapi (fun i t -> (Id (Id.of_string ("_x" ^ string_of_int i)), t)) (get_missing mldom ids)) in
  let ids,env = push_vars' (List.map (fun (x, ty) -> (remove_prime_id (id_of_mlid x), ty)) (missing @ ids)) (empty_env ()) in
  let ids = List.filter (fun (_, ty) -> not (ml_type_is_void ty)) ids in
  let ids = List.map (fun (x, ty) -> (x,  (Tmod (TMconst, convert_ml_type_to_cpp_type env [] [] ty)))) ids in
  let fun_tys = List.filter_map (fun (x, ty, i) ->
      match ty with
      |  (Tmod (TMconst, Tfun (dom, cod))) -> Some (x, TTfun (dom, cod), Id.of_string ("F" ^ (string_of_int i)))
      | _ -> None) (List.mapi (fun i (x, ty) -> (x, ty, i)) (List.rev ids)) in
  let ids = List.mapi (fun i (x, ty) ->
      match ty with
      |  (Tmod (TMconst, Tfun (dom, cod))) ->
        (x, Tref (Tref (Tvar (0, Some (Id.of_string ("F" ^ (string_of_int ((List.length ids) - i - 1))))))))
      | _ -> (x, ty)) ids in
  (* TODO: below is needed for lambdas in recursive positiions, but is badddddd. *)
  (* let rec_fun_tys = List.map (fun (_,t, _) ->
    match t with
    | TTfun (dom, cod) -> Tref (Tmod (TMconst, Tfun (dom, cod)))
    | _ -> assert false) fun_tys in
  let rec_call = CPPglob (n, List.map (fun (_, id) -> Tvar (0, Some id)) temps @ rec_fun_tys) in *)
  let rec_call = CPPglob (n, List.map (fun (_, id) -> Tvar (0, Some id)) temps) in (* TODO: REMOVE. Hack while we figure out missing type arguments for MLGlob terms when they are given as section variables. NOTE: doesn't work if parameters change in recursive call. *)
  let temps = temps @ (List.map (fun (_,t,n) -> (t,n)) fun_tys) in
  (* let forward_fun_args stmt = List.fold_left (fun s (x, _, fid) ->
    var_subst_stmt x (CPPforward (Tvar (0, Some fid), CPPvar x)) s) stmt fun_tys in *)
  let inner =
    if missing == [] then
      let b = List.map (glob_subst_stmt n rec_call) (gen_stmts env (fun x -> Sreturn x) b) in
      (* let b = List.map forward_fun_args b in *)
      Dfundef ([n, []], cod, ids, b)
    else
      let args = List.rev (List.mapi (fun i _ -> MLrel (i + 1)) missing) in
      let b = List.map (glob_subst_stmt n rec_call) (gen_stmts env (fun x -> Sreturn x) (MLapp (b, args))) in
      (* let b = List.map forward_fun_args b in *)
      Dfundef ([n, []], cod, ids, b) in
  (match temps with
    | [] -> inner, env
    | l -> Dtemplate (l, None, inner), env)

(* TODO: is this used? Likely, but the template stuff shouldn't be. *)
let gen_sfun n b dom cod temps =
  let ids,b = collect_lams b in
  let ids,env = push_vars' (List.map (fun (x, ty) -> (remove_prime_id (id_of_mlid x), ty)) ids) (empty_env ()) in
  let ids = List.filter (fun (_, ty) -> not (ml_type_is_void ty)) ids in
  let ids = List.map (fun (x, ty) -> (Some x,  (Tmod (TMconst, convert_ml_type_to_cpp_type env [] [] ty)))) ids in
  let dom = List.filter (fun ty -> ty != Tvoid) dom in
  let args = List.mapi (fun i ty -> (None,  (Tmod (TMconst, ty)))) dom in
  let inner = if List.length args > List.length ids (* TODO: find/fix bug so we don't need this *)
    then Dfundecl ([n, []], cod, List.rev args)
    else Dfundecl ([n, []], cod, ids) in
  (match temps with
    | [] -> inner, env
    | l -> Dtemplate (l, None, inner), env)

let gen_decl n b ty =
  let cty = convert_ml_type_to_cpp_type (empty_env ()) [] [] ty in
  let tvars = get_tvars cty in
  let temps = List.map (fun id -> (TTtypename, id)) tvars in
  match cty with
  | Tfun (dom, cod) -> let (f, env) = gen_dfun n b dom cod ty temps in f , env , tvars
  | _ ->
    let inner = Dasgn (n, cty,  gen_expr (empty_env ()) b) in
    (match temps with
      | [] -> inner, empty_env () , tvars
      | l -> Dtemplate (l, None, inner), empty_env () , tvars)

let gen_decl_for_pp n b ty =
  let cty = convert_ml_type_to_cpp_type (empty_env ()) [] [] ty in
  let tvars = get_tvars cty in
  let temps = List.map (fun id -> (TTtypename, id)) tvars in
  match cty with
  | Tfun (dom, cod) ->
    let f, e = gen_dfun n b dom cod ty temps in
  let fun_tys = List.filter_map (fun (ty, i) ->
      match ty with
      | Tfun (dom, cod) -> Some (Id.of_string ("F" ^ (string_of_int i)))
      | _ -> None) (List.mapi (fun i ty -> (ty, i)) dom) in
  let tvars = tvars @ fun_tys in
    Some f, e, tvars
  | _ ->
    None, empty_env (), tvars (*
    let inner = Dasgn (n, Tmod (TMconst, ty),  gen_expr (empty_env ()) b) in
    (match temps with
      | [] -> inner, empty_env ()
      | l -> Dtemplate (l, inner), empty_env ())*)

(* TODO: maybe cleanup this function/its name etc.. *)
let gen_decl_for_dfuns n b ty =
  let cty = convert_ml_type_to_cpp_type (empty_env ()) [] [] ty in
  let tvars = get_tvars cty in
  let temps = List.map (fun id -> (TTtypename, id)) tvars in
  match cty with
  | Tfun (dom, cod) ->
    let (f, env) = gen_dfun n b dom cod ty temps in
    let fun_tys = List.filter_map (fun (ty, i) ->
      match ty with
      | Tfun (dom, cod) -> Some (Id.of_string ("F" ^ (string_of_int i)))
      | _ -> None) (List.mapi (fun i ty -> (ty, i)) dom) in
    let tvars = tvars @ fun_tys in
    f , env , tvars
  | _ -> let (f, env) = gen_dfun n b [Tvoid] cty ty temps in f , env , tvars

let gen_spec n b ty =
  let ty = convert_ml_type_to_cpp_type (empty_env ()) [] [] ty in
  let temps = List.map (fun id -> (TTtypename, id)) (get_tvars ty) in
  match ty with
  | Tfun (dom, cod) -> gen_sfun n b dom cod temps
  | _ ->
    let b = gen_expr (empty_env ()) b in
    let inner = Dasgn (n, Tmod (TMconst, ty), b) in
    (match temps with
      | [] -> inner, empty_env ()
      | l -> Dtemplate (l, None, inner), empty_env ())

(* TODO: maybe cleanup this function/its name etc.. *)
let gen_spec_for_sfuns n b ty =
  let ty = convert_ml_type_to_cpp_type (empty_env ()) [] [] ty in
  let temps = List.map (fun id -> (TTtypename, id)) (get_tvars ty) in
  match ty with
  | Tfun (dom, cod) -> gen_sfun n b dom cod temps
  | _ -> gen_sfun n b [Tvoid] ty temps

let gen_dfuns (ns,bs,tys) =
  List.mapi (fun i name -> gen_decl_for_dfuns name bs.(i) tys.(i)) (Array.to_list ns)

let gen_dfuns_header (ns,bs,tys) =
  List.mapi (fun i name ->
    let (ds, env, tvars) = gen_decl_for_dfuns name bs.(i) tys.(i) in
    match tvars with
    | [] -> gen_spec_for_sfuns name bs.(i) tys.(i)
    | _::_ -> ds, env) (Array.to_list ns)

let gen_ind_header vars name cnames tys =
  let templates = List.map (fun n -> (TTtypename, n)) vars in
  let add_templates d = match templates with
  | [] -> d
  | _ -> Dtemplate (templates, None, d) in
  let header = Array.to_list (Array.map (fun x -> add_templates (Dstruct_decl x)) cnames) in
  let vartydecl = add_templates (Dusing (name , Tvariant (Array.to_list (Array.map (fun x -> Tstruct (x, List.mapi (fun i id -> Tvar (i, Some id)) vars)) cnames)))) in
  let constrdecl = Array.to_list (Array.mapi
    (fun i tys ->
      let c = cnames.(i) in
      (* eventually incorporate given names when they exist *)
      let constr = List.mapi (fun i x -> (Id.of_string ("_a" ^ string_of_int i) , convert_ml_type_to_cpp_type (empty_env ()) [name] vars x)) tys in
      let make_args = List.map(fun (x,_) -> CPPglob (GlobRef.VarRef x, [])) constr in
      let ty_vars = List.mapi (fun i x -> Tvar (i, Some x)) vars in
      let make_decl = Ffundecl (Id.of_string "make", Tmod (TMstatic, (ind_ty_ptr name ty_vars)), List.rev constr) in
      let make_def = Ffundef (Id.of_string "make", Tmod (TMstatic, Tshared_ptr (Tglob (name, ty_vars, []))), constr,
        [Sreturn (CPPfun_call (CPPmk_shared (Tglob (name, ty_vars, [])), [CPPstruct (c, ty_vars, make_args)]))]) in
      if ty_vars == []
        then add_templates (Dstruct (c, List.append (List.map (fun (x, y) -> (Fvar (x,y), true)) constr) [make_decl,true]))
        else add_templates (Dstruct (c, List.append (List.map (fun (x, y) -> (Fvar (x,y), true)) constr) [make_def,true])))
    tys) in
  Dnspace (Some name, List.append (List.append header [vartydecl]) constrdecl)
