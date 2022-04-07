open Containers
open Common
open Ast
(* module Tracing = Ppx_debug.Tracing *)

open Log.Make (struct
  let name = "types"
end)

let debug = true
let use_local_bindings = false

let fresh =
  let n = ref 0 in
  fun () ->
    let r = !n in
    incr n;
    r

let subst ~from ~to_ in_ =
  let vt =
    object
      inherit [_] map_typ as super

      method! visit_typ () v =
        if equal_typ from v then to_ else super#visit_typ () v
    end
  in
  vt#visit_typ () in_

let instantiate (Forall (vs, t)) =
  let fresh_vars =
    List.map (fun v -> (TyVar v, TyVar (UF.elt (fresh ())))) vs
  in
  List.fold_right (fun (from, to_) t -> subst ~from ~to_ t) fresh_vars t

let explain_env env =
  let ppi fmt { typ; own } =
    Format.fprintf fmt "typ = %a; ownership = %a" (Print.pp_typ ~env) typ
      (Print.pp_ownership ~env) own
  in
  [
    "---- parties";
    env.parties |> party_list
    |> List.map (fun p -> Format.sprintf "%a" pp_party_info p)
    |> String.concat "\n";
    "---- types";
    env.types |> IMap.bindings
    |> List.map (fun (k, v) -> Format.sprintf "%d: %a" k pp_typ v)
    |> String.concat "\n";
    "---- vars";
    env.bindings |> SMap.bindings
    (* |> List.map (fun (v, t) -> Format.asprintf "%s : %a" v pp_var_info t) *)
    |> List.map (fun (v, t) -> Format.asprintf "%s : %a" v ppi t)
    |> String.concat "\n";
    "---- local vars";
    env.local_bindings |> SMap.bindings
    (* |> List.map (fun (v, t) -> Format.asprintf "%s : %a" v pp_var_info t) *)
    |> List.map (fun (v, t) -> Format.asprintf "%s : %a" v ppi t)
    |> String.concat "\n";
    "----------------";
  ]
  |> String.concat "\n\n"

let unify_party_variables a b env =
  let a2, b2 = (UF.value a, UF.value b) in
  match (IMap.find_opt a2 env.parties, IMap.find_opt b2 env.parties) with
  | None, None ->
    UF.union a b;
    Ok env
  | Some a3, None ->
    UF.union a b;
    let parties = IMap.add b2 a3 env.parties in
    Ok { env with parties }
  | None, Some b3 ->
    UF.union a b;
    let parties = IMap.add b2 b3 env.parties in
    Ok { env with parties }
  | Some a3, Some b3 ->
    if equal_party_info a3 b3 then Ok env
    else
      Error
        (`Does_not_unify
          (Format.sprintf "could not unify parties %a and %a" pp_var a3.repr
             pp_var b3.repr))

let rec unify :
    typ ->
    typ ->
    env ->
    ( env,
      [> `Does_not_unify of string
      | `Parties_instantiated_but_different of string
      ] )
    result =
 fun a b env ->
  let open Result.Infix in
  if debug then log "unify: %a and %a" pp_typ a pp_typ b;
  match (a, b) with
  | TyInt, TyInt | TyBool, TyBool | TyString, TyString -> Ok env
  | TyParty a1, TyParty b1 -> unify_party_variables a1 b1 env
  | TyVar a, TyVar b ->
    let unify_type_variables a b env =
      let a1, b1 = (UF.value a, UF.value b) in
      match (IMap.find_opt a1 env.types, IMap.find_opt b1 env.types) with
      | Some a2, Some b2 ->
        (* this recursive call is the reason this is separate from unify_party_variables *)
        unify a2 b2 env
      | Some t, None ->
        let types = env.types in
        (* let types = IMap.remove a2 env.types in *)
        UF.union a b;
        let types = IMap.add (UF.value a) t types in
        Ok { env with types }
      | None, Some t ->
        let types = env.types in
        (* let types = IMap.remove b2 env.types in *)
        UF.union a b;
        let types = IMap.add (UF.value a) t types in
        Ok { env with types }
      | None, None ->
        UF.union a b;
        Ok env
    in
    unify_type_variables a b env
  | TyFn (a1, r1), TyFn (a2, r2) ->
    if List.length a1 = List.length a2 then
      List.fold_right2
        (fun a b t ->
          let* env = t in
          unify a b env)
        (a1 @ [r1]) (a2 @ [r2]) (Ok env)
    else Error (`Does_not_unify "argument lists have different lengths")
  | TyRecord r1, TyRecord r2 ->
    let r1 =
      List.sort (fun (k1, _v1) (k2, _v2) -> String.compare k1 k2) r1
      |> List.map snd
    in
    let r2 =
      List.sort (fun (k1, _v1) (k2, _v2) -> String.compare k1 k2) r2
      |> List.map snd
    in
    if List.length r1 = List.length r2 then
      List.fold_right2
        (fun a b t ->
          let* env = t in
          unify a b env)
        r1 r2 (Ok env)
    else Error (`Does_not_unify "records have different numbers of fields")
  | TyMap (k1, v1), TyMap (k2, v2) ->
    let* env = unify k1 k2 env in
    let* env = unify v1 v2 env in
    Ok env
  | TyVar a1, b1 | b1, TyVar a1 ->
    (* if one is a variable, look it up and bind it or unify what is already there *)
    let a2 = UF.value a1 in
    (match IMap.find_opt a2 env.types with
    | None -> Ok { env with types = IMap.add a2 b1 env.types }
    | Some t -> unify t b1 env)
    (* env *)
  | _, _ ->
    Error
      (`Does_not_unify
        (Format.sprintf "%a and %a do not unify" (Print.pp_typ ~env) a
           (Print.pp_typ ~env) b))

let dump_env env = log "ENV\n%s" (explain_env env)
let lookup_fn env f = SMap.find_opt f env.polymorphic

let lookup env v =
  SMap.find_opt v env.local_bindings
  |> Option.or_ ~else_:(SMap.find_opt v env.bindings)

let lookup_var ~loc env v =
  match lookup env v with
  | Some vi -> vi
  | None ->
    (* fresh_var env v *)
    (* dump_env env; *)
    fail ~loc "unbound variable %s" v

let fresh_type () =
  let tv = UF.elt (fresh ()) in
  TyVar tv

let fresh_ownership () =
  let r = UF.elt (fresh ()) in
  Party r

(** this binds a variable, unlike lookup_var, which expects the variable to already exist *)
let fresh_var env v =
  let own = fresh_ownership () in
  let typ = fresh_type () in
  let vi = { typ; own } in
  let bindings = SMap.add v vi env.bindings in
  ({ env with bindings }, vi)

(** this isn't entirely unification determined by form because Global doesn't unify with anything *)
let unify_ownership :
    ownership ->
    ownership ->
    env ->
    (ownership * env, [> `Does_not_unify of string ]) result =
 fun a b env ->
  if debug then log "unify_ownership: %a and %a" pp_ownership a pp_ownership b;
  match (a, b) with
  | Global, o1 | o1, Global -> Ok (o1, env)
  | Party p, Party q ->
    let open Result.Infix in
    let* env = unify_party_variables p q env in
    Ok (a, env)

(* high-level functions *)

let unify_two_types ~loc a b env =
  match unify a b env with
  | Ok env -> env
  | Error (`Does_not_unify s) -> fail ~loc "%s" s
  | Error (`Parties_instantiated_but_different s) -> fail ~loc "%s" s

let unify_two_ownerships ~loc a b env =
  let own, env =
    match unify_ownership a b env with
    | Ok oe -> oe
    | Error (`Does_not_unify s) -> fail ~loc "%s" s
  in
  (own, env)

let concretize env t =
  let vt =
    object
      inherit [_] map_typ as super
      method! visit_TyParty () p = TyParty (UF.find p)

      method! visit_TyVar () v =
        match IMap.find_opt (UF.value v) env.types with
        | None -> TyVar v
        | Some t1 -> super#visit_typ () t1
    end
  in
  vt#visit_typ () t

module Cast = struct
  let must_be_var (e : expr) =
    match e.expr with Var v -> v | _ -> fail ~loc:e.meta "expr must be a var"

  let must_be_var_t (e : texpr) =
    match e.expr with
    | Var v -> v
    | _ -> fail ~loc:e.meta.loc "texpr must be a var"

  let must_be_party_set env te =
    (* we need to concretize because it may be a variable *)
    match concretize env te.meta.info.typ with
    | TyMap (TyParty p, TyBool) ->
      (match IMap.find_opt (UF.value p) env.parties with
      | None ->
        fail ~loc:te.meta.loc "unknown party for %a" (Print.pp_texpr ~env) te
      | Some p -> p.repr |> var_name)
    | t ->
      fail ~loc:te.meta.loc "expected %a to be a set of parties but got %a"
        (Print.pp_texpr ~env) te (Print.pp_typ ~env) t

  let must_be_party env te =
    (* we need to concretize because it may be a variable *)
    match concretize env te.meta.info.typ with
    | TyParty p ->
      (match IMap.find_opt (UF.value p) env.parties with
      | None ->
        fail ~loc:te.meta.loc "unknown party for %a" (Print.pp_texpr ~env) te
      | Some p -> p.repr |> var_name)
    | t ->
      fail ~loc:te.meta.loc "expected %a to be a party but got %a"
        (Print.pp_texpr ~env) te (Print.pp_typ ~env) t

  let as_party_set_or_less env te =
    match te.expr with
    | Var _ ->
      let s = must_be_party_set env te in
      let name = must_be_var_t te |> var_name in
      (s, name, [])
    | App ("\\", [left; right]) ->
      let pname = must_be_party_set env left in
      let name = must_be_var_t left |> var_name in
      let minus =
        match right.expr with
        | Set vs -> vs |> List.map must_be_var_t |> List.map var_name
        | _ ->
          fail ~loc:right.meta.loc
            "expected right side to be a constant set instead of %a"
            (Print.pp_texpr ~env) right
      in
      (pname, name, minus)
    | _ ->
      fail ~loc:te.meta.loc
        "expected %a to be an expression that can be interpreted as a party \
         set minus some"
        (Print.pp_texpr ~env) te
end

open Cast

let find_party_var_by_type_of env var =
  let { typ; own } = var.meta.info in
  let loc = var.meta.loc in
  let name = var |> must_be_var_t |> var_name in
  let check_env e =
    e |> SMap.bindings
    |> List.filter (fun (v, info) ->
           (match (concretize env info.typ, own) with
           | TyParty p1, Party p2 -> UF.equal p1 p2
           | _ -> false)
           && not (String.equal v name))
  in
  match typ with
  | TyParty _ ->
    (* don't qualify things like the operands of send *)
    None
  | _
    when List.mem ~eq:String.equal name
           (env.parties |> IMap.bindings |> List.map snd
           |> List.map (fun p -> p.repr |> var_name)) ->
    (* principal party set, ignore those *)
    None
  | _ ->
    let candidate =
      match env.local_bindings |> check_env with
      | [] ->
        (match env.bindings |> check_env with
        | [] ->
          dump_env env;
          fail ~loc "could not insert qualifier for %a" Print.pp_texpr_untyped
            var
        | [(c, _)] -> c
        | cs ->
          fail ~loc "more than one possible qualifier for %a: %a"
            Print.pp_texpr_untyped var (List.pp String.pp)
            (cs |> List.map fst))
      | [(c, _)] -> c
      | cs ->
        fail ~loc "more than one possible qualifier for %a: %a"
          Print.pp_texpr_untyped var (List.pp String.pp)
          (cs |> List.map fst)
    in
    Some (Party candidate : party)

(** for party types only *)
let unify_type_owner :
    env ->
    typ ->
    ownership ->
    ( env,
      [> `Does_not_unify of string
      | `Parties_instantiated_but_different of string
      | `Type_not_party
      ] )
    result =
 fun env t o ->
  (* let open Result.Infix in *)
  if debug then log "unify_type_owner: %a and %a" pp_typ t pp_ownership o;
  match (t, o) with
  | TyParty _, Global -> Ok env
  | TyParty t, Party o -> unify_party_variables t o env
  | TyVar _, Party o -> unify t (TyParty o) env
  | _, _ -> Error `Type_not_party

let rec infer_all : expr list -> env -> texpr list * ownership * env =
 fun exprs env ->
  List.fold_right
    (fun c (tes, own, env) ->
      let te, env = infer_expr c env in
      match unify_ownership own te.meta.info.own env with
      | Ok (own1, env) -> (te :: tes, own1, env)
      | Error (`Does_not_unify s) -> fail ~loc:te.meta.loc "%s" s)
    exprs ([], Global, env)

and expr_must_be_type expr typ env =
  let te, env = infer_expr expr env in
  let env = unify_two_types ~loc:expr.meta te.meta.info.typ typ env in
  (te, env)

and infer_expr : expr -> env -> texpr * env =
 fun expr env ->
  if debug then (
    dump_env env;
    log "INFER EXPR %a" Print.pp_expr expr);
  let inferred =
    match expr.expr with
    | Int i ->
      ( {
          meta = { loc = expr.meta; info = { typ = TyInt; own = Global }; env };
          expr = Int i;
        },
        env )
    | Bool b ->
      ( {
          meta = { loc = expr.meta; info = { typ = TyBool; own = Global }; env };
          expr = Bool b;
        },
        env )
    | String s ->
      ( {
          meta =
            { loc = expr.meta; info = { typ = TyString; own = Global }; env };
          expr = String s;
        },
        env )
    | Var (V (p, v)) ->
      (* give previously-unassigned variables fresh types when they are read for the first time *)
      (* this produces worse error messages, because variables that are not in scope now get fresh types, and cannot remain uninstantiated rather than remain unbound *)
      (* let env, { own; typ } =
           match lookup env v with None -> fresh_var env v | Some vi -> (env, vi)
         in *)
      (* this causes a failure if a variable was never previously assigned to *)
      let { own; typ } = lookup_var ~loc:expr.meta env v in
      let te = Var (V (p, v)) in
      let texpr =
        { meta = { loc = expr.meta; info = { typ; own }; env }; expr = te }
      in
      (* check if a party is given for this variable *)
      (match p with
      | None -> (texpr, env)
      | Some (Party p1) ->
        let vi = lookup_var ~loc:expr.meta env p1 in
        (match unify_type_owner env vi.typ own with
        | Ok env -> (texpr, env)
        | Error (`Parties_instantiated_but_different s) ->
          fail ~loc:expr.meta "variable %s not owned by given party: %s" v s
        | Error `Type_not_party -> fail ~loc:expr.meta "type not party"
        | Error (`Does_not_unify s) ->
          fail ~loc:expr.meta "does not unify: %s" s))
    | App (fn, args) ->
      (match lookup_fn env fn with
      | None -> fail ~loc:expr.meta "function %s not bound" fn
      | Some f ->
        (match instantiate f with
        | TyFn (targs, ret) ->
          let tes, own, env = infer_all args env in

          let env =
            List.fold_right2
              (fun a b t ->
                match unify a b.meta.info.typ t with
                | Ok env -> env
                | Error (`Does_not_unify s)
                | Error (`Parties_instantiated_but_different s) ->
                  (* Format.printf "a %a@." pp_typ a;
                     Format.printf "b %a@." pp_typ b.meta.info.typ;
                     dump_env env; *)
                  fail ~loc:b.meta.loc
                    "could not unify arg %a of function %s: %s"
                    (Print.pp_texpr ~env) b fn s)
              targs tes env
          in

          let rtyp = fresh_type () in
          let env =
            match unify rtyp ret env with
            | Ok env -> env
            | Error (`Does_not_unify s)
            | Error (`Parties_instantiated_but_different s) ->
              fail ~loc:expr.meta "could not unify result type: %s" s
          in
          ( {
              meta = { loc = expr.meta; info = { own; typ = rtyp }; env };
              expr = App (fn, tes);
            },
            env )
        | _ -> fail ~loc:expr.meta "%s is not a function" fn))
    | Ite (e1, e2, e3) ->
      let te1, env = expr_must_be_type e1 TyBool env in
      let typ = fresh_type () in
      let te2, env = expr_must_be_type e2 typ env in
      let te3, env = expr_must_be_type e3 typ env in
      let own, env =
        let own, env =
          unify_two_ownerships ~loc:expr.meta te1.meta.info.own
            te2.meta.info.own env
        in
        unify_two_ownerships ~loc:expr.meta own te3.meta.info.own env
      in
      ( {
          meta = { loc = expr.meta; info = { own; typ }; env };
          expr = Ite (te1, te2, te3);
        },
        env )
    | Set s | List s ->
      begin
        match s with
        | [] ->
          (* empty; use a fresh type variable *)
          ( {
              meta =
                {
                  loc = expr.meta;
                  info =
                    {
                      own = fresh_ownership ();
                      typ =
                        (match expr.expr with
                        | Set _ -> ty_set (fresh_type ())
                        | List _ -> ty_list (fresh_type ())
                        | _ -> bug "unexpected");
                    };
                  env;
                };
              expr =
                (match expr.expr with
                | Set _ -> Set []
                | List _ -> List []
                | _ -> bug "unexpected");
            },
            env )
        | _ ->
          (* nonempty literal. infer types of everything then unify *)
          let tes, own, env = infer_all s env in
          let typ, env =
            List.fold_right
              (fun c (t, env) ->
                match t with
                | None -> (Some c, env)
                | Some t ->
                  (match unify c t env with
                  | Ok env -> (Some c, env)
                  | Error (`Does_not_unify s)
                  | Error (`Parties_instantiated_but_different s) ->
                    fail ~loc:expr.meta "%s" s))
              (List.map (fun (te : texpr) -> te.meta.info.typ) tes)
              (None, env)
          in
          (match expr.expr with
          | List _ ->
            let typ =
              typ |> Option.get_exn_or "nonempty list should have a type"
            in
            let typ = ty_list typ (* TyMap (TyInt, typ) *) in
            ( {
                meta = { loc = expr.meta; info = { own; typ }; env };
                expr = List tes;
              },
              env )
          | Set _ ->
            let typ =
              typ |> Option.get_exn_or "nonempty set should have a type"
            in
            let typ = ty_set typ (* TyMap (typ, TyBool) *) in
            ( {
                meta = { loc = expr.meta; info = { own; typ }; env };
                expr = Set tes;
              },
              env )
          | _ -> bug "unexpected")
      end
    | Map m ->
      (* similar approach to list/set: ensure that all values are of the same type *)
      begin
        match m with
        | [] ->
          (* empty; use a fresh type variable *)
          ( {
              meta =
                {
                  loc = expr.meta;
                  info =
                    {
                      own = fresh_ownership ();
                      typ = TyMap (fresh_type (), fresh_type ());
                    };
                  env;
                };
              expr = Map [];
            },
            env )
        | _ ->
          (* nonempty literal *)
          let s = List.map snd m in
          let tes, own, env = infer_all s env in
          let typ, env =
            List.fold_right
              (fun c (t, env) ->
                match t with
                | None -> (Some c, env)
                | Some t ->
                  (match unify c t env with
                  | Ok env -> (Some c, env)
                  | Error (`Does_not_unify s)
                  | Error (`Parties_instantiated_but_different s) ->
                    fail ~loc:expr.meta "%s" s))
              (List.map (fun (te : texpr) -> te.meta.info.typ) tes)
              (None, env)
          in
          let typ =
            TyMap
              ( TyString,
                typ |> Option.get_exn_or "nonempty list should have a type" )
          in
          ( {
              meta = { loc = expr.meta; info = { own; typ }; env };
              expr = Set tes;
            },
            env )
      end
    | MapComp mc ->
      let ik, iv, io = (fresh_type (), fresh_type (), fresh_ownership ()) in
      let in_typ = TyMap (ik, iv) in
      let ok, ov = (fresh_type (), fresh_type ()) in
      (* extend env with the two variable bindings *)
      let env =
        {
          env with
          bindings =
            env.bindings
            |> SMap.add (var_name mc.bind_key) { typ = ik; own = io }
            |> SMap.add (var_name mc.bind_val) { typ = iv; own = io };
        }
      in
      let out_typ = TyMap (ok, ov) in
      let tpred, env =
        match mc.pred with
        | None -> (None, env)
        | Some p ->
          let tp, env = expr_must_be_type p TyBool env in
          (Some tp, env)
      in
      let tinp, env = expr_must_be_type mc.inp in_typ env in
      let tmk, env = expr_must_be_type mc.map_key ok env in
      let tmv, env = expr_must_be_type mc.map_val ov env in
      let own, env =
        (* which is passed in as first arg matters for error msg? *)
        let own, env =
          unify_two_ownerships ~loc:tmk.meta.loc tmk.meta.info.own
            tmv.meta.info.own env
        in
        let own, env =
          unify_two_ownerships ~loc:tmv.meta.loc own tinp.meta.info.own env
        in
        let own, env =
          match tpred with
          | None -> (own, env)
          | Some tp ->
            unify_two_ownerships ~loc:tp.meta.loc own tp.meta.info.own env
        in
        (own, env)
      in
      ( {
          meta = { loc = expr.meta; info = { own; typ = out_typ }; env };
          expr =
            MapComp
              {
                pred = tpred;
                inp = tinp;
                map_key = tmk;
                map_val = tmv;
                bind_val = mc.bind_val;
                bind_key = mc.bind_key;
              };
        },
        env )
    | MapProj (e, i) ->
      (* infer both sides, unify ownership, determine what index should unify with based on e, so e must be instantiated. typeclasses would be a more pure way to support this *)
      let te, env = infer_expr e env in
      let ti, env = infer_expr i env in
      let own, env =
        unify_two_ownerships ~loc:expr.meta te.meta.info.own ti.meta.info.own
          env
      in
      let typ, env =
        match concretize env te.meta.info.typ with
        | TyMap (k, v) ->
          let env = unify_two_types ~loc:ti.meta.loc ti.meta.info.typ k env in
          (v, env)
        | TyRecord kvs ->
          let env =
            unify_two_types ~loc:ti.meta.loc ti.meta.info.typ TyString env
          in
          let key =
            match ti.expr with
            | String s -> s
            | _ ->
              fail ~loc:ti.meta.loc "not a string: %a" (Print.pp_texpr ~env) ti
          in
          (List.assoc ~eq:String.equal key kvs, env)
        | _ ->
          fail ~loc:e.meta "an instantiated collection type is required: %a"
            (Print.pp_texpr ~env) te
      in
      ( {
          meta = { loc = expr.meta; info = { own; typ }; env };
          expr = MapProj (te, ti);
        },
        env )
    | Let _ ->
      (* infer_all (List.map snd b) env *)
      nyi "infer_parties_expr let"
    | Record kvs ->
      (* treat this like a tuple, so it's structurally typed, and all we ensure is that tuple variables are used consistently as such *)
      let tes, own, env = infer_all (List.map snd kvs) env in
      let tes = List.map2 (fun (s, _) t -> (s, t)) kvs tes in
      let typ = TyRecord (List.map (fun (s, t) -> (s, t.meta.info.typ)) tes) in
      ( {
          meta = { loc = expr.meta; info = { own; typ }; env };
          expr = Record tes;
        },
        env )
  in
  log "=> %a" (Print.pp_texpr ~env) (fst inferred);
  inferred

(* can no longer use ppx_debug because of labelled arg *)
let rec infer : ?in_seq:bool -> protocol -> env -> tprotocol * env =
 fun ?(in_seq = false) p env ->
  if debug then (
    dump_env env;
    log "INFER %a" Print.pp_protocol p);
  let loc = p.pmeta in
  match p.p with
  | Emp -> ({ p = Emp; pmeta = pmeta ~loc ~env () }, env)
  | Call { f; args } ->
    (* TODO lookup the function environment *)
    let args, env =
      List.fold_left
        (fun (ts, env) c ->
          let te, env = infer_expr c env in
          (te :: ts, env))
        ([], env) args
    in
    let args = List.rev args in
    ({ p = Call { f; args }; pmeta = pmeta ~loc ~env () }, env)
  | Send { from; to_; msg = Message { args; typ = mtype } } ->
    let fm, tm = (from.meta, to_.meta) in
    let (V (fp, from)) = must_be_var from in
    let (V (tp, to_)) = must_be_var to_ in

    let f_vi = lookup_var ~loc:p.pmeta env from in
    let t_vi = lookup_var ~loc:p.pmeta env to_ in

    (* check that sender knows about itself *)
    let env =
      match unify_type_owner env f_vi.typ f_vi.own with
      | Ok env -> env
      | Error `Type_not_party ->
        fail ~loc:p.pmeta "sender %s of wrong type %a, should be a party" from
          (Print.pp_typ ~env) f_vi.typ
      | Error (`Does_not_unify _)
      | Error (`Parties_instantiated_but_different _) ->
        (* dump_env env; *)
        fail ~loc:p.pmeta
          "sender %s does not know of itself (of %a but known only to %a)" from
          (Print.pp_typ ~env) f_vi.typ (Print.pp_ownership ~env) f_vi.own
    in

    (* check that sender knows about recipient *)
    let env =
      match unify_ownership t_vi.own f_vi.own env with
      | Ok (_, env) -> env
      | Error (`Does_not_unify s) ->
        (* dump_env env; *)
        fail ~loc:p.pmeta "sender does not know of recipient: %s" s
    in

    (* expressions must be owned by sender *)
    let targs, env =
      List.fold_right
        (fun (k, arg) (targs, env) ->
          let targ, env = infer_expr arg env in

          let env =
            match unify_type_owner env f_vi.typ targ.meta.info.own with
            | Ok env -> env
            | Error (`Parties_instantiated_but_different s) ->
              fail ~loc:p.pmeta "%s" s
            | Error (`Does_not_unify s) -> fail ~loc:p.pmeta "%s" s
            | Error `Type_not_party ->
              fail ~loc:p.pmeta "sender does not know of message arguments"
          in
          (* variables are fresh and owned by recipient *)
          let vo = fresh_ownership () in
          (* use the same type, but ownership based on recipient *)
          let vi = { targ.meta.info with own = vo } in
          let env =
            match unify_type_owner env t_vi.typ vo with
            | Ok env -> env
            | Error (`Does_not_unify s) -> fail ~loc:p.pmeta "%s" s
            | Error (`Parties_instantiated_but_different s) ->
              fail ~loc:p.pmeta "%s" s
            | Error `Type_not_party ->
              fail ~loc:p.pmeta "recipient does not know of variables"
          in
          let (V (pv, v)) = must_be_var k in
          let env =
            if use_local_bindings then
              if in_seq then
                let local_bindings = SMap.add v vi env.local_bindings in
                { env with local_bindings }
              else env
            else
              let bindings = SMap.add v vi env.bindings in
              { env with bindings }
          in
          let k1 =
            { expr = Var (V (pv, v)); meta = { loc = k.meta; info = vi; env } }
          in

          ((k1, targ) :: targs, env))
        args ([], env)
    in
    ( {
        p =
          Send
            {
              from =
                {
                  meta =
                    { loc = fm; info = { typ = f_vi.typ; own = f_vi.own }; env };
                  expr = Var (V (fp, from));
                };
              to_ =
                {
                  meta =
                    { loc = tm; info = { typ = t_vi.typ; own = t_vi.own }; env };
                  expr = Var (V (tp, to_));
                };
              msg = Message { args = targs; typ = mtype };
            };
        pmeta = pmeta ~loc ~env ();
      },
      env )
  | Assign (lval, e) ->
    let vm = lval.meta in
    let V (vp, v), indices, env =
      (* must_be_var v *)
      (* may be an assignment *)
      match lval.expr with
      | Var var -> (var, [], env)
      | MapProj _ ->
        let rec unroll_proj ~loc e =
          match e.expr with
          | MapProj (e, i) ->
            let v, ii = unroll_proj ~loc e in
            (v, ii @ [i])
          | Var v -> (v, [])
          | _ -> fail ~loc "not a projection"
        in
        let tv, env = infer_expr lval env in
        let v, indices = unroll_proj ~loc:tv.meta.loc tv in
        (v, indices, env)
      | _ -> fail ~loc:e.meta "expr must be a var or project"
    in
    let env, { own = olhs; typ = tlhs } =
      (* whether or not to look up existing variables controls if a subsequent assignment to a variable can fill in a previously-unknown type, e.g. a={}; a = union(a, {1}) ==> a : int set *)
      match lookup env v with None -> fresh_var env v | Some vi -> (env, vi)
    in
    (* modify existing type using indices *)
    let tlhs, env =
      let rec projections t indices env =
        log "projecting %a %a" (Print.pp_typ ~env) t
          (List.pp (Print.pp_typ ~env))
          indices;
        match (t, indices) with
        | t, [] -> (t, env)
        | TyMap (k, v), i :: rest ->
          log "%b" (equal_typ k i);
          let env = unify k i env in
          begin
            match env with
            | Error _ -> fail ~loc:lval.meta "unable to project, cannot unify"
            | Ok env -> projections v rest env
          end
        | _ -> fail ~loc:lval.meta "unable to project"
      in
      projections tlhs (List.map (fun te -> te.meta.info.typ) indices) env
    in
    (* check that rhs and lhs have same type *)
    let trhs, env = infer_expr e env in
    let env =
      match unify tlhs trhs.meta.info.typ env with
      | Ok env -> env
      | Error (`Parties_instantiated_but_different s)
      | Error (`Does_not_unify s) ->
        fail ~loc:vm "could not unify sides of assignment: %s" s
    in
    (* right and left sides must be owned by same party *)
    (match unify_ownership olhs trhs.meta.info.own env with
    | Error (`Does_not_unify s) -> fail ~loc:vm "%s" s
    | Ok (_o, env) ->
      let env =
        (* if a party was given *)
        match vp with
        | None -> env
        | Some (Party p1) ->
          let vi = lookup_var ~loc:p.pmeta env p1 in
          (* the given party should match the ownership of the left side *)
          (match unify_type_owner env vi.typ olhs with
          | Ok env -> env
          | Error (`Does_not_unify s) -> fail ~loc:vm "%s" s
          | Error (`Parties_instantiated_but_different s) -> fail ~loc:vm "%s" s
          | Error `Type_not_party -> fail ~loc:vm "type is not a party")
      in
      let tlhs =
        {
          expr = Var (V (vp, v));
          meta = { loc = vm; info = { typ = tlhs; own = olhs }; env };
        }
      in
      ({ p = Assign (tlhs, trhs); pmeta = pmeta ~loc ~env () }, env))
  | Imply (c, p) ->
    let tc, env = infer_expr c env in
    let tp, env = infer p env in

    (match unify tc.meta.info.typ TyBool env with
    | Ok _ -> ()
    | Error (`Does_not_unify s) -> fail ~loc:tc.meta.loc "%s" s
    | Error (`Parties_instantiated_but_different s) ->
      fail ~loc:tc.meta.loc "%s" s);

    ({ p = Imply (tc, tp); pmeta = pmeta ~loc ~env () }, env)
  | BlockingImply (c, p) ->
    let tc, env = infer_expr c env in
    let tp, env = infer p env in
    (match unify tc.meta.info.typ TyBool env with
    | Ok _ -> ()
    | Error (`Does_not_unify s) -> fail ~loc:tc.meta.loc "%s" s
    | Error (`Parties_instantiated_but_different s) ->
      fail ~loc:tc.meta.loc "%s" s);

    ({ p = BlockingImply (tc, tp); pmeta = pmeta ~loc ~env () }, env)
  | Seq s ->
    (* List.fold_right infer_parties s env *)
    let local_bindings = env.local_bindings in
    let ts, env =
      List.fold_left
        (fun (ts, env) c ->
          let te, env = infer ~in_seq:true c env in
          (te :: ts, env))
        ([], env) s
    in
    let ts = List.rev ts in

    (* restore *)
    let env = if use_local_bindings then { env with local_bindings } else env in

    ({ p = Seq ts; pmeta = pmeta ~loc ~env () }, env)
  | Par ps ->
    let ts, env =
      List.fold_left
        (fun (ts, env) p ->
          let tp, env = infer p env in
          (tp :: ts, env))
        ([], env) ps
    in
    let ts = List.rev ts in
    ({ p = Par ts; pmeta = pmeta ~loc ~env () }, env)
  | Disj (a, b) ->
    let ta, env = infer a env in
    let tb, env = infer b env in
    ({ p = Disj (ta, tb); pmeta = pmeta ~loc ~env () }, env)
  | Forall (e, s, pb) ->
    let em = e.meta in
    let (V (pe, e)) = must_be_var e in
    let s, env = infer_expr s env in

    (* this binds only one new name, e. s is already defined *)
    let env, party, own =
      let pl = p.pmeta in
      match s.meta.info with
      | { typ = TyMap ((TyParty _ as p), TyBool); own } -> (env, p, own)
      (* | Some vi -> fail "not a party set: %a" pp_var_info vi *)
      | { typ; own } ->
        let[@warning "-8"] (TyVar p) = fresh_type () in
        let env =
          match unify typ (ty_set (TyParty p)) env with
          | Ok env -> env
          | Error (`Does_not_unify s)
          | Error (`Parties_instantiated_but_different s) ->
            fail ~loc:pl "could not unify set type: %s" s
        in
        (env, TyParty p, own)
    in

    let env =
      { env with bindings = SMap.add e { typ = party; own } env.bindings }
    in

    let tp1, env = infer pb env in

    (* unbind the bound variable *)
    let env = { env with bindings = SMap.remove e env.bindings } in

    (* TODO this always unbinds e even if it's been redefined, but we'll worry about that later *)
    let e =
      {
        expr = Var (V (pe, e));
        meta = { loc = em; info = { typ = party; own }; env };
      }
    in
    ({ p = Forall (e, s, tp1); pmeta = pmeta ~loc ~env () }, env)
  | Exists (_, _, _) -> nyi "infer_parties exists"
  | Comment (_, _, _) -> bug "infer_parties doesn't expect comments"
  | SendOnly _ -> bug "infer_parties doesn't expect send only"
  | ReceiveOnly _ -> bug "infer_parties doesn't expect receive only"

let initial_env party_decls =
  (* add all the party sets first, as initializers may depend on them *)
  let parties, bindings, party_vars =
    List.fold_right
      (fun (_v, s, _init, _sz) (party, bindings, party_vars) ->
        let i = fresh () in
        let r = UF.elt i in
        let set_typ = { typ = ty_set (TyParty r); own = Global } in
        let party = IMap.add i { repr = V (None, s) } party in
        let bindings = SMap.add s set_typ bindings in
        (party, bindings, (s, r) :: party_vars))
      party_decls
      (IMap.empty, SMap.empty, [])
  in
  let env = { empty_env with parties; bindings } in
  (* now infer types for initializers *)
  let env =
    List.fold_right
      (fun (_v, s, init, _sz) env ->
        let r = List.assoc ~eq:String.equal s party_vars in
        let bindings =
          SMap.add_list env.bindings
            (List.map
               (fun (v, e) ->
                 let texpr, _env = infer_expr e env in
                 let info = { typ = texpr.meta.info.typ; own = Party r } in
                 (v, info))
               init)
        in
        { env with bindings })
      party_decls env
  in
  (* add builtins *)
  let initial =
    {
      env with
      polymorphic =
        SMap.of_list
          [
            ( "size",
              let a = UF.elt (fresh ()) in
              let b = UF.elt (fresh ()) in
              let map = TyMap (TyVar a, TyVar b) in
              Forall ([a], TyFn ([map], TyInt)) );
            ( "card",
              let a = UF.elt (fresh ()) in
              let set_a = ty_set (TyVar a) in
              Forall ([a], TyFn ([set_a], TyInt)) );
            ( "member",
              let a = UF.elt (fresh ()) in
              let set_a = ty_set (TyVar a) in
              Forall ([a], TyFn ([TyVar a; set_a], TyBool)) );
            ( "min",
              let a = UF.elt (fresh ()) in
              let set_a = ty_set (TyVar a) in
              Forall ([a], TyFn ([set_a], TyVar a)) );
            ( "slice",
              let a = UF.elt (fresh ()) in
              let list_a = ty_list (TyVar a) in
              Forall ([a], TyFn ([list_a; TyInt; TyInt], list_a)) );
            (* ( "size",
               let a = UF.elt (fresh ()) in
               Forall ([a], TyFn ([ty_set (TyVar a)], TyInt)) ); *)
            ( "length",
              let a = UF.elt (fresh ()) in
              let list_a = ty_list (TyVar a) in
              Forall ([a], TyFn ([list_a], TyInt)) );
            ( "last",
              let a = UF.elt (fresh ()) in
              let list_a = ty_list (TyVar a) in
              Forall ([a], TyFn ([list_a], TyVar a)) );
            ( "append",
              let a = UF.elt (fresh ()) in
              let list_a = ty_list (TyVar a) in
              Forall ([a], TyFn ([list_a; list_a], list_a)) );
            ( "union",
              let a = UF.elt (fresh ()) in
              let set_a = ty_set (TyVar a) in
              Forall ([a], TyFn ([set_a; set_a], set_a)) );
            ( "\\",
              let a = UF.elt (fresh ()) in
              let set_a = ty_set (TyVar a) in
              Forall ([a], TyFn ([set_a; set_a], set_a)) );
            ( "p2i",
              let a = UF.elt (fresh ()) in
              Forall ([a], TyFn ([TyParty a], TyInt)) );
            (* TODO these should only be defined for invariants and ltl *)
            ( "[]",
              let a = UF.elt (fresh ()) in
              Forall ([a], TyFn ([TyVar a], TyBool)) );
            ( "<>",
              let a = UF.elt (fresh ()) in
              Forall ([a], TyFn ([TyVar a], TyBool)) );
            ("/", Forall ([], TyFn ([TyInt; TyInt], TyInt)));
            ("*", Forall ([], TyFn ([TyInt; TyInt], TyInt)));
            ("-", Forall ([], TyFn ([TyInt; TyInt], TyInt)));
            ("+", Forall ([], TyFn ([TyInt; TyInt], TyInt)));
            ("<", Forall ([], TyFn ([TyInt; TyInt], TyBool)));
            ("<=", Forall ([], TyFn ([TyInt; TyInt], TyBool)));
            (">", Forall ([], TyFn ([TyInt; TyInt], TyBool)));
            (">=", Forall ([], TyFn ([TyInt; TyInt], TyBool)));
            ("!", Forall ([], TyFn ([TyBool], TyBool)));
            ("|", Forall ([], TyFn ([TyBool; TyBool], TyBool)));
            ("&", Forall ([], TyFn ([TyBool; TyBool], TyBool)));
            ("==>", Forall ([], TyFn ([TyBool; TyBool], TyBool)));
            ( "!=",
              let a = UF.elt (fresh ()) in
              Forall ([a], TyFn ([TyVar a; TyVar a], TyBool)) );
            ( "==",
              let a = UF.elt (fresh ()) in
              Forall ([a], TyFn ([TyVar a; TyVar a], TyBool)) );
          ];
    }
  in
  dump_env initial;
  initial

let party_instantiated env p =
  match p with Global -> true | Party p -> IMap.mem (UF.value p) env.parties

let rec type_instantiated env t =
  match t with
  | TyParty p -> IMap.mem (UF.value p) env.parties
  | TyVar v ->
    (match IMap.find_opt (UF.value v) env.types with
    | None -> false
    | Some v -> type_instantiated env v)
  | TyInt | TyBool | TyString -> true
  | TyMap (k, v) -> type_instantiated env k && type_instantiated env v
  | TyRecord kvs -> List.for_all (type_instantiated env) (List.map snd kvs)
  | TyFn (args, ret) ->
    List.for_all (type_instantiated env) args && type_instantiated env ret

let check_instantiated, check_instantiated_expr =
  let vp =
    object
      inherit [_] reduce_protocol as super
      method zero = ()
      method plus _ _ = ()

      method! visit__expr env t =
        match t.expr with
        | Var (V (_, v)) ->
          let { typ; own } = t.meta.info in
          if not (type_instantiated env typ) then
            fail ~loc:t.meta.loc "failed to infer type for %s" v;
          if not (party_instantiated env own) then
            fail ~loc:t.meta.loc "failed to infer party for %s" v
        | _ -> super#visit__expr env t
    end
  in
  ( (fun env (tp : tprotocol) -> vp#visit__protocol env tp),
    fun env (tp : texpr) -> vp#visit__expr env tp )

(** this approach of separately traversing the AST is taken because
  trying to qualify during type inference won't work, as types won't be fully
  instantiated.

  to ensure that this works in the presence of transient bindings, we save the
  environment each expression is constructed with (it's persistent anyway) so
  the types of all other variables are in scope at the time are available. *)
let qualify_vars (tp : tprotocol) =
  let vp =
    object
      inherit [_] map_protocol as super

      method! visit_msg ve _vv () (Message { typ; args }) =
        let args = List.map (fun (v, e) -> (v, ve () e)) args in
        Message { typ; args }

      method! visit_msg_destruct _vv _env m = m

      method! visit__expr () e =
        match e.expr with
        | Var (V (p, v)) ->
          (match p with
          | None ->
            let party = find_party_var_by_type_of e.meta.env e in
            { e with expr = Var (V (party, v)) }
          | Some _ -> e)
        | _ -> super#visit__expr () e
    end
  in
  vp#visit__protocol () tp

let check_expr env e =
  let te, env = infer_expr env e in
  check_instantiated_expr env te;
  (* don't insert qualifier. may not be possible for an expression checked in insolation, such as an LTL property. also unnecessary as such expressions are not projected and must reside entirely on one side *)
  (* let te = qualify_vars_expr env te in *)
  (te, env)

let check env p =
  let tp, env = infer env p in
  check_instantiated env tp;
  log "FINISHED";
  dump_env env;
  let tp = qualify_vars tp in
  (tp, env)
