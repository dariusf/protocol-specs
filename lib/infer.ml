open Containers
open Common
open Ast
module Tracing = Ppx_debug.Tracing

let debug = false

let fresh =
  let n = ref 0 in
  fun () ->
    let r = !n in
    incr n;
    r

let rec subst ~from ~to_ in_ =
  if equal_typ from in_ then
    to_
  else
    match in_ with
    | TyParty _ | TyVar _ | TyInt | TyBool -> in_
    | TySet c -> TySet (subst ~from ~to_ c)
    | TyList c -> TyList (subst ~from ~to_ c)
    | TyFn (args, r) ->
      TyFn (List.map (subst ~from ~to_) args, subst ~from ~to_ r)

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
    |> String.concat "\n"; "---- types";
    env.types |> IMap.bindings
    |> List.map (fun (k, v) -> Format.sprintf "%d: %a" k pp_typ v)
    |> String.concat "\n"; "---- vars";
    env.bindings |> SMap.bindings
    (* |> List.map (fun (v, t) -> Format.asprintf "%s : %a" v pp_var_info t) *)
    |> List.map (fun (v, t) -> Format.asprintf "%s : %a" v ppi t)
    |> String.concat "\n"; "---- local vars";
    env.local_bindings |> SMap.bindings
    (* |> List.map (fun (v, t) -> Format.asprintf "%s : %a" v pp_var_info t) *)
    |> List.map (fun (v, t) -> Format.asprintf "%s : %a" v ppi t)
    |> String.concat "\n"; "----------------";
  ]
  |> String.concat "\n\n"

let unify_party_variables a b env =
  let (a2, b2) = (UF.value a, UF.value b) in
  match (IMap.find_opt a2 env.parties, IMap.find_opt b2 env.parties) with
  | (None, None) ->
    UF.union a b;
    Ok env
  | (Some a3, None) ->
    UF.union a b;
    let parties = IMap.add b2 a3 env.parties in
    Ok { env with parties }
  | (None, Some b3) ->
    UF.union a b;
    let parties = IMap.add b2 b3 env.parties in
    Ok { env with parties }
  | (Some a3, Some b3) ->
    if equal_party_info a3 b3 then
      Ok env
    else
      Error
        (`Does_not_unify
          (Format.sprintf "could not unify parties %a and %a" pp_var a3.repr
             pp_var b3.repr))

let%trace rec unify :
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
  if debug then
    Format.printf "unify: %a and %a @." pp_typ a pp_typ b;
  match (a, b) with
  | (TyInt, TyInt) | (TyBool, TyBool) -> Ok env
  | (TyParty a1, TyParty b1) -> unify_party_variables a1 b1 env
  | (TyVar a, TyVar b) ->
    let unify_type_variables a b env =
      let (a1, b1) = (UF.value a, UF.value b) in
      match (IMap.find_opt a1 env.types, IMap.find_opt b1 env.types) with
      | (Some a2, Some b2) ->
        (* this recursive call is the reason this is separate from unify_party_variables *)
        unify a2 b2 env
      | (Some t, None) ->
        let types = env.types in
        (* let types = IMap.remove a2 env.types in *)
        UF.union a b;
        let types = IMap.add (UF.value a) t types in
        Ok { env with types }
      | (None, Some t) ->
        let types = env.types in
        (* let types = IMap.remove b2 env.types in *)
        UF.union a b;
        let types = IMap.add (UF.value a) t types in
        Ok { env with types }
      | (None, None) ->
        UF.union a b;
        Ok env
    in
    unify_type_variables a b env
  | (TySet sa, TySet sb) -> unify sa sb env
  | (TyFn (a1, r1), TyFn (a2, r2)) ->
    if List.length a1 = List.length a2 then
      List.fold_right2
        (fun a b t ->
          let* env = t in
          unify a b env)
        (a1 @ [r1])
        (a2 @ [r2])
        (Ok env)
    else
      Error (`Does_not_unify "argument lists have different lengths")
  | (TyVar a1, b1) | (b1, TyVar a1) ->
    (* if one is a variable, look it up and bind it or unify what is already there *)
    let a2 = UF.value a1 in
    (match IMap.find_opt a2 env.types with
    | None -> Ok { env with types = IMap.add a2 b1 env.types }
    | Some t -> unify t b1 env)
    (* env *)
  | (_, _) ->
    Error
      (`Does_not_unify
        (Format.sprintf "%a and %a do not unify" (Print.pp_typ ~env) a
           (Print.pp_typ ~env) b))

let dump_env env = Format.printf "%s@." (explain_env env)

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
let%trace unify_ownership :
    ownership ->
    ownership ->
    env ->
    (ownership * env, [> `Does_not_unify of string ]) result =
 fun a b env ->
  if debug then
    Format.printf "unify_ownership: %a and %a @." pp_ownership a pp_ownership b;
  match (a, b) with
  | (Global, o1) | (o1, Global) -> Ok (o1, env)
  | (Party p, Party q) ->
    let open Result.Infix in
    let* env = unify_party_variables p q env in
    Ok (a, env)

let rec concretize env t =
  match t with
  | TyParty p -> TyParty (UF.find p)
  | TyInt | TyBool -> t
  | TySet s -> TySet (concretize env s)
  | TyList l -> TyList (concretize env l)
  | TyFn (args, ret) -> TyFn (List.map (concretize env) args, concretize env ret)
  | TyVar v ->
  match IMap.find_opt (UF.value v) env.types with
  | None -> t
  | Some t1 -> concretize env t1

let%trace unify_type_owner :
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
  if debug then
    Format.printf "unify_type_owner: %a and %a @." pp_typ t pp_ownership o;
  match (t, o) with
  | (TyParty _, Global) -> Ok env
  | (TyParty t, Party o) -> unify_party_variables t o env
  | (TyVar _, Party o) -> unify t (TyParty o) env
  | (_, _) -> Error `Type_not_party

let%trace rec infer_all : expr list -> env -> texpr list * ownership * env =
 fun exprs env ->
  List.fold_right
    (fun c (tes, own, env) ->
      let (te, env) = infer_parties_expr c env in
      match unify_ownership own te.meta.info.own env with
      | Ok (own1, env) -> (te :: tes, own1, env)
      | Error (`Does_not_unify s) -> fail ~loc:te.meta.loc "%s" s)
    exprs ([], Global, env)

and infer_parties_expr : expr -> env -> texpr * env =
 fun expr env ->
  if debug then (
    dump_env env;
    Format.printf "infer_parties_expr %a@." pp_expr expr);
  match expr.expr with
  | Int i ->
    ( {
        meta = { loc = expr.meta; info = { typ = TyInt; own = Global } };
        expr = Int i;
      },
      env )
  | Bool b ->
    ( {
        meta = { loc = expr.meta; info = { typ = TyBool; own = Global } };
        expr = Bool b;
      },
      env )
  | Var (V (p, v)) ->
    let { own; typ } = lookup_var ~loc:expr.meta env v in
    let te = Var (V (p, v)) in
    let texpr =
      { meta = { loc = expr.meta; info = { typ; own } }; expr = te }
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
      | Error (`Does_not_unify s) -> fail ~loc:expr.meta "does not unify: %s" s))
  | App (fn, args) ->
    (match lookup_fn env fn with
    | None -> fail ~loc:expr.meta "function %s not bound" fn
    | Some f ->
    match instantiate f with
    | TyFn (targs, ret) ->
      let (tes, own, env) = infer_all args env in

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
              fail ~loc:b.meta.loc "could not unify arg %a of function %s: %s"
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
          meta = { loc = expr.meta; info = { own; typ = rtyp } };
          expr = App (fn, tes);
        },
        env )
    | _ -> fail ~loc:expr.meta "%s is not a function" fn)
  | Set s | List s ->
    begin
      match s with
      | [] ->
        ( {
            meta =
              {
                loc = expr.meta;
                info =
                  {
                    own = fresh_ownership ();
                    typ =
                      (match expr.expr with
                      | Set _ -> TySet (fresh_type ())
                      | List _ -> TyList (fresh_type ())
                      | _ -> bug "unexpected");
                  };
              };
            expr =
              (match expr.expr with
              | Set _ -> Set []
              | List _ -> List []
              | _ -> bug "unexpected");
          },
          env )
      | _ ->
        let (tes, own, env) = infer_all s env in
        let (typ, env) =
          List.fold_right
            (fun c (t, env) ->
              match t with
              | None -> (Some c, env)
              | Some t ->
              match unify c t env with
              | Ok env -> (Some c, env)
              | Error (`Does_not_unify s)
              | Error (`Parties_instantiated_but_different s) ->
                fail ~loc:expr.meta "%s" s)
            (List.map (fun (te : texpr) -> te.meta.info.typ) tes)
            (None, env)
        in
        let typ =
          match expr.expr with
          | List _ ->
            TyList (typ |> Option.get_exn_or "nonempty list should have a type")
          | Set _ ->
            TySet (typ |> Option.get_exn_or "nonempty set should have a type")
          | _ -> bug "unexpected"
        in
        ( { meta = { loc = expr.meta; info = { own; typ } }; expr = Set tes },
          env )
    end
  | Map _ ->
    (* infer_all (List.map snd b) env *)
    nyi "infer_parties_expr map"
  | Tuple (_, _) ->
    (* infer_all [a; b] env *)
    nyi "infer_parties_expr tuple"

(* can no longer use ppx_debug because of labelled arg *)
let rec infer_parties : ?in_seq:bool -> protocol -> env -> tprotocol * env =
 fun ?(in_seq = false) p env ->
  if debug then (
    dump_env env;
    Format.printf "infer %a@." pp_protocol p);
  let p1 = { p = Emp; pmeta = pmeta ~loc:p.pmeta () } in
  match p.p with
  | Emp -> ({ p1 with p = Emp }, env)
  | Call (f, args) ->
    (* TODO lookup the function environment *)
    let (args, env) =
      List.fold_left
        (fun (ts, env) c ->
          let (te, env) = infer_parties_expr c env in
          (te :: ts, env))
        ([], env) args
    in
    let args = List.rev args in
    ({ p1 with p = Call (f, args) }, env)
  | Send { from; to_; msg = Message { args; typ = mtype } } ->
    let (fm, tm) = (from.meta, to_.meta) in
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
    let (targs, env) =
      List.fold_right
        (fun (k, arg) (targs, env) ->
          let (targ, env) = infer_parties_expr arg env in

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
            if in_seq then
              let local_bindings = SMap.add v vi env.local_bindings in
              { env with local_bindings }
            else
              env
          in
          let k1 =
            { expr = Var (V (pv, v)); meta = { loc = k.meta; info = vi } }
          in

          ((k1, targ) :: targs, env))
        args ([], env)
    in

    (* sender is now owned by recipient *)
    let recipient =
      match t_vi.typ with
      | TyParty p -> Party p
      | _ ->
        failwith "recipient is not a party, should have been caught earlier"
    in
    (* but only locally *)
    let env =
      if in_seq then
        {
          env with
          local_bindings =
            SMap.add from { f_vi with own = recipient } env.local_bindings;
        }
      else
        env
    in
    (* receiver is also owned by receiver *)
    let env =
      if in_seq then
        {
          env with
          local_bindings =
            SMap.add to_ { t_vi with own = recipient } env.local_bindings;
        }
      else
        env
    in

    ( {
        p1 with
        p =
          Send
            {
              from =
                {
                  meta = { loc = fm; info = { typ = f_vi.typ; own = f_vi.own } };
                  expr = Var (V (fp, from));
                };
              to_ =
                {
                  meta = { loc = tm; info = { typ = t_vi.typ; own = t_vi.own } };
                  expr = Var (V (tp, to_));
                };
              msg = Message { args = targs; typ = mtype };
            };
      },
      env )
  | Assign (v, e) ->
    let vm = v.meta in
    let (V (vp, v)) = must_be_var v in

    let (env, { own = olhs; typ = tlhs }) =
      (* whether or not to look up existing variables controls if the a subsequent assignment to a variable can fill in a previously-abstract type *)
      match lookup env v with None -> fresh_var env v | Some vi -> (env, vi)
    in
    let (trhs, env) = infer_parties_expr e env in
    let env =
      match unify tlhs trhs.meta.info.typ env with
      | Ok env -> env
      | Error (`Parties_instantiated_but_different _)
      | Error (`Does_not_unify _) ->
        fail ~loc:vm "could not unify sides of assignment"
    in
    (* right and left sides must be owned by same party *)
    (match unify_ownership olhs trhs.meta.info.own env with
    | Error (`Does_not_unify s) -> fail ~loc:vm "%s" s
    | Ok (_, env) ->
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

      ( {
          p1 with
          p =
            Assign
              ( {
                  expr = Var (V (vp, v));
                  meta = { loc = vm; info = { typ = tlhs; own = olhs } };
                },
                trhs );
        },
        env ))
  | Imply (c, p) ->
    let (tc, env) = infer_parties_expr c env in
    let (tp, env) = infer_parties p env in

    (match unify tc.meta.info.typ TyBool env with
    | Ok _ -> ()
    | Error (`Does_not_unify s) -> fail ~loc:tc.meta.loc "%s" s
    | Error (`Parties_instantiated_but_different s) ->
      fail ~loc:tc.meta.loc "%s" s);

    ({ p1 with p = Imply (tc, tp) }, env)
  | BlockingImply (c, p) ->
    let (tc, env) = infer_parties_expr c env in
    let (tp, env) = infer_parties p env in
    (match unify tc.meta.info.typ TyBool env with
    | Ok _ -> ()
    | Error (`Does_not_unify s) -> fail ~loc:tc.meta.loc "%s" s
    | Error (`Parties_instantiated_but_different s) ->
      fail ~loc:tc.meta.loc "%s" s);

    ({ p1 with p = BlockingImply (tc, tp) }, env)
  | Seq s ->
    (* List.fold_right infer_parties s env *)
    let local_bindings = env.local_bindings in
    let (ts, env) =
      List.fold_left
        (fun (ts, env) c ->
          let (te, env) = infer_parties ~in_seq:true c env in
          (te :: ts, env))
        ([], env) s
    in
    let ts = List.rev ts in

    (* restore *)
    let env = { env with local_bindings } in

    ({ p1 with p = Seq ts }, env)
  | Par ps ->
    let (ts, env) =
      List.fold_left
        (fun (ts, env) p ->
          let (tp, env) = infer_parties p env in
          (tp :: ts, env))
        ([], env) ps
    in
    let ts = List.rev ts in
    ({ p1 with p = Par ts }, env)
  | Disj (a, b) ->
    let (ta, env) = infer_parties a env in
    let (tb, env) = infer_parties b env in
    ({ p1 with p = Disj (ta, tb) }, env)
  | Forall (e, s, pb) ->
    let (em, sm) = (e.meta, s.meta) in
    let (V (pe, e)) = must_be_var e in
    let (V (ps, s)) = must_be_var s in

    (* this binds only one new name, e. s is already defined *)
    let (env, party, own) =
      let pl = p.pmeta in
      match lookup_var ~loc:pl env s with
      | { typ = TySet (TyParty _ as p); own } -> (env, p, own)
      (* | Some vi -> fail "not a party set: %a" pp_var_info vi *)
      | { typ; own } ->
        let[@warning "-8"] (TyVar p) = fresh_type () in
        let env =
          match unify typ (TySet (TyParty p)) env with
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

    let (tp1, env) = infer_parties pb env in

    (* unbind the bound variable *)
    let env = { env with bindings = SMap.remove e env.bindings } in

    (* TODO this always unbinds e even if it's been redefined, but we'll worry about that later *)
    let e =
      {
        expr = Var (V (pe, e));
        meta = { loc = em; info = { typ = party; own } };
      }
    in
    let s =
      {
        expr = Var (V (ps, s));
        meta = { loc = sm; info = { typ = TySet party; own } };
      }
    in

    ({ p1 with p = Forall (e, s, tp1) }, env)
  | Exists (_, _, _) -> nyi "infer_parties exists"
  | Comment (_, _, _) -> bug "infer_parties doesn't expect comments"
  | SendOnly _ -> bug "infer_parties doesn't expect send only"
  | ReceiveOnly _ -> bug "infer_parties doesn't expect receive only"

let initiator env p =
  let rec aux p =
    match p.p with
    | Seq (s :: _) -> aux s
    | Seq _ -> bug "empty seq"
    | Par [] -> bug "empty par"
    | Par ps ->
      let it = List.map aux ps in
      foldr1
        (fun (c, p) (t, _) ->
          if equal_party_info c t then
            (c, p)
          else
            fail ~loc:p.pmeta.loc "different initiator in par")
        (List.combine it ps)
      |> ignore;
      List.hd it
    | Disj (a, b) ->
      let ia = aux a in
      let ib = aux b in
      if equal_party_info ia ib then
        ia
      else
        fail ~loc:p.pmeta.loc "different initiator in disjunction" List.for_all
          aux [a; b]
    | Send { from; _ } ->
      (match from.meta.info.typ with
      | TyParty p -> IMap.find (UF.value p) env.parties
      | _ -> fail ~loc:from.meta.loc "no initiator")
    | Call (f, _) ->
      (match SMap.find_opt f env.subprotocols with
      | None -> fail ~loc:p.pmeta.loc "undefined function %s" f
      | Some { initiator; _ } -> { repr = var initiator })
    | Assign (e, _) | BlockingImply (e, _) | Imply (e, _) ->
      (match e.meta.info.own with
      | Party p -> IMap.find (UF.value p) env.parties
      | _ -> fail ~loc:e.meta.loc "no initiator")
    | Forall (_, _, p) | Exists (_, _, p) -> aux p
    | ReceiveOnly _ | SendOnly _ -> bug "initiator: multiparty spec only"
    | Comment _ -> bug "initiator comment"
    | Emp -> bug "initiator empty"
  in
  aux p

let parse_spec file =
  (* let p = Parsing.parse_inc file in *)
  match
    if String.equal file "-" then
      Parsing.parse_mono_ic file stdin
    else
      Parsing.parse_mono file
  with
  | Ok p -> p
  | Error s -> failwith s

let initial_env parties =
  let (parties, var_info) =
    parties
    |> List.map (fun p ->
           let i = fresh () in
           let r = UF.elt i in
           let name = var_name p.repr in
           let vi = { typ = TySet (TyParty r); own = Global } in
           ((i, p), (name, vi)))
    |> List.split
  in
  {
    empty_env with
    parties = IMap.of_list parties;
    bindings = SMap.of_list var_info;
    polymorphic =
      SMap.of_list
        [
          ( "union",
            let a = UF.elt (fresh ()) in
            let set_a = TySet (TyVar a) in
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
          ( "size",
            let a = UF.elt (fresh ()) in
            Forall ([a], TyFn ([TySet (TyVar a)], TyInt)) );
          ( "!=",
            let a = UF.elt (fresh ()) in
            Forall ([a], TyFn ([TyVar a; TyVar a], TyBool)) );
          ( "==",
            let a = UF.elt (fresh ()) in
            Forall ([a], TyFn ([TyVar a; TyVar a], TyBool)) );
        ];
  }

let party_instantiated env p =
  match p with Global -> true | Party p -> IMap.mem (UF.value p) env.parties

let rec type_instantiated env t =
  match t with
  | TyParty p -> IMap.mem (UF.value p) env.parties
  | TyVar v ->
    (match IMap.find_opt (UF.value v) env.types with
    | None -> false
    | Some v -> type_instantiated env v)
  | TyInt | TyBool -> true
  | TySet a | TyList a -> type_instantiated env a
  | TyFn (args, ret) ->
    List.for_all (type_instantiated env) args && type_instantiated env ret

let rec check_instantiated_expr env (t : texpr) =
  match t.expr with
  | Int _ | Bool _ -> ()
  | Set s -> List.iter (check_instantiated_expr env) s
  | List l -> List.iter (check_instantiated_expr env) l
  | Var (V (_, v)) ->
    let { typ; own } = t.meta.info in
    if not (type_instantiated env typ) then
      fail ~loc:t.meta.loc "failed to infer type for %s" v;
    if not (party_instantiated env own) then
      fail ~loc:t.meta.loc "failed to infer party for %s" v
  | App (_, args) -> List.iter (check_instantiated_expr env) args
  | Map _ -> nyi "map check_instanted_expr"
  | Tuple (_, _) -> nyi "tuple check_instanted_expr"

let rec check_instantiated env p =
  match p.p with
  | Seq s | Par s -> List.iter (check_instantiated env) s
  | Disj (a, b) -> List.iter (check_instantiated env) [a; b]
  | Send { from; to_; msg = Message { args; _ } } ->
    check_instantiated_expr env from;
    check_instantiated_expr env to_;
    List.iter (fun (_, e) -> check_instantiated_expr env e) args
  | Call (_, args) -> List.iter (check_instantiated_expr env) args
  | Assign (v, e) ->
    check_instantiated_expr env v;
    check_instantiated_expr env e
  | Imply (c, b) | BlockingImply (c, b) ->
    check_instantiated_expr env c;
    check_instantiated env b
  | Forall (v, s, b) | Exists (v, s, b) ->
    check_instantiated_expr env v;
    check_instantiated_expr env s;
    check_instantiated env b
  | Emp -> bug "emp should not appear"
  | SendOnly _ -> bug "send only should not appear"
  | ReceiveOnly _ -> bug "receive only should not appear"
  | Comment (_, _, _) -> bug "comment should not appear"
