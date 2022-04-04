open Containers
open Common
open Common.Printing
open Ast
open Infer.Cast

type fml =
  | Conj of fml list
  | Disj of fml list
  | If of fml * fml * fml
  | Apply of string * fml list
  | Op of string * fml list
  | Term of string
  (* this is not symmetric but oh well, we only generate this from our specs, not handwrite *)
  | Equals of string * fml
  (* AssignLocal(v, f) is v' = [v EXCEPT ![self] = subst(v, v[self], f) ] *)
  | AssignLocal of string * fml
  | AssignGlobal of string * fml
  (* MapUpdate(a, b, f) is [a EXCEPT ![b] = f] *)
  | MapUpdate of string * string * fml
  | Set of fml list
  | Map of (string * fml) list
  | List of fml list
  (* [i \in s |-> x] *)
  | SetCompConstant of string * string * fml
  | Exists of (string * fml) list * fml
  | Forall of (string * fml) list * fml
  | Let of (string * fml) list * fml
  | Unchanged of string list

type def =
  | Def of string * string list * fml
  | Comment of string
  | Variables of string list
  | Constants of string list

type tla = def list

let cfg_file_template ~constants ~symmetry =
  Format.sprintf
    {|
CONSTANTS
%s
%s
SPECIFICATION Spec
VIEW vars
\* INVARIANT Inv
|}
    constants symmetry

let with_preamble name spec =
  Format.sprintf
    {|
--------------------------------- MODULE %s ---------------------------------

EXTENDS Integers, FiniteSets, Sequences, TLC

VARIABLE messages

Send(m, msgs) ==
    IF m \in DOMAIN msgs THEN
        [msgs EXCEPT ![m] = msgs[m] + 1]
    ELSE
        msgs @@@@ (m :> 1)

Receive(m, msgs) ==
    IF m \in DOMAIN msgs THEN
        [msgs EXCEPT ![m] = msgs[m] - 1]
    ELSE
        msgs

VARIABLE pc

VARIABLE history
@[<h>%a@]

Spec == Init /\ [][Next]_<<vars, history>>

===============================================================================
|}
    name Print.pretty spec

(* |> ignore; *)
(* Format.sprintf "@[<h>%a@]" (PPrint.ToFormatter.pretty 0.8 120) spec *)

(* TODO this is a terrible idea in general as fml is a write-only data structure *)
let subst_fml ~sub ~replacement (f : fml) =
  let rec aux f =
    match f with
    | Term t when String.equal t sub -> Term replacement
    | Term _ -> f
    | Conj es -> Conj (List.map aux es)
    | Disj es -> Disj (List.map aux es)
    | If (p, c, a) -> If (aux p, aux c, aux a)
    (* the following two are the most important cases *)
    (* don't replace function names *)
    | Op (f, args) -> Op (f, List.map aux args)
    | Apply (f, args) -> Apply (f, List.map aux args)
    (* don't replace variables on the left for now *)
    | Equals (a, b) -> Equals (a, aux b)
    | AssignLocal (a, b) -> AssignLocal (a, aux b)
    | AssignGlobal (a, b) -> AssignGlobal (a, aux b)
    | MapUpdate (a, b, f) -> MapUpdate (a, b, aux f)
    | Set es -> Set (List.map aux es)
    (* don't replace map keys *)
    | Map kvs -> Map (List.map (fun (k, v) -> (k, aux v)) kvs)
    | List es -> List (List.map aux es)
    (* don't replace quantified or bound variables *)
    | SetCompConstant (v, s, f) -> SetCompConstant (v, s, aux f)
    | Exists (bs, b) -> Exists (bs, aux b)
    | Forall (bs, b) -> Forall (bs, b)
    | Let (bs, b) -> Let (bs, b)
    (* don't replace in unchanged *)
    | Unchanged _ -> f
  in
  aux f

let rec assignments_fml f =
  match f with
  | Term _ | Op _ | Apply _ | Set _ | SetCompConstant _ | Map _ | Unchanged _
  | MapUpdate _ | List _ | Equals _ ->
    []
  | Conj es | Disj es -> List.concat_map assignments_fml es
  | If (_, c, a) -> List.concat_map assignments_fml [c; a]
  | AssignLocal (a, _) | AssignGlobal (a, _) -> [a]
  | Let (_, b) | Exists (_, b) | Forall (_, b) -> assignments_fml b

open Actions

module Render = struct
  open PPrint

  let rec render_fml (f : fml) =
    let block op fs =
      nest 2
        (concat
           [
             nl;
             fs
             |> List.map (fun f -> concat [string op; space; render_fml f])
             |> separate nl;
           ])
    in
    let quantifier which vars x =
      concat
        [
          string which;
          space;
          separate space
            (vars
            |> List.concat_map (fun (v, s) ->
                   [string v; string "\\in"; render_fml s]));
          space;
          colon;
          (* nest 2 (nl ^^ render_fml x); nl; *)
          space ^^ render_fml x;
        ]
    in
    match f with
    | Conj fs ->
      (* separate (enclose space space (string "/\\")) (List.map render_fml fs) *)
      block "/\\" fs
    | Disj fs ->
      (* separate (enclose space space (string "\\/")) (List.map render_fml fs) *)
      block "\\/" fs
    | If (p, c, a) ->
      parens
        (separate space
           [
             string "IF";
             render_fml p;
             string "THEN";
             render_fml c;
             string "ELSE";
             render_fml a;
           ])
    | Apply (f, args) ->
      concat
        [
          string f;
          (match args with
          | [] -> empty
          | _ -> parens (separate (spaced comma) (List.map render_fml args)));
        ]
    | Op (op, args) ->
      parens
        (separate (enclose space space (string op)) (List.map render_fml args))
    | Term v -> string v
    | Equals (v, e) ->
      concat [string v; enclose space space equals; render_fml e]
    | AssignGlobal (v, e) ->
      concat [string (v ^ "'"); enclose space space equals; render_fml e]
    | AssignLocal (v, e) ->
      separate space
        [
          string (v ^ "'");
          equals;
          brackets
            (separate space
               [
                 string v;
                 string "EXCEPT";
                 string "!" ^^ brackets (string "self");
                 equals;
                 render_fml (subst_fml ~sub:v ~replacement:(v ^ "[self]") e);
               ]);
        ]
    | MapUpdate (a, k, v) ->
      separate space
        [
          brackets
            (separate space
               [
                 string a;
                 string "EXCEPT";
                 string "!" ^^ brackets (string k);
                 equals;
                 render_fml v;
               ]);
        ]
    | Set es -> braces (separate (spaced comma) (List.map render_fml es))
    | List es ->
      enclose (string "<<") (string ">>")
        (separate (spaced comma) (List.map render_fml es))
    | Map kvs ->
      brackets
        (separate (spaced comma)
           (List.map
              (fun (k, v) ->
                separate
                  (enclose space space (string "|->"))
                  [string k; render_fml v])
              kvs))
    | SetCompConstant (i, s, x) ->
      brackets
        (separate space
           [string i; string "\\in"; string s; string "|->"; render_fml x])
    | Let (bs, x) ->
      (match bs with
      | [] -> render_fml x
      | _ ->
        separate space
          [
            string "LET";
            nest 4
              (nl
              ^^ separate nl
                   (List.map
                      (fun (k, v) ->
                        separate space [string k; string "=="; render_fml v])
                      bs)
              ^^ nl);
            string "IN";
          ]
        ^^ nl ^^ render_fml x)
    | Exists (vars, x) -> quantifier "\\E" vars x
    | Forall (vars, x) -> quantifier "\\A" vars x
    | Unchanged vars ->
      string "UNCHANGED" ^^ space
      ^^ render_fml (List (List.map (fun v -> Term v) vars))

  let render_def d =
    match d with
    | Def (name, args, body) ->
      (* these start on a new line *)
      let space_after_eq =
        match body with
        | Conj _ | Disj _ | If (_, _, _) | Let (_, _) -> empty
        | _ -> space
      in
      let body = render_fml body in
      let args =
        match args with
        | [] -> empty
        | _ -> parens (separate (spaced comma) (List.map string args))
      in
      concat [string name; args; space; string "=="; space_after_eq; body]
    | Comment c -> separate space [string "\\*"; string c]
    | Variables vs ->
      separate space
        [string "VARIABLES"; separate (spaced comma) (List.map string vs)]
    | Constants cs ->
      separate space
        [string "CONSTANTS"; separate (spaced comma) (List.map string cs)]

  let render_tla t = List.map render_def t |> separate (nl ^^ nl)
end

let rec translate_expr (e : texpr) =
  match e.expr with
  | Int i -> Term (string_of_int i)
  | Bool b -> Term (b |> string_of_bool |> String.uppercase_ascii)
  | String s -> Term (Format.sprintf {|"%s"|} s)
  | Set es -> Set (List.map translate_expr es)
  | App (f, args) ->
    let args = List.map translate_expr args in
    (match f with
    | "union" -> Op ("\\union", args)
    | "size" -> Apply ("Cardinality", args)
    | "!=" -> Op ("/=", args)
    | "&" -> Op ("/\\", args)
    | "==" -> Op ("=", args)
    | "/" ->
      (* integer division *)
      Op ("\\div", args)
    | "+" | "*" | "-" | "<" | "<=" | ">" | ">=" -> Op (f, args)
    | _ -> Apply (f, args))
  | Var (V (_, v)) -> Term v
  | List _ -> nyi "do expr list"
  | Map _ -> nyi "do expr map"
  | MapComp _ -> nyi "do expr map comp"
  | Tuple (_, _) -> nyi "do expr tuple"
  | Else | Timeout -> nyi "else/timeout"

let rec translate_protocol (p : tprotocol) =
  match p.p with
  | Assign (v, e) ->
    let (V (_, v)) = must_be_var_t v in
    AssignLocal (v, translate_expr e)
  | ReceiveOnly { msg = MessageD { typ; args }; _ } ->
    let pre =
      [
        Op (">", [Term "messages[m]"; Term "0"]);
        Equals ("m.mtype", Term typ);
        Equals ("m.mdest", Term "self");
      ]
    in
    let _recv =
      AssignGlobal ("messages", Apply ("Receive", [Term "m"; Term "messages"]))
    in
    let _assignments =
      List.map
        (fun a ->
          let (V (_, _v)) = must_be_var_t a in
          (* TODO *)
          Term "a")
        args
    in
    Exists ([("m", Term "DOMAIN messages")], Conj pre)
  | Seq ({ p = ReceiveOnly { msg = MessageD { typ; args }; _ }; _ } :: rest) ->
    let pre =
      [
        Op (">", [Term "messages[m]"; Term "0"]);
        Equals ("m.mtype", Term typ);
        Equals ("m.mdest", Term "self");
      ]
    in
    let recv =
      AssignGlobal ("messages", Apply ("Receive", [Term "m"; Term "messages"]))
    in
    let rest =
      let body = List.map translate_protocol rest in
      match args with
      | [] -> body @ [recv]
      | _ ->
        (* TODO this may be wrong. shoudld be translated into assignments? *)
        let bindings =
          args
          |> List.map (fun a ->
                 let (V (_, v)) = must_be_var_t a in
                 (v, Term ("m." ^ v)))
        in
        [Let (bindings, Conj (body @ [recv]))]
    in
    Exists ([("m", Term "DOMAIN messages")], Conj (pre @ rest))
  | Seq ps -> Conj (List.map translate_protocol ps)
  | SendOnly { to_; msg = Message { typ; args }; _ } ->
    let (V (_, to_)) = must_be_var_t to_ in
    let bound =
      List.map
        (fun (v, e) ->
          let (V (_, v)) = must_be_var_t v in
          (v, translate_expr e))
        args
    in
    AssignGlobal
      ( "messages",
        Apply
          ( "Send",
            [
              Map
                (bound
                @ [
                    ("mtype", Term typ);
                    ("msrc", Term "self");
                    ("mdest", Term to_);
                  ]);
              Term "messages";
            ] ) )
  | Imply (c, body) ->
    If (translate_expr c, translate_protocol body, Term "TRUE")
  | BlockingImply (c, body) -> Conj [translate_expr c; translate_protocol body]
  | Call _ -> nyi "translate protocol call"
  (* these should have been removed by now *)
  | Exists (_, _, _) -> nyi "do protocol exists"
  | Forall (_, _, _) -> nyi "do protocol forall"
  | Par _ -> bug "do protocol par"
  | Disj (_, _) -> bug "do protocol disj"
  (* removed much earlier *)
  | Send _ -> bug "do protocol send"
  | Emp -> bug "do protocol emp"
  | Comment (_, _, _) -> bug "do protocol comment"

let translate_tid bound (t : tid) =
  match t.params with
  | [] -> Format.sprintf "%s" t.name
  | ps ->
    let ps1 =
      ps
      |> List.map (fun (p, _) ->
             match List.assoc_opt ~eq:String.equal p bound with
             | None -> p
             | Some p1 -> p1)
    in
    Format.sprintf "<<%s>>" (String.concat ", " (t.name :: ps1))

let fence_to_pc tid f =
  let rec aux bound f =
    match f with
    | ThreadStart ->
      (* use the current thread *)
      let pc = Format.sprintf "pc[self][%s]" (translate_tid bound tid) in
      Equals (pc, Term (string_of_int Actions.default_pc_value))
    | AnyOf fs -> Disj (List.map (aux bound) fs)
    | AllOf fs -> Conj (List.map (aux bound) fs)
    | Cond (t, i) ->
      (* use the thread that this part is dependent on *)
      let pc = Format.sprintf "pc[self][%s]" (translate_tid bound t) in
      Equals (pc, Term (string_of_int i))
    | Forall (v, s, b) ->
      (* rename the variable in case it conflicts with that of the quantifier in scope *)
      let v1 = v ^ "i" in
      let bound = (v, v1) :: bound in
      Forall ([(v1, Term s)], aux bound b)
  in
  aux [] f

let translate_node all_vars pname (id, node) =
  (* not sure if we want to get this from the graph? *)
  let tid = node.protocol.pmeta.tid in
  let pc_current = fence_to_pc tid node.cpre in
  let pc_next =
    AssignLocal
      ( "pc",
        MapUpdate ("pc[self]", translate_tid [] tid, Term (string_of_int id)) )
  in
  let name = Actions.node_name pname (id, node) in
  let history_next =
    AssignGlobal
      ( "history",
        Apply
          ( "Append",
            [
              List
                ([Term (Format.sprintf {|"%s"|} name)]
                @ (node.params |> List.map (fun (p, _) -> Term p)));
              Term "history";
            ] ) )
  in
  let body = translate_protocol node.protocol in
  let assigned = assignments_fml body in
  let unchanged =
    match
      all_vars
      |> List.filter (fun v -> not (List.mem ~eq:String.equal v assigned))
      |> List.filter (fun v -> not (String.equal "pc" v))
    with
    | [] -> []
    | u -> [Unchanged u]
  in
  Def
    ( name,
      "self" :: (node.params |> List.map fst),
      Conj ([pc_current; pc_next; history_next; body] @ unchanged) )

let rec default_value_of_type env t =
  match t with
  | TyParty _ ->
    (* TODO does this matter? *)
    Term "0"
  | TySet _ -> Set []
  | TyList _ -> List []
  | TyVar v -> default_value_of_type env (IMap.find (UF.value v) env.types)
  | TyInt -> Term "0"
  | TyBool -> Term "FALSE"
  | TyString -> Term {|""|}
  | TyFn (_, _) -> nyi "default party fn"

let single_party_to_tla all_vars env nodes pname protocol =
  let vars = Actions.assigned_variables protocol in
  let variables =
    match vars with
    | [] -> []
    | _ ->
      [
        Comment (Format.sprintf "Used by %s" pname);
        Variables (vars |> List.map fst);
      ]
  in

  let vars_def =
    Def (pname ^ "vars", [], List (List.map (fun (v, _) -> Term v) vars))
  in
  let init =
    vars
    |> List.map (fun (v, i) ->
           Equals
             ( v,
               match i.own with
               | Global -> default_value_of_type env i.typ
               | Party par ->
                 (* TODO can this be guaranteed by matching against the current party? *)
                 let (V (_, pname)) =
                   (IMap.find (UF.value par) env.parties).repr
                 in
                 SetCompConstant ("i", pname, default_value_of_type env i.typ)
             ))
  in

  let next =
    IMap.bindings nodes
    |> List.map (fun (id, action) ->
           let body =
             Apply
               ( node_name pname (id, action),
                 Term "self"
                 :: (action.params |> List.map (fun (p, _) -> Term p)) )
           in
           let body =
             match action.params with
             | [] -> body
             | _ ->
               Exists
                 (action.params |> List.map (fun (v, s) -> (v, Term s)), body)
           in
           Exists ([("self", Term pname)], body))
  in
  let actions =
    IMap.bindings nodes |> List.map (translate_node all_vars pname)
  in
  (variables, init, next, actions, vars_def)

let to_tla env party_sizes actions =
  let all_vars =
    (actions |> SMap.bindings
    |> List.map (fun (_, (_g, _n, p)) -> p)
    |> List.concat_map assigned_variables
    |> List.map fst)
    @ ["messages"; "pc"]
    (* pc is always changed so it isn't here *)
  in
  let all_threads =
    actions |> SMap.bindings
    |> List.concat_map (fun (_, (_g, n, _p)) ->
           (* TODO have to use n here because p's threads aren't labelled yet. find a way to remove p from the caller as it should be irrelevant, we can get everything from the action nodes *)

           (* let p = *)
           n |> IMap.bindings
           |> List.map (fun (_, nn) -> nn.protocol.pmeta.tid |> fun t -> t.name)
           (* .protocol in
              print_endline ("!!! " ^ p.pmeta.tid.name);
              Format.eprintf "thing %a@." (Print.pp_tprotocol_untyped ~env) p;
              n |> IMap.bindings |> List.map snd
              |> List.iter (fun nn -> Format.eprintf "node %a@." pp_node nn);
              p.pmeta.tid *))
    |> List.uniq ~eq:String.equal
    (* equal_tid *)
  in
  let party_sets =
    SMap.mapi
      (fun k v ->
        if v < 1 then []
        else
          (* this works for both increasing and decreasng ranges! *)
          List.range 1 v
          |> List.map (fun n ->
                 Format.sprintf "%s%d" (String.lowercase_ascii k) n))
      party_sizes
  in
  (* https://groups.google.com/g/tlaplus/c/WTb6JZDxorE/m/XpOrtsS8AgAJ
     because the n-ary cartesian product is expensive, generate code for exactly the <thread, participant, ...> tuples we'll need
  *)
  let participant_threads_def =
    let product_set =
      actions |> SMap.bindings
      |> List.concat_map (fun (_, (_, n, _)) ->
             n |> IMap.bindings |> List.map snd
             |> List.concat_map (fun node -> all_tids node.protocol)
             |> List.uniq ~eq:equal_tid)
      |> List.map (fun (t : tid) ->
             (* this is similar to translate_tid but different enough *)
             match t.params with
             | [] -> [Term t.name]
             | _ ->
               let params =
                 t.params |> List.map snd
                 |> List.map (fun p -> SMap.find p party_sets)
               in
               let params = [t.name] :: params in
               params |> List.cartesian_product
               |> List.map (fun l -> List (List.map (fun t -> Term t) l)))
      |> List.concat
      |> fun ts -> Set ts
    in
    Def ("threadParticipants", [], product_set)
  in
  let msg_types =
    actions |> SMap.bindings
    |> List.concat_map (fun (_, (_g, _n, p)) -> collect_message_types p)
    |> List.uniq ~eq:String.equal
  in
  let joint =
    actions |> SMap.bindings
    |> List.map (fun (p, (_, nodes, a)) ->
           single_party_to_tla all_vars env nodes p a)
  in
  let variables = List.map (fun (a, _, _, _, _) -> a) joint in
  let inits = List.map (fun (_, a, _, _, _) -> a) joint in
  let nexts = List.map (fun (_, _, a, _, _) -> a) joint in
  let actions1 = List.map (fun (_, _, _, a, _) -> a) joint in
  let var_defs = List.map (fun (_, _, _, _, a) -> a) joint in
  let all_vars_def =
    Def ("vars", [], List (List.map (fun v -> Term v) all_vars))
  in
  let participants = actions |> SMap.bindings |> List.map fst in
  let participants_def =
    Def
      ( "participants",
        [],
        List.fold_right
          (fun c t ->
            match t with
            | None -> Some (Term c)
            | Some t -> Some (Op ("\\union", [Term c; t])))
          participants None
        |> Option.get_exn_or "empty participants" )
  in
  let threads_def =
    Def
      ("threads", [], List.map (fun t -> Term t) all_threads |> fun ts -> Set ts)
  in
  let thread_constants = Constants all_threads in
  let party_constants = Constants (actions |> SMap.bindings |> List.map fst) in
  let symmetry_def, symmetry_cfg =
    let def = "Symmetry" in
    let cfg = Format.sprintf "SYMMETRY %s" def in
    ( Def
        ( def,
          [],
          Op
            ( "\\union",
              actions |> SMap.bindings |> List.map fst
              |> List.map (fun c -> Apply ("Permutations", [Term c])) ) ),
      cfg )
  in
  let party_member_constants =
    Constants (party_sets |> SMap.bindings |> List.concat_map snd)
  in
  let msg_type_constants = Constants msg_types in
  let init =
    Def
      ( "Init",
        [],
        Conj
          (List.concat inits
          @ [
              Equals ("messages", SetCompConstant ("i", "{}", Term "0"));
              Equals ("history", List []);
              Equals
                ( "pc",
                  SetCompConstant
                    ( "i",
                      "participants",
                      SetCompConstant
                        ( "j",
                          (* TODO note that this product needs to be extended for each additional level of nested quantification in a spec *)
                          (* "(threads \\X participants) \\union threads", *)
                          "threadParticipants",
                          Term (string_of_int default_pc_value) ) ) );
            ]) )
  in
  let next = Def ("Next", [], Disj (List.concat nexts)) in
  let spec =
    List.concat
      [
        [
          party_constants;
          party_member_constants;
          thread_constants;
          msg_type_constants;
          symmetry_def;
        ];
        List.concat variables;
        var_defs;
        [all_vars_def; threads_def; participants_def; participant_threads_def];
        [init];
        List.concat actions1;
        [next];
      ]
  in
  let cfg =
    let thread_constants =
      all_threads |> List.map (fun t -> Format.sprintf "  %s = %s" t t)
    in
    let psets =
      actions |> SMap.bindings |> List.map fst
      |> List.concat_map (fun c ->
             let mem = SMap.find c party_sets in
             Format.sprintf "  %s = {%s}" c (mem |> String.concat ", ")
             :: (mem |> List.map (fun m -> Format.sprintf "  %s = %s" m m)))
    in
    let mtypes =
      msg_types |> List.map (fun m -> Format.sprintf "  %s = %s" m m)
    in
    cfg_file_template
      ~constants:(String.concat "\n" (psets @ mtypes @ thread_constants))
      ~symmetry:symmetry_cfg
  in
  (spec, cfg)
