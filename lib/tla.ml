open Containers
open Common
open Common.Printing
open Ast

type fml =
  | Conj of fml list
  | Disj of fml list
  | If of fml * fml * fml
  | Apply of string * fml list
  | Op of string * fml list
  | Term of string
  (* this is not symmetric but oh well, we only generate this from our specs, not hadnwrite *)
  | Equals of string * fml
  (* AssignLocal(v, f) is v' = [v EXCEPT ![self] = subst(v, v[self], f) ] *)
  | AssignLocal of string * fml
  | AssignGlobal of string * fml
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
  | Constant of string

type tla = def list

let with_preamble name spec =
  Format.sprintf
    {|
--------------------------------- MODULE %s ---------------------------------

EXTENDS Naturals, FiniteSets, Sequences

VARIABLE messages

Send(m, msgs) ==
    IF m \in DOMAIN msgs THEN
        [msgs EXCEPT ![m] = msgs[m] + 1]
    ELSE
        msgs @@ (m :> 1)

Receive(m, msgs) ==
    IF m \in DOMAIN msgs THEN
        [msgs EXCEPT ![m] = msgs[m] - 1]
    ELSE
        msgs

VARIABLE pc

@[<h>%a@]

Spec == Init /\ [][Next]_vars

===============================================================================
|}
    name
    (PPrint.ToFormatter.pretty 0.8 120)
    spec

(* |> ignore; *)
(* Format.sprintf "@[<h>%a@]" (PPrint.ToFormatter.pretty 0.8 120) spec *)

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
  | List _ | Equals _ ->
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
    let quantifier vars x =
      concat
        [
          string "\\E"; space;
          separate space
            (vars
            |> List.concat_map (fun (v, s) ->
                   [string v; string "\\in"; render_fml s])); space; colon;
          (* nest 2 (nl ^^ render_fml x); nl; *) space ^^ render_fml x;
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
             string "IF"; render_fml p; string "THEN"; render_fml c;
             string "ELSE"; render_fml a;
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
          string (v ^ "'"); equals;
          brackets
            (separate space
               [
                 string v; string "EXCEPT";
                 string "!" ^^ brackets (string "self"); equals;
                 render_fml (subst_fml ~sub:v ~replacement:(v ^ "[self]") e);
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
              ^^ nl); string "IN";
          ]
        ^^ nl ^^ render_fml x)
    | Exists (vars, x) -> quantifier vars x
    | Forall (vars, x) -> quantifier vars x
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
      separate space [string "VARIABLES"; separate space (List.map string vs)]
    | Constant c -> separate space [string "CONSTANT"; string c]

  let render_tla t = List.map render_def t |> separate (nl ^^ nl)
end

let assigned_variables (t : tprotocol) =
  let rec aux t =
    match t.p with
    | Assign (v, _) ->
      let info = v.meta.info in
      let (V (_, v)) = must_be_var_t v in
      [(v, info)]
    | Seq es | Par es -> List.concat_map aux es
    | Disj (a, b) -> aux a @ aux b
    | Imply (_, b) | BlockingImply (_, b) | Forall (_, _, b) ->
      (* ignore the variables in forall *)
      aux b
    | SendOnly _ | ReceiveOnly _ ->
      (* ignore variables *)
      []
    | Exists (_, _, _) -> nyi "used variables exists"
    | Send _ -> bug "used variable send"
    | Comment (_, _, _) -> bug "used variables comment"
    | Emp -> bug "used variables emp"
  in
  aux t |> List.uniq ~eq:(fun (a, _) (b, _) -> String.equal a b)

let rec translate_expr (e : texpr) =
  match e.expr with
  | Int i -> Term (string_of_int i)
  | Bool b -> Term (b |> string_of_bool |> String.uppercase_ascii)
  | Set es -> Set (List.map translate_expr es)
  | App (f, args) ->
    let args = List.map translate_expr args in
    (match f with
    | "union" -> Op ("\\union", args)
    | "size" -> Apply ("Cardinality", args)
    | "!=" -> Op ("/=", args)
    | "&" -> Op ("/\\", args)
    | "==" -> Op ("=", args)
    | "+" | "*" | "-" | "/" | "<" | "<=" | ">" | ">=" -> Op (f, args)
    | _ -> Apply (f, args))
  | Var (V (_, v)) -> Term v
  | List _ -> nyi "do expr list"
  | Map _ -> nyi "do expr map"
  | Tuple (_, _) -> nyi "do expr tuple"

let rec translate_protocol (p : tprotocol) =
  match p.p with
  | Assign (v, e) ->
    let (V (_, v)) = must_be_var_t v in
    AssignLocal (v, translate_expr e)
  | Seq ({ p = ReceiveOnly { msg = MessageD { typ; args }; _ }; _ } :: rest) ->
    let pre = [Equals ("m.mtype", Term typ); Equals ("m.mdest", Term "self")] in
    let recv = AssignGlobal ("messages", Apply ("Receive", [Term "m"])) in
    let body = List.map translate_protocol rest in
    let rest =
      match args with
      | [] -> body @ [recv]
      | _ ->
        let bindings =
          args
          |> List.map (fun a ->
                 let (V (_, v)) = must_be_var_t a in
                 (v, Term ("m." ^ v)))
        in
        [Let (bindings, Conj (body @ [recv]))]
    in
    Exists ([("m", Term "messages")], Conj (pre @ rest))
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
    Equals
      ( "messages'",
        Apply
          ( "Send",
            [
              Map
                (bound
                @ [
                    ("mtype", Term typ); ("msrc", Term "self");
                    ("mdest", Term to_);
                  ]);
            ] ) )
  | Imply (c, body) ->
    If (translate_expr c, translate_protocol body, Term "TRUE")
  | BlockingImply (c, body) -> Conj [translate_expr c; translate_protocol body]
  (* these should have been removed by now *)
  | ReceiveOnly _ -> bug "receive should appear only inside a seq by this point"
  | Exists (_, _, _) -> nyi "do protocol exists"
  | Forall (_, _, _) -> nyi "do protocol forall"
  | Par _ -> bug "do protocol par"
  | Disj (_, _) -> bug "do protocol disj"
  (* removed much earlier *)
  | Send _ -> bug "do protocol send"
  | Emp -> bug "do protocol emp"
  | Comment (_, _, _) -> bug "do protocol comment"

let snake_to_camel s =
  s |> String.lowercase_ascii |> String.capitalize_ascii
  |> Str.global_substitute (Str.regexp {|_\([a-z]\)|}) (fun s ->
         Str.matched_group 1 s |> String.lowercase_ascii
         |> String.capitalize_ascii)

let node_name party (id, node) =
  let prefix =
    match node.protocol.p with
    | Seq ({ p = SendOnly { msg = Message { typ; _ }; _ }; _ } :: _)
    | SendOnly { msg = Message { typ; _ }; _ } ->
      Format.sprintf "Send%s" (typ |> snake_to_camel)
    | Seq ({ p = ReceiveOnly { msg = MessageD { typ; _ }; _ }; _ } :: _)
    | ReceiveOnly { msg = MessageD { typ; _ }; _ } ->
      Format.sprintf "Receive%s" (typ |> snake_to_camel)
    | Seq ({ p = Assign (v, _); _ } :: _) | Assign (v, _) ->
      let (V (_, v)) = must_be_var_t v in
      Format.sprintf "Change%s" (v |> snake_to_camel)
    | _ -> "Action"
  in
  Format.sprintf "%s%s%d" party prefix id

let translate_node all_vars graph pname (id, node) =
  (* not sure if we want to get this from the graph? *)
  let pc_current =
    let set_pc pred = Equals ("pc", Term (string_of_int pred)) in
    match G.pred graph id with
    | [] -> []
    | [pred] -> [set_pc pred]
    | preds -> [Disj (preds |> List.map set_pc)]
  in
  let pc_next = AssignLocal ("pc", Term (string_of_int id)) in
  let body = translate_protocol node.protocol in
  let assigned = assignments_fml body in
  let unchanged =
    match
      all_vars
      |> List.filter (fun v -> not (List.mem ~eq:String.equal v assigned))
    with
    | [] -> []
    | u -> [Unchanged u]
  in
  Def
    ( node_name pname (id, node),
      "self" :: (node.params |> List.map fst),
      Conj (pc_current @ [pc_next; body] @ unchanged) )

let rec default_value_of_type env t =
  match t with
  | TyParty _ -> nyi "default party party"
  | TySet _ -> Set []
  | TyList _ -> List []
  | TyVar v -> default_value_of_type env (IMap.find (UF.value v) env.types)
  | TyInt -> Term "0"
  | TyBool -> Term "FALSE"
  | TyFn (_, _) -> nyi "default party fn"

let single_party_to_tla all_vars env graph nodes party protocol =
  let (V (_, pname)) = party.repr in
  let vars = assigned_variables protocol in
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
    IMap.bindings nodes |> List.map (translate_node all_vars graph pname)
  in
  (variables, init, next, actions, vars_def)

let to_tla parties env actions =
  let all_vars =
    (actions
    |> List.map (fun (_g, _n, p) -> p)
    |> List.concat_map assigned_variables
    |> List.map fst)
    @ ["messages"]
    (* pc is always changed so it isn't here *)
  in
  let joint =
    List.mapi
      (fun i (graph, nodes, a) ->
        single_party_to_tla all_vars env graph nodes (List.nth parties i) a)
      actions
  in
  let variables = List.map (fun (a, _, _, _, _) -> a) joint in
  let inits = List.map (fun (_, a, _, _, _) -> a) joint in
  let nexts = List.map (fun (_, _, a, _, _) -> a) joint in
  let actions = List.map (fun (_, _, _, a, _) -> a) joint in
  let var_defs = List.map (fun (_, _, _, _, a) -> a) joint in
  let all_vars_def =
    Def ("vars", [], List (List.map (fun v -> Term v) all_vars))
  in
  let parties =
    List.map
      (fun p ->
        let (V (_, name)) = p.repr in
        name)
      parties
  in
  let party_constants = List.map (fun n -> Constant n) parties in
  let init = Def ("Init", [], Conj (List.concat inits)) in
  let next = Def ("Next", [], Disj (List.concat nexts)) in
  List.concat
    [
      party_constants; var_defs; [all_vars_def]; List.concat variables; [init];
      List.concat actions; [next];
    ]
