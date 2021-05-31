open Containers
open Common
open Ast

module Node = struct
  type t = int

  let compare = Int.compare

  let hash = Hashtbl.hash

  let equal = ( = )
end

module G = Graph.Persistent.Digraph.Concrete (Node)

let all_edges g =
  let res = ref [] in
  G.iter_edges_e (fun e -> res := e :: !res) g;
  !res

let pp_graph fmt g =
  Format.fprintf fmt "%s"
    (all_edges g
    |> List.map (fun (a, b) -> Format.sprintf "%d -> %d" a b)
    |> String.concat ", ")

let merge_graphs g1 g2 =
  g2
  |> G.fold_vertex (fun v g -> G.add_vertex g v) g1
  |> G.fold_edges_e (fun e g -> G.add_edge_e g e) g1

let find_vertices f g =
  let res = ref [] in
  G.iter_vertex (fun v -> if f v then res := v :: !res) g;
  !res

(** glues two dags together: the ending nodes of g1 get edges to the starting nodes of g2.  a cyclic graph would require something fancier. *)
let concat_graphs g1 g2 =
  let ending = find_vertices (fun v -> G.out_degree g1 v = 0) g1 in
  let starting = find_vertices (fun v -> G.in_degree g2 v = 0) g2 in
  merge_graphs g1 g2
  |> List.fold_right
       (fun s g -> List.fold_right (fun e g -> G.add_edge g e s) ending g)
       starting

type constr = Mutex of int [@@deriving show { with_path = false }]

type node = {
  preconditions : texpr list;
  protocol : tprotocol;
  params : (string * string) list;
  constraints : constr list;
}
[@@deriving show { with_path = false }]

let fresh_id =
  let n = ref 0 in
  fun () ->
    let r = !n in
    incr n;
    r

(** groups a seq into sub-seqs such that each one corresponds to an atomic action.

    subactions are

    - send
    - receive
    - assignment
    - something else (like a disj), but containing only subactions

    atomic actions are

    1. a+
    2. s
    3. r a*
    4. e

    there are other longer sequences which could be actions, like a+ s, but we'll keep it simple for now.
*)
let group_seq (ts : tprotocol list) =
  let rec loop curr acc (ts : tprotocol list) =
    match ts with
    | [] ->
      curr :: acc
      (* remove empty seqs. we could not add them instead, but this seems cleaner *)
      |> List.filter (function [] -> false | _ -> true)
      |> List.map List.rev |> List.rev
    | t :: ts1 ->
    match t.p with
    | ReceiveOnly _ ->
      (* also terminate current sequence *)
      loop [t] (curr :: acc) ts1
    | Assign (_, _) -> loop (t :: curr) acc ts1
    | SendOnly _ | _ ->
      (* always terminate the current sequence, and don't even start a new one *)
      loop [] ([t] :: curr :: acc) ts1
  in
  let label_action t =
    match t with
    | { p = ReceiveOnly _; _ } :: _
    | { p = SendOnly _; _ } :: _
    | { p = Assign _; _ } :: _ ->
      (`Atomic, t)
    | [{ p = _; _ }] -> (`Composite, t)
    | _ -> bug "not a valid composite action"
  in
  loop [] [] ts |> List.map label_action

let rec used_names_expr (t : texpr) =
  match t.expr with
  | Int _ | Bool _ -> []
  | Map kvs -> List.concat_map (fun (_, v) -> used_names_expr v) kvs
  | Set args | List args | App (_, args) -> List.concat_map used_names_expr args
  | Var (V (_, v)) -> [v]
  | Tuple (_, _) -> nyi "tuple used names"

let rec used_names (t : tprotocol) =
  match t.p with
  | Seq es | Par es -> List.concat_map used_names es
  | Disj (a, b) -> used_names a @ used_names b
  | Assign (v, e) -> used_names_expr v @ used_names_expr e
  | Imply (c, b) | BlockingImply (c, b) -> used_names_expr c @ used_names b
  | Forall (v, s, b) -> used_names_expr v @ used_names_expr s @ used_names b
  | SendOnly { from; to_; msg = Message { args; _ } } ->
    List.concat_map used_names_expr ([from; to_] @ List.map snd args)
  | ReceiveOnly { from; to_; msg = MessageD { args; _ } } ->
    List.concat_map used_names_expr ([from; to_] @ args)
  | Exists (_, _, _) -> nyi "used names exists"
  | Send _ -> bug "used names send"
  | Comment (_, _, _) -> bug "used names comment"
  | Emp -> bug "used names emp"

let rec split_actions ~preconditions ~params (t : tprotocol) =
  match t.p with
  | Forall (v, s, p) ->
    let (V (_, v1)) = must_be_var_t v in
    let (V (_, s1)) = must_be_var_t s in
    split_actions ~preconditions ~params:((v1, s1) :: params) p
  | Seq ps ->
    let ps1 = group_seq ps in
    let nodes =
      List.map
        (fun (comp, pr) ->
          match comp with
          | `Atomic ->
            let id = fresh_id () in
            let g = G.add_vertex G.empty id in
            let used_params =
              List.filter
                (fun (pa, _) ->
                  List.mem ~eq:String.equal pa
                    (pr |> List.concat_map used_names
                   |> List.uniq ~eq:String.equal))
                params
            in
            let m =
              IMap.singleton id
                {
                  constraints = [];
                  params = used_params;
                  preconditions;
                  protocol = { t with p = Seq pr };
                }
            in
            (g, m)
          | `Composite ->
            let[@warning "-8"] [p] = pr in
            split_actions ~preconditions ~params p)
        ps1
    in
    let res =
      List.fold_right
        (fun (gc, mc) (gt, mt) ->
          ( concat_graphs gc gt,
            IMap.union (fun _ _ _ -> bug "failed to merge node") mc mt ))
        nodes (G.empty, IMap.empty)
    in
    res
  | Assign (_, _) ->
      (* this happens when an assignment is on its own, outside a seq. the simplest thing to do is treat it as a seq *)
      split_actions ~preconditions ~params {t with p = Seq[t]}
  | SendOnly _ -> bug "find actions send"
  | ReceiveOnly _ -> bug "find actions receive"
  | Par ps ->
    let nodes = List.map (split_actions ~preconditions ~params) ps in
    let res =
      List.fold_right
        (fun (gc, mc) (gt, mt) ->
          ( merge_graphs gc gt,
            IMap.union (fun _ _ _ -> bug "failed to merge node") mc mt ))
        nodes (G.empty, IMap.empty)
    in
    res
  | Disj (a, b) ->
    (* TODO mutually exclusive constraints *)
    let (ag, am) = split_actions ~preconditions ~params a in
    let (bg, bm) = split_actions ~preconditions ~params b in
    let res =
      ( merge_graphs ag bg,
        IMap.union (fun _ _ _ -> bug "failed to merge node") am bm )
    in
    res
  | Imply (c, p) | BlockingImply (c, p) ->
    split_actions ~preconditions:(c :: preconditions) ~params p
  | Exists (_, _, _) -> nyi "find actions exists"
  | Comment (_, _, _) -> bug "find actions comment"
  | Emp -> bug "find actions empty"
  | Send _ -> bug "find actions send"

let compact = false

let maybe_nl = if compact then "" else "\n"

let maybe_indent = if compact then "" else "  "

let to_graphviz env g m =
  let strip_whitespace s =
    s
    |> Str.global_replace (Str.regexp "  +") ""
    |> String.replace ~which:`All ~sub:"\n" ~by:"\\n"
  in
  let nodes =
    IMap.bindings m
    |> List.map
         (fun (id, { preconditions; params; constraints = _; protocol }) ->
           let pre =
             match preconditions with
             | [] -> ""
             | _ ->
               Format.sprintf "{%a}\\n"
                 (List.pp ~pp_sep:(pp_const ", ") (Print.pp_texpr_untyped ~env))
                 preconditions
           in
           let params =
             match params with
             | [] -> ""
             | _ ->
               Format.sprintf "λ %a.\\n"
                 (List.pp ~pp_sep:(pp_const ", ")
                    (Pair.pp ~pp_sep:(pp_const ":") Format.pp_print_string
                       Format.pp_print_string))
                 params
           in
           Format.sprintf "%d [label=\"%s%s%a\"];" id pre params
             (Print.pp_tprotocol_untyped ~env)
             protocol
           |> strip_whitespace |> ( ^ ) maybe_indent)
  in
  let edges =
    all_edges g
    |> List.map (fun (a, b) -> Format.sprintf "%s%d -> %d;" maybe_indent a b)
  in
  Format.sprintf "digraph G {%s%s\n%s%s}" maybe_nl
    (nodes |> String.concat maybe_nl)
    (edges |> String.concat maybe_nl)
    maybe_nl

let split_into_actions : tprotocol -> G.t * node IMap.t =
 fun t ->
  let (g, m) = split_actions ~preconditions:[] ~params:[] t in
  (g, m)

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
