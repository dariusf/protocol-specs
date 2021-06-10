open Containers
open Common
open Ast
module Tracing = Ppx_debug.Tracing

module Node = struct
  type t = int

  let compare = Int.compare

  let hash = Hashtbl.hash

  let equal = ( = )
end

module G = struct
  include Graph.Persistent.Digraph.Concrete (Node)

  let all_edges g =
    let res = ref [] in
    iter_edges_e (fun e -> res := e :: !res) g;
    !res

  let find_vertices f g =
    let res = ref [] in
    iter_vertex (fun v -> if f v then res := v :: !res) g;
    !res

  let pp fmt g =
    let vertices = find_vertices (fun _ -> true) g in
    let edges =
      all_edges g |> List.map (fun (a, b) -> Format.sprintf "%d -> %d" a b)
    in
    Format.fprintf fmt "%a %a" (List.pp Int.pp) vertices (List.pp String.pp)
      edges

  let merge_graphs g1 g2 =
    g2
    |> fold_vertex (fun v g -> add_vertex g v) g1
    |> fold_edges_e (fun e g -> add_edge_e g e) g1

  (** glues two dags together: the ending nodes of g1 get edges to the starting nodes of g2.  a cyclic graph would require something fancier. *)
  let concat_graphs g1 g2 =
    let ending = find_vertices (fun v -> out_degree g1 v = 0) g1 in
    let starting = find_vertices (fun v -> in_degree g2 v = 0) g2 in
    merge_graphs g1 g2
    |> List.fold_right
         (fun s g -> List.fold_right (fun e g -> add_edge g e s) ending g)
         starting
end

type fence_cond =
  (* TODO tid? *)
  | ThreadStart
  | AnyOf of fence_cond list
  | AllOf of fence_cond list
  | Forall of string * string * fence_cond
  | Cond of tid * int
[@@deriving show { with_path = false }]

let rec render_fence f =
  match f with
  | ThreadStart -> "start"
  | AnyOf fs ->
    fs |> List.map render_fence |> String.concat ", "
    |> Format.sprintf "Any(%s)"
  | AllOf fs ->
    fs |> List.map render_fence |> String.concat ", "
    |> Format.sprintf "All(%s)"
  | Forall (s, v, b) -> Format.sprintf "∀ %s:%s. %s" s v (render_fence b)
  | Cond (tid, pc) -> Format.sprintf "%a = %d" Print.pp_tid tid pc

let compute_fence tid id (t : tprotocol) =
  let rec aux t =
    match t.p with
    | Forall (v, s, b) ->
      let (V (_, v)) = must_be_var_t v in
      let (V (_, s)) = must_be_var_t s in
      Forall (v, s, aux b)
    | Par ps -> AllOf (List.map aux ps)
    | Disj (a, b) -> AnyOf [aux a; aux b]
    | SendOnly _ | ReceiveOnly _ | Seq _ | Assign (_, _) -> Cond (tid, id)
    | Imply (_, b) | BlockingImply (_, b) -> aux b
    | Exists (_, _, _) -> nyi "compute fence Exists"
    | Comment (_, _, _) -> bug "compute fence Comment"
    | Send _ -> bug "compute fence Send"
    | Emp -> bug "compute fence Emp"
  in
  aux t

type constr = Mutex of int [@@deriving show { with_path = false }]

type node = {
  preconditions : texpr list;
  protocol : tprotocol;
  params : (string * string) list;
  constraints : constr list;
  fence : fence_cond;
}
[@@deriving show { with_path = false }]

let fresh_node_id =
  let n = ref 0 in
  fun () ->
    let r = !n in
    incr n;
    r

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
  | SendOnly { to_; msg = Message { args; _ } } ->
    List.concat_map used_names_expr ([to_] @ List.map snd args)
  | ReceiveOnly { from; msg = MessageD { args; _ } } ->
    List.concat_map used_names_expr ([from] @ args)
  | Exists (_, _, _) -> nyi "used names exists"
  | Send _ -> bug "used names send"
  | Comment (_, _, _) -> bug "used names comment"
  | Emp -> bug "used names emp"

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
let%trace rec group_seq :
    texpr list ->
    (string * string) list ->
    pmeta ->
    tprotocol list ->
    (G.t * node IMap.t * fence_cond) list =
 fun preconditions params meta (ts : tprotocol list) ->
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
  let label_action prs =
    match prs with
    | { p = ReceiveOnly _; pmeta } :: _
    | { p = SendOnly _; pmeta } :: _
    | { p = Assign _; pmeta } :: _ ->
      (* t *)
      (* print_endline "atomic"; *)
      let id = fresh_node_id () in
      let thread = pmeta.tid in
      (* let thread =
           match pr with
           | [] -> bug "empty protocol produced by grouping"
           | p :: _ -> p.pmeta.tid
         in *)
      let g = G.add_vertex G.empty id in
      let used_params =
        List.filter
          (fun (pa, _) ->
            List.mem ~eq:String.equal pa
              (prs |> List.concat_map used_names |> List.uniq ~eq:String.equal))
          params
      in

      let node =
        {
          constraints = [];
          params = used_params;
          preconditions;
          protocol = { p = Seq prs; pmeta = meta };
          (* temporarily, a more specific one is filled in when this appears as part of a larger structure *)
          fence = ThreadStart;
        }
      in
      let m = IMap.singleton id node in
      (g, m, Cond (thread, id) (* node.fence *))
    | [pp] -> split_actions preconditions params pp
    | _ -> bug "not a valid composite action"
  in
  loop [] [] ts |> List.map label_action

and split_actions :
    texpr list ->
    (string * string) list ->
    tprotocol ->
    G.t * node IMap.t * fence_cond =
 fun preconditions params (t : tprotocol) ->
  match t.p with
  | Forall (v, s, p) ->
    let (V (_, v1)) = must_be_var_t v in
    let (V (_, s1)) = must_be_var_t s in
    let (g, n, f) = split_actions preconditions ((v1, s1) :: params) p in
    (g, n, Forall (v1, s1, f))
  | Seq ps ->
    (* empty precondition *)
    let ps1 = group_seq [] params t.pmeta ps in

    (* only the first in a seq gets the precondition, because it may invalidate it, and we don't check for that atm *)
    let ps1 =
      List.mapi
        (fun i ((g, n, f) as p) ->
          if i = 0 then
            (g, n |> IMap.map (fun v -> { v with preconditions }), f)
          else
            p)
        ps1
    in

    (* the fence cond is what the SUCCESSOR of a node has to wait for *)
    let nodes = ps1 in

    let res =
      foldl1
        (fun (gt, mt, ft) (gc, mc, fc) ->
          let g1 = G.concat_graphs gt gc in
          ( g1,
            IMap.union
              (fun _ _ _ -> bug "failed to merge node")
              mt
              (mc
              |> IMap.mapi (fun id n ->
                     match G.in_degree gc id with
                     | 0 -> { n with fence = ft }
                     | _ -> n)),
            (* move to the next one *)
            fc ))
        nodes
    in

    let (_, bb, cc) = res in
    res
  | SendOnly _ | ReceiveOnly _ | Assign (_, _) ->
    (* this happens when an assignment is on its own, outside a seq. the simplest thing to do is treat it as a seq *)
    split_actions preconditions params { t with p = Seq [t] }
  | Par ps ->
    let nodes = List.map (split_actions preconditions params) ps in
    let (g, n, f) =
      List.fold_right
        (fun (gc, mc, fc) (gt, mt, ft) ->
          (* take disjoint union of the two graphs *)
          ( G.merge_graphs gc gt,
            IMap.union (fun _ _ _ -> bug "failed to merge node") mc mt,
            fc :: ft ))
        nodes (G.empty, IMap.empty, [])
    in
    (g, n, AllOf f)
  | Disj (a, b) ->
    (* TODO mutually exclusive constraints *)
    let (ag, am, af) = split_actions preconditions params a in
    let (bg, bm, bf) = split_actions preconditions params b in
    ( G.merge_graphs ag bg,
      IMap.union (fun _ _ _ -> bug "failed to merge node") am bm,
      AnyOf [af; bf] )
  | Imply (c, p) | BlockingImply (c, p) ->
    split_actions (c :: preconditions) params p
  | Exists (_, _, _) -> nyi "find actions exists"
  | Comment (_, _, _) -> bug "find actions comment"
  | Emp -> (G.empty, IMap.empty, ThreadStart)
  | Send _ -> bug "find actions send"

let compact = false

let maybe_nl = if compact then "" else "\n"

let maybe_indent = if compact then "" else "  "

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

let to_graphviz env pname g m =
  let strip_whitespace s =
    s
    |> Str.global_replace (Str.regexp "  +") ""
    |> String.replace ~which:`All ~sub:"\n" ~by:"\\n"
  in
  let nodes =
    IMap.bindings m
    |> List.map (fun (id, node) ->
           let { preconditions; params; constraints = _; protocol; fence } =
             node
           in
           let name = node_name pname (id, node) in
           let pre =
             match preconditions with
             | [] -> ""
             | _ ->
               Format.sprintf "{%a}\\n"
                 (List.pp (Print.pp_texpr_untyped ~env))
                 preconditions
           in
           let fence = Format.sprintf "{%s}\\n" (render_fence fence) in
           let params =
             match params with
             | [] -> ""
             | _ ->
               Format.sprintf "λ %a.\\n"
                 (List.pp
                    (Pair.pp ~sep:":" Format.pp_print_string
                       Format.pp_print_string))
                 params
           in
           Format.sprintf "%d [label=\"%s\\ntid: %a\\n%s%s%s%a\"];" id name
             Print.pp_tid protocol.pmeta.tid fence pre params
             (Print.pp_tprotocol_untyped ~env)
             protocol
           |> strip_whitespace |> ( ^ ) maybe_indent)
  in
  let edges =
    G.all_edges g
    |> List.map (fun (a, b) -> Format.sprintf "%s%d -> %d;" maybe_indent a b)
  in
  Format.sprintf "digraph G {%s%s\n%s%s}" maybe_nl
    (nodes |> String.concat maybe_nl)
    (edges |> String.concat maybe_nl)
    maybe_nl

let label_threads env party (p : tprotocol) : tprotocol =
  let fresh_thread_id =
    let n = ref 0 in
    fun () ->
      let r = !n in
      incr n;
      Format.sprintf "%st%d" party r
  in
  (* note that these names cannot have underscores or they become typed model values in TLA+ *)
  let main_thread = Format.sprintf "%smain" party in
  let rec aux tid p =
    let p = { p with pmeta = { p.pmeta with tid } } in
    let p1 =
      match p.p with
      | Par s ->
        let ts =
          s
          |> List.map (fun _ ->
                 (* inherit params *)
                 { tid with name = fresh_thread_id () })
        in
        Par (List.map2 aux ts s)
      | Forall (v, s, b) ->
        (* forall at this point (post-projection) causes concurrency *)
        let (V (_, v1)) = must_be_var_t v in
        let (V (_, s1)) = must_be_var_t s in
        (* let s_pname =
             match s.meta.info.own with
             | Party p ->
               (IMap.find (UF.value p) env.parties).repr |> var_name
             | Global ->
               party
           in *)
        let s_pname =
          match s.meta.info.typ with
          | TySet (TyParty p) ->
            (IMap.find (UF.value p) env.parties).repr |> var_name
          | _ -> fail ~loc:s.meta.loc "%s should be a party set" s1
        in
        (* let tp = fresh_thread_id ~prefix:v1 () in *)
        let tp = fresh_thread_id () in
        Forall (v, s, aux { name = tp; params = (v1, s_pname) :: tid.params } b)
      | Seq s -> Seq (List.map (aux tid) s)
      | Disj (a, b) -> Disj (aux tid a, aux tid b)
      | SendOnly _ | ReceiveOnly _ | Assign _ ->
        (* nothing to do *)
        p.p
      | Imply (c, b) -> Imply (c, aux tid b)
      | BlockingImply (c, b) -> BlockingImply (c, aux tid b)
      | Exists (v, s, b) -> Exists (v, s, aux tid b)
      | Send _ -> bug "send should be removed by this point"
      | Emp -> Emp
      | Comment (_, _, _) -> bug "comment should not appear"
    in
    { p with p = p1 }
  in
  aux { name = main_thread; params = [] } p

let split_into_actions : string -> env -> tprotocol -> G.t * node IMap.t =
 fun party env t ->
  let t = label_threads env party t in
  let (g, m, _f) = split_actions [] [] t in
  (g, m)

let collect_message_types (p : tprotocol) =
  (* TODO this only collects message types, not args, which should be checked as well *)
  let rec aux p =
    match p.p with
    | SendOnly { msg = Message { typ; _ }; _ }
    | ReceiveOnly { msg = MessageD { typ; _ }; _ }
    | Send { msg = Message { typ; _ }; _ } ->
      [typ]
    | Par es | Seq es -> List.concat_map aux es
    | Disj (a, b) -> List.concat_map aux [a; b]
    | Emp | Assign (_, _) -> []
    | Imply (_, b) | Forall (_, _, b) | Exists (_, _, b) | BlockingImply (_, b)
      ->
      aux b
    | Comment (_, _, _) -> []
  in
  aux p |> List.uniq ~eq:String.equal

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
    | Emp -> []
  in
  aux t |> List.uniq ~eq:(fun (a, _) (b, _) -> String.equal a b)

let all_tids (t : tprotocol) =
  let rec aux t =
    let thread = t.pmeta.tid in
    thread
    ::
    (match t.p with
    | SendOnly _ | ReceiveOnly _ | Assign _ -> []
    | Seq es | Par es -> List.concat_map aux es
    | Disj (a, b) -> aux a @ aux b
    | Imply (_, b) | BlockingImply (_, b) | Forall (_, _, b) -> aux b
    | Exists (_, _, _) -> nyi "all threads exists"
    | Send _ -> bug "all threads send"
    | Comment (_, _, _) -> bug "all threads comment"
    | Emp -> bug "all threads emp")
  in
  aux t |> List.uniq ~eq:equal_tid
