open Containers
open Common
open Ast
open Infer.Cast
(* module Tracing = Ppx_debug.Tracing *)

open Log.Make (struct
  let name = "actions"
end)

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
    Format.fprintf fmt "(%a, %a)" (List.pp Int.pp) vertices
      (List.pp ~start:"{" ~stop:"}" String.pp)
      edges

  let merge_graphs g1 g2 =
    g2
    |> fold_vertex (fun v g -> add_vertex g v) g1
    |> fold_edges_e (fun e g -> add_edge_e g e) g1

  let concat_graphs_with ~starting ~ending g1 g2 =
    merge_graphs g1 g2
    |> List.fold_right
         (fun s g -> List.fold_right (fun e g -> add_edge g e s) ending g)
         starting

  (** glues two dags together: the ending actions of g1 get edges to the starting actions of g2. use concat_graphs_with for cyclic graphs *)
  let concat_graphs g1 g2 =
    let ending = find_vertices (fun v -> out_degree g1 v = 0) g1 in
    let starting = find_vertices (fun v -> in_degree g2 v = 0) g2 in
    concat_graphs_with ~starting ~ending g1 g2
end

let default_pc_value = 0

let fresh_node_id =
  let n = ref (default_pc_value + 1) in
  fun () ->
    let r = !n in
    incr n;
    r

(* not binders, but used variables *)
let used_names (t : tprotocol) =
  let vp =
    object
      inherit [_] reduce_protocol_list
      method! visit_var _env (V (_, n)) = [n]
    end
  in
  vp#visit__protocol () t |> List.uniq ~eq:String.equal

type fence_cond =
  (* TODO tid? *)
  | ThreadStart
  | AnyOf of fence_cond list
  | AllOf of fence_cond list
  | Forall of string * party_set * fence_cond
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
  | Forall (s, v, b) ->
    Format.sprintf "∀ %s:%a. %s" s Print.pp_party_set v (render_fence b)
  | Cond (tid, pc) -> Format.sprintf "%a = %d" Print.pp_tid tid pc

type node = {
  lpre : texpr list;
  protocol : tprotocol;
  params : (string * party_set) list;
  cpre : fence_cond;
  cpost : fence_cond;
}
[@@deriving show { with_path = false }]

type state = {
  (* these three are for building the action graph *)
  start : int list;
  end_ : int list;
  graph : G.t;
  (* actions, or actions in the graph *)
  actions : node IMap.t;
  (* the postcondition of the returned node (and the precondition of its successor) *)
  post : fence_cond;
}

let split_actions_simple :
    texpr list ->
    (string * party_set) list ->
    (string * int) list ->
    tprotocol ->
    state =
 fun lpre params fn_entrypoints (tprotocol : tprotocol) ->
  let rec aux lpre params t =
    log "split simple\n%a %a" (List.pp String.pp) (List.map fst params)
      Print.pp_tprotocol_untyped t;
    match t.p with
    | Forall (v, s, body) ->
      let (V (_, v1)) = must_be_var_t v in
      (* let (V (_, s1)) = must_be_var_t s in *)
      let s1 =
        match s.expr with
        | Var (V (_, s1)) -> PSet s1
        | App ("\\", [{ expr = Var (V (_, s1)); _ }; _]) -> PSetLessSelf s1
        | _ -> failwith "cannot interpret set"
      in
      let st = aux lpre ((v1, s1) :: params) body in
      { st with post = Forall (v1, s1, st.post) }
    | Imply (cond, p) | BlockingImply (cond, p) -> aux (cond :: lpre) params p
    | Seq ps ->
      (* convert them all, then stitch them together after *)
      let states =
        (* empty precondition *)
        List.map (fun p -> aux [] params p) ps
      in

      (* only the first in a seq gets a logical precondition, because it may invalidate it, and we don't check for that atm *)
      let states =
        List.mapi
          (fun i p ->
            match i with
            | 0 ->
              { p with actions = IMap.map (fun v -> { v with lpre }) p.actions }
            | _ -> p)
          states
      in

      (* the fence cond is what the SUCCESSOR of a node has to wait for *)
      let st =
        foldl1
          (fun { start = st; end_ = et; graph = gt; actions = mt; post = ft }
               { start = sc; end_ = ec; graph = gc; actions = mc; post = fc } ->
            let g1 = G.concat_graphs_with ~ending:et ~starting:sc gt gc in
            {
              start = st;
              end_ = ec;
              graph = g1;
              actions =
                IMap.disjoint_union mt
                  (mc
                  (* change precondition to match predecessor's *)
                  |> IMap.mapi (fun id n ->
                         if List.mem ~eq:Int.equal id sc then
                           { n with cpre = ft }
                         else n));
              post = fc;
            })
          states
      in
      st
    | SendOnly _ | ReceiveOnly _ | Assign (_, _) ->
      begin
        match t with
        | { p = ReceiveOnly _; pmeta }
        | { p = SendOnly _; pmeta }
        | { p = Assign _; pmeta } ->
          let id = fresh_node_id () in
          let thread = pmeta.tid in
          let g = G.add_vertex G.empty id in
          let used_params =
            params
            |> List.filter (fun (pa, _) ->
                   List.mem ~eq:String.equal pa
                     (used_names t |> List.uniq ~eq:String.equal))
          in
          log "params for expr %d: %a | params %a | used %a" id
            Print.pp_tprotocol_untyped t (List.pp String.pp)
            (List.map fst params) (List.pp String.pp) (List.map fst used_params);

          let unq_fence = Cond (thread, id) in
          let node =
            {
              params = used_params;
              lpre;
              protocol = { t with p = t.p };
              (* temporarily, a more specific one is filled in when this appears as part of a larger structure *)
              cpre = ThreadStart;
              cpost = unq_fence;
            }
          in
          let m = IMap.singleton id node in
          {
            start = [id];
            end_ = [id];
            graph = g;
            actions = m;
            post = unq_fence;
          }
        | _ -> bug "unexpected"
      end
    | Call { f = name; _ } ->
      (* possibly cyclic graph *)
      (* create the beginning node *)
      let id = fresh_node_id () in
      let cpre = ThreadStart in
      let dest_id = List.assoc ~eq:String.equal name fn_entrypoints in
      let cpost = Cond (t.pmeta.tid, dest_id) in
      let action =
        {
          params;
          lpre;
          protocol = { p = Call { f = name; args = [] }; pmeta = t.pmeta };
          cpre;
          cpost;
        }
      in
      let m = IMap.singleton id action in

      let g = G.add_edge (G.add_vertex G.empty id) id dest_id in
      { start = [id]; end_ = [id]; graph = g; actions = m; post = cpost }
    | Par ps ->
      let actions = List.map (aux lpre params) ps in
      let st =
        foldl1
          (fun { start = sc; end_ = ec; graph = gc; actions = mc; post = fc }
               { start = st; end_ = et; graph = gt; actions = mt; post = ft } ->
            (* take disjoint union of the two graphs *)
            {
              start = sc @ st;
              end_ = ec @ et;
              graph = G.merge_graphs gc gt;
              actions = IMap.disjoint_union mc mt;
              post = AllOf [fc; ft];
            })
          actions
      in
      st
    | Disj (a, b) ->
      (* TODO mutually exclusive constraints *)
      let { start = as_; end_ = ae; graph = ag; actions = am; post = af } =
        aux lpre params a
      in
      let { start = bs; end_ = be; graph = bg; actions = bm; post = bf } =
        aux lpre params b
      in
      {
        start = as_ @ bs;
        end_ = ae @ be;
        graph = G.merge_graphs ag bg;
        actions = IMap.disjoint_union am bm;
        post = AnyOf [af; bf];
      }
    | Exists (_, _, _) -> nyi "find actions exists"
    | Comment (_, _, _) -> bug "find actions comment"
    | Emp ->
      {
        start = [];
        end_ = [];
        graph = G.empty;
        actions = IMap.empty;
        post = ThreadStart;
      }
    | Send _ -> bug "find actions send"
  in
  aux lpre params tprotocol

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
    | Call _ -> "Call"
    | Emp -> "Dummy"
    | _ -> "Action"
  in
  Format.sprintf "%s%s%d" party prefix id

let to_graphviz pname g m =
  let strip_whitespace s =
    s
    |> Str.global_replace (Str.regexp "  +") ""
    |> String.replace ~which:`All ~sub:"\n" ~by:"\\n"
  in
  let actions =
    IMap.bindings m
    |> List.map (fun (id, node) ->
           let { lpre; params; protocol; cpre; cpost } = node in
           let name = node_name pname (id, node) in
           let lpre =
             match lpre with
             | [] -> ""
             | _ ->
               Format.sprintf "{%a}\\n" (List.pp Print.pp_texpr_untyped) lpre
           in
           let cpre = Format.sprintf "{%s}\\n" (render_fence cpre) in
           let cpost = Format.sprintf "{%s}\\n" (render_fence cpost) in
           let params =
             match params with
             | [] -> ""
             | _ ->
               Format.sprintf "params: %a\\n"
                 (List.pp
                    (Pair.pp ~sep:":" Format.pp_print_string pp_party_set))
                 params
           in
           let succinct = true in
           let module Protocol = struct
             let to_string = Format.asprintf "%a" Print.pp_tprotocol_untyped
           end in
           begin
             (if succinct then
              [%string
                {|%{id#Int} [label="%{name}\n%{cpre}%{protocol#Protocol}\n%{cpost}"];|}]
             else
               let module Tid = struct
                 let to_string = Format.asprintf "%a" Print.pp_tid
               end in
               [%string
                 {|%{id#Int} [label="%{name}\ntid: %{protocol.pmeta.tid#Tid}\n%{cpre}%{cpost}%{lpre}%{params}%{protocol#Protocol}"];|}])
             |> String.replace ~sub:"->" ~by:"→"
             |> strip_whitespace |> ( ^ ) maybe_indent
           end)
  in
  let edges =
    G.all_edges g
    |> List.map (fun (a, b) -> Format.sprintf "%s%d -> %d;" maybe_indent a b)
  in
  let edges = edges |> String.concat maybe_nl in
  let actions = actions |> String.concat maybe_nl in
  Format.sprintf "digraph G {%s%s%s%s%s}"
    (if String.is_empty actions then "" else maybe_nl)
    actions
    (if String.is_empty edges then "" else maybe_nl)
    edges maybe_nl

(* thread ids are shared across all parties and functions *)
let fresh_thread_id =
  let n = ref 0 in
  fun party ->
    let r = !n in
    incr n;
    Format.sprintf "%st%d" party r

let label_threads env party (p : tprotocol) : tprotocol =
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
                 { tid with name = fresh_thread_id party })
        in
        Par (List.map2 aux ts s)
      | Forall (v, s, b) ->
        (* forall at this point (cpost-projection) causes concurrency *)
        let (V (_, v1)) = must_be_var_t v in
        (* let (V (_, s1)) = must_be_var_t s in *)
        (* let s_pname =
             match s.meta.info.own with
             | Party p ->
               (IMap.find (UF.value p) env.parties).repr |> var_name
             | Global ->
               party
           in *)
        let s_pname =
          match Infer.concretize env s.meta.info.typ with
          | TyMap (TyParty p, TyBool) ->
            (IMap.find (UF.value p) env.parties).repr |> var_name
          | _ ->
            fail ~loc:s.meta.loc "%a should be a party set instead of a %a"
              Print.pp_texpr_untyped s (* (Print.pp_typ ~env) *)
              pp_typ s.meta.info.typ
        in
        (* let tp = fresh_thread_id ~prefix:v1 () in *)
        let tp = fresh_thread_id party in
        Forall
          (v, s, aux { name = tp; params = (v1, PSet s_pname) :: tid.params } b)
      | Seq s -> Seq (List.map (aux tid) s)
      | Disj (a, b) -> Disj (aux tid a, aux tid b)
      | SendOnly _ | ReceiveOnly _ | Assign _ | Call _ ->
        (* nothing to do *)
        p.p
      | Imply (c, b) -> Imply (c, aux tid b)
      | BlockingImply (c, b) -> BlockingImply (c, aux tid b)
      | Exists (v, s, b) -> Exists (v, s, aux tid b)
      | Send _ ->
        bug "send should be removed by this point %a" Print.pp_tprotocol_untyped
          p
      | Emp -> Emp
      | Comment (_, _, _) -> bug "comment should not appear"
    in
    { p with p = p1 }
  in
  aux { name = main_thread; params = [] } p

let is_directed_edge n1 n2 g =
  (* TODO check post1 = pre2? *)
  if
    let s = G.succ g n1 in
    List.mem ~eq:Int.equal n2 s && List.length s = 1
  then Some (n1, n2)
  else if
    let s = G.succ g n2 in
    List.mem ~eq:Int.equal n1 s && List.length s = 1
  then Some (n2, n1)
  else None

let last xs = xs |> List.last 1 |> List.hd

(** this ends up being quadratic, can be fixed by maintaining an incremental representation which is updated when something is added *)
let rec should_merge_protocols grain (t1 : tprotocol) (t2 : tprotocol) =
  log "merge %a (%a) (%a)" pp_grain grain Print.pp_tprotocol_untyped t1
    Print.pp_tprotocol_untyped t2;
  let res =
    match (t1.p, t2.p, grain) with
    | _, (Emp | Call _), _ -> true
    | (Emp | Call _), _, _ -> true
    | Seq s1, Seq s2, _ -> should_merge_protocols grain (last s1) (List.hd s2)
    | Seq s1, _, _ -> should_merge_protocols grain (last s1) t2
    | _, Seq s2, _ -> should_merge_protocols grain t1 (List.hd s2)
    | Assign _, Assign _, (Standard | Communication) -> true
    | Assign _, (SendOnly _ | ReceiveOnly _), Communication -> true
    | _, _, _ -> false
  in
  log "merge %b" res;
  res

let merge_protocols (t1 : tprotocol) (t2 : tprotocol) : tprotocol =
  log "merge_protocols: (%a) (%a)" Print.pp_tprotocol_untyped t1
    Print.pp_tprotocol_untyped t2;
  let res =
    match (t1.p, t2.p) with
    | Seq s1, Seq s2 -> { t1 with p = Seq (s1 @ s2) }
    | _, (Emp | Call _) -> t1
    | (Emp | Call _), _ -> t2
    | Seq s1, _ -> { t1 with p = Seq (s1 @ [t2]) }
    | _, Seq s2 -> { t1 with p = Seq (t1 :: s2) }
    | _, _ -> { t1 with p = Seq [t1; t2] }
  in
  log "res (%a)" Print.pp_tprotocol_untyped res;
  res

let fuse n1 n2 graph actions =
  (* we could do nothing in these cases, but these are checked upstream *)
  assert (n1 <> n2);
  assert (G.mem_vertex graph n1 && G.mem_vertex graph n2);
  assert (IMap.mem n1 actions && IMap.mem n2 actions);
  match is_directed_edge n1 n2 graph with
  | None -> assert false
  | Some (n1, n2) ->
    (* n1 -> n2 *)
    let a2 = IMap.find n2 actions in
    let actions =
      actions |> IMap.remove n2
      |> IMap.update n1 (function
           | None -> bug "bug"
           | Some a1 ->
             (* update protocols and postcondition *)
             Some
               {
                 a1 with
                 params = a1.params @ a2.params;
                 cpost = a2.cpost;
                 protocol = merge_protocols a1.protocol a2.protocol;
               })
    in
    (* update graph *)
    let graph =
      (* n1 -> n2 -> n3 ==> n1 -> n3 *)
      let graph =
        let succ = G.succ graph n2 in
        List.fold_right
          (fun c t ->
            (* edge case: single-node cycles *)
            if n2 = c then G.add_edge t n1 n1
            else G.remove_edge (G.add_edge t n1 c) n2 c)
          succ graph
      in
      (* n3 -> n2 ==> n3 -> n1 *)
      let graph =
        let pred = G.pred graph n2 |> List.filter (( <> ) n1) in
        List.fold_right
          (fun c t -> G.remove_edge (G.add_edge t c n1) n2 c)
          pred graph
      in
      (* remove the node itself *)
      G.remove_vertex graph n2
    in
    (graph, actions)

(** More declarative version which iterates to a fixed point.

    Graph rewriting approach: find all candidate edges.
    For each one, if we transform it, invalidate subsequent involved edges.
    Repeat this until there are no more candidate edges, or no edges are transformed.
    The number of times an edge can appear as a candidate is bounded by the number of edges, so O(E^2). *)
let fuse_edges grain graph actions =
  log "grain: %a" pp_grain grain;
  let candidate_edges g =
    (* to begin with, there's no good way to fuse things like a and b given a->b, a->c, as we would have to enter/exit the merged action halfway. we use the conservative condition that a and b must have exactly one succ/pred (which are b and a respectively). this has the side effect of preventing some unsoundness when merging cycles, e.g. a->b, b->b; we would have to merge the preconditions of a and b in the final node, something we sidestep. *)
    g |> G.all_edges
    |> List.filter (fun (a, b) ->
           List.length (G.succ g a) = 1 && List.length (G.pred g b) = 1)
  in
  let rec loop changed work (g, a) =
    log "iteration %d %b" (List.length work) changed;
    match work with
    | [] ->
      begin
        match (changed, candidate_edges g) with
        | false, _ | _, [] ->
          log "end";
          (g, a)
        | _, w ->
          log "restarting";
          loop false w (g, a)
      end
    | (f, t) :: rest ->
      if
        should_merge_protocols grain (IMap.find f a).protocol
          (IMap.find t a).protocol
      then begin
        log "fusing %d %d" f t;
        let g, a = fuse f t g a in
        let rest =
          rest
          |> List.filter (fun (a, b) -> a <> f && a <> t && b <> f && b <> t)
        in
        loop true rest (g, a)
      end
      else begin
        log "skipping %d %d" f t;
        loop changed rest (g, a)
      end
  in
  loop false (candidate_edges graph) (graph, actions)

let remove_vertices vs graph actions =
  ( List.fold_right (Fun.flip G.remove_vertex) vs graph,
    List.fold_right IMap.remove vs actions )

let misc_pruning graph actions =
  (* find and remove no-op self loops, which occur when a subprotocol is projected but does nothing on a particular party *)
  let no_op_self_loops =
    actions |> IMap.bindings
    |> List.filter_map (fun (k, v) ->
           match v.protocol.p with
           | Emp when List.equal Int.equal [k] (G.succ graph k) -> Some k
           | _ -> None)
  in
  log "self loops removed %a" (List.pp Int.pp) no_op_self_loops;
  let graph, actions = remove_vertices no_op_self_loops graph actions in
  (* remove call nodes which aren't linked to anything, as a result of the previous transformation *)
  let useless_calls =
    actions |> IMap.bindings
    |> List.filter_map (fun (k, v) ->
           match v.protocol.p with
           | Call _ when List.is_empty (G.succ graph k) -> Some k
           | _ -> None)
  in
  log "useless calls removed %a" (List.pp Int.pp) useless_calls;
  let graph, actions = remove_vertices useless_calls graph actions in
  (graph, actions)

let split_into_actions :
    grain -> string -> env -> tprotocol -> G.t * node IMap.t =
 fun grain party env t ->
  let t = label_threads env party t in
  let env =
    {
      env with
      subprotocols =
        env.subprotocols
        |> SMap.map (fun sp ->
               { sp with tp = sp.tp |> label_threads env party });
    }
  in
  (* define every function's entry point *)
  let fns = env.subprotocols |> SMap.bindings in
  (* let initial_graph, fn_entrypoints = *)
  let fn_entrypoints =
    List.fold_right
      (fun (name, _sp) t ->
        let id = fresh_node_id () in
        (* let g = G.add_vertex g id in *)
        (name, id) :: t)
      (* (g, (name, id) :: t)) *)
      (* fns (G.empty, []) *)
      fns []
  in

  (* analyze functions first *)
  let fns =
    env.subprotocols |> SMap.bindings
    |> List.map (fun (name, sp) ->
           let st = split_actions_simple [] [] fn_entrypoints sp.tp in
           (* create the starting actions and link to the beginning of the function *)
           let st =
             let entry = List.assoc ~eq:String.equal name fn_entrypoints in
             (* let fn_start =
                  match st.start with
                  | [s] -> s
                  | _ ->
                    bug "invalid function start %d %a %a" (List.length st.start)
                      Print.pp_tprotocol_untyped
                      (IMap.find (st.start |> List.hd) st.actions).protocol
                      Print.pp_tprotocol_untyped
                      (IMap.find (st.start |> List.tl |> List.hd) st.actions)
                        .protocol
                in *)
             (* see if anything bad happens when we have multiple starts, say due to par *)
             let entry_cond = Cond (sp.tp.pmeta.tid, entry) in
             let actions =
               st.actions
               |> IMap.add entry
                    {
                      lpre = [];
                      params = [];
                      protocol = { pmeta = sp.tp.pmeta; p = Emp };
                      cpre = entry_cond;
                      (* cpost = Cond (sp.tp.pmeta.tid, fn_start); *)
                      cpost = entry_cond;
                    }
             in
             let actions, graph =
               List.fold_right
                 (fun st (a, g) ->
                   ( IMap.update st
                       (function
                         | None -> bug "invalid"
                         | Some act -> Some { act with cpre = entry_cond })
                       a,
                     G.add_edge g entry st ))
                 st.start (actions, st.graph)
             in
             { st with actions; graph }
           in
           (name, st))
  in

  (* analyze main + starting precondition *)
  let st = split_actions_simple [] [] fn_entrypoints t in
  let st =
    let actions = st.actions in
    { st with actions }
  in

  (* combine everything into a single graph *)
  let graph =
    let g = List.map (fun s -> s.graph) (st :: List.map snd fns) in
    List.fold_right (fun c t -> G.merge_graphs c t) g G.empty
  in
  let actions =
    let n = List.map (fun s -> s.actions) (st :: List.map snd fns) in
    List.fold_right (fun c t -> IMap.disjoint_union c t) n IMap.empty
  in
  let graph, actions = fuse_edges grain graph actions in
  let graph, actions = misc_pruning graph actions in
  (graph, actions)

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
    | Emp | Assign _ | Call _ ->
      (* call is empty because we don't use this to traverse the spec, that should be done higher up *)
      []
    | Imply (_, b) | Forall (_, _, b) | Exists (_, _, b) | BlockingImply (_, b)
      ->
      aux b
    | Comment (_, _, _) -> []
  in
  aux p |> List.uniq ~eq:String.equal

let assigned_variables (e : tprotocol) =
  let vp =
    object
      inherit [_] reduce_protocol_list

      method! visit_Assign () v _e =
        let info = v.meta.info in
        let (V (_, v)) = must_be_var_t v in
        [(v, info)]
    end
  in
  vp#visit__protocol () e
  |> List.uniq ~eq:(fun (a, _) (b, _) -> String.equal a b)

let abstract_state_variables (e : tprotocol) =
  let vp =
    object
      inherit [_] reduce_protocol_list

      method! visit_Assign () v _e =
        let info = v.meta.info in
        let (V (_, v)) = must_be_var_t v in
        [(v, info)]

      method! visit_msg_destruct _vv () (MessageD { args; _ }) =
        List.map
          (fun a ->
            let (V (_, v)) = must_be_var_t a in
            (v, a.meta.info))
          args
    end
  in
  vp#visit__protocol () e
  |> List.uniq ~eq:(fun (a, _) (b, _) -> String.equal a b)

let all_tids (e : tprotocol) =
  let vp =
    object
      inherit [_] reduce_protocol_list
      method! visit__protocol _env p = [p.pmeta.tid]
    end
  in
  vp#visit__protocol () e |> List.uniq ~eq:equal_tid
