open Containers
open Common
open Ast
open Infer.Cast
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

  (** glues two dags together: the ending nodes of g1 get edges to the starting nodes of g2. use concat_graphs_with for cyclic graphs *)
  let concat_graphs g1 g2 =
    let ending = find_vertices (fun v -> out_degree g1 v = 0) g1 in
    let starting = find_vertices (fun v -> in_degree g2 v = 0) g2 in
    concat_graphs_with ~starting ~ending g1 g2
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

(** the condition that the successor of this would have to wait for *)
let compute_fence tid id (t : tprotocol) =
  let rec aux t =
    match t.p with
    | Forall (v, s, b) ->
      let (V (_, v)) = must_be_var_t v in
      let (V (_, s)) = must_be_var_t s in
      Forall (v, s, aux b)
    | Par ps -> AllOf (List.map aux ps)
    | Disj (a, b) -> AnyOf [aux a; aux b]
    | Call _ ->
      (* there's no successor for now, as calls transfer control entirely *)
      AnyOf []
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
  my_fence : fence_cond;
}
[@@deriving show { with_path = false }]

let default_pc_value = 0

let fresh_node_id =
  let n = ref (default_pc_value + 1) in
  fun () ->
    let r = !n in
    incr n;
    r

let rec used_names_expr (t : texpr) =
  match t.expr with
  | Int _ | Bool _ | String _ -> []
  | Map kvs -> List.concat_map (fun (_, v) -> used_names_expr v) kvs
  | Set args | List args | App (_, args) -> List.concat_map used_names_expr args
  | Var (V (_, v)) -> [v]
  | Tuple (_, _) -> nyi "tuple used names"
  | Else | Timeout -> nyi "else/timeout"

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
  | Call (_, args) ->
    (* not higher-order *)
    List.concat_map used_names_expr args
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
    env ->
    texpr list ->
    (string * string) list ->
    pmeta ->
    (string * (int list * int list * G.t * node IMap.t * fence_cond)) list ->
    tprotocol list ->
    (int list * int list * G.t * node IMap.t * fence_cond) list =
 fun env preconditions params meta proc_actions (ts : tprotocol list) ->
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
      let id = fresh_node_id () in
      let thread = pmeta.tid in
      let g = G.add_vertex G.empty id in
      let used_params =
        params
        |> List.filter (fun (pa, _) ->
               List.mem ~eq:String.equal pa
                 (prs |> List.concat_map used_names
                |> List.uniq ~eq:String.equal))
      in

      let unq_fence = Cond (thread, id) in
      let my_fence =
        (* List.fold_right (fun (v, s) t -> Forall (v, s, t)) params *)
        unq_fence
      in
      let node =
        {
          constraints = [];
          params = used_params;
          preconditions;
          protocol = { p = Seq prs; pmeta = meta };
          (* temporarily, a more specific one is filled in when this appears as part of a larger structure *)
          fence = ThreadStart;
          my_fence;
        }
      in
      let m = IMap.singleton id node in
      ([id], [id], g, m, unq_fence)
    | [pp] -> split_actions env preconditions params proc_actions pp
    | _ -> bug "not a valid composite action"
  in
  loop [] [] ts |> List.map label_action

and split_actions :
    env ->
    texpr list ->
    (string * string) list ->
    (string * (int list * int list * G.t * node IMap.t * fence_cond)) list ->
    tprotocol ->
    int list * int list * G.t * node IMap.t * fence_cond =
 fun env preconditions params proc_actions (t : tprotocol) ->
  match t.p with
  | Forall (v, s, p) ->
    let (V (_, v1)) = must_be_var_t v in
    let (V (_, s1)) = must_be_var_t s in
    let (starting, ending, g, n, f) =
      split_actions env preconditions ((v1, s1) :: params) proc_actions p
    in
    (starting, ending, g, n, Forall (v1, s1, f))
  | Seq ps ->
    (* empty precondition *)
    let ps1 = group_seq env [] params t.pmeta proc_actions ps in

    (* only the first in a seq gets the precondition, because it may invalidate it, and we don't check for that atm *)
    let ps1 =
      List.mapi
        (fun i ((s, e, g, n, f) as p) ->
          if i = 0 then
            (s, e, g, n |> IMap.map (fun v -> { v with preconditions }), f)
          else
            p)
        ps1
    in

    (* the fence cond is what the SUCCESSOR of a node has to wait for *)
    let nodes = ps1 in

    let (s, e, g, m, f) =
      foldl1
        (fun (st, et, gt, mt, ft) (sc, ec, gc, mc, fc) ->
          let g1 = G.concat_graphs_with ~ending:et ~starting:sc gt gc in
          (* Format.eprintf
             "folding seq: fence between nodes %s (%s to %s) and %s (%s to %s): \
              %a and %a@."
             ([%derive.show: int list] (G.find_vertices (fun _ -> true) gt))
             ([%derive.show: int list] st)
             ([%derive.show: int list] et)
             ([%derive.show: int list] (G.find_vertices (fun _ -> true) gc))
             ([%derive.show: int list] sc)
             ([%derive.show: int list] ec)
             pp_fence_cond ft pp_fence_cond fc; *)
          ( st,
            ec,
            g1,
            IMap.union
              (fun _ _ _ -> bug "failed to merge node")
              mt
              (mc
              (* |> IMap.mapi (fun id n ->
                     match G.in_degree gc id with
                     | 0 -> { n with fence = ft }
                     | _ -> n
                     ) *)
              |> IMap.mapi (fun id n ->
                     if List.mem ~eq:Int.equal id sc then
                       { n with fence = ft }
                     else
                       n)),
            (* move to the next one *)
            fc ))
        nodes
    in
    (s, e, g, m, f)
  | SendOnly _ | ReceiveOnly _ | Assign (_, _) ->
    (* this happens when an assignment is on its own, outside a seq. the simplest thing to do is treat it as a seq *)
    split_actions env preconditions params proc_actions { t with p = Seq [t] }
  | Par ps ->
    let nodes =
      List.map (split_actions env preconditions params proc_actions) ps
    in
    let (s, e, g, n, f) =
      List.fold_right
        (fun (sc, ec, gc, mc, fc) (st, et, gt, mt, ft) ->
          (* take disjoint union of the two graphs *)
          ( sc @ st,
            ec @ et,
            G.merge_graphs gc gt,
            IMap.union (fun _ _ _ -> bug "failed to merge node") mc mt,
            fc :: ft ))
        nodes
        ([], [], G.empty, IMap.empty, [])
    in
    (s, e, g, n, AllOf f)
  | Disj (a, b) ->
    (* TODO mutually exclusive constraints *)
    let (as_, ae, ag, am, af) =
      split_actions env preconditions params proc_actions a
    in
    let (bs, be, bg, bm, bf) =
      split_actions env preconditions params proc_actions b
    in
    ( as_ @ bs,
      ae @ be,
      G.merge_graphs ag bg,
      IMap.union (fun _ _ _ -> bug "failed to merge node") am bm,
      AnyOf [af; bf] )
  | Imply (c, p) | BlockingImply (c, p) ->
    split_actions env (c :: preconditions) params proc_actions p
  | Call (name, _) ->
    (* possibly cyclic graph *)
    (match List.assoc_opt ~eq:String.equal name proc_actions with
    | None ->
      let body = SMap.find name env.subprotocols in
      (* create the beginning node *)
      let id = fresh_node_id () in
      let my_fence =
        (* List.fold_right
           (fun (v, s) t -> Forall (v, s, t))
           params *)
        Cond (t.pmeta.tid, id)
      in
      (* Format.eprintf "%a %s@."
         (List.pp (Print.pp_tprotocol_untyped ~env))
         prs
         ([%derive.show: (string * string) list] used_params); *)
      let node =
        {
          constraints = [];
          params;
          preconditions;
          protocol =
            {
              p = Emp;
              pmeta =
                pmeta ~tid:t.pmeta.tid ~loc:t.pmeta.ploc ~env:t.pmeta.penv ();
            };
          fence = (* don't know this at this point *)
                  AllOf [];
          my_fence;
        }
      in
      let m = IMap.singleton id node in
      let g = G.add_vertex G.empty id in
      let s = [id] in
      let e = [id] in

      (* the fence for that node is the current call site's *)
      let (s1, e1, g1, m1, f) =
        split_actions env preconditions params
          ((name, (s, e, g, m, my_fence)) :: proc_actions)
          body.tp
      in
      (* Format.eprintf "emerged from fn body %a@." pp_fence_cond f; *)
      (* if there's recursion in the body, it's possible the fence here will be of the form AnyOf[id; ...].
         this is harmless so we don't filter it out *)
      (* problems:
         - immediate successors of function nodes don't have its preconditions
         - function nodes don't have preconditions of recursive calls
      *)
      ( [id],
        e1,
        G.concat_graphs_with ~starting:s1 ~ending:[id] g g1,
        (* it's possible the same node reappears due to recursion *)
        IMap.union
          (fun _ a _ ->
            (* Format.eprintf "node a %a@." pp_node a; *)
            (* Format.eprintf "node b %a@." pp_node a; *)
            (* Some { a with fence = AnyOf [a.fence; b.fence] } *)
            Some a)
          m m1
        (* |> IMap.mapi (fun id n ->
               if List.mem ~eq:Int.equal id s1 then
                 { n with fence = my_fence }
               else
                 n) *),
        f )
    | Some (s, e, g, m, f) ->
      (* recursive call. add our fence to theirs *)
      (* Format.eprintf "recursive call %s %s@."
         ([%derive.show: int list] s)
         ([%derive.show: int list] e); *)
      (s, e, g, m, f)
      (* () *))
  | Exists (_, _, _) -> nyi "find actions exists"
  | Comment (_, _, _) -> bug "find actions comment"
  | Emp -> ([], [], G.empty, IMap.empty, ThreadStart)
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
           let {
             preconditions;
             params;
             constraints = _;
             protocol;
             fence;
             my_fence;
           } =
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
           let my_fence =
             Format.sprintf "this: {%s}\\n" (render_fence my_fence)
           in
           let params =
             match params with
             | [] -> ""
             | _ ->
               Format.sprintf "params: %a\\n"
                 (List.pp
                    (Pair.pp ~sep:":" Format.pp_print_string
                       Format.pp_print_string))
                 params
           in
           Format.sprintf "%d [label=\"%s\\ntid: %a\\n%s%s%s%s%a\"];" id name
             Print.pp_tid protocol.pmeta.tid fence my_fence pre params
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
      | SendOnly _ | ReceiveOnly _ | Assign _ | Call _ ->
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

let postprocess_graph g m =
  let fn_nodes =
    IMap.bindings m
    |> List.filter (fun (_, n) ->
           match n.protocol.p with Emp -> true | _ -> false)
  in
  (* let fn_node_preconditions =
       fn_nodes
       |> List.map (fun (id, _) ->
              ( id,
                AnyOf
                  (G.pred g id |> List.map (fun n1 -> (IMap.find n1 m).my_fence))
              ))
     in *)
  (* Format.eprintf "fn nodes %s@."
     ([%derive.show: int list] (fn_nodes |> List.map fst)); *)
  let fn_node_successor_preconditions =
    fn_nodes
    |> List.concat_map (fun (id, n) ->
           G.succ g id |> List.map (fun suc -> (suc, n.my_fence)))
  in
  (* Format.eprintf "pred %s@."
       ([%derive.show: (int * fence_cond) list] fn_node_preconditions);
     Format.eprintf "succ %s@."
       ([%derive.show: (int * fence_cond) list] fn_node_successor_preconditions); *)
  (* let m =
       List.fold_right
         (fun (id, f) m1 -> IMap.add id { (IMap.find id m1) with fence = f } m1)
         fn_node_preconditions m
     in *)
  let m =
    List.fold_right
      (fun (id, f) m1 -> IMap.add id { (IMap.find id m1) with fence = f } m1)
      fn_node_successor_preconditions m
  in
  (g, m)

let split_into_actions : string -> env -> tprotocol -> G.t * node IMap.t =
 fun party env t ->
  let t = label_threads env party t in
  (* TODO this doesn't work properly because the spec needs to be done all at once *)
  let env =
    {
      env with
      subprotocols =
        env.subprotocols
        |> SMap.map (fun sp ->
               { sp with tp = sp.tp |> label_threads env party });
    }
  in
  let (_s, _e, g, m, _f) = split_actions env [] [] [] t in
  (* this is necessary because cyclic structures can't be dealt with using recursion *)
  let (g, m) = postprocess_graph g m in
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
    | Emp | Assign _ | Call _ ->
      (* call is empty because we don't use this to traverse the spec, that should be done higher up *)
      []
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
    | Call _ -> []
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
    | SendOnly _ | ReceiveOnly _ | Assign _ | Call _ -> []
    | Seq es | Par es -> List.concat_map aux es
    | Disj (a, b) -> aux a @ aux b
    | Imply (_, b) | BlockingImply (_, b) | Forall (_, _, b) -> aux b
    | Exists (_, _, _) -> nyi "all threads exists"
    | Send _ -> bug "all threads send"
    | Comment (_, _, _) -> bug "all threads comment"
    | Emp -> bug "all threads emp")
  in
  aux t |> List.uniq ~eq:equal_tid
