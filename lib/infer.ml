open Containers
open Common
open Ast

type pvar =
  | Mono of int
  | Party of var
[@@deriving show { with_path = false }]

let fresh =
  let n = ref 0 in
  fun () ->
    let r = !n in
    incr n;
    r

(* is a party vs belongs to a party *)

type party_info = {
  (* representative set *)
  repr : var;
  (* other subsets of repr *)
  other_sets : var list;
  (* elements of repr *)
  vars : var list;
  (* variables owned by this party *)
  owned_vars : var list;
}
[@@deriving show { with_path = false }]

type env = {
  parties : party_info list;
  var_info : int VMap.t;
  var_constraints : pvar IMap.t;
}
[@@deriving show { with_path = false }]

let p_env env =
  let a = env.var_info |> VMap.bindings |> [%derive.show: (var * int) list] in
  let b =
    env.var_constraints |> IMap.bindings |> [%derive.show: (int * pvar) list]
  in
  Format.sprintf "%s;%s" a b

(*   let add_equality l  r env = *)
let rec solve_subs env =
  (* let%trace rec solve_subs : pvar IMap.t -> pvar IMap.t = *)
  (* fun env -> *)
  let p_env env = env |> IMap.bindings |> [%derive.show: (int * pvar) list] in
  Format.printf "solve %s@." (p_env env);
  (* right sides that occur on the left
     1->2
     2->4
     this returns (1, 2, 4)
  *)
  let rol =
    IMap.bindings env
    |> List.filter_map (fun (k, v) ->
           match v with
           | Party _ -> None
           | Mono i -> IMap.find_opt i env |> Option.map (fun rr -> (k, i, rr)))
  in
  match rol with
  | [] -> env
  | _ ->
    List.fold_right
      (fun (l, r, rr) t ->
        match rr with
        | Party _ -> IMap.add l rr t
        | Mono j when j > r -> IMap.add l (Mono j) t
        | Mono _ -> IMap.add l (Mono r) t)
      rol env
    |> solve_subs

(* let%expect_test "solve_subs" =
  let show a = a |> [%derive.show: (int * pvar) list] |> print_endline in
  solve_subs (IMap.of_list [(1, Mono 2); (2, Mono 4); (4, Party (var "a"))])
  |> IMap.bindings |> show;
  [%expect
    {|
    solve [(1, (Mono 2)); (2, (Mono 4)); (4, (Party a))]
    solve [(1, (Mono 4)); (2, (Party a)); (4, (Party a))]
    solve [(1, (Party a)); (2, (Party a)); (4, (Party a))]
    [(1, (Party a)); (2, (Party a)); (4, (Party a))] |}] *)

(* let%trace get_party : var -> env -> pvar option = *)
(* fun var env -> *)
let get_party var env =
  let open Option.Infix in
  let* v = VMap.find_opt var env.var_info in
  IMap.find_opt v env.var_constraints

(* let%trace put_party : var -> pvar -> env -> pvar * env = *)
(* fun var p env -> *)
let put_party var p env =
  let v = fresh () in
  ( Mono v,
    {
      env with
      var_info = VMap.add var v env.var_info;
      var_constraints = IMap.add v p env.var_constraints;
    } )

let init_party var env =
  (* let%trace init_party : var -> env -> pvar * env = *)
  (* fun var env -> *)
  let v = fresh () in
  (Mono v, { env with var_info = VMap.add var v env.var_info })

let add_equality v1 v2 env =
  (* let%trace add_equality : var -> var -> env -> env = *)
  (* fun v1 v2 env -> *)
  print_endline "equality";
  let v1p = get_party v1 env in
  let (v1p, env) =
    match v1p with None -> init_party v1 env | Some p -> (p, env)
  in
  let v2p = get_party v2 env in
  let (v2p, env) =
    match v2p with None -> init_party v2 env | Some p -> (p, env)
  in
  match (v1p, v2p) with
  | (Party p1, Party p2) when equal_var p1 p2 -> env
  | (Party _, Party _) -> fail "parties different"
  | (Mono p1, Mono _) | (Mono p1, Party _) ->
    {
      env with
      var_constraints = IMap.add p1 v2p env.var_constraints |> solve_subs;
    }
  | (Party _, Mono p2) ->
    {
      env with
      var_constraints = IMap.add p2 v1p env.var_constraints |> solve_subs;
    }

let rec vars_in e =
  match e with
  | Int _ | Bool _ -> []
  | Var v -> [v]
  | App (_, s) | Set s | List s -> List.concat_map vars_in s
  | Map s -> List.concat_map vars_in (List.map snd s)
  | Tuple (a, b) -> List.concat_map vars_in [a; b]

let infer_parties env p =
  (* let%trace infer_parties : env -> protocol -> env = *)
  (* fun env p -> *)
  let find_party v =
    env.parties
    |> List.filter (fun p -> List.mem ~eq:equal_var v p.vars)
    |> List.map (fun p -> p.repr)
    |> List.hd
  in
  let rec aux p env =
    Format.printf "infer %s %a@." (p_env env) pp_protocol p;
    match p with
    | Emp -> env
    | Send { from; to_; msg = Message { args; _ } } ->
      let sender = find_party from in
      let receiver = find_party to_ in
      let sender_vars = args |> List.map snd |> List.concat_map vars_in in
      let receiver_vars = args |> List.map fst in
      env
      |> List.fold_right
           (fun c t ->
             let v = get_party c t in
             match v with
             | None ->
               let (_, env) = put_party c (Party sender) env in
               env
             | Some _ -> env)
           sender_vars
      |> List.fold_right
           (fun c t ->
             let v = get_party c t in
             match v with
             | None ->
               let (_, env) = put_party c (Party receiver) env in
               env
             | Some _ -> env)
           receiver_vars
    | Assign (v, e) ->
      let rhs = vars_in e in
      pairwise_foldr add_equality env (v :: rhs)
    | Imply (c, p) | BlockingImply (c, p) ->
      let env = pairwise_foldr add_equality env (vars_in c) in
      aux p env
    | Seq s -> List.fold_right aux s env
    | Par ps -> List.fold_right aux ps env
    | Disj (a, b) -> List.fold_right aux [a; b] env
    | Forall (_, _, p1) | Exists (_, _, p1) | Comment (_, _, p1) -> aux p1 env
    | SendOnly _ -> fail "infer_parties doesn't expect send only"
    | ReceiveOnly _ -> fail "infer_parties doesn't expect receive only"
  in

  aux p env

(* let rec qualify_expr ((V (_, pn), vars) as party) e =
  match e with
  | Int _ | Bool _ -> e
  | Var (V (None, vn)) ->
    if List.mem ~eq:String.equal vn (var_names vars) then
      Var (V (Some (Party pn), vn))
    else
      fail "variable %a does not belong to %s" pp_expr e pn
  | Var (V (Some _, _)) -> e
  | Set s -> Set (List.map (qualify_expr party) s)
  | App (n, s) -> App (n, List.map (qualify_expr party) s) *)

let is_owned_by { owned_vars; vars; _ } (V (p, v)) =
  match p with
  | Some (Party p1) when List.mem ~eq:String.equal p1 (var_names vars) ->
    (* given *)
    (* TODO what if not in owned vars? *)
    true
  | None when List.mem ~eq:String.equal v (var_names owned_vars) ->
    (* inferred *)
    true
  | _ -> false

let has_initiative (V (_, party)) p =
  let rec aux p =
    match p with
    | Emp -> false
    | Seq (s :: _) -> aux s
    | Seq _ -> false
    | Par ps -> List.exists aux ps
    | Disj (a, b) -> List.for_all aux [a; b]
    | Send { from = V (_, pn); _ } -> String.equal party pn
    | Assign (_, _) -> true
    | Imply (_, _) -> true
    | BlockingImply (_, _) -> false
    | Forall (_, _, p) -> aux p
    | Exists (_, _, p) -> aux p
    | SendOnly _ -> true
    | ReceiveOnly _ -> false
    | Comment _ -> false
  in
  aux p
