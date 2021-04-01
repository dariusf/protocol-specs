open Containers
module Tracing = Ppx_debug.Tracing
open Ast

let rec pp_protocol fmt p =
  let open Format in
  match p with
  | Emp -> fprintf fmt "emp"
  | Seq ps ->
    List.pp
      ~pp_start:(fun fmt () -> fprintf fmt "(@[<v 0>")
      ~pp_stop:(fun fmt () -> fprintf fmt "@])")
      ~pp_sep:(fun fmt () -> fprintf fmt ";@,")
      pp_protocol fmt ps
  | Par ps ->
    List.pp
      ~pp_start:(fun fmt () -> fprintf fmt "")
      ~pp_stop:(fun fmt () -> fprintf fmt "")
      ~pp_sep:(fun fmt () -> fprintf fmt "@ *@ ")
      (fun fmt ps -> fprintf fmt "(%a)" pp_protocol ps)
      fmt ps
  | Send { from; to_; msg } ->
    fprintf fmt "%a->%a: %a" pp_var from pp_var to_ pp_msg msg
  | SendOnly { from; to_; msg } ->
    fprintf fmt "*%a->%a: %a" pp_var from pp_var to_ pp_msg_construct msg
  | ReceiveOnly { from; to_; msg } ->
    fprintf fmt "%a->%a*: %a" pp_var from pp_var to_ pp_msg_destruct msg
  | Assign (v, e) -> fprintf fmt "%a = %a" pp_var v pp_expr e
  | Disj (a, b) ->
    fprintf fmt "@[<v 0>%a@,\\/@,%a@]" pp_protocol a pp_protocol b
  | Imply (e, p) ->
    fprintf fmt "@[<v 0>%a =>@;<0 2>@[@,%a@]@]" pp_expr e pp_protocol p
  | BlockingImply (e, p) ->
    fprintf fmt "@[<v 0>%a =>*@;<0 2>@[@,%a@]@]" pp_expr e pp_protocol p
  | Forall (v, s, p) ->
    (* fprintf fmt "@[<v 0>forall %a:%a.@;<0 2>@[%a@]@]" pp_var v pp_var s pp_protocol p *)
    Boxes.block fmt
      ~enter:(fun m -> m "forall %a:%a." pp_var v pp_var s)
      ~content:(fun m -> m "%a" pp_protocol p)
  | Exists (v, s, p) ->
    fprintf fmt "@[<v 0>exists %a:%a.@;<0 2>@[%a@]@]" pp_var v pp_var s
      pp_protocol p
  | Comment (_, s, p) -> fprintf fmt "@[<v 0>// %s@,%a@]" s pp_protocol p

(** https://hackage.haskell.org/package/base-4.14.1.0/docs/src/Data.Foldable.html#foldr1 *)
let foldr1 f xs =
  List.fold_right
    (fun c t -> match t with None -> Some c | Some d -> Some (f c d))
    xs None
  |> Option.get_exn

let render_protocol p =
  let open PPrint in
  let indent d = blank 2 ^^ nest 2 d in
  let (arrow, disj, par, if_, when_, in_, forall, exists) =
    ( string "->",
      string "\\/",
      string "||",
      string "=>",
      string "=>*",
      string "in",
      string "forall",
      string "exists" )
  in
  let spaced d = terminate space d in
  let nl = break 1 in
  let render_var (V (p, v)) =
    match p with
    | None -> string v
    | Some (Party p) -> concat [string p; dot; string v]
  in
  let is_alpha = function 'a' .. 'z' | 'A' .. 'Z' -> true | _ -> false in
  (* this should be kept in sync with the parser *)
  let get_expr_prec op =
    match op with
    | "==" -> 5
    | "<" | "<=" | ">" | ">=" -> 6
    | "+" | "-" -> 7
    | "/" | "*" -> 8
    | "&" | "|" -> 9
    | "!" -> 10
    | _ -> 0
  in
  let get_expr_assoc _ = `Left in
  (* prec is the precedence of the context, so we make sure to
     parenthesize when passing an expression with lower precedence into one with higher precedence. see https://stackoverflow.com/a/43639618. starting with 0 means we
     never parenthesize at the top level. *)
  let rec render_expr ?(prec = 0) e =
    match e with
    | Int i -> string (string_of_int i)
    | Bool b -> string (string_of_bool b)
    | Set es -> braces (List.map render_expr es |> separate (spaced comma))
    | List es -> brackets (List.map render_expr es |> separate (spaced comma))
    | Map es ->
      braces
        (List.map
           (fun (k, v) -> concat [string k; spaced colon; render_expr v])
           es
        |> separate (spaced comma))
    | App (f, args) ->
      if List.length args = 2 && not (is_alpha f.[0]) then
        let n = get_expr_prec f in
        let[@warning "-8"] [left; right] = args in
        let (leftp, rightp) =
          match get_expr_assoc f with
          | `Left -> (n, n + 1)
          | `Right -> (n + 1, n)
        in
        let parens =
          if prec > n then
            parens
          else
            Fun.id
        in
        parens
          (separate
             (enclose space space (string f))
             [render_expr ~prec:leftp left; render_expr ~prec:rightp right])
      else
        precede (string f)
          (parens (List.map render_expr args |> separate (spaced comma)))
    | Var v -> render_var v
    | Tuple (_, _) -> failwith "tuples?"
  in
  let rec render_protocol p =
    match p with
    | Emp -> failwith "emp?"
    | Seq ps ->
      let l = List.length ps in

      (* instead of the whole precedence setup we have for
         expressions, we special-case the printing in here,
         as number of precedence levels is fixed and small.
         this also handles positioning semicolons at the
         end of blocks. *)
      ps
      |> List.mapi (fun i c ->
             if i = l - 1 then
               (c, `None)
             else
               match c with Par _ | Disj _ -> (c, `Indent) | _ -> (c, `Trail))
      |> List.map (fun (c, ind) ->
             let c = render_protocol c in
             match ind with
             | `None -> c
             | `Trail -> c ^^ semi ^^ nl
             | `Indent -> indent c ^^ nl ^^ semi ^^ nl)
      |> concat
    | Par ps ->
      separate
        (nl ^^ par ^^ nl)
        (ps |> List.map render_protocol |> List.map indent)
    | Disj (a, b) ->
      separate
        (nl ^^ disj ^^ nl)
        ([a; b] |> List.map render_protocol |> List.map indent)
    | Send { from; to_; msg = Message { typ; args } } ->
      concat
        [
          render_var from; arrow; render_var to_; colon; space; string typ;
          (match args with
          | [] -> empty
          | _ ->
            parens
              (separate (spaced comma)
                 (List.map
                    (fun (v, e) -> concat [render_var v; equals; render_expr e])
                    args)));
        ]
    | Assign (v, e) -> separate space [render_var v; equals; render_expr e]
    | Imply (b, p) ->
      nest 2 (concat [render_expr b; space; if_; nl; render_protocol p])
    | BlockingImply (b, p) ->
      nest 2 (concat [render_expr b; space; when_; nl; render_protocol p])
    | Forall (v, s, p) ->
      nest 2
        (concat
           [
             forall; space; render_var v; space; in_; space; render_var s; nl;
             render_protocol p;
           ])
    | Exists (v, s, p) ->
      nest 2
        (concat
           [
             exists; space; render_var v; space; in_; render_var s; nl;
             render_protocol p;
           ])
    | SendOnly { from; to_; msg = MessageC { typ; args } } ->
      concat
        [
          star; render_var from; arrow; render_var to_; colon; space;
          string typ;
          (match args with
          | [] -> empty
          | _ -> parens (separate (spaced comma) (List.map render_expr args)));
        ]
    | ReceiveOnly { from; to_; msg = MessageD { typ; args } } ->
      concat
        [
          render_var from; arrow; render_var to_; star; colon; space;
          string typ;
          (match args with
          | [] -> empty
          | _ -> parens (separate (spaced comma) (List.map render_var args)));
        ]
    | Comment (_, _, _) -> failwith "comment"
  in
  render_protocol p

let interleave_n xss = List.fold_right (fun c t -> List.interleave c t) xss []

exception Eval_failure of string

(* let fail s = raise (Eval_failure (Format.sprintf s)) *)
let fail s = Format.ksprintf ~f:(fun m -> raise (Eval_failure m)) s

let dump_env pr e =
  VMap.bindings e
  |> List.map (fun (a, b) -> Format.sprintf "%a->%a" pp_var a pr b)
  |> String.concat "; "

let dump_env_ env = Format.printf "%s@." (dump_env pp_expr env)

let rec eval_expr env e =
  (* Format.printf "eval_expr %a@." pp_expr e; *)
  (* dump_env_ env; *)
  match e with
  | Int _ | Bool _ -> e
  | Set s -> Set (s |> List.map (eval_expr env))
  | List s -> List (s |> List.map (eval_expr env))
  | Map s -> Map (List.map (fun (a, b) -> (a, eval_expr env b)) s)
  | Tuple (a, b) -> Tuple (eval_expr env a, eval_expr env b)
  | App (name, args) ->
    begin
      match name with
      | "+" ->
        List.fold_right
          (fun a b ->
            match (eval_expr env a, eval_expr env b) with
            | (Int a, Int b) -> Int (a + b)
            | (a, b) ->
              fail "invalid args to %s: %a, %a" name pp_expr a pp_expr b)
          args (Int 0)
      | "==" when List.length args = 2 ->
        let (a, b) = (List.hd args, List.hd (List.tl args)) in
        let a = eval_expr env a in
        let b = eval_expr env b in
        Bool (equal_expr a b)
      | "&" ->
        List.fold_right
          (fun a b ->
            match (eval_expr env a, eval_expr env b) with
            | (Bool a, Bool b) -> Bool (a && b)
            | (a1, b1) ->
              (* extra *)
              fail "invalid args to %s: %a -> %a, %a -> %a" name pp_expr a
                pp_expr a1 pp_expr b pp_expr b1)
          args (Bool true)
      | "|" ->
        List.fold_right
          (fun a b ->
            match (eval_expr env a, eval_expr env b) with
            | (Bool a, Bool b) -> Bool (a || b)
            | (a, b) ->
              fail "invalid args to %s: %a, %a" name pp_expr a pp_expr b)
          args (Bool false)
      | _ -> fail "invalid operator %s" name
    end
  | Var v ->
  try VMap.find v env with Not_found -> fail "%a is unbound" pp_var v

(* let rec pairwise f xs= 
match xs with
| [] | [_] -> xs
| a :: b :: xs -> f a b :: pairwise f( b :: xs) *)

let rec pairwise_foldr f init xs =
  match xs with
  | [] | [_] -> init
  | a :: b :: xs1 -> f a b (pairwise_foldr f init (b :: xs1))

let rec pairwise_foldr1 f xs =
  match xs with
  | [] | [_] -> xs
  | a :: b :: xs1 -> f a b (pairwise_foldr1 f (b :: xs1))

(** caller should return the left arg or info derived from it *)
let adj_concat_map f xs =
  let rec aux xs =
    match xs with [] | [_] -> [xs] | a :: b :: xs1 -> f a b :: aux (b :: xs1)
  in
  aux xs |> List.concat

(** each element is processed exactly once, like map. f has to produce information summarising both elements *)
let map_pairs f xs =
  let rec aux xs =
    match xs with [] | [_] -> [xs] | a :: b :: xs1 -> f a b :: aux xs1
  in
  aux xs |> List.concat

let rec normalize_once p =
  (* let%trace rec normalize_once : protocol -> protocol = fun p -> *)
  let rec useful = function
    | Emp | Seq [] -> false
    | Forall (_, _, p) | Exists (_, _, p) -> useful p
    | _ -> true
  in
  (* let aux p = *)
  match p with
  (* what's this for? *)
  (* | Seq [s] -> normalize_once s *)
  | Seq s ->
    let s = s |> List.map normalize_once |> List.filter useful in
    let s =
      map_pairs
        (fun a b ->
          match (a, b) with (Seq a1, Seq b1) -> [Seq (a1 @ b1)] | _ -> [a; b])
        s
    in
    Seq (s |> List.concat_map (fun p -> match p with Seq ps -> ps | _ -> [p]))
  | Par s ->
    let s = s |> List.map normalize_once |> List.filter useful in
    let s =
      map_pairs
        (fun a b ->
          match (a, b) with (Par a1, Par b1) -> [Par (a1 @ b1)] | _ -> [a; b])
        s
    in
    Par (s |> List.concat_map (fun p -> match p with Par ps -> ps | _ -> [p]))
  | Disj (a, b) ->
    begin
      match (a, b) with
      | (a, _) when not (useful a) -> normalize_once b
      | (_, b) when not (useful b) -> normalize_once a
      | _ -> Disj (normalize_once a, normalize_once b)
    end
  | Emp -> p
  | Send _ -> p
  | Assign (_, _) -> p
  | Imply (c, p) -> Imply (c, normalize_once p)
  | BlockingImply (c, p) -> BlockingImply (c, normalize_once p)
  | Forall (v, s, p) -> Forall (v, s, normalize_once p)
  | Exists (v, s, p) -> Exists (v, s, normalize_once p)
  | SendOnly _ -> p
  | ReceiveOnly _ -> p
  | Comment (pa, s, p) -> Comment (pa, s, normalize_once p)

(* in let r = aux p in *)
(* if useful r then Some r else None *)

let rec normalize p =
  let p1 = normalize_once p in
  (* print_endline "normalize"; *)
  if equal_protocol p p1 then
    p1
  else
    normalize p1

let rec transpose xss =
  match xss with
  | (_ :: _) :: _ -> List.map List.hd xss :: transpose (List.map List.tl xss)
  | _ -> []

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
(* let rec solve_subs env = *)
let%trace rec solve_subs : pvar IMap.t -> pvar IMap.t =
 fun env ->
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

let%trace get_party : var -> env -> pvar option =
 fun var env ->
  (* let get_party var env = *)
  let open Option.Infix in
  let* v = VMap.find_opt var env.var_info in
  IMap.find_opt v env.var_constraints

let%trace put_party : var -> pvar -> env -> pvar * env =
 fun var p env ->
  (* let put_party var p env = *)
  let v = fresh () in
  ( Mono v,
    {
      env with
      var_info = VMap.add var v env.var_info;
      var_constraints = IMap.add v p env.var_constraints;
    } )

(* let init_party var env = *)
let%trace init_party : var -> env -> pvar * env =
 fun var env ->
  let v = fresh () in
  (Mono v, { env with var_info = VMap.add var v env.var_info })

(* let add_equality v1 v2 env = *)
let%trace add_equality : var -> var -> env -> env =
 fun v1 v2 env ->
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

(* { env with var_constraints = IMap.add p1 v2p env.var_constraints |> solve_subs} *)

(* pairwise_foldr (fun a b t -> print_endline a; print_endline b; t) () ["a";"b";"c"];; *)

let rec vars_in e =
  match e with
  | Int _ | Bool _ -> []
  | Var v -> [v]
  | App (_, s) | Set s | List s -> List.concat_map vars_in s
  | Map s -> List.concat_map vars_in (List.map snd s)
  | Tuple (a, b) -> List.concat_map vars_in [a; b]

(* let infer_parties env p = *)
let%trace infer_parties : env -> protocol -> env =
 fun env p ->
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

let replace_self party v =
  if List.mem ~eq:equal_var v party.vars then
    var "self"
  else
    v

(* parties is a list of (party name, vars belonging to it) *)
let project env pr =
  let rec aux pr =
    match pr with
    | Emp -> env.parties |> List.map (fun _ -> Emp)
    | Assign (v, e) ->
      env.parties
      |> List.map (fun party ->
             if is_owned_by party v then
               (* leave unqualified for now, since unqualified vars after this become emp anyway *)
               Assign (v, e)
             else
               Emp)
    | Seq ps -> ps |> List.map aux |> transpose |> List.map (fun p -> Seq p)
    | Par ps -> ps |> List.map aux |> transpose |> List.map (fun p -> Par p)
    | Disj (a, b) ->
      [a; b] |> List.map aux |> transpose
      |> List.map (function [a; b] -> Disj (a, b) | _ -> failwith "invalid")
    | Send { from; to_; msg } ->
      env.parties
      |> List.map (fun party ->
             if List.mem ~eq:equal_var from party.vars then
               SendOnly
                 {
                   from = replace_self party from;
                   to_ = replace_self party to_;
                   msg = msg_construct msg;
                 }
             else if List.mem ~eq:equal_var to_ party.vars then
               ReceiveOnly
                 {
                   from = replace_self party from;
                   to_ = replace_self party to_;
                   msg = msg_destruct msg;
                 }
             else
               Emp)
    | Imply (c, body) ->
      List.map2
        (fun party body1 ->
          if List.for_all (is_owned_by party) (vars_in c) then
            Imply (c, body1)
          else (* note that this is the body of the conditional, not emp *)
            body1)
        env.parties (aux body)
    | BlockingImply (c, body) ->
      List.map2
        (fun party body1 ->
          if List.for_all (is_owned_by party) (vars_in c) then
            BlockingImply (c, body1)
          else
            body1)
        env.parties (aux body)
    | Forall (v, s, p) ->
      (* env.parties |> List.map (fun _ -> p) *)
      List.map2
        (fun party p1 ->
          (* Format.printf "v %a party %a@." pp_var v (List.pp pp_var) party.vars; *)
          if List.mem ~eq:equal_var v party.vars then
            p1
          else
            Forall (v, s, p1))
        env.parties (aux p)
    | Exists (v, s, p) ->
      List.map2
        (fun party p1 ->
          if List.mem ~eq:equal_var v party.vars then
            p1
          else
            Exists (v, s, p1))
        env.parties (aux p)
    | SendOnly _ -> fail "send only should not be used in front end language"
    | ReceiveOnly _ ->
      fail "receive only should not be used in front end language"
    | Comment (party, s, p) ->
      List.map2
        (fun party1 p1 ->
          match party with
          | None -> p1
          | Some party2 ->
            if equal_var party2 party1.repr then Comment (party, s, p1) else p1)
        env.parties (aux p)
  in
  aux pr |> List.map normalize

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

module Tpc = struct
  (* let coord = Party "coordinator" *)

  (* let part = Party "participant" *)

  let coordinator = var "C"

  let participants = var "P"

  let p = var "p"

  let c = var "c"

  let responded = var "responded"

  let aborted = var "aborted"

  let env =
    {
      parties =
        [
          {
            repr = coordinator;
            other_sets = [];
            vars = [c];
            owned_vars = [responded; aborted; p];
          };
          { repr = participants; other_sets = []; vars = [p]; owned_vars = [c] };
        ];
      var_info = VMap.empty;
      var_constraints = IMap.empty;
    }

  let protocol =
    Forall
      ( c,
        coordinator,
        Seq
          [
            Forall
              ( p,
                participants,
                Seq
                  [
                    Send { from = c; to_ = p; msg = msg "prepare" };
                    (* Comment *)
                    (* ( Some participants,
                       "participant's internal choice",
                       Comment
                         ( Some coordinator,
                           "coordinator's external choice", *)
                    Disj
                      ( Seq
                          [
                            Send { from = p; to_ = c; msg = msg "prepared" };
                            Assign
                              (responded, plus (Var responded) (Set [Var p]));
                          ],
                        Seq
                          [
                            Send { from = p; to_ = c; msg = msg "abort" };
                            Assign (aborted, plus (Var aborted) (Set [Var p]));
                          ] )
                    (* ) ) *);
                  ] );
            Disj
              ( BlockingImply
                  ( eq (Var aborted) (Set []),
                    Forall
                      ( p,
                        participants,
                        Seq
                          [
                            Send { from = c; to_ = p; msg = msg "commit" };
                            Send { from = p; to_ = c; msg = msg "commit_ack" };
                          ] ) ),
                Forall
                  ( p,
                    participants,
                    Seq
                      [
                        Send { from = c; to_ = p; msg = msg "abort" };
                        Send { from = p; to_ = c; msg = msg "abort_ack" };
                      ] ) );
          ] )
end

module Test = struct
  let responded = var "responded"

  let participant = var "P"

  let p = var "p"

  let env =
    {
      parties =
        [
          {
            repr = participant;
            other_sets = [];
            vars = [p];
            owned_vars = [responded];
          };
        ];
      var_info = VMap.empty;
      var_constraints = IMap.empty;
    }

  let protocol =
    Seq
      [
        Assign (responded, plus (Var responded) (Set [Var p]));
        Assign (responded, plus (Var responded) (Set [Var p]));
      ]
end

module Paxos = struct
  let proposers = var "P"

  let acceptors = var "A"

  let learners = var "L"

  let l = var "l"

  let p = var "p"

  let a = var "a"

  let a1 = var "a1"

  (* current proposal number of proposer *)
  let proposal = var "proposal"

  let value = var "value"

  let majority = var "majority"

  let promise_responses = var "promise_responses"

  (* acceptor *)
  let highest_proposal = var "highest_proposal"

  let accepted_proposal = var "accepted_proposal"

  let accepted_value = var "accepted_value"

  (* messages *)
  let n = var "n"

  let cv = var "cv"

  let cp = var "cp"

  let pn = var "pn"

  let pv = var "pv"

  let env =
    {
      parties =
        [
          {
            repr = proposers;
            other_sets = [];
            vars = [p];
            owned_vars =
              [a; p]
              @ [proposal; value; majority; promise_responses; cp]
              @ [cp; cv];
          }; { repr = learners; other_sets = []; vars = [l]; owned_vars = [] };
          {
            repr = acceptors;
            other_sets = [promise_responses];
            vars = [a; a1];
            owned_vars =
              [p]
              @ [highest_proposal; accepted_proposal; accepted_value]
              @ [n; pn; pv];
          };
        ];
      var_info = VMap.empty;
      var_constraints = IMap.empty;
    }

  let protocol =
    Comment
      ( None,
        "all currently-competing proposers",
        Seq
          [
            Forall
              ( p,
                proposers,
                Seq
                  [
                    Assign (p >. proposal, Int 0);
                    Assign (p >. value, App ("external", []));
                    Assign (p >. cp, Tuple (Int 0, Int 0));
                    Assign
                      ( p >. majority,
                        plus
                          (App ("/", [App ("size", [Var acceptors]); Int 2]))
                          (Int 1) ); Assign (p >. promise_responses, Set []);
                  ] );
            Forall
              ( a,
                acceptors,
                Seq
                  [
                    Assign (a >. highest_proposal, Tuple (Int 0, Int 0));
                    Assign (a >. accepted_proposal, Tuple (Int 0, Int 0));
                    Assign (a >. accepted_value, Int 0);
                  ] );
            Forall
              ( p,
                proposers,
                Par
                  [
                    Seq
                      [
                        Assign
                          (p >. proposal, plus (Var (p >. proposal)) (Int 1));
                        Forall
                          ( a,
                            acceptors,
                            Seq
                              [
                                Send
                                  {
                                    from = p;
                                    to_ = a;
                                    msg =
                                      Message
                                        {
                                          typ = "prepare";
                                          args =
                                            [
                                              ( n,
                                                Tuple
                                                  (Var p, Var (p >. proposal))
                                              );
                                            ];
                                        };
                                  };
                                Imply
                                  ( gt (Var n) (Var (a >. highest_proposal)),
                                    Seq
                                      [
                                        Assign (a >. highest_proposal, Var n);
                                        Send
                                          {
                                            from = a;
                                            to_ = p;
                                            msg =
                                              Message
                                                {
                                                  typ = "promise";
                                                  args =
                                                    [
                                                      ( cp,
                                                        Var
                                                          (a
                                                         >. accepted_proposal)
                                                      );
                                                      ( cv,
                                                        Var (a >. accepted_value)
                                                      );
                                                    ];
                                                };
                                          };
                                        Assign
                                          ( p >. promise_responses,
                                            plus
                                              (Var (p >. promise_responses))
                                              (Set [Var a]) );
                                        Comment
                                          ( Some proposers,
                                            "if a has already accepted \
                                             something",
                                            Imply
                                              ( and_
                                                  (gt (Var cp)
                                                     (Tuple (Int 0, Int 0)))
                                                  (gt (Var cp) (Var (p >. cp))),
                                                Seq
                                                  [
                                                    Assign (p >. cp, Var cp);
                                                    Assign (p >. value, Var cv);
                                                  ] ) );
                                      ] );
                              ] );
                      ];
                    Comment
                      ( Some proposers,
                        {|doesn't continue replying with accepts if others outside this set reply|},
                        BlockingImply
                          ( gt
                              (App ("size", [Var (p >. promise_responses)]))
                              (Var (p >. majority)),
                            Comment
                              ( Some proposers,
                                "it's sufficient to reply to the majority \
                                 subset",
                                Forall
                                  ( a1,
                                    p >. promise_responses,
                                    Seq
                                      [
                                        Send
                                          {
                                            from = p;
                                            to_ = a1;
                                            msg =
                                              Message
                                                {
                                                  typ = "propose";
                                                  args =
                                                    [
                                                      (pn, Var (p >. proposal));
                                                      (pv, Var (p >. value));
                                                    ];
                                                };
                                          };
                                        Imply
                                          ( eq (Var pn)
                                              (Var (a1 >. highest_proposal)),
                                            Seq
                                              [
                                                Assign
                                                  ( a1 >. accepted_proposal,
                                                    Var pn );
                                                Assign
                                                  (a1 >. accepted_value, Var pv);
                                                Send
                                                  {
                                                    from = a1;
                                                    to_ = p;
                                                    msg = msg "accept";
                                                  };
                                                Forall
                                                  ( l,
                                                    learners,
                                                    Send
                                                      {
                                                        from = a1;
                                                        to_ = l;
                                                        msg = msg "accept";
                                                      } );
                                              ] );
                                      ] ) ) ) );
                  ] );
          ] )
end

let snapshot_protocol name env pr =
  let projections =
    let res = project env pr in
    List.map2
      (fun { repr; _ } r ->
        let init =
          match has_initiative (V (None, var_name repr)) r with
          | true -> "has"
          | false -> "does not have"
        in
        Format.sprintf "projection of %s@.%s %s initiative@.@.%a"
          (var_name repr) (var_name repr) init pp_protocol r)
      env.parties res
    |> String.concat "\n--\n"
  in
  let inf =
    (* TODO toggle this *)
    (* infer_parties env pr |> ignore; *)
    (* let inf = infer_parties env pr in *)
    (* p_env inf *)
    "<inferred parties>"
  in
  let s =
    Format.sprintf "protocol:@.@.%a@.@.---@.@.projections:@.@.%s@.%s@."
      pp_protocol pr projections inf
  in
  IO.File.(write_exn (make ("/tmp/" ^ name ^ ".txt")) s);
  print_endline s

let parse_party_spec s =
  let parts = String.split ~by:":" s in
  let[@warning "-8"] [[repr]; vars; owned_vars] =
    List.map (String.split ~by:",") parts
  in
  {
    repr = var repr;
    vars = List.map var vars;
    owned_vars = List.map var owned_vars;
    other_sets = [];
  }

let print party_specs ast no_normalize file =
  match party_specs with
  | _ :: _ ->
    let parties = List.map parse_party_spec party_specs in
    Format.printf "parties %s@." ([%derive.show: party_info list] parties)
  | [] ->
    let p =
      if String.equal file "-" then
        Parsing.parse_mono_ic stdin
      else
        Parsing.parse_mono file
    in
    (* let p = Parsing.parse_inc file in *)
    (match p with
    | Ok p ->
      p
      (* |> eval |> string_of_int *)
      (* |> Exp.show *)
      (* |> Format.sprintf "%a" pp_protocol |> print_endline *)
      |> (if no_normalize then Fun.id else normalize)
      |> Fun.Infix.(
           if ast then
             show_protocol %> print_endline
           else
             render_protocol %> PPrint.ToChannel.pretty 0.8 120 stdout)
    | Error s -> print_endline s)

(* Tracing.wrap (fun () ->
    (* print_endline "abccc"; *)
    (* snapshot_protocol "test" Test.env Test.protocol *)
    snapshot_protocol "paxos" Paxos.env Paxos.protocol) *)

let%expect_test "2pc" =
  snapshot_protocol "2pc" Tpc.env Tpc.protocol;
  [%expect
    {|
    protocol:

    forall c:C.
      (forall p:P.
         (c->p: prepare;
          (p->c: prepared;
           responded = responded + {p})
          \/
          (p->c: abort;
           aborted = aborted + {p}));
       aborted == {} =>*
         forall p:P.
           (c->p: commit;
            p->c: commit_ack)
       \/
       forall p:P.
         (c->p: abort;
          p->c: abort_ack))

    ---

    projections:

    projection of C
    C has initiative

    (forall p:P.
       (*self->p: prepare;
        (p->self*: prepared;
         responded = responded + {p})
        \/
        (p->self*: abort;
         aborted = aborted + {p}));
     aborted == {} =>*
       forall p:P.
         (*self->p: commit;
          p->self*: commit_ack)
     \/
     forall p:P.
       (*self->p: abort;
        p->self*: abort_ack))
    --
    projection of P
    P does not have initiative

    forall c:C.
      (c->self*: prepare;
       (*self->c: prepared)
       \/
       (*self->c: abort);
       (c->self*: commit;
        *self->c: commit_ack)
       \/
       (c->self*: abort;
        *self->c: abort_ack))
    <inferred parties> |}]

let%expect_test "paxos" =
  snapshot_protocol "paxos" Paxos.env Paxos.protocol;
  [%expect
    {|
    protocol:

    // all currently-competing proposers
    (forall p:P.
       (p.proposal = 0;
        p.value = external();
        p.cp = <0, 0>;
        p.majority = size(A) / 2 + 1;
        p.promise_responses = {});
     forall a:A.
       (a.highest_proposal = <0, 0>;
        a.accepted_proposal = <0, 0>;
        a.accepted_value = 0);
     forall p:P.
       ((p.proposal = p.proposal + 1;
         forall a:A.
           (p->a: prepare(n=<p, p.proposal>);
            n > a.highest_proposal =>
              (a.highest_proposal = n;
               a->p: promise(cp=a.accepted_proposal, cv=a.accepted_value);
               p.promise_responses = p.promise_responses + {a};
               // if a has already accepted something
               cp > <0, 0> & cp > p.cp =>
                 (p.cp = cp;
                  p.value = cv)))))
       *
       (// doesn't continue replying with accepts if others outside this set reply
        size(p.promise_responses) > p.majority =>*
          // it's sufficient to reply to the majority subset
          forall a1:p.promise_responses.
            (p->a1: propose(pn=p.proposal, pv=p.value);
             pn == a1.highest_proposal =>
               (a1.accepted_proposal = pn;
                a1.accepted_value = pv;
                a1->p: accept;
                forall l:L.
                  a1->l: accept))))

    ---

    projections:

    projection of P
    P has initiative

    (p.proposal = 0;
     p.value = external();
     p.cp = <0, 0>;
     p.majority = size(A) / 2 + 1;
     p.promise_responses = {};
     ((p.proposal = p.proposal + 1;
       forall a:A.
         (*self->a: prepare(<p, p.proposal>);
          a->self*: promise(cp, cv);
          p.promise_responses = p.promise_responses + {a};
          // if a has already accepted something
          cp > <0, 0> & cp > p.cp =>
            (p.cp = cp;
             p.value = cv))))
     *
     (// doesn't continue replying with accepts if others outside this set reply
      size(p.promise_responses) > p.majority =>*
        // it's sufficient to reply to the majority subset
        forall a1:p.promise_responses.
          (*self->a1: propose(p.proposal, p.value);
           a1->self*: accept)))
    --
    projection of L
    L does not have initiative

    (forall p:P.
       (forall a1:p.promise_responses.
          (a1->self*: accept)))
    --
    projection of A
    A has initiative

    (a.highest_proposal = <0, 0>;
     a.accepted_proposal = <0, 0>;
     a.accepted_value = 0;
     forall p:P.
       ((p->self*: prepare(n);
         n > a.highest_proposal =>
           (a.highest_proposal = n;
            *self->p: promise(a.accepted_proposal, a.accepted_value))))
       *
       ((p->self*: propose(pn, pv);
         pn == a1.highest_proposal =>
           (a1.accepted_proposal = pn;
            a1.accepted_value = pv;
            *self->p: accept;
            forall l:L.
              *self->l: accept))))
    <inferred parties>
  |}]
