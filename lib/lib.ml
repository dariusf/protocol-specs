open Containers

type party = Party of string [@@deriving ord, eq]

let pp_party fmt (Party p) = Format.fprintf fmt "%s" p

type var = V of party * string [@@deriving ord, eq]

module VMap = struct
  include Map.Make (struct
    type t = var

    let compare = compare_var
  end)
end

type expr =
  | Int of int
  | Bool of bool
  | Fun of string * expr list
  | Var of var
[@@deriving eq]

let plus a b = Fun ("+", [a; b])

let eq a b = Fun ("=", [a; b])

let and_ a b = Fun ("/\\", [a; b])

let or_ a b = Fun ("\\/", [a; b])

let pp_var fmt (V (Party p, var)) = Format.fprintf fmt "%s.%s" p var

let rec pp_expr fmt e =
  let open Format in
  match e with
  | Int i -> fprintf fmt "%d" i
  | Bool b -> fprintf fmt "%b" b
  | Fun (name, es) ->
    if List.length es = 2 then
      fprintf fmt "@[%a@ %s@ %a@]" pp_expr (List.nth es 0) name pp_expr
        (List.nth es 1)
    else
      fprintf fmt "%s(%a)" name (List.pp pp_expr) es
  | Var v -> pp_var fmt v

type msg =
  | Message of {
      typ : string;
      args : (string * expr) list;
    }
[@@deriving show { with_path = false }]

let msg name = Message { typ = name; args = [] }

let pp_msg fmt (Message { typ; args }) =
  Format.fprintf fmt "%s%s" typ
    (match args with
    | [] -> ""
    | _ ->
      args
      |> List.map (fun (k, v) -> Format.sprintf "%s: %a" k pp_expr v)
      |> String.concat ", "
      |> fun a -> "(" ^ a ^ ")")

module Qn = struct
  type 'a t =
    | Some of 'a
    | All of 'a

  let get qp = match qp with Some p -> p | All p -> p

  let pp pr fmt qp =
    let s = match qp with Some _ -> "some" | All _ -> "all" in
    Format.fprintf fmt "%s %a" s pr (get qp)
end

type protocol =
  | Emp
  | Seq of protocol list
  | Par of protocol list
  | Send of {
      from : party Qn.t;
      to_ : party Qn.t;
      msg : msg;
    }
  | Assign of var * expr
  | If of expr * protocol * protocol

let rec pp_protocol fmt p =
  let open Format in
  match p with
  | Emp -> fprintf fmt "nil"
  | Seq ps ->
    List.pp
      ~pp_start:(fun fmt () -> fprintf fmt "@[<v 0>")
      ~pp_stop:(fun fmt () -> fprintf fmt "@]")
      ~pp_sep:(fun fmt () -> fprintf fmt ";@,")
      pp_protocol fmt ps
  | Par ps ->
    List.pp
      ~pp_start:(fun fmt () -> fprintf fmt "")
      ~pp_stop:(fun fmt () -> fprintf fmt "")
      ~pp_sep:(fun fmt () -> fprintf fmt "@ ||@ ")
      (fun fmt ps -> fprintf fmt "(%a)" pp_protocol ps)
      fmt ps
  | Send { from; to_; msg } ->
    fprintf fmt "%a->%a: %a" (Qn.pp pp_party) from (Qn.pp pp_party) to_ pp_msg
      msg
  | Assign (v, e) -> fprintf fmt "%a := %a" pp_var v pp_expr e
  | If (c, co, a) ->
    fprintf fmt
      "@[<v 0>if (%a) {@;<0 2>@[<v 0>%a@]@,} else {@;<0 2>@[<v 0>%a@]@,}@]"
      pp_expr c pp_protocol co pp_protocol a

(** generates some interleaving *)
let interleave_n xss = List.fold_right (fun c t -> List.interleave c t) xss []

let ( >. ) c s = V (c, s)

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
  | Fun (name, args) ->
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
      | "=" when List.length args = 2 ->
        let (a, b) = (List.hd args, List.hd (List.tl args)) in
        let a = eval_expr env a in
        let b = eval_expr env b in
        Bool (equal_expr a b)
      | "/\\" ->
        List.fold_right
          (fun a b ->
            match (eval_expr env a, eval_expr env b) with
            | (Bool a, Bool b) -> Bool (a && b)
            | (a1, b1) ->
              (* extra *)
              fail "invalid args to %s: %a -> %a, %a -> %a" name pp_expr a
                pp_expr a1 pp_expr b pp_expr b1)
          args (Bool true)
      | "\\/" ->
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

let eval p =
  let rec aux env p =
    (* Format.printf "eval %a@." pp_protocol p; *)
    match p with
    | Emp -> env
    | Seq ps ->
      (* Format.printf "seq@."; *)
      List.fold_left aux env ps
    | Par ps ->
      (* Format.printf "par@."; *)
      ps
      |> List.map (fun p ->
             match p with
             | Par _ -> fail "nested par not allowed"
             | Seq ps1 -> ps1
             | p -> [p])
      |> interleave_n
      |> fun ps2 -> aux env (Seq ps2)
    | Send { from; to_; msg } ->
      Format.printf "%a->%a: %a@." (Qn.pp pp_party) from (Qn.pp pp_party) to_
        pp_msg msg;
      let (Message { args; _ }) = msg in
      let assignments =
        List.map
          (fun (name, v) ->
            let var = V (Qn.get to_, "m_" ^ name) in
            Assign (var, v))
          args
      in
      aux env (Seq assignments)
    | Assign (v, e) ->
      let prev =
        VMap.find_opt v env
        |> Option.map (Format.sprintf "%a" pp_expr)
        |> Option.get_or ~default:"unset"
      in
      let e = eval_expr env e in
      Format.printf "%a := %a (prev. %s)@." pp_var v pp_expr e prev;
      VMap.add v e env
    | If (c, co, alt) ->
      let c = eval_expr env c in
      (match c with Bool true -> aux env co | _ -> aux env alt)
  in
  try aux VMap.empty p |> ignore
  with Eval_failure s -> Format.printf "evaluation failed: %s@." s

module Tpc = struct
  let coord = Party "coordinator"

  let part = Party "participant"

  let phase1 =
    Seq
      [
        Send { from = Some coord; to_ = All part; msg = msg "prepare" };
        Assign (part >. "ok", Bool false);
        Send
          {
            (* TODO need a way to make this dependent. That? *)
            from = Some part;
            to_ = All coord;
            (* decide *)
            msg =
              Message { typ = "prepare_ack"; args = [("commit", Bool true)] };
          };
        Assign
          ( coord >. "res",
            and_ (Var (coord >. "res")) (Var (coord >. "m_commit")) );
        Assign (coord >. "count", plus (Var (coord >. "count")) (Int 1));
      ]

  let phase2a =
    Seq
      [
        Send { from = Some coord; to_ = All part; msg = msg "commit" };
        Assign (part >. "ok", Bool false);
        Send { from = Some part; to_ = All coord; msg = msg "commit_ack" };
        Assign (coord >. "count", plus (Var (coord >. "count")) (Int 1));
      ]

  let phase2b =
    Seq
      [
        Send { from = Some coord; to_ = All part; msg = msg "abort" };
        Assign (part >. "ok", Bool false);
        Send { from = Some part; to_ = Some coord; msg = msg "abort_ack" };
        Assign (coord >. "count", plus (Var (coord >. "count")) (Int 1));
      ]

  let protocol =
    (* TODO is cardinality associated with each party or each par? *)
    Seq
      [
        Assign (coord >. "count", Int 0); Assign (coord >. "res", Bool true);
        Assign (coord >. "n", Int 2); phase1;
        If
          ( and_
              (Var (coord >. "res"))
              (eq (Var (coord >. "count")) (Var (coord >. "n"))),
            Seq [Assign (coord >. "count", Int 0); phase2a],
            Seq [Assign (coord >. "count", Int 0); phase2b] );
      ]
end

module Paxos = struct
  let proposer = Party "proposer"

  let acceptor = Party "acceptor"

  let protocol = Seq [Assign (proposer >. "count", Int 0)]
end

let snapshot_protocol p =
  Format.printf "%a@.---@." pp_protocol p;
  eval p

let%expect_test "2pc" =
  snapshot_protocol Tpc.protocol;
  [%expect
    {|
    coordinator.count := 0;
    coordinator.res := true;
    coordinator.n := 2;
    some coordinator->all participant: prepare;
    participant.ok := false;
    some participant->all coordinator: prepare_ack(commit: true);
    coordinator.res := coordinator.res /\ coordinator.m_commit;
    coordinator.count := coordinator.count + 1;
    if (coordinator.res /\ coordinator.count = coordinator.n) {
      coordinator.count := 0;
      some coordinator->all participant: commit;
      participant.ok := false;
      some participant->all coordinator: commit_ack;
      coordinator.count := coordinator.count + 1
    } else {
      coordinator.count := 0;
      some coordinator->all participant: abort;
      participant.ok := false;
      some participant->some coordinator: abort_ack;
      coordinator.count := coordinator.count + 1
    }
    ---
    coordinator.count := 0 (prev. unset)
    coordinator.res := true (prev. unset)
    coordinator.n := 2 (prev. unset)
    some coordinator->all participant: prepare
    participant.ok := false (prev. unset)
    some participant->all coordinator: prepare_ack(commit: true)
    coordinator.m_commit := true (prev. unset)
    coordinator.res := true (prev. true)
    coordinator.count := 1 (prev. 0)
    coordinator.count := 0 (prev. 1)
    some coordinator->all participant: abort
    participant.ok := false (prev. false)
    some participant->some coordinator: abort_ack
    coordinator.count := 1 (prev. 0)
  |}]

let%expect_test "paxos" =
  snapshot_protocol Paxos.protocol;
  [%expect
    {|
    proposer.count := 0
    ---
    proposer.count := 0 (prev. unset)
  |}]
