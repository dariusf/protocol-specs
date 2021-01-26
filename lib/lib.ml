open Containers

type party = Party of string [@@deriving ord, eq]

type var =
  | V of {
      party : party;
      var : string;
    }
[@@deriving ord, eq]

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

let pp_var fmt (V { party = Party party; var }) =
  Format.fprintf fmt "%s.%s" party var

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

let pp_msg fmt (Message { typ; args }) =
  Format.fprintf fmt "%s%s" typ
    (match args with
    | [] -> ""
    | _ ->
      args
      |> List.map (fun (k, v) -> Format.sprintf "%s: %a" k pp_expr v)
      |> String.concat ", "
      |> fun a -> "(" ^ a ^ ")")

type protocol =
  | Emp
  | Seq of protocol list
  | Par of protocol list
  | Send of {
      from : party;
      to_ : party;
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
  | Send { from = Party f; to_ = Party t; msg } ->
    fprintf fmt "%s->%s: %a" f t pp_msg msg
  | Assign (v, e) -> fprintf fmt "%a := %a" pp_var v pp_expr e
  | If (c, co, a) ->
    fprintf fmt
      "@[<v 0>if (%a) {@;<0 2>@[<v 0>%a@]@,} else {@;<0 2>@[<v 0>%a@]@,}@]"
      pp_expr c pp_protocol co pp_protocol a

(** generates some interleaving *)
let interleave_n xss = List.fold_right (fun c t -> List.interleave c t) xss []

let ( >. ) c s = V { party = c; var = s }

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
    | Send { from = Party a; to_ = Party b; msg } ->
      Format.printf "%s->%s: %a@." a b pp_msg msg;
      let (Message { args; _ }) = msg in
      let assignments =
        List.map
          (fun (name, v) ->
            let var = V { party = Party b; var = "m_" ^ name } in
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
  let coord = Party "coord"

  let part1 = Party "part1"

  let part2 = Party "part2"

  let participants = [| part1; part2 |]

  let msg name = Message { typ = name; args = [] }

  let phase1 i : protocol =
    Seq
      [
        Send { from = coord; to_ = participants.(i); msg = msg "prepare" };
        Assign (participants.(i) >. "ok", Bool false);
        Send
          {
            from = participants.(i);
            to_ = coord;
            (* decide *)
            msg =
              Message { typ = "prepare_ack"; args = [("commit", Bool true)] };
          };
        Assign
          ( coord >. "res",
            and_ (Var (coord >. "res")) (Var (coord >. "m_commit")) );
        Assign (coord >. "count", plus (Var (coord >. "count")) (Int 1));
      ]

  let phase2a i : protocol =
    Seq
      [
        Send { from = coord; to_ = participants.(i); msg = msg "commit" };
        Assign (participants.(i) >. "ok", Bool false);
        Send { from = participants.(i); to_ = coord; msg = msg "commit_ack" };
        Assign (coord >. "count", plus (Var (coord >. "count")) (Int 1));
      ]

  let phase2b i : protocol =
    Seq
      [
        Send { from = coord; to_ = participants.(i); msg = msg "abort" };
        Assign (participants.(i) >. "ok", Bool false);
        Send { from = participants.(i); to_ = coord; msg = msg "abort_ack" };
        Assign (coord >. "count", plus (Var (coord >. "count")) (Int 1));
      ]

  let protocol =
    Seq
      [
        Assign (coord >. "count", Int 0); Assign (coord >. "res", Bool true);
        Assign (coord >. "n", Int 2); Par [phase1 0; phase1 1];
        If
          ( and_
              (Var (coord >. "res"))
              (eq (Var (coord >. "count")) (Var (coord >. "n"))),
            Seq [Assign (coord >. "count", Int 0); Par [phase2a 0; phase2a 1]],
            Seq [Assign (coord >. "count", Int 0); Par [phase2b 0; phase2b 1]]
          );
      ]
end

let snapshot_protocol p =
  Format.printf "%a@." pp_protocol p;
  eval p

let%expect_test "2pc" =
  snapshot_protocol Tpc.protocol;
  [%expect {|
    coord.count := 0;
    coord.res := true;
    coord.n := 2;
    (coord->part1: prepare;
     part1.ok := false;
     part1->coord: prepare_ack(commit: true);
     coord.res := coord.res /\ coord.m_commit;
     coord.count := coord.count + 1)
    ||
    (coord->part2: prepare;
     part2.ok := false;
     part2->coord: prepare_ack(commit: true);
     coord.res := coord.res /\ coord.m_commit;
     coord.count := coord.count + 1);
    if (coord.res /\ coord.count = coord.n) {
      coord.count := 0;
      (coord->part1: commit;
       part1.ok := false;
       part1->coord: commit_ack;
       coord.count := coord.count + 1)
      ||
      (coord->part2: commit;
       part2.ok := false;
       part2->coord: commit_ack;
       coord.count := coord.count + 1)
    } else {
      coord.count := 0;
      (coord->part1: abort;
       part1.ok := false;
       part1->coord: abort_ack;
       coord.count := coord.count + 1)
      ||
      (coord->part2: abort;
       part2.ok := false;
       part2->coord: abort_ack;
       coord.count := coord.count + 1)
    }
    coord.count := 0 (prev. unset)
    coord.res := true (prev. unset)
    coord.n := 2 (prev. unset)
    coord->part1: prepare
    coord->part2: prepare
    part1.ok := false (prev. unset)
    part2.ok := false (prev. unset)
    part1->coord: prepare_ack(commit: true)
    coord.m_commit := true (prev. unset)
    part2->coord: prepare_ack(commit: true)
    coord.m_commit := true (prev. true)
    coord.res := true (prev. true)
    coord.res := true (prev. true)
    coord.count := 1 (prev. 0)
    coord.count := 2 (prev. 1)
    coord.count := 0 (prev. 2)
    coord->part1: commit
    coord->part2: commit
    part1.ok := false (prev. false)
    part2.ok := false (prev. false)
    part1->coord: commit_ack
    part2->coord: commit_ack
    coord.count := 1 (prev. 0)
    coord.count := 2 (prev. 1)
  |}]
