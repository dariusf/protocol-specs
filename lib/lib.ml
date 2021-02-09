open Containers

type party = Party of string [@@deriving ord, eq]

let pp_party fmt (Party p) = Format.fprintf fmt "%s" p

type var = V of party option * string [@@deriving ord, eq]

let var_name (V (_, v)) = v

let var_names vars = List.map var_name vars

module VMap = struct
  include Map.Make (struct
    type t = var

    let compare = compare_var
  end)
end

type expr =
  | Int of int
  | Bool of bool
  | Set of expr list
  | App of string * expr list
  | Var of var
[@@deriving eq]

let plus a b = App ("+", [a; b])

let eq a b = App ("==", [a; b])

let geq a b = App (">=", [a; b])

let ge a b = App (">", [a; b])

let and_ a b = App ("/\\", [a; b])

let or_ a b = App ("\\/", [a; b])

let pp_var fmt (V (p, var)) =
  match p with
  | Some p -> Format.fprintf fmt "%a.%s" pp_party p var
  | None -> Format.fprintf fmt "%s" var

let rec pp_expr fmt e =
  let open Format in
  match e with
  | Int i -> fprintf fmt "%d" i
  | Bool b -> fprintf fmt "%b" b
  | App (name, es) ->
    if List.length es = 2 then
      fprintf fmt "@[%a@ %s@ %a@]" pp_expr (List.nth es 0) name pp_expr
        (List.nth es 1)
    else
      fprintf fmt "%s(%a)" name (List.pp pp_expr) es
  | Var v -> pp_var fmt v
  | Set s -> fprintf fmt "{%a}" (List.pp pp_expr) s

type msg =
  | Message of {
      typ : string;
      args : (var * expr) list;
    }
[@@deriving show { with_path = false }, eq]

let msg name = Message { typ = name; args = [] }

let pp_msg fmt (Message { typ; args }) =
  Format.fprintf fmt "%s%s" typ
    (match args with
    | [] -> ""
    | _ ->
      args
      |> List.map (fun (k, v) -> Format.sprintf "%a: %a" pp_var k pp_expr v)
      |> String.concat ", "
      |> fun a -> "(" ^ a ^ ")")

type protocol =
  | Emp
  | Seq of protocol list
  | Par of protocol list
  | Disj of protocol * protocol
  | Send of {
      from : var;
      to_ : var;
      msg : msg;
    }
  | Assign of var * expr
  | Imply of expr * protocol
  | BlockingImply of expr * protocol
  | Forall of var * var * protocol
  | Exists of var * var * protocol
  (* extras *)
  | SendOnly of {
      from : var;
      to_ : var;
      msg : msg;
    }
  | ReceiveOnly of {
      from : var;
      to_ : var;
      msg : msg;
    }
[@@deriving eq]

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
      ~pp_sep:(fun fmt () -> fprintf fmt "@ ||@ ")
      (fun fmt ps -> fprintf fmt "(%a)" pp_protocol ps)
      fmt ps
  | Send { from; to_; msg } ->
    fprintf fmt "%a->%a: %a" pp_var from pp_var to_ pp_msg msg
  | SendOnly { from; to_; msg } ->
    fprintf fmt "*%a->%a: %a" pp_var from pp_var to_ pp_msg msg
  | ReceiveOnly { from; to_; msg } ->
    fprintf fmt "%a->%a*: %a" pp_var from pp_var to_ pp_msg msg
  | Assign (v, e) -> fprintf fmt "%a = %a" pp_var v pp_expr e
  | Disj (a, b) ->
    fprintf fmt "@[<v 0>%a@,\\/@,%a@]" pp_protocol a pp_protocol b
  | Imply (e, p) ->
    fprintf fmt "@[<v 0>%a =>@;<0 2>@[@,%a@]@]" pp_expr e pp_protocol p
  | BlockingImply (e, p) ->
    fprintf fmt "@[<v 0>%a =>*@;<0 2>@[@,%a@]@]" pp_expr e pp_protocol p
  | Forall (v, s, p) ->
    fprintf fmt "@[<v 0>forall %a:%a.@;<0 2>@[%a@]@]" pp_var v pp_var s
      pp_protocol p
  | Exists (v, s, p) ->
    fprintf fmt "@[<v 0>exists %a:%a.@;<0 2>@[%a@]@]" pp_var v pp_var s
      pp_protocol p

(* | If (c, co, a) ->
   fprintf fmt
     "@[<v 0>if (%a) {@;<0 2>@[<v 0>%a@]@,} else {@;<0 2>@[<v 0>%a@]@,}@]"
     pp_expr c pp_protocol co pp_protocol a *)

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
  | Set s -> Set (s |> List.map (eval_expr env))
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

let rec normalize_once p =
  match p with
  | Seq s ->
    Seq
      (s |> List.map normalize_once
      |> List.filter (function Emp -> false | _ -> true))
  | Par s ->
    Par
      (s |> List.map normalize_once
      |> List.filter (function Emp -> false | _ -> true))
  | Disj (a, b) ->
    begin
      match (a, b) with
      | (Emp, _) -> normalize_once b
      | (_, Emp) -> normalize_once a
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

let rec normalize p =
  let p1 = normalize_once p in
  if equal_protocol p p1 then
    p1
  else
    normalize p1

let rec transpose xss =
  match xss with
  | (_ :: _) :: _ -> List.map List.hd xss :: transpose (List.map List.tl xss)
  | _ -> []

let rec qualify_expr ((V (_, pn), vars) as party) e =
  match e with
  | Int _ | Bool _ -> e
  | Var (V (None, vn)) ->
    if List.mem ~eq:String.equal vn (var_names vars) then
      Var (V (Some (Party pn), vn))
    else
      fail "variable %a does not belong to %s" pp_expr e pn
  | Var (V (Some _, _)) -> e
  | Set s -> Set (List.map (qualify_expr party) s)
  | App (n, s) -> App (n, List.map (qualify_expr party) s)

(* parties is a list of (party name, vars belonging to it) *)
let project (parties : (var * var list) list) pr =
  let rec aux pr =
    match pr with
    | Emp -> parties |> List.map (fun _ -> Emp)
    | Assign (V (p1, v), e) ->
      parties
      |> List.map (fun ((V (_, pn), vars) as party) ->
             match p1 with
             | Some (Party p1) when String.equal pn p1 ->
               (* given *)
               Assign (V (Some (Party p1), v), qualify_expr party e)
             | None when List.mem ~eq:String.equal v (var_names vars) ->
               (* inferred *)
               Assign (V (Some (Party pn), v), qualify_expr party e)
             | _ -> Emp)
    | Seq ps -> ps |> List.map aux |> transpose |> List.map (fun p -> Seq p)
    | Par ps -> ps |> List.map aux |> transpose |> List.map (fun p -> Par p)
    | Disj (a, b) ->
      [a; b] |> List.map aux |> transpose
      |> List.map (function [a; b] -> Disj (a, b) | _ -> failwith "invalid")
    | Send { from; to_; msg } ->
      let (V (_, fr)) = from in
      let (V (_, to1)) = to_ in
      parties
      |> List.map (fun (V (_, pn), _) ->
             if String.equal pn fr then
               SendOnly { from; to_; msg }
             else if String.equal pn to1 then
               ReceiveOnly { from; to_; msg }
             else
               Emp)
    | Imply (c, body) ->
      List.map2
        (fun par body1 ->
          (* TODO check without exception *)
          try Imply (qualify_expr par c, body1)
          with Eval_failure _ ->
            (* note that this is the body of the conditional, not emp *)
            body1)
        parties (aux body)
    | BlockingImply (c, p) ->
      List.map2
        (fun par p1 ->
          try BlockingImply (qualify_expr par c, p1)
          with Eval_failure _ -> Emp)
        parties (aux p)
    | Forall (v, s, p) -> aux p |> List.map (fun p1 -> Forall (v, s, p1))
    | Exists (v, s, p) -> aux p |> List.map (fun p1 -> Exists (v, s, p1))
    | SendOnly _ -> fail "invalid send only"
    | ReceiveOnly _ -> fail "invalid receive only"
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
  in
  aux p

(* | _ -> parties |> List.map (fun _ -> pr) *)

(* fail "nyi" *)

(* let eval p =
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
  with Eval_failure s -> Format.printf "evaluation failed: %s@." s *)

module Tpc = struct
  (* let coord = Party "coordinator" *)

  (* let part = Party "participant" *)

  let coord = V (None, "C")

  let part = V (None, "P")

  let p = V (None, "p")

  let c = V (None, "c")

  let responded = V (None, "responded")

  let aborted = V (None, "aborted")

  let protocol =
    Seq
      [
        Forall
          ( p,
            part,
            Seq
              [
                Send { from = c; to_ = p; msg = msg "prepare" };
                Disj
                  ( Seq
                      [
                        Send { from = p; to_ = c; msg = msg "prepared" };
                        Assign (responded, plus (Var responded) (Set [Var p]));
                      ],
                    Seq
                      [
                        Send { from = p; to_ = c; msg = msg "abort" };
                        Assign (aborted, plus (Var aborted) (Set [Var p]));
                      ] );
              ] );
        Disj
          ( BlockingImply
              ( eq (Var aborted) (Set []),
                Forall
                  ( p,
                    part,
                    Seq
                      [
                        Send { from = c; to_ = p; msg = msg "commit" };
                        Send { from = p; to_ = c; msg = msg "commit_ack" };
                      ] ) ),
            Forall
              ( p,
                part,
                Seq
                  [
                    Send { from = c; to_ = p; msg = msg "abort" };
                    Send { from = p; to_ = c; msg = msg "abort_ack" };
                  ] ) );
      ]
end

module Test = struct
  let responded = V (None, "responded")

  let p = V (None, "p")

  let _protocol =
    Seq
      [
        Assign (responded, plus (Var responded) (Set [Var p]));
        Assign (responded, plus (Var responded) (Set [Var p]));
      ]
end

(* module Paxos = struct
  let proposer = Party "proposer"

  let acceptor = Party "acceptor"

  let protocol = Seq [Assign (proposer >. "count", Int 0)]
end
*)

module Paxos = struct
  (* let coord = Party "coordinator" *)

  (* let part = Party "participant" *)

  let proposers = V (None, "P")

  let acceptors = V (None, "A")

  let p = V (None, "p")

  let a = V (None, "a")

  let a1 = V (None, "a1")

  (* current proposal number of proposer *)
  let proposal = V (None, "proposal")

  let value = V (None, "value")

  let majority = V (None, "majority")

  let prepare_responses = V (None, "prepare_responses")

  (* acceptor *)
  let already_responded = V (None, "already_responded")

  let current_proposal = V (None, "current_proposal")

  let current_value = V (None, "current_value")

  (* messages *)
  let n = V (None, "n")

  let cv = V (None, "cv")

  let cp = V (None, "cp")

  let pn = V (None, "pn")

  let pv = V (None, "pv")

  let protocol =
    Exists
      ( p,
        proposers,
        Seq
          [
            Assign (proposal, plus (Var proposal) (Int 1));
            Assign (value, App ("external", []));
            Assign
              ( majority,
                plus (App ("/", [App ("size", [Var acceptors]); Int 2])) (Int 1)
              ); Assign (prepare_responses, Set []);
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
                            { typ = "propose"; args = [(n, Var proposal)] };
                      };
                    Imply
                      ( ge (Var n) (Var already_responded),
                        Seq
                          [
                            Assign (already_responded, Var n);
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
                                          (cp, Var current_proposal);
                                          (cv, Var current_value);
                                        ];
                                    };
                              };
                            Imply
                              ( ge (Var cp) (Int 0),
                                Seq
                                  [
                                    Assign (value, Var cv);
                                    Assign
                                      ( prepare_responses,
                                        plus (Var prepare_responses)
                                          (Set [Var a]) );
                                    Imply
                                      ( ge (Var cp) (Var proposal),
                                        Assign (proposal, Var cp) );
                                  ] );
                          ] );
                  ] );
            BlockingImply
              ( ge (App ("size", [Var prepare_responses])) (Var majority),
                Forall
                  ( a1,
                    prepare_responses,
                    Seq
                      [
                        Send
                          {
                            from = p;
                            to_ = a1;
                            msg =
                              Message
                                {
                                  typ = "accept";
                                  args = [(pn, Var proposal); (pv, Var value)];
                                };
                          };
                        Imply
                          ( geq (Var pn) (Var already_responded),
                            Send { from = a1; to_ = p; msg = msg "accepted" } );
                      ] ) );
          ] )
end

let snapshot_protocol parties pr =
  let projections =
    let res = project parties pr in
    List.map2
      (fun (V (_, p), _) r ->
        let init =
          match has_initiative (V (None, p)) r with
          | true -> "has"
          | false -> "does not have"
        in
        Format.sprintf "projection of %s@.%s %s initiative@.@.%a" p p init
          pp_protocol r)
      parties res
    |> String.concat "\n--\n"
  in
  Format.printf "protocol:@.@.%a@.---@.projections:@.@.%s@." pp_protocol pr
    projections

let%expect_test "2pc" =
  let parties = Tpc.[(c, [responded; aborted; p]); (p, [c])] in
  snapshot_protocol parties Tpc.protocol;
  [%expect
    {|
    protocol:

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

    projection of c
    c has initiative
    (forall p:P.
       (*c->p: prepare;
        (p->c*: prepared;
         c.responded = c.responded + {c.p})
        \/
        (p->c*: abort;
         c.aborted = c.aborted + {c.p}));
     c.aborted == {} =>*
       forall p:P.
         (*c->p: commit;
          p->c*: commit_ack)
     \/
     forall p:P.
       (*c->p: abort;
        p->c*: abort_ack))
    --
    projection of p
    p does not have initiative
    (forall p:P.
       (c->p*: prepare;
        (*p->c: prepared)
        \/
        (*p->c: abort));
     forall p:P.
       (c->p*: abort;
        *p->c: abort_ack))
  |}]

let%expect_test "2pc" =
  let msg = Paxos.[n; cv; cp; pn; pv] in
  let parties =
    Paxos.
      [
        ( p,
          msg @ [acceptors; proposal; value; majority; prepare_responses; a; a1]
        ); (a, msg @ [already_responded; current_proposal; current_value; p]);
        (a1, msg @ [already_responded; current_proposal; current_value; p]);
      ]
  in
  snapshot_protocol parties Paxos.protocol;
  [%expect {|
  |}]
