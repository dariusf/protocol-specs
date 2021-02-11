open Containers

type party = Party of string [@@deriving ord, eq]

let pp_party fmt (Party p) = Format.fprintf fmt "%s" p

type var = V of party option * string [@@deriving ord, eq]

let pp_var fmt (V (p, var)) =
  match p with
  | Some p -> Format.fprintf fmt "%a.%s" pp_party p var
  | None -> Format.fprintf fmt "%s" var

let var s = V (None, s)

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
[@@deriving eq]

type msg_destruct =
  | MessageD of {
      typ : string;
      args : var list;
    }
[@@deriving eq]

type msg_construct =
  | MessageC of {
      typ : string;
      args : expr list;
    }
[@@deriving eq]

let msg name = Message { typ = name; args = [] }

let msg_destruct (Message { typ; args }) =
  MessageD { typ; args = List.map fst args }

let msg_construct (Message { typ; args }) =
  MessageC { typ; args = List.map snd args }

let pp_msg fmt (Message { typ; args }) =
  Format.fprintf fmt "%s%s" typ
    (match args with
    | [] -> ""
    | _ ->
      args
      |> List.map (fun (k, v) -> Format.sprintf "%a: %a" pp_var k pp_expr v)
      |> String.concat ", "
      |> fun a -> "(" ^ a ^ ")")

let pp_msg_construct fmt (MessageC { typ; args }) =
  Format.fprintf fmt "%s%s" typ
    (match args with
    | [] -> ""
    | _ ->
      args
      |> List.map (fun v -> Format.sprintf "%a" pp_expr v)
      |> String.concat ", "
      |> fun a -> "(" ^ a ^ ")")

let pp_msg_destruct fmt (MessageD { typ; args }) =
  Format.fprintf fmt "%s%s" typ
    (match args with
    | [] -> ""
    | _ ->
      args
      |> List.map (fun k -> Format.sprintf "%a" pp_var k)
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
  (* TODO use bindlib? *)
  | Forall of var * var * protocol
  | Exists of var * var * protocol
  (* extras *)
  | SendOnly of {
      from : var;
      to_ : var;
      msg : msg_construct;
    }
  | ReceiveOnly of {
      from : var;
      to_ : var;
      msg : msg_destruct;
    }
  (* cst *)
  | Comment of var option * string * protocol
(* cst would have parens too *)
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
    fprintf fmt "@[<v 0>forall %a:%a.@;<0 2>@[%a@]@]" pp_var v pp_var s
      pp_protocol p
  | Exists (v, s, p) ->
    fprintf fmt "@[<v 0>exists %a:%a.@;<0 2>@[%a@]@]" pp_var v pp_var s
      pp_protocol p
  | Comment (_, s, p) -> fprintf fmt "@[<v 0>// %s@,%a@]" s pp_protocol p

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
  let useful = function Emp | Seq [] -> false | _ -> true in
  match p with
  | Seq s -> Seq (s |> List.map normalize_once |> List.filter useful)
  | Par s -> Par (s |> List.map normalize_once |> List.filter useful)
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
  | Comment _ -> p

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

(* module SMap = struct
  include Map.Make (struct
    type t = string

    let compare = String.compare
  end)
end *)

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

type env = { parties : party_info list }

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

let rec vars_in e =
  match e with
  | Int _ | Bool _ -> []
  | Var v -> [v]
  | App (_, s) | Set s -> List.concat_map vars_in s

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
    }

  let protocol =
    Seq
      [
        Forall
          ( p,
            participants,
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
  let proposers = var "P"

  let acceptors = var "A"

  let p = var "p"

  let a = var "a"

  let a1 = var "a1"

  (* current proposal number of proposer *)
  let proposal = var "proposal"

  let value = var "value"

  let majority = var "majority"

  let prepare_responses = var "prepare_responses"

  (* acceptor *)
  let highest_proposal = var "highest_proposal"

  let current_proposal = var "current_proposal"

  let current_value = var "current_value"

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
              [a] @ [proposal; value; majority; prepare_responses] @ [cp; cv];
          };
          {
            repr = acceptors;
            other_sets = [prepare_responses];
            vars = [a; a1];
            owned_vars =
              [p]
              @ [highest_proposal; current_proposal; current_value]
              @ [n; pn; pv];
          };
        ];
    }

  let protocol =
    Comment
      ( None,
        "these are all the proposers who are currently competing",
        Forall
          ( p,
            proposers,
            Seq
              [
                Assign (proposal, plus (Var proposal) (Int 1));
                Assign (value, App ("external", []));
                Assign
                  ( majority,
                    plus
                      (App ("/", [App ("size", [Var acceptors]); Int 2]))
                      (Int 1) ); Assign (prepare_responses, Set []);
                Comment
                  ( Some acceptors,
                    "disappears on the acceptor's side",
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
                                      typ = "propose";
                                      args = [(n, Var proposal)];
                                    };
                              };
                            Imply
                              ( ge (Var n) (Var highest_proposal),
                                Seq
                                  [
                                    Assign (highest_proposal, Var n);
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
                                    Assign
                                      ( prepare_responses,
                                        plus (Var prepare_responses)
                                          (Set [Var a]) );
                                    Imply
                                      ( ge (Var cp) (Int 0),
                                        Seq
                                          [
                                            Assign (value, Var cv);
                                            Imply
                                              ( ge (Var cp) (Var proposal),
                                                Assign (proposal, Var cp) );
                                          ] );
                                  ] );
                          ] ) );
                Comment
                  ( Some acceptors,
                    "could have more concurrency",
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
                                          args =
                                            [
                                              (pn, Var proposal); (pv, Var value);
                                            ];
                                        };
                                  };
                                Imply
                                  ( geq (Var pn) (Var highest_proposal),
                                    Send
                                      {
                                        from = a1;
                                        to_ = p;
                                        msg = msg "accepted";
                                      } );
                              ] ) ) );
              ] ) )
end

let snapshot_protocol env pr =
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
  Format.printf "protocol:@.@.%a@.---@.projections:@.@.%s@." pp_protocol pr
    projections

let%expect_test "2pc" =
  snapshot_protocol Tpc.env Tpc.protocol;
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

    ((c->self*: prepare;
      (*self->c: prepared)
      \/
      (*self->c: abort));
     (c->self*: commit;
      *self->c: commit_ack)
     \/
     (c->self*: abort;
      *self->c: abort_ack))
  |}]

let%expect_test "2pc" =
  snapshot_protocol Paxos.env Paxos.protocol;
  [%expect {|
    protocol:

    // these are all the proposers who are currently competing
    forall p:P.
      (proposal = proposal + 1;
       value = external();
       majority = size(A) / 2 + 1;
       prepare_responses = {};
       // disappears on the acceptor's side
       forall a:A.
         (p->a: propose(n: proposal);
          n > highest_proposal =>
            (highest_proposal = n;
             a->p: promise(cp: current_proposal, cv: current_value);
             prepare_responses = prepare_responses + {a};
             cp > 0 =>
               (value = cv;
                cp > proposal =>
                  proposal = cp)));
       // could have more concurrency
       size(prepare_responses) > majority =>*
         forall a1:prepare_responses.
           (p->a1: accept(pn: proposal, pv: value);
            pn >= highest_proposal =>
              a1->p: accepted))
    ---
    projections:

    projection of P
    P has initiative

    (proposal = proposal + 1;
     value = external();
     majority = size(A) / 2 + 1;
     prepare_responses = {};
     forall a:A.
       (*self->a: propose(proposal);
        (a->self*: promise(cp, cv);
         prepare_responses = prepare_responses + {a};
         cp > 0 =>
           (value = cv;
            cp > proposal =>
              proposal = cp)));
     size(prepare_responses) > majority =>*
       forall a1:prepare_responses.
         (*self->a1: accept(proposal, value);
          a1->self*: accepted))
    --
    projection of A
    A does not have initiative

    forall p:P.
      (// disappears on the acceptor's side
       (p->self*: propose(n);
        n > highest_proposal =>
          (highest_proposal = n;
           *self->p: promise(current_proposal, current_value);
           emp;
           (emp;
            emp)));
       // could have more concurrency
       (p->self*: accept(pn, pv);
        pn >= highest_proposal =>
          *self->p: accepted))
  |}]
