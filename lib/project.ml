open Ast
open Common
open Containers
open Normalize
open Infer.Cast
(* module Tracing = Ppx_debug.Tracing *)

let owned_by env party v =
  match v.meta.info.own with
  | Global -> true
  | Party w ->
    String.equal party ((IMap.find (UF.value w) env.parties).repr |> var_name)

let rec vars_in e =
  match e.expr with
  | Int _ | Bool _ | String _ -> []
  | Var _ -> [e]
  | App (_, s) | Set s | List s -> List.concat_map vars_in s
  | Map s -> List.concat_map vars_in (List.map snd s)
  | Tuple (a, b) -> List.concat_map vars_in [a; b]
  | Else | Timeout -> nyi "else/timeout"

let substitute_expr ~v ~by e =
  let rec aux e =
    match e.expr with
    | Int _ | Bool _ | String _ -> e
    | Var (V (p, v1)) ->
      let (p : party option) =
        match p with
        | Some (Party p1) when String.equal p1 v -> Some (Party by)
        | _ -> p
      in
      let v1 = if String.equal v1 v then by else v1 in
      { e with expr = Var (V (p, v1)) }
    | App (f, args) -> { e with expr = App (f, List.map aux args) }
    | Set s -> { e with expr = Set (List.map aux s) }
    | List s -> { e with expr = List (List.map aux s) }
    | Map s -> { e with expr = Map (List.map (fun (k, v) -> (k, aux v)) s) }
    | Tuple (a, b) -> { e with expr = Tuple (aux a, aux b) }
    | Else | Timeout -> nyi "else/timeout"
  in
  aux e

let substitute ~v ~by p =
  let rec aux p =
    match p.p with
    | Send { from; to_; msg = Message { typ; args } } ->
      {
        p with
        p =
          Send
            {
              from = substitute_expr ~v ~by from;
              to_ = substitute_expr ~v ~by to_;
              msg =
                Message
                  {
                    typ;
                    args =
                      List.map
                        (fun (va, e) -> (va, substitute_expr ~v ~by e))
                        args;
                  };
            };
      }
    | SendOnly { to_; msg = Message { typ; args } } ->
      {
        p with
        p =
          SendOnly
            {
              to_ = substitute_expr ~v ~by to_;
              msg =
                Message
                  {
                    typ;
                    args =
                      List.map
                        (fun (va, e) -> (va, substitute_expr ~v ~by e))
                        args;
                  };
            };
      }
    | ReceiveOnly { from; msg } ->
      { p with p = ReceiveOnly { from = substitute_expr ~v ~by from; msg } }
    | Emp -> { p with p = Emp }
    | Seq ps -> { p with p = Seq (List.map aux ps) }
    | Par ps -> { p with p = Par (List.map aux ps) }
    | Forall (va, s, b) ->
      {
        p with
        p = Forall (substitute_expr ~v ~by va, substitute_expr ~v ~by s, aux b);
      }
    | Disj (a, b) -> { p with p = Disj (aux a, aux b) }
    | Assign (va, e) ->
      {
        p with
        p = Assign (substitute_expr ~v ~by va, substitute_expr ~v ~by e);
      }
    | Call { f; args } ->
      { p with p = Call { f; args = List.map (substitute_expr ~v ~by) args } }
    | Imply (e, b) -> { p with p = Imply (substitute_expr ~v ~by e, aux b) }
    | BlockingImply (e, b) ->
      { p with p = BlockingImply (substitute_expr ~v ~by e, aux b) }
    | Exists (_, _, _) -> nyi "substitute Exists"
    | Comment (_, _, _) -> nyi "substitute Comment"
  in
  aux p

let remove_call (e : tprotocol) : tprotocol =
  let vp =
    object
      inherit [_] map_protocol

      method! visit__protocol _env p =
        match p.p with Call _ -> { p with p = Emp } | _ -> p
    end
  in
  vp#visit__protocol () e

(** Given the environment (which knows about all the parties),
    and a protocol to project, returns a list of protocols projected
    by each party *)
let rec project_protocol : string -> env -> tprotocol -> tprotocol =
 fun party env pr ->
  match pr.p with
  | Emp -> { pr with p = Emp }
  | Assign (v, _) ->
    (* we also have to look at these, as they are mandatory when dealing with self-sends *)
    let qualifier_bound =
      let (V (p, _)) = must_be_var_t v in
      match p with None | Some (Party "self") -> true | _ -> false
    in
    let p = if owned_by env party v && qualifier_bound then pr.p else Emp in
    { pr with p }
  | Send { from; to_; msg } ->
    let f = from |> must_be_var_t |> var_name in
    let t = to_ |> must_be_var_t |> var_name in
    let p =
      if String.equal f "self" && String.equal t "self" then
        Seq
          [
            { pr with p = SendOnly { to_; msg } };
            { pr with p = ReceiveOnly { from; msg = msg_destruct msg } };
          ]
      else if String.equal f "self" then SendOnly { to_; msg }
      else if String.equal t "self" then
        ReceiveOnly { from; msg = msg_destruct msg }
      else Emp
    in
    { pr with p }
  | Call _ ->
    let p = if true then pr.p else Emp in
    { pr with p }
  | Imply (c, body) ->
    let body1 = project_protocol party env body in
    let p =
      if List.for_all (owned_by env party) (vars_in c) then Imply (c, body1)
      else (* note that this is the body of the conditional, not emp *)
        body1.p
    in
    { pr with p }
  | BlockingImply (c, body) ->
    let body1 = project_protocol party env body in
    let p =
      if List.for_all (owned_by env party) (vars_in c) then
        BlockingImply (c, body1)
      else body1.p
    in
    { pr with p }
  | Forall (v, s, body) ->
    let name = v |> must_be_var_t |> var_name in
    let typ, sname, less = as_party_set_or_less env s in
    let p =
      if String.equal party typ then
        (* related. there are now two cases *)
        let c =
          let is_related = not (List.mem ~eq:String.equal "self" less) in
          if is_related then
            let left =
              project_protocol party env (substitute ~v:name ~by:"self" body)
            in
            let right = project_protocol party env (remove_call body) in
            let set_minus_self =
              App
                ( "\\",
                  (* this changes metadata but shouldn't matter *)
                  [
                    { s with expr = Var (var sname) };
                    {
                      s with
                      expr =
                        Set
                          (List.map
                             (fun v -> { s with expr = Var (V (None, v)) })
                             ("self" :: less));
                    };
                  ] )
            in
            (* this always generates two branches, but the operations across self and others in the set are disjoint if they only occur on one side (assignment, call). normalization then removes one of the branches *)
            let self_send =
              Par
                [
                  left;
                  {
                    pr with
                    p = Forall (v, { s with expr = set_minus_self }, right);
                  };
                ]
            in
            self_send
          else Forall (v, s, project_protocol party env body)
        in
        c
      else
        (* unrelated. just go deeper and don't bind, or "act homomorphically through quantification on different role" *)
        Forall (v, s, project_protocol party env body)
    in
    { pr with p }
  | Seq ps -> { pr with p = Seq (ps |> List.map (project_protocol party env)) }
  | Par ps -> { pr with p = Par (ps |> List.map (project_protocol party env)) }
  | Disj (a, b) ->
    let pa = project_protocol party env a in
    let pb = project_protocol party env b in
    { pr with p = Disj (pa, pb) }
  | Exists _ -> nyi "project aux exists"
  | SendOnly _ -> bug "send only should not be used in front end language"
  | ReceiveOnly _ -> bug "receive only should not be used in front end language"
  | Comment _ -> bug "invalid comment"

let strip_qualifiers (e : tprotocol) : tprotocol =
  let ve =
    object
      inherit [_] map_expr
      method! visit_var _env (V (_, v)) = V (None, v)
    end
  in
  let expr e = ve#visit__expr () e in
  let vp =
    object
      inherit [_] map_protocol
      method! visit_'e _env m = expr m
      method! visit_'v _env m = expr m
    end
  in
  vp#visit__protocol () e

let project parties env p =
  parties
  |> List.map (fun party ->
         project_protocol (party.repr |> var_name) env p
         |> strip_qualifiers |> normalize_t)
