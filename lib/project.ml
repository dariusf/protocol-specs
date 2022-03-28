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

let substitute ~v ~by (p : tprotocol) : tprotocol =
  let vp =
    object
      inherit [_] map_protocol

      method! visit_var _env (V (p, v1)) =
        let (p : party option) =
          match p with
          | Some (Party p1) when String.equal p1 v -> Some (Party by)
          | _ -> p
        in
        let v1 = if String.equal v1 v then by else v1 in
        V (p, v1)

      (* don't change message fields *)
      method! visit_msg ve _vv env (Message { typ; args }) =
        Message { typ; args = List.map (fun (k, v) -> (k, ve env v)) args }

      method! visit_msg_destruct _vv _env m = m
    end
  in
  vp#visit__protocol () p

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
            let right = project_protocol party env body in
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
  let vp =
    object
      inherit [_] map_protocol
      method! visit_var _env (V (_, v)) = V (None, v)
    end
  in
  vp#visit__protocol () e

let project parties env p =
  parties
  |> List.map (fun party ->
         project_protocol (party.repr |> var_name) env p
         |> strip_qualifiers |> normalize_t)
