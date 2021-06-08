open Ast
open Common
open Normalize

let owned_by parties party v =
  match v.meta.info.own with
  | Global -> true
  | Party w -> equal_party_info party (List.nth parties (UF.value w))

let is_party parties env party (v : texpr) =
  match Infer.concretize env v.meta.info.typ with
  | TyParty p -> equal_party_info party (List.nth parties (UF.value p))
  | t -> fail ~loc:v.meta.loc "got a %a, expected a party" (Print.pp_typ ~env) t

let rec vars_in e =
  match e.expr with
  | Int _ | Bool _ -> []
  | Var _ -> [e]
  | App (_, s) | Set s | List s -> List.concat_map vars_in s
  | Map s -> List.concat_map vars_in (List.map snd s)
  | Tuple (a, b) -> List.concat_map vars_in [a; b]

(** Given the environment (which knows about all the parties),
    and a protocol to project, returns a list of protocols projected
    by each party *)
let rec project_aux : party_info list -> env -> tprotocol -> tprotocol list =
 fun parties env pr ->
  let p2 =
    match pr.p with
    | Emp -> parties |> List.map (fun _ -> Emp)
    | Assign (v, e) ->
      parties
      |> List.map (fun party ->
             if owned_by parties party v then (* drop the party qualifiers *)
               Assign
                 ( { v with expr = Var (V (None, var_name (must_be_var_t v))) },
                   e )
             else
               Emp)
    | Send { from; to_; msg } ->
      parties
      |> List.map (fun party ->
             if is_party parties env party from then
               SendOnly
                 {
                   from = { from with expr = Var (V (None, "self")) };
                   to_;
                   msg;
                 }
             else if is_party parties env party to_ then
               ReceiveOnly
                 {
                   from;
                   to_ = { to_ with expr = Var (V (None, "self")) };
                   msg = msg_destruct msg;
                 }
             else
               Emp)
    | Imply (c, body) ->
      List.map2
        (fun party body1 ->
          if List.for_all (owned_by parties party) (vars_in c) then
            Imply (c, body1)
          else (* note that this is the body of the conditional, not emp *)
            body1.p)
        parties
        (project_aux parties env body)
    | BlockingImply (c, body) ->
      List.map2
        (fun party body1 ->
          if List.for_all (owned_by parties party) (vars_in c) then
            BlockingImply (c, body1)
          else
            body1.p)
        parties
        (project_aux parties env body)
    | Forall (v, s, p) ->
      List.map2
        (fun party p1 ->
          if is_party parties env party v then
            p1.p
          else
            Forall (v, s, p1))
        parties
        (project_aux parties env p)
    | Exists (v, s, p) ->
      List.map2
        (fun party p1 ->
          if is_party parties env party v then
            p1.p
          else
            Exists (v, s, p1))
        parties
        (project_aux parties env p)
    | Seq ps ->
      ps
      |> List.map (project_aux parties env)
      |> transpose
      |> List.map (fun p -> Seq p)
    | Par ps ->
      ps
      |> List.map (project_aux parties env)
      |> transpose
      |> List.map (fun p -> Par p)
    | Disj (a, b) ->
      [a; b]
      |> List.map (project_aux parties env)
      |> transpose
      |> List.map (function [a; b] -> Disj (a, b) | _ -> failwith "invalid")
    | SendOnly _ -> bug "send only should not be used in front end language"
    | ReceiveOnly _ ->
      bug "receive only should not be used in front end language"
    | Comment (party, s, p) ->
      List.map2
        (fun party1 p1 ->
          match party with
          | None -> p1.p
          | Some party2 ->
            if equal_var party2 party1.repr then
              Comment (party, s, p1)
            else
              p1.p)
        parties
        (project_aux parties env p)
  in
  (* check if this places the metadata somewhere weird *)
  p2 |> List.map (fun p -> { pr with p })

let project parties env p = project_aux parties env p |> List.map normalize_t
