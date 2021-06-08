open Ast
open Containers
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
let rec project_aux :
    party_info list -> env -> tprotocol -> (tprotocol * tprotocol list) list =
 fun parties env pr ->
  let p2 =
    match pr.p with
    | Emp -> parties |> List.map (fun _ -> (Emp, []))
    | Assign (v, _e) ->
      parties
      |> List.map (fun party ->
             if owned_by parties party v then
               (pr.p, [])
             (* Assign
                ( { v with expr = Var (V (None, var_name (must_be_var_t v))) },
                  e ) *)
             else
               (Emp, []))
    | Send { from; to_; msg } ->
      (* drop the party qualifiers *)
      parties
      |> List.map (fun party ->
             if is_party parties env party from then
               ( SendOnly
                   {
                     from = { from with expr = Var (V (None, "self")) };
                     to_;
                     msg;
                   },
                 [] )
             else if is_party parties env party to_ then
               ( ReceiveOnly
                   {
                     from;
                     to_ = { to_ with expr = Var (V (None, "self")) };
                     msg = msg_destruct msg;
                   },
                 [] )
             else
               (Emp, []))
    | Imply (c, body) ->
      List.map2
        (fun party (body1, ps) ->
          if List.for_all (owned_by parties party) (vars_in c) then
            (Imply (c, body1), ps)
          else (* note that this is the body of the conditional, not emp *)
            (body1.p, ps))
        parties
        (project_aux parties env body)
    | BlockingImply (c, body) ->
      List.map2
        (fun party (body1, ps) ->
          if List.for_all (owned_by parties party) (vars_in c) then
            (BlockingImply (c, body1), ps)
          else
            (body1.p, []))
        parties
        (project_aux parties env body)
    | Forall (v, s, p) ->
      List.map2
        (fun party (p1, ps) ->
          if is_party parties env party v then
            (p1.p, ps)
          else
            (Forall (v, s, p1), ps))
        parties
        (project_aux parties env p)
    | Exists _ -> nyi "project exists"
    | Seq ps ->
      ps
      |> List.map (project_aux parties env)
      |> transpose
      |> List.map (fun ps ->
             let (seq, side) =
               List.fold_right
                 (fun (p, ps) (p1, ps1) -> (p :: p1, ps @ ps1))
                 ps ([], [])
             in
             (Seq seq, side))
    | Par ps ->
      ps
      |> List.map (project_aux parties env)
      |> transpose
      |> List.map (fun ps ->
             let par =
               List.fold_right (fun (p, ps) ps1 -> p :: ps @ ps1) ps []
             in
             (Par par, []))
    | Disj (a, b) ->
      [a; b]
      |> List.map (project_aux parties env)
      |> transpose
      |> List.map (fun ps ->
             let[@warning "-8"] ([a; b], side) =
               List.fold_right
                 (fun (p, ps) (p1, ps1) -> (p :: p1, ps @ ps1))
                 ps ([], [])
             in
             (Disj (a, b), side))
    | SendOnly _ -> bug "send only should not be used in front end language"
    | ReceiveOnly _ ->
      bug "receive only should not be used in front end language"
    | Comment _ -> bug "comment should not be used in front end language"
  in
  (* TODO check if this places the metadata somewhere weird *)
  p2 |> List.map (fun (p, ps) -> ({ pr with p }, ps))

let project parties env p =
  let ps = project_aux parties env p in
  let dummy_loc =
    { start = { line = -1; col = -1 }; stop = { line = -1; col = -1 } }
  in
  List.map
    (fun (p, ps) ->
      normalize_t { p = Par (p :: ps); pmeta = pmeta ~loc:dummy_loc () })
    ps
