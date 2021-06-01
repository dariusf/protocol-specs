open Containers
open Common
open Ast

let parse_parties s =
  s |> String.split ~by:"," |> List.map (fun repr -> { repr = var repr })

let parse file =
  let spec = Infer.parse_spec file in
  {
    spec with
    protocol =
      spec.protocol
      |> (* if no_normalize then Fun.id else *)
      Normalize.normalize;
  }

let require_parties p =
  match Option.map parse_parties p with
  | None | Some [] -> bad_input "--parties must be given to infer types"
  | Some ps -> ps

let require_project_party =
  Option.get_exn_or "a party must be chosen using --project"

let typecheck parties protocol =
  let env = Infer.initial_env parties in
  let (tp, env) = Infer.infer_parties protocol env in
  Infer.check_instantiated env tp;
  (env, tp)

let project project_party parties env tprotocol =
  let projected = Project.project parties env tprotocol in
  let map =
    List.map2 (fun party pr -> (party.repr |> var_name, pr)) parties projected
    |> SMap.of_list
  in
  let one = SMap.find project_party map in
  (one, map)

let print project_party parties ast types actions file =
  let spec = parse file in
  let protocol = spec.protocol in
  match parties with
  | None ->
    if ast then
      protocol |> show_protocol |> print_endline
    else
      protocol |> Print.render_protocol
      |> PPrint.ToChannel.pretty 0.8 120 stdout
  | _ ->
    let parties = require_parties parties in
    let (env, tprotocol) = typecheck parties protocol in
    let tprotocol =
      match project_party with
      | None -> tprotocol
      | _ ->
        let project_party = require_project_party project_party in
        project project_party parties env tprotocol |> fst
    in
    if ast then
      tprotocol |> show_tprotocol |> print_endline
    else if actions then
      let project_party = require_project_party project_party in
      let (g, nodes) = Actions.split_into_actions tprotocol in
      print_endline (Actions.to_graphviz env project_party g nodes)
    else
      tprotocol
      |> (if types then
            Print.render_tprotocol ~env
         else
           Print.render_tprotocol_untyped ~env)
      |> PPrint.ToChannel.pretty 0.8 120 stdout

let print project_party parties ast types actions file =
  try print project_party parties ast types actions file
  with Check_failure s -> Format.printf "%s@." s

let tla project_party parties file =
  let spec_name = Filename.remove_extension file in
  let project_party = require_project_party project_party in
  let parties = require_parties parties in
  let spec = parse file in
  let protocol = spec.protocol in
  let (env, tprotocol) = typecheck parties protocol in
  let (_, all) = project project_party parties env tprotocol in

  let actions =
    all
    |> SMap.mapi (fun _ p ->
           let (graph, nodes) = Actions.split_into_actions p in
           (graph, nodes, p))
  in

  let tla = Tla.to_tla env actions |> Tla.Render.render_tla in
  let tla_s = Tla.with_preamble spec_name tla in
  write_to_file ~filename:(Format.sprintf "%s.tla" spec_name) tla_s

let tla project_party parties file =
  try tla project_party parties file
  with Check_failure s -> Format.printf "%s@." s

let monitor project_party parties file =
  (* TODO is this needed? *)
  let _spec_name = Filename.remove_extension file in
  let spec = parse file in
  let protocol = spec.protocol in

  let project_party = require_project_party project_party in
  let parties = require_parties parties in

  (* infer type for protocol *)
  let (env, tprotocol) = typecheck parties protocol in

  (* project *)
  let (_, all) = project project_party parties env tprotocol in

  (* infer ltl types *)
  (* this should work because variable bindings stay in the environment after type checking is done, unlike quantified variables and local bindings, but those are never used in properties *)
  let ltl_fml =
    spec.decls |> List.filter_map (function Ltl e -> Some e | _ -> None)
  in

  (match ltl_fml with
  | [] -> print_endline "no LTL properties given, nothing to do"
  | _ -> ());

  let (ltl_fml, env) =
    List.fold_right
      (fun e (ts, env) ->
        let (te, env) = Infer.infer_parties_expr e env in
        (te :: ts, env))
      ltl_fml ([], env)
  in

  List.iter (Infer.check_instantiated_expr env) ltl_fml;
  let ltl_fml =
    ltl_fml
    |> List.map (fun l ->
           match Ltl_go.fml_ownership env l with
           | [] -> bad_input "fml ownership: no variables?"
           | [o] -> (o, l)
           | _ -> bad_input "more than one party owns this")
    |> List.group_by ~eq:(fun (a, _) (b, _) -> String.equal a b)
    |> List.map (fun s ->
           match s with
           | [] -> bug "group by empty"
           | (p, _) :: _ -> (p, List.map snd s))
  in
  List.iteri
    (fun i (pname, ltl) ->
      let pr = SMap.find pname all in
      let (action_graph, action_nodes) = Actions.split_into_actions pr in
      Ltl_go.translate_party_ltl env i (pname, ltl) pr action_graph action_nodes
        (List.map (fun p -> p.repr |> var_name) parties))
    ltl_fml

let monitor project_party parties file =
  try monitor project_party parties file
  with Check_failure s -> Format.printf "%s@." s
