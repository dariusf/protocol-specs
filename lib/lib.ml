open Containers
open Common
open Ast

let parse_parties s =
  s |> String.split ~by:"," |> List.map (fun repr -> { repr = var repr })

let read project_party parties file =
  let protocol =
    Infer.parse_protocol file
    |> (* if no_normalize then Fun.id else *)
    Normalize.normalize
  in
  match parties with
  | None -> `Untyped protocol
  | Some parties ->
    let parties = parse_parties parties in
    let env = Infer.initial_env parties in
    let (tp, env) = Infer.infer_parties protocol env in
    Infer.check_instantiated env tp;

    let (tprotocol, all) =
      match project_party with
      | None -> (tp, None)
      | Some p_party ->
        let projected = Project.project parties env tp in
        (match
           List.find_idx
             (fun pr -> String.equal p_party (var_name pr.repr))
             parties
         with
        | None -> bad_input "could not find such a party"
        | Some (i, _) -> (List.nth projected i, Some projected))
    in
    `Typed (parties, env, tprotocol, all)

let print project_party parties ast types actions file =
  match read project_party parties file with
  | `Untyped protocol ->
    if ast then
      protocol |> show_protocol |> print_endline
    else
      protocol |> Print.render_protocol
      |> PPrint.ToChannel.pretty 0.8 120 stdout
  | `Typed (_, env, tprotocol, _) ->
    if ast then
      tprotocol |> show_tprotocol |> print_endline
    else if actions then
      let (g, nodes) = Actions.split_into_actions tprotocol in
      print_endline (Actions.to_graphviz env g nodes)
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
  match project_party with
  | None ->
    (* TODO fix unintuitiveness *)
    bad_input "use --project to say which party's spec to generate"
  | Some project_party ->
  match read (Some project_party) parties file with
  | `Untyped _ -> bad_input "--parties must be given to infer types"
  | `Typed (parties, env, _, tps) ->
    let tps = Option.get_exn_or "inconsistent args" tps in

    let actions =
      List.map
        (fun p ->
          let (graph, nodes) = Actions.split_into_actions p in
          (graph, nodes, p))
        tps
    in

    (* let (graph, nodes) = Actions.find_actions tprotocol in *)
    let tla = Tla.to_tla parties env actions |> Tla.Render.render_tla in
    Tla.with_preamble "spec" tla |> print_endline

let tla project_party parties file =
  try tla project_party parties file
  with Check_failure s -> Format.printf "%s@." s
