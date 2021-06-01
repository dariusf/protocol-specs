open Containers
open Common
open Ast

let parse_parties s =
  s |> String.split ~by:"," |> List.map (fun repr -> { repr = var repr })

let read project_party parties file =
  let spec = Infer.parse_spec file in
  let protocol =
    spec.protocol
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
    `Typed (spec, parties, env, tprotocol, all)

let print project_party parties ast types actions file =
  match read project_party parties file with
  | `Untyped protocol ->
    if ast then
      protocol |> show_protocol |> print_endline
    else
      protocol |> Print.render_protocol
      |> PPrint.ToChannel.pretty 0.8 120 stdout
  | `Typed (_, _, env, tprotocol, _) ->
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
  let spec_name = Filename.remove_extension file in
  match project_party with
  | None ->
    (* TODO fix unintuitiveness *)
    bad_input "use --project to say which party's spec to generate"
  | Some project_party ->
  match read (Some project_party) parties file with
  | `Untyped _ -> bad_input "--parties must be given to infer types"
  | `Typed (_, parties, env, _, tps) ->
    let tps = Option.get_exn_or "inconsistent args" tps in

    let actions =
      List.map
        (fun p ->
          let (graph, nodes) = Actions.split_into_actions p in
          (graph, nodes, p))
        tps
    in

    let tla = Tla.to_tla parties env actions |> Tla.Render.render_tla in
    Tla.with_preamble spec_name tla |> print_endline

let tla project_party parties file =
  try tla project_party parties file
  with Check_failure s -> Format.printf "%s@." s

let monitor project_party parties file =
  let spec_name = Filename.remove_extension file in
  match project_party with
  | None ->
    bad_input "use --project to say which party to generate a monitor for"
  | Some project_party ->
  match parties with
  | None -> bad_input "--parties must be given to infer types"
  | Some parties ->
    let spec = Infer.parse_spec file in
    let protocol =
      spec.protocol
      |> (* if no_normalize then Fun.id else *)
      Normalize.normalize
    in

    let parties = parse_parties parties in
    let env = Infer.initial_env parties in

    (* infer type for protocol *)
    let (tp, env) = Infer.infer_parties protocol env in
    Infer.check_instantiated env tp;

    (* project *)
    let projected = Project.project parties env tp in
    let get_party_protocol name =
      match
        List.find_idx (fun pr -> String.equal (var_name pr.repr) name) parties
      with
      | None -> bad_input "could not find such a party"
      | Some (i, _) -> List.nth projected i
    in

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
        let pr = get_party_protocol pname in
        let (action_graph, action_nodes) = Actions.split_into_actions pr in
        Ltl_go.translate_party_ltl env i (pname, ltl) pr action_graph
          action_nodes
          (List.map (fun p -> p.repr |> var_name) parties))
      ltl_fml

let monitor project_party parties file =
  try monitor project_party parties file
  with Check_failure s -> Format.printf "%s@." s
