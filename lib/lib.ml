open Containers
open Common
open Ast

let parse_parties s =
  s |> String.split ~by:"," |> List.map (fun repr -> { repr = var repr })

let parse_protocol = Infer.parse_protocol

let print project_party parties ast types file =
  let protocol =
    parse_protocol file
    |> (* if no_normalize then Fun.id else *)
    Normalize.normalize
  in
  match parties with
  | None ->
    if ast then
      protocol |> show_protocol |> print_endline
    else
      protocol |> Print.render_protocol
      |> PPrint.ToChannel.pretty 0.8 120 stdout
  | Some parties ->
    let parties = parse_parties parties in
    let env = Infer.initial_env parties in
    let (tp, env) = Infer.infer_parties protocol env in
    Infer.check_instantiated env tp;

    let tprotocol =
      match project_party with
      | None -> tp
      | Some p_party ->
        let projected = Project.project parties env tp in
        (match
           List.find_idx
             (fun pr -> String.equal p_party (var_name pr.repr))
             parties
         with
        | None -> failwith "could not find such a party"
        | Some (i, _) -> List.nth projected i)
    in

    if ast then
      tprotocol |> show_tprotocol |> print_endline
    else
      tprotocol
      |> (if types then
            Print.render_tprotocol ~env
         else
           Print.render_tprotocol_untyped ~env)
      |> PPrint.ToChannel.pretty 0.8 120 stdout

let print project_party parties ast types file =
  try print project_party parties ast types file
  with Check_failure s -> Format.printf "%s@." s

let infer file =
  let protocol = parse_protocol file in
  let env =
    Infer.initial_env [{ repr = V (None, "C") }; { repr = V (None, "P") }]
  in
  try
    let (tp, env) = Infer.infer_parties protocol env in
    env |> Infer.explain_env |> print_endline;
    tp |> Print.render_tprotocol ~env |> PPrint.ToChannel.pretty 0.8 120 stdout;
    print_endline "";
    print_endline "---"
  with Check_failure s -> Format.printf "%s@." s
