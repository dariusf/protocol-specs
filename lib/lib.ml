open Containers
open Common
open Ast
module Print = Print
module Lexer = Lexer
module Parsing = Parsing
module Ast = Ast

open Log.Make (struct
  let name = "lib"
end)

let parse_grain s =
  match s with
  | None | Some "standard" -> Standard
  | Some "communication" -> Communication
  | Some "statement" -> Statement
  | _ -> failwith "invalid grain"

let parse file =
  let spec = Parsing.parse_spec file in
  { spec with protocol = spec.protocol |> Normalize.normalize }
  |> Normalize.add_preamble

let parse_string s =
  let spec = Parsing.parse_string s in
  { spec with protocol = spec.protocol |> Normalize.normalize }
  |> Normalize.add_preamble

let require_project_party p =
  Option.get_exn_or "a party must be chosen using --project" p

let project_all_parties parties env tprotocol : (tprotocol * env) SMap.t =
  (* p -> [p_a, p_b, ...] *)
  let projected = Project.project parties env tprotocol in
  match SMap.cardinal env.subprotocols with
  | 0 ->
    List.map2 (fun party p -> (var_name party.repr, (p, env))) parties projected
    |> SMap.of_list
  | _ ->
    let envs =
      (* ps -> [ [p_a_1, p_a_2, ...], [p_b_1, p_b_2, ...], ...]
         -> [[p_a_1, p_b_1, ...], [p_a_2, p_b_2, ...], ...]
      *)
      env.subprotocols |> SMap.bindings
      |> List.map (fun (_, sp) -> sp)
      |> List.map (fun sp ->
             List.map (fun pa -> (sp, pa)) (Project.project parties env sp.tp))
      |> transpose
      (* this transposing business is required because of the interface of Project.project *)
    in
    let results =
      List.map2
        (fun p e ->
          ( p,
            {
              env with
              subprotocols =
                List.map (fun (sp, p) -> (sp.fname, { sp with tp = p })) e
                |> SMap.of_list;
            } ))
        projected envs
      |> List.map2 (fun n r -> (var_name n.repr, r)) parties
      |> SMap.of_list
    in
    results

(* (*
     List.map2 (fun party pr -> (party.repr |> var_name, pr)) parties projected
     |> SMap.of_list *)
   parties |> List.map (fun party ->
     let projected = Project.project parties env tprotocol |> SMap.find party in
     let env =
       {
         env with
         subprotocols =
           env.subprotocols
           |> SMap.map (fun sub ->
                  {
                    sub with
                    tp =
                      project_all_parties parties env sub.tp
                      |> SMap.find party;
                  });
       }
     in
     ) *)

let project_one_party parties project_party tprotocol env =
  project_all_parties parties env tprotocol |> SMap.find project_party
(* let tp =
   in
   let env =
     {
       env with
       subprotocols =
         env.subprotocols
         |> SMap.map (fun sub ->
                {
                  sub with
                  tp =
                    project_all_parties parties env sub.tp
                    |> SMap.find project_party;
                });
     }
   in
   (tp, env) *)

let typecheck spec =
  (* load the initial environment *)
  let party_decls =
    spec.decls
    |> List.filter_map (function
         | SpecParty sp -> Some (sp.var, sp.set, sp.initial, sp.size)
         | _ -> None)
  in
  let env = Infer.initial_env party_decls in
  let fns =
    spec.decls
    |> List.filter_map (function
         | Function (f, args, p) -> Some (f, args, p)
         | _ -> None)
  in
  (* check all the functions *)
  let env =
    List.fold_left
      (fun env (fname, fparams, p) ->
        let env =
          List.fold_right
            (fun c env ->
              let env, v = Infer.fresh_var env c in
              { env with bindings = SMap.add c v env.bindings })
            fparams env
        in
        let tp, env = Infer.check p env in
        {
          env with
          subprotocols = SMap.add fname { fname; fparams; tp } env.subprotocols;
        })
      env fns
  in
  (* type-checked functions are returned in the env, no longer in spec *)
  let tp, env = Infer.check spec.protocol env in
  (* handle legacy code *)
  let parties =
    party_decls |> List.map (fun (_, s, _, _) -> { repr = V (None, s) })
  in
  let party_sizes =
    party_decls |> List.map (fun (_, s, _, sz) -> (s, sz)) |> SMap.of_list
  in
  (env, tp, parties, party_sizes)

let print ~project_party ~ast ~types ~actions ~latex ~grain inp =
  let spec =
    match inp with
    | `File file -> parse file
    | `String s -> Parsing.parse_string s
  in
  match actions || types || Option.is_some project_party with
  | false ->
    (* show an untyped version *)
    (* TODO functions are not printed here *)
    if ast then
      (* protocol |> show_protocol |> print_endline *)
      spec |> show_spec |> print_endline
    else
      spec.protocol
      |> Print.render_protocol ~latex
      |> PPrint.ToChannel.pretty 0.8 120 stdout
  | true ->
    (* print typed version *)
    let env, tprotocol, parties, _party_sizes = typecheck spec in
    (* if there is a party to project on, operate on its protocol from here on. also project the protocols in the environment *)
    let tprotocol, env =
      match project_party with
      | None -> (tprotocol, env)
      | Some _ ->
        let project_party = require_project_party project_party in
        project_one_party parties project_party tprotocol env
    in
    if ast then tprotocol |> show_tprotocol |> print_endline
    else if actions then
      let project_party = require_project_party project_party in
      let g, nodes =
        Actions.split_into_actions (parse_grain grain) project_party env
          tprotocol
      in
      print_endline (Actions.to_graphviz project_party g nodes)
    else (
      Print.render_functions env |> PPrint.ToChannel.pretty 0.8 120 stdout;
      tprotocol
      |> (if types then Print.render_tprotocol ~latex ~env
         else Print.render_tprotocol_untyped ~latex)
      |> PPrint.ToChannel.pretty 0.8 120 stdout;
      print_endline "")

let print ~project_party ~ast ~types ~actions ~latex ~grain file =
  try print ~project_party ~ast ~types ~actions ~latex ~grain file
  with Check_failure s -> Format.printf "%s@." s

let tla spec_name grain file =
  let spec_name =
    spec_name
    |> Option.get_or
         ~default:(file |> Filename.remove_extension |> Filename.basename)
  in
  (* let parties, party_sizes = require_parties parties in *)
  let spec = parse file in
  let env, tprotocol, parties, party_sizes = typecheck spec in
  let all = project_all_parties parties env tprotocol in

  let actions =
    all
    |> SMap.mapi (fun party (p, env) ->
           let graph, nodes =
             Actions.split_into_actions (parse_grain grain) party env p
           in
           (graph, nodes, p))
  in

  let tla, cfg = Tla.to_tla env party_sizes actions in
  let tla = Tla.Render.render_tla tla in
  let tla_s = Tla.with_preamble spec_name tla in
  write_to_file ~filename:(Format.sprintf "%s.tla" spec_name) tla_s;
  let cfg_filename = Format.sprintf "%s.cfg" spec_name in
  (* if not (Sys.file_exists cfg_filename) then *)
  write_to_file ~filename:cfg_filename cfg

let tla ~spec_name ~grain file =
  try tla spec_name grain file with Check_failure s -> Format.printf "%s@." s

let monitor grain file =
  (* TODO is this needed? *)
  let _spec_name = Filename.remove_extension file in
  let spec = parse file in

  (* infer type for protocol *)
  let env, tprotocol, parties, _party_sizes = typecheck spec in

  (* project *)
  let all = project_all_parties parties env tprotocol in

  (* infer ltl types *)
  (* this should work because variable bindings stay in the environment after type checking is done, unlike quantified variables and local bindings, but those are never used in properties *)
  let ltl_fml =
    spec.decls |> List.filter_map (function Ltl e -> Some e | _ -> None)
  in

  let ltl_fml, env =
    List.fold_right
      (fun e (ts, env) ->
        let te, env = Infer.check_expr e env in
        (te :: ts, env))
      ltl_fml ([], env)
  in

  let ltl_fml =
    ltl_fml
    |> List.map (fun l ->
           match Monitor_go.fml_ownership env l with
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
    (fun i { repr = V (_, pname) } ->
      let pr, env = SMap.find pname all in
      let _, action_nodes =
        Actions.split_into_actions (parse_grain grain) pname env pr
      in
      action_nodes
      |> IMap.iter
           Actions.(
             fun i a ->
               log "%d %a" i (List.pp String.pp) (List.map fst a.params));
      let ltl =
        List.assoc_opt ~eq:String.equal pname ltl_fml
        |> Option.get_or ~default:[]
      in
      Monitor_go.translate_party_ltl env i pname ltl action_nodes
        (List.map (fun p -> p.repr |> var_name) parties))
    parties

let monitor ~grain file =
  try monitor grain file with Check_failure s -> Format.printf "%s@." s
