open Containers
open Cmdliner

(* Help sections common to all commands *)

let help_secs =
  [
    `S Manpage.s_common_options; `P "These options are common to all commands.";
    `S "MORE HELP";
    `P "Use `$(mname) $(i,COMMAND) --help' for help on a single command.";
    `Noblank; `P "Use `$(mname) help patterns' for help on patch matching.";
    `Noblank;
    `P "Use `$(mname) help environment' for help on environment variables.";
    `S Manpage.s_bugs; `P "Check bug reports at http://bugs.example.org.";
  ]

(* Commands *)

let help man_format cmds topic =
  match topic with
  | None -> `Help (`Pager, None) (* help about the program. *)
  | Some topic ->
    let topics = "topics" :: "patterns" :: "environment" :: cmds in
    let (conv, _) = Cmdliner.Arg.enum (List.rev_map (fun s -> (s, s)) topics) in
    (match conv topic with
    | `Error e -> `Error (false, e)
    | `Ok t when String.equal t "topics" ->
      List.iter print_endline topics;
      `Ok ()
    | `Ok t when List.mem ~eq:String.equal t cmds -> `Help (man_format, Some t)
    | `Ok _ ->
      let page = ((topic, 7, "", "", ""), [`S topic; `P "Say something"]) in
      `Ok (Cmdliner.Manpage.print man_format Format.std_formatter page))

let help_cmd =
  let topic =
    let doc = "The topic to get help on. `topics' lists the topics." in
    Arg.(value & pos 0 (some string) None & info [] ~docv:"TOPIC" ~doc)
  in
  let doc = "display help about wiki commands and other topics" in
  let man =
    [
      `S Manpage.s_description;
      `P "Prints help about wiki commands and other topics."; `Blocks help_secs;
    ]
  in
  ( Term.(ret (const help $ Arg.man_format $ Term.choice_names $ topic)),
    Term.info "help" ~doc ~exits:Term.default_exits ~man )

let print project parties ast types file =
  Ppx_debug.Tracing.wrap (fun () -> Lib.print project parties ast types file);
  `Ok ()

let print_cmd =
  let file =
    Arg.(value & pos 0 string "-" & info [] ~docv:"FILE" ~doc:"file")
  in
  let project =
    Arg.(
      value
      & opt (some string) None
          (info ~docv:"PROJECT" ~doc:"project protocol for a specific party"
             ["project"]))
  in
  let parties =
    Arg.(
      value
      & opt (some string) None
          (info ~docv:"PARTIES" ~doc:"indicate party sets" ["parties"]))
  in
  let ast =
    Arg.(value & flag (info ~docv:"AST" ~doc:"dumps the AST" ["ast"]))
  in
  let types =
    Arg.(
      value
      & flag
          (info ~docv:"TYPES" ~doc:"print values annotated with types" ["types"]))
  in
  let man =
    [
      `S Manpage.s_description; `P "Renders a specification in various forms.";
      `Blocks help_secs;
    ]
  in
  ( Term.(ret (const print $ project $ parties $ ast $ types $ file)),
    Term.info "print" ~doc:"renders a specification" ~exits:Term.default_exits
      ~man )

let cmds = [print_cmd; help_cmd]

let default_cmd =
  let doc = "Protocol specifications" in
  let sdocs = Manpage.s_common_options in
  let exits = Term.default_exits in
  let man = help_secs in
  ( Term.(ret (const (`Ok ()))),
    Term.info "protocol" ~version:"v0.1" ~doc ~sdocs ~exits ~man )

let () = Term.(eval_choice default_cmd cmds |> exit)
