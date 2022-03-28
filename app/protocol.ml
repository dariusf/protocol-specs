open Containers
open Cmdliner

(* Help sections common to all commands *)

let help_secs =
  [
    `S Manpage.s_common_options;
    `P "These options are common to all commands.";
    `S "MORE HELP";
    `P "Use `$(mname) $(i,COMMAND) --help' for help on a single command.";
    `Noblank;
    `P "Use `$(mname) help patterns' for help on patch matching.";
    `Noblank;
    `P "Use `$(mname) help environment' for help on environment variables.";
    `S Manpage.s_bugs;
    `P "Check bug reports at http://bugs.example.org.";
  ]

(* Commands *)

let help man_format cmds topic =
  match topic with
  | None -> `Help (`Pager, None) (* help about the program. *)
  | Some topic ->
    let topics = "topics" :: "patterns" :: "environment" :: cmds in
    let conv, _ = Cmdliner.Arg.enum (List.rev_map (fun s -> (s, s)) topics) in
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
      `P "Prints help about wiki commands and other topics.";
      `Blocks help_secs;
    ]
  in
  Cmd.v
    (Cmd.info "help" ~doc ~man)
    Term.(ret (const help $ Arg.man_format $ Term.choice_names $ topic))

let print project parties ast types actions latex file grain =
  (* Ppx_debug.Tracing.wrap (fun () -> *)
  Lib.print ~project_party:project ~parties ~ast ~types ~actions ~latex ~grain
    (`File file)
  (* ) *);
  `Ok ()

let tla parties spec_name grain file =
  (* Ppx_debug.Tracing.wrap (fun () -> *)
  Lib.tla ~parties ~spec_name ~grain file (* ) *);
  `Ok ()

let monitor parties grain file =
  (* Ppx_debug.Tracing.wrap (fun () -> *)
  Lib.monitor ~parties ~grain file (* ) *);
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
  let actions =
    Arg.(value & flag (info ~docv:"ACTIONS" ~doc:"print actions" ["actions"]))
  in
  let latex = Arg.(value & flag (info ~docv:"LATEX" ~doc:"latex" ["latex"])) in
  let grain =
    Arg.(
      value
      & opt (some string) None
          (info ~docv:"GRAIN" ~doc:"vary the grain of atomicity" ["grain"]))
  in
  let man =
    [
      `S Manpage.s_description;
      `P "Renders a specification in various forms.";
      `Blocks help_secs;
    ]
  in
  Cmd.v
    (Cmd.info "print" ~doc:"renders a specification" ~man)
    Term.(
      ret
        (const print $ project $ parties $ ast $ types $ actions $ latex $ file
       $ grain))

let tla_cmd =
  let file =
    Arg.(value & pos 0 string "-" & info [] ~docv:"FILE" ~doc:"file")
  in
  let parties =
    Arg.(
      value
      & opt (some string) None
          (info ~docv:"PARTIES" ~doc:"indicate party sets" ["parties"]))
  in
  let grain =
    Arg.(
      value
      & opt (some string) None
          (info ~docv:"GRAIN" ~doc:"vary the grain of atomicity" ["grain"]))
  in
  let spec_name =
    Arg.(
      value
      & opt (some string) None
          (info ~docv:"SPEC NAME" ~doc:"the name of the output spec"
             ["spec-name"]))
  in
  let man =
    [
      `S Manpage.s_description;
      `P "Compiles a specification to TLA+.";
      `Blocks help_secs;
    ]
  in
  Cmd.v
    (Cmd.info "tla" ~doc:"compiles a specification to TLA+" ~man)
    Term.(ret (const tla $ parties $ spec_name $ grain $ file))

let monitor_cmd =
  let file =
    Arg.(value & pos 0 string "-" & info [] ~docv:"FILE" ~doc:"file")
  in
  let parties =
    Arg.(
      value
      & opt (some string) None
          (info ~docv:"PARTIES" ~doc:"indicate party sets" ["parties"]))
  in
  let grain =
    Arg.(
      value
      & opt (some string) None
          (info ~docv:"GRAIN" ~doc:"vary the grain of atomicity" ["grain"]))
  in
  let man =
    [
      `S Manpage.s_description;
      `P "generates a monitor for runtime verification";
      `Blocks help_secs;
    ]
  in
  Cmd.v
    (Cmd.info "monitor" ~doc:"generates a monitor for runtime verification" ~man)
    Term.(ret (const monitor $ parties $ grain $ file))

let cmds = [print_cmd; tla_cmd; monitor_cmd; help_cmd]

let default_group =
  let doc = "Protocol specifications" in
  let sdocs = Manpage.s_common_options in
  let man = help_secs in
  let default = Term.(ret (const (`Ok ()))) in
  let info = Cmd.info "protocol" ~version:"v0.1" ~doc ~sdocs ~man in
  Cmd.group ~default info cmds

let () = Cmd.(eval default_group |> exit)
