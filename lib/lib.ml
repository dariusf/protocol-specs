open Containers

(* module Tracing = Ppx_debug.Tracing *)

open Ast

module Tpc = struct
  (* let coord = Party "coordinator" *)

  (* let part = Party "participant" *)

  let coordinator = var "C"

  let participants = var "P"

  let p = var "p"

  let c = var "c"

  let responded = var "responded"

  let aborted = var "aborted"

  let env =
    Infer.
      {
        parties =
          [
            {
              repr = coordinator;
              other_sets = [];
              vars = [c];
              owned_vars = [responded; aborted; p];
            };
            {
              repr = participants;
              other_sets = [];
              vars = [p];
              owned_vars = [c];
            };
          ];
        var_info = VMap.empty;
        var_constraints = IMap.empty;
      }

  let protocol =
    Forall
      ( c,
        coordinator,
        Seq
          [
            Forall
              ( p,
                participants,
                Seq
                  [
                    Send { from = c; to_ = p; msg = msg "prepare" };
                    (* Comment *)
                    (* ( Some participants,
                       "participant's internal choice",
                       Comment
                         ( Some coordinator,
                           "coordinator's external choice", *)
                    Disj
                      ( Seq
                          [
                            Send { from = p; to_ = c; msg = msg "prepared" };
                            Assign
                              (responded, plus (Var responded) (Set [Var p]));
                          ],
                        Seq
                          [
                            Send { from = p; to_ = c; msg = msg "abort" };
                            Assign (aborted, plus (Var aborted) (Set [Var p]));
                          ] )
                    (* ) ) *);
                  ] );
            Disj
              ( BlockingImply
                  ( eq (Var aborted) (Set []),
                    Forall
                      ( p,
                        participants,
                        Seq
                          [
                            Send { from = c; to_ = p; msg = msg "commit" };
                            Send { from = p; to_ = c; msg = msg "commit_ack" };
                          ] ) ),
                Forall
                  ( p,
                    participants,
                    Seq
                      [
                        Send { from = c; to_ = p; msg = msg "abort" };
                        Send { from = p; to_ = c; msg = msg "abort_ack" };
                      ] ) );
          ] )
end

module Test = struct
  let responded = var "responded"

  let participant = var "P"

  let p = var "p"

  let env =
    Infer.
      {
        parties =
          [
            {
              repr = participant;
              other_sets = [];
              vars = [p];
              owned_vars = [responded];
            };
          ];
        var_info = VMap.empty;
        var_constraints = IMap.empty;
      }

  let protocol =
    Seq
      [
        Assign (responded, plus (Var responded) (Set [Var p]));
        Assign (responded, plus (Var responded) (Set [Var p]));
      ]
end

module Paxos = struct
  let proposers = var "P"

  let acceptors = var "A"

  let learners = var "L"

  let l = var "l"

  let p = var "p"

  let a = var "a"

  let a1 = var "a1"

  (* current proposal number of proposer *)
  let proposal = var "proposal"

  let value = var "value"

  let majority = var "majority"

  let promise_responses = var "promise_responses"

  (* acceptor *)
  let highest_proposal = var "highest_proposal"

  let accepted_proposal = var "accepted_proposal"

  let accepted_value = var "accepted_value"

  (* messages *)
  let n = var "n"

  let cv = var "cv"

  let cp = var "cp"

  let pn = var "pn"

  let pv = var "pv"

  let env =
    Infer.
      {
        parties =
          [
            {
              repr = proposers;
              other_sets = [];
              vars = [p];
              owned_vars =
                [a; p]
                @ [proposal; value; majority; promise_responses; cp]
                @ [cp; cv];
            };
            { repr = learners; other_sets = []; vars = [l]; owned_vars = [] };
            {
              repr = acceptors;
              other_sets = [promise_responses];
              vars = [a; a1];
              owned_vars =
                [p]
                @ [highest_proposal; accepted_proposal; accepted_value]
                @ [n; pn; pv];
            };
          ];
        var_info = VMap.empty;
        var_constraints = IMap.empty;
      }

  let protocol =
    Comment
      ( None,
        "all currently-competing proposers",
        Seq
          [
            Forall
              ( p,
                proposers,
                Seq
                  [
                    Assign (p >. proposal, Int 0);
                    Assign (p >. value, App ("external", []));
                    Assign (p >. cp, Tuple (Int 0, Int 0));
                    Assign
                      ( p >. majority,
                        plus
                          (App ("/", [App ("size", [Var acceptors]); Int 2]))
                          (Int 1) ); Assign (p >. promise_responses, Set []);
                  ] );
            Forall
              ( a,
                acceptors,
                Seq
                  [
                    Assign (a >. highest_proposal, Tuple (Int 0, Int 0));
                    Assign (a >. accepted_proposal, Tuple (Int 0, Int 0));
                    Assign (a >. accepted_value, Int 0);
                  ] );
            Forall
              ( p,
                proposers,
                Par
                  [
                    Seq
                      [
                        Assign
                          (p >. proposal, plus (Var (p >. proposal)) (Int 1));
                        Forall
                          ( a,
                            acceptors,
                            Seq
                              [
                                Send
                                  {
                                    from = p;
                                    to_ = a;
                                    msg =
                                      Message
                                        {
                                          typ = "prepare";
                                          args =
                                            [
                                              ( n,
                                                Tuple
                                                  (Var p, Var (p >. proposal))
                                              );
                                            ];
                                        };
                                  };
                                Imply
                                  ( gt (Var n) (Var (a >. highest_proposal)),
                                    Seq
                                      [
                                        Assign (a >. highest_proposal, Var n);
                                        Send
                                          {
                                            from = a;
                                            to_ = p;
                                            msg =
                                              Message
                                                {
                                                  typ = "promise";
                                                  args =
                                                    [
                                                      ( cp,
                                                        Var
                                                          (a
                                                         >. accepted_proposal)
                                                      );
                                                      ( cv,
                                                        Var (a >. accepted_value)
                                                      );
                                                    ];
                                                };
                                          };
                                        Assign
                                          ( p >. promise_responses,
                                            plus
                                              (Var (p >. promise_responses))
                                              (Set [Var a]) );
                                        Comment
                                          ( Some proposers,
                                            "if a has already accepted \
                                             something",
                                            Imply
                                              ( and_
                                                  (gt (Var cp)
                                                     (Tuple (Int 0, Int 0)))
                                                  (gt (Var cp) (Var (p >. cp))),
                                                Seq
                                                  [
                                                    Assign (p >. cp, Var cp);
                                                    Assign (p >. value, Var cv);
                                                  ] ) );
                                      ] );
                              ] );
                      ];
                    Comment
                      ( Some proposers,
                        {|doesn't continue replying with accepts if others outside this set reply|},
                        BlockingImply
                          ( gt
                              (App ("size", [Var (p >. promise_responses)]))
                              (Var (p >. majority)),
                            Comment
                              ( Some proposers,
                                "it's sufficient to reply to the majority \
                                 subset",
                                Forall
                                  ( a1,
                                    p >. promise_responses,
                                    Seq
                                      [
                                        Send
                                          {
                                            from = p;
                                            to_ = a1;
                                            msg =
                                              Message
                                                {
                                                  typ = "propose";
                                                  args =
                                                    [
                                                      (pn, Var (p >. proposal));
                                                      (pv, Var (p >. value));
                                                    ];
                                                };
                                          };
                                        Imply
                                          ( eq (Var pn)
                                              (Var (a1 >. highest_proposal)),
                                            Seq
                                              [
                                                Assign
                                                  ( a1 >. accepted_proposal,
                                                    Var pn );
                                                Assign
                                                  (a1 >. accepted_value, Var pv);
                                                Send
                                                  {
                                                    from = a1;
                                                    to_ = p;
                                                    msg = msg "accept";
                                                  };
                                                Forall
                                                  ( l,
                                                    learners,
                                                    Send
                                                      {
                                                        from = a1;
                                                        to_ = l;
                                                        msg = msg "accept";
                                                      } );
                                              ] );
                                      ] ) ) ) );
                  ] );
          ] )
end

let snapshot_protocol name env pr =
  let projections =
    let res = Project.project env pr in
    List.map2
      (fun Infer.{ repr; _ } r ->
        let init =
          match Infer.has_initiative (V (None, var_name repr)) r with
          | true -> "has"
          | false -> "does not have"
        in
        Format.sprintf "projection of %s@.%s %s initiative@.@.%a"
          (var_name repr) (var_name repr) init pp_protocol r)
      env.parties res
    |> String.concat "\n--\n"
  in
  let inf =
    (* TODO toggle this *)
    (* infer_parties env pr |> ignore; *)
    (* let inf = infer_parties env pr in *)
    (* p_env inf *)
    "<inferred parties>"
  in
  let s =
    Format.sprintf "protocol:@.@.%a@.@.---@.@.projections:@.@.%s@.%s@."
      pp_protocol pr projections inf
  in
  IO.File.(write_exn (make ("/tmp/" ^ name ^ ".txt")) s);
  print_endline s

let parse_party_spec s =
  let parts = String.split ~by:":" s in
  let[@warning "-8"] [[repr]; vars; owned_vars; other_sets] =
    parts
    |> List.map (String.split ~by:",")
    |> List.map (List.filter (Fun.negate String.is_empty))
  in
  (* don't handle error *)
  Infer.
    {
      repr = var repr;
      vars = List.map var vars;
      owned_vars = List.map var owned_vars;
      other_sets = List.map var other_sets;
    }

let print project_party party_specs ast no_normalize file =
  let protocol =
    let prot =
      (* let p = Parsing.parse_inc file in *)
      match
        if String.equal file "-" then
          Parsing.parse_mono_ic file stdin
        else
          Parsing.parse_mono file
      with
      | Ok p -> p
      | Error s -> failwith s
    in
    match project_party with
    | Some p_party ->
      begin
        match party_specs with
        | [] -> failwith "party specs are required for projection"
        | _ ->
          let parties = List.map parse_party_spec party_specs in
          (* Format.printf "parties %s@." ([%derive.show: party_info list] parties) *)
          let env =
            Infer.
              { parties; var_info = VMap.empty; var_constraints = IMap.empty }
          in
          let projected = Project.project env prot in
          (match
             List.find_idx
               (fun pr -> String.equal p_party (var_name pr.Infer.repr))
               parties
           with
          | None -> failwith "could not find such a party"
          | Some (i, _) -> List.nth projected i)
      end
    | None -> prot
  in

  protocol
  (* |> eval |> string_of_int *)
  (* |> Exp.show *)
  (* |> Format.sprintf "%a" pp_protocol |> print_endline *)
  |> (if no_normalize then Fun.id else Normalize.normalize)
  |> Fun.Infix.(
       if ast then
         show_protocol %> print_endline
       else
         Print.render_protocol %> PPrint.ToChannel.pretty 0.8 120 stdout)

module U = UnionFind.Make (UnionFind.StoreMap)

let test () =
  let store = U.new_store () in
  let (s, r) = U.make store 1 in
  let (s, r1) = U.make s 2 in
  (* let s = U.set s r 3 in *)
  let s = U.union max s r r1 in
  (U.get s r |> snd, U.get s r1 |> snd)

(* Tracing.wrap (fun () ->
    (* print_endline "abccc"; *)
    (* snapshot_protocol "test" Test.env Test.protocol *)
    snapshot_protocol "paxos" Paxos.env Paxos.protocol) *)
