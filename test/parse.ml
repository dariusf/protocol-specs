open Lib

let%expect_test "lexer" =
  let inp = "if b then forall c in C c.a = 1 else c->b: m end" in
  let lb = Lexing.from_string inp in
  print_string "prot: ";
  let rec loop () =
    let t = Lexer.token lb in
    match t with
    | EOF -> ()
    | _ ->
      print_string (Parsing.show_token t ^ " ");
      loop ()
  in
  loop ();
  [%expect
    {| prot: IF IDENT THEN FORALL IDENT IN IDENT IDENT DOT IDENT EQ INT ELSE IDENT ARROW IDENT COLON IDENT END |}]

let%expect_test "parsing" =
  let test s =
    let inp = s in
    Format.printf "%a@." Print.pp_protocol (parse_string inp).protocol
  in
  test "p.a = ${{ k: v for k, v in {} }}";
  test "p.a = 'b'";
  test "p.a = p.a[1]";
  test "p.a = p.a['x']";
  (* test "p.a = p.a.x"; *)
  test "p.a = [0]";
  test "p.a = [ ]";
  test "if b then forall c in C c.a = 1 else c->b: m end";
  test "p.a = let x = 1 in y";
  [%expect
    {|
    p.a = ${{k: v for k, v in {}}}
    p.a = 'b'
    p.a = p.a[1]
    p.a = p.a['x']
    p.a = [0]
    p.a = []
    b =>*
      (forall c in C
         c.a = 1)
    \/
    !(b) =>*
      c->b : m
    p.a = let x = 1 in y |}]

let%expect_test "spec" =
  let test s =
    let inp = s in
    (parse_string inp).decls
    |> List.iter (fun d -> Format.printf "%a@." Print.pp_spec_decl d)
  in
  test {|party c in C (
    c.a = 1;
    c.b = 2)
  p.a = 1|};
  [%expect {|
    party c in C (
      c.a = 1;
      c.b = 2
    ) |}]
