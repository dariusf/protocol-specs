open Lib

let%expect_test "lexer" =
  let inp = "${{k:v for k, v in 1}} => 1" in
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
    {| prot: DOLLAR LCURLY2 IDENT COLON IDENT FOR IDENT COMMA IDENT IN INT RCURLY2 COND INT |}]

let%expect_test "parsing" =
  let inp = "p.a = ${{ k: v for k, v in {} }}" in
  Format.printf "%a@." Print.pp_protocol (parse_string inp).protocol;
  [%expect {| p.a = ${{k: v for k, v in {}}} |}]
