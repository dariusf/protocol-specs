module P = Parser

let show_token t =
  let open P in
  match t with
  | WHEN -> "WHEN"
  | STAR -> "STAR"
  | SPACE n -> Format.sprintf "SPACE %d" n
  | INDENT n -> Format.sprintf "INDENT %d" n
  | SEMI -> "SEMI"
  | COLON -> "COLON"
  | COMMA -> "COMMA"
  | RPAREN -> "RPAREN"
  | PAR -> "PAR"
  | DISJ -> "DISJ"
  | NOT -> "NOT"
  | LPAREN -> "LPAREN"
  | INT i -> Format.sprintf "INT %d" i
  | IN -> "IN"
  | IF -> "IF"
  | IDENT i -> Format.sprintf "IDENT %s" i
  | FORALL -> "FORALL"
  | EXISTS -> "EXISTS"
  | EQ -> "EQ"
  | EQEQ -> "EQEQ"
  | EOF -> "EOF"
  | DOT -> "DOT"
  | ARROW -> "ARROW"
  | AND -> "AND"
  | OR -> "OR"
  | TRUE -> "TRUE"
  | FALSE -> "FALSE"
  | PLUS -> "PLUS"
  | MINUS -> "MINUS"
  | DIV -> "DIV"
  | LCURLY -> "LCURLY"
  | RCURLY -> "RCURLY"
  | LBRACKET -> "LBRACKET"
  | RBRACKET -> "RBRACKET"
  | GE -> ">="
  | GT -> ">"
  | LE -> "<="
  | LT -> "<"

let convert_space_to_parens f =
  let indent = ref [] in
  let bof = ref true in
  let rec aux lexbuf =
    (* Format.printf "---aux@."; *)
    match f lexbuf with
    | P.SPACE _ when not !bof ->
      (* print_endline "ignored space"; *)
      aux lexbuf
    | P.SPACE n when !bof ->
      (* print_endline "space bof"; *)
      indent := n :: !indent;
      bof := false;
      [P.LPAREN]
    | P.INDENT n ->
      bof := false;
      (* Format.printf "indent %d@." n; *)
      let k = match !indent with [] -> 0 | h :: _ -> h in
      if n > k then (
        (* Format.printf "up %s@." ([%derive.show: int list] !indent); *)
        indent := n :: !indent;
        [P.LPAREN])
      else if n < k then (
        let l1 = List.length !indent in
        indent := Containers.List.drop_while (fun m -> m > n) !indent;
        let l2 = List.length !indent in
        assert (l1 - l2 > 0);
        (* Format.printf "down %d %s@." (l1 - l2) ([%derive.show: int list] !indent); *)
        List.init (l1 - l2) (fun _ -> P.RPAREN))
      else (* equal, nothing to do *)
        aux lexbuf
    | P.EOF ->
      bof := false;
      (* print_endline "eof"; *)
      let close = List.map (fun _ -> P.RPAREN) !indent in
      indent := [];
      close @ [P.EOF]
    | e ->
      (* Format.printf "else %s@." (show_token e); *)
      bof := false;
      [e]
  in
  aux

let flatten f =
  let xs = ref [] in
  fun lexbuf ->
    match !xs with
    | x :: xs' ->
      xs := xs';
      x
    | [] ->
    match f lexbuf with
    | x :: xs' ->
      xs := xs';
      x
    | [] -> failwith "Lexer did nto return EOF token"

let echo f lexbuf =
  let t = f lexbuf in
  (* Format.printf "tok %s@." (show_token t); *)
  t

let f = Lexer.f |> convert_space_to_parens |> flatten |> echo
