open Containers
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

let echo f lexbuf =
  let t = f lexbuf in
  Format.printf "tok %s@." (show_token t);
  t

let f = Lexer.f

let parse_mono_ic ic =
  let lexer = Lexing.from_channel ~with_positions:true ic in
  (* 4.11 *)
  (* Lexing.set_filename lexer file; *)
  try Ok (lexer |> Parser.p f) with
  | Parser.Error ->
    let pos = lexer.Lexing.lex_curr_p in
    let tok = Lexing.lexeme lexer in
    (* (Printexc.to_string e) *)
    Error
      (Format.sprintf "parse error near \"%s\", %s, line %d, col %d@." tok
         pos.pos_fname pos.pos_lnum
         (pos.pos_cnum - pos.pos_bol + 1))
  | Lexer.SyntaxError ->
    let pos = lexer.Lexing.lex_curr_p in
    (* (Printexc.to_string e) *)
    Error
      (Format.sprintf "unrecognized token, %s, line %d, col %d@." pos.pos_fname
         pos.pos_lnum
         (pos.pos_cnum - pos.pos_bol + 1))

let parse_mono file = Containers.IO.with_in file parse_mono_ic

(* https://baturin.org/blog/declarative-parse-error-reporting-with-menhir/ *)
open Lexing
module I = Parser.MenhirInterpreter

exception Syntax_error of ((int * int) option * string)

let get_lexing_position lexbuf =
  let p = Lexing.lexeme_start_p lexbuf in
  let line_number = p.Lexing.pos_lnum in
  let column = p.Lexing.pos_cnum - p.Lexing.pos_bol + 1 in
  (line_number, column)

let get_parse_error env =
  match I.stack env with
  | (lazy Nil) -> "Invalid syntax"
  | (lazy (Cons (I.Element (_state, _, _, _), _))) ->
    (* re-enable this if using the messages file *)
    (* try Parser_messages.message (I.number state)
       with Not_found -> "invalid syntax (no specific message for this eror)" *)
    "Invalid syntax"

let rec parse lexbuf (checkpoint : Ast.protocol I.checkpoint) =
  match checkpoint with
  | I.InputNeeded _env ->
    let token = Lexer.f lexbuf in
    let startp = lexbuf.lex_start_p and endp = lexbuf.lex_curr_p in
    let checkpoint = I.offer checkpoint (token, startp, endp) in
    parse lexbuf checkpoint
  | I.Shifting _ | I.AboutToReduce _ ->
    let checkpoint = I.resume checkpoint in
    parse lexbuf checkpoint
  | I.HandlingError _env ->
    let (line, pos) = get_lexing_position lexbuf in
    let err = get_parse_error _env in
    raise (Syntax_error (Some (line, pos), err))
  | I.Accepted v -> v
  | I.Rejected ->
    raise (Syntax_error (None, "invalid syntax (parser rejected the input)"))

let parse_inc file =
  Containers.IO.with_in file (fun ic ->
      (* stdin *)
      let lexbuf = Lexing.from_channel ~with_positions:true ic in
      (* 4.11 *)
      (* Lexing.set_filename lexer file; *)
      try Ok (parse lexbuf (Parser.Incremental.p lexbuf.lex_curr_p))
      with Syntax_error (pos, err) ->
        Error
          (Format.sprintf "%s%s" err
             (match pos with
             | None -> ""
             | Some (line, pos) -> Format.sprintf "line %d, col %d" line pos)))
