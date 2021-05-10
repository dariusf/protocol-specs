open Ast
open Common

(** printing contexts *)
type pctx = {
  (* precedence of the expression in which the current ast node appears *)
  prec : int;
  (* whether or not nodr is last in a sequence of some kind *)
  last : bool;
}

let render_protocol p =
  let open PPrint in
  (* let indent d = blank 2 ^^ nest 2 d in *)
  let (arrow, disj, par, if_, when_, in_, forall, exists) =
    ( string "->",
      string "\\/",
      string "||",
      string "=>",
      string "=>*",
      string "in",
      string "forall",
      string "exists" )
  in
  let spaced d = terminate space d in
  let nl = break 1 in
  let render_var (V (p, v)) =
    match p with
    | None -> string v
    | Some (Party p) -> concat [string p; dot; string v]
  in
  let is_alpha = function 'a' .. 'z' | 'A' .. 'Z' -> true | _ -> false in
  (* this should be kept in sync with the parser *)
  let get_expr_prec op =
    match op with
    | "==" -> 5
    | "<" | "<=" | ">" | ">=" -> 6
    | "+" | "-" -> 7
    | "/" | "*" -> 8
    | "&" | "|" -> 9
    | "!" -> 10
    | _ -> 0
  in
  let get_expr_assoc _ = `Left in
  (* prec is the precedence of the context, so we make sure to
     parenthesize when passing an expression with lower precedence into one with higher precedence. see https://stackoverflow.com/a/43639618. starting with 0 means we
     never parenthesize at the top level. *)
  let rec render_expr ?(prec = 0) e =
    match e with
    | Int i -> string (string_of_int i)
    | Bool b -> string (string_of_bool b)
    | Set es -> braces (List.map render_expr es |> separate (spaced comma))
    | List es -> brackets (List.map render_expr es |> separate (spaced comma))
    | Map es ->
      braces
        (List.map
           (fun (k, v) -> concat [string k; spaced colon; render_expr v])
           es
        |> separate (spaced comma))
    | App (f, args) ->
      if List.length args = 2 && not (is_alpha f.[0]) then
        let n = get_expr_prec f in
        let[@warning "-8"] [left; right] = args in
        let (leftp, rightp) =
          match get_expr_assoc f with
          | `Left -> (n, n + 1)
          | `Right -> (n + 1, n)
        in
        let parens =
          if prec > n then
            parens
          else
            Fun.id
        in
        parens
          (separate
             (enclose space space (string f))
             [render_expr ~prec:leftp left; render_expr ~prec:rightp right])
      else
        precede (string f)
          (parens (List.map render_expr args |> separate (spaced comma)))
    | Var v -> render_var v
    | Tuple (_, _) -> failwith "tuples?"
  in
  let get_protocol_prec p =
    match p with
    | Seq _ -> 5
    | Imply _ | BlockingImply (_, _) -> 4
    | Forall _ | Exists _ -> 3
    | Par _ | Disj _ -> 2
    | _ -> 0
  in
  let parens_multiline d = parens (nest 1 d) in
  let parens_multiline_if ~pctx ~n =
    if
      pctx.prec > n
      (* not sure if this is correct *)
      (* && not pctx.last *)
    then
      parens_multiline
    else
      Fun.id
  in
  let rec render_protocol ?(pctx = { prec = 0; last = false }) p =
    let n = get_protocol_prec p in
    match p with
    | Emp -> failwith "emp?"
    | Seq ps ->
      separate (semi ^^ nl)
        (ps
        |> map_last (fun last p -> render_protocol ~pctx:{ prec = n; last } p))
    | Par ps ->
      parens_multiline_if ~pctx ~n
      @@ separate
           (nl ^^ par ^^ nl)
           (ps
           |> map_last (fun last p ->
                  render_protocol ~pctx:{ prec = n; last } p))
    | Disj (a, b) ->
      parens_multiline_if ~pctx ~n
      @@ separate
           (nl ^^ disj ^^ nl)
           ([a; b]
           |> map_last (fun last p ->
                  render_protocol ~pctx:{ prec = n; last } p))
    | Send { from; to_; msg = Message { typ; args } } ->
      concat
        [
          render_var from; arrow; render_var to_; colon; space; string typ;
          (match args with
          | [] -> empty
          | _ ->
            parens
              (separate (spaced comma)
                 (List.map
                    (fun (v, e) -> concat [render_var v; equals; render_expr e])
                    args)));
        ]
    | Assign (v, e) -> separate space [render_var v; equals; render_expr e]
    | Imply (b, p) ->
      parens_multiline_if ~pctx ~n
      @@ nest 2
           (concat
              [
                render_expr b; space; if_; nl;
                render_protocol ~pctx:{ pctx with prec = n } p;
              ])
    | BlockingImply (b, p) ->
      parens_multiline_if ~pctx ~n
      @@ nest 2
           (concat
              [
                render_expr b; space; when_; nl;
                render_protocol ~pctx:{ pctx with prec = n } p;
              ])
    | Forall (v, s, p) ->
      parens_multiline_if ~pctx ~n
      @@ nest 2
           (concat
              [
                forall; space; render_var v; space; in_; space; render_var s;
                nl; render_protocol ~pctx:{ pctx with prec = n } p;
              ])
    | Exists (v, s, p) ->
      parens_multiline_if ~pctx ~n
      @@ nest 2
           (concat
              [
                exists; space; render_var v; space; in_; render_var s; nl;
                render_protocol ~pctx:{ pctx with prec = n } p;
              ])
    | SendOnly { from; to_; msg = MessageC { typ; args } } ->
      concat
        [
          star; render_var from; arrow; render_var to_; colon; space;
          string typ;
          (match args with
          | [] -> empty
          | _ -> parens (separate (spaced comma) (List.map render_expr args)));
        ]
    | ReceiveOnly { from; to_; msg = MessageD { typ; args } } ->
      concat
        [
          render_var from; arrow; render_var to_; star; colon; space;
          string typ;
          (match args with
          | [] -> empty
          | _ -> parens (separate (spaced comma) (List.map render_var args)));
        ]
    | Comment (_, _, _) -> failwith "comment"
  in
  render_protocol p
