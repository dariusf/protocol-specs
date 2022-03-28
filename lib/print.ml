open Ast
open Common
open Common.Printing
open PPrint

let latex_escape = enclose (string "/*$") (string "$*/")
let arrow latex = if latex then latex_escape (string "\\send") else string "->"

let disj latex =
  if latex then
    latex_escape (string "\\vee")
  else
    string "\\/"

let if_ latex =
  if latex then
    latex_escape (string "\\pif")
  else
    string "=>"

let when_ latex =
  if latex then
    latex_escape (string "\\when")
  else
    string "=>*"

let (par, in_, forall, exists) =
  (string "||", string "in", string "forall", string "exists")

(** printing contexts *)
type pctx = {
  (* precedence of the expression in which the current ast node appears *)
  prec : int;
  (* whether or not nodr is last in a sequence of some kind *)
  last : bool;
}

let render_var (V (p, v)) =
  match p with
  | None -> string v
  | Some (Party p) -> concat [string p; dot; string v]

(* this should be kept in sync with the parser *)
let get_expr_prec op =
  match op with
  | "<>" | "[]" -> 1
  | "==>" -> 2
  | "|" -> 3
  | "&" -> 4
  | "==" | "!=" -> 5
  | "<" | "<=" | ">" | ">=" -> 6
  | "+" | "-" | "\\" -> 7
  | "/" | "*" -> 8
  | "!" -> 10
  | _ -> 0

let fact f n = match n with 0 -> 1 | _ -> n * f (n - 1)
let rec fact1 n = fact fact1 n
let get_expr_assoc _ = `Left

(** prec is the precedence of the context, so we make sure to
    parenthesize when passing an expression with lower precedence into one with higher precedence. see https://stackoverflow.com/a/43639618. starting with 0 means we
    never parenthesize at the top level. *)
let render_expr_ :
    (?prec:int -> 'a _expr -> document) -> ?prec:int -> 'a _expr -> document =
 fun f ?(prec = 0) e ->
  match e.expr with
  | Int i -> string (string_of_int i)
  | Bool b -> string (string_of_bool b)
  | String s -> string (Format.sprintf {|"%s"|} s)
  | Timeout -> string "timeout"
  | Else -> string "else"
  | Set es -> braces (List.map f es |> separate (spaced comma))
  | List es -> brackets (List.map f es |> separate (spaced comma))
  | Map es ->
    braces
      (List.map (fun (k, v) -> concat [string k; spaced colon; f v]) es
      |> separate (spaced comma))
  | App (fn, args) ->
    if List.length args = 2 && not (is_alpha fn.[0]) then
      let n = get_expr_prec fn in
      let[@warning "-8"] [left; right] = args in
      let (leftp, rightp) =
        match get_expr_assoc fn with `Left -> (n, n + 1) | `Right -> (n + 1, n)
      in
      let parens =
        if prec > n then
          parens
        else
          Fun.id
      in
      parens
        (separate
           (enclose space space (string fn))
           [f ~prec:leftp left; f ~prec:rightp right])
    else
      precede (string fn) (parens (List.map f args |> separate (spaced comma)))
  | Var v -> render_var v
  | Tuple (_, _) -> failwith "tuples?"

let rec render_expr : ?prec:int -> expr -> document =
 fun ?prec e -> render_expr_ render_expr ?prec e

let rec strip_type : texpr -> expr =
 fun e ->
  let e1 =
    match e.expr with
    | Int i -> Int i
    | Bool b -> Bool b
    | String s -> String s
    | Timeout -> Timeout
    | Else -> Else
    | Var v -> Var v
    | Set es -> Set (List.map strip_type es)
    | List es -> List (List.map strip_type es)
    | Map es -> Map (List.map (fun (k, v) -> (k, strip_type v)) es)
    | App (f, args) -> App (f, List.map strip_type args)
    | Tuple (_, _) -> failwith "tuples?"
  in
  { meta = e.meta.loc; expr = e1 }

let render_party party = render_var party.repr
let render_uf u = string ("$" ^ string_of_int (UF.value u))

let render_own ~env own =
  match own with
  | Global -> string "global"
  | Party p ->
  match IMap.find_opt (UF.value p) env.parties with
  | None -> separate space [string "unbound"; render_uf p]
  | Some p -> render_party p

let rec render_typ ?(latex = false) ~env t =
  match t with
  | TyParty p -> separate space [string "party"; render_own ~env (Party p)]
  | TySet e -> braces (render_typ ~latex ~env e)
  | TyList e -> brackets (render_typ ~latex ~env e)
  | TyVar v ->
    (match IMap.find_opt (UF.value v) env.types with
    | None -> separate space [string "unbound"; render_uf v]
    | Some t -> render_typ ~latex ~env t)
  | TyInt -> string "int"
  | TyBool -> string "bool"
  | TyString -> string "string"
  | TyFn (args, r) ->
    separate
      (enclose space space (arrow latex))
      [
        parens (separate (spaced comma) (List.map (render_typ ~latex ~env) args));
        (render_typ ~latex ~env) r;
      ]

let rec render_texpr : ?prec:int -> env:env -> texpr -> document =
 fun ?(prec = 0) ~env e ->
  match e.expr with
  | Var _ ->
    parens
      (separate
         (enclose space space colon)
         [
           render_expr_ (render_texpr ~env) ~prec e;
           separate semi
             [
               render_typ ~env e.meta.info.typ; (render_own ~env) e.meta.info.own;
             ];
         ])
  | _ -> render_expr_ (render_texpr ~env) ~prec e

let rec render_texpr_as_expr : ?prec:int -> env:env -> texpr -> document =
 fun ?(prec = 0) ~env e ->
  match e.expr with _ -> render_expr_ (render_texpr_as_expr ~env) ~prec e

(* let indent d = blank 2 ^^ nest 2 d in *)
let get_protocol_prec p =
  match p.p with
  | Seq _ -> 5
  | Imply _ | BlockingImply (_, _) -> 4
  | Forall _ | Exists _ -> 3
  | Par _ | Disj _ -> 2
  | _ -> 0

let parens_multiline d = parens (nest 1 d)

let parens_multiline_if ~pctx ~n =
  if
    pctx.prec > n
    (* not sure if this is correct *)
    (* && not pctx.last *)
  then
    parens_multiline
  else
    Fun.id

let render_protocol_ :
    bool -> ('e -> document) -> ('a, 'e, 'v) _protocol -> document =
 fun latex render_expr p ->
  let rec render_protocol ?(pctx = { prec = 0; last = false }) p =
    let n = get_protocol_prec p in
    match p.p with
    | Emp -> string "skip"
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
           (nl ^^ disj latex ^^ nl)
           ([a; b]
           |> map_last (fun last p ->
                  render_protocol ~pctx:{ prec = n; last } p))
    | Call { f; args; _ } ->
      concat
        [
          string "$"; string f;
          parens (separate (spaced comma) (List.map render_expr args));
        ]
    | Send { from; to_; msg = Message { typ; args } } ->
      concat
        [
          render_expr from; arrow latex; render_expr to_;
          enclose space space colon; string typ;
          (match args with
          | [] -> empty
          | _ ->
            parens
              (separate (spaced comma)
                 (List.map
                    (fun (v, e) ->
                      concat [render_expr v; equals; render_expr e])
                    args)));
        ]
    | SendOnly { to_; msg = Message { typ; args }; _ } ->
      concat
        [
          arrow latex; render_expr to_; enclose space space colon; string typ;
          (match args with
          | [] -> empty
          | _ ->
            parens
              (separate (spaced comma)
                 (List.map
                    (fun (v, e) ->
                      concat [render_expr v; equals; render_expr e])
                    args)));
        ]
    | ReceiveOnly { from; msg = MessageD { typ; args }; _ } ->
      concat
        [
          render_expr from; arrow latex; enclose space space colon; string typ;
          (match args with
          | [] -> empty
          | _ -> parens (separate (spaced comma) (List.map render_expr args)));
        ]
    | Assign (v, e) -> separate space [render_expr v; equals; render_expr e]
    | Imply (b, p) ->
      parens_multiline_if ~pctx ~n
      @@ nest 2
           (concat
              [
                render_expr b; space; if_ latex; nl;
                render_protocol ~pctx:{ pctx with prec = n } p;
              ])
    | BlockingImply (b, p) ->
      parens_multiline_if ~pctx ~n
      @@ nest 2
           (concat
              [
                render_expr b; space; when_ latex; nl;
                render_protocol ~pctx:{ pctx with prec = n } p;
              ])
    | Forall (v, s, p) ->
      parens_multiline_if ~pctx ~n
      @@ nest 2
           (concat
              [
                forall; space; render_expr v; space; in_; space;
                (match s.expr with
                | Var _ -> render_expr s
                | _ -> parens (render_expr s)); nl;
                render_protocol ~pctx:{ pctx with prec = n } p;
              ])
    | Exists (v, s, p) ->
      parens_multiline_if ~pctx ~n
      @@ nest 2
           (concat
              [
                exists; space; render_expr v; space; in_; render_expr s; nl;
                render_protocol ~pctx:{ pctx with prec = n } p;
              ])
    | Comment (_, _, _) -> failwith "comment"
  in
  render_protocol p

let render_protocol ?(latex = false) p = render_protocol_ latex render_expr p

let render_tprotocol ?(latex = false) ~env p =
  render_protocol_ latex (render_texpr ~env) p

let render_tprotocol_untyped ?(latex = false) ~env p =
  render_protocol_ latex (render_texpr_as_expr ~env) p

let render_functions env =
  env.subprotocols |> SMap.bindings
  |> List.map (fun (name, f) ->
         separate space
           [
             string "protocol"; string name ^^ parens empty;
             parens (nest 2 (nl ^^ render_tprotocol_untyped ~env f.tp) ^^ nl);
             nl;
           ])
  |> concat

let pretty fmt d = PPrint.ToFormatter.pretty 0.8 120 fmt d

let to_pp ?(one_line = true) render fmt a =
  Format.fprintf fmt
    (if one_line then "@[<h>%a@]@?" else "%a")
    pretty (render a)

let pp_tprotocol ~env = to_pp (render_tprotocol ~env)
let pp_tprotocol_untyped ~env = to_pp (render_tprotocol_untyped ~env)
let pp_expr = to_pp (fun t -> render_expr t)
let pp_texpr ~env = to_pp (fun t -> render_texpr ~env t)
let pp_texpr_untyped ~env = to_pp (fun t -> render_texpr_as_expr ~env t)
let pp_typ ~env = to_pp (fun t -> render_typ ~env t)
let pp_ownership ~env = to_pp (fun t -> render_own ~env t)

let pp_tid fmt t =
  Format.fprintf fmt "%s%s" t.name
    (match t.params with
    | [] -> ""
    | ts ->
      Format.sprintf "(%s)"
        (String.concat ", "
           (List.map (fun (t, s) -> Format.sprintf "%s:%s" t s) ts)))
