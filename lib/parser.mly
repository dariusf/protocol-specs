%token <int> SPACE
%token <int> INDENT
%token EOF
%token LPAREN RPAREN COLON COMMA
%token AND OR NOT PLUS MINUS DIV LT LE GT GE EQEQ
%token TRUE FALSE LBRACKET RBRACKET LCURLY RCURLY
%token <int> INT
%token <string> IDENT
%token FORALL EXISTS IN DOT IF WHEN DISJ SEMI PAR ARROW EQ STAR

%left PAR DISJ
(* this also resolves shift/reduce conflicts with par/disj/semi, has to be before (lower than) semi *)
%right IF WHEN
(* this resolves the shift/reduce conflict caused by forall protocol; protocol in favour of shifting (negation of case 1 in 6.1 of the menhir manual) if this is before semi (try moving it after to see the effect). it's given a name because we don't want to use the rightmost terminal to figure out that production's precedence level *)
%right forall_exists
%left SEMI (* this being after if/when makes it the reverse of what ocaml does: semicolons get nested inside conditionals  *)

%left EQEQ
%left LT LE GT GE
%left PLUS MINUS
%left DIV STAR
%left OR
%left AND
%nonassoc NOT

%start <Ast.expr> f
%start <Ast.protocol> p

%%

f : e = expr; EOF { e }

%inline binop :
  | PLUS { "+" }
  | MINUS { "-" }
  | STAR { "*" }
  | DIV { "/" }
  | AND { "&" }
  | EQEQ { "==" }
  | OR { "|" }
  | GT { ">" }
  | GE { ">=" }
  | LT { "<" }
  | LE { "<=" }

map_kvp :
  | v = IDENT; COLON; e = expr; { (v, e) }

expr :
  | n = INT; { Ast.Int n }

  | i = IDENT;
    { Ast.Var (V (None, i)) }
  | p = IDENT; DOT; i = IDENT;
    { Ast.Var (V (Some (Party p), i)) }
  | f = IDENT; args = delimited(LPAREN, separated_list(COMMA, expr), RPAREN)
    { Ast.App (f, args) }

  (* ugh using the macros causes shift/reduce conflicts but inlining this doesn't! *)
  (*
  | party = terminated(IDENT?, DOT); i = IDENT;
    { Ast.Var (V (Option.map (fun p -> Ast.Party p) party, i)) }
*)

  (*%prec dot*)
  (*
  | party = terminated(expr?, DOT); i = IDENT;
  (*%prec dot*)
    { Ast.Var (V (Option.map (fun p -> Ast.Party p) party, i)) }
  *)
  | TRUE; { Ast.Bool true }
  | FALSE; { Ast.Bool false }
  | a = expr; o = binop; b = expr; { Ast.App (o, [a; b]) }
  | NOT; e = expr; { Ast.App ("!", [e]) }
  | es = delimited(LCURLY, separated_list(COMMA, expr), RCURLY) { Ast.Set es }
  | es = delimited(LBRACKET, separated_nonempty_list(COMMA, expr), RBRACKET) { Ast.List es }
  (* empty set/map are ambiguous *)
  | es = delimited(LCURLY, separated_nonempty_list(COMMA, map_kvp), RCURLY) { Ast.Map es }
  | LPAREN; e = expr; RPAREN; { e }

p : pr = protocol; EOF { pr }

msg_kvp :
  | v = IDENT; EQ; e = expr; { (V (None, v), e) }

var :
  | var = IDENT;
    { Ast.V (None, var) }
  | party = IDENT; DOT; var = IDENT;
    { Ast.V (Some (Party party), var) }

protocol :
  (*| party = terminated(IDENT?, DOT) var = IDENT; EQ; e = expr;*)
    (*{ Ast.Assign (V (Option.map (fun p -> Ast.Party p) party, var), e) }*)
    (*
  | var = IDENT; EQ; e = expr;
    { Ast.Assign (V (None, var), e) }
  | party = IDENT; DOT; var = IDENT; EQ; e = expr;
    { Ast.Assign (V (Some (Party party), var), e) }
*)
  | v = var; EQ; e = expr; { Ast.Assign (v, e) }
  | p1 = IDENT; ARROW; p2 = IDENT; COLON; m = IDENT; args = loption(delimited(LPAREN, separated_nonempty_list(COMMA, msg_kvp), RPAREN));
    { Ast.Send { from = V (None, p1); to_ = V (None, p2); msg = Message { typ = m; args = args } } }
  | STAR; p1 = IDENT; ARROW; p2 = IDENT; COLON; m = IDENT; es = loption(delimited(LPAREN, separated_nonempty_list(COMMA, expr), RPAREN));
    { Ast.SendOnly { from = V (None, p1); to_ = V (None, p2); msg = MessageC { typ = m; args = es } } }
  | p1 = IDENT; ARROW; p2 = IDENT; STAR; COLON; m = IDENT; is = loption(delimited(LPAREN, separated_nonempty_list(COMMA, IDENT), RPAREN));
    { Ast.ReceiveOnly { from = V (None, p1); to_ = V (None, p2); msg = MessageD { typ = m; args = is |> List.map (fun i -> Ast.V (None, i)) } } }
  (*| ps = separated_nonempty_list(SEMI, protocol) { Ast.Seq ps }*)
  | p1 = protocol; SEMI; p2 = protocol; { Ast.Seq [p1; p2] }
  | p1 = protocol; PAR; p2 = protocol; { Ast.Par [p1; p2] }
  (*| ps = separated_nonempty_list(PAR, protocol) { Ast.Par ps }*)
  | p1 = protocol; DISJ; p2 = protocol; { Ast.Disj (p1, p2) }
  | b = expr; IF; p = protocol; { Ast.Imply (b, p) }
  | b = expr; WHEN; p = protocol; { Ast.BlockingImply (b, p) }
  (*
  | FORALL; v = IDENT; IN; s = var; DOT; p = protocol; %prec forall_exists
    { Ast.Forall (V (None, v), s, p) }
*)
  | FORALL; v = IDENT; IN; s = var; p = protocol; %prec forall_exists
    { Ast.Forall (V (None, v), s, p) }
  | EXISTS; v = IDENT; IN; s = IDENT; DOT; p = protocol; %prec forall_exists
    { Ast.Exists (V (None, v), V (None, s), p) }
  | LPAREN; p = protocol; RPAREN; { p }