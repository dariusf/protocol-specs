%{
  open Ast
%}

%token EOF
%token LPAREN RPAREN COLON COMMA
%token AND OR NOT PLUS MINUS SETMINUS DIV LT LE GT GE EQEQ NEQ
%token BOX DIAMOND IMPLIES
%token TRUE FALSE LBRACKET RBRACKET LCURLY RCURLY
%token TIMEOUT ELSE
%token <int> INT
%token <string> IDENT
%token <string> STRING
%token FORALL EXISTS IN DOT IF WHEN DISJ SEMI PAR ARROW EQ STAR DOLLAR
%token INVARIANT LTL PROTOCOL

%left PAR DISJ
(* this also resolves shift/reduce conflicts with par/disj/semi, has to be before (lower than) semi *)
%right IF WHEN
(* this resolves the shift/reduce conflict caused by forall protocol; protocol in favour of shifting (negation of case 1 in 6.1 of the menhir manual) if this is before semi (try moving it after to see the effect). it's given a name because we don't want to use the rightmost terminal to figure out that production's precedence level *)
%right forall_exists
%left SEMI (* this being after if/when makes it the reverse of what ocaml does: semicolons get nested inside conditionals  *)

(* keep in sync with the table in Print *)
%nonassoc BOX DIAMOND
%right IMPLIES
%left OR
%left AND
%left EQEQ NEQ
%left LT LE GT GE
%left PLUS MINUS SETMINUS
%left DIV STAR
%nonassoc NOT

%start <protocol> p
%start <spec> spec

%%

spec : sa = list(spec_decl); p = protocol; sb = list(spec_decl); EOF
  { { decls = sa @ sb; protocol = p } }

spec_decl :
  | INVARIANT; LPAREN; i = expr; RPAREN
    { Invariant i }
  | LTL; LPAREN; i = expr; RPAREN
    { Ltl i }
  | PROTOCOL; name = IDENT; args = delimited(LPAREN, separated_list(COMMA, IDENT), RPAREN); LPAREN; pr = protocol; RPAREN;
    { Function (name, args, pr) }

p :
  | pr = protocol; EOF { pr }

protocol :
  | v = var; EQ; e = expr;
    { p_with_pos $startpos $endpos (Assign (v, e)) }
  | p1 = var; ARROW; p2 = var; COLON; m = IDENT; args = loption(delimited(LPAREN, separated_nonempty_list(COMMA, msg_kvp), RPAREN));
    { p_with_pos $startpos $endpos (Send { from = p1; to_ = p2; msg = Message { typ = m; args = args } }) }
  | DOLLAR; f = IDENT; args = loption(delimited(LPAREN, separated_list(COMMA, expr), RPAREN));
    { p_with_pos $startpos $endpos (Call (f, args)) }
  | p1 = protocol; SEMI; p2 = protocol;
    { p_with_pos $startpos $endpos (Seq [p1; p2]) }
  | p1 = protocol; PAR; p2 = protocol;
    { p_with_pos $startpos $endpos (Par [p1; p2]) }
  | p1 = protocol; DISJ; p2 = protocol;
    { p_with_pos $startpos $endpos (Disj (p1, p2)) }
  | b = expr; IF; p = protocol;
    { p_with_pos $startpos $endpos (Imply (b, p)) }
  | b = expr; WHEN; p = protocol;
    { p_with_pos $startpos $endpos (BlockingImply (b, p)) }
  | FORALL; v = var; IN; s = var; p = protocol; %prec forall_exists
    { p_with_pos $startpos $endpos (Forall (v, s, p)) }
  | FORALL; v = var; IN; LPAREN; s = expr; RPAREN; p = protocol; %prec forall_exists
    { p_with_pos $startpos $endpos (Forall (v, s, p)) }
  | EXISTS; v = var; IN; s = var; p = protocol; %prec forall_exists
    { p_with_pos $startpos $endpos (Exists (v, s, p)) }
  | LPAREN; p = protocol; RPAREN;
    { p }

expr :
  | n = INT; { with_pos $startpos $endpos (Int n) }

  | s = STRING; { with_pos $startpos $endpos (String s) }
  | TIMEOUT; { with_pos $startpos $endpos Timeout }
  | ELSE; { with_pos $startpos $endpos Else }

  | i = IDENT;
    { with_pos $startpos $endpos (Var (V (None, i))) }
  | p = IDENT; DOT; i = IDENT;
    { with_pos $startpos $endpos (Var (V (Some (Party p), i))) }
  | f = IDENT; args = delimited(LPAREN, separated_list(COMMA, expr), RPAREN)
    { with_pos $startpos $endpos (App (f, args)) }

  (* ugh using the macros causes shift/reduce conflicts but inlining this doesn't! *)
  (*
  | party = terminated(IDENT?, DOT); i = IDENT;
    { Var (V (Option.map (fun p -> Party p) party, i)) }
*)

  | TRUE; { with_pos $startpos $endpos (Bool true) }
  | FALSE; { with_pos $startpos $endpos (Bool false) }
  | a = expr; o = binop; b = expr; { with_pos $startpos $endpos (App (o, [a; b])) }
  | u = unop; e = expr; { with_pos $startpos $endpos (App (u, [e])) }
  | es = delimited(LCURLY, separated_list(COMMA, expr), RCURLY) { with_pos $startpos $endpos (Set es) }
  | es = delimited(LBRACKET, separated_nonempty_list(COMMA, expr), RBRACKET) { with_pos $startpos $endpos (List es) }
  (* empty set/map are ambiguous *)
  | es = delimited(LCURLY, separated_nonempty_list(COMMA, map_kvp), RCURLY) { with_pos $startpos $endpos (Map es) }
  | LPAREN; e = expr; RPAREN; { e }

var :
  | var = IDENT;
    { with_pos $startpos $endpos (Var (V (None, var))) }
  | party = IDENT; DOT; var = IDENT;
    { with_pos $startpos $endpos (Var (V (Some (Party party), var))) }

msg_kvp :
  | v = var; EQ; e = expr; { (v, e) }

%inline binop :
  | PLUS { "+" }
  | MINUS { "-" }
  | SETMINUS { "\\" }
  | STAR { "*" }
  | DIV { "/" }
  | AND { "&" }
  | EQEQ { "==" }
  | NEQ { "!=" }
  | OR { "|" }
  | GT { ">" }
  | GE { ">=" }
  | LT { "<" }
  | LE { "<=" }
  | IMPLIES { "==>" }

%inline unop :
  | NOT { "!" }
  | DIAMOND { "<>" }
  | BOX { "[]" }

map_kvp :
  | v = IDENT; COLON; e = expr; { (v, e) }
