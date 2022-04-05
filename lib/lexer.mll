{
open Parser
exception SyntaxError
}

let digit = ['0'-'9']
let ident = ['_' 'a'-'z' 'A'-'Z'] ['a'-'z' 'A'-'Z' '0'-'9' '_']*
let num = (digit | ['1'-'9'] digit*)
let tabs = ['\t' ' ']

rule token = parse
  (* | spaces as s { SPACE (String.length s) } *)
  (* -1 for the newline *)
  (* | indent as s { Lexing.new_line lexbuf; INDENT (String.length s - 1) } *)
  | '\n' { Lexing.new_line lexbuf; token lexbuf }
  | tabs+ { token lexbuf }
  | num as n { INT (int_of_string n) }
  | "forall" { FORALL }
  | "exists" { EXISTS }
  | "for" { FOR }
  | "in" { IN }
  | "true" { TRUE }
  | "false" { FALSE }
  | "and" { AND }
  | "or" { OR }
  | "invariant" { INVARIANT }
  | "party" { PARTY }
  | "protocol" { PROTOCOL }
  | "ltl" { LTL }
  | "if" { IF }
  | "then" { THEN }
  | "else" { ELSE }
  | "end" { END }
  | "let" { LET }
  | "always" { BOX }
  | "eventually" { DIAMOND }
  | ident as i { IDENT i }
  | "$" { DOLLAR }
  | "&" { AND }
  | "|" { OR }
  | "!" { NOT }
  | "." { DOT }
  | ";" { SEMI }
  | "||" { PAR }
  | "\\/" { DISJ }
  | "\\" { SETMINUS }
  (* | "/\\" { CONJ } *)
  | ":" { COLON }
  | "," { COMMA }
  | "->" { ARROW }
  | "=>" { COND }
  | "==>" { IMPLIES }
  | "=>*" { WHEN }
  | "=" { EQ }
  | "==" { EQEQ }
  | "!=" { NEQ }
  | "+" { PLUS }
  | "*" { STAR }
  | "-" { MINUS }
  | "/" { DIV }
  | ">" { GT }
  | ">=" { GE }
  | "<" { LT }
  | "<=" { LE }
  | "(" { LPAREN }
  | ")" { RPAREN }
  | "{{" { LCURLY2 }
  | "}}" { RCURLY2 }
  | "<<" { LANGLE2 }
  | ">>" { RANGLE2 }
  | "{" { LCURLY }
  | "}" { RCURLY }
  | "[" { LBRACKET }
  | "]" { RBRACKET }
  | "?" { QUESTION }
  | "<>" { DIAMOND }
  (* conflict with empty list; consider using always *)
  | "[]" { BOX }
  | '"' { STRING (string `Double (Buffer.create 100) lexbuf) }
  | '\'' { STRING (string `Single (Buffer.create 100) lexbuf) }
  | "//" { comments lexbuf }
  | _ { raise SyntaxError }
  | eof { EOF }

and comments = parse
  | '\n' { Lexing.new_line lexbuf; token lexbuf }
  | _ { comments lexbuf }

and string which buf = parse
| [^'"' '\'' '\n' '\\']+
  { Buffer.add_string buf (Lexing.lexeme lexbuf); string which buf lexbuf }
| '\n'
  { Buffer.add_string buf (Lexing.lexeme lexbuf); Lexing.new_line lexbuf; string which buf lexbuf }
| '\\' '"'
  { Buffer.add_char buf '"'; string which buf lexbuf }
| '\\' '\''
  { Buffer.add_char buf '\''; string which buf lexbuf }
| '\\'
  { Buffer.add_char buf '\\'; string which buf lexbuf }
| '"'
  { match which with | `Double -> Buffer.contents buf | `Single -> Buffer.add_char buf '"'; string which buf lexbuf }
| '\''
  { match which with | `Single -> Buffer.contents buf | `Double -> Buffer.add_char buf '\''; string which buf lexbuf }
| eof
  { raise SyntaxError }
| _
  { raise SyntaxError }