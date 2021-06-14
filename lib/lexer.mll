{
open Parser
exception SyntaxError
}

let digit = ['0'-'9']
let ident = ['a'-'z' 'A'-'Z'] ['a'-'z' 'A'-'Z' '0'-'9' '_']*
let num = (digit | ['1'-'9'] digit*)
let tabs = ['\t' ' ']

rule f = parse
  (* | spaces as s { SPACE (String.length s) } *)
  (* -1 for the newline *)
  (* | indent as s { Lexing.new_line lexbuf; INDENT (String.length s - 1) } *)
  | '\n' { Lexing.new_line lexbuf; f lexbuf }
  | tabs+ { f lexbuf }
  | num as n { INT (int_of_string n) }
  | "forall" { FORALL }
  | "exists" { EXISTS }
  | "in" { IN }
  | "true" { TRUE }
  | "false" { FALSE }
  | "and" { AND }
  | "or" { OR }
  | "invariant" { INVARIANT }
  | "protocol" { PROTOCOL }
  | "ltl" { LTL }
  | "timeout" { TIMEOUT }
  | "else" { ELSE }
  | ident as i { IDENT i }
  | "$" { DOLLAR }
  | "&" { AND }
  | "|" { OR }
  | "!" { NOT }
  | "." { DOT }
  | ";" { SEMI }
  | "||" { PAR }
  | "\\/" { DISJ }
  (* | "/\\" { CONJ } *)
  | ":" { COLON }
  | "," { COMMA }
  | "->" { ARROW }
  | "=>" { IF }
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
  | "{" { LCURLY }
  | "}" { RCURLY }
  | "[" { LBRACKET }
  | "]" { RBRACKET }
  | "<>" { DIAMOND }
  | "[]" { BOX }
  | '"' { STRING (string (Buffer.create 100) lexbuf) }
  | "//" { comments lexbuf }
  | _ { raise SyntaxError }
  | eof { EOF }

and comments = parse
  | '\n' { Lexing.new_line lexbuf; f lexbuf }
  | _ { comments lexbuf }

and string buf = parse
| [^'"' '\n' '\\']+
  { Buffer.add_string buf (Lexing.lexeme lexbuf); string buf lexbuf }
| '\n'
  { Buffer.add_string buf (Lexing.lexeme lexbuf); Lexing.new_line lexbuf; string buf lexbuf }
| '\\' '"'
  { Buffer.add_char buf '"'; string buf lexbuf }
| '\\'
  { Buffer.add_char buf '\\'; string buf lexbuf }
| '"'
  { Buffer.contents buf }
| eof
  { raise SyntaxError }
| _
  { raise SyntaxError }