{
open Parser
}

let digit = ['0'-'9']
let ident = ['a'-'z' 'A'-'Z'] ['a'-'z' 'A'-'Z' '0'-'9' '_']*
let num = (digit | ['1'-'9'] digit*)
let spaces = ' '+
let indent = '\n' ' '*
(* let newline = '\n'+ *)
let tabs = ['\t']

rule f = parse
  | spaces as s { SPACE (String.length s) }
  (* -1 for the newline *)
  | indent as s { Lexing.new_line lexbuf; INDENT (String.length s - 1) }
  (* | newline { NEWLINE } *)
  | tabs+ { f lexbuf }
  | num as n { INT (int_of_string n) }
  | "forall" { FORALL }
  | "exists" { EXISTS }
  | "in" { IN }
  | "true" { TRUE }
  | "false" { FALSE }
  | "and" { AND }
  | "or" { OR }
  | ident as i { IDENT i }
  | "&" { AND }
  | "|" { OR }
  | "!" { NOT }
  | "." { DOT }
  | ";" { SEMI }
  | "||" { PAR }
  | "\\/" { DISJ }
  | ":" { COLON }
  | "," { COMMA }
  | "->" { ARROW }
  | "=>" { IF }
  | "=>*" { WHEN }
  | "=" { EQ }
  | "==" { EQEQ }
  | "+" { PLUS }
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
  | "//" { comments lexbuf }
  | eof { EOF }

and comments = parse
  | '\n' { Lexing.new_line lexbuf; f lexbuf }
  | _ { comments lexbuf }