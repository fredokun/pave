
{ 
  open Parser
  let line=ref 1
}

let eol = '\n'
let ident = ['a'-'z''A'-'Z'] ['a'-'z''A'-'Z''0'-'9']*
let digit = ['0'-'9']
let int = (['1'-'9'] digit*)

let cmt = ('#' [^'\n']*)
  
let r_def = "def"
let r_true = "true"
let r_false = "false"
let r_end = "end"
let r_new = "new" | "nu"
let r_tau = "tau"
 
let op_dot = '.'
let op_plus = '+'
let op_par = "||"
let op_out = '!'
let op_in = '?'
let div = '/'
let lparen = '('
let rparen = ')'
let lbracket = '['
let rbracket = ']'
let comma = ','
let equal = '='
let eqeq = "=="
let tild = "~"
let semicol = ";"
let ws = (['\t' ' ']*)
let command = (':' ident)
let cmd_norm = "norm"
let cmd_struct = "struct"
let cmd_bisim = "bisim"
let cmd_fbisim = "fbisim"
let cmd_deriv = "deriv"
let cmd_lts = "lts"
let cmd_mini = "mini"
let cmd_free = "free"
let cmd_bound = "bound"
let cmd_names = "names"

  rule token = parse
    | ws
	{token lexbuf}
    | eol                                
	{ incr line;
	  token lexbuf }
    | cmt
	{token lexbuf}
    | digit as n
	{ INT(int_of_string (Char.escaped n)) }
    | int as n
	{ INT(int_of_string n) }
    | r_def { DEF }
    | r_true { TRUE }
    | r_false { FALSE }
    | r_end { END }
    | r_new { NEW }
    | r_tau { TAU }
    | op_dot { DOT } 
    | op_plus { PLUS } 
    | op_par { PAR }
    | op_out { OUT }
    | op_in { IN }
    | div { DIV }
    | lparen { LPAREN }
    | rparen { RPAREN }
    | lbracket { LBRACKET }
    | rbracket { RBRACKET }
    | comma { COMMA }
    | semicol { EOF }
    | tild { TILD }
    | eqeq { EQEQ }
    | equal { EQUAL }
    | cmd_norm { NORM }
    | cmd_struct { STRUCT }
    | cmd_bisim { BISIM }
    | cmd_fbisim { FBISIM }
    | cmd_deriv { DERIV }
    | cmd_lts { LTS }
    | cmd_mini { MINI }
    | cmd_free { FREE }
    | cmd_bound { BOUND }
    | cmd_names { NAMES }
    | command as cmd
	{ COMMAND (cmd) }
    | ident as id                   
	{ IDENT (id) }
    | eof { EOF }
    | _ { failwith((Lexing.lexeme lexbuf) ^ 
		      ": mistake at line " ^ string_of_int !line)}
	
	{
	}
