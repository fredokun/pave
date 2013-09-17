
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
let r_when = "when"

let r_not = "not"
let r_and = "and"
let r_or = "or"
let r_if = "if"
let r_then = "then"
let r_else = "else"

let r_const = "const"
let r_type = "type"

let const = ('%' ident)
let var = ('$' ident)

let op_mod = '%'
let dollar = '$'
let op_dot = '.'
let dotdot = ".."
let op_plus = '+'
let op_par = "||"
let op_out = '!'
let op_in = '?'
let op_div = '/'
let op_mult = "*"
let op_minus = "-"

let lparen = '('
let rparen = ')'
let lbracket = '['
let rbracket = ']'
let laccol = '{'
let raccol = '}'
let comma = ','
let equal = '='
let eqeq = "=="
let inf = '<'
let infeq = "<="
let sup = '>'
let supeq = ">="
let diff = "<>"
let tild = "~"
let semicol = ";"
let ws = (['\t' ' ']*)
let colon = ':'

let implies_1 = "==>"
let implies_2 = "=>"

let cmd_help = "help"
let cmd_quit = "quit"
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

let cmd_wderiv = "wderiv"
let cmd_tderiv = "tderiv"
let cmd_wbisim = "wbisim"
let cmd_wlts = "wlts"
let cmd_wmini = "wmini"
let cmd_wfbisim = "wfbisim"

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
    | const as n
        { CONST(n) }
    | var as n
        { VAR(n) }
    | r_def { DEF }
    | r_true { TRUE }
    | r_false { FALSE }
    | r_end { END }
    | r_new { NEW }
    | r_when { WHEN }
    | r_tau { TAU }
    | r_not { NOT }
    | r_and { AND }
    | r_or { OR }
    | r_if { IF }
    | r_then { THEN }
    | r_else { ELSE }
    | r_const { CONSTDEF }
    | r_type { TYPEDEF }
    | dotdot { DOTDOT }
    | op_dot { DOT } 
    | op_plus { PLUS } 
    | op_minus { MINUS }
    | op_par { PAR }
    | op_out { OUT }
    | op_in { IN }
    | op_div { DIV }
    | op_mod { MOD }
    | inf { INF }
    | sup { SUP }
    | infeq { INFEQ }
    | supeq { SUPEQ }
    | diff { DIFF }
    | colon { COLON }
    | lparen { LPAREN }
    | rparen { RPAREN }
    | lbracket { LBRACKET }
    | rbracket { RBRACKET }
    | laccol { LACCOL }
    | raccol { RACCOL }
    | comma { COMMA }
    | semicol { SEMICOL }
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
	
    | implies_1 { IMPLIES }
    | implies_2 { IMPLIES }

    | cmd_wderiv { WDERIV }
    | cmd_tderiv { TDERIV }
    | cmd_wbisim { WBISIM }
    | cmd_wlts { WLTS }
    | cmd_wmini { WMINI }
    | cmd_wfbisim { WFBISIM }
    
    | cmd_help { HELP }
    | cmd_quit { QUIT }
    | ident as id                   
	{ IDENT (id) }
    | eof { EOF }
    | _ { failwith((Lexing.lexeme lexbuf) ^ 
		      ": mistake at line " ^ string_of_int !line)}
	
	{
	}
