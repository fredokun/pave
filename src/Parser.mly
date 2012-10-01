/* header */
%{
  open Printf

  open Utils
  open Syntax


  let rec mkRes ns p = match ns with
    | [] -> p
    | n::ns' -> Res(n,(mkRes ns' p))

  let mkRename ns p = 
    let rec ren = function
    | [] -> p
    | (old,value) :: ns' -> Rename(old,value,(ren ns'))
    in
    ren (List.rev ns)  


(***
  let parse_error s = (* Called by the parser function on error *)
    print_endline s;
    flush stdout
    (* raise Parsing.Parse_error *)
***)
%}

/* reserved keywords */
%token DEF TRUE FALSE END NEW TAU DIV

/* identifiers */
%token <string> IDENT

/* commands */
%token <string> COMMAND
%token NORM
%token STRUCT
%token BISIM
%token FBISIM
%token DERIV
%token LTS
%token MINI
%token FREE
%token BOUND
%token NAMES

/* inturals */
%token <int> INT

/* punctuation */
%token LPAREN RPAREN LBRACKET RBRACKET COMMA EQUAL EQEQ TILD INTERG

/* operators */
%token PAR PLUS DOT OUT IN

%left PAR
%left PLUS
%right COMMA
%right RENAME
%left OUT IN

%nonassoc UNARY

/* end of statement */

%token SEMICOL EOF

  /* types */
%start script
%type <bool> script
%type <process> process
%type <prefix> prefix
%type <definition> definition

  /* grammar */
%%
    script:
  | EOF { false }
  | statement SEMICOL { true }
  | statement SEMICOL script { true }
  | statement error { raise (Fatal_Parse_Error "missing ';' after statement") }

      statement:
  | definition                     
      { Control.handle_definition $1 }
  | NORM process                   
      { Control.handle_normalization $2 }
  | NORM error     
      { raise (Fatal_Parse_Error "missing process to normalize") }
  | STRUCT process EQEQ process
      { Control.handle_struct_congr $2 $4 }
  | STRUCT process error
      { raise (Fatal_Parse_Error "missing '==' for structural congruence") }
  | STRUCT process EQEQ error
      { raise (Fatal_Parse_Error "missing process after '==' for structural congruence") }
  | STRUCT error 
      {raise (Fatal_Parse_Error "missing process before '==' for structural congruence") }
  | BISIM IN process TILD process 
      { Control.handle_is_bisim $3 $5 }
  | BISIM IN process error
      { raise (Fatal_Parse_Error "missing '~' for strong bisimilarity") }
  | BISIM IN process TILD error
      { raise (Fatal_Parse_Error "missing process after '~' for strong bisimilarity") }
  | BISIM process TILD process
      { Control.handle_bisim $2 $4 }
  | BISIM process error
      { raise (Fatal_Parse_Error "missing '~' for strong bisimilarity") }
  | BISIM process TILD error
      { raise (Fatal_Parse_Error "missing process after '~' for strong bisimilarity") }
  | BISIM error 
      { raise (Fatal_Parse_Error "missing '?' or process before '~' for strong bisimilarity") }
  | FBISIM IN process TILD process 
      { Control.handle_is_fbisim $3 $5 }
  | FBISIM IN process error
      { raise (Fatal_Parse_Error "missing '~' for strong bisimilarity") }
  | FBISIM IN process TILD error
      { raise (Fatal_Parse_Error "missing process after '~' for strong bisimilarity") }
  | FBISIM error 
      { raise (Fatal_Parse_Error "missing '?' or process before '~' for strong bisimilarity") }
  | DERIV process
      { Control.handle_deriv $2 }
  | DERIV error
      { raise (Fatal_Parse_Error "missing process to derivate") } 
  | LTS process
      { Control.handle_lts $2 }
  | LTS error
      { raise (Fatal_Parse_Error "missing process for LTS") } 
  | MINI process
      { Control.handle_minimization $2 }
  | MINI error
      {raise (Fatal_Parse_Error "missing process for minimization") } 
  | FREE process
      { Control.handle_free $2 }
  | FREE error
      { raise (Fatal_Parse_Error "missing process for free names") } 
  | BOUND process
      { Control.handle_bound $2 }
  | BOUND error
      { raise (Fatal_Parse_Error "missing process for bound names") } 
  | NAMES process
      { Control.handle_names $2 }
  | NAMES error
      { raise (Fatal_Parse_Error "missing process for names") } 
  | COMMAND
      { Control.handle_command $1 }

      process:
  | INT 
      { if $1 = 0 then Silent 
        else raise (Fatal_Parse_Error "Only 0 can be used as Silent process") }
  | END 
      { Silent }
  | prefix COMMA process 
      {  Prefix ($1,$3) }
  | prefix error
      { raise (Fatal_Parse_Error "missing ',' after prefix") }
  | prefix COMMA error
      { raise (Fatal_Parse_Error (sprintf "process missing after prefix '%s'" (string_of_prefix $1))) }
  | prefix { Prefix ($1,Silent) }
  | process PAR process {  Par($1,$3) }
  | process PAR error
      { raise (Fatal_Parse_Error "right-hand process missing in parallel") }      
  | process PLUS process { Sum($1,$3) }
  | process PLUS error
      { raise (Fatal_Parse_Error "right-hand process missing in sum") }
  | process error
      { raise (Fatal_Parse_Error "missing parallel '||' or sum '+' symbol after process"); }
  | NEW LPAREN list_of_names RPAREN %prec UNARY process { mkRes $3 $5 }
  | IDENT LPAREN list_of_values RPAREN { Call($1,$3) }
  | IDENT { Call($1,[]) }
  | %prec RENAME process LBRACKET list_of_renames RBRACKET { mkRename $3 $1 }
  | LPAREN process RPAREN { $2 }
  | LBRACKET process RBRACKET { $2 }

      prefix:
  | TAU       { Tau }
  | IDENT OUT { Out($1) }
  | IDENT IN  { In($1) }

      list_of_renames :
  | IDENT DIV IDENT { [($3,$1)] }
  | IDENT DIV IDENT COMMA list_of_renames { ($3,$1) :: $5 }

      list_of_names:
  | IDENT { [$1] }
  | IDENT COMMA list_of_names { $1::$3 }

      list_of_values:
  | /* empty */ { [] }
  | value list_of_values { $1::$2 }

      definition:
  | DEF IDENT LPAREN list_of_values RPAREN EQUAL process {Definition($2,$4,$7)}
  | DEF IDENT EQUAL process { Definition($2,[],$4) }

      value:
  | TRUE  { Bool true }
  | FALSE { Bool false }
  | INT   { Int $1 }
  | IDENT { Name $1 }

%%
(* end of grammar *)
