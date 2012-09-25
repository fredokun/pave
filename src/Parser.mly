/* header */
%{
  open Syntax

  let rec mkRes ns p = match ns with
    | [] -> p
    | n::ns' -> Res(n,(mkRes ns' p))

  let rec mkRename ns p = match ns with
    | [] -> p
    | (old,value) :: ns' -> Rename(old,value,(mkRename ns' p))
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

/* inturals */
%token <int> INT

/* punctuation */
%token LPAREN RPAREN LBRACKET RBRACKET COMMA EQUAL EQEQ TILD INTERG

/* operators */
%token PAR PLUS DOT OUT IN

%left PAR
%left PLUS
%right COMMA
%left OUT IN

%nonassoc UNARY

/* end of file */

%token EOF

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
  | statement script { true }

statement:
  | definition                     { Control.handle_definition $1 }
  | NORM process                   { Control.handle_normalization $2 }
  | STRUCT process EQEQ process    { Control.handle_struct_congr $2 $4 }
  | BISIM process TILD process    { Control.handle_bisim $2 $4 }
  | BISIM IN process TILD process { Control.handle_is_bisim $3 $5 }
  | FBISIM IN process TILD process { Control.handle_is_fbisim $3 $5 }
  | DERIV process                  { Control.handle_deriv $2 }
  | LTS process                    { Control.handle_lts $2 }
  | MINI process                   { Control.handle_minimization $2 }
  | COMMAND                        { Control.handle_command $1 }

process:
  | INT { if $1 = 0 then Silent else failwith "Only 0 at end" }
  | END { Silent }
  | prefix COMMA process {  Prefix ($1,$3) }
  | prefix { Prefix ($1,Silent) }
  | process PAR process {  Par($1,$3) }
  | process PLUS process { Sum($1,$3) }
  | NEW LPAREN list_of_names RPAREN %prec UNARY process { mkRes $3 $5 }
  | IDENT LPAREN list_of_values RPAREN { Call($1,$3) }
  | IDENT { Call($1,[]) }
  | LPAREN process RPAREN LBRACKET list_of_renames RBRACKET { mkRename $5 $2 }
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
