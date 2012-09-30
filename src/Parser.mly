/* header */
%{
  open Syntax

  open Printf

  let rec mkRes ns p = match ns with
    | [] -> p
    | n::ns' -> Res(n,(mkRes ns' p))

  let mkRename ns p = 
    let rec ren = function
    | [] -> p
    | (old,value) :: ns' -> Rename(old,value,(ren ns'))
    in
    ren (List.rev ns)  


  let parse_error s = (* Called by the parser function on error *)
    print_endline s;
    flush stdout
    (* raise Parsing.Parse_error *)
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
  | definition                     
      { Control.handle_definition $1 }
  | NORM process                   
      { Control.handle_normalization $2 }
  | NORM error     
      { printf "Parse error: missing process to normalize\n%!"; 
        (* raise Parsing.Parse_error *) }
  | STRUCT process EQEQ process
      { Control.handle_struct_congr $2 $4 }
  | STRUCT process error
      { printf "Parse error: missing '==' for structural congruence\n%!";
        (* raise Parsing.Parse_error *) }
  | STRUCT process EQEQ error
      { printf "Parse error: missing process after '==' for structural congruence\n%!";
        (* raise Parsing.Parse_error *) }
  | STRUCT error 
      { printf "Parse error: missing process before '==' for structural congruence\n%!";
        (* raise Parsing.Parse_error *) }
  | BISIM IN process TILD process 
      { Control.handle_is_bisim $3 $5 }
  | BISIM IN process error
      { printf "Parse error: missing '~' for strong bisimilarity\n%!";
        (* raise Parsing.Parse_error *) }
  | BISIM IN process TILD error
      { printf "Parse error: missing process after '~' for strong bisimilarity\n%!";
        (* raise Parsing.Parse_error *) }
  | BISIM process TILD process
      { Control.handle_bisim $2 $4 }
  | BISIM process error
      { printf "Parse error: missing '~' for strong bisimilarity\n%!";
        (* raise Parsing.Parse_error *) }
  | BISIM process TILD error
      { printf "Parse error: missing process after '~' for strong bisimilarity\n%!";
        (* raise Parsing.Parse_error *) }
  | BISIM error 
      { printf "Parse error: missing '?' or process before '~' for strong bisimilarity\n%!";
        (* raise Parsing.Parse_error *) }
  | FBISIM IN process TILD process { Control.handle_is_fbisim $3 $5 }
  | FBISIM IN process TILD process 
      { Control.handle_is_fbisim $3 $5 }
  | FBISIM IN process error
      { printf "Parse error: missing '~' for strong bisimilarity\n%!";
        (* raise Parsing.Parse_error *) }
  | FBISIM IN process TILD error
      { printf "Parse error: missing process after '~' for strong bisimilarity\n%!";
        (* raise Parsing.Parse_error *) }
  | DERIV process
      { Control.handle_deriv $2 }
  | DERIV error
      { printf "Parse error: missing process to derivate\n%!"; 
        (* raise Parsing.Parse_error *) }
  | LTS process
      { Control.handle_lts $2 }
  | LTS error
      { printf "Parse error: missing process for LTS\n%!"; 
        (* raise Parsing.Parse_error *) }
  | MINI process
      { Control.handle_minimization $2 }
  | MINI error
      { printf "Parse error: missing process for minimization\n%!"; 
        (* raise Parsing.Parse_error *) }
  | FREE process
      { Control.handle_free $2 }
  | FREE error
      { printf "Parse error: missing process for free names\n%!"; 
        (* raise Parsing.Parse_error *) }
  | BOUND process
      { Control.handle_bound $2 }
  | BOUND error
      { printf "Parse error: missing process for bound names\n%!"; 
        (* raise Parsing.Parse_error *) }
  | NAMES process
      { Control.handle_names $2 }
  | NAMES error
      { printf "Parse error: missing process for names\n%!"; 
        (* raise Parsing.Parse_error *) }
  | COMMAND
      { Control.handle_command $1 }

      process:
  | INT { if $1 = 0 then Silent else failwith "Only 0 at end" }
  | END { Silent }
  | prefix COMMA process {  Prefix ($1,$3) }
  | prefix error
      { printf "HERE HERE HERE !\n%!" ;
        parse_error "Parse error: missing ',' after prefix\n%!" ;
        raise Parsing.Parse_error }
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
