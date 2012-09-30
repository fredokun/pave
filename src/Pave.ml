open Printf

let version_str = "Pave' v.1 r20120924"
let usage = "Usage: pave <opt>"
let banner = 
"\n"^
"===============\n"^
"   .+------+                                         +------+.\n"^
" .' |    .'|   (P)ROCESS                             |`.    | `.\n"^
"+---+--+'  |             (A)LGEBRA                   |  `+--+---+\n"^
"|   |  |   |                        (VE')RIFIER      |   |  |   |\n"^
"|  ,+--+---+                                         +---+--+   |\n"^
"|.'    | .'   (C) 2009-2012 F.Peschanski & B.Vaugon   `. |   `. |\n"^
"+------+'         & V.Membre' & A.Deharbe & J.Salvucci  `+------+\n"^
"              released under the GPL (cf. LICENSE)\n"^
"===============\n"^
 version_str ^ "\n"

let load_file = ref None;;
let debug_mode = ref false;;

Arg.parse [
  ("-load", Arg.String (fun fname -> load_file := Some fname),
   "load commands from file");
  ("-debug", Arg.Set debug_mode,
   "debug mode");
  ("-version", Arg.Unit (fun () -> printf "%s\n%!" version_str ; exit 0),
   "print version information")
]
  (fun arg -> eprintf "Invalid argument: %s\n%!" arg ; exit 1)
  usage;
;;

printf "%s\n%!" banner;;

match !load_file with
  | None ->
      printf "Interactive mode... \n%!";
    while true do
      let lexbuf = Lexing.from_channel stdin in
	printf "> %!";
	try
	  ignore (Parser.script Lexer.token lexbuf)
	with 
	| Failure msg -> printf "Lexing error: %s\n%!" msg
	| Parsing.Parse_error -> 
          let p = lexbuf.Lexing.lex_curr_p in
          let l = p.Lexing.pos_lnum in
          let c = p.Lexing.pos_cnum - p.Lexing.pos_bol in
            printf "Parser error at line %d char %d\n%!" l c   
    done
  | Some file ->
      printf "Loading file %s... \n%!" file;
      let lexbuf = Lexing.from_channel (open_in file) in
      let rec loop () =
	let continue = 
	  try
	    Parser.script Lexer.token lexbuf
	  with 
	    | Failure msg -> printf "Syntax error: %s\n%!" msg ; true
	    | Parsing.Parse_error -> 
              let p = lexbuf.Lexing.lex_curr_p in
              let l = p.Lexing.pos_lnum in
              let c = p.Lexing.pos_cnum - p.Lexing.pos_bol in
                printf "Parser error at line %d char %d\n%!" l c ; true  
	in
	  if continue then loop ();
      in
	loop ()
;;
