open Printf
open Utils

let version_str = "Pave' v.1 r20130910"
let usage = "Usage: pave <opt>"
let banner = 
"\n"^
"===============\n"^
"   .+------+                                         +------+.\n"^
" .' |    .'|   (P)ROCESS                             |`.    | `.\n"^
"+---+--+'  |             (A)LGEBRA                   |  `+--+---+\n"^
"|   |  |   |                        (VE')RIFIER      |   |  |   |\n"^
"|  ,+--+---+                                         +---+--+   |\n"^
"|.'    | .'   (C) 2009-2012 F.Peschanski              `. |   `. |\n"^
"+------+'                                               `+------+\n"^
"              released under the GPL (cf. LICENSE)\n"^
"===============\n"^
 version_str ^ "\n"

let load_file = ref None
let debug_mode = ref false

let () =  Arg.parse [
  ("-load", Arg.String (fun fname -> load_file := Some fname),
   "load commands from file")
  ; ("-debug", Arg.Set debug_mode,
     "debug mode")
  ; ("-version", Arg.Unit (fun () -> printf "%s\n%!" version_str ; exit 0),
     "print version information")
]
  (fun arg -> eprintf "Invalid argument: %s\n%!" arg ; exit 1)
  usage

let parse_error_msg lexbuf =
  let p = lexbuf.Lexing.lex_curr_p in
  let l = p.Lexing.pos_lnum in
  let c = p.Lexing.pos_cnum - p.Lexing.pos_bol in
  let tok = Lexing.lexeme lexbuf
  in
    printf "Parser error at line %d char %d: ~%s~\n%!" l c tok 

let main () = 
  printf "%s\n%!" banner;
  match !load_file with
  | None ->
      printf "Interactive mode... \n%!";
    Control.script_mode := false ;
    while true do
	printf "> %!";
      let lexbuf = Lexing.from_channel stdin in
	try
	  ignore (Parser.script Lexer.token lexbuf)
	with 
	| Failure msg -> printf "Failure: %s\n%!" msg
        | Fatal_Parse_Error(msg) ->
          parse_error_msg lexbuf ;
          printf " ==> %s\n%!" msg
	| Parsing.Parse_error -> 
          parse_error_msg lexbuf
	| End_of_file -> print_newline (); exit 0
    done
  | Some file ->
      printf "Loading file %s... \n%!" file;
    Control.script_mode := true ;
      let lexbuf = Lexing.from_channel (open_in file) in
      let rec loop () =
	let continue = 
	  try
	    Parser.script Lexer.token lexbuf
	  with 
	    | Failure msg -> printf "Failure: %s\n%!" msg ; true
            | Fatal_Parse_Error(msg) ->
              parse_error_msg lexbuf ;
              printf " ==> %s\n%!" msg ; true
	    | Parsing.Parse_error -> 
              parse_error_msg lexbuf ; true
	    | End_of_file -> false
	in
	  if continue then loop ();
      in
	loop ()

let () = main ()
