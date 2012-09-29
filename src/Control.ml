open Printf

open Utils
open Syntax
open Normalize
open Semop
open Minim

let help_me = "\n\
Command summary:\n\
  def <name> = <proc>     -> register new (basic) definition\n\
  norm <proc>             -> normalize process\n\
  deriv <proc>            -> show derivatives of process\n\
  lts <proc>              -> show labelled transition system\n\
  mini <proc>             -> minimize process\n\
  struct <proc> == <proc> -> check structural congruence\n\
  bisim <proc> ~ <proc> -> check bisimilarity (slow)\n\
  fbisim <proc> ~ <proc> -> check bisimilarity (fast)\n\
---\n\
  :help                   -> this help message\n\
  :quit                   -> quit the program\n\
"

let handle_command = function
  | ":help" -> printf "%s\n%!" help_me;
  | ":quit" -> printf "bye bye !\n%!" ; exit 0
  | cmd -> printf "Unknown command: %s\n%!" cmd

let timing operation =
  let start_time = Sys.time()
  in let result = operation()
     in let end_time = Sys.time()
        in
        (result, end_time -. start_time) 

let handle_free proc =
  printf "%s\n" (string_of_set (fun v -> v) (freeNames proc))

let handle_bound proc =
  printf "%s\n" (string_of_set (fun v -> v) (boundNames proc))

let handle_names proc =
  printf "%s\n" (string_of_set (fun v -> v) (names proc))

let handle_normalization proc =
  printf "Normalize process...\n%!";
  let proc',time = timing (fun () -> normalize proc)
  in
  printf "%s\n%!" (string_of_nprocess proc') ;
  printf "(elapsed time=%fs)\n%!" time 

let handle_struct_congr p q =
  printf "Check structural congruence...\n%!";
  let ok, time = timing (fun () -> p === q)
  in
  (if ok
   then printf "the processes *are* structurally congruent\n%!"
   else printf "the processes are *not* structurally congruent\n%!") ;
  printf "(elapsed time=%fs)\n%!" time 

let global_definition_map = Hashtbl.create 64

let handle_deriv p =
  let op = fun () ->
    let np = normalize p in
    derivatives global_definition_map np 
  in
  let derivs, time = timing op
  in
  TSet.iter (fun t -> printf "%s\n" (string_of_derivative t)) derivs;
  printf "(elapsed time=%fs)\n%!" time 
  
let fetch_definition key =
  Hashtbl.find global_definition_map key

let register_definition def =
  Hashtbl.replace global_definition_map (string_of_def_header def) def

let handle_definition def =
  register_definition def;
  printf "Definition registered\n%!"

let dot_style_format (p, l, p') =
  sprintf "\"%s\" -> \"%s\" [ label = \"%s\", fontcolor=red ]"
    (string_of_nprocess p) (string_of_nprocess p') (string_of_label l)

let dot_style_format' (pl, l, pl') = 
  sprintf "\"%s\" -> \"%s\" [ label = \"%s\", fontcolor=red ]"
    (string_of_list string_of_nprocess pl)
    (string_of_list string_of_nprocess pl')
    (string_of_label l)

let handle_lts p =
  let transs, time = timing (fun () -> lts global_definition_map (normalize p)) 
  in
  List.iter (fun t -> printf "%s\n" (string_of_transition t)) transs;
  printf "\nGenerating lts.dot... %!";
  let nprocs =
    List.fold_left (fun acc (x, _, y) -> PSet.add x (PSet.add y acc))
      PSet.empty transs
  in
  let oc = open_out "lts.dot" in
  fprintf oc "digraph LTS {\n";
  PSet.iter
    (fun np ->
      fprintf oc "\"%s\" [ fontcolor=blue ]\n" (string_of_nprocess np))
    nprocs;
  if transs = [] then fprintf oc "  0\n" else
    List.iter (fun t -> fprintf oc "  %s\n" (dot_style_format t)) transs;
  fprintf oc "}\n";
  close_out oc;
  printf "done\n(elapsed time=%fs)\n%!" time

let handle_minimization proc =
  printf "Minimize process...\n%!";
  let transs, time = timing (fun () ->
    let p = normalize proc in
    minimize global_definition_map p) 
  in
  List.iter (fun t -> printf "%s\n" (string_of_transitions t)) transs;
  printf "\nGenerating lts_mini.dot... %!";
  let nprocs = 
    List.fold_left (fun acc (x, _, y) -> x::(y::acc)) [] transs
  in
  let oc = open_out "lts_mini.dot" in
  fprintf oc "digraph LTSMINI {\n";
  List.iter 
    (fun x -> fprintf oc "\"%s\" [ fontcolor=blue ]\n"
      (string_of_list string_of_nprocess x))
    nprocs;
  if transs = [] then fprintf oc "  0\n" else
    List.iter (fun t -> fprintf oc "  %s\n" (dot_style_format' t)) transs;
  fprintf oc "}\n";
  close_out oc;
  printf "done\n(elapsed time=%fs)\n%!" time

let handle_bisim p1 p2 =
  printf "Calculate bisimilarity (slow)...\n%!";
  let start_time = Sys.time()
  in
  let np1 = normalize p1 in
  let np2 = normalize p2 in
  try
    let bsm = construct_bisimilarity global_definition_map np1 np2 
    in
    let end_time = Sys.time()
    in
    let print (np1, np2) =
      printf "{ %s ; %s }\n" (string_of_nprocess np1) (string_of_nprocess np2)
    in
    printf "the processes are bisimilar\n(elapsed time=%fs)\n%!" (end_time-.start_time) ;
    BSet.iter print bsm
  with Failure "Not bisimilar" ->
    let end_time = Sys.time()
    in
    printf "the processes are *not* bisimilar\n(elapsed time=%fs)\n%!" (end_time-.start_time)

let handle_is_bisim p1 p2 =
  let ok,time = timing (fun () ->
    let np1 = normalize p1 in
    let np2 = normalize p2 in
    is_bisimilar global_definition_map np1 np2)
  in
  if ok 
  then printf "the processes *are* bisimilar\n(elapsed time=%fs)\n%!" time
    else printf "the processes are *not* bisimilar\n(elapsed time=%fs)\n%!" time

let handle_is_fbisim p1 p2 =
  let ok,time = timing (fun () ->
    let np1 = normalize p1 in
    let np2 = normalize p2 in
    is_fbisimilar global_definition_map np1 np2)
  in
  if ok
  then printf "the processes *are* bisimilar\n(elapsed time=%fs)\n%!" time
  else printf "the processes are *not* bisimilar\n(elapsed time=%fs)\n%!" time
