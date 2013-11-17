open Printf
open Global
open Utils
open Syntax
open Normalize
open Semop
open Minim

let help_me = "\n\
Command summary:\n\
  def <name> = <proc>     -> register new definition\n\
  free <proc>             -> free names of process\n\
  bound <proc>            -> bound names of process\n\
  names <proc>            -> names of process\n\
  norm <proc>             -> normalize process\n\
  deriv <proc>            -> show derivatives of process\n\
  lts <proc>              -> show labelled transition system\n\
  struct <proc> == <proc> -> check structural congruence\n\
  bisim <proc> ~ <proc>   -> calculate bisimilarity\n\
  bisim ? <proc> ~ <proc> -> check bisimilarity (slow)\n\
  fbisim ? <proc> ~ <proc> -> check bisimilarity (fast)\n\
  mini <proc>             -> minimize process\n\
  \n\
  wderiv <proc>            -> show weak derivatives of process\n\
  tderiv <proc>            -> show silent derivatives of process\n\
  wbisim <proc> ~~ <proc>   -> calculate weak bisimilarity\n\
  wbisim ? <proc> ~~ <proc> -> check weak bisimilarity (slow)\n\
  wlts <proc>              -> show labelled transition system\n\
  wmini <proc>             -> minimize process\n\
  wfbisim ? <proc> ~~ <proc> -> check weak bisimilarity (fast)\n\
---\n\
  help                   -> this help message\n\
  quit                   -> quit the program\n\
"

let script_mode = ref false ;;


exception Constdef_Exception of string ;;
exception Typedef_Exception of string ;;

let handle_help () =
  printf "%s\n> %!" help_me

let handle_quit () =
  printf "bye bye !\n%!" ;
  exit 0

let timing operation =
  let start_time = Sys.time()
  in let result = operation()
     in let end_time = Sys.time()
        in
        (result, end_time -. start_time)

let handle_constdef (const_name:string) (const_val:int) =
  (* printf "(handle_constdef %s %d)\n%!" const_name const_val ; *)
  if not (SMap.mem const_name !Presyntax.env_const) then
    Presyntax.env_const := SMap.add const_name const_val !Presyntax.env_const
  else
    raise (Constdef_Exception const_name)
;;

let handle_typedef_range (type_name:string) (min_val:string) (max_val:string) =
  (* printf "(handle_typedef_range %s %s %s)\n%!" type_name min_val max_val ; *)
  if not (SMap.mem type_name !Presyntax.env_type) then
    let find_val v =
      try
	SMap.find v !Presyntax.env_const
      with
	Not_found ->
	  try
	    int_of_string v
	  with
	    Failure _ -> raise (Typedef_Exception type_name)
    in
    let min = find_val min_val
    and max = find_val max_val in

    Presyntax.add_to_env_type type_name
      ( if min < max then
	  Presyntax.PTDefRange (type_name, min, max)
	else
	  Presyntax.PTDefRange (type_name, max, min)
      )
  else
    raise (Typedef_Exception type_name)
;;

let handle_typedef_enum (type_name:string) (names:string list) =
  (* printf "(handle_typedef_enum %s %s)\n%!" type_name (string_of_list (fun x->x) names) ; *)
  let rec list2set l =
    match l with
    | [] -> SSet.empty
    | hd::tl -> SSet.add hd (list2set tl)
  in
  if not (SMap.mem type_name !Presyntax.env_type) then
    Presyntax.add_to_env_type type_name ( Presyntax.PTDefEnum (type_name, list2set names) )
  else
    raise (Typedef_Exception type_name)
;;

let handle_free proc =
  if !script_mode then
    printf "> free %s\n%!" (string_of_process proc) ;
  printf "%s\n%!" (string_of_set (fun v -> v) (freeNames proc))

let handle_bound proc =
  if !script_mode then
    printf "> bound %s\n%!" (string_of_process proc) ;
  printf "%s\n%!" (string_of_set (fun v -> v) (boundNames proc))

let handle_names proc =
  if !script_mode then
    printf "> names %s\n%!" (string_of_process proc) ;
  printf "%s\n%!" (string_of_set (fun v -> v) (names proc))

let handle_normalization proc =
  if !script_mode then
    printf "> norm %s\n%!" (string_of_process proc) ;
  printf "Normalize process...\n%!";
  let proc',time = timing (fun () -> normalize proc)
  in
  printf "%s\n%!" (string_of_nprocess proc') ;
  printf "(elapsed time=%fs)\n%!" time

let handle_struct_congr p q =
  if !script_mode then
    printf "> struct %s == %s\n%!" (string_of_process p) (string_of_process q) ;
  printf "Check structural congruence...\n%!";
  let ok, time = timing (fun () -> p === q)
  in
  (if ok
   then printf "the processes *are* structurally congruent\n%!"
   else printf "the processes are *not* structurally congruent\n%!") ;
  printf "(elapsed time=%fs)\n%!" time

let common_deriv f_deriv f_print str str2 p =
  if !script_mode then
    printf "> %s %s\n%!" str (string_of_process p) ;
  printf "Compute %s...\n%!" str2;
  let op = fun () ->
    let np = normalize p in
    f_deriv global_definition_map np
  in
  let derivs, time = timing op
  in
  f_print derivs;
  printf "(elapsed time=%fs)\n%!" time

let fetch_definition key =
  Hashtbl.find global_definition_map key

let register_definition def =
  Hashtbl.replace global_definition_map (string_of_def_header def) def

let handle_definition def =
  if !script_mode then
    printf "> %s\n%!" (string_of_definition def) ;
  register_definition def;
  printf "Definition '%s' registered\n%!" (def_name def)

let dot_style_format (p, l, p') =
  sprintf "\"%s\" -> \"%s\" [ label = \"%s\", fontcolor=red ]"
    (string_of_nprocess p) (string_of_nprocess p') (string_of_label l)

let dot_style_format' (pl, l, pl') =
  sprintf "\"%s\" -> \"%s\" [ label = \"%s\", fontcolor=red ]"
    (string_of_list string_of_nprocess pl)
    (string_of_list string_of_nprocess pl')
    (string_of_label l)

let common_lts f str p =
  if !script_mode then
    printf "> %s %s\n%!" str (string_of_process p) ;
  let transs, time = timing (fun () -> f global_definition_map (normalize p))
  in
  List.iter (fun t -> printf "%s\n" (string_of_transition t)) transs;
  printf "\nGenerating %s.dot... %!" str;
  let nprocs =
    List.fold_left (fun acc (x, _, y) -> PSet.add x (PSet.add y acc))
      PSet.empty transs
  in
  let oc = open_out (sprintf "%s.dot" str ) in
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

let common_minimization f_deriv str proc =
  if !script_mode then
    printf "> %s %s\n%!" str (string_of_process proc) ;
  printf "Minimize process...\n%!";
  let transs, time = timing (fun () ->
    let p = normalize proc in
    minimize f_deriv global_definition_map p)
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


let common_bisim f_bisim str str2 str3 p1 p2 =
  if !script_mode then
    printf "> %s %s ~ %s\n%!" str (string_of_process p1) (string_of_process p2) ;
  printf "Calculate %s...\n%!" str2;
  let start_time = Sys.time()
  in
  let np1 = normalize p1 in
  let np2 = normalize p2 in
  try
    let bsm = f_bisim global_definition_map np1 np2
    in
    let end_time = Sys.time()
    in
    let print (np1, np2) =
      printf "{ %s ; %s }\n" (string_of_nprocess np1) (string_of_nprocess np2)
    in
    printf "the processes are %s\n(elapsed time=%fs)\n%!" str3 (end_time-.start_time) ;
    BSet.iter print bsm
  with Failure "Not bisimilar" ->
    let end_time = Sys.time()
    in
    printf "the processes are *not* %s\n(elapsed time=%fs)\n%!" str3 (end_time-.start_time)

let common_is_bisim f_bisim str str2 p1 p2 =
  if !script_mode then
    printf "> %s ? %s ~ %s\n%!" str (string_of_process p1) (string_of_process p2) ;
  let ok,time = timing (fun () ->
    let np1 = normalize p1 in
    let np2 = normalize p2 in
    f_bisim global_definition_map np1 np2)
  in
  if ok
  then printf "the processes *are* %s\n(elapsed time=%fs)\n%!" str2 time
  else printf "the processes are *not* %s\n(elapsed time=%fs)\n%!" str2 time

let common_is_fbisim f_deriv str1 str2 p1 p2 =
if !script_mode then
    printf "> %s ? %s ~ %s\n%!" str1 (string_of_process p1) (string_of_process p2) ;
  let ok,time = timing (fun () ->
    let np1 = normalize p1 in
    let np2 = normalize p2 in
    is_fbisimilar f_deriv global_definition_map np1 np2)
  in
  if ok
  then printf "the processes *are* %s\n(elapsed time=%fs)\n%!" str2 time
  else printf "the processes are *not* %s\n(elapsed time=%fs)\n%!" str2 time

(* On a factorisé les handlers  *)

let handle_lts p = common_lts (lts derivatives) "lts" p

let handle_wlts p = common_lts (lts (weak_transitions false)) "wlts" p


let handle_minimization p = common_minimization derivatives "mini" p

let handle_wminimization p = common_minimization (weak_transitions false) "wmini" p


let handle_bisim p1 p2 = common_bisim construct_bisimilarity "bisim" "bisimilarity" "bisimilar" p1 p2

let handle_wbisim p1 p2 = common_bisim construct_weak_bisimilarity "wbisim" "weak bisimilarity" "weakly bisimilar" p1 p2


let handle_is_bisim p1 p2 = common_is_bisim is_bisimilar "bisim" "bisimilar" p1 p2

let handle_is_fbisim p1 p2 = common_is_fbisim derivatives "fbisim" "bisimilar" p1 p2

let handle_is_wbisim p1 p2 = common_is_bisim is_weakly_bisimilar "wbisim" "weakly bisimilar" p1 p2

let handle_is_fwbisim p1 p2 = common_is_fbisim (weak_transitions false) "wfbisim" "weakly bisimilar" p1 p2

let handle_deriv p = common_deriv derivatives (TSet.iter (fun t -> printf "%s\n" (string_of_derivative t))) "deriv" "derivatives" p

let handle_wderiv p = common_deriv (weak_derivatives false) printPfixMap "wderiv" "weak derivatives" p

let handle_tderiv p = common_deriv (weak_derivatives true) printPfixMap "tderiv" "tau derivatives" p


(*** Mu-Calculus part *)

let handle_prop name idents formula =
  Formula.add_prop name idents formula(* ; *)
  (* ignore (Check.bdd_of_formula formula name) *)

let handle_check_local =
  Check.handle_check_local

let handle_check_global _ _ = failwith "TODO: handle_check_global"
