open Printf
open Utils
open Syntax
open Normalize

let rand_proc n =
  let rec f i vars =
    if i = 0 then Silent else
      let rand_var () = List.nth vars (Random.int (List.length vars)) in
	match Random.int (if i = 1 then 2 else 4) with
	  | 0 ->
	      let pref =
		if Random.int 4 = 0 then Tau
		else if Random.bool () then In (rand_var ())
		else Out (rand_var ())
	      in
		Prefix (pref, f (pred i) vars)
	  | 1 ->
	      let name =
		if Random.bool () then rand_var ()
		else
		  let s = String.create 1 in
		    s.[0] <- char_of_int (int_of_char 'a' + Random.int 26);
		    s
	      in
		Res (name, f (pred i) (name :: vars))
	  | 2 ->
	      let left_i = Random.int (pred i) in
	      let right_i = i - left_i - 1 in
		Sum (f left_i vars, f right_i vars)
	  | 3 ->
	      let left_i = Random.int (pred i) in
	      let right_i = i - left_i - 1 in
		Par (f left_i vars, f right_i vars)
	  | _ -> assert false
  in
    if n < 0 then invalid_arg "rand_proc";
    f n [ "a" ; "b" ; "c" ; "d" ; "e" ]
;;

let rec perm_saps proc =
  let rand_list l =
    let a = Array.of_list l in
    let len = Array.length a in
      for i = 0 to pred len do
	let r = Random.int len in
	let x = a.(i) in
	  a.(i) <- a.(r);
	  a.(r) <- x;
      done;
      a
  in
  let rec search_sums = function
    | Sum (proc1, proc2) -> search_sums proc1 @ search_sums proc2
    | proc -> [ proc ]
  in
  let rec search_pars = function
    | Par (proc1, proc2) -> search_pars proc1 @ search_pars proc2
    | proc -> [ proc ]
  in
  let tree_of_sop cons sop =
    let rec f min max =
      let delta = max - min in
	if delta = 1 then sop.(min) else
	  let pivo = min + 1 + Random.int (delta - 1) in
	    cons (f min pivo) (f pivo max)
    in
      f 0 (Array.length sop)
  in
    match proc with
      | Silent | Call (_, _) -> proc
      | Prefix (name, proc) -> Prefix (name, perm_saps proc)
      | Res (name, proc) -> Res (name, perm_saps proc)
      | Sum (_, _) ->
	  tree_of_sop (fun p1 p2 -> Sum (p1, p2)) (rand_list (search_sums proc))
      | Par (_, _) ->
	  tree_of_sop (fun p1 p2 -> Par (p1, p2)) (rand_list (search_pars proc))
      |Rename (old,value,proc) ->  Rename(old,value,perm_saps proc)
;;

let alea_nus proc =
  let rec f map proc =
    match proc with
      | Silent | Call (_, _) -> proc
      | Prefix (Tau, proc) -> Prefix (Tau, f map proc)
      | Prefix (In name, proc) -> Prefix (In (SMap.find name map), f map proc)
      | Prefix (Out name, proc) -> Prefix (Out (SMap.find name map), f map proc)
      | Sum (proc1, proc2) -> Sum (f map proc1, f map proc2)
      | Par (proc1, proc2) -> Par (f map proc1, f map proc2)
      | Rename (old,value,proc) -> Rename (old,value, f map proc)
      | Res (name, proc) ->
	  let frees = freeNames proc in
	  let defined =
	    SMap.fold (fun k _ acc -> SSet.add k acc) map SSet.empty
	  in
	  let poss = SSet.diff defined frees in
	  let new_name =
	    let nb = SSet.cardinal poss in
	      if nb > 0 then List.nth (SSet.elements poss) (Random.int nb)
	      else
		let rec create n =
		  let s = "f" ^ (string_of_int n) in
		    if SSet.mem s poss then create (succ n) else s
		in
		  create 0
	  in
	    Res (new_name, f (SMap.add name new_name map) proc)
  in
  let frees = freeNames proc in
  let init_map = SSet.fold (fun n -> SMap.add n n) frees SMap.empty in
    f init_map proc
;;

let perm_proc proc = perm_saps (alea_nus proc);;

let normalize_random_check proc_sizes repeat_nb =
  eprintf "Checking normalization (random version)... %!";
  for i = 1 to repeat_nb do
    ignore i ;
    let proc = rand_proc proc_sizes in
    let nproc = normalize proc in
    let rand_proc = perm_proc proc in
    let rand_nproc = normalize proc in
      if nproc <> rand_nproc then (
	eprintf "\nNormalization error:\
\
  normalize( %s )\
  -> %s\
\
  normalize( %s )\
  -> %s\
\
" (string_of_process proc) (string_of_nprocess nproc)
  (string_of_process rand_proc) (string_of_nprocess (rand_nproc));
	failwith "normalization error";
      )
  done;
  eprintf "done\n** Normalization checked successfully !\n%!"
;;

let normalize_exhaustive_check child_sizes child_nb =
  let childs = Array.init child_nb (fun _ -> rand_proc child_sizes) in
  let main_proc =
    let rec f n = if n = 0 then childs.(0) else Sum (childs.(n), f (pred n)) in
      f (pred child_nb);
  in
  let main_normalized = normalize main_proc in
  let check_proc proc =
    let nproc = normalize proc in
      if nproc <> main_normalized then (
	eprintf "\nNormalization error:\
\
  normalize( %s )\
  -> %s\
\
  normalize( %s )\
  -> %s\
\
" (string_of_process proc) (string_of_nprocess nproc)
  (string_of_process main_proc) (string_of_nprocess (main_normalized));
	failwith "normalization error";
      )
  in
  let iter_tree () =
    let rec f min max g =
      if min = pred max then g childs.(min) else
	for i = succ min to pred max do
	  f min i (fun p1 -> f i max (fun p2 -> g (Sum (p1, p2))));
	done
    in
      f 0 child_nb check_proc
  in
  let rec iter_order n =
    let pn = pred n in
      if pn = 0 then iter_tree ()
      else (
	iter_order pn;
	for i = 0 to (pred pn) do
	  let x = childs.(i) in
	    childs.(i) <- childs.(pn);
	    childs.(pn) <- x;
	    iter_order pn;
	    childs.(pn) <- childs.(i);
	    childs.(i) <- x;
	done;
      )
  in
    eprintf "Checking normalization (exhaustive version)... %!";
    iter_order child_nb;
    eprintf "done\n** Normalization checked successfully !\n%!";
;;

Random.self_init ()
