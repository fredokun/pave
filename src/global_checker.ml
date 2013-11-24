open Formula
open Presyntax
open Syntax
open Semop
open Normalize



(*
let establish_system proc =
  (* proc, states, transitions *)
  let rec aux p s t =
    match p with
    | Silent -> (p :: s, t)
    | Prefix (a, proc) ->
      add_transition t a p proc;
      aux proc (p :: s) t
    | Sum (p1, p2) ->
      union (aux p1 s (Hashtbl.copy t)) (aux p2 s (Hashtbl.copy t))
    | Par (p1, p2) ->
      cartesian_product (aux p1 s (Hashtbl.copy t)) (aux p1 s (Hashtbl.copy t))
    | _ -> failwith "TODO"
  in
  aux proc [] (Hashtbl.create 10)
*)

let make_pset_from_tlist tlist =
  let res = ref PSet.empty in
  List.iter
    (fun (p1, _, p2) ->
      if not (PSet.mem p1 !res) then res := PSet.add p1 !res;
      if not (PSet.mem p2 !res) then res := PSet.add p2 !res)
    tlist;
  !res


let establish_system p =
  let tlist = lts derivatives (Hashtbl.create 10) (normalize p) in
  (make_pset_from_tlist tlist, tlist)

(*  *)
let transitions_from_act act (_, t) =
  let res = Hashtbl.create 10 in
  List.iter
    (fun (p1, lbl, p2) ->
      let p1_succ =
	try Hashtbl.find res p1 with
	| Not_found -> let succs = ref [] in Hashtbl.replace res p1 succs; succs
      in
      match act, lbl with
      | Any_in, T_In _
      | Any_out, T_Out _
      | Any, _ ->
	p1_succ := p2 :: !p1_succ
      | Coll l, _ ->
	if (List.exists (fun e -> string_of_preprefix e = string_of_label lbl) l)
	then p1_succ := p2 :: !p1_succ
      | _ -> ()
    )
    t;
  res

let tau_after_states p (_, t) =
  let res = ref (PSet.singleton p) in
  let rec loop () =
    List.iter
      (fun (p1, lbl, p2) ->
	if PSet.mem p1 !res && not (PSet.mem p2 !res) && lbl = T_Tau then
	  begin
	    res := PSet.add p2 !res;
	    loop ()
	  end)
      t
  in
  loop ();
  !res

let tau_before_states p (_, t) =
  let res = ref (PSet.singleton p) in
  let rec loop () =
    List.iter
      (fun (p1, lbl, p2) ->
	if PSet.mem p2 !res && lbl = T_Tau then
	  begin
	    res := PSet.add p1 !res;
	    loop ()
	  end)
      t
  in
  loop ();
  !res
(* liste proc qui valident f
  liste trans par act
   poss => tau_before_states act && il existe after_states act vérifiant f
   nec => pr tt état faire la liste des 
*)
let rec eval_modality m f sys env =
  match m with
  | Possibly (str, act) ->
    begin
      match str with
      | Weak ->
	Printf.printf "eval_modality %s\n" (string_of_modality m);
	let trans = transitions_from_act act sys in
	let next = eval f sys env in
	Printf.printf "var ok\n";
	Hashtbl.fold
	  (fun p1 succs acc ->
	    Printf.printf "hash fold\n";
	    if List.exists (fun succ ->
	      Printf.printf "list exists\n";
	      PSet.exists
		(fun tau_state ->
		  Printf.printf "pset exists\n";
		  PSet.mem tau_state (eval f sys env))
		(tau_after_states succ sys))
	      !succs
	    then PSet.union (tau_before_states p1 sys) acc else acc)
	  trans
	  PSet.empty
      | Strong ->
	let trans = transitions_from_act act sys in
	Hashtbl.fold
	  (fun p1 succs acc ->
	    if (List.exists (fun p -> PSet.mem p (eval f sys env)) !succs)
	    then PSet.add p1 acc else acc)
	  trans
	  PSet.empty
    end
  | Necessity (str, act) ->
    begin
      match str with
      | Weak -> failwith "bl"
      | Strong ->
	let trans = transitions_from_act act sys in
	Hashtbl.fold
	  (fun p1 succs acc ->
	    if (List.for_all (fun p -> PSet.mem p (eval f sys env)) !succs)
	    then PSet.add p1 acc else acc)
	  trans
	  PSet.empty
    end
	

(*
  let rec eval_mu_nu is_mu var f sys env =
  let old = ref (if is_mu then FTrue else FFalse) in
  let curr = ref (if is_mu then FFalse else FTrue) in
  while (!old <> !curr) do
    old := !curr;
    Hashtbl.replace env var !curr;
    curr := eval f sys env;
  done;
  !curr
*)
and eval f sys env =
  match f with
  | FTrue -> (fst sys)
  | FFalse -> PSet.empty
  | FAnd (f1, f2) -> PSet.union (eval f1 sys env) (eval f2 sys env)
  | FOr (f1, f2) -> PSet.union (eval f1 sys env) (eval f2 sys env)
  | FNot ff ->
    let s = eval ff sys env in
    PSet.filter (fun e -> not (PSet.mem e s)) (fst sys)
  | FImplies (f1, f2) ->
    eval (FOr (FNot f1, f2)) sys env
  | FVar name ->
    (*begin try Hashtbl.find env with Not_found -> failwith "eval Var" end*)
    failwith "var"
  | FModal (m, ff) -> eval_modality m ff sys env
  | FMu (s, _, ff) -> (*eval_mu_nu true s ff sys env*) failwith "mu"
  | _ -> failwith "check global"
    

let p_test =
  Par
    (Sum
       ((Prefix (In "a", Silent)),
       (Prefix (Out "b", Silent))),
     Prefix (Tau, Silent))



let _ =
  let (s, t) = establish_system p_test in
  List.iter (fun e -> print_endline (string_of_transition e)) t
  
