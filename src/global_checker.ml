open Formula
open Presyntax
(* open Syntax *)
open Semop
open Normalize

let make_pset_from_tlist tlist =
  let res = ref PSet.empty in
  List.iter
    (fun (p1, _, p2) ->
      if not (PSet.mem p1 !res) then res := PSet.add p1 !res;
      if not (PSet.mem p2 !res) then res := PSet.add p2 !res)
    tlist;
  !res


let establish_system p def_env =
  let tlist = lts derivatives def_env (normalize p) in
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
let rec eval_modality m f sys def_env prop_env =
  match m with
  | Possibly (str, act) ->
    begin
      match str with
      | Weak ->
	(*PSet.fold
	  (fun p acc ->
	    if (List.exists (fun (p1, lbl, p2) ->
	      (PSet.mem p2 (eval f sys def_env prop_env))
	      && (TSet.exists p1 (weak_transitions false def_env p)))
		  (snd sys))
	    then
	      PSet.add p acc
	    else
	      acc)
	  (fst sys)
	  PSet.empty*)
	failwith "weak"
      | Strong ->
	let trans = transitions_from_act act sys in
	Hashtbl.fold
	  (fun p1 succs acc ->
	    if (List.exists (fun p -> PSet.mem p (eval f sys def_env prop_env)) !succs)
	    then PSet.add p1 acc else acc)
	  trans
	  PSet.empty
    end
  | Necessity (str, act) ->
    begin
      match str with
      | Weak -> failwith "weak"
      | Strong ->
	let trans = transitions_from_act act sys in
	Hashtbl.fold
	  (fun p1 succs acc ->
	    if (List.for_all (fun p -> PSet.mem p (eval f sys def_env prop_env)) !succs)
	    then PSet.add p1 acc else acc)
	  trans
	  PSet.empty
    end
       
and eval f sys def_env prop_env =
  let rec loop = function
  | FTrue -> (fst sys)
  | FFalse -> PSet.empty
  | FAnd (f1, f2) ->
    PSet.inter (loop f1) (loop f2)
  | FOr (f1, f2) ->
    PSet.union (loop f1) (loop f2)
  | FNot ff ->
    let s = loop ff in
    PSet.filter (fun e -> not (PSet.mem e s)) (fst sys)
  | FImplies (f1, f2) -> loop (FOr (FNot f1, f2))
  | FModal (m, ff) -> eval_modality m ff sys def_env prop_env
  | FInvModal (m, ff) -> loop (FNot (FModal (m, ff)))
  | FProp (id, args) -> 
    loop (Local_checker.reduce_proposition prop_env id args)
  | FVar id -> 
    loop (Local_checker.reduce_proposition prop_env id [])
  | _ -> failwith "Mu and Nu not implemented"
  in
  loop f

  
