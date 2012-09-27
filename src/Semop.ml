open Printf

open Utils
open Syntax
open Normalize

(* Remark: we use a dedicated type because in further
   extension, the set of possible transition labels could
   be distinct from action prefixes *)
type label = T_Tau | T_In of name | T_Out of name

let string_of_label = function
  | T_Tau -> tau_str
  | T_In n -> n ^ "?"
  | T_Out n -> n ^ "!"

type transition = nprocess * label * nprocess

let string_of_transition (p, l, p') =
  sprintf "%s --[%s]-> %s" (string_of_nprocess p) (string_of_label l)
    (string_of_nprocess p')

let string_of_derivative (_,l,p') =
  (* a derivative is a transition without the start state *)
  sprintf "--[%s]-> %s" (string_of_label l) (string_of_nprocess p')

module TSet = Set.Make (
  struct
    type t = transition
    let compare ((s1,l1,d1):t) ((s2,l2,d2):t) = compare (l1,d1,s1) (l2,d2,s2)
  end
)

module PSet = Set.Make (
  struct
    type t = nprocess
    let compare (x:t) (y:t) = compare x y
  end
)

module BSet = Set.Make (
  struct
    type t = nprocess * nprocess
    let compare (x:t) (y:t) = compare x y
  end
)

let derivatives defs ((orig_res, orig_np) as orig_nproc) =
  let restrict res derivs =
    let filter (_, lab, _) =
      match lab with
      | T_Tau -> true
      | T_In n | T_Out n -> not (SSet.mem n res)
    in
      TSet.filter filter derivs
  in
  let renames var name derivs=
    let folder (src, lab, (dres,dest)) acc =
      let lab' = match lab with
        | T_Tau -> T_Tau
        | T_In n -> T_In (if n = var then name else n)
        | T_Out n -> T_Out (if n = var then name else n)
      in
        TSet.add (src, lab', (dres,NRename(var,name,dest))) acc
    in
      TSet.fold folder derivs TSet.empty
  in
  let label_of_prefix =
    function | Tau -> T_Tau | In n -> T_In n | Out n -> T_Out n
  in
  let rec f res np =
    match np with
    | NSilent -> TSet.empty
    | NCall (name, args) ->
      let def_sign = string_of_def_header (Definition(name,args,Silent)) in
      let Definition (_, _, body) =
	try Hashtbl.find defs def_sign
	with Not_found -> failwith (sprintf "Process %s not found" name)
      in
      let (body_res, body_np) = normalize body in
      let derivs = f body_res body_np in
	restrict body_res derivs
    | NPrefix (pref, np) ->
      TSet.singleton (orig_nproc, label_of_prefix pref, renormalize(res,np))
    | NRename (var,name,np) -> 
      let derivs = f res np
      in
        renames var name derivs
    | NSum nps ->
      List.fold_left (fun acc np -> TSet.union (f res np) acc)
	TSet.empty nps
    | NPar nps ->
      let np_frees = SSet.diff (nfreeNames np) res in
      let ((set_par : TSet.t), (set_simpl : (TSet.t * nproc list) list)) =
	let folder (acc_par, acc_simpl) np =
	  let oths_np = List.filter ((!=) np) nps in
	  let nexts = f SSet.empty np in
	  let folder (src, lab, (in_res, dst)) acc =
	    let new_dst =
	      let in_frees = SSet.diff (nfreeNames dst) in_res in
	      let in_forbid = SSet.inter in_res np_frees in
	      let np_forbid = SSet.inter res in_frees in
	      let folder_in name (cnt, acc_in, acc_in_res) =
		let rec gen_name n =
		  let new_n = "f" ^ (string_of_int n) in
		    if SSet.mem new_n in_frees || SSet.mem new_n in_res
		    then gen_name (succ n)
		    else (succ n, new_n)
		in
		let (new_cnt, new_name) = gen_name cnt in
		  (new_cnt, nproc_subst acc_in name new_name,
		   SSet.add new_name (SSet.remove name acc_in_res))
	      in
	      let (_, new_in, new_in_res) =
		SSet.fold folder_in in_forbid (0, dst, in_res)
	      in
	      let folder_oths name (cnt, acc_oths, acc_oths_res) =
		let rec gen_name n =
		  let new_n = "f" ^ (string_of_int n) in
		    if SSet.mem new_n np_frees || SSet.mem new_n res
		    then gen_name (succ n)
		    else (succ n, new_n)
		in
		let (new_cnt, new_name) = gen_name cnt in
		  (new_cnt,
		   List.map (fun np -> nproc_subst np name new_name)
		     acc_oths,
		   SSet.add new_name (SSet.remove name acc_oths_res))
	      in
	      let (_, new_oths, new_oths_res) =
		SSet.fold folder_oths np_forbid (0, oths_np, res)
	      in
		renormalize (SSet.union new_in_res new_oths_res,
			     NPar (new_in :: new_oths))
	    in
	      TSet.add (src, lab, new_dst) acc
	  in
	    (TSet.fold folder nexts acc_par, (nexts, oths_np) :: acc_simpl)
	in
	  List.fold_left folder (TSet.empty, []) nps
      in
      let folder ((map, _) as acc) (elt_set, oths) =
	let folder' (_, lab, dst) ((map', set') as acc') =
	  let add_taus org opp =
	    let new_map' =
	      try SMap.add org ((dst,oths) :: SMap.find org map') map'
	      with Not_found -> SMap.add org [(dst,oths)] map'
	    in
	      try
		let dsts' = SMap.find opp map in
		let folder acc (np, oths') =
		  let oths_np =
		    List.filter (fun e -> List.memq e oths) oths'
		  in
		  let nproc' =
		    let p1 = denormalize np in
		    let p2 = denormalize dst in
		    let oths_p =
		      List.map (fun np -> denormalize (res, np)) oths_np
		    in
		    let p =
		      List.fold_left (fun acc p -> Par (p, acc)) Silent
			(p1 :: p2 :: oths_p)
		    in
		      normalize p
		  in
		    TSet.add (orig_nproc, T_Tau, nproc') acc
		in
		  (new_map', List.fold_left folder set' dsts')
	      with Not_found -> (new_map', set')
	  in
	    match lab with
	    | T_Tau -> acc'
	    | T_In n -> add_taus (n ^ "?") (n ^ "!")
	    | T_Out n -> add_taus (n ^ "!") (n ^ "?")
	in
	  TSet.fold folder' elt_set acc
      in
	snd (List.fold_left folder (SMap.empty, set_par) set_simpl)
  in
  let derivs = f orig_res orig_np in
    restrict orig_res derivs
;;

let lts defs p =
  let rec f acc_trans procs_todo procs_done =
    try
      let p = PSet.choose procs_todo in
      let derivs = derivatives defs p in
      let new_acc_trans = TSet.union acc_trans derivs in
      let next_procs =
	TSet.fold (fun (_,_,dst) acc -> PSet.add dst acc) derivs PSet.empty
      in
      let new_procs_todo =
	PSet.remove p (PSet.union (PSet.diff next_procs procs_done) procs_todo)
      in
      let new_procs_done = PSet.add p procs_done in
	f new_acc_trans new_procs_todo new_procs_done
    with Not_found -> acc_trans
  in
  let transs = f TSet.empty (PSet.singleton p) PSet.empty in
    TSet.fold (fun t acc -> t :: acc) transs []
;;

let construct_bisimilarity defs nproc1 nproc2 =
  let rec construct bsm np1 np2 =
    let d1s = derivatives defs np1 in
    let d2s = derivatives defs np2 in
    let folder dys inv (_, labx, dstx) acc_bsm =
      let rec search acc_dys =
	if TSet.is_empty acc_dys then failwith "Bad path"
	else
	  let ((_, laby, dsty) as ty) = TSet.choose acc_dys in
	    if labx <> laby then search (TSet.remove ty acc_dys)
	    else
	      let dst1 = if inv then dsty else dstx in
	      let dst2 = if inv then dstx else dsty in
	      let dsts = (dst1, dst2) in
		if BSet.mem dsts acc_bsm || BSet.mem (dst2, dst1) acc_bsm
		  || dst1 = dst2 then acc_bsm
		else
		  try construct (BSet.add dsts acc_bsm) dst1 dst2
		  with Failure "Bad path" -> search (TSet.remove ty acc_dys)
      in
	search dys
    in
      TSet.fold (folder d2s false) d1s
	(TSet.fold (folder d1s true) d2s bsm)
  in
    try construct (BSet.singleton (nproc1, nproc2)) nproc1 nproc2
    with Failure "Bad path" -> failwith "Not bisimilar"
;;

let is_bisimilar defs nproc1 nproc2 =
  try ignore (construct_bisimilarity defs nproc1 nproc2) ; true
  with Failure "Not bisimilar" -> false
;;
