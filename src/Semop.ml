open Printf

open Utils
open Syntax
open Normalize

module PrefixMap = Map.Make (
  struct
    type t = prefix
    let compare (x:t) (y:t) = compare x y
  end
)

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

let label_of_prefix =function 
  | Tau -> T_Tau | In n -> T_In n | Out n -> T_Out n
    

let derivatives defs ((orig_res, orig_np) as orig_nproc) =
  let restrict res derivs =
    let filter (_, lab, _) =
      match lab with
      | T_Tau -> true
      | T_In n | T_Out n -> not (SSet.mem n res)
    in TSet.filter filter derivs
  in
  let renames var name derivs=
    let folder (src, lab, (dres,dest)) acc =
      let lab' = match lab with
        | T_Tau -> T_Tau
        | T_In n -> T_In (if n = var then name else n)
        | T_Out n -> T_Out (if n = var then name else n)
      in TSet.add (src, lab', (dres,NRename(var,name,dest))) acc
    in TSet.fold folder derivs TSet.empty
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
	let folder (acc_par, acc_simpl) np = (*folder_1*)
	  (* accumulateur ?*)
	  let oths_np = List.filter ((!=) np) nps in
	  let nexts = f SSet.empty np in
	  let folder (src, lab, (in_res, dst)) acc =
	    let new_dst =
	      let in_frees = SSet.diff (nfreeNames dst) in_res in
	      let in_forbid = SSet.inter in_res np_frees in
	      let np_forbid = SSet.inter res in_frees in
	      let folder_in name (cnt, acc_in, acc_in_res) =
		(*compteur, accu processus, accu restrictions*)
		let rec gen_name n =
		  let new_n = "f" ^ (string_of_int n) in
		  if SSet.mem new_n in_frees || SSet.mem new_n in_res
		  then gen_name (succ n)
		  else (succ n, new_n)
		in
		let (new_cnt, new_name) = gen_name cnt in
		(new_cnt, nproc_subst acc_in name new_name,
		 SSet.add new_name (SSet.remove name acc_in_res))
		  (* nproc_subst renames the first encountered label != Tau
		     or the name in a Rename node
		     We delete the passage and we rename name by new_name in the set
		  *) in
	      let (_, new_in, new_in_res) =
		SSet.fold folder_in in_forbid (0, dst, in_res)
	      (*We rename all the names (at depth 1) 
		of dst in folder_in by the new name
	      *) 
	      in let folder_oths name (cnt, acc_oths, acc_oths_res) =
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
		 in renormalize (SSet.union new_in_res new_oths_res,
				 NPar (new_in :: new_oths))
	    in TSet.add (src, lab, new_dst) acc
	  in (TSet.fold folder nexts acc_par, (nexts, oths_np) :: acc_simpl)
	in List.fold_left folder (TSet.empty, []) nps
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
		  in normalize p
		in TSet.add (orig_nproc, T_Tau, nproc') acc
	      in (new_map', List.fold_left folder set' dsts')
	    with Not_found -> (new_map', set')
	  in match lab with
	  | T_Tau -> acc'
	  | T_In n -> add_taus (n ^ "?") (n ^ "!")
	  | T_Out n -> add_taus (n ^ "!") (n ^ "?")
	in TSet.fold folder' elt_set acc
      in snd (List.fold_left folder (SMap.empty, set_par) set_simpl)
  in
  let derivs = f orig_res orig_np in
  restrict orig_res derivs
;;

let lts deriv_f defs p =
  let rec f acc_trans procs_todo procs_done =
    try
      let p = PSet.choose procs_todo in
      let derivs = deriv_f defs p in
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


(******************************************************************************************)
(******************************************************************************************)
(************************************ Weak path *******************************************)
(******************************************************************************************)
(******************************************************************************************)

let name_of_pfix = function
  | Tau -> ""
  | In n -> n
  | Out n -> n
    
let rename_pfix oldp n = 
  match oldp with
  | Tau -> Tau
  | In _ -> In n
  | Out _ -> Out n

let cond_pfix_rename oldpfix to_replace newn =
  match oldpfix with
  | Tau -> Tau
  | In n -> if n = to_replace then In newn else oldpfix
  | Out n -> if n = to_replace then Out newn else oldpfix

let pmap_get_set map key =
  try
    PrefixMap.find key map
  with
    Not_found -> PSet.empty

let pmap_in_map map key v =
  PSet.mem v (pmap_get_set map key )
and pmap_add_val map key v =
  let s = pmap_get_set map key in
  PrefixMap.add key (PSet.add v s) map

let is_restricted rest pf =
  SSet.mem (name_of_pfix pf) rest

let prefix_of_label = function 
  | T_Tau -> Tau | T_In n -> In n | T_Out n -> Out n
    

let weak_derivatives tau_only defs (orig_restrict, p) : PSet.t PrefixMap.t =
  let rec weak_deriv_aux pfix_key entry_map (restrict, p) =
    let get_set key =
      try 
	PrefixMap.find key entry_map
      with
	Not_found -> PSet.empty
    in
    let in_map key v =
      PSet.mem (restrict, v) ( get_set key )
    and add_val key v =
      let s = get_set key in
      PrefixMap.add key (PSet.add (restrict, v) s) entry_map
    in
    match p with
    | NSilent -> add_val pfix_key NSilent
    | NPrefix (pfix, p') ->
      (match pfix with
      | Tau -> 
	if in_map pfix_key p' then
	  entry_map
	else
	  let m = add_val pfix_key p' in
	  weak_deriv_aux pfix_key m (restrict, p')
      | _ ->
	if (not tau_only) && (pfix_key = Tau) then (*Rappel réccursif potentiel*)
	  if in_map pfix p' then
	    entry_map
	  else
	    let m = add_val pfix p' in
	    weak_deriv_aux pfix m (restrict, p')
	else (*2ème transition non tau -> fin de la récursion ou on ne cherche que les tau transitions*)
	  entry_map
      )
    | NSum p_list ->
      List.fold_left (fun m p -> weak_deriv_aux pfix_key m (restrict, p)) entry_map p_list
	
    | NPar _ -> 
      let a_suivre = ref [] in
      let rmap = ref entry_map in
      let follow = function (_, lbl, pr') ->
	let a = prefix_of_label lbl in
	match (pfix_key, a) with
	| Tau, pfix | pfix, Tau -> 
      	  if not (pmap_in_map !rmap pfix pr') then
	    (a_suivre:= (pr', pfix) ::!a_suivre;
	     rmap:= pmap_add_val !rmap pfix pr')
	| _, _ -> ()
      and tau_follow = function (_, lbl, pr') ->
	if lbl = T_Tau && not (pmap_in_map !rmap Tau pr') then
	  (a_suivre:= (pr', Tau) ::!a_suivre;
	   rmap:= pmap_add_val !rmap Tau pr')
      in
      let pl = TSet.elements (derivatives defs (restrict, p)) in 
      (* Nous avions commencé par écrire notre fonction dans l'optique de ne 
	 pas utiliser derivatives. Cependant à la fin on s'est retrouvé face au problème 
	 de l'extraction des restrictions dans le cas parallèle.
	 Par manque de temps, nous avons du nous résoudre à utiliser derivatives.
	 
	 Vous pourrez trouvez nos essais dans Semop_abandon.ml
	 Notament notre version de derivatives, réservée au cas parallele: par_derivatives
      *)
      (if tau_only then
	  List.iter tau_follow pl
       else
	  List.iter follow pl);
      List.fold_left (fun m (p,a) -> weak_deriv_aux a m p) !rmap !a_suivre
	
    | NCall (name, args) -> 
      let def_sign = string_of_def_header (Definition(name,args,Silent)) in
      let Definition (_, _, body) =
      	try Hashtbl.find defs def_sign
      	with Not_found -> failwith (sprintf "Process %s not found" name)
      in
      let (body_res, body_np) = normalize body in
      let derivs = weak_deriv_aux pfix_key entry_map ((SSet.union restrict body_res), body_np) in
      PrefixMap.filter (fun k _ -> not (is_restricted body_res k)) derivs
    (* on ne filtre que sur body_res -> restrict sera au pire filtré à la sortie
     * de weak_derivatives, et plus d'états dans la map peut empêcher des récursions *)
    | NRename (old, newn, p') ->
      (*ici on fait un appel réccursif avec une map vide et on trie à la sortie*)
      let m = weak_deriv_aux pfix_key PrefixMap.empty (restrict, p')
      and merger _ s1 s2 = 
	match s1,s2 with
	  None, Some s -> Some s
	| Some s, None -> Some s
	| Some s, Some s' -> Some (PSet.union s s')
	| None, None -> None
      and package_set s =
	let l = List.map (fun (r,p) -> (r, NRename (old, newn, p))) (PSet.elements s) in
	List.fold_left (fun s e -> PSet.add e s) PSet.empty l
      and find_rename f m =
	try
	  let s = PrefixMap.find (f old) m in
	  let s' = 
	    try 
	      PrefixMap.find (f newn) m
	    with
	      Not_found -> PSet.empty
	  in 
	  PrefixMap.add (f newn) (PSet.union s s') (PrefixMap.remove (f old) m)
	with 
	  Not_found -> m
      in
      let m'= PrefixMap.map package_set (find_rename (fun x -> Out x) 
					   (find_rename (fun x -> In x) m)) in
      PrefixMap.merge merger m' entry_map
  in
  let derivs = weak_deriv_aux Tau PrefixMap.empty (orig_restrict,p) in
  let derivs = PrefixMap.filter (fun k _ -> not (is_restricted orig_restrict k)) derivs in
  pmap_add_val derivs Tau (orig_restrict, p)

    

let printPfixMap map =
  let b = PrefixMap.bindings map in
  let print_b (k, s) = 
    let l = PSet.elements s in
    let arrow = Printf.sprintf "==%s==>" (string_of_prefix k) in
    List.iter (fun p -> print_string arrow; print_endline (string_of_nprocess p)) l
  in
  List.iter print_b b  


let construct_weak_bisimilarity defs nproc1 nproc2 =
  let rec construct bsm np1 np2 =
    let wd1s = weak_derivatives false defs np1 in
    let wd2s = weak_derivatives false defs np2 in
    (if (PrefixMap.cardinal wd1s) <> (PrefixMap.cardinal wd2s) then
	failwith "Not bisimilar");

    let d1s = derivatives defs np1 in
    let d2s = derivatives defs np2 in
    
    let folder wds inv (_, lab, dstx) acc_bsm =
      let dys = 
	try PrefixMap.find (prefix_of_label lab) wds
	with Not_found -> failwith "Bad path"
      in
      let rec search candidates =
	if PSet.is_empty candidates then failwith "Bad path"
	else
	  let dsty = PSet.choose candidates in
	  let dst1 = if inv then dsty else dstx in
	  let dst2 = if inv then dstx else dsty in
	  let dsts = (dst1, dst2) in
	  if BSet.mem dsts acc_bsm || BSet.mem (dst2, dst1) acc_bsm
	    || dst1 = dst2 then acc_bsm
	  else
	    try construct (BSet.add dsts acc_bsm) dst1 dst2
	    with Failure "Bad path" -> search (PSet.remove dsty candidates)
      in
      search dys
    in
    TSet.fold (folder wd2s false) d1s 
      (TSet.fold (folder wd1s true) d2s bsm)
  in
  try construct (BSet.singleton (nproc1, nproc2)) nproc1 nproc2
  with Failure "Bad path" -> failwith "Not bisimilar"
;;

let is_weakly_bisimilar defs nproc1 nproc2 =
  try ignore (construct_weak_bisimilarity defs nproc1 nproc2) ; true
  with Failure "Not bisimilar" -> false
;;


(* a small hack to go from strong transitions to weak ones
*)
let pmap_to_trans map orig =
  let bds = PrefixMap.bindings map in
  List.fold_left (fun acc (pfix, dst_set) -> 
    let lbl= label_of_prefix pfix in
    PSet.fold (fun dst acc' -> TSet.add (orig, lbl, dst) acc') dst_set acc) TSet.empty bds

let weak_transitions tau_only defs p =
  ignore tau_only ;
  pmap_to_trans (weak_derivatives false defs p) p
