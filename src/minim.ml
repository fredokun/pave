open Printf

open Utils
open Normalize
open Semop

(* Graph structure : maps a graph state to a GSet of previous graph states *)
(* Partition structure : is a list of GSets *)


type gstate = PState of bool * nprocess | LState of transition

module GMap = Map.Make (
  struct
    type t = gstate
    let compare (x:t) (y:t) = compare x y
  end
)

module GSet = Set.Make (
  struct
    type t = gstate
    let compare (x:t) (y:t) = compare x y
  end
)

type transitions = nprocess list * label * nprocess list

module TsSet = Set.Make (
  struct
    type t = transitions
    let compare ((s1,l1,d1):t) ((s2,l2,d2):t) = compare (l1,d1,s1) (l2,d2,s2)
  end
)

let string_of_transitions (pl, l, pl') =
  sprintf "%s --[%s]-> %s" (string_of_list string_of_nprocess pl)
    (string_of_label l) (string_of_list string_of_nprocess pl')

let string_of_gstate gs = match gs with
  | PState (r, _) when r -> "*root*"
  | PState (_, p) -> string_of_nprocess p
  | LState trans -> sprintf "(%s)" (string_of_transition trans)

let string_of_gset tostr set =
  string_of_collection "{" "}" "," tostr (GSet.elements set)

let string_of_graph g =
  let folder dst prevs acc =
    acc ^ (sprintf "%s has prevs %s\n" (string_of_gstate dst)
	     (string_of_gset string_of_gstate prevs))
  in
    GMap.fold folder g ""

let string_of_partition parts = 
  (List.fold_left
    (fun s part -> s ^ "\n" ^ (string_of_gset string_of_gstate part)) "" parts)
    ^ "\n"

let build_graph f_deriv init_graph init_partition defs ps =
  let rec add_to_partition part elem =
    match part with
      | [] -> [GSet.singleton elem]
      | set::ss ->
	begin
	  match (GSet.choose set, elem) with
	    | (PState _, PState _) ->
	      (GSet.add elem set)::ss
	    | (LState(_,a,_), LState(_,b,_)) when a = b ->
	      (GSet.add elem set)::ss
	    | _ -> set::(add_to_partition ss elem)
	end
  in
  let rec f (graph, part) procs_todo procs_done =
    try
      let p = PSet.choose procs_todo in
      let derivs = f_deriv defs p in
      let (new_graph, new_part) =
	let folder ((src,_,dst) as trans) (accg, accp) =
	  let (src', lbl', dst') =
	    (PState(false,src), LState trans, PState(false,dst)) in
	  let accg' = GMap.add lbl' (GSet.singleton src') accg in
	  let accp' = add_to_partition accp lbl' in
	  if GMap.mem dst' accg' then
	    let l = GMap.find dst' accg' in
	    (GMap.add dst' (GSet.add lbl' l) accg', accp')
	  else
	    (GMap.add dst' (GSet.singleton lbl') accg',
	     add_to_partition accp' dst')
	in
	TSet.fold folder derivs (graph, part)
      in
      let next_procs =
	TSet.fold (fun (_,_,dst) acc -> PSet.add dst acc) derivs PSet.empty
      in
      let new_procs_todo =
	PSet.remove p (PSet.union (PSet.diff next_procs procs_done) procs_todo)
      in
      let new_procs_done = PSet.add p procs_done in
	f (new_graph, new_part) new_procs_todo new_procs_done
    with Not_found -> (graph, part)
  in
  match ps with
    | [] -> (init_graph, init_partition)
    | p1::[] -> f (init_graph, init_partition) (PSet.singleton p1) PSet.empty
    | p1::p2::[] ->
      let tmp = f (init_graph, init_partition) (PSet.singleton p1) PSet.empty
      in f tmp (PSet.singleton p2) PSet.empty
    | _ -> (init_graph, init_partition)

let rec refine (graph, part) =
  let prevs = 
    List.map (fun x ->
      GSet.fold (fun x' acc -> GSet.union acc (GMap.find x' graph))
	x GSet.empty) part
  in
  let split part prev = 
    let p1 = GSet.inter part prev in
    let p2 = GSet.diff part prev in
    (p1, p2)
  in
  let rec f1 pt pr =
    match pt with
      | [] -> []
      | h1::t1 -> (f2 h1 pr)@(f1 t1 pr)
  and f2 pt pr = 
    match pr with
      | [] -> [pt]
      | h2::t2 -> let (spl1, spl2) = split pt h2 in
		  if GSet.is_empty spl1 || GSet.is_empty spl2 then
		    f2 pt t2
		  else
		    [spl1 ; spl2]
  in
  let part' = f1 part prevs in
  if (List.length part = List.length part')
  then part' else refine (graph, part')

let build_lts partition =
  let (ps, ls) = 
    List.partition (fun x -> match GSet.choose x with
		    | LState _ -> false
		    | PState _ -> true)
      partition in
  let pstates = List.map
    (fun set ->
       GSet.fold
	 (fun x acc -> match x with
	    | PState (_, np) -> np::acc
	    | LState _ -> acc) set []
    ) ps
  and lstates = List.map
    (fun set ->
       GSet.fold
	 (fun x acc -> match x with
	    | PState _ -> acc
	    | LState t -> t::acc) set []
    ) ls
  in
  let rec f transs todos =
    match todos with
      | [] -> transs
      | cp::t ->
	  begin
	    let p = List.hd cp in
	    let labs = 
	      List.fold_left
		(fun acc x -> 
		   match List.filter (fun (src,_,_) -> src = p) x with
		     | [] -> acc
		     | t::_ -> t::acc
		)
		[] lstates
	    in let transs' = 
		List.fold_left
		  (fun acc (_,lbl,dst) ->
		     let cdl = List.filter
		       (fun x -> List.mem dst x) pstates in
		       assert ((List.length cdl) = 1);
		       let cd = List.hd cdl in
                       TsSet.add (cp, lbl, cd) acc
		  ) transs labs
	    in f transs' t
	  end
  in
    f TsSet.empty pstates


let minimize f_deriv defs proc =
  let init_graph = GMap.add (PState(false,proc)) GSet.empty GMap.empty in
  let init_partition = [GSet.singleton (PState(false,proc))] in
  let (graph, partition) = build_graph f_deriv init_graph init_partition defs [proc] in
    (*print_endline "STATE GRAPH :";
    print_string (string_of_graph graph);
    print_string "PARTITION :";
    print_string (string_of_partition partition);*)
    let partition' = refine (graph, partition) in
      (*print_string "PARTITION REFINED :";
	print_string (string_of_partition partition');*)
    let transitions = build_lts partition' in
      TsSet.fold (fun t acc -> t :: acc) transitions []

let is_fbisimilar f_deriv defs p1 p2 =
  let root = PState(true,(SSet.empty,NSilent)) in
  let pst1 = PState(false, p1) in
  let pst2 = PState(false, p2) in
  let init_graph =
    GMap.add pst2 (GSet.singleton root)
      (GMap.add pst1 (GSet.singleton root)
	 (GMap.add root GSet.empty GMap.empty)) in
  let init_partition =
    [GSet.add pst1 (GSet.add pst2 (GSet.singleton root))] in
  let (graph, partition) =
    build_graph f_deriv init_graph init_partition defs [p1;p2] in
  let partition' = refine (graph, partition) in
  let l = List.filter (fun x ->
    (GSet.mem pst1 x) || (GSet.mem pst2 x)) partition' in
  (List.length l) = 1


