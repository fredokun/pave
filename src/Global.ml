(** Global Model Checking Module *)


type error =
| No_global_not

exception Error of error

let print_error = function
  | No_global_not -> Printf.printf "Cannot global check formula with negation"


module Obdd = struct
  type unique = int

  type t = Zero | One | Node of unique * int * t * t
  type obdd = t

  module S = Set.Make(
    struct
      type t = int
      let compare = compare
    end
  )
  type elt = S.t

  let zero = Zero
  let empty = zero
  let is_empty obdd = obdd == Zero

  let one = One

  let unique = function
    | Zero -> 0
    | One -> 1
    | Node (u , _, _, _) -> u

  let hash_node i o1 o2 = (19 * (19 * i + unique o1) + unique o2) land max_int

  let unique_ref = ref 2

  module HashedObdd = struct
    type t = obdd
    let hash = function
      | Zero -> 0
      | One -> 1
      | Node (_, i, o1, o2) -> hash_node i o1 o2
    let equal k1 k2 = match k1, k2 with
      | One, One
      | Zero, Zero -> true
      | Node (_, i1, l1, r1), Node (_, i2, l2, r2) ->
        i1 = i2 && unique l1 = unique l2 && unique r1 = unique r2
      | _ -> false
  end
end

module Obddtbl = Hashtbl.Make (Obdd.HashedObdd)
let hsize = 19997 (* 200323 *)


open Obdd


(* let construct global_table i o1 o2 = *)
(*   if o2 = Zero then o1 else *)
(*     let obdd = Node (!unique_ref, i, o1, o2) in *)
(*     try *)
(*       Obddtbl.find global_table obdd *)
(*     with Not_found -> *)
(*       Obddtbl.add global_table obdd obdd; *)
(*       incr unique_ref; *)
(*       obdd *)

(* let memo_rec2 f = *)
(*   let h = Obddtbl.create hsize in *)
(*   let rec g x = *)
(*     try Obddtbl.find h x *)
(*     with Not_found -> let y = f g x in Obddtbl.add h x y; y *)
(*   in *)
(*   g *)


(* let union = memo_rec2 ( *)
(*   fun union -> function *)
(*   | Node(_, i, o1, o2), One *)
(*   | One, Node(_, i, o1, o2) -> construct i (union (o1, One)) o2 *)
(*   | One, One -> One *)
(*   | Zero, o *)
(*   | o, Zero -> o *)
(*   | (Node (_, i1, l1, r1) as o1), (Node (_, i2, l2, r2) as o2) -> *)
(*     if i1 = i2 then *)
(*       construct i1 (union (l1, l2)) (union (r1, r2)) *)
(*     else if i1 > i2 then *)
(*       construct i2 (union (o1, l2)) r2 *)
(*     else (\* i1 < i2 *\) *)
(*       construct i1 (union (l1, o2)) r1 *)
(* ) *)

(* let union o1 o2 = union (o1, o2) *)

let rec obdd_of_formula formula =
  let open Formula in
  match formula with
  | FTrue -> One
  | FFalse -> Zero
  | FNot _ -> raise @@ Error (No_global_not)
  (* | FAnd (f1, f2) -> Obdd.inter (obdd_of_formula f1) (obdd_of_formula f2) *)
  (* | FOr  (f1, f2) -> Obdd.union (obdd_of_formula f1) (obdd_of_formula f2) *)
  (* | FImplies of formula * formula *)
  (* | FModal of modality * formula *)
  (* | FInvModal of modality * formula *)
  (* | FProp of string * formula list *)
  (* | FVar of string *)
  (* | FMu of string * nprocess list * formula *)
  (* | FNu of string * nprocess list * formula *)
   | _ -> assert false

let check _formula _proc = assert false (* TODO *)
