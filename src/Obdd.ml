
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

module Obddtbl = Hashtbl.Make (HashedObdd)

let hsize = 19997 (* 200323 *)


module H2 = Hashtbl.Make
  (struct
     type t = obdd * obdd
     let hash (o1, o2) = (19 * unique o1 + unique o2) land max_int
     let equal (o11, o12) (o21, o22) = o11 == o21 && o12 == o22
   end)


let construct =
  let global_table = Obddtbl.create hsize in
  fun i o1 o2 ->
  if o2 = Zero then o1 else
    let obdd = Node (!unique_ref, i, o1, o2) in
    try
      Obddtbl.find global_table obdd
    with Not_found ->
      Obddtbl.add global_table obdd obdd;
      incr unique_ref;
      obdd

let memo_rec2 f =
  let h = H2.create hsize in
  let rec g x =
    try H2.find h x
    with Not_found -> let y = f g x in H2.add h x y; y
  in
  g

let union = memo_rec2 (
  fun union -> function
    | Node(_, i, o1, o2), One
    | One, Node(_, i, o1, o2) -> construct i (union (o1, One)) o2
    | One, One -> One
    | Zero, o | o, Zero -> o
    | (Node (_, i1, l1, r1) as o1), (Node (_, i2, l2, r2) as o2) ->
      if i1 = i2 then
        construct i1 (union (l1, l2)) (union (r1, r2))
      else if i1 > i2 then
        construct i2 (union (o1, l2)) r2
      else
        construct i1 (union (l1, o2)) r1
)

let union o1 o2 = union (o1, o2)

let inter = memo_rec2 (
  fun inter -> function
    | Node(_, _, o1, _), One
    | One, Node(_, _, o1, _) -> inter (o1, One)
    | One, One -> One
    | Zero, _
    | _, Zero -> Zero
    | (Node (_, i1, l1, r1) as o1),
        (Node (_, i2, l2, r2) as o2) ->
        if i1 = i2 then
          construct i1 (inter (l1, l2)) (inter (r1, r2))
        else if i1 > i2 then
          inter (o1, l2)
        else
          inter (o2, l1)
  )

let inter o1 o2 = inter (o1, o2)

