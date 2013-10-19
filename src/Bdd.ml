(** Implementation of BDDs with hashconsing *)

type t = {id: int; l: t; r: t; value: int}

let rec null = {id = -1; l = null; r = null; value = -1}

let one = {id = 0; l = null; r = null; value = -1}
let zero = {id = 1; l = null; r = null; value = -1}

type bdd = t

module S = struct
  type t = bdd

  let equal b1 b2 =
    b1.l == b2.l && b1.r == b2.r

  let hash b =
    29 * (b.l.id + (29 * b.r.id))

end

module HBdd = Hashtbl.Make(S)

let create =
  let htbl = HBdd.create 53 in
  let id = ref 2 in
  fun v l r ->
    let i = !id in
    let b = {id = i; l; r; value = v} in
    try
      HBdd.find htbl b
    with
      Not_found ->
        HBdd.add htbl b b;
        incr id;
        b

module HPair = Hashtbl.Make(
  struct
    type t = bdd * bdd

    let equal (b1, b2) (b1', b2') =
      S.equal b1 b1' && S.equal b2 b2'

    let hash (b1, b2) =
      S.hash b1 + 29 * S.hash b2
  end)

let is_leaf b = b == one || b == zero

let boolean_equiv b =
  if b == one then true
  else if b == zero then false
  else assert false

let apply =
  let htbl = HPair.create 53 in
  let apply_op op b1 b2 =
    let b1 = boolean_equiv b1 in
    let b2 = boolean_equiv b2 in
    let res = op b1 b2 in
    if res then one else zero
  in
  fun op ->
    let rec apply b1 b2 =
      try HPair.find htbl (b1, b2)
      with Not_found ->
        let res =
          if is_leaf b1 && is_leaf b2 then
            apply_op op b1 b2
          else if b1.value = b2.value then
            create b1.value (apply b1.l b2.l) (apply b1.r b2.r)
          else if b1.value < b2.value then
            create b1.value (apply b1.l b2) (apply b1.r b2)
          else create b2.value (apply b1 b2.l) (apply b1 b2.r)
        in
        HPair.add htbl (b1, b2) res; res
    in
    apply

let rec restrict bool value b =
  if is_leaf b then b
  else
    if b.value < value then
      let l = restrict bool value b.l in
      let r = restrict bool value b.r in
      create b.value l r
    else if b.value = value then
      if bool then b.r else b.l
    else b

let exists value b =
  let l = restrict false value b in
  let r = restrict true value b in
  apply ( or ) l r
