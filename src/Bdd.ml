(** Implementation of BDDs with hashconsing *)

type t = {id: int; l: t; r: t}

let rec null = {id = 0; l = null; r = null}

let rec one = {id = 1; l = null; r = null}
let rec zero = {id = 2; l = null; r = null}

type bdd = t

module S = struct
  type t = bdd

  let equal b1 b2 =
    b1.l == b2.l && b1.r == b2.r

  let hash b =
    29 * (b.l.id + (29 * b.r.id))

end

module H = Hashtbl.Make(S)

let create =
  let htbl = H.create 53 in
  let id = ref 4 in
  fun l r ->
    if l == r then l
    else
      let i = !id in
      let b = {id = i; l; r} in
      try
        H.find htbl b
      with
        Not_found ->
          H.add htbl b b;
          incr id;
          b
