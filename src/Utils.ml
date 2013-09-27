open Printf

(* global parser exception *)

exception Fatal_Parse_Error of string ;;

(* string sets and maps *)

module SSet = Set.Make(String)
module SMap = Map.Make(String)

(* print utilities *)

let tau_str = "\207\132"

let string_of_collection (op:string) (cl:string) (sep:string)
    (tostr: 'a -> string) (lst: 'a list) =
  let rec str = function
    | [] -> ""
    | e::[] -> tostr e
    | e::es -> (tostr e) ^ sep ^ (str es)
  in
    op ^ (str lst) ^ cl

let string_of_list tostr lst = string_of_collection "[" "]" ";" tostr lst

let string_of_args tostr lst = string_of_collection "(" ")" "," tostr lst

let string_of_set tostr set =
  string_of_collection "{" "}" "," tostr (SSet.elements set)

let string_of_map map = 
  string_of_collection "{" "}" "," (fun (old,value) -> sprintf "%s/%s" value old) (SMap.bindings map)


(* test utilities *)

let checkEq descr e v =
  printf "%s " descr;
  try
    if e () = v then printf "(pass)\n%!"
    else printf "(fails)\n%!"
  with _ -> printf "(except)\n%!"

(* set utilities -> replaced by SSet (Set.Make (String)) *)

(* misc. *)
let ident n = n

let forget _ = ()

(* permutations:: 'a list -> 'a list list *)
let rec permutations =
  let rec inject_all e n l llen = 
    if n > llen then []
    else (inject e n l)::(inject_all e (n+1) l llen)
  and inject e n l =
    if n = 0 then e::l
    else (List.hd l)::(inject e (n-1) (List.tl l))
  in function
    | [] -> []
    | e::[] -> [[e]]
    | e::r ->
	List.fold_right (fun l ls -> (inject_all e 0 l (List.length l)) @ls)
	  (permutations r) []

(* take an element of a list, and get the list without the element *)

let list_take l n =
  let rec take head tail n =
    if n = 0 then (List.hd tail, (List.rev head) @ (List.tl tail))
    else take ((List.hd tail)::head) (List.tl tail) (n - 1)
  in take [] l n

let list_inject e n l =
  let rec inject n head tail =
    if n = 0 then (List.rev head) @ (e::tail)
    else inject (n - 1) (List.hd tail::head) (List.tl tail)
  in inject n [] l

let rec list_replace e n l =
  if n = 0 then e::(List.tl l)
  else (List.hd l)::(list_replace e (n-1) (List.tl l))
