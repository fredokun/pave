open Printf
open Utils

(******************************************)
(*** Partie 1 : définitions syntaxiques ***)
(******************************************)

(* Noms manipulés dans CCS *)
type name = string

(* Encodage des valeurs utilisées: booléens, noms symboliques et entiers *)
type value =
  | Bool of bool
  | Name of name
  | Int of int

let rec string_of_value = function
  | Bool b -> if b then "true" else "false"
  | Name n -> n
  | Int i -> string_of_int i

(* Préfixes de processus *)
type prefix =
  | Tau
  | In of name
  | Out of name

let string_of_prefix = function
  | Tau -> tau_str
  | In(n) -> n ^ "?"
  | Out(n) -> n ^ "!"

(* Structure inductive de la syntaxe des processus CCS *)
type process =
  | Silent
  | Prefix of prefix * process
  | Sum of process * process
  | Par of process * process
  | Res of name * process
  | Call of string * value list
  | Rename of name * name * process

let rec string_of_process = function
  | Silent -> "0"
  | Prefix(a,p) -> sprintf "%s,%s" (string_of_prefix a) (string_of_process p)
  | Sum(p,q) -> sprintf "(%s+%s)" (string_of_process p) (string_of_process q)
  | Par(p,q) -> sprintf "(%s||%s)" (string_of_process p) (string_of_process q)
  | Res(n,p) -> sprintf "new(%s)[%s]" n (string_of_process p)
  | Call(d,vs) -> d ^ (string_of_args string_of_value vs)
  | Rename(old,value,p) -> sprintf "(%s)[%s/%s]" (string_of_process p)  value old

(* Définitions de processus *)
type definition = Definition of string * value list * process

let def_name = function
  | Definition (name,_,_) -> name

let def_values = function
  | Definition (_,values,_) -> values

let def_body = function
  | Definition (_,_,body) -> body

let string_of_def_header (Definition (name,values,_)) = 
  name ^ (string_of_args string_of_value values)

let string_of_definition = function
  | Definition (_,_,body) as def ->
    "def " ^ (string_of_def_header def) ^ " = " ^ (string_of_process body)


(**************************************************)
(*** Partie 2 :  Noms, noms libres et noms liés ***)
(**************************************************)

let freeNamesOfPrefix = function
  | Tau -> SSet.empty
  | In(n) -> SSet.singleton n
  | Out(n) -> SSet.singleton n

let boundNamesOfPrefix _ = SSet.empty

let namesOfPrefix a = SSet.union (freeNamesOfPrefix a) (boundNamesOfPrefix a)

let freeNamesOfValue = function
  | Name(n) -> SSet.singleton n
  | _ -> SSet.empty

let boundNamesOfValue _ = SSet.empty

let namesOfValue a = SSet.union (freeNamesOfValue a) (boundNamesOfValue a)

let rec freeNamesOfValues = function
  | [] -> SSet.empty
  | v::vs -> SSet.union (freeNamesOfValue v) (freeNamesOfValues vs)

let rec boundNamesOfValues = function
  | [] -> SSet.empty
  | v::vs -> SSet.union (boundNamesOfValue v) (boundNamesOfValues vs)

let rec namesOfValues vs =
  SSet.union (freeNamesOfValues vs) (boundNamesOfValues vs)

(* freeNames: process -> SSet.t *)
let rec freeNames = function
  | Call (_, vs) -> 
    List.fold_left (fun fn v -> match v with
    | Name n -> SSet.add n fn
    | _ -> fn) SSet.empty vs
  | Silent -> SSet.empty
  | Prefix (Tau, proc) -> freeNames proc
  | Prefix (In name, proc) | Prefix (Out name, proc) ->
      SSet.add name (freeNames proc)
  | Sum (proc1, proc2) | Par (proc1, proc2) ->
      SSet.union (freeNames proc1) (freeNames proc2)
  | Res (name, proc) -> SSet.remove name (freeNames proc)
  | Rename (old , value , proc) ->  
    let fn = freeNames proc
    in (* XXX: this is not clear 
      if SSet.mem old fn
      then SSet.add value (SSet.remove old fn)
      else fn *)
      SSet.add old (SSet.add value fn)

(* boundNames: process -> SSet.t *)
let boundNames proc =
  let rec f = function
    | Call (_, _) | Silent -> SSet.empty
    | Prefix (_, proc) -> f proc
    | Sum (proc1, proc2) | Par (proc1, proc2) -> SSet.union (f proc1) (f proc2)
    | Res (name, proc) -> SSet.add name (f proc)
    | Rename (_,_,proc) -> f proc
  in
    f proc

(* names: process -> SSet.t *)
let names p = SSet.union (freeNames p) (boundNames p)

(*****************************************)
(*** Partie 3 :  Substitutions de noms ***)
(*****************************************)

let fresh p forbid =
  let ns = names p
  in let rec try_fresh n =
       let fname = ("f_" ^ (string_of_int n))
       in  if (SSet.mem fname  ns) || (SSet.mem fname forbid)
	 then try_fresh (n+1)
	 else fname
     in try_fresh 0

let substPrefix p m n = match p with
  | Tau -> Tau
  | In(a) -> if a = n then (In m) else (In a)
  | Out(a) -> if a = n then (Out m) else (Out a)
  
let substName a b c = if a = c then b else a 

let substValue v m n = match v with
  | Name a -> Name (substName a m n)
  | _ -> v
	
let rec subst p m (* overrides *) n = 
  match p with
    | Silent -> Silent
    | Prefix(a,q) -> Prefix((substPrefix a m n),(subst q m n))
    | Sum(q,r) -> Sum((subst q m n),(subst r m n))
    | Par(q,r) -> Par((subst q m n),(subst r m n))
    | Res(a,q) -> 
      if a = n
      then Res(a,q)
      else if a = m
      then let fname = fresh q SSet.empty
	   in Res(fname, (subst (subst q fname a) m n))
      else Res(a,(subst q m n))
    | Call(d,vs) -> Call(d,(List.map (fun v -> substValue v m n) vs))
    | Rename (old,value,q) -> Rename(substName old m n,substName value m n,subst q m n) 

let rec substs p ms ns = match (ms,ns) with
  | ([],[]) -> p
  | ([],_) -> failwith "substs: bad cosupport"
  | (_,[]) -> failwith "substs: bad support"
  | (m::ms',n::ns') -> substs (subst p m n) ms' ns'



