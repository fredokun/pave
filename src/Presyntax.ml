
open Printf

open Utils

open Syntax

exception Typedef_Exception of string
exception Vardef_Exception of string ;;

let env_const = ref SMap.empty ;;
let env_var = ref SMap.empty ;;


type preconstdef =
| PConstDef of string * int

let string_of_preconstdef = function
  | PConstDef (name,value) -> sprintf "const %%%s = %d" name value

type pretypedef =
| PTDefRange of string * int * int
| PTDefEnum of string * SSet.t




let env_type =
  let bool_type = PTDefEnum( "Bool", (SSet.add "True" (SSet.add "False" SSet.empty)))
  in ref (SMap.add "Bool" bool_type SMap.empty) ;;

let add_to_env_type k v =
   env_type := SMap.add k v !env_type
;;


let string_of_pretypedef = function
  | PTDefRange (name,min,max) -> sprintf "type %s = [%d..%d]" name min max
  | PTDefEnum (name,names) -> "type " ^ name ^ " = " ^ (string_of_set (fun x -> x) names)

type preexpr =
| PTrue
| PFalse
| PInt of int
| PName of string
| PConst of string
| PVar of string
| PNot of preexpr
| PAnd of preexpr * preexpr
| POr of preexpr * preexpr
| PAdd of preexpr * preexpr
| PSub of preexpr * preexpr
| PMul of preexpr * preexpr
| PDiv of preexpr * preexpr
| PMod of preexpr * preexpr
| PInf of preexpr * preexpr
| PSup of preexpr * preexpr
| PEq of preexpr * preexpr
| PNeq of preexpr * preexpr
| PInfEq of preexpr * preexpr
| PSupEq of preexpr * preexpr
| PIf of preexpr * preexpr * preexpr

exception Type_Exception of string

let bool_of_value = function
  | Bool b -> b
  | Name n -> raise (Type_Exception (sprintf "Name %s was received where Bool was expected !!!" n))
  | Int i -> raise (Type_Exception (sprintf "Int %d was received where Bool was expected !!!" i))

let strname_of_value = function
  | Bool b -> raise (Type_Exception (sprintf "Bool %s was received where String was expected !!!" (if b then "true" else "false")))
  | Name n -> n
  | Int i -> raise (Type_Exception (sprintf "Int %d was received where String was expected !!!" i))

let int_of_value = function
  | Bool b -> raise (Type_Exception (sprintf "Bool %s was received where Int was expected !!!" (if b then "true" else "false")))
  | Name n -> raise (Type_Exception (sprintf "Name %s was received where Int was expected !!!" n))
  | Int i -> i

let rec interprete_preexpr : preexpr -> value = function
  | PTrue -> Bool true
  | PFalse -> Bool false
  | PInt i -> Int i
  | PName str -> Name str
  | PConst name -> Int (SMap.find name !env_const)
  | PVar name -> begin
      try (SMap.find name !env_var) with Not_found -> raise @@ Vardef_Exception name
    end
  | PNot pexpr -> let b = bool_of_value (interprete_preexpr pexpr) in Bool (not b)
  | PAnd (preexpr1, preexpr2) ->
    let b1 = bool_of_value (interprete_preexpr preexpr1)
    and b2 = bool_of_value (interprete_preexpr preexpr2) in
    Bool ( b1 && b2 )
  | POr (preexpr1, preexpr2) ->
    let b1 = bool_of_value (interprete_preexpr preexpr1)
    and b2 = bool_of_value (interprete_preexpr preexpr2) in
    Bool ( b1 || b2 )

  | PAdd (preexpr1, preexpr2) ->
    let i1 = int_of_value (interprete_preexpr preexpr1 )
    and i2 = int_of_value ( interprete_preexpr preexpr2 ) in
    Int ( i1 + i2 )

  | PSub (preexpr1, preexpr2) ->
    let i1 = int_of_value (interprete_preexpr preexpr1 )
    and i2 = int_of_value ( interprete_preexpr preexpr2 ) in
    Int ( i1 - i2 )

  | PMul (preexpr1, preexpr2) ->
    let i1 = int_of_value (interprete_preexpr preexpr1 )
    and i2 = int_of_value ( interprete_preexpr preexpr2 ) in
    Int ( i1 * i2 )

  | PDiv (preexpr1, preexpr2) ->
    let i1 = int_of_value (interprete_preexpr preexpr1 )
    and i2 = int_of_value ( interprete_preexpr preexpr2 ) in
    Int ( i1 / i2 )

  | PMod (preexpr1, preexpr2) ->
    let i1 = int_of_value (interprete_preexpr preexpr1 )
    and i2 = int_of_value ( interprete_preexpr preexpr2 ) in
    Int ( i1 mod i2 )

  | PInf (preexpr1, preexpr2) ->
    let i1 = int_of_value (interprete_preexpr preexpr1 )
    and i2 = int_of_value ( interprete_preexpr preexpr2 ) in
    Bool ( i1 < i2 )

  | PSup (preexpr1, preexpr2) ->
    let i1 = int_of_value (interprete_preexpr preexpr1 )
    and i2 = int_of_value ( interprete_preexpr preexpr2 ) in
    Bool ( i1 > i2 )

  | PEq (preexpr1, preexpr2) ->
    let p1 = interprete_preexpr preexpr1
    and p2 = interprete_preexpr preexpr2 in
    (match (p1, p2) with
    | (Bool b1, Bool b2) -> Bool ( b1 = b2 )
    | (Int i1, Int i2) -> Bool ( i1 = i2 )
    | (Name n1, Name n2) -> Bool ( n1 = n2 )
    | (_, _) -> Bool ( false ))

  | PNeq (preexpr1, preexpr2) ->
    let p1 = interprete_preexpr preexpr1
    and p2 = interprete_preexpr preexpr2 in
    (match (p1, p2) with
    | (Bool b1, Bool b2) -> Bool ( b1 <> b2 )
    | (Int i1, Int i2) -> Bool ( i1 <> i2 )
    | (Name n1, Name n2) -> Bool ( n1 <> n2 )
    | (_, _) -> Bool ( true ))

  | PInfEq (preexpr1, preexpr2) ->
    let i1 = int_of_value (interprete_preexpr preexpr1 )
    and i2 = int_of_value ( interprete_preexpr preexpr2 ) in
    Bool ( i1 <= i2 )

  | PSupEq (preexpr1, preexpr2) ->
    let i1 = int_of_value (interprete_preexpr preexpr1 )
    and i2 = int_of_value ( interprete_preexpr preexpr2 ) in
    Bool ( i1 >= i2 )

  | PIf (cond, preexpr1, preexpr2) ->
    let b = bool_of_value (interprete_preexpr cond) in
    if b then
      interprete_preexpr preexpr1
    else
      interprete_preexpr preexpr2
;;

let rec string_of_preexpr = function
  | PTrue -> "true"
  | PFalse -> "false"
  | PInt n -> string_of_int n
  | PName n -> n
  | PConst c -> c
  | PVar v -> v
  | PNot e -> sprintf "not(%s)" (string_of_preexpr e)
  | PAnd (e1,e2) -> sprintf "(%s) and (%s)" (string_of_preexpr e1) (string_of_preexpr e2)
  | POr (e1,e2) -> sprintf "(%s) or (%s)" (string_of_preexpr e1) (string_of_preexpr e2)
  | PAdd (e1,e2) -> sprintf "(%s) + (%s)" (string_of_preexpr e1) (string_of_preexpr e2)
  | PSub (e1,e2) -> sprintf "(%s) - (%s)" (string_of_preexpr e1) (string_of_preexpr e2)
  | PMul (e1,e2) -> sprintf "(%s) * (%s)" (string_of_preexpr e1) (string_of_preexpr e2)
  | PDiv (e1,e2) -> sprintf "(%s) / (%s)" (string_of_preexpr e1) (string_of_preexpr e2)
  | PMod (e1,e2) -> sprintf "(%s) %% (%s)" (string_of_preexpr e1) (string_of_preexpr e2)
  | PInf (e1,e2) -> sprintf "(%s) < (%s)" (string_of_preexpr e1) (string_of_preexpr e2)
  | PSup (e1,e2) -> sprintf "(%s) > (%s)" (string_of_preexpr e1) (string_of_preexpr e2)
  | PEq (e1,e2) -> sprintf "(%s) = (%s)" (string_of_preexpr e1) (string_of_preexpr e2)
  | PNeq (e1,e2) -> sprintf "(%s) <> (%s)" (string_of_preexpr e1) (string_of_preexpr e2)
  | PInfEq (e1,e2) -> sprintf "(%s) <= (%s)" (string_of_preexpr e1) (string_of_preexpr e2)
  | PSupEq (e1,e2) -> sprintf "(%s) >= (%s)" (string_of_preexpr e1) (string_of_preexpr e2)
  | PIf (c,e1,e2) -> sprintf "if (%s) then (%s) else (%s)" (string_of_preexpr c) (string_of_preexpr e1) (string_of_preexpr e2)

type preprefix =
  | PTau
  | PIn of preexpr
  | POut of preexpr
  | PReceive of preexpr * string * string
  | PSend of preexpr * preexpr

let string_of_preprefix = function
  | PTau -> "tau"
  | PIn n -> sprintf "%s?" (string_of_preexpr n)
  | POut n -> sprintf "%s!" (string_of_preexpr n)
  | PReceive (c,x,t) -> sprintf "%s?(%s:%s)" (string_of_preexpr c) x t
  | PSend (c,e) -> sprintf "%s!%s" (string_of_preexpr c) (string_of_preexpr e)

type preprocess =
| PSilent
| PPrefix of preprefix * preprocess
| PSum of preprocess * preprocess
| PPar of preprocess * preprocess
| PRes of name * preprocess
| PCall of string * preexpr list
| PRename of name * name * preprocess
| PGuard of preexpr * preprocess

let rec string_of_preprocess = function
  | PSilent -> "0"
  | PPrefix(a,p) -> sprintf "%s,%s" (string_of_preprefix a) (string_of_preprocess p)
  | PSum(p,q) -> sprintf "( %s + %s )" (string_of_preprocess p) (string_of_preprocess q)
  | PPar(p,q) -> sprintf "(%s||%s)" (string_of_preprocess p) (string_of_preprocess q)
  | PRes(n,p) -> sprintf "new(%s)[%s]" n (string_of_preprocess p)
  | PCall(d,es) -> d ^ (string_of_args string_of_preexpr es)
  | PRename(old,value,p) -> sprintf "(%s)[%s/%s]" (string_of_preprocess p)  value old
  | PGuard(g,p) -> sprintf "when (%s) %s" (string_of_preexpr g) (string_of_preprocess p)



let make_int_list min max =
  let rec make_aux m =
    if m < max then
      (Int m)::( make_aux  (m + 1))
    else
      [Int max]
  in
  make_aux min

let value_list : pretypedef -> (value list) = function
  | PTDefRange (_, min,max) ->(make_int_list min max)
  | PTDefEnum ("Bool" , _) -> [Bool true; Bool false]
  | PTDefEnum (_ , enum) -> (List.map (fun a -> Name a) (SSet.elements enum))

let rec process_of_receive : string -> string -> pretypedef -> preprocess -> process =
  fun canal nomVar theType pproc ->
    let val_list = value_list theType  in
    let rec process_of_receive_aux v_list=
      match v_list with
      | [] -> failwith "Empty list"
      | hd::[] -> (env_var := (SMap.add nomVar hd !env_var);
		   Prefix( In( sprintf "%s_%s" canal
				 (string_of_value hd)), (process_of_preprocess pproc) ))
      | hd::tl ->
	env_var:=(SMap.add nomVar hd !env_var);
	let pref = Prefix( In( sprintf "%s_%s" canal
				 (string_of_value hd)), (process_of_preprocess pproc) ) in
	Sum( pref, process_of_receive_aux tl)
    in
    process_of_receive_aux val_list
(*  au matching PReceive on a duplication des fils dans l'AST*)
and process_of_prefix : preprefix -> preprocess -> process =
  fun pfix pproc ->
    match pfix with
    | PTau -> Prefix(Tau, (process_of_preprocess pproc) )
    | PIn (pexpr) -> Prefix( In ( string_of_value (interprete_preexpr pexpr)),
			     (process_of_preprocess pproc) )
    | POut(pexpr) -> Prefix( Out ( string_of_value (interprete_preexpr pexpr)),
			     (process_of_preprocess pproc) )

    | PSend(pexprCanal, pexprVal) -> Prefix( Out ( sprintf "%s_%s"
						     (string_of_value (interprete_preexpr pexprCanal))
						     (string_of_value (interprete_preexpr pexprVal)) ),
					     (process_of_preprocess pproc))
    | PReceive(pexprCanal, nomVar, nomType) ->
      (if SMap.mem nomVar !env_var then
	  raise (Vardef_Exception nomVar));
      let canal = string_of_value (interprete_preexpr pexprCanal)
      and theType = SMap.find nomType !env_type in
      let prc = process_of_receive canal nomVar theType pproc in
      (env_var := SMap.remove nomVar !env_var;
       prc)
and process_of_preprocess : preprocess -> process =
  fun preproc ->
    printf "Transforming process:\n%s\n%!" (string_of_preprocess preproc) ;
    match preproc with
    | PSilent -> Silent
    | PPrefix (pfix, pproc) -> process_of_prefix pfix pproc

    | PSum (pproc1, pproc2) ->
      Sum( (process_of_preprocess pproc1),
	   (process_of_preprocess pproc2) )

    | PPar (pproc1, pproc2) ->
      Par( (process_of_preprocess pproc1),
	   (process_of_preprocess pproc2) )

    | PRes (nvar, pproc) ->
      Res(nvar, (process_of_preprocess pproc) )

    | PCall( nom, pexprList) -> Call (nom,
                                      (List.map interprete_preexpr pexprList))

    | PRename( oldName, newName , pproc) ->
      Rename( oldName, newName, (process_of_preprocess pproc) )

    | PGuard( pexpr, ppro) ->
      let b = bool_of_value (interprete_preexpr pexpr) in
      if b then
	process_of_preprocess ppro
      else
	Silent

type preparam =
| PParamVar of string * string
| PParamBool of bool
| PParamName of name
| PParamInt of int

let string_of_preparam = function
  | PParamVar (x,t) -> sprintf "%s:%s" x t
  | PParamBool b -> if b then "true" else "false"
  | PParamName n -> n
  | PParamInt n -> string_of_int n

type predefinition = PDefinition of string * preparam list * preprocess

let string_of_predef_header (PDefinition (name,params,_)) =
  name ^ (string_of_args string_of_preparam params)

let string_of_predefinition = function
  | PDefinition (_,_,body) as def ->
    "def " ^ (string_of_predef_header def) ^ " = " ^ (string_of_preprocess body)

let definitions_of_predefinition : predefinition -> definition list =
  function predef ->
    let PDefinition (name, preparams, preproc) = predef in
    (* let rec def_of_predef_aux : string -> value list -> preparam list -> preprocess -> definition list= *)
    (*   function name computed_params preparams preproc -> *)
    let rec def_of_predef_aux  name computed_params preparams preproc =
	match preparams with
	| [] -> [ Definition (name, computed_params, process_of_preprocess preproc) ]
	| (PParamBool b)::tl -> def_of_predef_aux name
    (computed_params@[Bool b]) tl preproc
	| (PParamName n)::tl -> def_of_predef_aux name
    (computed_params@[Name n]) tl preproc
	| (PParamInt i)::tl -> def_of_predef_aux name
    (computed_params@[Int i]) tl preproc
	| (PParamVar (nomVar, theType))::tl ->
	  (if SMap.mem nomVar !env_var then
	      raise @@ Vardef_Exception nomVar);
	  let val_list =
            try value_list (SMap.find theType !env_type) with Not_found -> raise @@ Typedef_Exception theType
          in
	  let def_list = List.map (function v ->
	    env_var := (SMap.add nomVar v !env_var);
	    (def_of_predef_aux name (computed_params@[v]) tl preproc) )
	    val_list
	  in
	  (env_var := SMap.remove nomVar !env_var;
	   List.flatten def_list)
    in
    printf "Transforming definition:\n%s\n%!"
      (string_of_predefinition predef) ;
    def_of_predef_aux name [] preparams preproc


