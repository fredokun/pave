
open Printf

open Utils

type preconstdef =
    PConstDef of String * int

let string_of_preconstdef = function
  | PConstDef (name,value) = sprintf "const %%%s = %d" name value
  
type pretypedef =
| PTDefRange of string * int * int
| PTDefEnum of string * SSet.t
    
let string_of_pretypedef = function
  | PTDefRange (name,min,max) = sprintf "type %s = [%d..%d]" name min max
  | PTDefEnum (name,names) = "type " ^ name ^ " = " ^ (string_of_set (fun x -> x) names)
  
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
  | PIn n -> sprintf "%s!" (string_of_preexpr n)
  | POut n -> sprintf "%s?" (string_of_preexpr n)
  | PReceive (c,x,t) -> sprintf "%s?(%s:%s)" (string_of_preexpr c) x t
  | PSend (c,e) -> sprintf "%s!%e" (string_of_preexor c) (string_of_preexpr e)

type preprocess =
  | PSilent
  | PPrefix of preprefix * preprocess
  | PSum of process * preprocess
  | PPar of process * preprocess
  | PRes of preexpr * preprocess
  | PCall of string * preexpr list
  | PRename of preexpr * preexpr * process
  | PGuard of preexpr * preprocess

let rec string_of_preprocess = function
  | PSilent -> "0"
  | PPrefix(a,p) -> sprintf "%s,%s" (string_of_preprefix a) (string_of_preprocess p)
  | PSum(p,q) -> sprintf "(%s+%s)" (string_of_preprocess p) (string_of_preprocess q)
  | PPar(p,q) -> sprintf "(%s||%s)" (string_of_preprocess p) (string_of_preprocess q)
  | PRes(n,p) -> sprintf "new(%s)[%s]" n (string_of_preprocess p)
  | PCall(d,es) -> d ^ (string_of_args string_of_preexpr es)
  | PRename(old,value,p) -> sprintf "(%s)[%s/%s]" (string_of_preprocess p)  value old
  | PGuard(g,p) -> sprintf "when (%s) %s" (string_of_preexpr g) (string_of_preprocess p)

type preparam =
  | PParam of string * string
  | PParamBool of bool
  | PParamName of name
  | PParamInt of int

let string_of_preparam = function
  | PParam (x,t) -> sprintf "%s:%t" x t
  | PParamBool b -> if b then "true" else "false"
  | PParamName n -> n
  | PParamInt n -> string_of_int n

type predefinition = PDefinition of string * preparam list * preprocess

let string_of_predef_header (PDefinition (name,params,_)) = 
  name ^ (string_of_args string_of_preparam params)

let string_of_predefinition = function
  | PDefinition (_,_,body) as def ->
    "def " ^ (string_of_predef_header def) ^ " = " ^ (string_of_preprocess body)
