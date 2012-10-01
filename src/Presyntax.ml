
open Printf

open Utils

type preconstdef =
    PConstDef of String * int

let string_of_preconstdef = function
  | PConstDef (name,value) = sprintf "const %%%s = %d" name value

type pretypedef =
    PTDefRange of string * int * int
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
  | PMult of preexpr * preexpr
  | PDiv of preexpr * preexpr
  | PMod of preexpr * preexpr
  | PInf of preexpr * preexpr
  | PSup of preexpr * preexpr
  | PEq of preexpr * preexpr
  | PNeq of preexpr * preexpr
  | PInfEq of preexpr * preexpr
  | PSupEq of preexpr * preexpr
  | PIf of preexpr * preexpr * preexpr

type preprefix =
  | PTau
  | PIn of preexpr
  | POut of preexpr
  | PReceive of preexpr * string * string
  | PSend of preexpr * preexpr

type preprocess =
  | PSilent
  | PPrefix of preprefix * preprocess
  | PSum of process * preprocess
  | PPar of process * preprocess
  | PRes of preexpr * preprocess
  | PCall of string * preexpr list
  | PRename of preexpr * preexpr * process
  | PGuard of preexpr * preprocess

type preparam =
  | PParam of string * string
  | PParamBool of bool
  | PParamName of name
  | PParamInt of int

type predefinition = Definition of string * preparam list * process

