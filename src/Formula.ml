(*** Representation of mu-calculus formulae ***)

open Printf

open Syntax
open Utils

(* mu-calculus formulae *)

type modality =
  | FPossibly of prefix list
  | FOutPossibly
  | FInPossibly
  | FAnyPossibly
  | FWPossibly of prefix list
  | FWOutPossibly
  | FWInPossibly
  | FWAnyPossibly
  | FNecessity of prefix list
  | FOutNecessity
  | FInNecessity
  | FAnyNecessity
  | FWNecessity of prefix list
  | FWOutNecessity
  | FWInNecessity
  | FWAnyNecessity

let string_of_modality : modality -> string = function
  | FPossibly(acts) -> string_of_collection "<" ">" ","  string_of_prefix acts
  | FOutPossibly -> "<!>"
  | FInPossibly -> "<?>"
  | FAnyPossibly -> "<.>"
  | FWPossibly(acts) -> string_of_collection "<<" ">>" ","  string_of_prefix acts
  | FWOutPossibly -> "<<!>>"
  | FWInPossibly -> "<<?>>"
  | FWAnyPossibly -> "<<.>>"
  | FNecessity(acts) -> string_of_collection "[" "]" ","  string_of_prefix acts
  | FOutNecessity -> "[!]"
  | FInNecessity -> "[?]"
  | FAnyNecessity -> "[.]"
  | FWNecessity(acts) -> string_of_collection "[[" "]]" ","  string_of_prefix acts
  | FWOutNecessity -> "[[!]]"
  | FWInNecessity -> "[[?]]"
  | FWAnyNecessity -> "[[.]]"

type formula = 
  | FTrue
  | FFalse
  | FAnd of formula * formula
  | FOr of formula * formula
  | FImplies of formula * formula
  | FModal of modality * formula
  | FInvModal of modality * formula
  | FProp of string * (string list)
 
let rec string_of_formula : formula -> string = function
  | FTrue -> "True"
  | FFalse -> "False"
  | FAnd(f,g) -> sprintf "(%s and %s)" (string_of_formula f) (string_of_formula g)
  | FOr(f,g) -> sprintf "(%s or %s)" (string_of_formula f) (string_of_formula g)
  | FImplies(f,g) -> sprintf "(%s ==> %s)" (string_of_formula f) (string_of_formula g)
  | FModal(m,f) -> (string_of_modality m) ^ (string_of_formula f)
  | FInvModal(m,f) ->  "~" ^ (string_of_modality m) ^ (string_of_formula f)
  | FProp(prop,params) -> prop ^ (string_of_collection "(" ")" "," (fun s -> s) params)

