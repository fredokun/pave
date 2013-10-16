(*** Representation of mu-calculus formulae ***)

open Printf

open Presyntax
open Utils


(* mu-calculus formulae *)

type modality =
  | FPossibly of preprefix list
  | FOutPossibly
  | FInPossibly
  | FAnyPossibly
  | FWPossibly of preprefix list
  | FWOutPossibly
  | FWInPossibly
  | FWAnyPossibly
  | FNecessity of preprefix list
  | FOutNecessity
  | FInNecessity
  | FAnyNecessity
  | FWNecessity of preprefix list
  | FWOutNecessity
  | FWInNecessity
  | FWAnyNecessity

let string_of_modality : modality -> string = function
  | FPossibly(acts) -> string_of_collection "<" ">" ","  string_of_preprefix acts
  | FOutPossibly -> "<!>"
  | FInPossibly -> "<?>"
  | FAnyPossibly -> "<.>"
  | FWPossibly(acts) -> string_of_collection "<<" ">>" ","  string_of_preprefix acts
  | FWOutPossibly -> "<<!>>"
  | FWInPossibly -> "<<?>>"
  | FWAnyPossibly -> "<<.>>"
  | FNecessity(acts) -> string_of_collection "[" "]" ","  string_of_preprefix acts
  | FOutNecessity -> "[!]"
  | FInNecessity -> "[?]"
  | FAnyNecessity -> "[.]"
  | FWNecessity(acts) -> string_of_collection "[[" "]]" ","  string_of_preprefix acts
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
  | FVar of string
  | FMu of string * formula
  | FNu of string * formula

let rec string_of_formula : formula -> string = function
  | FTrue -> "True"
  | FFalse -> "False"
  | FAnd(f,g) -> sprintf "(%s and %s)" (string_of_formula f) (string_of_formula g)
  | FOr(f,g) -> sprintf "(%s or %s)" (string_of_formula f) (string_of_formula g)
  | FImplies(f,g) -> sprintf "(%s ==> %s)" (string_of_formula f) (string_of_formula g)
  | FModal(m,f) -> (string_of_modality m) ^ (string_of_formula f)
  | FInvModal(m,f) ->  "~" ^ (string_of_modality m) ^ (string_of_formula f)
  | FProp(prop,params) -> prop ^ (string_of_collection "(" ")" "," (fun s -> s) params)
  | FVar(var) -> var
  | FMu(x,f) -> sprintf "Mu(%s).%s" x (string_of_formula f)
  | FNu(x,f) -> sprintf "Nu(%s).%s" x (string_of_formula f)

type proposition = string * string list * formula

let string_of_prop_header (name, params, _) = 
  name ^ (string_of_args (fun x -> x) params)

let string_of_proposition ((_, _, formula) as prop) =
  "prop " ^ (string_of_prop_header prop) ^ " = " ^ (string_of_formula formula)

let rec formula_of_preformula formula =
  printf "Transforming %s\n" @@ string_of_formula formula;
  match formula with
  | FTrue -> formula
  | FFalse ->  formula
  | FAnd (f1, f2) -> FAnd (formula_of_preformula f1, formula_of_preformula f2)
  | FOr (f1, f2) -> FOr (formula_of_preformula f1, formula_of_preformula f2)
  | FImplies (f1, f2) -> FImplies (formula_of_preformula f1, formula_of_preformula f2)
  | FModal (m, f) -> FModal (m, formula_of_preformula f)
  | FInvModal (m, f) -> FInvModal (m, formula_of_preformula f)
  | FProp (prop, params) -> 
      printf "%s : Not implemented\n" @@ string_of_formula formula;
      formula
  | FVar var -> 
      printf "%s : Not implemented\n" @@ string_of_formula formula;
      formula
  | FMu (x, f) -> FMu (x, formula_of_preformula f)
  | FNu (x, f) -> FNu (x, formula_of_preformula f)

