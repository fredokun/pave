(*** Representation of mu-calculus formulae ***)

open Printf

open Presyntax
open Utils


(* mu-calculus formulae *)

type restr = Rin | Rout | Rany | Rpref of preprefix list
type existence = Possibly | Necessity
type strength = Weak | Strong
type modality = strength * existence * restr

let string_of_restr = function
  | Rout -> "!"
  | Rin -> "?"
  | Rany -> "."
  | Rpref acts -> string_of_collection_no_block "," string_of_preprefix acts

let string_of_existence = function Possibly -> sprintf "<%s>"
  | Necessity -> sprintf "[%s]"

let string_of_strongness f r = function Weak -> f (f r)
  | Strong -> f r

let string_of_modality (s, e, r) =
  string_of_strongness (string_of_existence e) (string_of_restr r) s


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

type proposition = Proposition of string * string list * formula

let string_of_prop_header (Proposition(name, params, _)) =
  name ^ (string_of_args (fun x -> x) params)

let string_of_proposition (Proposition(_, _, formula) as prop) =
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
