(*** Representation of mu-calculus formulae ***)

open Printf

open Normalize
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
  | FNot of formula
  | FAnd of formula * formula
  | FOr of formula * formula
  | FImplies of formula * formula
  | FModal of modality * formula
  | FInvModal of modality * formula
  | FProp of string * formula list
  | FVar of string
  | FMu of string * nprocess list * formula
  | FNu of string * nprocess list * formula

let rec string_of_formula : formula -> string = function
  | FTrue -> "True"
  | FFalse -> "False"
  | FAnd(f,g) -> sprintf "(%s and %s)" (string_of_formula f) (string_of_formula g)
  | FOr(f,g) -> sprintf "(%s or %s)" (string_of_formula f) (string_of_formula g)
  | FImplies(f,g) -> sprintf "(%s ==> %s)" (string_of_formula f) (string_of_formula g)
  | FModal(m,f) -> (string_of_modality m) ^ (string_of_formula f)
  | FInvModal(m,f) ->  "~" ^ (string_of_modality m) ^ (string_of_formula f)
  | FProp(prop,params) -> prop ^ (string_of_collection "(" ")" "," string_of_formula params)
  | FVar var -> var
  | FNot f -> sprintf "not %s" (string_of_formula f)
  | FMu(x, env, f) ->
      sprintf "Mu(%s){%s}.%s" x (string_of_args string_of_nprocess env)
      (string_of_formula f)
  | FNu(x, env, f) ->
      sprintf "Nu(%s){%s}.%s" x (string_of_args string_of_nprocess env)
      (string_of_formula f)

type proposition = Proposition of string * string list * formula

let string_of_prop_header (Proposition(name, _, _)) =
  name

let string_of_proposition (Proposition(_, _, formula) as prop) =
  "prop " ^ (string_of_prop_header prop) ^ " = " ^ (string_of_formula formula)

let rec formula_of_preformula formula =
  printf "Transforming %s\n" @@ string_of_formula formula;
  match formula with
  | FTrue -> formula
  | FFalse ->  formula
  | FNot _ -> formula
  | FAnd (f1, f2) -> FAnd (formula_of_preformula f1, formula_of_preformula f2)
  | FOr (f1, f2) -> FOr (formula_of_preformula f1, formula_of_preformula f2)
  | FImplies (f1, f2) -> FImplies (formula_of_preformula f1, formula_of_preformula f2)
  | FModal (m, f) -> FModal (m, formula_of_preformula f)
  | FInvModal (m, f) -> FInvModal (m, formula_of_preformula f)
  | FProp (prop, params) ->
      printf "%s : Not implemented\n" @@ string_of_formula formula;
      FProp(prop, List.map formula_of_preformula params)
  | FVar _ ->
      printf "%s : Not implemented\n" @@ string_of_formula formula;
      formula
  | FMu (x, env, f) -> FMu (x, env, formula_of_preformula f)
  | FNu (x, env, f) -> FNu (x, env, formula_of_preformula f)
