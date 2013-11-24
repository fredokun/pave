(*** Representation of mu-calculus formulae ***)

open Printf

open Presyntax
open Utils

(* mu-calculus formulae *)

exception Unsatisfied of string

type action = Any_in | Any_out | Any | Coll of preprefix list

type strength = Weak | Strong

type modality = Possibly of strength * action | Necessity of strength * action

let string_of_action = function
  | Any_in -> "?" 
  | Any_out -> "!" 
  | Any -> "."
  | Coll pres -> List.map string_of_preprefix pres >> String.concat ","

let string_of_modality m =
  let l,r = match m with Possibly _ -> "<",">" | Necessity _ -> "[","]" in
  match m with
    | Possibly (s,a)
    | Necessity (s,a) -> 
      let act_str = string_of_action a in
      match s with
	| Weak -> sprintf "%s%s%s" (l^l) act_str (r^r)
	| Strong -> sprintf "%s%s%s" l act_str r

type formula = 
  | FTrue
  | FFalse
  | FAnd of formula * formula
  | FOr of formula * formula
  | FNot of formula
  | FImplies of formula * formula
  | FModal of modality * formula
  | FInvModal of modality * formula
  | FProp of string * formula list
  | FVar of string
  (* +env for local model checking algorithm *)
  | FMu of string * Semop.PSet.t * formula
  | FNu of string * Semop.PSet.t * formula
 
let rec string_of_formula : formula -> string = function
  | FTrue -> "true"
  | FFalse -> "false"
  | FAnd(f,g) -> sprintf "(%s and %s)" (string_of_formula f) (string_of_formula g)
  | FOr(f,g) -> sprintf "(%s or %s)" (string_of_formula f) (string_of_formula g)
  | FImplies(f,g) -> sprintf "(%s ==> %s)" (string_of_formula f) (string_of_formula g)
  | FNot f -> sprintf "¬%s" (string_of_formula f)
  | FModal(m,f) -> (string_of_modality m) ^ (string_of_formula f)
  | FInvModal(m,f) ->  "~" ^ (string_of_modality m) ^ (string_of_formula f)
  | FProp(prop,params) -> prop ^ (string_of_collection "(" ")" "," (fun s -> s) 
				    (List.map string_of_formula params))
  | FVar(var) -> var
  | FMu(x,_,f) -> sprintf "µ%s.%s" x (string_of_formula f)
  | FNu(x,_,f) -> sprintf "ν%s.%s" x (string_of_formula f)

let is_weak_modality = function
  | (Possibly (Weak, _) | Necessity (Weak, _)) -> true
  | _ -> false

let formula_of_preformula formula = formula
