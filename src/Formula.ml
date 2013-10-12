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

type prop = string list * formula

let props : (string, prop) Hashtbl.t = Hashtbl.create 53

exception Formdef_exception of string
(* exception Unbound_variable of string *)
exception Unbound_prop of string

(* let rec verify_vars f idents = *)
(*   match f with *)
(*   | FVar v -> if not (List.mem v idents) then raise (Unbound_variable v) *)
(*   | FAnd (f,g) | FOr (f,g) | FImplies (f,g) -> *)
(*     verify_vars f idents; verify_vars g idents *)
(*   | FModal (_, f) | FInvModal (_, f) -> verify_vars f idents *)
(*   | FMu (x,f) | FNu (x,f) -> verify_vars f (x :: idents) *)
(*   | FProp (_, l) -> List.iter (fun v -> verify_vars (FVar v) idents) l *)
(*   | _ -> () *)

(** val add_prop : string -> string list -> formula -> unit *)
let add_prop name idents formula =
  if Hashtbl.mem props name then
    raise (Formdef_exception name)
  else
    begin
      (* verify_vars formula idents; *)
      Hashtbl.add props name (idents, formula)
    end

(** Bad understanding : vars aren't bound by props argument *)
(* let substitute f sub_list = *)
(*   let rec step sl = function *)
(*   | FVar v -> FVar (List.assoc v sl) *)
(*   | FTrue | FFalse as f -> f *)
(*   | FAnd (f, g) -> FAnd (step sl f, step sl g) *)
(*   | FOr (f, g) -> FOr (step sl f, step sl g) *)
(*   | FImplies (f, g) -> FImplies (step sl f, step sl g) *)
(*   | FModal(m, f) -> FModal (m, step sl f) *)
(*   | FInvModal (m, f) -> FInvModal (m, step sl f) *)
(*   | FMu (x, f) -> FMu (x, step ((x, x)::sl) f) *)
(*   | FNu (x, f) -> FNu (x, step ((x, x)::sl) f) *)
(*   | _ -> assert false (\* Technically, no Prop should remain ? *\) *)
(*   in *)
(*   step sub_list f *)

let formula_of_preformula pf =
  let rec step = function
    | FTrue | FFalse as f -> f
    | FAnd (f, g) -> FAnd (step f, step g)
    | FOr (f, g) -> FOr (step f, step g)
    | FImplies (f, g) -> FImplies (step f, step g)
    | FModal(m, f) -> FModal (m, step f)
    | FInvModal (m, f) -> FInvModal (m, step f)
    | FVar v -> FVar v
    | FMu (x, f) -> FMu (x, step f)
    | FNu (x, f) -> FNu (x, step f)
    | FProp (_, _) -> failwith "Something to do here ?"
      (* if Hashtbl.mem props s then *)
      (*   let (vars, formula) = Hashtbl.find props s in *)
      (*   substitute formula @@ List.combine vars il *)
      (* else *)
      (*   raise (Unbound_prop s) *)
  in
  Format.printf "Preformula received :\n%s@." @@ string_of_formula pf;
  let res = step pf in
  Format.printf "Result :\n%s@." @@ string_of_formula res;
  res
