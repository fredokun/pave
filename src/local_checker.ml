open Formula
open Syntax
open Presyntax

let (>>) h f = f h


let equals_preprefix_prefix prepre pre =
  match prepre, pre with
  | PTau, Tau -> true
  | PIn e, In n -> string_of_preexpr e = n
  | POut e, Out n -> string_of_preexpr e = n
  | PTau, _
  | PIn _, _
  | POut _, _ -> false
  | _ -> failwith "equals_prepre... TODO"

let is_action_in_list pre l =
  List.exists (fun e -> equals_preprefix_prefix e pre) l

let is_possibly = function
  | FPossibly _
  | FOutPossibly
  | FInPossibly
  | FAnyPossibly
  | FWPossibly _
  | FWOutPossibly
  | FWInPossibly
  | FWAnyPossibly -> true
  | _ -> false

(* returns the possibles sub processes after the action described by this modality *)
let rec modal_sub_processes modality process =
  match process, modality with
  | Silent, _ -> []

    (* unnamed actions *)
  | Prefix (Out _, proc), FOutPossibly
  | Prefix (In _, proc), FInPossibly
  | Prefix (_, proc), FAnyPossibly
  | Prefix (Out _, proc), FOutNecessity
  | Prefix (In _, proc), FInNecessity
  | Prefix (_, proc), FAnyNecessity -> [proc]

  | Prefix (Out _, proc), FWOutPossibly
  | Prefix (In _, proc), FWInPossibly
  | Prefix (_, proc), FWAnyPossibly
    -> proc :: (modal_sub_processes modality proc)

  | Prefix (_, proc), FWOutPossibly
  | Prefix (_, proc), FWInPossibly -> modal_sub_processes modality proc

    (* Compositions (+, ||) *)
  | Par (p1, p2), _ ->
    List.map (fun sub_p -> Par (sub_p, p2)) (modal_sub_processes modality p1)
    @ List.map (fun sub_p -> Par (p1, sub_p)) (modal_sub_processes modality p2)
  | Sum (p1, p2), _ ->
    (modal_sub_processes modality p1) @ (modal_sub_processes modality p2)

  (* Named actions *)
  | Prefix (pre, proc), FPossibly acts
  | Prefix (pre, proc), FNecessity acts ->
    if (is_action_in_list pre acts) then [proc] else []

  | Prefix (pre, proc), FWPossibly acts
  | Prefix (pre, proc), FWNecessity acts ->
    (if (is_action_in_list pre acts) then [proc] else [])
      @ (modal_sub_processes modality proc)

  | _ -> []

module Env = Map.Make(String)

let rec check_modality modality formula process =
  let sub_processes = modal_sub_processes modality process in
  List.iter (fun p -> Printf.printf "sub_processes : %s\n" (string_of_process p)) sub_processes;
  if (is_possibly modality)
  then List.exists (check_formula formula) sub_processes
  else List.for_all (check_formula formula) sub_processes


(* formule => mu calcul
   process => ccs
   
   Quick ref -> 
   | Fmodal -> [.] <.> ... etc

   | FInvModal of modality * formula -> not Fmodal
   | FProp of string * (string list) ?? to check
   | FVar of string ?? to check
   | FMu of string * formula
   | FNu of string * formula
   
*)

and check_formula_local env formula process =
  match formula with
    | FTrue -> true
    | FFalse -> false
    | FAnd (f1, f2) -> check_formula_local env f1 process && check_formula_local env f2 process
    | FOr (f1, f2) -> check_formula_local env f1 process || check_formula_local env f2 process
    | FImplies (f1, f2) -> not (check_formula_local env f1 process) || check_formula_local env f2 process
    | FModal (m, f) -> check_modality m f process
    | FInvModal (m, f) -> not (check_modality m f process)
    | FProp _ -> failwith "pas compris."
    | FVar id -> 
	check_formula_local env (Env.find id env) process

    | FMu (id, f) -> 
      (* let new_env = Env.add id f env in
      false || check_formula_local new_env f process *)
      false
    | FNu (id, f) -> 
      false
      (* let new_env = Env.add id f env in
      true && check_formula_local new_env f process *)

and check_formula form proc = 
  check_formula_local Env.empty form proc
