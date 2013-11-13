(** Local checker *)
open Formula
open Syntax
open Presyntax

let (>>) h f = f h


type local_formula =
  | LTrue
  | LFalse
  | LAnd of formula * formula
  | LOr of formula * formula
  | LImplies of formula * formula
  | LModal of modality * formula
  | LInvModal of modality * formula
  | LProp of string * (string list)
  | LVar of string
  | LMu of string * formula
  | LNu of string * formula


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

let rec subst_proc id proc new_proc =
  match proc with
    | Silent
    | Call _

      -> proc

    | Prefix (pre, p) -> Prefix (pre, subst_proc id p new_proc)
    | Sum (p1, p2) -> Sum(subst_proc id p1 new_proc, subst_proc id p2 new_proc)
    | Par (p1, p2) -> Par(subst_proc id p1 new_proc, subst_proc id p2 new_proc)
    | Res (n, p) -> Res (n, subst_proc id p new_proc)

    | Rename (n1, n2, p) -> Rename (n1, n2, subst_proc id p new_proc)


(** @return the possibles sub processes after the action described by this modality *)
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

  | Res (name, proc), _ -> 
    print_endline "loop?";
    let p' = subst_proc name proc proc in
    modal_sub_processes modality p'
    

  | _ -> []

module Env = Map.Make(String)

let nu_env : process list ref = ref []

(** [subst_fix id B B'] substitue les occurences de la variable [id]
    (e.g, les X d'un nu) dans la formule [B] par [B'] *)
let rec subst_fix id f f' =
  match f with
    | FVar s when s = id -> f'

    | FTrue
    | FFalse
    | FProp _ (* ? *)
    | FVar _ -> f

    | FAnd (f1, f2) -> FAnd (subst_fix id f1 f', subst_fix id f2 f')
    | FOr (f1, f2) -> FOr (subst_fix id f1 f', subst_fix id f2 f')
    | FImplies (f1, f2) -> FImplies (subst_fix id f1 f', subst_fix id f2 f')
    | FModal (m, f) -> FModal (m, subst_fix id f f')
    | FInvModal (m, f) -> FInvModal (m, subst_fix id f f')
    | FMu (s, f) -> FMu(s, subst_fix id f f')
    | FNu (s, f) -> FNu(s, subst_fix id f f')


let rec check_modality modality formula process =
  print_endline "check_modality :";
  Printf.printf "m : %s, form : %s, proc : %s\n%!" (string_of_modality modality) (string_of_formula formula) (string_of_process process) ;
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
   | FVar of string -> var mu / nu seulement?
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
      (* let formula' =
        FNot (FNu (x, env, FNot (beta_reduce f x (FNot (FVar x)))))
      in loop formula' 
      => why ?*)

      (* let new_env = Env.add id f env in
	 false || check_formula_local new_env f process *)
      ignore id; ignore f;
      false
    | FNu (id, f) ->
      print_endline "@@@\ncurrent_env :";
      List.iter (fun p -> print_endline (string_of_process p)) !nu_env;
      print_endline "@@@";
 
      List.mem process !nu_env 
      ||
	begin
	  nu_env := process::!nu_env;
	  let b' = (subst_fix id f formula) in
	  print_endline "formula :"; string_of_formula b' >> print_endline;
	  check_formula_local env b' process
	end	 
      (*
	p satisfait vX{rvect}.B
	
	si p appartient à {rvect} alors
	vrai
	sinon 
	{
	soit B' le nouveau processus dans lequel on remplace 
	les occurences de X par vX{p,rvect}B,
	p satisfait B
	}
      *)

and check_formula form proc = 
  check_formula_local Env.empty form proc
