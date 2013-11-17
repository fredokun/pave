(** Local checker *)
open Formula
open Syntax
open Presyntax

let (>>) h f = f h

(** {3 utility functions } *)

let equals_preprefix_prefix prepre pre =
  match prepre, pre with
  | PTau, Tau -> true
  | PIn e, In n -> string_of_preexpr e = n
  | POut e, Out n -> string_of_preexpr e = n
  | PTau, _
  | PIn _, _
  | POut _, _ -> false
  | PReceive _, _ 
  | PSend _, _ -> failwith "PReceive - PSend : Not implemented yet"


let is_action_in_list pre l =
  List.exists (fun e -> equals_preprefix_prefix e pre) l

let is_possibly = function
  | Possibly _ -> true | _ -> false

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
    | FNot f -> FNot (subst_fix id f f')
    | FImplies (f1, f2) -> FImplies (subst_fix id f1 f', subst_fix id f2 f')
    | FModal (m, f) -> FModal (m, subst_fix id f f')
    | FInvModal (m, f) -> FInvModal (m, subst_fix id f f')
    | FMu (s, env, f) -> FMu(s, env, subst_fix id f f')
    | FNu (s, env, f) -> FNu(s, env, subst_fix id f f')


(* Todo faire des tests d'exhaustivité *)
(* [[a!]]P ===? µX.[a!](µY.[tau]Y v [.]P) v [tau]X *)
let handle_weak_modalities modality process =
  (* Retire les premiers tau du processus et retourne les ensembles du reste du processus
  e.g: [[?]] avec Tau,Tau,c?,Tau,d! retourne Tau,d! *)
  let rec remove_first_part = function
    | (Possibly (Weak, Any) | Necessity (Weak, Any)), Prefix(Tau, proc)
      -> [proc]
    | (Possibly (Weak, Coll l) | Necessity (Weak, Coll l)), Prefix(Tau, proc) when is_action_in_list Tau l
	-> [proc]

    (* On esquive les tau *)
    | _, Prefix (Tau, proc) ->
      remove_first_part (modality, proc)
	
    (* In *)
    | (Possibly (Weak, (Any | Any_in)) | Necessity (Weak, (Any | Any_in))), Prefix (In n, proc) 
            
    (* Out *)
    | (Possibly (Weak, (Any | Any_out)) | Necessity (Weak, (Any | Any_out))), Prefix (Out n, proc)
      -> [proc]
      
    (* Var *)
    | (Possibly (Weak, Coll l) | Necessity (Weak, Coll l)), Prefix (prefix, proc)
      when is_action_in_list prefix l
	-> assert (prefix <> Tau); [proc]

    | _, Par (p1, p2) ->
      let sub_p1 = remove_first_part (modality, p1) in
      let sub_p2 = remove_first_part (modality, p2) in
      
      List.map (fun sub_p -> Par (sub_p, p2)) (remove_first_part (modality, p1))
      @ List.map (fun sub_p -> Par (p1, sub_p)) (remove_first_part (modality, p2))
    | _, Sum (p1, p2) ->
      remove_first_part (modality, p1) @ remove_first_part (modality, p2)


    | _, Res (name, proc) -> failwith "rm-first - Res : not handled yet"
    | _, Call (name, vl) -> failwith "rm-first - Call : not handled yet"
    | _, Rename (n1, n2, proc) -> failwith "rm-first - Rename : not handled yet"

    | _ -> []
  in
  (* On "slurp" tous les tau restants *)
  let rec remove_last_part = function
    | Prefix (Tau, proc) ->
      remove_last_part proc
    
    | Par (p1, p2) ->
      let sub_p1 = remove_last_part p1 in
      let sub_p2 = remove_last_part p2 in
      List.map (fun p1 -> List.map (fun p2 -> Par(p1, p2)) sub_p2) sub_p1
      >> List.flatten 

    | Sum (p1, p2) ->
      remove_last_part p1 @ remove_last_part p2

    | Prefix(_, _) as id -> [id]

    | Res (name, proc) -> failwith "rm_last - Res : not handled yet"
    | Call (name, vl) -> failwith "rm_last - Call : not handled yet"
    | Rename (n1, n2, proc) -> failwith "rm_last - Rename : not handled yet"

  in
  let first_parts = remove_first_part (modality, process) in
  List.map remove_last_part first_parts >> List.flatten
  

(** @return L'ensemble des processus découlant de l'action décrit par la modalité *)
let rec modal_sub_processes modality process =
  match (modality, process) with      
    | _, Silent -> []

    | (Possibly (Weak, _) | Necessity (Weak, _)), _ ->
      handle_weak_modalities modality process 
    
    (* 'a! , <!> | [!] *)
    | (Possibly (Strong, Any_out) | Necessity (Strong, Any_out)),
      Prefix (Out _, proc)
    (* 'a? , <?> | [?] *)
    | (Possibly (Strong, Any_in) | Necessity (Strong, Any_in)),
      Prefix (In _, proc)
    (* * , <.> | [.] *)
    | (Possibly (Strong, Any) | Necessity (Strong, Any)),
      Prefix (_, proc)
      -> [proc]

    (* Compositions (+, ||) *)
    | _, Par (p1, p2) ->
      List.map (fun sub_p -> Par (sub_p, p2)) (modal_sub_processes modality p1)
      @ List.map (fun sub_p -> Par (p1, sub_p)) (modal_sub_processes modality p2)
    | _, Sum (p1, p2) ->
      modal_sub_processes modality p1 @ modal_sub_processes modality p2

    (* Named actions *)
    | (Possibly (Strong, Coll acts) | Necessity (Strong, Coll acts)), Prefix (pre, proc)
      when is_action_in_list pre acts -> [proc]

    | _, Res (name, proc) -> failwith "Res : not handled yet"
    | _, Call (name, vl) -> failwith "Call : not handled yet"
    | _, Rename (n1, n2, proc) -> failwith "Rename : not handled yet"

    | _ -> []
  
module Env = Map.Make(String)

let nu_env : process list ref = ref []

let rec check_modality modality formula process =
(*  print_endline "check_modality :";
  Printf.printf "m : %s, form : %s, proc : %s\n%!" (string_of_modality modality) (string_of_formula formula) (string_of_process process) ;*)
  let sub_processes = modal_sub_processes modality process in
(*   List.iter (fun p -> Printf.printf "sub_processes : %s\n" (string_of_process p)) sub_processes;*)
  if (is_possibly modality)
  then List.exists (check_formula formula) sub_processes
  else List.for_all (check_formula formula) sub_processes

and check_formula_local env formula process =
  match formula with
    | FTrue -> true
    | FFalse -> false
    | FAnd (f1, f2) -> check_formula_local env f1 process && check_formula_local env f2 process
    | FOr (f1, f2) -> check_formula_local env f1 process || check_formula_local env f2 process
    | FNot f -> not (check_formula_local env f process)
    | FImplies (f1, f2) -> not (check_formula_local env f1 process) || check_formula_local env f2 process
    | FModal (m, f) -> check_modality m f process
    | FInvModal (m, f) -> not (check_modality m f process)
    | FProp _ -> failwith "not implemented yet"
    | FVar id -> 
	check_formula_local env (Env.find id env) process
    
    | FMu (id, mu_env, f) -> 
      let equiv = FNot (FNu (id, mu_env, FNot (subst_fix id f (FNot (FVar id))))) in
      check_formula_local env equiv process

    | FNu (id, nu_env, f) -> 
      FixEnv.mem process nu_env 
      || let new_env = FixEnv.add process nu_env in
	 let b' = subst_fix id f (FNu(id, new_env, f)) in
	 check_formula_local env b' process

and check_formula form proc = 
  check_formula_local Env.empty form proc
