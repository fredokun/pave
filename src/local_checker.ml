(** Local checker *)
open Formula
open Presyntax
open Utils

open Semop

(** {3 utility functions } *)

let equals_label_preprefix pre prepre =
  match prepre, pre with
  | PTau, T_Tau -> true
  | PIn e, T_In n
  | POut e, T_Out n -> string_of_preexpr e = n
  | PTau, _
  | PIn _, _
  | POut _, _ -> false
  | PReceive _, _ 
  | PSend _, _ -> failwith "PReceive - PSend : Not implemented yet"

let is_action_in_list pre l =
  List.exists (equals_label_preprefix pre) l

(** [subst id B B'] substitue les occurences de la variable [id]
    (e.g, les X d'un nu) dans la formule [B] par [B'] *)
let rec subst id f f' =
  match f with
    | FVar s when s = id -> f'

    | FTrue
    | FFalse
    | FProp _
    | FVar _ -> f

    | FAnd (f1, f2) -> FAnd (subst id f1 f', subst id f2 f')
    | FOr (f1, f2) -> FOr (subst id f1 f', subst id f2 f')
    | FNot f -> FNot (subst id f f')
    | FImplies (f1, f2) -> FImplies (subst id f1 f', subst id f2 f')
    | FModal (m, f) -> FModal (m, subst id f f')
    | FInvModal (m, f) -> FInvModal (m, subst id f f')
    | FMu (s, env, f) -> FMu(s, env, subst id f f')
    | FNu (s, env, f) -> FNu(s, env, subst id f f')
    
(** @return L'ensemble des processus découlant de l'action décrit par la modalité *)
let modal_sub_processes modality proc_set =
  let select transition old_proc_set =
    let _, label, res_proc = transition in
    match modality, label with
      | (Possibly (_, Any_out) | Necessity (_, Any_out)), (T_Out _)
      | (Possibly (_, Any_in) | Necessity (_, Any_in)), (T_In _)
      | (Possibly (_, Any) | Necessity (_, Any)), _
	-> PSet.add res_proc old_proc_set

      | (Possibly (_, Coll acts) | Necessity (_, Coll acts)), label
	when is_action_in_list label acts
        -> PSet.add res_proc old_proc_set

      | _ -> old_proc_set
  in 
  TSet.fold select proc_set PSet.empty

(** Substitue les propositions par leurs corps *)
let reduce_proposition prop_env id fargs =
  let (args, formula) = 
    try Hashtbl.find prop_env id
    with
      | Not_found -> raise (Failure ("Unbound proposition : "^id))
  in
  try
    List.fold_left2 (fun f a f_a -> subst a f f_a)
      formula args fargs 
  with 
    | Invalid_argument _ -> raise (Failure ("Wrong arity in the proposition : "^id))

(** False_property of reason * proc *)
exception False_property of string

type debug_stack = {expected_result:bool; process_stack:Normalize.nprocess list}

let reverse_expected_result stack = {stack with expected_result=not stack.expected_result}
let push_process p stack = {stack with process_stack=p::stack.process_stack}
let new_debug_stack = {expected_result=true; process_stack=[]}

let check_necessity debug_stack f_checker sub_processes =
  let res = PSet.exists f_checker sub_processes in
  if res = debug_stack.expected_result then
    res
  else
    let (sats, unsats) = PSet.partition f_checker sub_processes in
    assert false

(** Calcul l'ensemble des transitions possibles pour le processus puis
    filtre celles satisfaisant la modalité pour finalement vérifier,
    selon la modalité, la satisfaction de la formule *)
let rec check_modality debug_stack def_env prop_env modality formula process =
  let f_checker = check_formula debug_stack def_env prop_env formula in
  let derivs =
    if is_weak_modality modality then
      Semop.weak_transitions false def_env process
    else 
      Semop.derivatives def_env process 
  in
  let sub_processes = modal_sub_processes modality derivs in
  let op = match modality with 
    | Possibly _ -> PSet.exists 
    | Necessity _ -> PSet.for_all 
  in
  op f_checker sub_processes     

(** Vérifie la satisfaction d'une formule pour un processus *)
and check_formula debug_stack def_env prop_env formula process = 
  let rec loop debug_stack = function
    | FTrue -> true
    | FFalse -> false
    | FAnd (f1, f2) -> loop debug_stack f1 && loop debug_stack f2
    | FOr (f1, f2) -> loop debug_stack f1 || loop debug_stack f2
    | FNot f -> not (loop (reverse_expected_result debug_stack) f)
    | FImplies (f1, f2) ->
      not (loop (reverse_expected_result debug_stack) f1)
      || loop debug_stack f2
    | FModal (m, f) -> check_modality debug_stack def_env prop_env m f process
    | FInvModal (m, f) -> not (check_modality (reverse_expected_result debug_stack) def_env prop_env m f process)
    | FProp (id, args) -> 
      loop debug_stack (reduce_proposition prop_env id args)
    | FVar id -> 
      loop debug_stack (reduce_proposition prop_env id [])
    | FMu (id, mu_env, f) -> 
      let equiv = FNot (FNu (id, mu_env, FNot (subst id f (FNot (FVar id))))) in
      loop debug_stack equiv
    | FNu (id, nu_env, f) -> 
      PSet.mem process nu_env
      || let new_env = PSet.add process nu_env in
	 let b' = subst id f (FNu(id, new_env, f)) in
	 loop debug_stack b'
  in loop (push_process process debug_stack) formula

(** [check_local def_env prop_env formula process] vérifie que
    [formula] |- [process] pour un environnement de définitions de process
    [def_env] et un environnement de formule [prop_env] *)
and check_local def_env prop_env formula process =
  Normalize.normalize process >> check_formula new_debug_stack def_env prop_env formula
