open Formula
open Semop


type error = Unbound_Proposition of string
exception Error of error

let print_error = function
  | Unbound_Proposition s -> Printf.printf "unbound proposition %s" s

(*

Dans checklocal :
   - on normalise le proc
   - une fois dans Fmodal : on appelle next_process_set et on
   appelle check sur l'ensemble résultat
*)

let transitions_of def_map nproc = Semop.derivatives def_map nproc

(* Semop.PSet : set de processus *)


let check_label_prefixes lbl pref =
  let open Presyntax in
  match pref, lbl with
  | PTau, T_Tau -> true
  | (PIn (PName s1), (T_In s2)) when s1 = s2 -> true
  | (POut (PName s1), (T_Out s2)) when s1 = s2 -> true
  | _ -> false


let rec next_process_set def_map modality transitions =
  let choose transition destination_set =
    let _, mod_to_check, destination = transition in
    match modality, mod_to_check with
    | ((Strong | Weak), _, Rany), _
    | ((Strong | Weak), _, Rout), (T_Out _)
    | ((Strong | Weak), _, Rin), (T_In _) ->
      PSet.add destination destination_set
    | (Weak, _, _), T_Tau ->
      PSet.union destination_set @@
        next_process_set def_map modality (transitions_of def_map destination)
    | (_, _, Rpref acts), label ->
      if List.exists (check_label_prefixes label) acts then
        PSet.add destination destination_set
      else destination_set
    | _ -> destination_set
  in TSet.fold choose transitions PSet.empty


let beta_reduce in_formula expected_var replacement =
  let rec beta_reduce = function
  | FTrue | FFalse -> in_formula
  | FAnd (f1, f2) -> FAnd(beta_reduce f1, beta_reduce f2)
  | FOr (f1, f2) -> FOr(beta_reduce f1, beta_reduce f2)
  | FImplies (f1, f2) -> FImplies(beta_reduce f1, beta_reduce f2)
  | FModal (modality, formula) -> FModal(modality, beta_reduce formula)
(* transitions : <a> [a] *)
  | FInvModal (modality, formula) -> FInvModal(modality, beta_reduce formula)
  | FProp (prop_name, params) -> in_formula
  | FVar var when var = expected_var -> replacement
  | FMu (x, formula) -> FMu(x, beta_reduce formula)
  | FNu (x, formula) -> FNu(x, beta_reduce formula)
  in
  beta_reduce in_formula


let rec check def_map prop_map formula nproc =
  Printf.printf "Checking %s |- %s\n" (Normalize.string_of_nprocess nproc)
    (string_of_formula formula);
  let rec check_internal = function
    | FTrue -> true
    | FFalse -> false
    | FAnd (f1, f2) -> check_internal f1 && check_internal f2
    | FOr (f1, f2) -> check_internal f1 || check_internal f2
    | FImplies (f1, f2) -> check_internal f1 |> not || check_internal f2
    | FModal (modality, formula) ->
        check_modality def_map prop_map modality formula nproc
    | FInvModal (modality, formula) ->
        not @@ check_modality def_map prop_map modality formula nproc
        (* TODO : à vérifier la correctness *)
    (* transitions : not <a> ou not [a] *)
    | FProp (prop_name, params) ->
        check_prop_call def_map prop_map prop_name params nproc
    | FVar var ->
        check_prop_call def_map prop_map var [] nproc
    | FMu (x, formula) ->
      let reduced_formula = beta_reduce formula x @@ (FMu (x, formula)) in
      check_internal reduced_formula

  (* | FNu (x, f) -> assert false (\* TODO *\) *)
    | _-> assert false
  in
  check_internal formula


    (* AND rec *)

and check_modality def_map prop_map modality formula process =
  let ts = transitions_of def_map process  in
  let quantif = match modality with
    | _, Necessity, _ -> PSet.for_all
    | _, Possibly, _  -> PSet.exists
  in
  quantif (check def_map prop_map formula)
    (next_process_set def_map modality ts)


and check_prop_call def_map prop_map prop_name params process =
  let (Proposition (nom, expected_params, formula)) =
    try
      Hashtbl.find prop_map prop_name
    with Not_found -> raise @@ Error(Unbound_Proposition prop_name)
  in
  let params_length1 = List.length params in
  let params_length2 = List.length expected_params in
  if params_length1 <> params_length2 then
    failwith "unmatched length"
  else
    let params_map = List.combine expected_params params in
    let reduce_param formula (expected_param, param) =
        beta_reduce formula expected_param param
    in
    let reduced_formula = List.fold_left reduce_param formula params_map in
    check def_map prop_map reduced_formula process
