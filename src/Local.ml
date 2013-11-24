(** Local Model Checking Module *)

open Formula
open Semop

type error =
| Unbound_Proposition of string
| Unmatching_length of string

exception Error of error

(* Trace, tuple of labels visited and 
   process remaining to execute *)
type trace = (formula * Normalize.nprocess) list  

let print_error = function
  | Unbound_Proposition s -> Printf.printf "unbound proposition %s\n" s
  | Unmatching_length s ->
    Printf.printf "unmatching length on proposition %s\n" s

let transitions_of def_map nproc = Semop.derivatives def_map nproc
let weak_transitions_of def_map nproc = Semop.weak_derivatives true def_map nproc


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
        (PrefixMap.fold (fun k d a -> PSet.union d a)
           (weak_transitions_of def_map destination)
           destination_set)
    | (_, _, Rpref acts), label ->
      if List.exists (check_label_prefixes label) acts then
        PSet.add destination destination_set
      else destination_set
    | _ -> destination_set
  in TSet.fold choose transitions PSet.empty


let beta_reduce in_formula expected_var replacement =
  let rec beta_reduce in_formula =
  match in_formula with
  | FTrue | FFalse -> in_formula
  | FAnd (f1, f2) -> FAnd(beta_reduce f1, beta_reduce f2)
  | FOr (f1, f2) -> FOr(beta_reduce f1, beta_reduce f2)
  | FImplies (f1, f2) -> FImplies(beta_reduce f1, beta_reduce f2)
  | FModal (modality, formula) -> FModal(modality, beta_reduce formula)
  | FInvModal (modality, formula) -> FInvModal(modality, beta_reduce formula)
  | FProp _ -> in_formula
  | FVar var when var = expected_var -> replacement
  | FVar _ -> in_formula
  | FMu (x, env, formula) -> FMu(x, env, beta_reduce formula)
  | FNu (x, env, formula) -> FNu(x, env, beta_reduce formula)
  | FNot formula -> FNot (beta_reduce formula)
  in
  beta_reduce in_formula

let rec check def_map prop_map trace formula nproc  =
  let rec check_internal trace = function
    | FTrue -> (true, trace)
    | FNot formula ->
      let okay1, trace1 = check_internal ((formula, nproc)::trace) formula in
      (not okay1, trace1)
    | FFalse -> (false, trace)
    | FAnd (f1, f2) -> 
      let okay1, trace1 = check_internal ((f1, nproc)::trace) f1 in
      if not okay1 then okay1, trace1 else
      let okay2, trace2 = check_internal  ((f2, nproc)::trace1) f2 in
      (okay1 && okay2, trace2)
    | FOr (f1, f2) -> 
      let okay1, trace1 = check_internal ((f1, nproc)::trace) f1 in
      if okay1 then okay1, trace else
      let okay2, trace2 = check_internal ((f2, nproc)::trace1) f2 in
      (okay1 || okay2, trace2)
    | FImplies (f1, f2) -> 
      let okay1, trace1 = check_internal ((f1, nproc)::trace) f1 in
      if not okay1 then not okay1, trace1 else
      let okay2, trace2 = check_internal ((f2, nproc)::trace1) f2 in
      (not okay1 || okay2, trace2) 
    | FModal (modality, formula) ->
        check_modality def_map prop_map trace modality formula nproc
    | FInvModal (modality, formula) ->
        let okay1, trace1 = 
          check_modality def_map prop_map trace modality formula nproc
        in
        (not okay1, trace1)
        (* TODO : à vérifier la correctness *)
    (* transitions : not <a> ou not [a] *)
    | FProp (prop_name, params) ->
        check_prop_call def_map prop_map prop_name trace formula params nproc
    | FVar var ->
        check_prop_call def_map prop_map var trace formula [] nproc
    | FMu (x, env, mu_formula) ->
      let formula' =
        FNot (FNu (x, env, FNot (beta_reduce mu_formula x (FNot (FVar x)))))
      in check_internal ((formula', nproc)::trace) formula'
    | FNu (_, env, _) when List.mem nproc env -> (true, trace)
    | FNu (x, env, formula) ->
        let reduced_formula =
          beta_reduce formula x @@ FNu(x, nproc::env, formula)
        in
        check_internal ((reduced_formula, nproc)::trace) reduced_formula
  in
  check_internal trace formula


and check_modality def_map prop_map trace modality formula process =
  let ts = transitions_of def_map process  in
  let operator, acc_init = match modality with
    | _, Necessity, _ -> (&&), true
    | _, Possibly, _  -> (||), false
  in
  let folding element (acc_okay, acc_trace) =
    let okay1, trace1 = 
      check def_map prop_map ((formula, element)::acc_trace) formula element
    in
      Printf.printf "here : %s\n" @@ string_of_bool okay1;
      Printf.printf "here : %s\n" @@ string_of_bool acc_okay;
      Printf.printf "here : %s\n\n" @@ string_of_bool (operator okay1 acc_okay);
      (operator okay1 acc_okay, trace1)
  in
  PSet.fold folding (next_process_set def_map modality ts) (acc_init, trace)


and check_prop_call def_map prop_map prop_name trace formula params process =
  let (Proposition (_, param_names, formula)) =
    try
      Hashtbl.find prop_map prop_name
    with Not_found -> raise @@ Error(Unbound_Proposition prop_name)
  in
  let params_length1 = List.length params in
  let params_length2 = List.length param_names in
  if params_length1 <> params_length2 then
    raise @@ Error (Unmatching_length prop_name)
  else
    let params_map = List.combine param_names params in
    let reduce_param formula (param_name, param_content) =
        beta_reduce formula param_name param_content
    in
    let reduced_formula = List.fold_left reduce_param formula params_map in
    check def_map prop_map ((reduced_formula, process)::trace) 
          reduced_formula process
