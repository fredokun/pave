open Formula
open Semop

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


(* recupère l'ensemble des processus suivants de nproc *)
let next_process_set modality transitions =
  let choose transition destination_set =
    let _, mod_to_check, destination = transition in
    let is_next =
      match modality, mod_to_check with
      | ((Strong | Weak), _, Rany), _ -> true
      | ((Strong | Weak), _, Rout), (T_Out _) -> true
      | ((Strong | Weak), _, Rin), (T_In _) -> true

      | (_, _, Rpref acts), label -> 
        List.exists (check_label_prefixes label) acts

      | _ -> false
    in
    if is_next then PSet.add destination destination_set else destination_set
  in
    TSet.fold choose transitions PSet.empty


(*
mod_to_check :

W: weak
Possibly : <>
Necessity : []

type preprefix =
  | PTau
  | PIn of preexpr
  | POut of preexpr
  | PReceive of preexpr * string * string
  | PSend of preexpr * preexpr

type label = T_Tau | T_In of name | T_Out of name

=============

type restr = Rin | Rout | Rany | Rpref of preprefix list
type existence = Possibly | Necessity
type strength = Weak | Strong
type modality = strength * existence * restr

*)

let rec check def_map prop_map formula nproc =
  let rec check_internal formula =
    match formula with
    | FTrue -> true
    | FFalse -> false
    | FAnd (f1, f2) -> check_internal f1 && check_internal f2
    | FOr (f1, f2) -> check_internal f1 || check_internal f2
    | FImplies (f1, f2) -> check_internal f1 |> not || check_internal f2
    | FModal (modality, formula) -> 
        check_modality def_map prop_map modality formula nproc
  (* transitions : <a> [a] *)
    | FInvModal (modality, formula) -> 
        not @@ check_modality def_map prop_map modality formula nproc
        (* TODO : à vérifier la correctness *)
    (* transitions : not <a> ou not [a] *)
    | _-> assert false
    | FProp (prop, params) -> 
      let (Proposition (nom, expected_params, formula)) =
        try 
          Hashtbl.find prop_map prop
        with Not_found -> assert false (* TODO *)
      in
      let params_length1 = List.length params in
      let params_length2 = List.length expected_params in
      if params_length1 <> params_length2 then
        assert false (* TODO *)
      else
        assert false
        (* beta_reduce all params *)
  (* | FVar var -> *)
  (*   (\* begin try let name, params, _ = fetch_prop prop in *\) *)
  (*   assert false (\* TODO *\) *)
  (* (\* with Not_found -> raise @@ Error (Unbound_Proposition prop) *\) *)
  (* (\* end *\) *)
  (* | FMu (x, f) -> assert false (\* TODO *\) *)
  (* | FNu (x, f) -> assert false (\* TODO *\) *)
  in
  check_internal formula

and check_modality def_map prop_map modality formula process = 
  let ts = transitions_of def_map process  in
  let quantif = match modality with
    | _, Necessity, _ -> PSet.for_all 
    | _, Possibly, _  -> PSet.exists 
  in
  quantif (check def_map prop_map formula) (next_process_set modality ts)

