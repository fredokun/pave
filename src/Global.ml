(** Global Model Checking Module *)


type error =
| No_global_not

exception Error of error

let print_error = function
  | No_global_not -> Printf.printf "Cannot global check formula with negation"




(*
  L p = sous ensemble de Top tq p est vraie
  T action = relation binaire sur t en fonction de a
*)

let rec simple_eval process defs formula env =
  let lts = Semop.lts defs Semop.derivatives process in
  let rec eval formula env =
    let open Formula in
    match formula with
    | FNot _ -> raise @@ Error (No_global_not)
    | FTrue -> lts
    | FFalse -> []
    | FAnd (f1, f2) -> eval f1 env @ eval f2 env
    | FOr  (f1, f2) -> eval f1 env @ eval f2 env
    | _ -> assert false
  in eval formula env

let rec obdd_of_modality env modality =
    match modality with
    (* | Strong, Possibly, Rany _ *)
    (* | Strong, Possibly, Rout *)
    (* | Strong, Possibly, Rin -> *)
    (* | (Weak, _, _), T_Tau -> *)
    (* | (_, _, Rpref acts), label -> *)
    | _ -> assert false



let rec obdd_of_formula env formula =
  let open Formula in
  let open Obdd in
  match formula with
  | FTrue -> One
  | FFalse -> Zero
  | FNot _ -> raise @@ Error (No_global_not)
  | FAnd (f1, f2) -> inter (obdd_of_formula env f1)
    (obdd_of_formula env f2)
  | FOr  (f1, f2) -> union (obdd_of_formula env f1)
    (obdd_of_formula env f2)
  (* | FImplies of formula * formula *)
  | FModal (modality, f) ->
    inter (obdd_of_formula env f) (obdd_of_modality env f)
  (* | FInvModal of modality * formula *)
  (* | FProp of string * formula list *)
  (* | FVar v -> assert false *)
  (* | FMu of string * nprocess list * formula *)
  (* | FNu of string * nprocess list * formula *)
  | _ -> assert false

let check _formula _proc = assert false (* TODO *)
