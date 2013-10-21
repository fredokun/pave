(*** Representation of mu-calculus formulae ***)

open Printf

open Presyntax
open Utils
open Global
open Normalize
open Semop
open Bdd

type fprefix =
| FIn of string
| FInVar of string
| FOut of string
| FOutVar of string
| FTau

let fprefix_of_preprefix = function
  | PIn (PName n) -> FIn n
  | POut (PName n) -> FOut n
  | PIn (PVar n) -> FInVar n
  | POut (PVar n) -> FOutVar n
  | PTau -> FTau
  | _ as pr -> failwith (Format.sprintf "Received : %s@." @@ string_of_preprefix pr)

let string_of_fprefix = function
  | FIn n | FInVar n -> n ^ "?"
  | FOut n | FOutVar n -> n ^ "!"
  | FTau -> "tau"

let parse_preprefix_list =
  List.map fprefix_of_preprefix

type strongness = Strong | Weak
type modal = Possibly | Necessity
type io =
  In | Out | Any | Prefix of fprefix list

type modality = strongness * modal * io

let string_of_modality (s, m, io) =
  let io = match io with
    | In -> "!"
    | Out -> "?"
    | Any -> "."
    | Prefix pl -> List.fold_left
      (fun acc p -> acc ^ "," ^ (string_of_fprefix p))
      (string_of_fprefix (List.hd pl))
      (List.tl pl)
  in
  match s, m with
    | Strong, Possibly -> Format.sprintf "<%s>" io
    | Strong, Necessity -> Format.sprintf "[%s]" io
    | Weak, Possibly -> Format.sprintf "<<%s>>" io
    | Weak, Necessity -> Format.sprintf "[[%s]]" io

let diamond = function
  | _, Possibly, _ -> true
  | _, _, _ -> false

type formula =
  | FTrue
  | FFalse
  | FPar of formula
  | FAnd of formula * formula
  | FOr of formula * formula
  | FImplies of formula * formula
  | FModal of modality * formula
  | FInvModal of modality * formula
  | FProp of string * (string list)
  | FVar of string
  | FMu of string * formula
  | FNu of string * formula
  | FNot of formula (* considered only internaly *)

let rec string_of_formula : formula -> string = function
  | FTrue -> "True"
  | FFalse -> "False"
  | FPar f -> sprintf "(%s)" @@ string_of_formula f
  | FAnd(f,g) -> sprintf "(%s and %s)" (string_of_formula f) (string_of_formula g)
  | FOr(f,g) -> sprintf "(%s or %s)" (string_of_formula f) (string_of_formula g)
  | FImplies(f,g) -> sprintf "(%s ==> %s)" (string_of_formula f) (string_of_formula g)
  | FModal(m,f) -> (string_of_modality m) ^ (string_of_formula f)
  | FInvModal(m,f) ->  "~" ^ (string_of_modality m) ^ (string_of_formula f)
  | FProp(prop,params) -> prop ^ (string_of_collection "(" ")" "," (fun s -> s) params)
  | FVar(var) -> var
  | FMu(x,f) -> sprintf "Mu(%s).%s" x (string_of_formula f)
  | FNu(x,f) -> sprintf "Nu(%s).%s" x (string_of_formula f)
  | FNot f -> sprintf "~%s" @@ string_of_formula f

type prop = string list * formula

let props : (string, prop) Hashtbl.t = Hashtbl.create 53

exception Formdef_exception of string
exception Unbound_variable of string
exception Unbound_prop of string

let rec verify_vars f idents =
  match f with
  | FVar v -> if not (List.mem v idents) then raise (Unbound_variable v)
  | FAnd (f,g) | FOr (f,g) | FImplies (f,g) ->
    verify_vars f idents; verify_vars g idents
  | FModal (_, f) | FInvModal (_, f) -> verify_vars f idents
  | FMu (x,f) | FNu (x,f) -> verify_vars f (x :: idents)
  | FProp (_, l) -> List.iter (fun v -> verify_vars (FVar v) idents) l
  | _ -> ()

(** val add_prop : string -> string list -> formula -> unit *)
let add_prop name idents formula =
  if Hashtbl.mem props name then
    raise (Formdef_exception name)
  else
    begin
      verify_vars formula idents;
      Hashtbl.add props name (idents, formula)
    end


let reduce f var value =
  let rec step = function
  | FVar v -> if v = var then value else FVar v
  | FTrue | FFalse as f -> f
  | FPar f -> FPar (step f)
  | FAnd (f, g) -> FAnd (step f, step g)
  | FOr (f, g) -> FOr (step f, step g)
  | FImplies (f, g) -> FImplies (step f, step g)
  | FModal(m, f) -> FModal (m, step f)
  | FInvModal (m, f) -> FInvModal (m, step f)
  | FMu (x, f) -> FMu (x, step f)
  | FNu (x, f) -> FNu (x, step f)
  | _ -> assert false (* Technically, no Prop should remain ? *)
  in
  step f

let substitute f sub_list =
  let rec step sl = function
  | FVar v -> FVar (List.assoc v sl)
  | FTrue | FFalse as f -> f
  | FPar f -> FPar (step sl f)
  | FAnd (f, g) -> FAnd (step sl f, step sl g)
  | FOr (f, g) -> FOr (step sl f, step sl g)
  | FImplies (f, g) -> FImplies (step sl f, step sl g)
  | FModal(m, f) -> FModal (m, step sl f)
  | FInvModal (m, f) -> FInvModal (m, step sl f)
  | FMu (x, f) -> FMu (x, step ((x, x)::sl) f)
  | FNu (x, f) -> FNu (x, step ((x, x)::sl) f)
  | _ -> assert false (* Technically, no Prop should remain ? *)
  in
  step sub_list f

let substitute_prop pf =
  let rec step = function
    | FTrue | FFalse as f -> f
    | FPar f -> FPar (step f)
    | FAnd (f, g) -> FAnd (step f, step g)
    | FOr (f, g) -> FOr (step f, step g)
    | FImplies (f, g) -> FImplies (step f, step g)
    | FModal(m, f) -> FModal (m, step f)
    | FInvModal (m, f) -> FInvModal (m, step f)
    | FVar v -> FVar v
    | FMu (x, f) -> FMu (x, step f)
    | FNu (x, f) -> FNu (x, step f)
    | FNot f -> FNot (step f)
    | FProp (s, il) ->
      if Hashtbl.mem props s then
        let (vars, formula) = Hashtbl.find props s in
        substitute formula @@ List.combine vars il
      else
        raise (Unbound_prop s)
  in
  Format.printf "Preformula received :\n%s@." @@ string_of_formula pf;
  let res = step pf in
  Format.printf "Result :\n%s@." @@ string_of_formula res;
  res


let formula_of_preformula = substitute_prop
  (* let rename_modality = assert false (\* function *\) *)
  (*   (\* | FPossibility pl -> *\) *)
  (* in *)
  (* let sub = function *)
  (*   | FModal (m, f) -> *)

  (*     let rename m = *)
  (*       match fprefix_of_preprefix m with *)
  (*       | FInVar n -> PIn (PName (n ^ "_" ^ value)) *)
  (*       | FOutVar n -> POut (PName (n ^ "_" ^ value)) *)
  (*       | _ -> m *)
  (*     in *)
  (*     FModal (m, sub value f) *)
  (*   | FInvModal (m, f) -> *)
  (*     let m = *)
  (*       match fprefix_of_preprefix m with *)
  (*       | FInVar n -> PIn (PName (n ^ "_" ^ value)) *)
  (*       | FOutVar n -> POut (PName (n ^ "_" ^ value)) *)
  (*       | _ -> m *)
  (*     in *)
  (*     FInvModal (m, sub value f) *)
  (*   | FTrue | FFalse as f -> f *)
  (*   | FAnd (f, g) -> FAnd (sub value f, sub value g) *)
  (*   | FOr (f, g) -> FOr (sub value f, sub value g) *)
  (*   | FImplies (f, g) -> FImplies (sub value f, sub value g) *)
  (*   | FModal(m, f) -> FModal (m, sub value f) *)
  (*   | FInvModal (m, f) -> FInvModal (m, sub value f) *)
  (*   | FVar v -> FVar v *)
  (*   | FMu (x, f) -> FMu (x, sub value f) *)
  (*   | FNu (x, f) -> FNu (x, sub value f) *)
  (* in *)
  (* let rec step = function *)
  (*   | FTrue | FFalse as f -> f *)
  (*   | FAnd (f, g) -> FAnd (step f, step g) *)
  (*   | FOr (f, g) -> FOr (step f, step g) *)
  (*   | FImplies (f, g) -> FImplies (step f, step g) *)
  (*   | FModal(m, f) -> *)
  (*     let v = *)
  (*       if SMap.mem const_name !env_const then *)
  (*         SMap.find var *)
  (*       else *)
  (*         raise (Constdef_Exception const_name) *)

  (*     FModal (m, step f) *)
  (*   | FInvModal (m, f) -> FInvModal (m, step f) *)
  (*   | FVar v -> FVar v *)
  (*   | FMu (x, f) -> FMu (x, step f) *)
  (*   | FNu (x, f) -> FNu (x, step f) *)
  (*   | FProp (s, il) -> *)
  (*     if Hashtbl.mem props s then *)
  (*       let (vars, formula) = Hashtbl.find props s in *)
  (*       substitute formula @@ List.combine vars il *)
  (*     else *)
  (*       raise (Unbound_prop s) *)
  (* in *)
  (* Format.printf "Preformula received :\n%s@." @@ string_of_formula pf; *)
  (* let res = step pf in *)
  (* Format.printf "Result :\n%s@." @@ string_of_formula res; *)
  (* res *)

(** Local model checker *)

(** takes a normalized processor *)
let compute_derivation =
  Semop.derivatives global_definition_map

exception Impossible_transition

let compute_modality modl tr =

  let get_matching_derivations_named act tr acc =
    TSet.fold
      (fun t acc ->
        let _, pre, _ = t in
        match act, pre with
        | FIn s, T_In n | FOut s, T_Out n ->
          if s = n then TSet.add t acc else acc
        | _, T_Tau -> TSet.add t acc
        | _, _ -> acc)
      tr
      acc
  in

  let get_matching_derivations io tr =
    TSet.fold
      (fun t acc ->
        let _, pre, _ = t in
        match io, pre with
        | In, T_In _ | Out, T_Out _ | Any, T_Tau | _, T_Tau -> TSet.add t acc
        | _, _ -> acc)
      tr
      TSet.empty
  in

  match modl with
  | Strong, _, Prefix acts ->
    List.fold_left
      (fun acc a ->
        get_matching_derivations_named a tr acc)
      TSet.empty
      acts
  | Strong, _, (_ as io) ->
    Format.printf "%s@." @@ string_of_modality modl;
    get_matching_derivations io tr
  | Weak, _, _ -> failwith "Weak not implemented yet"


let handle_check_local form proc =
  let proc = normalize proc in
  let pset = PSet.empty in

  let rec step proc pset = function
    | FTrue -> true
    | FFalse -> false
    | FPar f -> step proc pset f
    | FNot f -> not @@ step proc pset f
    | FAnd (f, g) -> step proc pset f && step proc pset g
    | FOr (f, g) -> step proc pset f || step proc pset g
    | FImplies (f, g) -> not (step proc pset f) || step proc pset g
    | FModal (m, f) ->
      let d = compute_derivation proc in
      let res = compute_modality m d in
      if TSet.is_empty res then not @@ diamond m
      else if diamond m then
        TSet.fold
          (fun (_, _, p') acc ->
            if acc then acc (* no need to test the transition if one is
                               true *)
            else step p' pset f)
          res
          false
      else
        TSet.fold
          (fun (_, _, p') acc ->
            if not acc then acc (* no need to test the transition if one is
                                   false *)
            else step p' pset f)
          res
          true
    | FInvModal(m, f) ->
      not @@ step proc pset @@ FModal (m,f)
    | FNu (x, f) as nu -> if PSet.mem proc pset then true
      else
        let f = reduce f x nu in
        let pset = PSet.add proc pset in
        step proc pset f

    | FMu (x, f) ->
      let nu = FNu(x, f) in
      let f' = reduce f x @@ FNot nu in
      let f = FNot f' in
      not @@ step proc pset f

    | _ -> assert false
  in
  let res = step proc pset form in
  if res then
    Format.printf "The processor given matches the model@."
  else
    Format.printf "Doesn't match, here is why : <not implemented yet>@."


let bdd_of_formula f =
  (* let fix f l = assert false in *)
  let implies b1 b2 = (not b1) || b2 in
  let xor b1 b2  = ((not b1) && b2) || (b1 && (not b2)) in
  let _env = [] in
  let rec step f env =
    match f with
    | FTrue -> one
    | FFalse -> zero
    | FNot f -> apply xor (step f env) one
    | FAnd (f1, f2) ->
      let b1 = step f1 env in
      let b2 = step f2 env in
      apply ( && ) b1 b2
    | FOr (f1, f2) ->
      let b1 = step f1 env in
      let b2 = step f2 env in
      apply ( || ) b1 b2
    | FImplies (f1, f2) ->
      let b1 = step f1 env in
      let b2 = step f2 env in
      apply implies b1 b2
    | FModal (_m, _f) -> assert false
    | _ -> assert false
  in
  step f
