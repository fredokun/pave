(*** Representation of mu-calculus formulae ***)

open Printf
open Semop
open Presyntax
open Utils

(** Type of "named" prefix *)
type fprefix =
| FIn of string
| FInVar of string
| FOut of string
| FOutVar of string
| FTau

(** Takes a preprefix and gives its corresponding fprefix to be used correctly in
   the formula *)
let fprefix_of_preprefix = function
  | PIn (PName n) -> FIn n
  | POut (PName n) -> FOut n
  | PIn (PVar n) -> FInVar n (* (String.sub n 1 (String.length n - 1)) *)
  | POut (PVar n) -> FOutVar n (* (String.sub n 1 (String.length n - 1)) *)
  | PTau -> FTau
  | _ as pr -> failwith (Format.sprintf "Received : %s@." @@ string_of_preprefix pr)

let string_of_fprefix = function
  | FIn n -> n ^ "?"
  | FInVar n -> "var:" ^ n ^ "?"
  | FOut n -> n ^ "!"
  | FOutVar n -> "var:" ^ n ^ "!"
  | FTau -> "tau"

(** Transform a preprefix list into a fprefix list *)
let parse_preprefix_list =
  List.map fprefix_of_preprefix

(** Types used to represent modalities *)
type strongness = Strong | Weak
type modal = Possibly | Necessity
type io =
  In | Out | Any | Prefix of fprefix list

type modality = strongness * modal * io

let string_of_io = function
  | In -> "?"
  | Out -> "!"
  | Any -> "."
  | Prefix pl -> List.fold_left
    (fun acc p -> acc ^ "," ^ (string_of_fprefix p))
    (string_of_fprefix (List.hd pl))
    (List.tl pl)


let string_of_modality (s, m, io) =
  let io = string_of_io io  in
  match s, m with
    | Strong, Possibly -> Format.sprintf "<%s>" io
    | Strong, Necessity -> Format.sprintf "[%s]" io
    | Weak, Possibly -> Format.sprintf "<<%s>>" io
    | Weak, Necessity -> Format.sprintf "[[%s]]" io

let diamond = function
  | _, Possibly, _ -> true
  | _, _, _ -> false

(** Type to represent preformula, particularely the ForAll and Exists terms *)
type preformula =
  | PFTrue
  | PFFalse
  | PFPar of preformula
  | PFAnd of preformula * preformula
  | PFOr of preformula * preformula
  | PFImplies of preformula * preformula
  | PFModal of modality * preformula
  | PFInvModal of modality * preformula
  | PFProp of string * (preformula list)
  | PFVar of string
  | PFMu of string * preformula
  | PFNu of string * preformula
  | PFForall of preparam * preexpr * preformula
  | PFExists of preparam * preexpr * preformula

let rec string_of_preformula : preformula -> string = function
  | PFTrue -> "True"
  | PFFalse -> "False"
  | PFPar f -> sprintf "(%s)" @@ string_of_preformula f
  | PFAnd(f,g) -> sprintf "(%s and %s)" (string_of_preformula f) (string_of_preformula g)
  | PFOr(f,g) -> sprintf "(%s or %s)" (string_of_preformula f) (string_of_preformula g)
  | PFImplies(f,g) -> sprintf "(%s ==> %s)" (string_of_preformula f) (string_of_preformula g)
  | PFModal(m,f) -> (string_of_modality m) ^ (string_of_preformula f)
  | PFInvModal(m,f) ->  "~" ^ (string_of_modality m) ^ (string_of_preformula f)
  | PFProp(prop,params) -> prop ^
    (string_of_collection "(" ")" ","
       (fun s ->
         string_of_preformula s)
       params)
  | PFVar(var) -> var
  | PFMu(x,f) -> sprintf "Mu(%s).%s" x (string_of_preformula f)
  | PFNu(x,f) -> sprintf "Nu(%s).%s" x (string_of_preformula f)
  | PFForall (par, pe, f) ->
    sprintf "(forall %s, %s in %s)"
      (string_of_preparam par) (string_of_preexpr pe) (string_of_preformula f)
  | PFExists (par, pe, f) ->
    sprintf "(exists %s, %s in %s)"
      (string_of_preparam par) (string_of_preexpr pe) (string_of_preformula f)

(** Similar to preformula, without the quantifying clauses *)
type formula =
  | FTrue
  | FFalse
  | FPar of formula
  | FAnd of formula * formula
  | FOr of formula * formula
  | FImplies of formula * formula
  | FModal of modality * formula
  | FInvModal of modality * formula
  | FProp of string * (formula list)
  | FVar of string
  | FMu of string * PSet.t * formula
  | FNu of string * PSet.t * formula
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
  | FProp(prop,params) ->
    prop ^ (string_of_collection "(" ")" ","
              (fun s ->
                string_of_formula s)
              params)
  | FVar(var) -> var
  | FMu(x, _, f) -> sprintf "Mu(%s).%s" x (string_of_formula f)
  | FNu(x, _, f) -> sprintf "Nu(%s).%s" x (string_of_formula f)
  | FNot f -> sprintf "~%s" @@ string_of_formula f

(** A prop is a list of bound variables and its formulas *)
type prop = string list * formula

let props : (string, prop) Hashtbl.t = Hashtbl.create 53

exception Formdef_exception of string
exception Unbound_variable of string
exception Unbound_prop of string

(** Will verify if every variable is bound in the prop *)
let rec verify_vars f idents =
  match f with
  | FVar v -> if not (List.mem v idents) then raise (Unbound_variable v)
  | FAnd (f,g) | FOr (f,g) | FImplies (f,g) ->
    verify_vars f idents; verify_vars g idents
  | FModal (_, f) | FInvModal (_, f) -> verify_vars f idents
  | FMu (x,_,f) | FNu (x,_,f) -> verify_vars f (x :: idents)
  (* | FProp (_, l) -> List.iter (fun v -> verify_vars (FVar v) idents) l *)
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

module IMap = Map.Make(
  struct
    type t = int
    let compare = compare
 end)

(** Converts a variable name to avoid multiple definitions. Never used however,
    since the fixed points variables are always in tail position *)
let alpha_convert f =
  let i = ref 0 in
  let rec step f env =
    match f with
    | FVar v ->
      if SMap.mem v env then FVar (SMap.find v env)
      else FVar v

    | FTrue | FFalse as f -> f
    | FPar f -> FPar (step f env)
    | FNot f -> FNot (step f env)
    | FAnd (f, g) -> FAnd (step f env, step g env)
    | FOr (f, g) -> FOr (step f env, step g env)
    | FImplies (f, g) -> FImplies (step f env, step g env)
    | FModal(m, f) -> FModal (m, step f env)
    | FInvModal (m, f) -> FInvModal (m, step f env)
    | FMu (x, s, f) ->
      let nx = x ^ "_" ^ (string_of_int !i) in
      let env = SMap.add x nx env in
      incr i;
      FMu (nx, s, step f env)
    | FNu (x, s, f) ->
      let nx = x ^ "_" ^ (string_of_int !i) in
      let env = SMap.add x nx env in
      incr i;
      FNu (x, s, step f env)
    | FProp (_,_) -> f
  in
  step f SMap.empty

(** Replaces a var in f by the formula given *)
let reduce f var value =
  let rec step = function
  | FVar v -> if v = var then value else FVar v
  | FTrue | FFalse as f -> f
  | FPar f -> FPar (step f)
  | FNot f -> FNot (step f)
  | FAnd (f, g) -> FAnd (step f, step g)
  | FOr (f, g) -> FOr (step f, step g)
  | FImplies (f, g) -> FImplies (step f, step g)
  | FModal(m, f) -> FModal (m, step f)
  | FInvModal (m, f) -> FInvModal (m, step f)
  | FMu (x, s, f) -> FMu (x, s, step f)
  | FNu (x, s, f) -> FNu (x, s, step f)
  | _ -> failwith (string_of_formula f)
  in
  step f

(** Replaces each Var by its correspondance. Works as a reduce for multiple
    vars. Assumes each variable is correctly bound *)
let substitute f sub_list =
  let rec step sl = function
  | FVar v -> List.assoc v sl
  | FTrue | FFalse as f -> f
  | FPar f -> FPar (step sl f)
  | FAnd (f, g) -> FAnd (step sl f, step sl g)
  | FOr (f, g) -> FOr (step sl f, step sl g)
  | FImplies (f, g) -> FImplies (step sl f, step sl g)
  | FModal(m, f) -> FModal (m, step sl f)
  | FInvModal (m, f) -> FInvModal (m, step sl f)
  | FMu (x, s, f) -> FMu (x, s, step ((x, FVar x)::sl) f)
  | FNu (x, s, f) -> FNu (x, s, step ((x, FVar x)::sl) f)
  | _ -> assert false (* Technically, no Prop should remain ? *)
  in
  step sub_list f

(** Inlines a prop call *)
let substitute_prop f =
  let rec step = function
    | FTrue | FFalse as f -> f
    | FPar f -> FPar (step f)
    | FAnd (f, g) -> FAnd (step f, step g)
    | FOr (f, g) -> FOr (step f, step g)
    | FImplies (f, g) -> FImplies (step f, step g)
    | FModal(m, f) -> FModal (m, step f)
    | FInvModal (m, f) -> FInvModal (m, step f)
    | FVar v -> FVar v
    | FMu (x, s, f) -> FMu (x, s, step f)
    | FNu (x, s, f) -> FNu (x, s, step f)
    | FNot f -> FNot (step f)
    | FProp (s, fl) ->
      if Hashtbl.mem props s then
        let (vars, formula) = Hashtbl.find props s in
        substitute formula @@ List.combine vars fl
      else
        raise (Unbound_prop s)
  in
  step f

(** Renames a modality *)
let substitute_modality m vars =
  let rename_modal (s,mo,io) =
    match io with
    | In | Out | Any -> m
    | Prefix l ->
      s, mo, Prefix (List.map
        (fun fpref ->
          match fpref with
          | FTau -> FTau
          | FOut _ | FIn _ -> fpref
          | FInVar s ->
            if SMap.mem s vars then
              let n = String.sub s 1 @@ String.length s - 1 in
              FIn (n ^ "_" ^ (string_of_int @@ int_of_value @@ (SMap.find s vars)))
            else fpref
          | FOutVar s -> if SMap.mem s vars then
              let n = String.sub s 1 @@ String.length s - 1 in
              FOut (n ^ "_" ^ (string_of_int @@ int_of_value @@ (SMap.find s vars)))
            else fpref)
        l)
  in
  rename_modal m

(** Computes a preformula quantified into a correct formula *)
let formula_of_preformula pf =
  let open Syntax in
  let compute_param p =
    match p with
    | PParamVar (n, t) ->
      if not @@ SMap.mem t !env_type then failwith "Not found" else
      n, value_list (SMap.find t !env_type)
    | _ -> failwith
      (Format.sprintf "Unusable param for mu-calculus:%s@." @@ string_of_preparam p)
  in

  (* From Presyntax, modified not to used a global hashtbl, but a local map
     instead *)
  let rec test_expr vars = function
    | PTrue -> Bool true
    | PFalse -> Bool false
    | PInt i -> Int i
    | PName str -> Name str
    | PConst name -> Int (SMap.find name !env_const)
    | PVar name -> if not @@ SMap.mem name vars then
        failwith "Var not found"
      else
        (SMap.find name vars)
    | PNot pexpr -> let b = bool_of_value (test_expr vars pexpr) in Bool (not b)
    | PAnd (preexpr1, preexpr2) ->
      let b1 = bool_of_value (test_expr vars preexpr1)
      and b2 = bool_of_value (test_expr vars preexpr2) in
      Bool ( b1 && b2 )
    | POr (preexpr1, preexpr2) ->
      let b1 = bool_of_value (test_expr vars preexpr1)
      and b2 = bool_of_value (test_expr vars preexpr2) in
      Bool ( b1 || b2 )

    | PAdd (preexpr1, preexpr2) ->
      let i1 = int_of_value (test_expr vars preexpr1 )
      and i2 = int_of_value ( test_expr vars preexpr2 ) in
      Int ( i1 + i2 )

    | PSub (preexpr1, preexpr2) ->
      let i1 = int_of_value (test_expr vars preexpr1 )
      and i2 = int_of_value ( test_expr vars preexpr2 ) in
      Int ( i1 - i2 )

    | PMul (preexpr1, preexpr2) ->
      let i1 = int_of_value (test_expr vars preexpr1 )
      and i2 = int_of_value ( test_expr vars preexpr2 ) in
      Int ( i1 * i2 )

    | PDiv (preexpr1, preexpr2) ->
      let i1 = int_of_value (test_expr vars preexpr1 )
      and i2 = int_of_value ( test_expr vars preexpr2 ) in
      Int ( i1 / i2 )

    | PMod (preexpr1, preexpr2) ->
      let i1 = int_of_value (test_expr vars preexpr1 )
      and i2 = int_of_value ( test_expr vars preexpr2 ) in
      Int ( i1 mod i2 )

    | PInf (preexpr1, preexpr2) ->
      let i1 = int_of_value (test_expr vars preexpr1 )
      and i2 = int_of_value ( test_expr vars preexpr2 ) in
      Bool ( i1 < i2 )

    | PSup (preexpr1, preexpr2) ->
      let i1 = int_of_value (test_expr vars preexpr1 )
      and i2 = int_of_value ( test_expr vars preexpr2 ) in
      Bool ( i1 > i2 )

    | PEq (preexpr1, preexpr2) ->
      let p1 = test_expr vars preexpr1
      and p2 = test_expr vars preexpr2 in
      (match (p1, p2) with
      | (Bool b1, Bool b2) -> Bool ( b1 = b2 )
      | (Int i1, Int i2) -> Bool ( i1 = i2 )
      | (Name n1, Name n2) -> Bool ( n1 = n2 )
      | (_, _) -> Bool ( false ))

    | PNeq (preexpr1, preexpr2) ->
      let p1 = test_expr vars preexpr1
      and p2 = test_expr vars preexpr2 in
      (match (p1, p2) with
      | (Bool b1, Bool b2) -> Bool ( b1 <> b2 )
      | (Int i1, Int i2) -> Bool ( i1 <> i2 )
      | (Name n1, Name n2) -> Bool ( n1 <> n2 )
      | (_, _) -> Bool ( true ))

    | PInfEq (preexpr1, preexpr2) ->
      let i1 = int_of_value (test_expr vars preexpr1 )
      and i2 = int_of_value ( test_expr vars preexpr2 ) in
      Bool ( i1 <= i2 )

    | PSupEq (preexpr1, preexpr2) ->
      let i1 = int_of_value (test_expr vars preexpr1 )
      and i2 = int_of_value ( test_expr vars preexpr2 ) in
      Bool ( i1 >= i2 )

    | PIf (cond, preexpr1, preexpr2) ->
      let b = bool_of_value (test_expr vars cond) in
      if b then
        test_expr vars preexpr1
      else
        test_expr vars preexpr2
  in

  let res_of_expr e vars =
    match test_expr vars e with
    | Bool b -> b
    | _ -> failwith "The result of the expression wasn't a boolean expression"
  in

  let rec step vars = function
    | PFTrue -> FTrue
    | PFFalse -> FFalse
    | PFPar f -> FPar (step vars f)
    | PFAnd (f, g) -> FAnd (step vars f, step vars g)
    | PFOr (f, g) -> FOr (step vars f, step vars g)
    | PFImplies (f, g) -> FImplies (step vars f, step vars g)
    | PFModal(m, f) -> FModal (substitute_modality m vars, step vars f)
    | PFInvModal (m, f) -> FInvModal (substitute_modality m vars, step vars f)
    | PFVar v -> FVar v
    | PFMu (x, f) -> FMu (x, PSet.empty, step vars f)
    | PFNu (x, f) -> FNu (x, PSet.empty, step vars f)

    | PFProp (s, pfl) -> (* inlining *)
      if Hashtbl.mem props s then
        let (vars', formula) = Hashtbl.find props s in
        let fl = List.map (step vars) pfl in
        substitute formula @@ List.combine vars' fl
      else
        raise (Unbound_prop s)

(* The next two cases compute the qunatification, modifying the modalities to
   the value given by the quantification *)
    | PFForall (param, expr, f) ->
      let n, val_list = compute_param param in
      List.fold_left
        (fun acc_f i ->
          let vars = SMap.add n i vars in
          let b = res_of_expr expr vars in
          if b then
            let f = step vars f in
            if acc_f = FTrue then f
            else FAnd (f, acc_f)
          else acc_f)
        FTrue
        val_list

    | PFExists (param, expr, f) ->
      let n, val_list = compute_param param in
      List.fold_left
        (fun acc_f i ->
          let vars = SMap.add n i vars in
          let b = res_of_expr expr vars in
          if b then
            let f = step vars f in
            if acc_f = FFalse then f
            else FOr (f, acc_f)
          else acc_f)
        FFalse
        val_list

  in
  Format.printf "Preformula received :\n%s@." @@ string_of_preformula pf;
  let res = step SMap.empty pf in
  Format.printf "Result :\n%s@." @@ string_of_formula res;
  res
