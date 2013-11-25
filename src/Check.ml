open Formula
open Global
open Semop
open Bdd
open Utils

(** Local model checker *)

(** takes a normalized processor *)
let compute_derivation s =
  if s = Weak then
    Semop.weak_transitions false global_definition_map
  else
    Semop.derivatives global_definition_map

exception Impossible_transition

(* Computes derivations for named actions *)
let get_matching_derivations_named act tr acc =
  TSet.fold
    (fun t acc ->
      let _, pre, _ = t in
      match act, pre with
      | FIn s, T_In n | FOut s, T_Out n ->
        if s = n then TSet.add t acc else acc
      | FTau, T_Tau -> TSet.add t acc
      | _, _ -> acc)
    tr
    acc

(* Computes derivation for "polymorphic" actions *)
let get_matching_derivations io tr =
  TSet.fold
    (fun t acc ->
      let _, pre, _ = t in
      match io, pre with
      | In, T_In _ | Out, T_Out _ | _, T_Tau | Any, _ -> TSet.add t acc
      | _, _ -> acc)
    tr
    TSet.empty


(* Returns the transitions that matches the actions in the modality *)
let compute_modality modl tr =
  match modl with
  | _, _, Prefix acts ->
    List.fold_left
      (fun acc a ->
        get_matching_derivations_named a tr acc)
      TSet.empty
      acts
  | _, _, (_ as io) ->
    get_matching_derivations io tr

(** Main function for the local checker *)
let handle_check_local form proc =
  let proc = Normalize.normalize proc in

  let rec step proc trace = function
    | FTrue -> true, trace

    | FFalse -> false, trace

    | FVar v -> failwith (Format.sprintf "This variable is unbound: %s@." v)

    | FPar f -> step proc trace f

    | FNot f -> let r, t = step proc trace f in
                (not r, t)

    | FAnd (f, g) -> let r1, t1 = step proc trace f in
                     let r2, t2 = step proc trace g in
                     if r1 && r2 then true, t1
                     else if r1 then false, t2
                     else false, t1

    | FOr (f, g) -> let r1, t1 = step proc trace f in
                    let r2, _ = step proc trace g in
                    if r1 || r2 then true, t1
                    else false, t1 (* both can be considered as an incorrect
                                      trace *)

    | FImplies (f, g) ->
      let r1, t1 = step proc trace f in
      let r2, _t2 = step proc trace g in
      not r1 || r2, t1

    | FModal (m, f) ->
      let s,_,_ = m in
      let d = compute_derivation s proc in
      let res = compute_modality m d in (* gets the transitions corresponding to
                                           the modal *)
      if TSet.is_empty res then (not @@ diamond m, trace)
      else if diamond m then
        (* We could have used TSet.exists, but we only can get the boolean
           results, not the trace *)
        TSet.fold
          (fun ((_, m, p') as _tr) (r, t) ->
            if r then r,t (* no need to test the transition if one is
                             true *)
            else step p' (m::t) f)
          res
          (false, trace)
      else
        TSet.fold
          (fun (_, m, p') (r, t) ->
            if not r then r,t (* no need to test the transition if one is
                                 false *)
            else step p' (m::t) f)
          res
          (true, trace)

    | FInvModal(m, f) ->
      let r, t = step proc trace @@ FModal (m,f) in
      (not r, t)

    | FNu (x, s, f) ->
      if PSet.mem proc s then true, trace
      else
        let s = PSet.add proc s in
        let f = reduce f x @@ FNu(x, s, f) in
        step proc trace f

    | FMu (x, s, f) ->
      (* We use the duality of the least fixed point *)
      let f = FNot (reduce f x @@ FNot (FVar x)) in
      let f = FNot (FNu (x, s, f))  in
      step proc trace f

        (* In case that happen, we substitute the prop by its corresponding
           formula, that shouldn't however *)
    | FProp (s, il) ->
      let f = if Hashtbl.mem props s then
        let (vars, formula) = Hashtbl.find props s in
        substitute formula @@ List.combine vars il
      else
        raise (Unbound_prop s) in
      step proc trace f

  in
  let (res, trace) = step proc [] form in
  if res then
    Format.printf "The processor given matches the model@."
  else
    begin
      let t = List.rev trace |>
          List.fold_left (fun acc t ->
            Format.sprintf "%s --> %s" acc @@ string_of_label t) ""
      in
      let t = Format.sprintf "%s --> <stuck>"  t in
      Format.printf "Doesn't match, here is why: @.%s@." t
    end

(** Global model checking *)

(** This is not working, those functions are only draft to show the work done to
    understand and implement the global model checking algorithm *)

let associate_vars f =
  let rec step f acc =
    match f with
    | FTrue | FFalse -> acc
    | FVar x -> x :: acc
    | FPar f | FNot f -> step f acc
    | FAnd (f1, f2) | FImplies (f1, f2) | FOr (f1, f2) ->
      let acc = step f1 acc in
      step f2 acc
    | FModal (_, f) | FInvModal (_, f) -> step f acc
    | FProp (_,_) -> assert false (* assuming there is no prop at this state *)
    | FMu (_, _, f) | FNu (_, _, f) -> step f acc
  in
  step f []



let (bdds : (string, Bdd.bdd) Hashtbl.t)= Hashtbl.create 19


let rec fix f env name =
  let rec step f env =
    let old = SMap.find name env in
    let env = SMap.add name old env in
    let res = compute_obdd f env in
    if HashedBdd.equal res old then res
    else step f env
  in
  step f env


and compute_obdd f env =

  let implies b1 b2 = (not b1) || b2 in
  let xor b1 b2  = ((not b1) && b2) || (b1 && (not b2)) in
  let rec step f env  =
    match f with
    | FTrue -> one
    | FFalse -> zero
    | FVar x -> SMap.find x env
    | FPar f -> step f env
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
    | FModal (m, f) ->
      if not @@ diamond m then step (FInvModal(m, FNot f)) env
      else assert false
    | FInvModal (_m, _f) -> assert false
    | FProp (name,_) -> Hashtbl.find bdds name
    | FMu (name, _, f) -> fix f (SMap.add name zero env) name
    | FNu (name, _, f) -> fix f (SMap.add name one env) name

  in
  step f env

let bdd_of_formula f name =
  (* let vars = associate vars f in *)
  if Hashtbl.mem bdds name then Hashtbl.find bdds name
  else
    let bdd = compute_obdd f @@ SMap.empty in
    (Hashtbl.add bdds name bdd;
     bdd)

let count_fixpoint f =
  let rec step f acc count =
    match f with
    | FTrue | FFalse -> acc, count
    | FVar _ -> step f acc count
    | FPar f | FNot f -> step f acc count
    | FAnd (f1, f2) | FImplies (f1, f2) | FOr (f1, f2) ->
      let acc, count = step f1 acc count in
      step f2 acc count
    | FModal (_, f) | FInvModal (_, f) -> step f acc count
    | FProp (_,_) -> assert false
    | FMu (_, _, f) -> step f ((count, true) :: acc) (count+1)
    | FNu (_, _, f) -> step f ((count, false) :: acc) (count+1)
  in
  step f [] 0

type ens =
  Top | Bot
| Trans of io * ens
| EForAll of ens list
| Exists of ens list

let rec string_of_ens = function
  | Top -> "Top"
  | Bot -> "Bot"
  | Trans (io, ens) -> "Trans: " ^ (string_of_io io) ^ "->" ^
    (string_of_ens ens)
  | EForAll l ->
    (List.fold_left
      (fun acc e -> acc ^ "; " ^ (string_of_ens e)) "EForAll:[" l) ^ "]"
  | Exists l ->
    (List.fold_left
      (fun acc e -> acc ^ "; " ^ (string_of_ens e)) "Exists:[" l) ^ "]"

let trans_equiv a b =
  match a, b with
  | Any, _ | _, Any -> true
  | In, In | Out, Out -> true
  | In, Prefix pl | Prefix pl, In ->
    List.fold_left
      (fun acc fp ->
        match fp with
        | FTau | FIn _ | FInVar _ -> acc
        | _ -> false)
      true
      pl
  | Out, Prefix pl | Prefix pl, Out ->
    List.fold_left
      (fun acc fp ->
        match fp with
        | FTau | FOut _ | FOutVar _ -> acc
        | _ -> false)
      true
      pl
  | _, _ -> a = b


let rec union ens1 ens2 =
  Format.printf "Union between: %s && %s@." (string_of_ens ens1) (string_of_ens ens2);
  match ens1, ens2 with
  | Top, _ | _, Top-> Top
  | e, Bot | Bot, e -> e

  | Trans (a1, e1), Trans (a2, e2) ->
    if a1 = a2 then Trans (a1, union e1 e2)
    else Exists ([ens1; ens2])

  | (Trans (a, e) as t), Exists l
  | Exists l, (Trans (a, e) as t) ->
    let added = ref false in
    let l = List.fold_left
      (fun acc el ->
        match el with
        | Trans (a2, e2) ->
          if a2 = a then (added := true; Trans (a, union e e2) :: acc)
          else el :: acc
        | _ -> el :: acc)
      []
      l
    in
    let l = if !added then l else t :: l in
    Exists l

  | (Trans (a, e) as t), (EForAll l) | (EForAll l), (Trans (a, e) as t) ->
    let added = ref false in
    let l = List.fold_left
      (fun acc el ->
        match el with
          Trans (a2, e2) ->
            if a2 = a then (added := true;Trans (a, union e e2) :: acc)
            else el :: acc
        | _ -> el :: acc)
      []
      l
    in
    let l = if !added then l else t :: l in
    EForAll l

  | EForAll l1, EForAll l2 ->
    let l = List.fold_left
      (fun acc e -> union e acc) (EForAll l2) l1 in
    l

  | Exists l1, Exists l2 ->
    let l = List.fold_left
      (fun acc e -> union acc e) (Exists l2) l1 in
    l

  | (Exists _ as c), (EForAll _ as a) | (EForAll _ as a), (Exists _ as c) ->
    Exists [c; a]


let rec inter ens1 ens2 =
  Format.printf "Inter between: %s && %s@." (string_of_ens ens1) (string_of_ens ens2);
  match ens1, ens2 with
  | _, _ when ens1 = ens2 -> ens1
  | Top, e | e, Top -> e
  | _, Bot | Bot, _ -> Bot

  | Trans (a, e1), Trans (b, e2) ->
    if trans_equiv a b then
      Trans (a, inter e1 e2)
    else Bot

  | (Trans (a, e) as t), Exists l | Exists l, (Trans (a, e) as t) ->
    let added = ref false in
    let l = List.fold_left
      (fun acc el ->
        match el with
        | Trans (a2, e2) ->
          if a2 = a then (added := true; Trans (a, inter e e2) :: acc)
          else el :: acc
        | _ -> el :: acc)
      []
      l
    in
    let l = if !added then l else t :: l in
    Exists l

  | (Trans (a, e) as t), EForAll l | EForAll l, (Trans (a, e) as t) ->
    let added = ref false in
    let l = List.fold_left
      (fun acc el ->
        match el with
          Trans (a2, e2) ->
            if a2 = a then (added := true;Trans (a, inter e e2) :: acc)
            else el :: acc
        | _ -> el :: acc)
      []
      l
    in
    let l = if !added then l else t :: l in
    EForAll l

  | EForAll l1, EForAll l2 ->
    let l = List.fold_left
      (fun acc e -> inter e acc) (EForAll l2) l1 in
    l

  | Exists l1, Exists l2 ->
    let l = List.fold_left
      (fun acc e -> inter acc e) (Exists l2) l1 in
    l


  | (Exists _ as c), (EForAll _ as a) | (EForAll _ as a), (Exists _ as c) ->
    Exists [c; a]

type fp = Nu | Mu


let rec evalrec a f env i =
  match f with
  | FTrue -> Top
  | FFalse -> Bot
  | FVar v -> SMap.find v env
  | FPar f -> evalrec a f env i

  | FAnd (f1, f2) ->
    let e1 = evalrec a f1 env i in
    let e2 = evalrec a f2 env i in
    inter e1 e2

  | FOr (f1, f2) ->
    let e1 = evalrec a f1 env i in
    let e2 = evalrec a f2 env i in
    union e1 e2

  | FModal (m, f) | FInvModal (m, f) ->
    let _, m, io = m in
    let f = evalrec a f env i in
    (match m with
    | Possibly -> Exists([Trans(io, f)])
    | _ -> EForAll([Trans(io, f)]))

  | FMu (v, _, f) -> fixpoint a Mu v f i env
  | FNu (v, _, f) -> fixpoint a Nu v f i env
  | FProp (_, _) -> assert false
  | FNot _ -> assert false
  | FImplies (_, _) -> assert false

and fixpoint a fp var f i env =
  let ens = match fp with Mu -> Top | Nu -> Bot in
  for j=0 to i-1 do
    let (ty, _) = a.(j) in
    if ty = fp then a.(j) <- ty, ens
  done;
  let r_old = ref a.(i) in
  let first = ref true in
  while !r_old <> a.(i) || !first do
    first := false;
    let ty, ens = a.(i) in
    r_old := ty, ens;
    let env = SMap.add var ens env in
    a.(i) <- ty, evalrec a f env (i+1);
  done;
  let _, ens = a.(i) in
  ens

let check_ens ens proc =

  (* let get_matching_deriv s p a = *)
  (*   let deriv = compute_derivation s p in *)
  (*   TSet.fold *)
  (*     (fun ((_, m, p') as _tr) acc -> *)
  (*       step p' (m::t) f) *)
  (*     deriv *)
  (*     [] *)
  (* in *)

  let _proc = Normalize.normalize proc in
  let res = match ens with
    | Bot -> false
    | Top -> true
    | Trans(_a, _e) -> assert false
      (* let m = Strong, Possibly, a in (\* The first two are just to match the *)
      (*                                   modality scheme *\) *)
      (* let d = compute_derivation Strong proc in *)
      (* let res = compute_modality m d in *)
      (* if TSet.is_empty res then false *)
      (* else if diamond m then *)
      (*   TSet.fold *)
      (*     (fun ((_, m, p') as _tr) (r, t) -> *)
      (*       (\* Format.printf "t: %s@." @@ string_of_transition tr; *\) *)
      (*       if r then r,t (\* no need to test the transition if one is *)
      (*                        true *\) *)
      (*       else step p' (m::t) f) *)
      (*     res *)
      (*     false *)
    | Exists _l -> assert false
    | EForAll _l -> assert false
  in
  res

let check_global f _ =
  let acc, n = count_fixpoint f in
  let a = Array.make n (Mu, Top) in
  let rec make acc =
    match acc with
    | [] -> ()
    | (i, b)::l ->
      a.(i) <- if b then Mu, Top else Nu, Bot;
      make l
  in
  make acc;
  let ens = evalrec a f SMap.empty 0 in
  Format.printf "Ens: %s@." @@ string_of_ens ens
