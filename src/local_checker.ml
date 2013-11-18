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

(** [subst id B B'] substitue les occurences de la variable [id]
    (e.g, les X d'un nu) dans la formule [B] par [B'] *)
let rec subst id f f' =
  match f with
    | FVar s when s = id -> f'

    | FTrue
    | FFalse
    | FProp _ (* ? *)
    | FVar _ -> f

    | FAnd (f1, f2) -> FAnd (subst id f1 f', subst id f2 f')
    | FOr (f1, f2) -> FOr (subst id f1 f', subst id f2 f')
    | FNot f -> FNot (subst id f f')
    | FImplies (f1, f2) -> FImplies (subst id f1 f', subst id f2 f')
    | FModal (m, f) -> FModal (m, subst id f f')
    | FInvModal (m, f) -> FInvModal (m, subst id f f')
    | FMu (s, env, f) -> FMu(s, env, subst id f f')
    | FNu (s, env, f) -> FNu(s, env, subst id f f')

let eval_call def_env id values = 
(* Ouais bah pas l'choix ! *)
  let def = ref None in
  let (Definition (name, values, body)) = 
    Hashtbl.iter 
      (fun _ ((Definition (name,_,_)) as v) -> 
	if name = id then def := Some v) def_env;
    match !def with
      | Some v -> v
      | None -> raise (Failure ("Unbound definition : "^ id))
  in
  (* Je sais pas comment faire pour évaluer le call. *)
  (* let evaluated_body = substs body vl values in *)
  ignore values;
  body
    
let restriction name proc = 
  match proc with
    | Silent -> true
    | Prefix ((In n | Out n),_) -> not (n = name)
    | Prefix _ -> true
    | Res _
    | Rename _
    | Sum _ 
    | Par _ 
    | Call _ -> assert false

(* Todo faire des tests d'exhaustivité *)
(* [[a!]]P ===? µX.[a!](µY.[tau]Y v [.]P) v [tau]X *)
let handle_weak_modalities def_env modality process =
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
    | (Possibly (Weak, (Any | Any_in)) | Necessity (Weak, (Any | Any_in))), Prefix (In _, proc) 
            
    (* Out *)
    | (Possibly (Weak, (Any | Any_out)) | Necessity (Weak, (Any | Any_out))), Prefix (Out _, proc)
      -> [proc]
      
    (* Var *)
    | (Possibly (Weak, Coll l) | Necessity (Weak, Coll l)), Prefix (prefix, proc)
      when is_action_in_list prefix l
	-> assert (prefix <> Tau); [proc]

    | _, Par (p1, p2) ->
      List.map (fun sub_p -> Par (sub_p, p2)) (remove_first_part (modality, p1))
      @ List.map (fun sub_p -> Par (p1, sub_p)) (remove_first_part (modality, p2))
    | _, Sum (p1, p2) ->
      remove_first_part (modality, p1) @ remove_first_part (modality, p2)


    | _, Res (name, proc) -> failwith "rm-first - Res : not handled yet"
    | _, Call (name, vl) -> remove_first_part (modality, (eval_call def_env name vl))
    | _, Rename (n1, n2, proc) -> remove_first_part (modality, (Syntax.subst proc n1 n2))

    | _ -> []
  in
  (* On "slurp" tous les tau restants *)
  let rec remove_last_part = function
    | Silent -> []

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
    | Call (name, vl) -> remove_last_part (eval_call def_env name vl)
    | Rename (n1, n2, proc) -> remove_last_part (Syntax.subst proc n1 n2)

  in
  let first_parts = remove_first_part (modality, process) in
  List.map remove_last_part first_parts >> List.flatten
  

(** @return L'ensemble des processus découlant de l'action décrit par la modalité *)
let rec modal_sub_processes def_env modality process =
  match (modality, process) with      
    | _, Silent -> []

    | (Possibly (Weak, _) | Necessity (Weak, _)), _ ->
      handle_weak_modalities def_env modality process 
    
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
      (* Todo : ajouter le tau aux transitions *)
	List.map (fun sub_p -> Par (sub_p, p2)) (modal_sub_processes def_env modality p1)
	@ List.map (fun sub_p -> Par (p1, sub_p)) (modal_sub_processes def_env modality p2)
    | _, Sum (p1, p2) ->
      modal_sub_processes def_env modality p1 @ modal_sub_processes def_env modality p2
	
    (* Named actions *)
    | (Possibly (Strong, Coll acts) | Necessity (Strong, Coll acts)), Prefix (pre, proc)
      when is_action_in_list pre acts -> [proc]

    | _, Res (name, proc) -> failwith "TODO"
    (* let possibles_processes = modal_sub_processes def_env modality proc in
       List.filter (restriction name) possibles_processes*)
    | _, Call (name, vl) ->
      modal_sub_processes def_env modality (eval_call def_env name vl)
      
    | _, Rename (n1, n2, proc) -> 
      modal_sub_processes def_env modality (Syntax.subst proc n1 n2)
	
    | _ -> []
  
module Prop_env = Map.Make(String)

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
    

let rec check_modality def_env prop_env modality formula process =
(*  print_endline "check_modality :";
  Printf.printf "m : %s, form : %s, proc : %s\n%!" (string_of_modality modality) (string_of_formula formula) (string_of_process process) ;*)
  let sub_processes = modal_sub_processes def_env modality process in
(*   List.iter (fun p -> Printf.printf "sub_processes : %s\n" (string_of_process p)) sub_processes;*)
  if (is_possibly modality)
  then List.exists (fun p -> check_formula def_env prop_env p formula) sub_processes
  else List.for_all (fun p -> check_formula def_env prop_env p formula) sub_processes

and check_formula def_env prop_env process = function
  | FTrue -> true
  | FFalse -> false
  | FAnd (f1, f2) -> check_formula def_env prop_env process f1 && check_formula def_env prop_env process f2
  | FOr (f1, f2) -> check_formula def_env prop_env process f1 || check_formula def_env prop_env process f2
  | FNot f -> not (check_formula def_env prop_env process f)
  | FImplies (f1, f2) -> 
    not (check_formula def_env prop_env process f1) 
    || check_formula def_env prop_env process f2
  | FModal (m, f) -> check_modality def_env prop_env m f process
  | FInvModal (m, f) -> not (check_modality def_env prop_env m f process)
  | FProp (id, args) -> 
    check_formula def_env prop_env process (reduce_proposition prop_env id args)
  | FVar id -> 
    check_formula def_env prop_env process (reduce_proposition prop_env id [])  
  | FMu (id, mu_env, f) -> 
    let equiv = FNot (FNu (id, mu_env, FNot (subst id f (FNot (FVar id))))) in
    check_formula def_env prop_env process equiv

  | FNu (id, nu_env, f) -> 
    FixSet.mem process nu_env
    || let new_env = FixSet.add process nu_env in
       let b' = subst id f (FNu(id, new_env, f)) in
       check_formula def_env prop_env process b'    
