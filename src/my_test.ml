open Syntax
open Local_checker
open Formula
open Presyntax

let p1 =
  Par
    (Sum
       (Prefix (Tau, Prefix (In "a", Prefix (Out "b", Silent))),
        Prefix (Out "a", Prefix (In "b", Silent))),
     Prefix (In "c", Silent))

let p2 = Res ("a", p1)

let f1 =
  FModal (Necessity (Strong, Coll [(PIn (PName "b"))]), FFalse)

let f2 =
  FModal (Possibly (Weak, Coll [(POut (PName "a"))]), FTrue)

let f3 =
  FModal (Possibly (Strong, Coll [PTau]), FTrue)

let f4 =
  FAnd (FModal (Necessity (Strong, Any), FTrue), FTrue)

let f5 =
  FModal (Possibly (Strong, Coll [POut (PName "b")]), FTrue)

(* νX.([b!]False and [b!]X) *)
let f_nu = FNu ("X", FixSet.empty, FAnd ((FModal (Necessity (Strong, Coll [(POut (PName "b"))]), FFalse)), 
					(FModal (Necessity (Strong, Any), FVar "X"))))

let p_nu = Prefix (Out "a", (Prefix (Out "a", Silent)))

(* tau,tau,c!,tau,tau,P *)
let weak_test_process1 = Prefix (Tau, Prefix (Tau, Prefix (Out "c", Prefix (Tau, Prefix (Out "a", Silent)))))
let weak_test_formula1 = FModal(Necessity(Weak, Coll [POut (PName "c")]), 
				FModal (Possibly (Strong, Coll [POut (PName "a")]), FTrue))

let weak_test_formula2 = FModal (Necessity (Weak, Any), 
				 FModal (Possibly (Strong, Coll [POut (PName "c")]), FTrue))

(* tau,a!,tau,b! + tau,a!,c! *)
let weak_test_process3 = 
  let g = Prefix (Tau, Prefix (Out "a", Prefix (Tau, Prefix (Out "b", Silent)))) in
  let d = Prefix (Tau, Prefix (Out "a", Prefix (Tau, Prefix (Out "c", Silent)))) in
  Par (g, d)

(* [[a!]][!]true *)
let weak_test_formula3 = FModal (Necessity (Weak, Coll [POut (PName "a")]), 
				 FModal (Necessity (Strong, Coll [PTau]), FFalse))

let tests = 
  [ (f1, p1)
  ; (f2, p1)
  ; (f3, p1)
  ; (f4, p1)
  ; (f5, p1)
  ; (f_nu, p_nu)
  ; (weak_test_formula1, weak_test_process1)
  ; (weak_test_formula2, weak_test_process1)
  ; (weak_test_formula3, weak_test_process3)
  ]
 
let () =
  let cpt = ref 1 in
  List.iter 
    (fun (form, proc) ->
      Printf.printf "----------------\nTest %d\n" !cpt;
      Printf.printf "%s satisfait-il %s\n%!"
	(string_of_process proc)
	(string_of_formula form);
      Printf.printf "=> %b\n%!"
	(check_formula (Hashtbl.create 0) (Hashtbl.create 0) proc form);
      incr cpt) 
    tests
