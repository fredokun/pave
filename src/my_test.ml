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
  FModal (FNecessity [(PIn (PName "b"))], FFalse)

let f2 =
  FModal (FWPossibly [(POut (PName "a"))], FTrue)

let f3 =
  FModal (FPossibly [PTau], FTrue)

let f4 =
  FAnd ((FModal (FAnyNecessity, FTrue)), FTrue)

let f5 =
  FModal (FPossibly [POut (PName "b")], FTrue)

(* νX.([b!]False and [b!]X) *)
let f_nu = FNu("X", FAnd ((FModal (FNecessity [(POut (PName "b"))], FFalse)), 
			 (FModal (FAnyNecessity, FVar "X"))))

let p_nu = Prefix (Out "a", (Prefix (Out "a", Silent)))

let tests = 
  [ (f1, p1)
  ; (f2, p1)
  ; (f3, p1)
  ; (f4, p1)
  ; (f5, p1)
  ; (f_nu, p_nu)
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
	(check_formula form proc);
      incr cpt) 
    tests
