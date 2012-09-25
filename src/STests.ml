open Printf
open Utils
open Syntax
open NormTests

let once = Prefix(Out "once", Silent)

let def_once = Definition ("OneShot",[],once)

let pileGagne = Sum (Prefix (In("pile"), Prefix(Out("gagne"),Silent)),
		     Prefix (In("face"), Prefix(Out("perd"),Silent)))

let def_PileGagne = Definition ("PileGagne",[],pileGagne)

let piece = Sum (Prefix(Out("pile"),Silent),
		 Prefix(Out("face"),Silent))

let def_Piece = Definition ("Piece",[],piece)

let def_Jeu = Definition("Jeu",[], Par (piece,pileGagne))

let def_com = Res("a",Par(Prefix(Out("a"),Silent),
			       Prefix(In("a"),Silent)))

let def_com' = Res("b",Par(Prefix(Out("b"),Silent),
			       Prefix(In("b"),Silent)))

let def_res = Par( (Res("a",(Par ((Prefix(Out("a"),Silent)),
				  (Prefix(In("a"),Prefix(Tau,Silent))))))),
		   (Prefix(In("a"), Silent)))
			     

let def_res' = Par( (Res("b",(Par ((Prefix(Out("b"),Silent)),
				  (Prefix(In("b"),Prefix(Tau,Silent))))))),
		   (Prefix(In("a"), Silent)))

let prNames pref fn pname proc =
  printf "%s (%s) = %s\n" pref pname (string_of_set ident (fn proc));
;;

let prAllNames proc = 
  printf "---------\n";
  printf "P := %s\n" (string_of_process proc);
  prNames "free" freeNames "P" proc;
  prNames "bound" boundNames "P" proc;
  prNames "names" names "P" proc;
  flush stdout;
;;  

let testCongr proc1 proc2 =
  printf "---------\n";
  printf "P := %s\n" (string_of_process proc1);
  printf "norm(P) = %s\n" (string_of_nprocess (normalize proc1));
  printf "Q := %s\n" (string_of_process proc2);
  printf "norm(Q) := %s\n" (string_of_nprocess (normalize proc2));
  printf "P == Q ? %s\n%!" (if proc1 === proc2 then "yes" else "no");
;;

let test1 = prAllNames (def_body def_Jeu);;

let test2 = testCongr def_com def_com';;

let test3 = testCongr def_res def_res';;

normalize_random_check 1000 50;;
normalize_exhaustive_check 50 5;;
