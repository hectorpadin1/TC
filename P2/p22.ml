#load "talf.cma";;
open Auto;;
open Conj;;
open Ergo;;
open Graf;;

(*

pruebas

let lst =
[
	[ Conjunto [No_terminal "S"; No_terminal "C"]];
	[ Conjunto [No_terminal "A"]; Conjunto [No_terminal "S"; No_terminal "C"]];
	[ Conjunto []; Conjunto [No_terminal "A"; No_terminal "S"]; Conjunto [No_terminal "S"; No_terminal "C"]];
	[ Conjunto [No_terminal "B"]; Conjunto [No_terminal "B"]; Conjunto [No_terminal "A"; No_terminal "C"]; Conjunto [No_terminal "B"]]
];;
let r = [Regla_gic (No_terminal "S", [No_terminal "A"; No_terminal "B"]);
      Regla_gic (No_terminal "S", [No_terminal "B"; No_terminal "C"]);
      Regla_gic (No_terminal "A", [No_terminal "B"; No_terminal "A"]);
      Regla_gic (No_terminal "A", [Terminal "a"]);
      Regla_gic (No_terminal "B", [No_terminal "C"; No_terminal "C"]);
      Regla_gic (No_terminal "B", [Terminal "b"]);
      Regla_gic (No_terminal "C", [No_terminal "A"; No_terminal "B"]);
            Regla_gic (No_terminal "C", [Terminal "a"])];;
let c = cadena_of_string "b b a b";;
*)

(*
# find (Terminal "a") r;;
- : Auto.simbolo Conj.conjunto = Conjunto [No_terminal "A"; No_terminal "C"]
*)
let find terminal reglas =
	let rec loop lst = function
		[] -> conjunto_of_list (List.rev lst)
		| (Regla_gic(not_terminal, l))::tl -> 
			if (List.mem terminal l) then
				loop (not_terminal::lst) tl
			else
				loop lst tl
	in loop [] reglas
;;

(*
# init_list r c;;
- : Auto.simbolo Conj.conjunto list =
[Conjunto [No_terminal "B"];
 Conjunto [No_terminal "B"];
 Conjunto [No_terminal "A"; No_terminal "C"];
 Conjunto [No_terminal "B"]]
*)
let init_list reglas inputs =
	let rec loop lst = function
		[] -> List.rev lst
		| terminal::tl -> loop ((find terminal reglas)::lst) tl
	in loop [] inputs
;;

let rec geti number = function
	hd::tl -> 
		if (number = 1) then
			hd
		else
			geti (number-1) tl
	| _ -> raise(Not_found)
;;

let getj number lst =
	let l = List.rev lst
	in geti number l
;;

(*
# add 2 2 1 r lst;;
- : Auto.simbolo Conj.conjunto = Conjunto [No_terminal "S"; No_terminal "A"]
# add 2 3 1 r lst;;
- : Auto.simbolo Conj.conjunto = Conjunto [No_terminal "S"; No_terminal "C"]
*)
let add j i k reglas lst =
	let rec loop conj c1 c2 = function
		(Regla_gic (nt, [t1;t2]))::tl -> 
	 		if ((pertenece t1 c1) && (pertenece t2 c2)) then
	 			loop (agregar nt conj) c1 c2 tl
	 		else 
	 			loop conj c1 c2 tl
	 	| _::tl -> loop conj c1 c2 tl
	 	| [] -> conjunto_of_list (List.rev (list_of_conjunto conj))
	and conj1 = geti i (getj k lst)
	and conj2 = geti (i+k) (getj (j-k) lst)
	in loop (Conjunto []) conj1 conj2 reglas
;;


(*
# loopk 2 1 lst r;;
- : Auto.simbolo Conj.conjunto list = [Conjunto []]
# loopk 2 2 lst r;;
- : Auto.simbolo Conj.conjunto list =
[Conjunto [No_terminal "S"; No_terminal "A"]]
*)
let loopk j i lst reglas = 
	let rec loop conj k m =
		if (k=m) then
			[union (add j i k reglas lst) conj]
		else
			loop (union (add j i k reglas lst) conj) (k+1) m
	in loop (Conjunto []) 1 (j-1)
;;

(*
# loopi 4 2 lst r;; 
- : Auto.simbolo Conj.conjunto list =
[Conjunto []; Conjunto [No_terminal "S"; No_terminal "A"];
 Conjunto [No_terminal "S"; No_terminal "C"]]
*)
let loopi n j lst reglas =
	let rec loop i max =
		if (i=max) then
			loopk j i lst reglas
		else
			(loopk j i lst reglas)@(loop (i+1) max)
	in loop 1 (n-j+1)  
;;


let cyk inputs (Gic(no_terminales, terminales, reglas_gic, destacado)) =
	let reglas = list_of_conjunto reglas_gic in
	let primera_fila = init_list reglas inputs
	and len = (List.length inputs) in
	let rec loop lst j = 
		if (j=len) then 
			(loopi len j lst reglas)::lst
		else
			loop ((loopi len j lst reglas)::lst) (j+1)
	in loop [primera_fila] 2
;;
cyk (cadena_of_string "b b a b") (gic_of_string "S A B C; a b; S;S -> A B | B C;A -> B A | a;B -> C C | b;C -> A B | a;");;

