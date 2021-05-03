#load "talf.cma";;
open Auto;;
open Conj;;
open Ergo;;
open Graf;;

(*EJERCICIO 1*)

let es_fnc (Gic(no_terminales, terminales, reglas, destacado)) = 
	let rec loop = function
		[] -> true
		| (Regla_gic(not_terminal, lst))::tl -> match lst with
			[] -> loop tl
			| l -> 
				match l with
					[Terminal _] -> loop tl
					| [No_terminal _] -> loop tl
					| [No_terminal _; No_terminal _] -> loop tl
					| _ -> false
	in loop (list_of_conjunto reglas)
;;

(*
	Ejemplos para el ejercicio 1:

	let gic_fnc = gic_of_string "S A B C; a b; S;S -> A B | B C;A -> B A | a;B -> C C | b;C -> A B | a;";;
	es_fnc gic_fnc;;

	(A -> a B)
	let gic1 = gic_of_string "S A B; a b c; S;S -> A;S -> B;A -> a B;B -> A B | epsilon;";;
	es_fnc gic1;;

	(B -> A B A)
	let gic2 = gic_of_string "S A B; a b c; S;S -> A;S -> B;A -> a;A -> B;B -> A B A | epsilon;";;
	es_fnc gic2;;

	(A -> a a)
	let gic3 = gic_of_string "S A B; a b c; S;S -> A;S -> B;A -> a a;A -> B;B -> A B | epsilon;";;
	es_fnc gic3;;

	let gic = gic_of_string "S A B; a b c; S;S -> a A;A -> a b c A;B -> b c B | epsilon;";;
	es_fnc gic;;
*)



(*EJERCICIO 2*)


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


(*
# next_lvl (init_list r c);;
- : (Auto.simbolo * Auto.simbolo) Conj.conjunto list =
[Conjunto [(No_terminal "B", No_terminal "B")];
 Conjunto [
 	(No_terminal "B", No_terminal "A");
 	(No_terminal "B", No_terminal "C")];
 Conjunto [
 	(No_terminal "A", No_terminal "B");
 	(No_terminal "C", No_terminal "B")]
]
*)
let next_lvl lst =
	let rec loop conj l = match l with
		[] -> List.rev (list_of_conjunto conj)
		| hd::tl -> match tl with
				hd2::t -> loop (agregar (cartesiano hd hd2) conj) tl
				| _ -> loop conj tl
	in loop (Conjunto []) lst 
;;


(*
# find2 [No_terminal "B"; No_terminal "B"] r;;
- : Auto.simbolo Conj.conjunto = Conjunto []
# find2 [No_terminal "B"; No_terminal "A"] r;;
- : Auto.simbolo Conj.conjunto = Conjunto [No_terminal "A"]
# find2 [No_terminal "A"; No_terminal "B"] r;;
- : Auto.simbolo Conj.conjunto = Conjunto [No_terminal "S"; No_terminal "C"]
*)
let find2 not_terminales reglas = 
	let rec loop lst = function
		[] -> conjunto_of_list (List.rev lst)
		| (Regla_gic(not_terminal, l))::tl -> 
			if (not_terminales = l) then
				loop (not_terminal::lst) tl
			else
				loop lst tl
	in loop [] reglas
;;

let next reglas lst =
	let rec loop l = function
		[] -> List.rev l
		| (Conjunto l)::tl ->
			let rec loop2 conj = function
				(h1,h2)::tl -> loop2 (agregar (find2 [h1;h2] reglas) conj) tl
				| [] -> conj
			in loop ((loop2 (Conjunto []) l)::l) tl
	in loop [] lst
;;

let next reglas lst =
	let rec loop l_aux = function
		[] -> List.rev l
		| (Conjunto l)::tl ->
			let rec loop2 ll = function
				(h1,h2)::tl -> loop2 ((find2 [h1;h2] reglas)::ll) tl
				| [] -> ll
			in loop ((loop2 [] l)@l_aux) tl
	in loop [] lst
;;


let cyk inputs (Gic(no_terminales, terminales, reglas_gic, destacado)) =
	let reglas = list_of_conjunto reglas_gic
	in
	let rec loop lst count = match count with
		0 -> lst
		| _ -> loop (next_lvl lst) (count-1)
	in loop (init_list reglas inputs) (List.length inputs)
;;





(*
pruebas 

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


let cyk inputs (Gic(no_terminales, terminales, reglas, destacado)) =
	if ((List.length inputs) = 0) then
		raise(Failure "Input string is empty.")
	else if not (es_fnc gic) then
		raise(Failure "GIC is not in FNC.")
	else
		let rec loop = function
			[] -> ""
			| (Terminal t)::tl -> t^(loop tl)
		in loop inputs
;;

(*
	let g = gic_of_string "S A B C; a b; S;S -> A B | B C;A -> B A | a;B -> C C | b;C -> A B | a;";;
	cyk (cadena_of_string "b b a b") g;;
*)
