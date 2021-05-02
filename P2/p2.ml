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

let find terminal reglas =
	let rec loop conj = function
		[] -> conj
		| (Regla_gic(not_terminal, lst))::tl -> 
			if (List.mem terminal lst) then
				loop (agregar not_terminal conj) tl
			else
				loop conj tl
	in loop (Conjunto []) reglas
;;

let cyk inputs (Gic(no_terminales, terminales, reglas, destacado)) =
	if ((List.length inputs) = 0) then
		raise(Failure "Input string is empty.")
	else if not (es_fnc (Gic(no_terminales, terminales, reglas, destacado))) then
		raise(Failure "GIC is not in FNC.")
	else
		let rec loop lst = function
			[] -> List.rev lst
			| terminal::tl -> loop ((find terminal (list_of_conjunto reglas))::lst) tl
		in loop [] inputs
;;


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
