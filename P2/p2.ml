#load "talf.cma";;
open Auto;;
open Conj;;
open Ergo;;
open Graf;;

(*EJERCICIO 1*)

let es_fnc (Gic(_, _, reglas, _)) = 
	let rec loop = function
		[] -> true
		| (Regla_gic(_, lst))::tl -> match lst with
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


exception Parsing_Error;;
exception Null_String;;
exception GIC_not_FNC;;



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
	| _ -> raise Parsing_Error
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


let cyk inputs (Gic(nt, t, reglas_gic, destacado)) =
	let reglas = list_of_conjunto reglas_gic in
	let primera_fila = init_list reglas inputs
	and len = (List.length inputs) in
	let rec loop lst j = 
		if (j=len) then 
			(loopi len j lst reglas)::lst
		else
			loop ((loopi len j lst reglas)::lst) (j+1)
	in 
	if (len=0) then
		raise (Null_String)
	else if not (es_fnc (Gic(nt, t, reglas_gic, destacado))) then
		raise (GIC_not_FNC)
	else
		if (len=1) then
			let conj = find (List.hd inputs) reglas
			in
			pertenece destacado conj
		else
			let gic = loop [primera_fila] 2
			in pertenece destacado (List.hd (geti 1 gic))
;;

(*
	Ejemplos para el ejercicio 2


	GIC no es FNC
	let g = gic_of_string "S A B C; a b; S;S -> A B a | B C;A -> B A | a;B -> C C | b;C -> A B | a;";;
	cyk (cadena_of_string "b b a b") g;;


	Cadena vacía
	cyk [] (gic_of_string "S A B; a b c; S;S -> a A;A -> a b c A;B -> b c B | epsilon;");;


	let g = gic_of_string "S A B C; a b; S;S -> A B | B C;A -> B A | a;B -> C C | b;C -> A B | a;";;
	
	Sí pertenece
	cyk (cadena_of_string "b b a b") g;;
	cyk (cadena_of_string "a b") g;;
	cyk (cadena_of_string "b a b") g;;

	No Pertenece
	cyk (cadena_of_string "a") g;;


	let g = gic_of_string "S X Y A B C; a b c; S;S -> X Y | Y X; X -> A B | C B; Y -> B B | C C; A -> a; B -> b; C -> c;";;

	Sí pertenece
	cyk (cadena_of_string "a b c c") g;;
	cyk (cadena_of_string "c b b b") g;;

	No Pertenece
	cyk (cadena_of_string "a a b b b b") g;;
	cyk (cadena_of_string "a") g;;


	let g = gic_of_string "S X Y A B C; a b c; S;S -> X Y | Y X | a; X -> A B | C B; Y -> B B | C C; A -> a; B -> b; C -> c;";;

	Sí pertenece
	cyk (cadena_of_string "a") g;;
	cyk (cadena_of_string "a b c c") g;;
	cyk (cadena_of_string "c b b b") g;;

	No Pertenece
	cyk (cadena_of_string "a a b b b b") g;;
	cyk (cadena_of_string "b") g;;
*)