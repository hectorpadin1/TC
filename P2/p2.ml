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
	let g = gic_of_string "S A B C; a b; S;S -> A B a | B C;A -> B A | a;B -> C C | b;C -> A B | a;";;
	cyk (cadena_of_string "b b a b") g;;

	let g = gic_of_string "S A B C; a b; S;S -> A B | B C;A -> B A | a;B -> C C | b;C -> A B | a;";;
	cyk (cadena_of_string "b b a b") g;;
	cyk (cadena_of_string "a a b b b b") g;;

	let g = gic_of_string "S A B C; a b c; S;S -> A B | B C;A -> B A C | a;B -> C C | b;C -> A B | c;";;
	cyk (cadena_of_string "b b a c") g;;

	let g = gic_of_string "S X Y A B C D; a b c d; S;S -> A X | C Y | C D; X -> S B; Y -> S D; A -> a; B -> b; C -> c; D -> d";;
	cyk (cadena_of_string "b b a c") g;;
	cyk (cadena_of_string "b b a c") g;;
*)

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


(*
let lst =
[
	[ Conjunto [No_terminal "S"; No_terminal "C"]];
	[ Conjunto [No_terminal "A"]; Conjunto [No_terminal "S"; No_terminal "C"]];
	[ Conjunto []; Conjunto [No_terminal "A"; No_terminal "S"]; Conjunto [No_terminal "S"; No_terminal "C"]];
	[ Conjunto [No_terminal "B"]; Conjunto [No_terminal "B"]; Conjunto [No_terminal "A"; No_terminal "C"]; Conjunto [No_terminal "B"]]
];;

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


(*
# cart (init_list r c);;
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
let cart lst =
	let rec loop conj l = match l with
		[] -> List.rev (list_of_conjunto conj)
		| hd::tl -> match tl with
				hd2::t -> loop (agregar (cartesiano hd hd2) conj) tl
				| _ -> loop conj tl
	in loop (Conjunto []) lst 
;;

(*
# get 0 lst;;
- : Auto.simbolo Conj.conjunto list =
[Conjunto [No_terminal "S"; No_terminal "C"]]
# get 1 lst;;
- : Auto.simbolo Conj.conjunto list =
[Conjunto [No_terminal "A"]; Conjunto [No_terminal "S"; No_terminal "C"]]
*)
let rec get number = function
	hd::tl -> 
		if (number = 0) then
			hd
		else
			get (number-1) tl
	| _ -> raise(Not_found)
;;

(*
# gen_casilla (No_terminal "A") (No_terminal "B") r;;
- : Auto.simbolo Conj.conjunto = Conjunto [No_terminal "S"; No_terminal "C"]
# gen_casilla (No_terminal "B") (No_terminal "B") r;;
- : Auto.simbolo Conj.conjunto = Conjunto []
*)
let gen_casilla c1 c2 reglas =
 	let rec loop conj c1 c2 = function
	 	(Regla_gic (nt, [t1;t2]))::tl -> 
	 		if ((t1 = c1) && (t2 = c2)) then
	 			loop (agregar nt conj) c1 c2 tl
	 		else
	 			loop conj c1 c2 tl
	 	| _::tl -> loop conj c1 c2 tl
	 	| [] -> conjunto_of_list (List.rev (list_of_conjunto conj))
	 in loop (Conjunto []) c1 c2 reglas
;;

(*
generar_casilla r ([
   (No_terminal "A", No_terminal "B");
     (No_terminal "C", No_terminal "B")]);;
- : Auto.simbolo Conj.conjunto = Conjunto [No_terminal "S"; No_terminal "C"]
*)
let generar_casilla reglas lst =
	let rec loop conj = function
		(hd1,hd2)::tl -> 
			let element = gen_casilla hd1 hd2 reglas in
			loop (union element conj) tl
		| [] -> conj
	in loop (Conjunto []) lst
;;

(*
# generar_fila r (cart (init_list r c));;
- : Auto.simbolo Conj.conjunto list =
[
 Conjunto [];
 Conjunto [No_terminal "S"; No_terminal "A"];
 Conjunto [No_terminal "S"; No_terminal "C"]]
*)
let generar_fila reglas prod_cart =
	let rec loop lst = function
		[] -> List.rev lst
		| hd::tl -> loop ((generar_casilla reglas (list_of_conjunto hd))::lst) tl
	in loop [] prod_cart
;;

let cyk inputs (Gic(no_terminales, terminales, reglas_gic, destacado)) =
	let reglas = list_of_conjunto reglas_gic in
	let primera_fila = init_list reglas inputs
	and len = (List.length inputs) in
	let rec loop lst n = match n with
		2 -> generar_fila reglas (cart (get 0 lst))
		| _ -> loop ((generar_fila reglas (cart (get 0 lst)))::lst) (n-1)
	in loop [primera_fila] (len-1)
;;
cyk (cadena_of_string "b b a b") g;;
generar_fila reglas (cart (get 0 lst))
(*
cyk (cadena_of_string "b b a b") g;;
*)

(generar_fila reglas (get 0 lst))::lst

[
	[Conjunto []];
	[Conjunto []; Conjunto []];
	[Conjunto []; Conjunto [No_terminal "S"; No_terminal "A"];Conjunto [No_terminal "S"; No_terminal "C"]];
	[Conjunto [No_terminal "B"]; Conjunto [No_terminal "B"];Conjunto [No_terminal "A"; No_terminal "C"]; Conjunto [No_terminal "B"]]
]




