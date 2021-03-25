#load "talf.cma";;
open Auto;;
open Conj;;
open Ergo;;
open Graf;;

let string_of_estado (Estado e) =
	e;;


let string_of_simbolo = function
	Terminal s -> s
	| No_terminal s -> s;;

let rec printing (Conjunto cadena) =
	match Conjunto cadena with
		Conjunto [] ->print_string "";
		| Conjunto(a::l) -> print_string (string_of_estado a);
			printing (Conjunto l);
;;

let traza_af cadena (Af (_, _, inicial, _, finales) as a) =
	let rec aux = function
	(Conjunto [], _) -> false
	| (actuales, []) ->
		print_string "(";
		printing actuales;
		print_string ",";
		print_string " ";
		print_endline ")";
			not (es_vacio (interseccion actuales finales))
	| (actuales, simbolo :: t) ->
		print_string "(";
		printing actuales;
		print_string ",";
		print_string (string_of_simbolo simbolo);
		print_string " ";
		print_string (string_of_cadena t);
		print_endline ")";
			aux ((epsilon_cierre (avanza simbolo actuales a) a), t);
	in
		aux ((epsilon_cierre (Conjunto [inicial]) a), cadena)
;;

let rec at_least_1 x c = match x with
Conjunto([]) -> false
| Conjunto(e1::en) -> pertenece e1 c || at_least_1 (Conjunto(en)) c;;

let rec combine l = match l with
	Conjunto(Estado(e1)::[]) -> e1
	| Conjunto(Estado(e1)::en) -> e1 ^ (combine (Conjunto(en)));;

let first x = match x with
	(a,b,c) -> a;;

let second x = match x with
	(a,b,c) -> b;;
let third x = match x with
	(a,b,c) -> c;;

let is_afn (Af (states,input,e_ini,fun_trans,e_fin)) =
	let rec aux c arcs = match arcs with
		Conjunto([]) -> false
		| Conjunto((Arco_af(e1,e2,a))::en) -> if pertenece ((e1,a)) c
												then true
												else aux (agregar ((e1,a)) c) (Conjunto(en))
	in aux (Conjunto([])) fun_trans;;

let create_arcs ces (Af (states,input,e_ini,fun_trans,e_fin) as a) =
	let rec aux acc ft = match ft with
	Conjunto([]) -> acc
	| Conjunto(Arco_af(i,f,l)::b) -> if pertenece i ces
										then aux (agregar (Arco_af(Estado(combine ces),f,l)) acc) (Conjunto(b))
										else aux acc (Conjunto(b))
	in aux (Conjunto([])) fun_trans;;

let rec afd_of_afn (Af (states,input,e_ini,fun_trans,e_fin) as a) =
	let rec aux e_list ei ef arc = match e_list with
	[] -> (ei,ef,arc)
	| Estado(e1)::en -> let rec simb letters ei2 ef2 arc2 = match letters with
		[] -> (ei2,ef2,arc2)
		| Terminal(e1b)::enb -> let result = (avanza (Terminal(e1b)) (Conjunto((Estado(e1)::[]))) a) in
			if cardinal result == 1 then
				if (pertenece (List.hd (list_of_conjunto result)) e_fin) then
					simb enb (agregar (List.hd (list_of_conjunto result)) ei2) (agregar (List.hd (list_of_conjunto result)) ef2) (agregar (Arco_af(Estado(e1),(List.hd (list_of_conjunto result)),Terminal(e1b))) arc2)
				else simb enb (agregar (List.hd (list_of_conjunto result)) ei2) (ef2) (agregar (Arco_af(Estado(e1),(List.hd (list_of_conjunto result)),Terminal(e1b))) arc2)
			else if (at_least_1 result e_fin) then
				simb enb (agregar (Estado(combine result)) ei2) (agregar (Estado(combine result)) ef2) (union (agregar (Arco_af(Estado(e1),Estado(combine result) ,Terminal(e1b))) arc2) (create_arcs result a))
			else if (cardinal result)<0 then
				simb enb (agregar (Estado(combine result)) ei2) (ef2) (union (agregar (Arco_af(Estado(e1),Estado(combine result) ,Terminal(e1b))) arc2) (create_arcs result a))	
			else simb enb (ei2) (ef2) (arc2)
	in let simb_result = simb (list_of_conjunto input) ei ef arc in aux en (first simb_result) (second simb_result) (third simb_result) in let aux_result = aux (list_of_conjunto states) (Conjunto(e_ini::[])) (Conjunto([])) (Conjunto([])) in let afd = Af (first aux_result,input,e_ini,third aux_result,second aux_result) in if is_afn afd then afd_of_afn afd else afd;;