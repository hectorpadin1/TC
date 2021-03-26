#load "talf.cma";;
open Auto;;
open Conj;;
open Ergo;;
open Graf;;

(*
let afne = af_of_string "0 1 2 3; a b c; 0; 1 3; 0 1 a; 1 1 b; 1 2 a; 2 0 epsilon; 2 3 epsilon; 2 3 c;";;
*)
let afne = Af (
	Conjunto [Estado "0"; Estado "1"; Estado "2"; Estado "3"],
	Conjunto [Terminal "a"; Terminal "b"; Terminal "c"],
	Estado "0",
	Conjunto [
		Arco_af (Estado "0", Estado "1", Terminal "a");
		Arco_af (Estado "1", Estado "1", Terminal "b");
		Arco_af (Estado "1", Estado "2", Terminal "a");
		Arco_af (Estado "2", Estado "0", Terminal "");
		Arco_af (Estado "2", Estado "3", Terminal "");
		Arco_af (Estado "2", Estado "3", Terminal "c")
	],
	Conjunto [Estado "1"; Estado "3"]
);;

(*
let afn = af_of_string "";;
*)
let afn_vacio = Af (
	Conjunto [Estado "0"; Estado "1"; Estado "2"; Estado "3"],
	Conjunto [Terminal "a"; Terminal "b"; Terminal "c"],
	Estado "0",
	Conjunto [],
	Conjunto [Estado "1"; Estado "3"]
);;

(*
let afn = af_of_string "0 1 2 3; a b c; 0; 1 3; 0 1 a; 1 1 b; 1 2 a; 2 3 c;";;
*)
let afn = Af (
	Conjunto [Estado "0"; Estado "1"; Estado "2"; Estado "3"],
	Conjunto [Terminal "a"; Terminal "b"; Terminal "c"],
	Estado "0",
	Conjunto [
		Arco_af (Estado "0", Estado "1", Terminal "a");
		Arco_af (Estado "1", Estado "1", Terminal "b");
		Arco_af (Estado "1", Estado "2", Terminal "a");
		Arco_af (Estado "1", Estado "3", Terminal "b");
		Arco_af (Estado "2", Estado "3", Terminal "c")
	],
	Conjunto [Estado "1"; Estado "3"]
);;


let afd = Af (
	Conjunto [Estado "0"; Estado "1"; Estado "2"; Estado "3"],
	Conjunto [Terminal "a"; Terminal "b"; Terminal "c"],
	Estado "0",
	Conjunto [
		Arco_af (Estado "0", Estado "1", Terminal "a");
		Arco_af (Estado "1", Estado "1", Terminal "b");
		Arco_af (Estado "2", Estado "3", Terminal "c")
	],
	Conjunto [Estado "1"; Estado "3"]
);;


let es_afne (Af (_,_,_,arcs,_)) =
	let rec loop = function
		Conjunto ((Arco_af(_,_,terminal))::tl) ->
			if terminal = (Terminal "") then
				true
			else
				loop (Conjunto tl)
		| Conjunto _ -> false
	in loop arcs
;;

let es_afn (Af (_,_,_,arcs,_)) =
	let rec loop cc boolean = function
		Conjunto ((Arco_af(s1,_,terminal))::tl) ->
			if terminal = (Terminal "") then
				false
			else if pertenece (s1,terminal) cc then
				loop (agregar (s1,terminal) cc) true (Conjunto(tl))
			else
				loop (agregar (s1,terminal) cc) boolean (Conjunto(tl))
		| Conjunto _ -> boolean
	in loop (Conjunto []) false arcs
;;

let es_afd (Af (_,_,_,arcs,_)) =
	let rec loop cc = function
		Conjunto ((Arco_af(s1,_,terminal))::tl) ->
			if (terminal = (Terminal "") || pertenece (s1,terminal) cc) then
				false
			else
				loop (agregar (s1,terminal) cc) (Conjunto(tl))
		| Conjunto _ -> true
	in loop (Conjunto []) arcs
;;

let af_of_er expression = match expression with
	Vacio -> af_of_string ("0; ; 0; 1; 0 0 epsilon;")
	| Constante (Terminal t) -> af_of_string ("0 1; "^t^"; 0; 1; 0 1 "^t^";")
	| _ -> raise(Not_found)
;;

(*
af_of_er (Vacio);;
af_of_er (Constante (Terminal ""));;
af_of_er (Constante (Terminal "aaa"));;
*)