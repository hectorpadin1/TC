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

let mix_states s1 s2 =
	let rec loop s1 s2 cc = match (s1,s2) with
		(Conjunto ((Estado str1)::tl1), Conjunto ((Estado str2)::tl2)) -> loop (Conjunto tl1) (Conjunto tl2) (agregar (Estado ("1"^str2)) (agregar (Estado ("2"^str1)) cc))
		| _ -> cc
	in loop s1 s2 (Conjunto [])
;;

let st_state cc = match cc with
	Conjunto [] -> raise(Not_found)
	| Conjunto ((state)::tl) -> state
;;

let union af1 af2 = match (af1, af2) with
	(Af(states1,simb1,i_states1,arcs1,f_states1), Af(states2,simb2,i_states2,arcs2,f_states2)) ->
		Af (
			agregar (Estado "0") (mix_states states1, states2),
			agregar (Terminal "") (union simb1 simb2),
			Conjunto [(Estado "0")],
			agregar (Arco_af (Estado "0", (st_state states1), Terminal "")) (agregar (Arco_af (Estado "0", (st_state states2), Terminal "")) )


		Arco_af (Estado "1", Estado "1", Terminal "b");
		)
;;

let af_of_er expression = 
	let rec loop (Af(states,simb,i_states,arcs,f_states)) count = function
		Vacio -> (Af(states,simb,i_states,arcs,f_states))
		| Constante (t) -> 
			if (t = Terminal "") then
				loop (Af(Conjunto [Estado "0"], Conjunto [], Estado "0", Conjunto [], Conjunto [Estado "0"])) (count+1) (Vacio)
			else
				let af = Af(
					agregar (Estado (string_of_int (count+1))) states,
					agregar t simb,
					i_states,
					agregar (Arco_af(Estado (string_of_int count), Estado (string_of_int (count+1)), t)) arcs,
					agregar (Estado (string_of_int (count+1))) f_states)
				in loop af (count+1) (Vacio)
		| Union (er1, er2) -> (Af(states,simb,i_states,arcs,f_states))
		| Concatenacion (er1, er2) -> (Af(states,simb,i_states,arcs,f_states))
		| Repeticion er -> (Af(states,simb,i_states,arcs,f_states))
	in loop (Af(Conjunto [Estado "0"], Conjunto [], Estado "0", Conjunto [], Conjunto [])) 0 expression
;;

(*
let vacio = af_of_er (Vacio);;
dibuja_af vacio;;
let a_epsilon = af_of_er (Constante (Terminal ""));;
dibuja_af a_epsilon;;
let a0 = af_of_er (Constante (Terminal "a"));;
dibuja_af a0;;
*)





(*

let af_of_er expression = match expression with
(*	Vacio -> af_of_string ("0; ; 0; 1; 0 0 epsilon;")*)
	Vacio -> Af(
			Conjunto [Estado "0"],
			Conjunto [],
			Estado "0",
			Conjunto [],
			Conjunto []
		)
	(*| Constante (Terminal t) -> af_of_string ("0 1; "^t^"; 0; 1; 0 1 "^t^";")*)
	| Constante (Terminal t) ->
		if t = "" then
			Af(
				Conjunto [Estado "0"],
				Conjunto [],
				Estado "0",
				Conjunto [],
				Conjunto [Estado "0"]
			)
		else
			Af(
				Conjunto [Estado "0"; Estado "1"],
				Conjunto [Terminal t],
				Estado "0",
				Conjunto [Arco_af(Estado "0", Estado "1", Terminal t)],
				Conjunto [Estado "1"]
			)
	| _ -> 

*)