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



(*EJERCICIO 2*)

let a0 = Af (
	Conjunto [Estado "0"; Estado "1"],
	Conjunto [Terminal "a"],
	Estado "0",
	Conjunto [Arco_af (Estado "0", Estado "1", Terminal "a")],
	Conjunto [Estado "1"]
);;

let a1 = Af (
	Conjunto [Estado "2"; Estado "3"],
	Conjunto [Terminal "b"],
	Estado "2",
	Conjunto [Arco_af (Estado "2", Estado "3", Terminal "b")],
	Conjunto [Estado "3"]
);;

dibuja_af (af_concat a0 a1);;
dibuja_af (af_union a0 a1);;

#load "talf.cma";;
open Auto;;
open Conj;;
open Ergo;;
open Graf;;

let mix_states s1 s2 =
	let rec loop i cc = 
		if (i=0) then
			cc
		else
			loop (i-1) (agregar (Estado (string_of_int i)) cc)
	in loop (cardinal s1 + cardinal s2) (Conjunto [])
;;

let new_state (Conjunto simbolos) =
    let nombres = List.map (function Estado s -> s) simbolos in
   		let rec aux m =
        	if List.mem (string_of_int m) nombres then
            	aux (m+1)
         	else
            	m
    	in aux (cardinal (Conjunto simbolos))
;;

let fst_state cc = match cc with
	Conjunto [] -> raise(Not_found)
	| Conjunto ((state)::tl) -> state
;;

(*let union_epsilon arcs state i_states1 i_states2 = match (i_states1, i_states2) with*)

let af_union af1 af2 = match (af1, af2) with
	(Af(states1,simb1,i_state1,arcs1,f_states1), Af(states2,simb2,i_state2,arcs2,f_states2)) ->
		let states = union states1 states2
		and st = Estado (string_of_int (new_state (union states1 states2)))
		in Af(
			agregar st states,
			union simb1 simb2,
			st,
			agregar (Arco_af(st, i_state2, Terminal "")) (agregar (Arco_af(st, i_state1, Terminal "")) (union arcs1 arcs2)),
			union f_states1 f_states2 
		)
;;

let get_final_to_ini f_states1 i_state2 = 
	let rec loop f_states i_state cc = match (f_states) with
		Conjunto [] -> cc
		| Conjunto (f_state::tl) -> loop (Conjunto (tl)) i_state (agregar (Arco_af(f_state,i_state, Terminal "")) cc)
	in loop f_states1 i_state2 (Conjunto [])
;;

let af_concat af1 af2 = match (af1, af2) with
	(Af(states1,simb1,i_state1,arcs1,f_states1), Af(states2,simb2,i_state2,arcs2,f_states2)) ->
		let states = (union states1 states2)
		in Af(
			states,
			union simb1 simb2,
			i_state1,
			union (get_final_to_ini f_states1 i_state2) (union arcs1 arcs2),
			f_states2 
		)
;;

let get_states af = match af with
	(Af(st,_,_,_,_)) -> cardinal st
;;

(*estoy en este*)
let af_of_er expression =
	let rec loop (Af(states,simb,i_state,arcs,f_states)) count = function
		[] -> Af(states,simb,i_state,arcs,agregar (Estado (string_of_int count)) f_states)
		| Vacio::tl -> Af(states,simb,i_state,arcs,f_states)
		| Constante (t)::tl ->
			if (t = Terminal "") then
				let af = Af(states, agregar t simb, i_state, arcs, f_states) in loop af (count) tl
			else
				let af = Af(
					Conjunto [Estado (string_of_int (count)); Estado (string_of_int (count+1))],
					agregar t simb,
					Estado (string_of_int (count)),
					Conjunto [Arco_af(Estado (string_of_int count), Estado (string_of_int (count+1)), t)],
					f_states
				)
				in loop af (count+1) tl
		| Union (er1, er2)::tl ->
			let af = loop (Af(states,simb,i_state,arcs,f_states)) (count) (tl@[er1])
			in af_union af (loop (Af(states,simb,i_state,arcs,f_states)) (get_states af) (tl@[er2]))
		| Concatenacion (er1, er2)::tl ->
			let af = loop (Af(states,simb,i_state,arcs,f_states)) (count) (tl@[er1])
			in af_concat af (loop (Af(states,simb,i_state,arcs,f_states)) (get_states af) (tl@[er2]))
		| Repeticion er::tl -> loop (Af(states,simb,i_state,arcs,f_states)) (count+1) (tl@[er])
	in loop (Af(Conjunto [Estado "0"], Conjunto [], Estado "0", Conjunto [], Conjunto [])) 0 [expression]
;;





(*
let vacio = af_of_er (Vacio);;
dibuja_af vacio;;
let a_epsilon = af_of_er (Constante (Terminal ""));;
dibuja_af a_epsilon;;
let a0 = af_of_er (Constante (Terminal "a"));;
dibuja_af a0;;
*)

(*a.be.be*)
let concat_compleja = Concatenacion (Concatenacion (Constante (Terminal "a"),(Constante (Terminal "be"))),(Constante (Terminal "be")));;
dibuja_af (af_of_er concat_compleja);;

let a2 = af_of_er (Union (Constante (Terminal "a"),(Constante (Terminal "be"))));;
dibuja_af a2;;

let a3 = af_of_er (Concatenacion (Constante (Terminal "a"),(Union (Constante (Terminal "ce"),(Constante (Terminal "be"))))));;
dibuja_af a3;;

let rep = Repeticion (Constante (Terminal "a"));;

let expr1 = Concatenacion (Constante (Terminal "a"),Repeticion (Union (Constante (Terminal "be"),Constante (Terminal "ce"))));;

let af_vacio = Af(Conjunto [Estado "0"], Conjunto [], Estado "0", Conjunto [], Conjunto []);;


let af_of_er expression =
	let rec loop = function
		[] -> Printf.sprintf "sacabo"
		| Vacio::tl -> Printf.sprintf "vasio\n"^loop tl
		| Constante (t)::tl -> Printf.sprintf "konstante\n"^loop tl
		| Union (er1, er2)::tl -> Printf.sprintf "uuuunion\n"^loop (tl@[er1;er2])
		| Concatenacion (er1, er2)::tl -> Printf.sprintf "concak\n"^loop (tl@[er1;er2])
		| Repeticion er::tl -> Printf.sprintf "repe\n"^loop (tl@[er])
	in loop [expression]
;;

