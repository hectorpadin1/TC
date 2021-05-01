#load "talf.cma";;
open Auto;;
open Conj;;
open Ergo;;
open Graf;;

(*
let gic = Gic (
	Conjunto [No_terminal "S"; No_terminal "A"; No_terminal "B"],
	Conjunto [Terminal "a"; Terminal "b"; Terminal "c"],
	Conjunto [
		Regla_gic (No_terminal "S", [Terminal "a"; No_terminal "A"]);
		Regla_gic (
			No_terminal "A",
			[Terminal "a"; Terminal "b"; Terminal "c";
			No_terminal "A"]);
		Regla_gic (No_terminal "A", [Terminal "b"; No_terminal "B"]);
		Regla_gic (No_terminal "B",
			[Terminal "b"; Terminal "c"; No_terminal "B"]);
		Regla_gic (No_terminal "B", [])],
	No_terminal "S")

let gic = Gic (
	Conjunto [No_terminal "S"; No_terminal "A"; No_terminal "B"],
	Conjunto [Terminal "a"; Terminal "b"; Terminal "c"],
	Conjunto [
		Regla_gic (No_terminal "S", [No_terminal "A"]);
		Regla_gic (No_terminal "S", [No_terminal "B"]);
		Regla_gic (No_terminal "A", [Terminal "C"]);
		Regla_gic (No_terminal "B", []);
		Regla_gic (No_terminal "C", [])],
	No_terminal "S");;

*)

let es_fnc (Gic(no_terminales, terminales, reglas, destacado)) = 
	let rec loop = function
		[] -> true
		| (Regla_gic(not_terminal, lst))::tl -> match lst with
			[] -> loop tl
			| hd::tail ->
				if ((List.length tail) = 0) then
					loop tl 
				else false
	in loop (list_of_conjunto reglas)
;;

let es_fnc (Gic(no_terminales, terminales, reglas, destacado)) = 
	let rec loop = function
		(Regla_gic(not_terminal, lst))::tl -> match lst with
			[] -> loop tl
			| hd::[] -> loop tl
			| hd::tail -> match (hd,tail) with
				((No_terminal t1), [(No_terminal t2)]) -> loop tl
				| _ -> false
		| _ -> true
	in loop (list_of_conjunto reglas)
;;