#load "talf.cma";;
open Auto;;
open Conj;;
open Ergo;;
open Graf;;

(*
Gic (
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
*)

let rec print = function
	[] -> ". \n "
	| (Terminal(str)::tl) -> str^(print tl)
;;

let es_fnc (Gic(no_terminales, terminales, reglas, destacado)) = 
	let rec loop = function
		[] -> ""
		| (Regla_gic(No_terminal(str), lst))::tl -> str^" -> "^(print lst)
	in loop (list_of_conjunto reglas)
;;