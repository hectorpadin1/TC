(*
* Práctica 0.
* Héctor Padín Torrente
* Grupo 3.3 (Computación).
*
*)


(*
*
* Exercise 1.
*
* Define function mapdoble.
* Applies a function to the odd elements of a list, and another 
* to the even elements.
*
*)


let rec mapdoble f1 f2 = function
	| [] -> []
	| hd::tl -> (f1 hd)::(mapdoble f2 f1 tl) 
;;
(*- : ('a -> 'b) -> ('a -> 'b) -> 'a list -> 'b list = <fun>*)
(*
mapdoble (function x -> x) (function x -> -x) [1;1;1;1;1];;
mapdoble (function x -> x) (function x -> 2*x) [1;1;1;1;1;1];;
mapdoble (function x -> x) (function x -> 2*x) [1];;
mapdoble (function x -> x) (function x -> 2*x) [];;
*)

(*

mapdoble (function x -> x*2) (function x -> "x") [1;2;3;4;5];;
Nos salta un error de tipado porque como vemos en la definición del tipo de
mapdoble, ambas funciones son de 'a -> 'b, por lo tanto no podemos tener una
función que sea int -> int y otra que sea int -> string.

let y = function x -> 5 in mapdoble y;;
- : ('_weak1 -> int) -> '_weak1 list -> int list = <fun>
El tipo '_weak1 indica que el compilador no pudo inferir el tipo de la 
variable y lo indica como un "tipo desconocido". Lo que quiere decir el 
compilador es que el tipo debería de ser monomórfico, pero no puede inferir
su tipo todavía y lo hará en tiempo de ejecución, cuadno nosotros le 
asignemos algún valor.


*)



(*
*
* Exercise 2.
*
*
*)


let rec primero_que_cumple f = function
	| [] -> raise(Not_found)
	| hd::tl -> if (f hd) then hd else primero_que_cumple f tl
;;
(*- : ('a -> bool) -> 'a list -> 'a = <fun>*)
(*
primero_que_cumple (function x -> x>0) [-1;0;1;2];;
primero_que_cumple (function x -> x>0) [];; # not found!!
primero_que_cumple (function x -> x>10) [-1;0;1;2;11];;
*)

let existe f list =
	try f (primero_que_cumple f list)
	with Not_found -> false
;;
(*- : ('a -> bool) -> 'a list -> bool = <fun>*)
(*
existe (function x -> x>0) [-1;0;1;2];;
existe (function x -> x>0) [];;
existe (function x -> x>10) [-1;0;1;2;11];;
existe (function x -> x>10) [-1;0;1;2;10];;
*)

let rec asociado list key =
	snd (primero_que_cumple (function (a,b) -> a = key) list)
;;
(*- : ('a * 'b) list -> 'a -> 'b = <fun>*)
(*
asociado [(1,false);(2,true);(3,false)] 2;;
asociado [] 2;;
asociado [(1,"uno");(2,"dos");(3,"tres");(4,"cuatro")] 3;;
*)




(*
*
* Ejercicio 3.
*
*
*)


type 'a arbol_binario =
	Vacio
	| Nodo of 'a * 'a arbol_binario * 'a arbol_binario;;

(*let t = Nodo(3,Nodo(2,Vacio,Vacio),Nodo(5,Nodo(4,Vacio,Vacio),Nodo(1,Vacio,Vacio)));;*)


let rec in_orden = function
    Vacio -> []
    | Nodo (r,i,d) -> in_orden i @ r::in_orden d
;;
(*
in_orden t;;
- : int list = [2; 3; 4; 5; 1]
*)

let rec pre_orden = function
    Vacio -> []
    | Nodo (r,i,d) -> r::pre_orden i @ pre_orden d
;;
(*
pre_orden t;;
- : int list = [3; 2; 5; 4; 1]
*)

let rec post_orden = function
    Vacio -> []
    | Nodo (r,i,d) -> post_orden i @ post_orden d @ [r]
;;
(*
post_orden t;;
- : int list = [2; 4; 1; 5; 3]
*)

let anchura tree = 
	let rec loop l = function
		| [] -> List.rev l
		| Vacio::t -> loop l t
		| Nodo(x,Vacio,Vacio)::t -> loop (x::l) t
		| Nodo(x,h1,h2)::t -> loop (x::l) (t@[h1;h2])
	in loop [] [tree]
;;
(*
anchura t;;
- : int list = [3; 2; 5; 4; 1]
*)




(*
*
*
* Ejercicio 4.
*
*
*)

type 'a conjunto = Conjunto of 'a list;;


(*
	Here i defined some common functions over lists to avoid repeating code 
	and make the functions over sets look cleaner and can be better understood.
*)

(*
	Deletes the 1st occurrence of a element in a list (use only validated sets).

	@args:
		element: 'a
		list: 'a list
	@return: 'a list
*)
let rec del element = function
	[] -> []
	| h::tl -> if h = element then
					tl
				else h::(del element tl)
;;

(*
	Function to append two lists.

	@args:
		l1: 'a list
		l2: 'a list
	@return: 'a list
*)
let append l1 l2 =
	let rec loop acc l1 l2 = match l1, l2 with
	    | [], [] -> List.rev acc
	    | [], hd::tl -> loop (hd::acc) [] tl
	    | hd::tl, l -> loop (hd::acc) tl l
    in loop [] l1 l2
;;

(*
	Function to check if a element is in a list.

	@args:
		e: 'a 
		list: 'a list
	@return: bool
*)
let rec mem e = function
	| [] -> false
	| hd::tl when hd = e -> true
	| _::tl -> mem e tl
;;

(*
	Function that checks if the 1st list is inside of l2

	@args:
		l1: 'a list
		l2: 'a list
	@return: bool
*)
let rec contenida lst1 lst2 = match lst1 with
	| [] -> true
	| hd::tl ->
			if mem hd lst2 then
			   	contenida tl lst2
			else
			   	false
;;


(*
	Starts functions over sets.
*)


(*
	Function that checks if an element belongs to a set.

	@args:
		a: 'a
		conjunto: 'a conjunto
	@return: bool
*)
let rec pertenece a = function
	Conjunto [] -> false
	| Conjunto (hd::tl) -> if hd = a then true else pertenece a (Conjunto tl)
;;
(*- : 'a -> 'a conjunto -> bool = <fun>*)
(*
pertenece 1 (Conjunto [1;2;3]);;
pertenece 1 (Conjunto [2;2;3]);;
pertenece 1 (Conjunto []);;
pertenece [1;2] (Conjunto [[2;3];[1;2];[3;4]]);;
*)


(*
	Function that adds an element to a set.

	@args:
		a: 'a
		conjunto: 'a conjunto
	@return: 'a conjunto
*)
let agregar a conjunto = 
	if (pertenece a conjunto) then
		conjunto
	else match conjunto with
		Conjunto l -> Conjunto (a::l)
;;
(*- : 'a -> 'a conjunto -> 'a conjunto = <fun>*)
(*
agregar 1 (Conjunto []);;
agregar 1 (Conjunto [1;2;3]);;
*)


(*
	Function that creates a valid set from a list.

	@args:
		l: 'a list
	@return: 'a conjunto
*)
let conjunto_of_list l =
	let rec loop conjunto = function
		| [] -> conjunto
		| hd::tl -> loop (agregar hd conjunto) tl
	in loop (Conjunto []) l
;;
(*val conjunto_of_list : 'a list -> 'a conjunto = <fun>*)
(*
conjunto_of_list [];;
conjunto_of_list [1;2;3];;
conjunto_of_list [1;1;2;3;4;3;2;5;6;7;1;6;2;8];;
*)



(*
	Function that deletes a element from a set.

	@args:
		elemento: 'a
		conjunto: 'a conjunto
	@return: 'a conjunto
*)
let suprimir elemento = function
	Conjunto l -> Conjunto (del elemento l)
;;
(*- : 'a -> 'a conjunto -> 'a conjunto = <fun>*)
(*
suprimir 1 (Conjunto []);;
suprimir 1 (Conjunto [3;4;5;1;6]);;
suprimir 1 (Conjunto [4;5;3;5;9]);;
suprimir 1 (Conjunto [4;5;3;1;10;01;5;9]);;
*)



(*
	Function that returns the cardinal of a list.

	@args:
		conjunto: 'a conjunto
	@return: int
*)
let cardinal = function
	Conjunto l -> List.length l
;;
(*- : 'a conjunto -> int = <fun>*)
(*
cardinal (Conjunto []);;
cardinal (Conjunto [1;2;3;4;5;6]);;
*)


(*
	Function that returns the union of two sets.

	@args:
		c1: 'a conjunto
		c2: 'a conjunto
	@return: 'a conjunto
*)
let union c1 c2 = match (c1,c2) with
	((Conjunto l1),(Conjunto l2)) -> conjunto_of_list (append l1 l2)
;;
(*- : 'a conjunto -> 'a conjunto -> 'a conjunto = <fun>*)
(*
union (Conjunto [1]) (Conjunto []);;
union (Conjunto [1;2;3;4]) (Conjunto [5;6;7;8]);;
union (Conjunto [1;2;3;4]) (Conjunto [3;4;5;6]);;
union (Conjunto [1;2;3;4]) (Conjunto [1;2;3;4]);;
*)


(*
	Function that intersects two sets.

	@args:
		c1: 'a conjunto
		c2: 'a conjunto
	@return: 'a conjunto
*)
let interseccion c1 c2 = match (c1,c2) with
	((Conjunto l1),(Conjunto l2)) -> 
		let rec intersect lst1 lst2 = match lst1 with
			| [] -> if (lst2 = []) then [] else intersect lst2 lst1
			| hd::tl ->
			    if mem hd lst2 then
			        hd::(intersect tl (del hd lst2))
			    else
			        intersect tl lst2
		in Conjunto (intersect l1 l2)
;;
(*- : 'a conjunto -> 'a conjunto -> 'a conjunto = <fun>*)
(*
interseccion (Conjunto [1;2;3;4]) (Conjunto [1;2;3;4]);;
interseccion (Conjunto [1;2;3;4]) (Conjunto [3;4;5;6]);;
interseccion (Conjunto []) (Conjunto []);;
interseccion (Conjunto [1;2;3;4]) (Conjunto [5;6;7;8]);;
*)


(*
	Function that returns the difference of two sets.

	@args:
		c1: 'a conjunto
		c2: 'a conjunto
	@return: 'a conjunto
*)
let diferencia c1 c2 = match (c1,c2) with
	((Conjunto l1),(Conjunto l2)) -> 
		let rec diff lst1 lst2 = match lst1 with
			| [] -> []
			| hd::tl ->
			    if mem hd lst2 then
			        diff tl lst2
			    else
			        hd::(diff tl lst2)
		in Conjunto (diff l1 l2)
;;
(*- : 'a conjunto -> 'a conjunto -> 'a conjunto = <fun>*)
(*
diferencia (Conjunto [1;2;3;4]) (Conjunto [3;4;5;6]);;
diferencia (Conjunto [1;2;3;4]) (Conjunto [5;6;7;8]);;
diferencia (Conjunto [1;2;3;4]) (Conjunto [1;2;3;4]);;
diferencia (Conjunto []) (Conjunto [1;2;3;4]);;
diferencia (Conjunto [1;2;3;4]) (Conjunto []);;
*)


(*
	Function that checks if the 1st set is a subset of the 2nd.

	@args:
		c1: 'a conjunto
		c2: 'a conjunto
	@return: bool
*)
let incluido c1 c2 = match (c1,c2) with
	((Conjunto l1),(Conjunto l2)) -> (List.length l2 > List.length l1) && contenida l1 l2
;;
(*- : 'a conjunto -> 'a conjunto -> bool = <fun>*)
(*
incluido (Conjunto [2;3]) (Conjunto [1;2;3;4]);;
incluido (Conjunto [1;2;3;4]) (Conjunto [3;4;5;6]);;
incluido (Conjunto [1;2;3;4]) (Conjunto [5;6;7;8]);;
incluido (Conjunto [1;2;3;4]) (Conjunto [1;2;3;4]);;
incluido (Conjunto []) (Conjunto []);;
*)


(*
	Function that checks if two sets are equals.

	@args:
		c1: 'a conjunto
		c2: 'a conjunto
	@return: bool
*)
let igual c1 c2 = match (c1,c2) with
	((Conjunto l1),(Conjunto l2)) -> (List.length l2 = List.length l1) && contenida l1 l2
;;
(*- : 'a conjunto -> 'a conjunto -> bool = <fun>*)
(*
igual (Conjunto [2;3]) (Conjunto [1;2;3;4]);;
igual (Conjunto [1;2;3;4]) (Conjunto [3;4;5;6]);;
igual (Conjunto [1;2;3;4]) (Conjunto [5;6;7;8]);;
igual (Conjunto [1;2;3;4]) (Conjunto [1;2;3;4]);;
igual (Conjunto []) (Conjunto []);;
*)


(*
	Function that returns the cartesian product of two sets.

	@args:
		c1: 'a conjunto
		c2: 'a conjunto
	@return: bool
*)
let producto_cartesiano c1 c2 = match (c1,c2) with
	((Conjunto l1),(Conjunto l2)) ->
	let rec loop2 element lst =
	  match lst with
		| [] -> []
		| hd::tl -> (element,hd)::(loop2 element tl)
	in
	let rec loop lst1 lst2 = match (lst1,lst2) with
		| ([],_) -> []
		| (_,[]) -> []
		| (hd1::tl,_) -> (loop2 hd1 lst2) @ (loop tl lst2)
	in Conjunto (loop l1 l2)
;;
(*- : 'a conjunto -> 'b conjunto -> ('a * 'b) conjunto = <fun>*)
(*
producto_cartesiano (Conjunto [1;2;3;4]) (Conjunto ['a';'b']);;
producto_cartesiano (Conjunto ['a';'b']) (Conjunto [1;2;3;4]);;
producto_cartesiano (Conjunto [1;2;3]) (Conjunto ['a';'b';'c';'d']);;
producto_cartesiano (Conjunto [1;2;3]) (Conjunto []);;
producto_cartesiano (Conjunto []) (Conjunto ['a';'b';'c';'d']);;
producto_cartesiano (Conjunto []) (Conjunto []);;
*)


(*
	Function that returns the elements of a set in a list.

	@args:
		conjunto: 'a conjunto
	@return: 'a list
*)
let list_of_conjunto conjunto = match conjunto with Conjunto l -> l;;
(*- : 'a conjunto -> 'a list = <fun>*)
(*
list_of_conjunto (Conjunto []);;
list_of_conjunto (Conjunto [1;2;3;4]);;
*)