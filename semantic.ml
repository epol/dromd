(*
 * semantic.ml
 * This file is part of dromd
 *
 * Copyright (C) 2013 - Enrico Polesel and Alessadro Achille
 *
 * dromd is free software; you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation; either version 2 of the License, or
 * (at your option) any later version.
 *
 * dromd is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with dromd. If not, see <http://www.gnu.org/licenses/>
 * or write to the Free Software Foundation, Inc., 51 Franklin Street, 
 * Fifth Floor, Boston, MA 02110-1301 USA.
 *)

(* semantica *)

#use "syntax.ml"

type loc = int;; (* indirizzi di memoria *)

type storable =
	| SInt of int
	| SPointer of loc
	| SPair of storable * storable
	| SFunc of stm * vname * environment
and denotabile = 
	| DInt of int
	| DPointer of loc
	| DPair of storable * storable
	| DFunc of stm * vname * environment
	| Address of loc
	| List of llist
	| Array of int * loc
and llist =
	| Empty
	| LList of int * llist
and expressible =
	| EInt of int
	| EBool of bool
and environment = vname -> denotabile
;;

type storage = loc -> storable
;;


let storable_to_int (s:storable) = match s with
	| SInt i -> i
	| SPointer p -> p
	| _ -> raise (Failure "Wrong data type in conversion")
;;

let denotabile_to_int (d:denotabile) = match d with
	| DInt i -> i 
	| DPointer p -> p
	| _ -> raise (Failure "Wrong data type in conversion")
;;

let expressibile_to_int (e:expressible) = match e with
	| EInt i -> i
	| _ -> raise (Failure "Wrong data type in conversion")

let rec a_sem (s:a_exp) (env:environment) (sto:storage) = match s with
	| Avar v ->
		(
			match env v with 
				| DInt i -> EInt i
				| DPointer p -> EInt p
				| Address l -> 
					(
						match sto l with 
							| SInt i -> EInt i
							| SPointer p -> EInt p
							| _ -> raise (Failure "Not int variable in a arithmetic expression")
					)
				| _ -> raise (Failure "Not int constant in a arithmetic expression")
		)
	| Anum n -> EInt n
	| Aplus ( a1,a2) -> EInt (expressibile_to_int ( a_sem a1 env sto ) + expressibile_to_int ( a_sem a2 env sto ))
	| Aminus ( a1,a2) -> EInt (expressibile_to_int ( a_sem a1 env sto ) - expressibile_to_int ( a_sem a2 env sto ))
	| Aneg a1 -> EInt ( - expressibile_to_int ( a_sem a1 env sto ))
	| Aprod ( a1,a2) -> EInt (expressibile_to_int ( a_sem a1 env sto ) * expressibile_to_int ( a_sem a2 env sto ))
	| Adiv ( a1,a2) -> EInt (expressibile_to_int ( a_sem a1 env sto ) / expressibile_to_int ( a_sem a2 env sto ))
	| Apair2num p1 -> 
		(
			match pair_sem p1 env sto with
				| EInt n -> EInt n
				| _ -> raise (Failure "I can't do arithmetic with pairs!")
		)

	| AvarArray (arrayName , indexExp) -> 
		(
			match a_sem indexExp env sto with
				|	EInt index ->
					( match env arrayName with
							|	Array ( arrayLength , arrayLocation ) ->
								if index < arrayLength then
									(
										match sto ( arrayLocation + index) with
											| SInt i -> EInt i
											| SPointer p -> EInt p
											| _ -> raise (Failure "Error in seeking array (or not implemented yet)")
									)
								else 
									raise (Failure "Segmentation Fault!")
							| _ -> raise (Failure "Is that an array?")
					)
				|	_ -> raise (Failure "Invalid array index expression")
		)


(* TODO: finish the a_exp semantic			

	| Apnt2val v -> (match sto (env v) with
    		| ( Pointer p , t ) -> sto_to_result ( sto p )
    		| _ -> raise (Failure "Not a pointer")
    	)
	| Avar2pnt v -> Pointer (env v)
	| Aarr2pnt v -> 
		(
			match sto_to_result (sto (env v)) with 
				| Array ( p , n ) -> Pointer p
				| _ -> raise ( Failure ("This is not an array"))
		) *)
	| _ -> raise (Failure "Invalid a-exp")

and pair_sem (p:pair_exp) (env:environment) (sto:storage) = match p with
	| Pvar v -> sto_to_result (sto (env v))
	| Pnumnum (a1, a2) -> Pair ( a_sem a1 env sto, a_sem a2 env sto)
	| Ppairnum (p1 , a1) -> Pair ( pair_sem p1 env sto, a_sem a1 env sto)
	| Pnumpair (a1 , p1) -> Pair ( a_sem a1 env sto, pair_sem p1 env sto)
	| Ppairpair (p1 , p2) -> Pair ( pair_sem p1 env sto, pair_sem p2 env sto)
	| Pproj1 p1 -> 
		(
			match pair_sem p1 env sto with
				| Pair (r1, r2) -> r1
				| _ -> raise (Failure "I can only project a couple!")
		)
	| Pproj2 p1 -> 
		(
			match pair_sem p1 env sto with
				| Pair (r1, r2) -> r2
				| _ -> raise (Failure "I can only project a couple!")
		)
;;

(* questa è una riga di commento *)
(* lists semantic *)

let update_storage (sto:storage) (n:loc) (new_value:result) x =
	if x=n then
		new_value , Var
	else
		sto x
;;

let rec list_concat (ptr1:loc) (ptr2:loc) (sto:storage) = 
	match ptr1 with
		| 0 -> (sto,ptr2);
		| node_ptr ->
			(match sto node_ptr with
				| (Node (r, next_node), Var) ->
					let (new_sto , next_concat)=list_concat next_node ptr2 sto in
						(update_storage new_sto node_ptr (Node(r,next_concat)), node_ptr)
				| _ -> raise (Failure "List does not point to a node.")
			)

let rec list_sem (l:list_exp) (env:environment) (sto:storage) = match l with
	| Lvar v ->
		(match sto (env v) with
			| List l , Var -> List l 
			| _ -> raise (Failure "Variable in list_exp is not a list.")
		)
	| Lempty -> List 0
(*	| Lconcat (lexp1, lexp2) ->
		let list1=list_sem lexp1 env sto and list2=list_sem lexp2 env sto in
			(match (list1, list2) with
				| (List list_ptr1, List list_ptr2) ->
					List (list_concat list_ptr1 list_ptr2 sto)
			)*)
	| _ -> raise (Failure "Funzione per liste non ancora implementata.")
;;

let rec b_sem (b:b_exp) (env:environment) (sto:storage) = match b with
  | Bvar v -> sto_to_result (sto (env v))
  | Btrue -> Bool true
  | Bfalse -> Bool false
  | Bequal (a1,a2) -> Bool (to_int(a_sem a1 env sto) = to_int(a_sem a2 env sto)) 
  | Bleq (a1,a2) -> Bool (to_int(a_sem a1 env sto) <= to_int(a_sem a2 env sto))
  | Bnot b1 -> Bool ( not( to_bool (b_sem b1 env sto)))
  | Band (b1,b2) -> Bool ( (to_bool ( b_sem b1 env sto )) && (to_bool (b_sem b2 env sto)))
  (*| _ -> raise (Failure "Invalid b-exp")*)
;;

let rec print_result r = match r with
	| Int n ->
		Printf.printf "%d" n
	| Pair (e1,e2) ->
		Printf.printf "(";
		print_result e1;
		Printf.printf ",";		
		print_result e2;
		Printf.printf ")"
	| Bool b ->
		Printf.printf "%b" b
	| Pointer p ->
		Printf.printf "%d" p
	|	Func (s , v, e) ->
		Printf.printf "This is a function\n"
	| Array ( address , length ) ->
		Printf.printf "Array %d %d" address length
	| _ -> raise (Failure "Cannot print a list or a node")
;;

let generic_assign (location:loc) (value:result) (env:environment) (sto:storage) = 
	match sto_to_tag ( sto location ) with
	| Var ->
		(
			env,
			(fun (n:loc) ->
				if n = location then
					value , Var
				else
					sto (n)
			)
		)
	|	Const -> raise (Failure "You can't modify a const")
;;

let rec sem (s:stm) (env:environment) (sto:storage) = match s with
	| Slet (t,v,a) ->
	  (
	  	let insertPosition = to_int ( sto_to_result (sto (-1) )) in 
				(fun (v1:vname) ->
					if v1 = v then
						insertPosition
					else
						env(v1)
				),
				(fun (n:loc) ->
					if n = insertPosition then
						a_sem a env sto , t
					else if n = -1 then
						(Int (insertPosition + 1)  , Var)
					else
						sto (n)
				)
	  )
	| Sskip -> (env, sto)
	| Sassign (v,a) -> generic_assign  (env v) (a_sem a env sto) env sto
	| SassignPnt (v,a) -> 
		(
			match sto (env v) with
				| (Pointer p , t ) -> generic_assign p (a_sem a env sto) env sto
				| _ -> raise (Failure "This is not a pointer")		
		)
	| Ssequence (s1,s2) ->
		let (env1, sto1) = sem s1 env sto in
			sem s2 env1 sto1
	| Sifthenelse (b,s1,s2) ->
		let b_value = to_bool (b_sem b env sto) in
			if b_value then
				sem s1 env sto
			else
				sem s2 env sto
	| Swhile (b,s1) ->
		let b_value = to_bool (b_sem b env sto) in
			if b_value then
				let (env1,sto1) = sem s1 env sto in
					sem s env1 sto1
			else
				(env,sto)
	| Sprint a ->
		let a_value=a_sem a env sto in
			print_result a_value;
			Printf.printf "\n";
			(env, sto)
	| Sblock s1 ->
		let (env1,sto1) = sem s1 env sto in
			(env,sto1)
	| Sfun (f , p , s1) ->
		let insertPosition = to_int ( sto_to_result (sto (-1) )) in 
			(
				(fun (v1:vname) ->
					if v1 =f then 
						insertPosition
					else
						env(v1)
				),
				(fun (n:loc) ->
					if n = insertPosition then 
						Func ( s1 , p, env) , Var 
					else if n = -1 then
							Int ( insertPosition +1 ) , Var
						else
							sto(n)
				)
			)
	|	Scall ( f , a) -> 
		(
			match sto_to_result (sto (env f)) with
				| Func ( s1, v , envf ) ->
					let ( env1 , sto1 )=
						let insertPosition = to_int ( sto_to_result (sto (-1) )) in 
							( 
								(
									fun (v1:vname) ->
										if v1=v then
											insertPosition
										else
											envf(v1)
								), 
								(
									fun ( n:loc) ->
										if n = insertPosition then
											a_sem a env sto , Var
										else if n = -1 then 
												Int (insertPosition +1) , Var
											else
												sto(n)
									)
								) in
									let (env2, sto2) = sem s1 env1 sto1 in
										(env , sto2)
				| _ -> raise (Failure "Call to an invalid function")
		)
	|	SletArray ( t , arrayName , arrayLengthExp , arrayInitialValueExp ) ->
		(
			match ( a_sem arrayLengthExp env sto , a_sem arrayInitialValueExp env sto ) with 
				|	(Int arrayLength , Int arrayInitialValue ) ->
					let insertPosition = to_int ( sto_to_result (sto (-1) )) in
						(
							(fun (v:vname) ->
								if v = arrayName then 
									insertPosition
								else 
									env (v)
							),
							(fun (n:loc) ->
								if n=insertPosition then Array ( insertPosition +1 , arrayLength ) , t
								else if n> insertPosition && n <= insertPosition +arrayLength then Int arrayInitialValue , t
								else if n = -1 then Int (insertPosition + 1 + arrayLength) , Var
								else sto(n)
							)
						)
				| _ -> raise (Failure "Invalid array initialization") 
		)
	| SassignArray (arrayName , indexExp, valueExp) ->
		(
			match sto_to_tag ( sto (env arrayName)) with
				| Var ->	
					(
						match (a_sem indexExp env sto , sto_to_result (sto ( env arrayName ) )) with 
							|	(Int index , Array (firstElement ,  arrayLength ))->
								if index < arrayLength then
									(
										env,
										(fun (n:loc) ->
											if n = firstElement + index  then
												a_sem valueExp env sto , Var
											else
												sto (n)
										)
									)
								else 
									raise (Failure "Segmentation Fault")
							| _ -> raise (Failure "Invalid array access") 
					)
				| Const -> raise (Failure "You can't modify a const")
		)
		| SletList (t, listName, listInitialValueExp) ->
				(
					let insertPosition = to_int ( sto_to_result (sto (-1) )) in 
						(fun (v1:vname) ->
							if v1 = listName then
								insertPosition
							else
								env(v1)
						),
						(fun (n:loc) ->
							if n = insertPosition then
								(list_sem listInitialValueExp env sto, t)
							else if n = -1 then
								(Int (insertPosition + 1)  , Var)
							else
								sto (n)
						)
				)
(*	| _ -> raise (Failure "Semantic not implemented yet")   *)
;;


















