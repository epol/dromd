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

type int_list = Empty | Conc of int * int_list;;

type storable =
	| SInt of int
	| SPointer of loc
	| SPair of storable * storable
	| SFunc of stm * vname * environment
and denotabile = 
	| DInt of int
	| DPointer of loc
	| DPair of denotabile * denotabile
	| DFunc of stm * vname * environment
	| L of loc
	| DList of int_list
	| DArray of int * loc
and expressible =
	| EInt of int
	| EBool of bool
	| EPair of expressible * expressible
	| EFunc of stm * vname * environment
	| EList of int_list;
and environment = vname -> denotabile
;;

type storage = int * (loc -> storable)
;;

let apply_storage sto:storage l:loc = (snd sto) l
;;

let update_storage (sto:storage) (l:loc) (d:storable) = 
	let updated_memory l1 = if (l1=l) then d else apply_storage sto l1 in
	(fst sto, updated_memory)
;;

let bind (env:environment) (v:vname) (d:denotable) = 
	let new_env v1 = if (v1=v) then d else env v1 in
	new_env
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
;;

let expressibile_to_bool (e:expressible) = match e with
	| EBool b -> b
	| _ -> raise (Failure "Wrong data type in conversion")
;;

let expressibile_to_function (e:expressible) = match e with
	| EFunction (s,v,en) -> (s,v,en)
	| _ -> raise (Failure "Wrong data type in conversion")
;;

let rec access_list_n (l1:int_list) (n:int) = match l1 with
	| Empty -> raise (Failure "The list isn't so long")
	| Conc ( e , l2 ) -> if n=0 then e else (access_list_n l2 (n - 1) )
;;

let rec denotabile_to_expressible (d:denotabile) = match d with
	| DInt n -> EInt n
	| DPointer p -> EInt p
	| DPair (p1, p2) -> EPair ( denotabile_to_expressible p1 , denotabile_to_expressible p2 )
	| DFunc (s,t,e) -> EFunc (s,t,e)
	| DList l -> raise (Failure "bug in implementation")
	| DAddress l -> raise (Failure "bug in implementation")
	| DArray (n,l) -> raise (Failure "bug in implementation or not implemented yet")

let rec storable_to_expressible (s:storable) = match s with
	| SInt n -> EInt n
	| SPointer p -> EInt p
	| SPair (p1, p2) -> EPair ( storable_to_expressible p1 , storable_to_expressible p2)
	| SFunc (s,t,e) -> EFunc (s,t,e)


let get_var_value (v:vname) (env:environment) (sto:storage) =
	match (env v) with
		| L l -> storable_to_expressible (apply_storage sto l)
		| d -> denotabile_to_expressible(e)
;;

(* funzioni semantica *)

let rec a_sem (s:a_exp) (env:environment) (sto:storage) = match s with
	| Avar v -> expressible_to_int (get_var_value v env sto)
		(*(
			match env v with 
				| DInt i -> EInt i
				| DPointer p -> EInt p
				| Address l -> 
					(
						match applay_storage sto l with 
							| SInt i -> EInt i
							| SPointer p -> EInt p
							| _ -> raise (Failure "Not int variable in a arithmetic expression")
					)
				| _ -> raise (Failure "Not int constant in a arithmetic expression")
		)*)
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
	| Apnt2val a ->
		(
			match  a_sem a env sto with
				| EInt p ->
					(
						match sto p with
							| SInt n -> EInt n
							| SPointer p -> EInt p
							| _ -> raise (Failure "Not int variable pointed in a arithmetic expression")
					)
				| _ -> raise (Failure "Not a valid pointer")
		)
	| Avar2pnt v ->
		(
			match env v with
				| Address l -> EInt l
				| _ -> raise (Failure "Unable to point to a const value")
		)
	| Aarr2pnt v ->
		(
			match env v with
				| Array ( arrayLength, arrayLocation ) -> EInt arrayLocation
				| _ -> raise (Failure "This is not an array")
		)
	| AvarList ( v, a) -> 
		(
			match (env v , a_sem a env sto ) with
				| List l , EInt n -> EInt ( access_list_n l n )
				| _ -> raise (Failure "Illegal access to a list")
		)
(*	| _ -> raise (Failure "Invalid a-exp") *)

and pair_sem (p:pair_exp) (env:environment) (sto:storage) = match p with
	| Pvar v ->
		(
			match env v with
				| DPair (d1, d2) -> denotabile_to_expressible (DPair (d1,d2)) 
				| Address l -> storable_to_expressible (sto l)
				| _ -> raise (Failure "Pvar must be applied to a pair")
		)
	| Pnumnum (a1, a2) -> EPair ( a_sem a1 env sto, a_sem a2 env sto)
	| Ppairnum (p1 , a1) -> EPair ( pair_sem p1 env sto, a_sem a1 env sto)
	| Pnumpair (a1 , p1) -> EPair ( a_sem a1 env sto, pair_sem p1 env sto)
	| Ppairpair (p1 , p2) -> EPair ( pair_sem p1 env sto, pair_sem p2 env sto)
	| Pproj1 p1 -> 
		(
			match pair_sem p1 env sto with
				| EPair (r1, r2) -> r1
				| _ -> raise (Failure "I can only project a couple!")
		)
	| Pproj2 p1 -> 
		(
			match pair_sem p1 env sto with
				| EPair (r1, r2) -> r2
				| _ -> raise (Failure "I can only project a couple!")
		)
;;

let rec b_sem (s:b_exp) (env:environment) (sto:storage) = match s with
	| Btrue -> EBool true
	| Bfalse -> EBool false
	| Bequal (a1,a2) -> EBool (expressibile_to_int (a_sem a1 env sto) = expressibile_to_int (a_sem a2 env sto))
	| Bleq (a1,a2) -> EBool (expressibile_to_int (a_sem a1 env sto) <= expressibile_to_int (a_sem a2 env sto))
	| Bnot b1 -> EBool ( not ( expressibile_to_bool (b_sem b1 env sto)))
	| Band (b1, b2) -> EBool ( (expressibile_to_bool (b_sem b1 env sto)) && (expressibile_to_bool (b_sem b2 env sto)))
;;

let rec list_sem (l:list_exp) (env:environment) (sto:storage) = match l with
	| Lvar v ->
		(match env v with
			| List l -> EList l
			| _ -> raise (Failure "Non list variable in list expression.")
		)
	| LpushFront (ae, le) ->
		let a=a_sem ae env sto in
		let l=list_sem ae env sto in
		EList Conc (expressibile_to_int a) l
	| Lempty -> EList Empty
;;

let rec b_sem (b:b_exp) (env:environment) (sto:storage) = match b with
  | Bvar v -> sto_to_result (sto (env v))
  | Btrue -> EBool true
  | Bfalse -> EBool false
  | Bequal (a1,a2) -> EBool (to_int(a_sem a1 env sto) = to_int(a_sem a2 env sto)) 
  | Bleq (a1,a2) -> EBool (to_int(a_sem a1 env sto) <= to_int(a_sem a2 env sto))
  | Bnot b1 -> EBool ( not( to_bool (b_sem b1 env sto)))
  | Band (b1,b2) -> EBool ( (to_bool ( b_sem b1 env sto )) && (to_bool (b_sem b2 env sto)))
  (*| _ -> raise (Failure "Invalid b-exp")*)
;;

let rec fun_sem (f:fun_exp) (env:environment) (sto:storage) =
	| FVar v -> get_var_value vf env sto
	| FDefine (vp, s) -> EFunc (s, vp, env)
;;

let exp_sem (e:exp_sem) (env:environment) (sto:storage) =
	match e with
		| Aexp ae -> a_sem ae env sto
		| Bexp be -> b_sem be env sto
		| Pexp pe -> pair_sem pe env sto
		| Lexp le -> list_sem le env sto
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

let rec sem (s:stm) (env:environment) (sto:storage) = match s with
	| Slet (t,v,e) -> bind env v (exp_sem e)
	| Sskip -> (env, sto)
	| Sassign (v,e) ->
		(match (env v) with
			| L l -> update_storage sto l (e_sem e ens sto)
			| _ -> raise (Failure "Trying to assign a constant.")
		)
	| Ssequence (s1,s2) ->
		let (env1, sto1) = sem s1 env sto in
			sem s2 env1 sto1
	| Sifthenelse (b,s1,s2) ->
		let b_value = expressible_to_bool (b_sem b env sto) in
			if b_value then
				sem s1 env sto
			else
				sem s2 env sto
	| Swhile (b,s1) ->
		let b_value = expressible_to_bool (b_sem b env sto) in
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
	|	Scall ( vf , e) ->
		(let (s,vp,f_env)=expressibile_to_function (get_var_value vf env sto) in
		(*DA STRAMEGA RICONTROLLARE *)
		let new_f_env = bind vp f_env (env vp) in
		match  sem s new_f_env sto with
			| (env1, sto1) -> (env, sto1)
		)
		(* DA ELIMINARE APPENA SIAMO CERTI CHE NON E' INUTILE
		(match sto_to_result (sto (env f)) with
				| Func ( s1, v , envf ) ->
					let ( env1 , sto1 ) =
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
		)*)
	(* @ENRICO: Vedi di aggiornarle tu queste due? 
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
		)*)
	| _ -> raise (Failure "Semantic not implemented yet")
;;


















