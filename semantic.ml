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
(*| SPointer of loc*)
	| SPair of storable * storable
	| SFunc of (stm * exp * vname * environment)
and denotabile = 
	| DInt of int
(*	| DPointer of loc *)
	| DPair of denotabile * denotabile
	| DFunc of (stm * exp * vname * environment)
	| L of loc
	| DList of int_list
	| DArray of int * loc
and expressible =
	| EInt of int
	| EBool of bool
	| EPair of expressible * expressible
	| EFunc of (stm * exp * vname * environment)
	| EList of int_list
and environment = vname -> denotabile
;;

type storage = int * (loc -> storable)
;;

let apply_storage (sto:storage) (l:loc) = (snd sto) l
;;

let update_storage (sto:storage) (l:loc) (d:storable) = 
	let updated_memory l1 = if (l1=l) then d else apply_storage sto l1 in
	(fst sto, updated_memory)
;;


(*
let extend_storage (sto:storage) (s:storable) = 
	let updated_memory l1 = if (l1=(fst sto)) then s else apply_storage sto l1 in
	(fst sto +1, updated_memory)
;;*)

let extend_storage (sto:storage) (s:storable) (n:int) = 
	let updated_memory l1 =
		if (l1>= (fst sto) &&l1 < ((fst sto) + n))
			then s
			else apply_storage sto l1
	in ((fst sto + n), updated_memory)
;;

let bind (env:environment) (v:vname) (d:denotabile) = 
	let new_env v1 = if (v1=v) then d else env v1 in
	new_env
;;

let storable_to_int (s:storable) = match s with
	| SInt i -> i
(*	| SPointer p -> p *)
	| _ -> raise (Failure "Wrong data type in conversion")
;;

let denotabile_to_int (d:denotabile) = match d with
	| DInt i -> i 
(*	| DPointer p -> p *)
	| _ -> raise (Failure "Wrong data type in conversion")
;;

let expressible_to_int (e:expressible) = match e with
	| EInt i -> i
	| _ -> raise (Failure "Wrong data type in conversion")
;;

let expressible_to_bool (e:expressible) = match e with
	| EBool b -> b
	| _ -> raise (Failure "Wrong data type in conversion")
;;

let expressible_to_function (e:expressible) = match e with
	| EFunc (s,e,v,en) -> (s,e,v,en)
	| _ -> raise (Failure "Wrong data type in conversion")
;;

let expressible_to_list (e:expressible) = match e with 
	| EList l -> l
	| _ -> raise (Failure "Wrong data type in conversion")

let rec access_list_n (l1:int_list) (n:int) = match l1 with
	| Empty -> raise (Failure "The list isn't so long")
	| Conc ( e , l2 ) -> if n=0 then e else (access_list_n l2 (n - 1) )
;;

let rec denotabile_to_expressible (d:denotabile) = match d with
	| DInt n -> EInt n
(*	| DPointer p -> EInt p *)
	| DPair (p1, p2) -> EPair ( denotabile_to_expressible p1 , denotabile_to_expressible p2 )
	| DFunc (s,e,t,env) -> EFunc (s,e,t,env)
	| DList l -> raise (Failure "bug in implementation")
	| L l -> raise (Failure "bug in implementation")
	| DArray (n,l) -> raise (Failure "bug in implementation or not implemented yet")
;;

let rec storable_to_expressible (s:storable) = match s with
	| SInt n -> EInt n
(*	| SPointer p -> EInt p *)
	| SPair (p1, p2) -> EPair ( storable_to_expressible p1 , storable_to_expressible p2)
	| SFunc (s,e,t,env) -> EFunc (s,e,t,env)
;;


let rec expressible_to_storable (e:expressible) = match e with
	| EInt n -> SInt n
	| EBool b -> raise (Failure "Bool is not storable")
	| EPair (p1,p2) -> SPair ( expressible_to_storable p1, expressible_to_storable p2)
	| EFunc (s,e,t,env) -> SFunc (s,e,t,env)
	| EList l -> raise (Failure "List is not storable")
;;

let rec expressible_to_denotabile (e:expressible) = match e with
	| EInt n -> DInt n
	| EPair (p1, p2) -> DPair ( expressible_to_denotabile p1 , expressible_to_denotabile p2 )
	| EFunc (s,e,t,env) -> DFunc (s,e,t,env)
	| EList l -> DList l
	| EBool b -> raise (Failure "bool is not denotabile")	
;;


let get_var_value (v:vname) (env:environment) (sto:storage) =
	match (env v) with
		| L l -> storable_to_expressible (apply_storage sto l)
		| d -> denotabile_to_expressible(d)
;;

(* funzioni semantica *)

let rec a_sem (s:a_exp) (env:environment) (sto:storage) = match s with
	| Avar v -> get_var_value v env sto
	| Anum n -> EInt n
	| Aplus ( a1,a2) -> EInt (expressible_to_int ( a_sem a1 env sto ) + expressible_to_int ( a_sem a2 env sto ))
	| Aminus ( a1,a2) -> EInt (expressible_to_int ( a_sem a1 env sto ) - expressible_to_int ( a_sem a2 env sto ))
	| Aneg a1 -> EInt ( - expressible_to_int ( a_sem a1 env sto ))
	| Aprod ( a1,a2) -> EInt (expressible_to_int ( a_sem a1 env sto ) * expressible_to_int ( a_sem a2 env sto ))
	| Adiv ( a1,a2) -> EInt (expressible_to_int ( a_sem a1 env sto ) / expressible_to_int ( a_sem a2 env sto ))
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
							|	DArray ( arrayLength , arrayLocation ) ->
								if index < arrayLength then
									(
										match (snd sto) ( arrayLocation + index) with
											| SInt i -> EInt i
										(*	| SPointer p -> EInt p *)
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
						match (snd sto) p with
							| SInt n -> EInt n
							(*| SPointer p -> EInt p *)
							| _ -> raise (Failure "Not int variable pointed in a arithmetic expression")
					)
				| _ -> raise (Failure "Not a valid pointer")
		)
	| Avar2pnt v ->
		(
			match env v with
				| L l -> EInt l
				| _ -> raise (Failure "Unable to point to a const value")
		)
	| Aarr2pnt v ->
		(
			match env v with
				| DArray ( arrayLength, arrayLocation ) -> EInt arrayLocation
				| _ -> raise (Failure "This is not an array")
		)
	| AvarList ( l, a) -> 
		(
			match (list_sem l env sto , a_sem a env sto ) with
				| EList l , EInt n -> EInt ( access_list_n l n )
				| _ -> raise (Failure "Illegal access to a list")
		)
	| AlistHead l1 -> 
		(
			match list_sem l1 env sto with
				| EList Empty -> raise (Failure "Trying to access the head of an empty list")
				| EList Conc (n,l2) -> EInt n
				| _ -> raise (Failure "Not a list")
		)
(*	| _ -> raise (Failure "Invalid a-exp") *)

and pair_sem (p:pair_exp) (env:environment) (sto:storage) = match p with
	| Pvar v ->
		(
			match env v with
				| DPair (d1, d2) -> denotabile_to_expressible (DPair (d1,d2)) 
				| L l -> storable_to_expressible ((snd sto) l)
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

and b_sem (s:b_exp) (env:environment) (sto:storage) = match s with
	| Btrue -> EBool true
	| Bfalse -> EBool false
	| Bequal (a1,a2) -> EBool (expressible_to_int (a_sem a1 env sto) = expressible_to_int (a_sem a2 env sto))
	| Bleq (a1,a2) -> EBool (expressible_to_int (a_sem a1 env sto) <= expressible_to_int (a_sem a2 env sto))
	| Bnot b1 -> EBool ( not ( expressible_to_bool (b_sem b1 env sto)))
	| Band (b1, b2) -> EBool ( (expressible_to_bool (b_sem b1 env sto)) && (expressible_to_bool (b_sem b2 env sto)))
	| BisListEmpty l -> EBool ((list_sem l env sto) = EList Empty)

and list_sem (l:list_exp) (env:environment) (sto:storage) = match l with
	| Lvar v ->
		(match env v with
			| DList l -> EList l
			| _ -> raise (Failure "Non list variable in list expression.")
		)
	| LpushFront (ae, le) ->
			let a=a_sem ae env sto in
				let l=list_sem le env sto in
					EList (Conc ((expressible_to_int a), (expressible_to_list l)))
	| Lempty -> EList Empty
	| Ltail l1 -> 
		(
			match list_sem l1 env sto with
				| EList Empty -> raise (Failure "Trying to access the tail of an empty list")
				| EList Conc (n,l2) -> EList l2
				| _ -> raise (Failure "Not a list")
		)
;;


let rec fun_sem (f:fun_exp) (env:environment) (sto:storage) =
	match f with
		| Fvar vf -> get_var_value vf env sto
		| Fdefine (vp, s,e) -> EFunc (s,e, vp, env)
;;

let exp_sem (e:exp) (env:environment) (sto:storage) =
	match e with
		| Aexp ae -> a_sem ae env sto
		| Bexp be -> b_sem be env sto
		| Pexp pe -> pair_sem pe env sto
		| Lexp le -> list_sem le env sto
		| Fexp fe -> fun_sem fe env sto
;;

let rec print_expressible (e:expressible) =
	match e with
		| EInt n -> Printf.printf "%d" n
		| EBool b -> Printf.printf "%b" b
		| EPair (p1,p2) -> 
				Printf.printf "(";
				print_expressible p1;
				Printf.printf ",";
				print_expressible p2;
				Printf.printf ")"
		| EFunc (s,e,t,env) -> Printf.printf "Printing functions is not supported yet"
		| EList Empty -> Printf.printf "[]"
		| EList Conc (n,l) -> 
				Printf.printf "%d:" n;
				print_expressible (EList l)

(* TODO Fare in modo che tutti i call usino questa funzione *)
let rec call_function (f:stm*exp*vname*environment) (d:denotabile) (sto:storage) =
	let (s,re, vp, f_env) = f in	
	let new_f_env = bind f_env vp d in
	let (env1, sto1) =  sem s new_f_env sto in
		(exp_sem re env1 sto1,sto1)
and iterArray (element:loc) (left:int) (fun_stm:stm) (fun_param:vname) (fun_env:environment) (sto:storage) = 
	if left = 0 then sto
	else
		let fun_env1  = bind fun_env fun_param (expressible_to_denotabile (storable_to_expressible ((snd sto) element))) in
			let (env_garage,sto1) = sem fun_stm fun_env1 sto in
				iterArray (element +1) (left -1) fun_stm fun_param fun_env sto1
and iter_list (l:int_list) (f:stm*exp*vname*environment) (sto:storage) = 
	match l with
		| Empty -> sto
		| Conc (n,l1) ->
				let sto1 = snd (call_function f (DInt n) sto) in
				iter_list l1 f sto1
and sem (s:stm) (env:environment) (sto:storage) = match s with
	| Slet (v,e) -> (bind env v (expressible_to_denotabile (exp_sem e env sto)),sto)
	| Sskip -> (env, sto)
	| Sassign (v,e) ->
		env,
		(match (env v) with
			| L l -> update_storage sto l (expressible_to_storable(exp_sem e env sto))
			| _ -> raise (Failure "Trying to assign a constant.")
		)
	| Svar (v,e) ->
		bind env v (L (fst sto)),
		extend_storage sto (expressible_to_storable (exp_sem e env sto)) 1
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
	| Sprint e -> 
			print_expressible (exp_sem e env sto);
			Printf.printf "\n";
			(env, sto)
	| Sblock s1 ->
		let (env1,sto1) = sem s1 env sto in
			(env,sto1)
	| Scall ( returnVar, funNameExp , e) ->
		(
			let (s1,returnExp,vp,f_env)=expressible_to_function (fun_sem funNameExp env sto) in
				let new_f_env = bind f_env vp (expressible_to_denotabile (exp_sem e env sto)) in
					let (env1, sto1) =  sem s1 new_f_env sto in
						match env returnVar with
							| L l -> ( env , update_storage sto1 l (expressible_to_storable(exp_sem returnExp env1 sto1)))
							| _ -> raise (Failure "A function result must be stored in a variable!")
		)
	| SvarArray (arrayName, lengthExp , initValueExp) ->
		(
			match ( a_sem lengthExp env sto , a_sem initValueExp env sto ) with 
				| (EInt length , EInt initValue ) ->
					(
						bind env arrayName (DArray (length, (fst sto))),
						extend_storage sto (SInt initValue) length
					)
				| _ -> raise (Failure "Invalid initialization of an array")
		)
	|	SassignArray (arrayName, indexExp, valueExp) ->
		(
			match env arrayName with
				| DArray (length, firstLocation) ->
					(
						match a_sem indexExp env sto , a_sem valueExp env sto with
							| EInt index , EInt value -> 
								if index < length then
									(
										env,
										update_storage sto (firstLocation + index) (SInt value)
									)
								else
									raise (Failure "Segmentation Fault")
							| _ -> raise (Failure "Invalid array assign")
					)
				| _ -> raise (Failure "Not an array")
		)
	| SassignPnt (a,e) ->
		(
			match a_sem a env sto with
				| EInt address ->
					env,
					update_storage sto address (expressible_to_storable(exp_sem e env sto))
				| _ -> raise (Failure "Invalid pointer value")
		)
	| SiterArray (arrayName, funExp) ->
		(
			match env arrayName with
				| DArray (length, firstElement) ->
					(
						match fun_sem funExp env sto with
							| EFunc (funcStm,returnExp,paramName,f_env) -> 
								(env, iterArray firstElement length funcStm paramName f_env sto)
							| _ -> raise (Failure "Not a valid function")
					)
				| _ -> raise (Failure "iterArray must be applied to an array!")
		)
	| SiterList (le, fe) ->
		(match list_sem le env sto with
				| EList l ->
					(match fun_sem fe env sto with
							| EFunc f -> (env, iter_list l f sto )
							| _ -> raise (Failure "Not a valid function")
					)
				| _ -> raise (Failure "iterList must be applied to a list!")
		)
(*	| _ -> raise (Failure "Semantic not implemented yet") *)
;;

