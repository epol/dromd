(* semantica *)

#use "syntax.ml"

type loc = int;; (* indirizzi di memoria *)
type environment = vname -> loc;;

type result = Int of int | Pointer of loc | Bool of bool | Couple of result*result | Func of stm * vname * environment ;;

let to_int (r:result) = match r with
	| Int i -> i
	| _ -> raise (Failure "Wrong data type in conversion")
;;

let to_bool (r:result) = match r with
  | Bool b -> b
  | _ -> raise (Failure "Wrong data type in conversion")


type storage = loc -> result;;

let rec a_sem (s:a_exp) (env:environment) (sto:storage) = match s with
	| Avar v -> sto (env v)
	| Anum n -> Int n
	| Aplus (a1,a2) -> Int (to_int (a_sem a1 env sto) + to_int (a_sem a2 env sto))
	| Aminus (a1,a2)-> Int (to_int (a_sem a1 env sto) - to_int (a_sem a2 env sto))
	| Aneg a1 -> Int (- to_int (a_sem a1 env sto))
	| Aprod (a1,a2)-> Int (to_int (a_sem a1 env sto) * to_int (a_sem a2 env sto))
	| Adiv (a1,a2)-> Int (to_int (a_sem a1 env sto) / to_int (a_sem a2 env sto))
(*	| Avar2pnt v -> Int (env v)   *)
	| Acouple (a1,a2) -> Couple (a_sem a1 env sto,a_sem a2 env sto)
	| Aproj1 Acouple (a1, a2) -> a_sem a1 env sto
	| Aproj2 Acouple (a1, a2) -> a_sem a2 env sto
  | Apnt2val v -> (match sto (env v) with
    | Pointer p -> sto ( p )
    | _ -> raise (Failure "Not a pointer")
    )
	| AvarArray (arrayName , indexExp) -> 
		(
			match a_sem indexExp env sto with
				|	Int index ->
					( match sto ((env arrayName )-1)  with
							|	Int arrayLength ->
								if index < arrayLength then
									sto (env arrayName + index)
								else 
									raise (Failure "Segmentation Fault!")
							| _ -> raise (Failure "Is that an array?")
					)
				|	_ -> raise (Failure "Invalid array index expression")
		)
	| _ -> raise (Failure "Invalid a-exp")
;;

let rec b_sem (b:b_exp) (env:environment) (sto:storage) = match b with
  | Bvar v -> sto (env v)
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
	| Couple (e1,e2) ->
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
;;

let rec sem (s:stm) (env:environment) (sto:storage) = match s with
	| Slet (v,a) ->
	  (
			(fun (v1:vname) ->
				if v1 = v then
					to_int (sto(-1))
				else
					env(v1)
			),
			(fun (n:loc) ->
				if n = to_int (sto(-1)) then
					a_sem a env sto
				else if n = -1 then
					Int (to_int (sto(-1)) + 1)
				else
					sto (n)
	  	)
	  )
	| Sskip -> (env, sto)
	| Sassign (v,a) ->
	  (
			env,
			(fun (n:loc) ->
				if n = env v then
					a_sem a env sto
				else
					sto (n)
	  	)
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
		(
			(fun (v1:vname) ->
				if v1 =f then 
					to_int (sto(-1))
				else
					env(v1)
			),
			(fun (n:loc) ->
				if n = to_int(sto(-1)) then 
					Func ( s1 , p, env)
				else if n = -1 then
					Int (to_int( sto(-1)) +1 )
					else
						sto(n)
			)
		)
	|	Scall ( f , a) -> 
		(
			match sto (env f) with
				| Func ( s1, v , envf ) ->
					let ( env1 , sto1 )=
						( (
							fun (v1:vname) ->
								if v1=v then
									to_int (sto(-1))
								else
									envf(v1)
							), (
							fun ( n:loc) ->
								if n = to_int (sto(-1)) then
									a_sem a env sto
								else if n = -1 then 
										Int (to_int (sto(-1)) +1)
									else
										sto(n)
								)
							) in
							let (env2, sto2) = sem s1 env1 sto1 in
								(env , sto2)
				| _ -> raise (Failure "Call to an invalid function")
		)
	|	SletArray ( arrayName , arrayLengthExp , arrayInitialValueExp ) ->
		(
			match ( a_sem arrayLengthExp env sto , a_sem arrayInitialValueExp env sto ) with 
				|	(Int arrayLength , Int arrayInitialValue ) ->
					(fun (v:vname) ->
						if v = arrayName then 
							(to_int (sto(-1))) + 1
						else 
							env (v)
					),
					(fun (n:loc) ->
						if n=to_int(sto(-1)) then Int arrayLength
						else if n>to_int(sto(-1)) && n <= to_int(sto(-1)) +arrayLength then Int arrayInitialValue
						else if n = -1 then Int (to_int (sto (-1)) + 1 + arrayLength)
						else sto(n)
					)
				| _ -> raise (Failure "Invalid array initialization") 
		)
	| SassignArray (arrayName , indexExp, valueExp) ->
		(
			match a_sem indexExp env sto with 
				|	Int index ->
					(
						env,
						(fun (n:loc) ->
							if n = (env arrayName) + index  then
								a_sem valueExp env sto
							else
								sto (n)
						)
					)
				| _ -> raise (Failure "Invalid index") 
		)
(*	| _ -> raise (Failure "Semantic not implemented yet")   *)
;;


















