(* semantica *)

type result = Int of int | Bool of bool | Couple of result*result;;

let to_int (r:result) = match r with
	| Int i -> i
	| _ -> raise (Failure "Wrong data type in conversion")
;;

let to_bool (r:result) = match r with
  | Bool b -> b
  | _ -> raise (Failure "Wrong data type in conversion")

type loc = int;; (* indirizzi di memoria *)

type environment = vname -> loc;;
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
	| _ -> raise (Failure "Invalid a-exp")
;;

let rec b_sem (b:a_exp) (env:environment) (sto:storage) = match b with
  | Bvar v -> sto (env v)
  | Btrue -> Bool true
  | Bfalse -> Bool false
  | Bequal (a1,a2) -> Bool (to_int(a_sem a1 env sto) = to_int(a_sem a2 env sto)) 
  | Bleq (a1,a2) -> Bool (to_int(a_sem a1 env sto) <= to_int(a_sem a2 env sto))
  | Bnot b1 -> Bool ( not( to_bool (b_sem b1 env sto)))
  | Band (b1,b2) -> Bool ( (to_bool (b1 env sto)) && (to_bool (b2 env sto)))
  | _ -> raise (Failure "Invalid b-exp")
;;
