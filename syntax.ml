 (* sintassi *)

type vname = string

type a_exp = 
	| Avar of vname
	| Anum of int
	| Aplus of a_exp * a_exp (* a1 + a2 *)
	| Aminus of a_exp * a_exp (* a1 - a2 *)
	| Aneg of a_exp (* -a1 *)
	| Aprod of a_exp * a_exp (* a1 * a2 *)
	| Adiv of a_exp * a_exp (* a1 / a2 *)
	| Acouple of a_exp * a_exp
	| Aproj1 of a_exp
	| Aproj2 of a_exp
;;

type b_exp =
	| Btrue
	| Bfalse
	| Bequal of a_exp * a_exp
	| Bleq of a_exp * a_exp
	| Bnot of b_exp
	| Band of b_exp * b_exp
;;

type stm =
	| Sassign of vname * a_exp
	| Sskip
	| Slet of vname * a_exp
	| Sfun of vname * vname * stm
	| Ssequence of stm * stm
	| Sifthenelse of b_exp * stm * stm
	| Swhile of b_exp * stm
	| Sblock of stm
	| Scall of fname
	| Sprint of a_exp
;;
