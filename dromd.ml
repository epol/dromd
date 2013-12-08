(*open Syntax;;
open Semantic;;*)

#use "semantic.ml"

let env = function
	| "x" -> 1
	| "y" -> 2
	| v -> raise (Failure "Variable not declared")
;;

let sto = function
	| -1 -> Int 3
	| 1 -> Int 5
	| 2 -> Int 7
	| _ -> Int 0
;;

open Printf;;

printf "%d \n" (env "x" );;
printf "%d \n" (env "y" );;

let r=a_sem (Aplus(Anum 5, Avar "x")) env sto;;
let br=b_sem (Bnot(Bequal(Avar "x", Anum 7))) env sto;;

printf "%d \n" (to_int r );;
printf "%b \n" (to_bool br );;

(*
let s = Ssequence(Slet("z", Aplus(Avar "x", Avar "y")), Swhile(Bleq(Anum 7, Avar "z"), Ssequence(Sprint (Avar "z"), Sassign("z", Aminus(Avar "z", Anum 1))))) ;;
let (env1, sto1) = sem s env sto;;

let s2 = Ssequence(Sprint(Avar "x"),Sprint(Avar "y")) ;;
let (env2,sto2) = sem s2 env1 sto1;;
*)

let s = Ssequence( Ssequence ( Sfun ("g","t",Sprint( Avar "t")) , 
	Sblock ( 
		Ssequence ( 
			Slet ("t", Anum 3 ) , 
			
			Ssequence ( 
				Sfun ( "f" , "s" , 
 					Sprint ( Aplus ( ( Avar "t" ) , (Avar "s" )) ) 
					) ,
				Sassign ( "g" , Avar "f")
				)

			)
		) ), 
		Scall ( "g" , Anum 4 ) 
	);;	
let (env1, sto1) = sem s env sto ;;

let s2 = Ssequence ( SletArray ("array",Anum 20 , Anum 8) , Sprint ( AvarArray ( "array", Anum 19 ) ) );;
let (env2,sto2) = sem s2 env1 sto1 ;;	

let s3 = Ssequence ( SassignArray ("array",Anum 10, Anum 5) , Sprint( AvarArray ("array" ,Anum 10)));;
let (env3,sto3) = sem s3 env2 sto2 ;;



