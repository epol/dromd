(*
 * dromd.ml
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

(*open Syntax;;
open Semantic;;*)

#use "semantic.ml"

let env = function
	| _ -> raise (Failure "Name not declared")
;;

let sto = 
	1 ,
	(
		function
			| _ -> raise (Failure "Segmentation Fault") 
	)
;;


let test1 = 
	Ssequence (
		Svar ( "f" , Fexp (Fdefine ( "t" , Sskip , Aexp (Aplus ( Avar "t" , Anum 10 ))))),
		Ssequence (
			Slet ("costante", Aexp (Anum 5)),
			Ssequence (
				Svar ( "variabile" , Aexp (Aneg (Avar "costante"))),
				Ssequence (
					Svar ( "result" , Aexp (Anum 9999)),
					Ssequence (
						Scall ("result", Fvar "f", Aexp (Avar "costante")),
						Sprint (Aexp (Avar "result"))
					)
				)
			)
		)
	)
;;

let (env1, sto1) = sem test1 env sto;;

(*

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

(* Testing the function variable scoping *)
let s = Ssequence( Ssequence ( Sfun ("g","t",Sprint( Avar "t")) , 
	Sblock ( 
		Ssequence ( 
			Slet (Var, "t", Anum 3 ) , 
			
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

(* Creating an array *)
let s2 = Ssequence ( SletArray (Var ,"array",Anum 20 , Anum 8) , Sprint ( AvarArray ( "array", Anum 19 ) ) );;
let (env2,sto2) = sem s2 env1 sto1 ;;	

(* Writing on an array *)
let s3 = Ssequence ( SassignArray ("array",Anum 10, Anum 5) , Sprint( AvarArray ("array" ,Anum 10)));;
let (env3,sto3) = sem s3 env2 sto2 ;;


(* let's try call by reference *)
let s4 = Ssequence ( 
		Sfun ("f" , "t", SassignPnt ( "t", Aplus(Apnt2val "t", Anum 1))) , 
		Ssequence ( 
			Slet ( Var , "t" , Anum 11),
			Ssequence (
				Scall ( "f" , Avar2pnt "t"),
				Sprint (Avar "t")
			)
		)
	) ;;
let (env4,sto4) = sem s4 env3 sto3 ;;



*)
