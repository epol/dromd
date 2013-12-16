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
	| name -> raise (Failure (String.concat "" [ "Variable not found: " ; name ]))
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
		Svar ( "f" , Fexp (Fdefine ( "variabilePnt" , 
										Ssequence (
											SassignPnt (Avar "variabilePnt" , Aexp (Aplus (Apnt2val (Avar "variabilePnt"), Anum 1))),
											Sprint ( Aexp (Apnt2val (Avar "variabilePnt")))
										),
										Aexp (Aplus ( Apnt2val (Avar "variabilePnt") , Anum 10 ))))),
		Ssequence (
			Slet ("costante", Aexp (Anum 5)),
			Ssequence (
				Svar ( "variabile" , Aexp (Aneg (Avar "costante"))),
				Ssequence (
					Svar ( "result" , Aexp (Anum 9999)),
					Ssequence (
						Scall ("result", Fvar "f", Aexp (Avar2pnt "variabile")),
						Ssequence (
							Sprint (Aexp (Avar "result")),
							Ssequence (
								Sblock (
									Ssequence (
										Svar ( "lambda" , Aexp (Anum 10 )),
										Sassign ( "f" , Fexp ( Fdefine ( "t" , Sprint ( Aexp (Aprod (Avar "t", Avar "lambda"))) , Aexp (Aprod (Avar "t", Avar "lambda")) )))
									)
								),
								Ssequence (
									SvarArray ( "array" , Anum 5 , Anum 0 ),
									Ssequence (
										Sblock (
											Ssequence (
												Svar ( "i" , Aexp (Anum 0)),
												Swhile ( Band (Bleq ( Avar "i" , Anum 5 ) , Bnot ( Bequal ( Avar "i" , Anum 5))) , 
																	Ssequence (
																		SassignArray ( "array" , Avar "i" , Avar "i"),
																		Sassign ("i" , Aexp (Aplus (Avar "i", Anum 1 )))
																	)
																)
											)
										),
										Ssequence (
											SiterArray ("array", Fvar "f"),
											Sskip (* TODO: Here we should try the map function *)
										)
									)
								)
							)
						)
					)
				)
			)
		)
	)
;;

Printf.printf "%s\n" "---- Code ----";;
Printf.printf "%s\n" (stm_to_str test1 0);;
Printf.printf "%s\n" "---- Result ----";;
let (env1, sto1) = sem test1 env sto;;

let test2 = 
	Ssequence (
		Slet("l",Lexp (LpushFront (Anum 5, LpushFront (Anum 7, (LpushFront (Anum 4, Lempty)))))),
		Ssequence (
			Slet("f", Fexp ( Fdefine ("x", (Sprint (Aexp (Aplus(Avar "x",Anum 1)))),Aexp (Avar "x")))),
			SiterList(Lvar "l", Fvar "f");
		)
	)
;;
Printf.printf "%s\n" "---- Code ----";;
Printf.printf "%s\n" (stm_to_str test2 0);;
Printf.printf "%s\n" "---- Result ----";;
let (env1, sto1) = sem test2 env sto;;


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
