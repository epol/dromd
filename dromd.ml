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
											SmapArray ("array", Fvar "f"),
											SiterArray ("array", Fvar "f")
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

let test3 = 
	Ssequence (
		Slet("l",Lexp (LpushFront (Anum 5, LpushFront (Anum 7, (LpushFront (Anum 4, Lempty)))))),
	Ssequence (
		Slet("f", Fexp ( Fdefine ("x", (Sskip),Aexp (Aplus(Avar "x",Anum 1))))),
	Ssequence(
		Slet("map", Fexp ( Fdefine ("arg", (
				Ssequence (
					Slet("res", Lexp Lempty),
				Ssequence (
					Svar ("y", Aexp (Anum 0)),
					Swhile (BisListEmpty (Lvar "l"), 
						Ssequence (
							Scall ("y", Fpair2fun (Pproj1(Pvar "arg")), Aexp (AlistHead (Lpair2list (Pproj2 (Pvar "arg"))))),
						Ssequence (
							Sassign("res", Lexp (LpushFront (Avar "y", Lvar "res"))),
							Slet ("l", Lexp (Ltail (Lvar "l")))
						))
					)
					))),
			Lexp (Lvar "res")
			))
		),
		Ssequence(
			Svar("z", Lexp Lempty),
		Ssequence(
			Scall ("z",Fvar "map", Pexp (Pnumnum(Fexp (Fvar "f"), Lexp (Lvar "l")))),
			Sprint (Lexp (Lvar "l"))
	)))))
;;
Printf.printf "%s\n" "---- Code ----";;
Printf.printf "%s\n" (stm_to_str test3 0);;
Printf.printf "%s\n" "---- Result ----";;
let (env1, sto1) = sem test3 env sto;;


