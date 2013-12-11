(*
 * syntax.ml
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
	(* couples *)
	| Apair2num of pair_exp
	(* array *)
	| AvarArray of vname * a_exp
	(* pointers *)
	| Apnt2val of vname
	| Avar2pnt of vname
	| Aarr2pnt of vname
	(* lists *)
	| AvarList of vname*a_exp
and b_exp =
	| Bvar of vname
	| Btrue
	| Bfalse
	| Bequal of a_exp * a_exp
	| Bleq of a_exp * a_exp
	| Bnot of b_exp
	| Band of b_exp * b_exp
and list_exp =
	| Lempty
	| LpushFront of a_exp * list_exp
	| Lvar of vname
	| Lempty
and pair_exp =
	| Pvar of vname
	| Pnumnum of a_exp * a_exp
	| Ppairnum of pair_exp * a_exp
	| Pnumpair of  a_exp * pair_exp
	| Ppairpair of pair_exp * pair_exp
	| Pproj1 of pair_exp
	| Pproj2 of pair_exp
and fun_exp =
	| Fvar of vname
	| Finit of vname * stm										(* f(v1) = stm																								*)
;;

type exp = 
	| Aexp of a_exp
	| Bexp of b_exp
	| Lexp of list_exp
	| Pexp of pair_exp
;;

type stm =
	| Sskip																		(* skip																												*)
	| Ssequence of stm * stm									(* s1 ; s2																										*)
	| Sassign of vname * exp									(* v1 := e1																										*)
	| Slet of vname * exp											(* const v1 := e1																							*)
	| Svar of vname * exp											(* var v1 := e1																								*)
	| Sifthenelse of b_exp * stm * stm				(* if b then s1 else s2																				*)
	| Swhile of b_exp * stm										(* while (b1) do s1 																					*)
	| Sblock of stm														(* begin s1 end																								*)
	| Scall of vname * exp										(* f ( e1)																										*)
	| Sprint of exp														(* print (a1)																									*)
	|	SassignArray of vname * a_exp * a_exp		(* arrayName [indexExp] = valueExp 														*)
	| SassignPnt of vname * a_exp 						(* *v1 := a1																									*)
;;
