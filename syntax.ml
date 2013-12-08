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
type tag = Var | Const ;;

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
  | Apnt2val of vname
  |	Avar2pnt of vname
  |	AvarArray of vname * a_exp
  | Aarr2pnt of vname
;;

type b_exp =
  | Bvar of vname
	| Btrue
	| Bfalse
	| Bequal of a_exp * a_exp
	| Bleq of a_exp * a_exp
	| Bnot of b_exp
	| Band of b_exp * b_exp
;;

type stm =
	| Sassign of vname * a_exp								(* v1 := a1																										*)
	| Sskip																		(* skip																												*)
	| Slet of tag * vname * a_exp							(* tag v1 := a1																								*)
	| Sfun of vname * vname * stm							(* fun f (t) := s1																						*)
	| Ssequence of stm * stm									(* s1 ; s2																										*)
	| Sifthenelse of b_exp * stm * stm				(* if b then s1 else s2																				*)
	| Swhile of b_exp * stm										(* while (b1) do s1 																					*)
	| Sblock of stm														(* begin s1 end																								*)
	| Scall of vname * a_exp									(* f ( a1)																										*)
	| Sprint of a_exp													(* print (a1)																									*)
	|	SletArray of tag *vname * a_exp * a_exp	(* tag arrayName [arrayLengthExp] := arrayInitialValueExp			*)
	|	SassignArray of vname * a_exp * a_exp		(* arrayName [indexExp] = valueExp 														*)
	| SassignPnt of vname * a_exp 						(* *v1 := a1																									*)
;;
