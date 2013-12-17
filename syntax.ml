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
	| Apnt2val of a_exp (* TODO: Non c'è un modo migliore di farlo? *)
	| Avar2pnt of vname
	| Aarr2pnt of vname
	(* lists *)
	| AvarList of list_exp*a_exp
	| AlistHead of list_exp
and b_exp =
	| Btrue
	| Bfalse
	| Bequal of a_exp * a_exp
	| Bleq of a_exp * a_exp
	| Bnot of b_exp
	| Band of b_exp * b_exp
	| BisListEmpty of list_exp
and list_exp =
	| Lempty
	| LpushFront of a_exp * list_exp
	| Lvar of vname
	| Ltail of list_exp
	| Lpair2list of pair_exp
and pair_exp =
	| Pvar of vname
	| Pnumnum of exp * exp
	| Ppairnum of pair_exp * exp
	| Pnumpair of  exp * pair_exp
	| Ppairpair of pair_exp * pair_exp
	| Pproj1 of pair_exp
	| Pproj2 of pair_exp
and fun_exp =
	| Fvar of vname
	| Fdefine of vname * stm * exp						(* execute stm with param v, return e						*)
	| Fpair2fun of pair_exp
and exp = 
	| Aexp of a_exp
	| Bexp of b_exp
	| Lexp of list_exp
	| Pexp of pair_exp
	| Fexp of fun_exp
and stm =
	| Sskip																		(* skip																					*)
	| Ssequence of stm * stm									(* s1 ; s2																			*)
	| Sassign of vname * exp									(* v1 := e1																			*)
	| Slet of vname * exp											(* const v1 := e1																*)
	| Svar of vname * exp											(* var v1 := e1																	*)
	| Sifthenelse of b_exp * stm * stm				(* if b then s1 else s2													*)
	| Swhile of b_exp * stm										(* while (b1) do s1 														*)
	| Sblock of stm														(* begin s1 end																	*)
	| Scall of vname * fun_exp * exp					(* x := f ( e1)																	*)
	| Sprint of exp														(* print (a1)																		*)
	| SvarArray of vname * a_exp * a_exp			(* var arrayName[arrayLength] = arrayInitValue	*)
	|	SassignArray of vname * a_exp * a_exp		(* arrayName [indexExp] = valueExp 							*)
	| SassignPnt of a_exp * exp								(* *(a) := e																		*)
	| SiterArray of vname * fun_exp
	| SmapArray of vname * fun_exp
	| SiterList of list_exp * fun_exp
;;

(* funzioni di stampa *)

let rec tab n = match n with
	| 0 -> ""
	| x -> "  " ^ tab (x-1)
;;

let rec b_exp_to_str be = match be with 
	| Btrue -> "true"
	| Bfalse -> "false"
	| Bequal (a1,a2) -> a_exp_to_str a1 ^ " == " ^ a_exp_to_str a2
	| Bleq (a1,a2) -> a_exp_to_str a1 ^ " <= " ^ a_exp_to_str a2
	| Bnot b -> "!("^b_exp_to_str b ^")"
	| Band (b1, b2) -> b_exp_to_str b1 ^ " && " ^ b_exp_to_str b2
	| BisListEmpty le -> "is_empty("^list_exp_to_str le ^")"
and a_exp_to_str ae = match ae with
	| Avar (v) -> v
	| Anum n-> string_of_int n
	| Aplus (a1,a2) ->  a_exp_to_str a1 ^ " + " ^ a_exp_to_str a2
	| Aminus (a1,a2) ->  a_exp_to_str a1 ^ " - " ^ a_exp_to_str a2
	| Aneg a ->  "-(" ^ a_exp_to_str a ^ ")"
	| Aprod (a1,a2) ->  "(" ^ a_exp_to_str a1 ^ ") * (" ^ a_exp_to_str a2 ^ ")"
	| Adiv (a1,a2) ->  "(" ^ a_exp_to_str a1 ^ " / " ^ a_exp_to_str a2 ^ ")"
	| Apair2num pe-> "pair_to_num(" ^ pair_exp_to_str pe ^")"
	| AvarArray (v,a) -> v^"["^ a_exp_to_str a ^"]"
	| Apnt2val a-> "*("^a_exp_to_str a^")"
	| Avar2pnt v-> "&"^v^""
	| Aarr2pnt v-> v
	| AvarList (l,a) -> list_exp_to_str l^"["^ a_exp_to_str a ^"]"
	| AlistHead le -> "head(" ^ list_exp_to_str le ^")"
and list_exp_to_str le = match le with
	| Lempty -> "[]"
	| LpushFront (a,l) -> a_exp_to_str a ^ " : " ^ list_exp_to_str l
	| Lvar v -> v
	| Ltail l-> "tail(" ^ list_exp_to_str l ^")"
	| Lpair2list pe -> "pair_to_list(" ^ pair_exp_to_str pe ^")"
and pair_exp_to_str pe = match pe with 
	| Pvar v -> v
	| Pnumnum (a1,a2) ->  "("^(exp_to_str a1 0) ^ "," ^ (exp_to_str a2 0) ^ ")"
	| Ppairnum (p,a) ->  "("^pair_exp_to_str p ^ "," ^ exp_to_str a 0 ^ ")"
	| Pnumpair (a,p) ->  "("^exp_to_str a 0 ^ "," ^ pair_exp_to_str p ^ ")"
	| Ppairpair (p1,p2) ->  "("^pair_exp_to_str p1 ^ "," ^ pair_exp_to_str p2 ^ ")"
	| Pproj1 p -> "fst(" ^ pair_exp_to_str p ^")"
	| Pproj2 p -> "snd(" ^ pair_exp_to_str p ^")"
and fun_exp_to_str fe ind=  match fe with
	| Fvar v -> v;
	| Fdefine (vp, s,e ) -> "fun ("^vp^") {\n" ^
			stm_to_str s (ind+1) ^ "\n" ^
			tab (ind+1) ^ "return " ^ exp_to_str e ind ^ ";\n"^
			tab ind ^ "}"
	| Fpair2fun pe -> "pair_to_fun(" ^ pair_exp_to_str pe ^")"
and exp_to_str e ind= match e with
	| Aexp ae -> a_exp_to_str ae
	| Bexp be -> b_exp_to_str be
	| Lexp le -> list_exp_to_str le
	| Pexp pe -> pair_exp_to_str pe
	| Fexp fe -> fun_exp_to_str fe ind
and stm_to_str s ind=	match s with
	| Sskip -> tab ind ^ "skip;"
	| Ssequence (s1,s2) -> (stm_to_str s1 ind) ^ "\n" ^ (stm_to_str s2 ind)
	| Sassign (v, e) -> tab ind ^ v ^ " := " ^ exp_to_str e ind^ ";"
	| Slet (v, e) -> tab ind ^ "let " ^ v ^ " := " ^ exp_to_str e ind^ ";"
	| Svar (v, e) -> tab ind ^ "var " ^ v ^ " := " ^ exp_to_str e ind^ ";"
	| Sifthenelse (be, s1, s2) -> tab ind ^ "if " ^ b_exp_to_str be ^ "{\n" ^ stm_to_str s1 ind ^"\n" ^ tab ind ^"} else {\n"^ stm_to_str s2 ind ^ tab ind ^ "\n"
	| Swhile (be, s) -> tab ind ^ "while (" ^ b_exp_to_str be ^ ") {\n" ^ stm_to_str s (ind+1) ^ "\n"^ tab ind ^"}"
	| Sblock s -> tab ind ^ "{\n" ^ stm_to_str s (ind+1) ^ "\n" ^ tab ind ^"}"
	| Scall (v,fe,e) -> v ^ " := " ^ fun_exp_to_str fe ind ^ "(" ^ exp_to_str e ind^ ");"
	| Sprint e -> tab ind ^ "print " ^ exp_to_str e ind ^ ";"
	| SvarArray (v,ae_len,ae_init) -> tab ind ^ "var " ^ v ^ "[] of len " ^ a_exp_to_str ae_len ^ " := " ^ a_exp_to_str ae_init ^ ";"
	| SassignArray (v,ae_index,ae_value) ->  tab ind ^ v ^ "[" ^ a_exp_to_str ae_index ^ "] := " ^ a_exp_to_str ae_value ^ ";"
	| SassignPnt (ae_pnt, e) -> tab ind ^ "*("^a_exp_to_str ae_pnt ^ ") := " ^ exp_to_str e ind^ ";"
	| SiterArray (v, fe) -> tab ind ^ "iter_array(" ^ v ^ "," ^ fun_exp_to_str fe (ind+1) ^ ");"
	| SmapArray (v, fe) -> tab ind ^ "map_array(" ^ v ^ "," ^ fun_exp_to_str fe (ind+1) ^ ");"
	| SiterList (le, fe) -> tab ind ^ "iter_list(" ^ list_exp_to_str le ^ "," ^ fun_exp_to_str fe (ind+1) ^");"
;;
