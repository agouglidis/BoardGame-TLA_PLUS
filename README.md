# BoardGame-TLA_PLUS
 Solution to a puzzle game using TLA+

(***************************************************************************)
(* The rules of the puzzle is to fill in a 5x5 matrix with consecutive     *)
(* numbers from 1 to 25. You can start from any cell in the matrix by      *)
(* placing number 1. Every next cell is selected by:                       *)
(* - jumping over 2 adjacent cells if you move left or right or up or down *)
(*    or                                                                   *) 
(* - jumping over 1 adjacent cell if you move diagonally up right or       *)
(*   diagonally up left or diagonally down right or diagonally down left   *)
(*                                                                         *)
(* This is a simplification of the 10x10 version. When 5x5 is solved       *)
(* symmetric solutions can be combined to solve larger matrices e.g. 10x10 *)
(***************************************************************************)


(***************************************************************************)
(*                          Example solution                               *)
(*     1   2   3   4   5                                                   *)
(* 1   2   19  11  1   18                                                  *)
(* 2   13  5   22  14  6                                                   *)
(* 3   10  25  17  9   24                                                  *)
(* 4   3   20  12  4   21                                                  *)
(* 5   16  8   23  15  7                                                   *)                                                                        
(***************************************************************************)