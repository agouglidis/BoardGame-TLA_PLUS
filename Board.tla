------------------------------- MODULE Board -------------------------------

(***************************************************************************)
(* The rules of the puzzle is to fill in a 5x5 matrix with consecutive     *)
(* numbers from 1 to 25. You can start from any cell in the matrix by      *)
(* placing number 1. Every next cell is selected by:                       *)
(* - jumping over 2 adjacent cells if you move left or right or up or down *)
(*    or                                                                   *) 
(* - jumping over 1 adjacent cell if you move diagonally up right or       *)
(*   diagonally up left or diagonally down right or diagonally down left   *)
(*                                                                         *)
(* When the 5x5 problem is solved symmetric solutions can be combined t    *)
(* solve bigger problems e.g. 10x10                                        *)
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

EXTENDS TLC, Sequences, Integers, FiniteSets

(* --algorithm board_game


variables 
    (* Define the size of the x and y dimensions of the matrix *)
    size_x = 5;
    size_y = 5; 
    
    (* Set a board using the cartesian product *)
    board = (1..size_x) \X (1..size_y);
    
    (* Set to keep track of visited cells *)
    visited = {};
    
    (* variables to keep the current cell coordinates *)
    x \in 1..size_x;
    y \in 1..size_y;
    
    (* A sequence to keep track of the cells in the way these are visited *)
    solution = <<>>;

begin

(* This is a label for the first step *)
START:
    (* Select a random cell *)
    x := RandomElement(1..size_x);
    y := RandomElement(1..size_y); 
    
    (* Insert the coordinates of the cell in the set of visited cells *)
    visited := visited \union {<<x, y>>};
    
    (* Append the current cell coordinates in the sequence *)
    solution := solution \o (<<x, y>>);
    
(* This is the every next step label *)    
MOVE:
 while TRUE do 
    (* Create different behaviours for any potential next move *)
    either
        (* ------ Jump 2 adjacent cells right ------               *)
        (* Check if the new x value doesn't exceeds size_x and     *) 
        (*  new coordinates are in the boundaries of the board and *) 
        (*  new coordinates are not visited before                 *)
        if x+3 <= size_x /\ <<x+3, y>> \in board /\ <<x+3, y>> \notin visited then 
            (* Mark as visited *)
            visited := visited \union {<<x+3, y>>};
            
            (* Assign the new value*)
            x := x+3;
            
            (* Append the cell's coordinated to the solution sequence *)
            solution := solution \o <<x, y>>;
        end if;
    or
        (* ------ Jump 2 adjacent cells left ------ *) 
        if x-3 >=1 /\ <<x-3, y>> \in board /\ <<x-3, y>> \notin visited then 
            visited := visited \union {<<x-3, y>>};
            x := x-3;
            solution := solution \o <<x, y>>;
        end if;
    or 
        (* ------ Jump 2 adjacent cells up 2 ------ *)
        if y-3 >=1 /\ <<x, y-3>> \in board /\ <<x, y-3>> \notin visited then 
            visited := visited \union {<<x, y-3>>};
            y := y-3;                        
            solution := solution \o <<x, y>>;
        end if;        
    or 
        (* ------ Jump 2 adjacent cells down ------ *)
        if y+3 <= size_y /\ <<x, y+3>> \in board /\ <<x, y+3>> \notin visited then 
            visited := visited \union {<<x, y+3>>};
            y := y+3;
            solution := solution \o <<x, y>>;
        end if;
    or         
        (* ------ Jump 1 cell diagonally up right ------ *)
        if x+2 <= size_x /\ y-2 >=1 /\ <<x+2, y-2>> \in board /\ <<x+2, y-2>> \notin visited then 
            visited := visited \union {<<x+2, y-2>>};
            x := x+2;
            y := y-2;  
            solution := solution \o <<x, y>>;  
        end if;
    or  
        (* ------ Jump 1 cell diagonally up left ------ *)
        if x-2 >= 1 /\ y-2 >=1 /\ <<x-2, y-2>> \in board /\ <<x-2, y-2>> \notin visited then 
            visited := visited \union {<<x-2, y-2>>};
            x := x-2;
            y := y-2;            
            solution := solution \o <<x, y>>;
        end if;
    or         
        (* ------ Jump 1 cell diagonally down right ------ *)    
        if x+2 <= size_x /\ y+2 <= size_y /\ <<x+2, y+2>> \in board /\ <<x+2, y+2>> \notin visited then 
            visited := visited \union {<<x+2, y+2>>};    
            x := x+2;
            y := y+2;
            solution := solution \o <<x, y>>;
        end if;
    or       
        (* ------ Jump 1 cell diagonally down left ------ *)    
        if x-2 >= 1 /\ y+2 >= 1 /\ <<x-2, y+2>> \in board /\ <<x-2, y+2>> \notin visited then 
            visited := visited \union {<<x-2, y+2>>};
            x := x-2;
            y := y+2;
            solution := solution \o <<x, y>>;
        end if;                        
    end either;
    (* Create a new label *)
    CHECK:
        (* This assertion will check is all cells are visited using the above rules       *)
        (*  and report it as an error. The full solution will be in the solution sequence *)
        assert Cardinality(visited) # size_x*size_y;
 end while;            
 end algorithm; *)
\* BEGIN TRANSLATION (chksum(pcal) = "f6bbccb" /\ chksum(tla) = "7a5d63cb")
VARIABLES size_x, size_y, board, visited, x, y, solution, pc

vars == << size_x, size_y, board, visited, x, y, solution, pc >>

Init == (* Global variables *)
        /\ size_x = 5
        /\ size_y = 5
        /\ board = (1..size_x) \X (1..size_y)
        /\ visited = {}
        /\ x \in 1..size_x
        /\ y \in 1..size_y
        /\ solution = <<>>
        /\ pc = "START"

START == /\ pc = "START"
         /\ x' = RandomElement(1..size_x)
         /\ y' = RandomElement(1..size_y)
         /\ visited' = (visited \union {<<x', y'>>})
         /\ solution' = solution \o (<<x', y'>>)
         /\ pc' = "MOVE"
         /\ UNCHANGED << size_x, size_y, board >>

MOVE == /\ pc = "MOVE"
        /\ \/ /\ IF x+3 <= size_x /\ <<x+3, y>> \in board /\ <<x+3, y>> \notin visited
                    THEN /\ visited' = (visited \union {<<x+3, y>>})
                         /\ x' = x+3
                         /\ solution' = solution \o <<x', y>>
                    ELSE /\ TRUE
                         /\ UNCHANGED << visited, x, solution >>
              /\ y' = y
           \/ /\ IF x-3 >=1 /\ <<x-3, y>> \in board /\ <<x-3, y>> \notin visited
                    THEN /\ visited' = (visited \union {<<x-3, y>>})
                         /\ x' = x-3
                         /\ solution' = solution \o <<x', y>>
                    ELSE /\ TRUE
                         /\ UNCHANGED << visited, x, solution >>
              /\ y' = y
           \/ /\ IF y-3 >=1 /\ <<x, y-3>> \in board /\ <<x, y-3>> \notin visited
                    THEN /\ visited' = (visited \union {<<x, y-3>>})
                         /\ y' = y-3
                         /\ solution' = solution \o <<x, y'>>
                    ELSE /\ TRUE
                         /\ UNCHANGED << visited, y, solution >>
              /\ x' = x
           \/ /\ IF y+3 <= size_y /\ <<x, y+3>> \in board /\ <<x, y+3>> \notin visited
                    THEN /\ visited' = (visited \union {<<x, y+3>>})
                         /\ y' = y+3
                         /\ solution' = solution \o <<x, y'>>
                    ELSE /\ TRUE
                         /\ UNCHANGED << visited, y, solution >>
              /\ x' = x
           \/ /\ IF x+2 <= size_x /\ y-2 >=1 /\ <<x+2, y-2>> \in board /\ <<x+2, y-2>> \notin visited
                    THEN /\ visited' = (visited \union {<<x+2, y-2>>})
                         /\ x' = x+2
                         /\ y' = y-2
                         /\ solution' = solution \o <<x', y'>>
                    ELSE /\ TRUE
                         /\ UNCHANGED << visited, x, y, solution >>
           \/ /\ IF x-2 >= 1 /\ y-2 >=1 /\ <<x-2, y-2>> \in board /\ <<x-2, y-2>> \notin visited
                    THEN /\ visited' = (visited \union {<<x-2, y-2>>})
                         /\ x' = x-2
                         /\ y' = y-2
                         /\ solution' = solution \o <<x', y'>>
                    ELSE /\ TRUE
                         /\ UNCHANGED << visited, x, y, solution >>
           \/ /\ IF x+2 <= size_x /\ y+2 <= size_y /\ <<x+2, y+2>> \in board /\ <<x+2, y+2>> \notin visited
                    THEN /\ visited' = (visited \union {<<x+2, y+2>>})
                         /\ x' = x+2
                         /\ y' = y+2
                         /\ solution' = solution \o <<x', y'>>
                    ELSE /\ TRUE
                         /\ UNCHANGED << visited, x, y, solution >>
           \/ /\ IF x-2 >= 1 /\ y+2 >= 1 /\ <<x-2, y+2>> \in board /\ <<x-2, y+2>> \notin visited
                    THEN /\ visited' = (visited \union {<<x-2, y+2>>})
                         /\ x' = x-2
                         /\ y' = y+2
                         /\ solution' = solution \o <<x', y'>>
                    ELSE /\ TRUE
                         /\ UNCHANGED << visited, x, y, solution >>
        /\ pc' = "CHECK"
        /\ UNCHANGED << size_x, size_y, board >>

CHECK == /\ pc = "CHECK"
         /\ Assert(Cardinality(visited) # size_x*size_y, 
                   "Failure of assertion at line 141, column 9.")
         /\ pc' = "MOVE"
         /\ UNCHANGED << size_x, size_y, board, visited, x, y, solution >>

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == pc = "Done" /\ UNCHANGED vars

Next == START \/ MOVE \/ CHECK
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(pc = "Done")

\* END TRANSLATION 
 
=============================================================================
\* Modification History
\* Last modified Wed Mar 24 21:57:16 GMT 2021 by agouglidis
\* Created Tue Mar 23 17:29:45 GMT 2021 by agouglidis
