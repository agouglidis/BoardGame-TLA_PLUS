# BoardGame-TLA_PLUS
 Solution to a puzzle game using PlusCal/TLA+

The rules of the puzzle is to fill in a 5x5 matrix with consecutive numbers from 1 to 25. You can start from any cell in the matrix by placing number 1. Every next cell is selected by:                       

- jumping over 2 adjacent cells if you move left or right or up or down  
- jumping over 1 adjacent cell if you move diagonally up right or diagonally up left or diagonally down right or diagonally down left   

When the 5x5 problem is solved, symmetric solutions can be combined to solve bigger problems e.g. 10x10.

