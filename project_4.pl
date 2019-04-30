%
% A0195439N
% Xin Cen
%

%
% Question One
%
% Reference
%   1. Wikipedia Eight queens puzzle
%       https://en.wikipedia.org/wiki/Eight_queens_puzzle
%   2. N Queen Problem Using Recursive Backtracking
%       https://codepumpkin.com/n-queen-problem
%

%
% Some Utilities
%

%
% get_a_solution/3
%
% Generate a solution
%
% +Nat  
%   Lower bound
%
% +Nat 
%   Upper bound
%
% -List 
%   A list of numbers from I to J
%
get_a_solution(I, I, [I]).

get_a_solution(I, J, [I| T]):-
  I < J,
  I2 is I + 1,
  get_a_solution(I2, J, T).

%
% is_safe/3
%
% Judge whether the placement is safe
%
% +Nat
%   The target queen
%
% +List
%   Other queens
%
% +D
%   Diagonal
%
is_safe(_, [], _).

is_safe(Qa, [Qb| Qn], D):-
  % Qa and Qb cannot be in the same column
  Qa =\= Qb,
  Qd is abs(Qa - Qb),
  % Also not in the diagonal
  Qd =\= D,
  D2 is D + 1,
  % Judge with another queen
  is_safe(Qa, Qn, D2).

%
% find_queen/2
%
% Recursively get a solution,
% and judge whether it is safe,
% then save the solution to a list
%
% -List
%   The position of each queen in row
%
% +Nat
%   Number of queens
%
find_queen([], _).

find_queen([Qa| Qn], Nat):-
  % Recursively get the queen
  find_queen(Qn, Nat),
  % Generate a possible solution 
  get_a_solution(1, Nat, Possible_solution),
  % Get a queen
  member(Qa, Possible_solution),
  % If the queen is placed in a safe position
  is_safe(Qa, Qn, 1).

%
% transfer/4
%
% Transfer the position in row to
% the positoin in the chessboard
%
% +List
%   List of positions in row
%
% -List
%   List of positions in the chessboard
%
% +Nat
%   Current row
%
% +Nat
%   Max row
%
transfer([], [], _, _).

transfer([Qa| Qn], [Qa2| Qn2], I, J):-
  Qa2 is I * J + Qa,
  I2 is I + 1,
  transfer(Qn, Qn2, I2, J).

%
% nqueens/2
%
% +Nat
%   The number of queens
%
% ?List
%   The queens' position in the chessboard
%
nqueens(Nat, Solution):-
  % Create an empty list of queens
  length(Raw_solution, Nat),
  % Find the queen recursively
  find_queen(Raw_solution, Nat),
  % Transfer the solution into correct position
  transfer(Raw_solution, Solution, 0, Nat).
  
