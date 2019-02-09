%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% Author: Cen XIN                                                         %

% Date: 9th Feb 2019                                                      %

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% Use this template to write your program                                 %

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% This section declares prefix and infix notations                        %

% as well as precedence of connectives                                    %

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

:-op(1200, xfy, implies).

:-op(600, xfy, and).

:-op(500, xfy, or).

:-op(500, xfy, xor).

:-op(100, fy, not).


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% interpretation/2                                                        %

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%



% Write your code here.
interpretation(top, true).

interpretation(bot, false).

interpretation(not A, true):-
  interpretation(A, false).

interpretation(not A, false):-
  interpretation(A, true).

interpretation(A and B, true):-
  interpretation(A, true), 
  interpretation(B, true).

interpretation(A and B, false):-
  interpretation(A, false).

interpretation(A and B, false):-
  interpretation(B, false).

interpretation(A or B, true):-
  interpretation(A, true).

interpretation(A or B, true):-
  interpretation(B, true).

interpretation(A or B, false):-
  interpretation(A, false), 
  interpretation(B, false).

interpretation(A implies B, true):-
  interpretation(A, true),
  interpretation(B, true).

interpretation(A implies B, true):-
  interpretation(A, false),
  interpretation(B, true).

interpretation(A implies B, true):-
  interpretation(A, false),
  interpretation(B, false).

interpretation(A implies B, false):-
  interpretation(A, true),
  interpretation(B, false).

interpretation(A xor B, true):-
  interpretation((A and not B) or ((not A) and B), true).

interpretation(A xor B, false):-
  interpretation(A, true),
  interpretation(B, true).

interpretation(A xor B, false):-
  interpretation(A, false),
  interpretation(B, false).
  

% interpretation(top and top, true). % should succeeds.

% interpretation(bot or bot, false). % should succeeds.

% interpretation(top xor bot, true). % should succeeds.

% interpretation(top xor bot, X). % should succeed with X = true.



%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% propositions/2                                                          %

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%



% Write your code here.
propositions(A, [A]):-
  atom(A),
  A \= top,
  A \= bot.

propositions(A, []):-
  A == top.

propositions(A, []):-
  A == bot.

propositions(not A, L3):-
  propositions(A, L1), 
  append(L1, [], L2),
  rm_dup(L2, L3).

propositions(A and B, L4):-
  propositions(A, L1), 
  propositions(B, L2), 
  append(L1, L2, L3),
  rm_dup(L3, L4).

propositions(A or B, L4):-
  propositions(A, L1), 
  propositions(B, L2), 
  append(L1, L2, L3),
  rm_dup(L3, L4).

propositions(A implies B, L4):-
  propositions(A, L1), 
  propositions(B, L2), 
  append(L1, L2, L3),
  rm_dup(L3, L4).

propositions(A xor B, L4):-
  propositions(A, L1),
  propositions(B, L2), 
  append(L1, L2, L3),
  rm_dup(L3, L4).

rm_dup([], []).

rm_dup([H|T], L):-
  member(H, T),
  !,
  rm_dup(T, L).

rm_dup([H|T], [H|C]):-
  rm_dup(T, C).


% propositions(x1 xor x2, L). % should succeed with L = [x1, x2].

% propositions(not x1 and  x1, L). % should succeed with L = [x1].



%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% assign/4                                                                %

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%



% Write your code here.
assign(A, A, true, top):-
  atom(A).

assign(A, B, true, A):-
  A \= B,
  atom(A).

assign(A, A, false, bot):-
  atom(A).

assign(A, B, false, A):-
  A \= B,
  atom(A).

assign(not L1, A, V, not L2):-
  assign(L1, A, V, L2).

assign(L1_1 and L1_2, A, V, L2_1 and L2_2):-
  assign(L1_1, A, V, L2_1),
  assign(L1_2, A, V, L2_2).

assign(L1_1 or L1_2, A, V, L2_1 or L2_2):-
  assign(L1_1, A, V, L2_1),
  assign(L1_2, A, V, L2_2).

assign(L1_1 implies L1_2, A, V, L2_1 implies L2_2):-
  assign(L1_1, A, V, L2_1),
  assign(L1_2, A, V, L2_2).

assign(L1_1 implies L1_2, A, V, L2_1 implies L2_2):-
  assign(L1_1, A, V, L2_1),
  assign(L1_2, A, V, L2_2).

assign(L1_1 xor L1_2, A, V, L2_1 xor L2_2):-
  assign(L1_1, A, V, L2_1),
  assign(L1_2, A, V, L2_2).


% assign(x1 xor x2, x1, true, L). 
% should succeed with F = top xor x2

% assign(x1 implies x1, x1, true, L). 
% should succeed with F = top implies top



%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% assignment/3                                                            %

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%



% Write your code here.

assignment(Formula, true, []):-
  propositions(Formula, []),
  interpretation(Formula, true).

assignment(Formula, false, []):-
  propositions(Formula, []),
  interpretation(Formula, false).

assignment(Formula, TruthValue, [[FirstProp, Value]| ListofAssign]):-
  propositions(Formula, [FirstProp| ListofProps]),
  assign(Formula, FirstProp, Value, FormulawithAssign),
  assignment(FormulawithAssign, TruthValue, ListofAssign).

% assignment(not (x1 and not x2), T, L)
% should succeeds 4 times with the corresponding truth values.



%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% Tests (add the tests that you are using)                                %

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% assignment(x1 and x2, true, L)
% should succeed with L = [[x1, true], [x2, true]].
%
% assignment(x1 or x2, false, [[x1, false], [x2, false]])
% should succeed.
%
% assignment(not (x1 and not x2), false, L)
% should succeed with L = [[x1, true], [x2, false]].
%
% assignment(x1 implies x2, T, L)
% should succeed with:
%   T = true
%   L = [[x1, true], [x2, true]]
%   T = false
%   L = [[x1, true], [x2, false]]
%   T = true
%   L = [[x1, false], [x2, true]]
%   T = true
%   L = [[x1, false], [x2, false]]
%
% assignment(x xor y, T, L)
% should succeed with:
%   T = true
%   L = [[x, true], [y, false]]
%   T = true
%   L = [[x, false], [y, true]]
%   T = false
%   L = [[x, true], [y, true]]
%   T = false
%   L = [[x, false], [y, false]]
%
% assignment(not y xor x and z, T, L)
% should succeed with:
%   T = true
%   L = [[y, true], [x, true], [z, true]]
%   T = false
%   L = [[y, true], [x, true], [z, false]]
%   T = false
%   L = [[y, true], [x, false], [z, true]]
%   T = false
%   L = [[y, true], [x, false], [z, false]]
%   T = false
%   L = [[y, false], [x, true], [z, true]]
%   T = false
%   L = [[y, false], [x, true], [z, false]]
%   T = true
%   L = [[y, false], [x, false], [z, true]]
%   T = false
%   L = [[y, false], [x, false], [z, false]]
