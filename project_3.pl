%%%%%%%%%%%%%%%%%%%%%%%%%
% Student ID: A0195439N %
% Name:       Xin Cen   %
%%%%%%%%%%%%%%%%%%%%%%%%%

:-import nth0/3 from listut.
:-import flatten/3, delete/3 from lists.

%%%%%%%%%%%%%%%%%%
% Some utilities %
%%%%%%%%%%%%%%%%%%

%
% rm_not/2
%
% Get rid of "not()"
%
% +List
%   Input a list of atoms (may contain "not()")
%
% -List
%   Output a list of atoms
%
rm_not([], []).

rm_not([Head| Tail_1], [Head| Tail_2]):-
  atom(Head),
  rm_not(Tail_1, Tail_2).

rm_not([not(Head)| Tail_1], [Head| Tail_2]):-
  rm_not(Tail_1, Tail_2).


%
% rm_true/2
%
% Remove all [true] from clauses
%
% +List
%   Input a list of lists which may contain [true]
%
% -List
%   Output a list of lists without [true]
%
rm_true([], []).

rm_true([[Head| T]| Tail_1], [[Head| T]| Tail_2]):-
  Head \= true,
  rm_true(Tail_1, Tail_2).

rm_true([[Head]| Tail_1], Tail_2):-
  Head == true,
  rm_true(Tail_1, Tail_2).


%
% detect_false/1
%
% Judge if the first element of the list is
% false
%
% +List
%   Input list
%
detect_false([Head| _]):-
  (
    Head == false->
    fail;
    true
  ).


%
% check_propositions/1
%
% Check all the propositions in Clauses,
% and pick out [] or [false]
%
% +List
%   Input a list of lists (all the clauses)
%
check_propositions(Clauses):-
  flatten(Clauses, Appended_clauses),
  rm_not(Appended_clauses, Dup_props),
  elim_dup_literal(Dup_props, Props_tmp),
  sort(0, <, Props_tmp, Props),
  % After sorting we can just judge the
  % first element
  detect_false(Props).


%
% get_first_prop/2
%
% Get the first proposition from a
% sorted list of propositions
%
% +List
%   Input a list of lists (all the clauses)
%
% -Atom
%   Output the first proposition in the list 
%
get_first_prop(Clauses, First_prop):-
  flatten(Clauses, Appended_clauses),
  rm_not(Appended_clauses, Dup_props),
  elim_dup_literal(Dup_props, Props_tmp),
  sort(0, <, Props_tmp, [First_prop| _]).


% 
% is_equal/2
%
% Judge if two lists are equal in no order
%
% +List1
%   Target list 1
%
% +List2
%   Target list 2
%
% If two lists are equal, return true,
% otherwise, fail.
%
is_equal(List_1, List_2):-
  sort(0, <, List_1, Sorted_1),
  sort(0, <, List_2, Sorted_2),
  Sorted_1 == Sorted_2.


%
% nonmember_of_lists/2
%
% Judge if a list is a member of a list of lists
% in no order
%
% +List
%   Target list
%
% +Lists
%   A list of lists
%
% If the list is not a member of the list of lists,
% return true. If is, return false.
%
nonmember_of_lists(List, Lists):-
  (
    foreach(L, Lists),
    param(List)
  do
    (
      is_equal(List, L)->
      false;
      true
    )
  ).


% 
% elim_dup_literal/2
%
% Eliminate duplicate literal
%
% +List1
%   Input clause with duplicate literals
%
% -List2
%   Output clause without duplicate literals
%
elim_dup_literal([], []).

elim_dup_literal([Head| Tail], List):-
  member(Head, Tail),
  !,
  elim_dup_literal(Tail, List).

elim_dup_literal([Head| Tail_1], [Head| Tail_2]):-
  elim_dup_literal(Tail_1, Tail_2).


% 
% detect_taut_clause/2
%
% Detect a tautological clause
%
% +List1
%   Input clause with tautology
%
% -List2
%   Output clause wihout a certain kind tautology
%
detect_taut_clause([], []).

detect_taut_clause([Head| Tail], List):-
  member(not(Head), Tail),
  !,
  detect_taut_clause([], List).

detect_taut_clause([Head| Tail_1], [Head| Tail_2]):-
  detect_taut_clause(Tail_1, Tail_2).


% 
% judge_taut_clause/3
%
% Judge if it is a tautological clause and parse it
%
% +List1
%   Original clause
%
% +List2
%   Clause parsed by "elim_taut_clause()"
%
% -List3
%   If the parsed clause is the same as original one,
%   output the original one. If not, output a cube
%
judge_taut_clause([true], [true], [true]).

judge_taut_clause(List_1, List_2, List_3):-
  length(List_1, N_1),
  length(List_2, N_2),
  !,
  ( 
    (N_2 < N_1)->
    judge_taut_clause([true], [true], List_3);
    append(List_1, [], List_3)
  ).


%
% elim_dup_clause/2
%
% Eliminate duplicate clauses
%
% +List1
%   Original clauses
%
% -List2
%   Clauses without duplicate ones
%
elim_dup_clause([], []).

elim_dup_clause([Head| Tail], List):-
  (
    nonmember_of_lists(Head, Tail)->
    false;
    !,
    elim_dup_clause(Tail, List)
  ).

elim_dup_clause([Head| Tail_1], [Head| Tail_2]):-
  elim_dup_clause(Tail_1, Tail_2).


% 
% well_form/2
%
% Get formula well-formed
%
% +List1
%   Orignial clauses
%
% -List2
%   Well-formed clauses without
%     -duplicate literals
%     -tautological clauses
%     -duplicate clauses
%     -all true clauses
%
well_form(Clauses_1, Clauses_4):-
  ( 
    foreach(Clause_1, Clauses_1), 
    foreach(Clause_2, Clauses_2)
  do
    ( 
      elim_dup_literal(Clause_1, Clause_1_1),
      detect_taut_clause(Clause_1_1, Clause_1_2),
      judge_taut_clause(Clause_1_1, Clause_1_2, Clause_2)
    )
  ),
  elim_dup_clause(Clauses_2, Clauses_3),
  rm_true(Clauses_3, Clauses_4).


%
% unit_propagate/2
%
% Remove the designated literal from all clauses
%
% +List1
%   Input the clauses (without duplicate clauses and atoms)
%
% +Atom
%   The atom to remove
%
% -List2
%   Output the completed clauses
%
unit_propagate([], _, []).

unit_propagate(Clauses_1, Literal, Clauses_2):-
  (
    foreach(Clause_1, Clauses_1),
    foreach(Clause_2, Clauses_2),
    param(Literal)
  do
    (
      delete(Literal, Clause_1, Clause_2)->
      true;
      append(Clause_1, [], Clause_2)
    )
  ).


% 
% dp/1
%
% David-Putnam algorithm
%
% +List
%   Input the original CNF
%
dp(Raw_CNF):-
  % To get the original CNF well formed
  well_form(Raw_CNF, Formed_clauses),
  % Check is there any [] or [false]
  check_propositions(Formed_clauses),
  % Find all pairs containing xn and not(xn)
  findall([Clause_1, Clause_2],
          (member(Clause_1, Formed_clauses),
          member(Clause_2, Formed_clauses),
          nth0(I, Formed_clauses, Clause_1),
          nth0(J, Formed_clauses, Clause_2),
          I < J,
          member(Prop, Clause_1),
          member(not(Prop), Clause_2)),
          Pairs_1),
  % Find all pairs containing not(xn) and xn
  findall([Clause_1, Clause_2],
          (member(Clause_1, Formed_clauses),
          member(Clause_2, Formed_clauses),
          nth0(I, Formed_clauses, Clause_1),
          nth0(J, Formed_clauses, Clause_2),
          I < J,
          member(not(Prop), Clause_1),
          member(Prop, Clause_2)),
          Pairs_2),
  % Get the two pairs together
  append(Pairs_1, Pairs_2, Pairs),
  flatten(1, Pairs, Pairs_tmp),
  % Remove duplicate ones, and the rest is those to be
  % deleted from the well formed CNF
  elim_dup_clause(Pairs_tmp, Pairs_to_delete),
  % Delete all clauses containing xn and not(xn) from
  % the well formed CNF
  subtract(Formed_clauses, Pairs_to_delete, Remained_clauses).


%
% dll_rec/1
%
% Do dll recursively (without detect [] and form clauses)
%
% +List
%   Input the clauses
%
dll_rec([]).

dll_rec(Formed_clauses):- 
  % Remove unit clause (and pure literal) with literal l
  get_first_prop(Formed_clauses, Literal_1),
  unit_propagate(Formed_clauses, Literal_1, Clauses_tmp),
  unit_propagate(Clauses_tmp, not(Literal_1), Clauses_without_l),
  % Choose a literal from the clauses without l
  get_first_prop(Clauses_without_l, Literal_2),
  % Do dll/1 recursively
  append(Clauses_without_l, [[Literal_2]], New_clauses_1),
  (
    dll_rec(New_clauses_1)->
    true;
    append(Clauses_without_l, [[not(Literal_2)]], New_clauses_2),
    dll_rec(New_clauses_2)
  ).


%
% dll/1
%
% +List
%   Input the original CNF
%
dll(Raw_CNF):-
  (
    % Check if the formula is an empty cube
    Raw_CNF == [true]->
    true;
    % To get the original CNF well formed
    well_form(Raw_CNF, Formed_clauses),
    % Check if there is any empty clause
    check_propositions(Formed_clauses),
    % Remove unit clause (and pure literal) with literal l
    get_first_prop(Formed_clauses, Literal_1),
    unit_propagate(Formed_clauses, Literal_1, Clauses_tmp),
    unit_propagate(Clauses_tmp, not(Literal_1), Clauses_without_l),
    % Choose a literal from the clauses without l
    get_first_prop(Clauses_without_l, Literal_2),
    % Do dll/1 recursively
    append(Clauses_without_l, [[Literal_2]], New_clauses_1),
    (
      dll_rec(New_clauses_1)->
      true;
      append(Clauses_without_l, [[not(Literal_2)]], New_clauses_2),
      dll_rec(New_clauses_2)
    )
  ).  


% 
% A complicated test sample
% L = [[x1, x2, x1, x3],
%      [x2, x1, x3],
%      [x4, not(x3), x5, x3],
%      [true],
%      [x1, x5, x5, x1],
%      [x5, x1, x1, x5],
%      [not(x5), x1, x2],
%      [true],
%      [x5, x1, x3],
%      [x4, x2, x5],
%      [x3, not(x5), x1],
%      [x3]].
%








