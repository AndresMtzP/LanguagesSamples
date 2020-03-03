%Define main tower predicate using FD Domain Solver, Include Early Exit Cases.
tower(N, _, _) :- (N < 0), !, fail.
tower(0, [], counts([],[],[],[])).
tower(N, T, C) :- 
	%call predicates to create constraints through fd solver and length predicate.	
	length(T, N),
	fd_solve_grid(N, T, N),
	transpose(T, TPrime),
	fd_solve_grid(N, TPrime, N),
	maplist(fd_labeling, T),

	%define C as Count structure and call constraints on the elements
	C = counts(Top, Bottom, Left, Right),
 	length(Top, N),
 	fd_domain(Top, 1, N),
	length(Bottom, N),
	fd_domain(Bottom, 1, N),
	length(Left, N),
	fd_domain(Left, 1, N),
	length(Right, N),
	fd_domain(Right, 1, N),
	
	%Once the main constraints have been set, we call predicate to find solution to the puzzle
	towerhelper(T, Left, Right),
	towerhelper(TPrime, Top, Bottom).

%definition of puxxle helper predicate.
towerhelper([], [], []).
towerhelper([H|T], [LCons|LTail], [RCons|RTail]) :-
	viewtowers(H, LCons),
	(reverse(H, RH, []), viewtowers(RH, RCons)),
	towerhelper(T, LTail, RTail).

%This predicate packages all the fd_domain predicates needed by calling the constraints on each row
fd_solve_grid(_,_,N) :- N < 0, !, fail.
fd_solve_grid(_, [], 0).
fd_solve_grid(N, [Row|GridTail], Count) :-
	fd_solve_row(N, Row),
	DCount is Count - 1,
	fd_solve_grid(N, GridTail, DCount).
	
%This predicate indicates the constraints for each row of the puzzle grid.
fd_solve_row(N, Row) :-
	length(Row,N),
	fd_domain(Row, 1, N),
	fd_all_different(Row).
	
%Predicate used to determine if all elements of a row are unique, fail early if we find a duplicate
unique([]).
unique([H|Tail]) :- member(H, Tail), !, fail.
unique([_|Tail]) :- unique(Tail).

%This predicate packages the conditions for each of the rows in the puzzle grid, for plain solution
plainlist(List, N) :-
	length(List, N),
	maplist(between(1, N), List),
	unique(List).

%simlpe predicate to increment a variable
increment(X, XI) :-
	XI is X + 1.

%simple predicate to decrement a variable
decrement(X, XD) :-
	XD is X - 1.

%Main predicate for part 2 of assignment. This does the same as the tower predicate, but does not use 
%fd_solver, instead, constraints are determined through helper function for each row.
plain_tower(N, _, _) :- (N < 0), !, fail.
plain_tower(0, [], counts([],[],[],[])).
plain_tower(N, T, C) :- 
	length(T, N),
	(elementat(T, R, 0), length(R,N)),
	transpose(T, TPrime),
	length(TPrime, N),
	C = counts(Top, Bottom, Left, Right),
 	length(Top, N),
	length(Bottom, N),
	length(Left, N),
	length(Right, N),

	plaintowerhelper(T, Left, Right, N),
	plaintowerhelper(TPrime, Top, Bottom, N).

%helper predicate, determine constraints for row, then call our view_tower predicate to confirm correctnes
%for puzzle
plaintowerhelper([], [], [], _).
plaintowerhelper([H|T], [LCons|LTail], [RCons|RTail], N) :-
	plainlist(H, N),
	viewtowers(H, LCons),
	(reverse(H, RH, []), viewtowers(RH, RCons)),
	plaintowerhelper(T, LTail, RTail, N).

%Reverse Append predicate, as seen in lecture, linear complexity by using Aggregate method
reverse([],RL,RL).
reverse([H|T],RL,Aggregate) :- reverse(T,RL,[H|Aggregate]).

%predicate to find an element at an index of a row.
elementat([H|_], H, 0).
elementat([_|T], Res, I) :- I > 0, decrement(I, ID), elementat(T, Res, ID).

%Predicate used by transpose predicate, gets a grid and returns a column as a row, given the column index
columnasrow([], _, []).
columnasrow([H|T], Index, [El|R]) :- elementat(H, El, Index), columnasrow(T, Index, R).

%helper predicate for transposing grid
transposehelper(_, I, I, _). 
transposehelper(Grid, RowLength, ColumnIndex, [ColRow|GridTail]) :-  
	columnasrow(Grid, ColumnIndex, ColRow),
	increment(ColumnIndex, ColumnIndexI),
	transposehelper(Grid, RowLength, ColumnIndexI, GridTail).

%Transpose predicate is used to analyze the main grids coluymns as lists, so it 
%can be processes by viewtowers predicate
transpose([], []).
transpose([H|Grid], TGrid) :- 
	length(H, L),
	transposehelper([H|Grid], L, 0, TGrid).


%This predicate iterates over a row, given a puzzle constraint and finds a row,
%wherein the puzzle constraint is correct
viewtowers(Towers, Constraint) :- viewtowershelper(Towers, Constraint, 0, 0).
viewtowershelper([], Constraint, Constraint, _).
viewtowershelper([H|Tail], Constraint, Count, Prevmax) :- ((H > Prevmax), increment(Count, CountI), viewtowershelper(Tail, Constraint, CountI, H));
														  ((H < Prevmax), viewtowershelper(Tail, Constraint, Count, Prevmax)).

%Time the tower predicate using statistics predicate, the test case was determined as the 
%last found solution of predicate call tower(5,T,C)
time_tower(Time) :-
	statistics(real_time, [Start1|_]),
	tower(5, _, counts([1,2,3,2,4],[5,2,1,2,2],[1,2,2,3,3],[5,2,2,1,3])),
	statistics(real_time, [Start2|_]),
	Time is Start2 - Start1.

%Time the plain_tower predicate using the the exact same calls as with tower timer, to generate a good ratio.
time_plain_tower(Time) :-
	statistics(real_time, [Start1|_]),
	plain_tower(5, _, counts([1,2,3,2,4],[5,2,1,2,2],[1,2,2,3,3],[5,2,2,1,3])),
	statistics(real_time, [Start2|_]),
	Time is Start2 - Start1.

%speedup result is simply the time of plain_tower divided by the time of tower, to get a ratio
speedup(Res) :- 
	time_tower(T1),
	time_plain_tower(T2),
	Res is T2 / T1.

%Ambiguous finds a solution for tower, then tries to find a new solution for which the grid solution differs,
% while the constraints stay the same, representing a tower puzzle with more than one solution.
ambiguous(N, C, T1, T2) :-
  tower(N, T1, C),
  tower(N, T2, C),
  \+ T1 = T2.