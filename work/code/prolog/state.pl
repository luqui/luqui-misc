% s is the state predicate: all stateful things go in here
% 0 is the initial state, t(0) is the next state, t(t(0)) is the next state after that, etc.

tran(t(T0), false, X) :- s(T0, X), \+ s(t(T0), X).
tran(t(T0), true,  X) :- s(t(T0), X), \+ s(T0, X).

s(0, owns(me,car)).
s(t(0), owns(thief,car)).

lost(Time, Owner, Item)   :- tran(Time, false, owns(Owner, Item)).
gained(Time, Owner, Item) :- tran(Time, true,  owns(Owner, Item)).
stolen(Time, Orig, New, Item) :-
		lost(Time, Orig, Item),
         gained(Time, New, Item).

% vim: ft=prolog :
