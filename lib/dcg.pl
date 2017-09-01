#!/Applications/SWI-Prolog.app/Contents/MacOS/swipl

/* this is to define infix operators  and their argument precedence
   x represents an argument whose precedence is strictly lower than that
   of the operator. y represents an argument whose precedence is lower 
   or equal than that of the operator. */

:- op(100,xfy,'&').
:- op(150,xfx,'=>').

/* when using sentence we need to pass 3 arguments, 
   the first will match S in the head of the DGC clause
   the second is the list containing the words in the sentence
   the third is the empty list.
   Example:
     sentence(Meaning, [every,man,that,paints,likes,monet],[])
*/

sentence(LF) -->
	noun_phrase(X,Assn,LF), verb_phrase(X,Assn).
noun_phrase(X,Assn,LF) -->
	determiner(X,Prop12,Assn,LF), noun(X,Prop1), rel_clause(X,Prop1,Prop12).
noun_phrase(X,Assn,Assn) --> 
	proper_noun(X).

verb_phrase(X,Assn) --> 
	trans_verb(X,Y,Assn1), noun_phrase(Y,Assn1,Assn).
verb_phrase(X,Assn) --> 
	intrans_verb(X,Assn).
rel_clause(X,Prop1,Prop1 and Prop2) --> 
	[that],verb_phrase(X,Prop2).
rel_clause(_,Prop1,Prop1) --> [].

determiner(X,Prop,Assn,all(X,(Prop => Assn))) --> [every].
determiner(X,Prop,Assn,all(X,(Prop => Assn))) --> [all].
determiner(X,Prop,Assn,exists(X,Prop & Assn)) --> [a].

noun(X,man(X)) --> [man].
noun(X,man(X)) --> [men].
noun(X,woman(X)) --> [woman].
noun(X,woman(X)) --> [women].
noun(X,mortal(X)) --> [mortal].

proper_noun(PN) --> [PN], {proper(PN)}.
proper(Name) :- atom_codes(Name, Codes2), head(Codes2, First), char_type(First,upper),!.

trans_verb(X,Y,like(X,Y)) --> [likes].
trans_verb(X,Y,admire(X,Y)) --> [admires].
trans_verb(X,Y,exist(X,Y)) --> [is].
trans_verb(X,Y,exist(X,Y)) --> [are].

intrans_verb(X,paint(X)) --> [paints].

/*
 * Support stuff
 */

input_to_atom_list(L) :-
    read_line_to_codes(user_input, Input),
    string_to_atom(Input,IA),
    tail_not_mark(IA, R, T),
    atomic_list_concat(XL, ',', R),
    maplist(split_atom(' '), XL, S),
    append(S, [T], L).

is_terminal_punc(.).
is_terminal_punc(?).
is_terminal_punc(!).

split_atom(S, A, L) :- atomic_list_concat(XL, S, A), delete(XL, '', L).

% if tale is ? or ! or . then remove
% A:Atom, R:Removed, T:special mark
tail_not_mark(A, R, T) :- atom_concat(R, T, A), is_terminal_punc(T),!.
tail_not_mark(A, R, '') :- A = R.

headtail([H|T], H, T).
head([H|_], H).

capitalize([], []).
capitalize([H1|T], [H2|T]) :- code_type(H2, to_upper(H1)).

trim_period([.],[]).
trim_period([X|R],[X|T]) :- trim_period(R,T).

parse :-
    write('Enter English input or q to quit:'),nl,
    input_to_atom_list(Input),
    headtail(Input, Root, Punctuation),
    write(Root),
    write(Punctuation),
    nl,
    ( Root == q -> !
       ;
        sentence(Logical_form, Root, []),
        write(Logical_form),
        nl,parse).

