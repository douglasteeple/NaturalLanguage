#!/Applications/SWI-Prolog.app/Contents/MacOS/swipl

/* this is to define infix operators  and their argument precedence
x represents an argument whose precedence is strictly lower than that
of the operator. y represents an argument whose precedence is lower
or equal than that of the operator. */
:- op(100,xfy,and).
:- op(150,xfx,'=>').

sentence(declare(NP,VP))  -->  simple_sentence(declare(NP,VP)).
sentence(conj(declare(NP1,VP1),CONJ,declare(NP2,VP2)))  -->  simple_sentence(declare(NP1,VP1)), conj(CONJ), sentence(declare(NP2,VP2)).

simple_sentence(declare(NP,VP)) --> noun_phrase(Num,NP), verb_phrase(Num,VP).
simple_sentence(question(NP,VP)) --> verb_phrase(Num,NP), noun_phrase(Num,VP).
simple_sentence(imperative(NP,VP)) --> verb_phrase(Num,NP), noun_phrase(Num,VP).

noun_phrase(Num,noun_phrase(PN)) --> pronoun(Num,PN).
noun_phrase(Num,proper(PN)) --> proper(Num,PN).
noun_phrase(Num,NP) -->
   determiner(Num,Det),
   noun(Num,N),
   relative_clause(Num,Rel),
   {build_np(Det,N,Rel,NP)}. /* embedded Prolog goal */

/* Prolog rules for build_np */
build_np(Det,N,relative_clause(nil),noun_phrase(Det,N)).
build_np(Det,N,relative_clause(RP,VP),noun_phrase(Det,N,relative_clause(RP,VP))).

verb_phrase(Num,verb_phrase(TV,NP)) --> transitive_verb(Num,TV), noun_phrase(_,NP).
verb_phrase(Num,verb_phrase(IV)) --> intransitive_verb(Num,IV).

relative_clause(_Num,relative_clause(nil)) --> [].
relative_clause(Num,relative_clause(RP,VP)) --> relative_pronoun(RP), verb_phrase(Num,VP).

pronoun(sing,pronoun(PN)) --> [PN], {pronoun(PN,_X)}.
pronoun(plu,pronoun(PN)) --> [PN], {pronoun(_X,PN)}.

pronoun('I',we).
pronoun(she,they).
pronoun(he,they).
pronoun(it,they).

proper(sing,proper(PN)) --> [PN], {proper(PN)}.
proper(Name) :- atom_codes(Name, Codes2), head(Codes2, First), char_type(First,upper),!.

relative_pronoun(relative_pronoun(RPN)) --> [RPN], {relative_pronoun(RPN)}.
relative_pronoun(that).
relative_pronoun(which).
relative_pronoun(who).
relative_pronoun(whom).

intransitive_verb(sing,intransitive_verb(IV)) -->[IV], {intransitive_verb(IV,_X)}.
intransitive_verb(plu,intransitive_verb(IV)) --> [IV], {intransitive_verb(_X,IV)}.
intransitive_verb(runs,run).
intransitive_verb(sits,sit).

determiner(Num,determiner(DET)) --> [DET], {determiner(Num,DET)}.
determiner(sing,a).
determiner(sing,an).
determiner(sing,the).
determiner(plu,all).
determiner(sing,every).
determiner(plu,some).

noun(sing,noun(N)) --> [N], {noun(N,_X)}.
noun(plu,noun(N)) --> [N], {noun(_X,N)}.

noun(book,books).
noun(girl,girls).
noun(boy,boys).
noun(man,men).
noun(woman,women).

transitive_verb(sing,transitive_verb(TV)) --> [TV], {transitive_verb(TV,_X)}.
transitive_verb(plu,transitive_verb(TV))  --> [TV], {transitive_verb(_X,TV)}.

transitive_verb(gives,give).
transitive_verb(reads,read).
transitive_verb(likes,like).
transitive_verb(is,are).

conj(conj(CONJ)) --> [CONJ], {conj(CONJ)}.
conj(and).
conj(or).
conj(but).

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
        sentence(Parse_form, Root, []),
        write(Parse_form), 
        nl,parse).

