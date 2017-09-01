#!/Applications/SWI-Prolog.app/Contents/MacOS/swipl
/*
 * Adapted from prolog :- tutorial, by J.R. Fisher
 */

/* 
    Infix operators  and their argument precedence
    x represents an argument whose precedence is strictly lower than that
    of the operator. y represents an argument whose precedence is lower
    or equal than that of the operator. 
 */

:- op(100,xfy,'&').
:- op(150,xfx,'=>').
:- set_prolog_flag(history, 50).
:- ensure_loaded('wn_s_convert.pl').
:- ensure_loaded( 'pronto_morph_engine.pl' ).
:- ensure_loaded( 'morph_lookup.pl' ).

sentence(LF,declare(NP,VP))  -->  simple_sentence(LF,declare(NP,VP)).
sentence(LF1&LF2,conj(declare(NP1,VP1),CONJ,declare(NP2,VP2)))  -->  simple_sentence(LF1,declare(NP1,VP1)), conj(CONJ), sentence(LF2,declare(NP2,VP2)).

simple_sentence(LF,declare(NP,VP))    --> noun_phrase(Num,X,Assn,LF,NP), verb_phrase(Num,X,Assn,VP).
simple_sentence(LF,question(LC,VP))   --> locator(X,LF,LC), verb_phrase(_,X,LF,VP).
simple_sentence(LF,imperative(VP,NP)) --> verb_phrase(Num,X,Assn,VP), noun_phrase(Num,X,Assn,LF,NP).
/*
 WINOGRAD:
S -> NP,VP
NP -> Determiner, NP
NP-> Noun
NP -> Adjective, NP
NP-> NP,PP
VP-> Verb
VP -> Verb, NP
VP-> VP,PP
PP -> Preposition, NP
*/

/*
McCord MODL:
 
sent(P) --> np(X,PI,P): vp(X,Pl). 
np(X,P1,P) --> det(P2,P1,P): noun(X,P3): relclause(X,P3,P2).
np(X,P,P) --> name(X).
vp(X,P) --> transverb(X,Y,Pl): np(Y,Pl,P). 
vp(X,P) --> intransverb(X,P). 
relclause(X,Pl,Pl&P2) --> +that: vp(X,P2).
relclause(*,P,P) --> nil.
det(PI,P2,P) --> +D: $dt(D,PI,P2,P).
noun(X,P) --> +N: SnfN,X,P).
name(X) --> +X: $nm(X). 
transverb(X,Y,P) --> +V: $tv(V,X,Y,P). 
intransverb(X,P) --> +V: $iv(V,X,P).
/ * Lexicon * /
n(man,X,man(X)).
n(woman,X,woman(X)).
nm(john).
nm(mary).
 
MLGRAM:
 
 sent ==> np(X): vp(X).
 np(X) ==> det: noun(X): relclause(X).
 np(X) ==> name(X).
 vp(X) ==> transverb(X,Y): np(Y). 
 vp(X) ==> intransverb(X).
 relclause(X) ==> +that: vp(X). 
 relclause(*) ==> nil.
 det ==> +D: $dt(D,P1,P2,P): P2/P1-P.
 noun(X) ==> +N: $n(N,X,P): l-P.
 name(X) ==> +X: $nm(X).
 transverb(X,Y) ==> +V: $tv(V,X,Y,P): l-P.
 intransverb(X) ==> +V: $iv(V,X,P): l-P.
 
analyze2(Sent) <-
    sentence(Syn,Sent,nil) &
    synsem(Syn,Sems,nil) & 
    semant(top:nil,Sems,sem(*,*,LF):nil,niI) &
    outlogform(LF).
 
synsem(syn(Feas,Mods),Sems2,Sems3) <- 
    synsemlist(Mods,Sems) & 
    reorder(Sems,Semsl) & 
    modlist(Semsl,sem(Feas,id,t),Sem,Sems2,Sem:Sems3).
 
synsemlist(syn(Feas,Mods0):Mods,Sems1) <- /&
    synsem(syn(Feas,Mods0),Sems1,Sems2) &
    synsemlist(Mods,Sems2).
synsemlist((Op-LF):Mods, sem(terminal:nil,Op,LF):Sems) <- /&
    synsemlist(Mods,Sems). 
synsemlist(Nod:Mods,Sems) <-
    synsemlist(Mods,Sems). 
synsemlist(nil,nil).
 
reorder(A:L,H) <-
    reorder(L,Ll) & insert(A,L1,M).
reorder(nil,nil).
 
 
insert(A,B:L,B:Ll) <-
    prec(A,PA) & prec(B,PB) & gt(PB,PA) &/&
    insert(A,L,Li). insert(A,L,A:L).

prec(sem(terminal:*,*,*),2) <- /.
prec(sem(relc!ause:*,*,*),l) <- /.
prec(e,3).
 
mod(id-*, Sem, Sem) <- /.
mod(Sem, id-*, Sem) <- /.
mod(l-P, Op-Q, Op-R) <- and(P,Q,R). mod(P/Q-R, Op-Q, @P-R).
mod(@P-Q, Op-P, Op-Q).
 
*/


/* 
 fragments
noun_phrase(Num,X,Assn,Assn,NP)   --> pronoun(Num,X,Assn,NP).
noun_phrase(Num,X,Assn,Assn,NP)   --> proper(Num,X,Assn,NP).
noun_phrase(Num,X,Assn,LF,NP)     -->
    determiner(Num,X,Prop12,Assn,LF,Det),
    noun(Num,X,Prop1,Noun),
    relative_clause(Num,X,Prop1,Prop12,Rel),
    {build_np(Det,Noun,Mods,Rel,NP)}.

sentence(LF) -->
    noun_phrase(X,Assn,LF), verb_phrase(X,Assn).
noun_phrase(X,Assn,LF) -->
    determiner(X,Prop12,Assn,LF), noun(X,Prop1), rel_clause(X,Prop1,Prop12).
noun_phrase(X,Assn,Assn) -->
    proper_noun(X).

*/

noun_phrase(Num,X,Assn,Assn,NP)   --> pronoun(Num,X,Assn,NP).
noun_phrase(Num,X,Assn,Assn,NP)   --> proper(Num,X,Assn,NP).
noun_phrase(Num,X,Assn,LF,NP)     --> {write('adj'),}
    adjective(Num,X,Prop12,Adj),
{write('adj'),write(Num),write(X),writeln(Prop12),}
    noun_phrase(Num,X,Assn,Prop1,Noun),
{write('noun'),write(Num),write(X),write(Assn),writeln(Prop1),}
    {build_np(nil,Noun,relative_clause(nil),NP)}.
noun_phrase(Num,X,Assn,LF,NP)     -->
    determiner(Num,X,Prop12,Assn,LF,Det),
    %noun_phrase(Num,X,Assn,Prop12,Noun),
    noun(Num,X,Prop12,Noun),
    {build_np(Det,Noun,relative_clause(nil),NP)}.
%noun_phrase(Num,X,Assn,LF,noun_phrase(NP))     -->
%    noun(Num,X,Assn,Noun),
%    {build_np(nil,Noun,relative_clause(nil),NP)}.
noun_phrase(Num,X,Assn,LF,NP)     -->
    noun_phrase(Num,X,Assn,Prop1,Noun),
    preposition_phrase(Num,X,Assn,LF,PP),
    {build_np(PP,Noun,relative_clause(nil),NP)}.
noun_phrase(Num,X,Assn,LF,NP)     -->
    noun_phrase(Num,X,Assn,Prop1,Noun),
    relative_clause(Num,X,Prop1,Prop12,Rel),
    {build_np(nil,Noun,Rel,NP)}.

preposition_phrase(Num,X,Assn,LF,PP) -->
    preposition(X,Assn,Prop1,PP),
    noun_phrase(Num,X,Prop1,LF,NP).

/* Prolog rules for build_np */
build_np(nil,Noun,relative_clause(nil),noun_phrase(Noun)).
build_np(Det,Noun,relative_clause(nil),noun_phrase(Det,Noun)).
build_np(Det,Noun,relative_clause(RP,VP),noun_phrase(Det,Noun,relative_clause(RP,VP))).

verb_phrase(Num,X,LF,verb_phrase(ADV,TV,NP)) --> adverb(LF2,LF,ADV), transitive_verb(Num, X, Y, LF1, TV), noun_phrase(Num,Y,LF1,LF2,NP).
verb_phrase(Num,X,LF,verb_phrase(TV,NP))     --> transitive_verb(Num, X, Y, LF1, TV), noun_phrase(Num,Y,LF1,LF,NP).
verb_phrase(Num,X,LF,verb_phrase(IV))        --> adverb(LF1,LF,ADV), intransitive_verb(Num,X,LF1,IV).
verb_phrase(Num,X,LF,verb_phrase(ADV,IV))    --> intransitive_verb(Num,X,LF,IV).
verb_phrase(Num,X,LF,verb_phrase(PP,VP))     --> verb_phrase(Num,X,LF,VP), preposition_phrase(Num,X,LF1,LF,PP).

relative_clause(_,X,LF,LF,relative_clause(nil)) --> [].
relative_clause(Num,X,LF1,LF2,relative_clause(RP,VP)) --> relative_pronoun(X,LF1,RP), verb_phrase(Num,X,LF2,VP).

adjective(X,Prop1,LF,adjective(ADJ)) --> [ADJ], {adjective(ADJ), LF=..[ADJ,X]}.

adjective(happy).
adjective(sad).
adjective(big).
adjective(small).
adjective(old).
adjective(young).
adjective(fat).
adjective(skinny).
adjective(nice).
adjective(surly).
adjective(A) :- morphit(A,List,Out), check_list(a,List,Out,Num,Root). % s(A,_,_,a,_,_).
adjective(A) :- morphit(A,List,Out), check_list(s,List,Out,Num,Root). % s(A,_,_,s,_,_). % satellite - no antonym

locator(X,LF,locator(LC)) --> [LC], {locator(LC), LF=..[LC,X]}.
locator(which).
locator(what).
locator(where).
locator(who).
locator(when).
locator(there).

pronoun(sing,X,LF,pronoun(PN)) --> [PN], {pronoun(PN,_X), LF=..[PN,X]}.
pronoun(plu,X,LF,pronoun(PN))  --> [PN], {pronoun(_X,PN), LF=..[PN,X]}.

pronoun('I',we).
pronoun(she,they).
pronoun(he,they).
pronoun(it,they).

proper(sing,PN,_,proper(PN)) --> [PN], {proper(PN)}.
proper([Name]) :- proper(Name), !.
proper(Name) :- atom(Name), atom_codes(Name, Codes2), head(Codes2, First), char_type(First,upper), !.

relative_pronoun(X,LF,relative_pronoun(RPN)) --> [RPN], {relative_pronoun(RPN), LF=..[RPN,X]}.
relative_pronoun(that).
relative_pronoun(which).
relative_pronoun(who).
relative_pronoun(whom).

intransitive_verb(Num,X,LF,intransitive_verb(IV)) -->[IV], {intransitive_verb(IV,Num,Root), LF=..[Root,X]}.
intransitive_verb(runs,sing,run).
intransitive_verb(run,plu,run).
intransitive_verb(sits,sing,sit).
intransitive_verb(sit,plu,sit).
intransitive_verb(V,Num,Root) :- morphit(V,List,Out), check_list(v,List,Out,Num,Root).

transitive_verb(Num,X,Y,LF,transitive_verb(TV))  --> [TV], {transitive_verb(TV,Num,Root), LF=..[Root,X,Y]}.
transitive_verb(is,sing,is).
transitive_verb(are,pl,is).
transitive_verb(V,Num,Root) :- morphit(V,List,Out), check_list(v,List,Out,Num,Root).
   
adverb(Prop1,LF,adverb(ADV)) --> [ADV], {adverb(ADV,Root), LF=..[Root,Prop1]}.
adverb(really,real).
adverb(truly,true).
adverb(A,Root) :- morphit(A,List,Out), check_list(r,List,Out,Num,Root). % s(A,_,_,r,_,_).
adverb(A,Root) :- morphit(A,List,Out), check_list(s,List,Out,Num,Root). % s(A,_,_,s,_,_).
    
determiner(Num,X,Prop,Assn,LF,determiner(DET)) --> [DET], {determiner(Num,X,Prop,Assn,LF,DET)}.
determiner(sing,X,Prop,Assn,exist(X,(Prop & Assn)),a).
determiner(sing,X,Prop,Assn,exist(X,(Prop & Assn)),an).
determiner(sing,X,Prop,Assn,the(X,(Prop & Assn)),the).
determiner(plu,X,Prop,Assn,all(X,(Prop => Assn)),all).
determiner(sing,X,Prop,Assn,all(X,(Prop => Assn)),every).
determiner(plu,X,Prop,Assn,some(X,(Prop & Assn)),some).

noun(Num, X, LF, noun(N)) --> [N], {noun(N,Num,R), LF=..[R,X]}.
noun(N,Num,Root) :- morphit(N,List,Out), check_list(n,List,Out,Num,Root).

morphit(X,List,Out) :- morph_atoms_bag(X, List), morph_bag_lookup(List, Out),!.
    
preposition(X,Prop1,LF, prep(PP)) --> [PP], {preposition(PP), LF=..[PP,X]}.
preposition(under).
preposition(in).
preposition(on).
preposition(of).
preposition(to).
preposition(above).
preposition(from).
preposition(over).

conj(conj(CONJ)) --> [CONJ], {conj(CONJ)}.
conj(and).
conj(or).
conj(but).
    
check_list(_,[],[],_,_) :- fail.
check_list(PartOfSpeech,[[A]],[B],Num,R) :- check_it(PartOfSpeech,A,B,Num,R).
check_list(PartOfSpeech,[[A]|_],[B|_],Num,R) :- check_it(PartOfSpeech,A,B,Num,R).
check_list(PartOfSpeech,[_|T],[_|BT],Num,R) :- check_list(PartOfSpeech,T,BT,Num,R).
    
check_it(PartOfSpeech,[A,-s],B,sing,A) :- isadictword(PartOfSpeech,B,A),!.
check_it(PartOfSpeech,[A,-pl],B,plu,A) :- isadictword(PartOfSpeech,B,A),!.
check_it(PartOfSpeech,[A],B,plu,A)     :- isadictword(PartOfSpeech,B,A),!.
check_it(PartOfSpeech,[A],B,sing,A)    :- isadictword(PartOfSpeech,B,A),!.
isadictword(PartOfSpeech,[Root,_,_,PartOfSpeech],Root).
    
/*
 * Support stuff
 */

last_input(q).
    
input_to_atom_list(L) :-
    read_line_to_codes(user_input, Input),
    string_to_atom(Input,IA),
    ( IA == '!' -> last_input(L);
        tail_not_mark(IA, R, T),
        atomic_list_concat(XL, ',', R),
        maplist(split_atom(' '), XL, S),
        append(S, [T], L),
        asserta(last_input(L))
     ).

is_terminal_punc(.).
is_terminal_punc(?).
is_terminal_punc(!).

s_type([.],statement).
s_type([?],question).
s_type([!],imperative).
s_type(X,X).

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

nspaces(N) :- N > 0, write(' '), N1 is N - 1, nspaces(N1).
nspaces(_).

pp(X,NN) :- functor(X, F, N), !, nspaces(NN), writeln(F), NN1 is NN + 1, nspaces(NN1), ppa(X,1,N,NN1).
pp(X,NN) :- nspaces(NN), writeln(X).
ppa(X,N,T,NN) :- N =< T, !, nspaces(NN), arg(N,X,A), pp(A,NN), N1 is N + 1, NN1 is NN + 1, ppa(X,N1,T,NN1).
ppa(_,_,_,_).

definitions([]) :- !.
definitions(H) :- atom(H), definition(H),!.
definitions([H|T]) :- definition(H), !, definitions(T).

cat(n,noun).
cat(a,verb).
cat(a,adjective).
cat(r,adverb).
cat(pn,propernoun).
cat(X,X).
    
definition(Word) :-
    proper(Word),
    write(Word), write(':'), cat(pn,Cat), writeln(Cat),
    !.
    
definition(Word) :-
    s(Word,_,_,Category,_,_),
    write(Word), write(':'), cat(Category,Cat),writeln(Cat),
    g(Number,Definition),
    writeln(Definition),
    !.

parse :-
    write('Enter English input or q to quit:'),nl,
    input_to_atom_list(Input),
    headtail(Input, Root, Punctuation),
    ( Root == [q] -> halt;
        (
         s_type(Punctuation, S_type), write(S_type), write(': '), writeln(Root),
         sentence(Logical_form, Parse_form, Root, []),
         write('Logical Form: '),writeln(Logical_form),
         writeln('Parse Form: '),pp(Parse_form,0),nl,
         parse;
         write("Pardon?"),nl,parse
        )
     ).

