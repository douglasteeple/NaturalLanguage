#! /Applications/SWI-Prolog.app/Contents/MacOS/swipl

/*
 * Adapted from Gurney
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
dt(a,PI,P2,ex(Pl,P2)).
dt(all,PI,P2,all(Pl,P2)).
tv(loves,X,Y,love(X,Y)).
iv(lives,X,live(X)).
 
MLGRAM:
 
 sent --> np(X), vp(X).
 np(X) --> det, noun(X), relclause(X).
 np(X) --> name(X).
 vp(X) --> transverb(X,Y), np(Y).
 vp(X) --> intransverb(X).
 relclause(X) --> [that], vp(X).
 relclause(*) --> [].
 det --> [D], {dt(D,P1,P2,P)}, P2/P1-P.
noun(X) --> [N], {n(N,X,P)}, l-P.
name(X) --> [X], {nm(X)}.
transverb(X,Y) --> [V], {tv(V,X,Y,P)}, l-P.
intransverb(X) --> [V], {iv(V,X,P)}, l-P.
*/

:- op(100,xfx,':').
:- op(100,xfx,'-').
:- op(200,xf,'@').

analyze2(Sent) :-
    sentence(Syn,Sent,[]),
    synsem(Syn,Sems,[]),
    semant([top],Sems,[sem(_,_,LF)|[]],[]),
    outlogform(LF).
 
synsem(syn(Feas,Mods),Sems2,Sems3) :-
    synsemlist(Mods,Sems), 
    reorder(Sems,Semsl), 
    modlist(Semsl,sem(Feas,id,t),Sem,Sems2,[Sem|Sems3]).
 
synsemlist([syn(Feas,Mods0)|Mods],Sems1) :- !,
    synsem(syn(Feas,Mods0),Sems1,Sems2),
    synsemlist(Mods,Sems2).

synsemlist([(Op-LF)|Mods], [sem(terminal,Op,LF)|Sems]) :- !,
    synsemlist(Mods,Sems).

synsemlist(Mod:Mods,Sems) :-
    synsemlist(Mods,Sems).

synsemlist(nil,nil).
 
reorder(A:L,H) :-
    reorder(L,Ll), insert(A,L1,M).
reorder(nil,nil).
 
 
insert(A,[B|L],[B|Ll]) :-
    prec(A,PA), prec(B,PB), gt(PB,PA),!,
    insert(A,L,Li).
insert(A,L,[A|L]).

prec(sem([terminal|_]),2) :- !.
prec(sem([relclause|_]),l) :- !.
prec(e,3).
 
mod(id-_, Sem, Sem) :- !.
mod(Sem, id-_, Sem) :- !.
mod(l-P, Op-Q, Op-R) :- and(P,Q,R).
mod(P/Q-R, Op-Q, @P-R).
mod(@P-Q, Op-P, Op-Q).

/* Lexicon */
n(man,X,man(X)).
n(woman,X,woman(X)).
nm(john).
nm(mary).
dt(a,PI,P2,ex(Pl,P2)).
dt(all,PI,P2,all(Pl,P2)).
tv(loves,X,Y,love(X,Y)).
iv(lives,X,live(X)).


/* Gurney: */

% ------------------------------------------------------------------------------------------------
% Sentences and Independent Clauses
% ------------------------------------------------------------------------------------------------
% independent clauses are sentences

% where is question?
sentence(LF, question(Phrase)) -->
    relative_pronoun(rpron(P), Number, Person, Case),
    sense_verb_phrase(VPhr, Number,Person),
    direct_object(Object, Number, Person),
    {Phrase=..[P,VPhr,Object]}.

% is X a Y?
sentence(LF, question(is(VPhr,Object1,Object2))) -->
    sense_verb_phrase(VPhr, Number,Person),
    direct_object(Object1, Number, Person),
    indirect_object(Object2, Number, Person).

% imperative
sentence(LF, imperative(VPhr, Object)) -->
    verb_phrase(VPhr,singular,first,intransitive),
    direct_object(Object, Number, Person).
 
sentence(LF, imperative(VPhr, Object, Object2)) -->
    verb_phrase(VPhr,singular,first,transitive),
    direct_object(Object, Number, Person),
    indirect_object(Object2, Number, Person).

% statement
sentence(LF, statement(Sent)) -->
    independent_clause(LF, Sent).

% if/then statements
sentence(if(LF1,LF2), implies(Sentl, Sent2)) -->
    [if],
    independent_clause(LF1, Sentl),
    [then],
    independent_clause(LF2, Sent2).
 
sentence(if(LF1,LF2), implies(Sentl, Sent2)) -->
    [if],
    independent_clause(LF1, Sentl),
    independent_clause(LF2, Sent2).
 
% ------------------------------------------------------------------------------------------------
% canonical independent clause
% ------------------------------------------------------------------------------------------------
 
independent_clause(LF, clause(Subj, VPhr)) -->
    subject(Subj, Number, Person),
    predicate(VPhr, Number, Person).
 
% adverb prefix to a sentence
 
independent_clause(LF, clause(Subj, pred(mods(rtshift(Advphr)), VPhr))) -->
    adverb_phrase(Advphr),
    subject(Subj, Number, Person),
    predicate(VPhr, Number, Person).
 
% independent_clauses using expletive "There" as empty subject ["There are apples"]
 
independent_clause(exist(NPhr), exist(NPhr)) --> [there, is],
    subject(NPhr, singular, Person).

independent_clause(exist(NPhr), exist(NPhr)) --> [there, are],
    subject(NPhr, plural, Person).
 
% ------------------------------------------------------------------
% subject of a sentence
% ------------------------------------------------------------------ 
% nominative case noun phrase is a subject
subject(subj(NPhr), Number, Person) -->
    noun_phrase(NPhr, Number, Person, nominative).
 
% an infinitive verb phrase: "to run" is a subject 
subject(subj(IVP), singular, third) -->
    inf_verb_phrase(IVP).
 
 %------------------------------------------------------------------
 % other noun type parts
 %------------------------------------------------------------------
 % a nominative case noun phrase is a predicate nominative
 pred_nominative(pdnom(NPhr), Number, Person) -->
    noun_phrase(NPhr, Number, Person, nominative).
 
 % any adjective phrase is a predicate adjective
 pred_adjective(pdadj(Adj)) --> 
    adjective_phrase(Adj).
 
 direct_object(do(NPhr), Number, Person) --> 
    noun_phrase(NPhr, Number, Person, objective).
 
 indirect_object(io(NPhr), Number, Person) --> 
    noun_phrase(NPhr, Number, Person, objective).
 
 % ------------------------------------------------------------------ 
 % predicates
 % ------------------------------------------------------------------
 
 predicate(pred(Pred2), Number, Person) -->
    predicate_2(Pred2, Number, Person).
 
 % verb phrase, prepositions
 % example: [I nibbled the carrot in the garden.]
 predicate(pred(Pred2, vcomp(Advs)), Number, Person) -->
    predicate_2(Pred2, Number, Person),
    adverbs(Advs).
 
 % sense-verb -\- prepositional phrase
 % example: [I am in the garden.]
 predicate(pred(VPhr, padv(Advphr)), Number, Person) --> 
    sense_verb_phrase(VPhr, Number,Person), 
    adverb_phrase(Advphr).
 
 % an intransitive verb cannot have a direct object 
 predicate_2(VPhr, Number, Person) -->
    verb_phrase(VPhr, Number, Person, intransitive).

 predicate_2(Pred3, Number, Person) --> 
    predicate_3(Pred3, Number, Person).
 
 % sense verb -\-predicate nominative 
 % example: [I am a rabbit.]
 predicate_2(pred(VPhr, pnom(PredNom)), Number, Person) --> 
    sense_verb_phrase(VPhr, Number, Person), 
    pred_nominative(PredNom, Number, Person_2).
 
% sense verb -\- predicate adjective
% example: [I am angry.]
predicate_2(pred(VPhr, padj(Adj)), Number, Person) --> 
    sense_verb_phrase(VPhr, Number, Person),
    pred_adjective(Adj).

% verb -\- direct object
predicate_3(*(VPhr, DirObj), Number, Person) -->
    verb_phrase(VPhr, Number, Person, transitive),
    direct_object(DirObj, Number2, Person2).

% verb -\- indirect object -\- direct object
predicate_3(*(VPhr, IndObj, DirObj), Number, Person) --> 
    verb_phrase(VPhr, Number, Person, bitransitive),
    indirect_object(IndObj, Number2, Person2),
    direct_object(DirObj, Number3, Person3).
 
%--------------------------------------------------------
% The Subordinate Adverb Clause
%--------------------------------------------------------
subord_adv_clause(sadvcls(Subconj, IndCls)) --> 
    subordconj(Subconj),
    independent_clause(IndCls).

%--------------------------------------------------------
% Infinitives
%--------------------------------------------------------
% intransitive verbs cannot have objects
inf_verb_phrase_2(*(to, head(V))) --> 
    [to], [V],
    {averb(V,Past, SingThrd, PresPart, Part, intransitive)}.
 
% transitive verbs must have objects
inf_verb_phrase_2(*(to, head(V), NPhr)) --> 
    [to], [V],
    direct_object(NPhr, Number, Person),
    {averb(V,Past, SingThrd, PresPart, Part, transitive)}.
 
% bi-transitive verbs must have indirect and direct objects
inf_verb_phrase_2(*(to, head(V), IndObj, DirObj)) --> 
    [to],
    indirect_object(IndObj, Number, Person),
    direct_object(DirObj, Number2, Person2),
    {averb(V,Past, SingThrd, PresPart, Part, bitransitive)}.
 
% infinitive verb phrases may or may not have adverb modifiers
inf_verb_phrase(infvp(InfPhr, vcomp(Advs))) --> 
    inf_verb_phrase_2(InfPhr),
    adverbs(Advs).
inf_verb_phrase(infvp(InfPhr)) --> 
    inf_verb_phrase_2(InfPhr).

%-------------------------------------------------------------------
% adverbial phrases
% ------------------------------------------------------------------ 
adverbs(Advp) --> adverb_phrase(Advp).
adverbs(advs(Advp,Preps)) --> adverb_phrase(Advp), prepositions(Props).

adverb_phrase(advp(head(Adv))) --> adverb(Adv).
adverb_phrase(advp(SubAdvCls)) --> subord_adv_clause(SubAdvCls).
adverb_phrase(advp(mod(Adv), Advph)) --> adverb(Adv), adverb_phrase(Advph).
adverb_phrase(advp(PrtPhr)) --> participial_phrase(PrtPhr).
adverb_phrase(advp(Prep)) --> prepositions(Prep).
 
%-------------------------------------------------------------------
% adjective phrases
% ------------------------------------------------------------------
adjective_phrase(Adj) --> adjective(Adj).
 
adjective_phrase(adjs(Adj, Adjph)) -->
    adjective(Adj),
    adjective_phrase(Adjph).
 
% adverbs can modify adjectives
adjective_phrase(adjp(Adv, Adj)) --> 
    adverb(Adv),
    adjective(Adj).
% ------------------------------------------------------------------
% prepositional phrase
% ------------------------------------------------------------------
prepositions(preps(Prphr)) --> prepositional_phrase(Prphr).
 
prepositions(preps(Prphr,Preps)) --> prepositional_phrase(Prphr), prepositions(Preps).
 
prepositional_phrase(prepp(head(Prep),(obj(NPhr)))) --> 
    preposition(Prep), 
    noun_phrase(NPhr, Number2, Person, objective).

% ------------------------------------------------------------------
% Participials and Gerunds
% ------------------------------------------------------------------
participle(part(past(PartPhr)), Type) --> [PartPhr], {averb(Infinitive, Past, SingThrd, PresPart, PartPhr, Type)}.
participle(part(pres(PartPhr)), Type) --> [PartPhr], {averb(Infinitive, Past, SingThrd, PartPhr, PastPart, Type)}.

participial_phrase(partp(PrtPhr, NPhr)) -->
    participle(PrtPhr, transitive),
    noun_phrase(NPhr, Number, Person, objective).
 
participial_phrase(partp(PrtPhr, AdvPh, NPhr)) --> 
    participle(PrtPhr, transitive),
    adverb_phrase(AdvPh),
    noun_phrase(NPhr, Number, Person, objective).
 
participial_phrase(partp(PrtPhr)) --> 
    participle(PrtPhr, intransitive).
 
participial_phrase(partphr(PrtPhr, Advphr)) --> 
    participle(PrtPhr, intransitive), 
    adverb_phrase(Advphr).

% ------------------------------------------------------------------
% gerund phrases: verbs in their present participle form
% treated as noun phrases
% ------------------------------------------------------------------
gerund(ger(Phrase), Type) -->
    [Part], 
    {averb(Root, Past, SingThrd, Part, PastPart, Type)},
    Phrase=..[Part,root(Root)].
 
gerund_phrase_2(gerp(Part, NPhr)) -->
    gerund(Part, transitive),
    noun_phrase(NPhr, Number, Person, objective).
 
gerund_phrase_2(gerp(Part)) -->
    gerund(Part, intransitive).
 
gerund_phrase(gerp(Part)) -->
    gerund_phrase_2(Part).
 
gerund_phrase(gerp(Gerp2,Advphr)) -->
    gerund_phrase_2(Gerp2),
    adverb_phrase(Advphr).

% ------------------------------------------------------------------
% noun phrases
% ------------------------------------------------------------------
% a proper noun is a noun phrase

proper_noun_phrase(Proper) --> proper_noun_phrase2(Proper1), proper_noun_phrase(Proper2), {atomic_list_concat([Proper1, Proper2], ' ', Proper)}.
proper_noun_phrase(Proper) --> proper_noun_phrase2(Proper).

proper_noun_phrase2(Proper) --> [Proper], {proper_noun(Proper)}.

% a proper noun is a noun phrase
noun_phrase(np(head(name(Proper))), singular, third, Case) --> proper_noun_phrase(Proper).

% infinitive verb phrase is a noun phrase
noun_phrase(np(head(InfPhr)), singular, third, Case) --> inf_verb_phrase(InfPhr).
 
% gerunds are noun phrases
noun_phrase(np(head(GerPhr)),singular, third, Case) --> gerund_phrase(GerPhr).
 
% noun with determiner in front
noun_phrase(np(Det, NPhr2), Number, third, Case) -->
    determiner(Det, Number),
    noun_phrase_2(NPhr2, Number).
 
% noun without determiner
noun_phrase(np(NPhr2), Number, third, Case) -->
    noun_phrase_2(NPhr2, Number).
 
% pronoun is a noun phrase
noun_phrase(np(head(NPhr)), Number,Person, Case) --> pronoun(NPhr, Number, Person, Case).
 
noun_phrase(np(NPhr1, conj(Conj), NPhr2), plural, Person, Case) -->
    noun_phrase_2(NPhr1, Number),
    [Conj],
    {conjunction(Conj)}, 
    noun_phrase_2(NPhr2, Number).

% noun with adjective in front
noun_phrase_2(*(NPhr2, mods(Adj)), Number) --> 
    adjective_phrase(Adj),
    noun_phrase_3(NPhr2, Number). 
 
% A noun without adjective
noun_phrase_2(NPhr3, Number) --> noun_phrase_3(NPhr3, Number).
 
% A noun with prepositional phrase after
noun_phrase_3(*(head(N),Pmods), Number) --> 
    noun(N,Number),
    noun_complements(Pmods).
 
% plain noun
noun_phrase_3(head(N), Number) -->
    noun(N,Number).
 
%--------------------------------------------------------------------
% noun post modifiers can be prepositions, subordinate adjectives, etc.
%--------------------------------------------------------------------
 
noun_complements(ncomps(Pnphr)) --> noun_complement(Pnphr).
noun_complements(ncomps(Pnphr,Pnmods)) -->
    noun_complement(Pnphr), 
    noun_complements(Pnmods).
noun_complement(ncomp(Prphr)) --> prepositional_phrase(Prphr).

%--------------------------------------------------------------------
% verb phrases with or without auxiliary verbs
 
verb_phrase(vp(Vphr),Number,Person,Type) --> verb_phrase_2(Vphr,Number,Person,Type).

verb_phrase(vp(Vphr, mods(Adv)),Number,Person,Type) -->
    adverb_phrase(Adv),
    verb_phrase_2(Vphr,Number,Person,Type).
 
% this predicate tests for third person singular verb forms
sing_third(singular,third).
 
% tense: past simple
verb_phrase_2(head(past(root(Infinitive))), Number, Person, Type) --> 
    [V], 
    {averb(Infinitive, V, SingThrd, PresPart, PastPart, Type)}.
 
% tense: past perfect
verb_phrase_2(head(pastperf(root(Infinitive))), Number, Person, Type) --> 
    [had], 
    [V], 
    {averb(Infinitive, Past, SingThrd, PresPart, V, Type)}.
 
verb_phrase_2(*(head(pastperf(root(Infinitive))),mods(Adv)), Number, Person, Type) --> 
    [had],
    adverb_phrase(Adv), 
    [V], 
    {averb(Infinitive, Past, SingThrd, PresPart, V, Type)}. 
 
% tense: present simple
verb_phrase_2(head(present(root(Infinitive))), singular, third, Type) --> 
    [V], 
    {averb(Infinitive, Past, V, PresPart, PastPart, Type)}.
 
verb_phrase_2(head(present(root(V))), Number, Person, Type) --> 
    {not(sing_third(Number,Person))},
    [V], 
    {averb(V,Past, SingThrd, PresPart, PastPart, Type)}.

% tense: future simple
verb_phrase_2(head(future(root(V))), Number, Person, Type) -->
    [will],
    [V], 
    {averb(V,Past, SingThrd, PresPart, PastPart, Type)}.
 
verb_phrase_2(*(head(future(root(V))), mods(Adv)), Number, Person, Type) -->
    [will],
    adverb_phrase(Adv),
    [V], 
    {averb(V, Past, SingThrd, ProsPart, PastPart, Type)}.
 
% tense: present perfect
verb_phrase_2(head(presperf(root(Infinitive))), singular, third, Type) --> 
    [has],
    [V], 
    {averb(Infinitive, Past, SingThrd, PresPart, V, Type)}.
 
verb_phrase_2(*(head(presperf(root(Infinitive))),mods(Adv)), singular, third, Type) -->
    [has], 
    adverb_phrase(Adv),
    [V],
    {averb(Infinitive, Past, SingThrd, PresPart, V, Type)}.
 
verb_phrase_2(head(presperf(root(Infinitive))), Number, Person, Type) --> 
    {not(sing_third(Number,Person))},
    [have],
    [V], 
    {averb(Infinitive, Past, SingThrd, ProsPart, V, Type)}.
 
verb_phrase_2(*(Adv,head(presperf(root(Infinitive)))), Number, Person, Type) --> 
    {not(sing_third(Number, Person))},
    [have], 
    adverb_phrase(Adv),
    [V], 
    {averb(Infinitive, Past, SingThrd, PresPart, V, Type)}.

% tense: future perfect
verb_phrase_2(head(futperf(root(Infinitive))), Number, Person, Type) --> 
    [will], [have],
    [V], 
    {averb(Infinitive, Past, SingThrd, PresPart, V, Type)}.
 
verb_phrase_2(*(head(futperf(root(Infinitive))),mods(Adv)), Number, Person, Type) -->
    [will], [have],
    adverb_phrase(Adv),
    [V], 
    {averb(Infinitive, Past, SingThrd, PresPart, V, Type)}.

verb_phrase_2(*(head(futperf(root(Infinitive))),mods(Adv)),Number, Person, Type) -->
    [will],
    adverb_phrase(Adv),
    [have],
    [V], 
    {averb(Infinitive, Past, SingThrd, PresPart, V, Type)}.
 
verb_phrase_2(*(head(futperf(root(Infinitive))),mods(Advl,Adv2)), Number, Person, Type) -->
    [will],
    adverb_phrase(Adv1),
    [have],
    adverb_phrase(Adv2),
    [V], 
    {averb(Infinitive, Past, SingThrd, PresPart, V, Type)}.

% Tenses for the Verb To Be - verbs of "being"
sense_verb_phrase(Vphr,Number,Person) --> 
    be_verb_phrase(Vphr,Number, Person).
 
be_verb_phrase(Vphr,Number,Person) --> 
    be_verb_phrase_2(Vphr, Number, Person).
 
be_verb_phrase(vp(Adv,Vphr),Number,Person) --> 
    adverb_phrase(Adv),
    be_verb_phrase_2(Vphr, Number,Person).

% tense: past simple
be_verb_phrase_2(head(past(root(be))), Number, Person) --> 
    [V],
    {beverb(V,Number, Person, past)},!.

% tense: past perfect
be_verb_phrase_2(head(pastperf(root(be))), Number, Person) -->
    [had], [been].

be_verb_phrase_2(*(head(pastperf(root(be))), mods(Adv)), Number, Person) -->
    [had],
    adverb_phrase(Adv),
    [been].
 
% tense: present simple
be_verb_phrase_2(head(present(root(be))), Number, Person) -->
    [V], 
    {beverb(V, Number, Person, present)},!.
 
%. tense: future simple
be_verb_phrase_2(head(future(root(be))), Number, Person) --> [will], [be].
 
be_verb_phrase_2(*(head(future(root(be))),mods(Adv)), Number, Person) -->
    [will],
    adverb_phrase(Adv),
    [be].
 
% tense: present perfect
be_verb_phrase_2(head(presperf(root(be))), Number, Person) -->
    {not(sing_third(Number,Person))},
    [have], [been].

be_verb_phrase_2(*(head(presperf(root(be))), mods(Adv)), Number, Person) -->
    {not(sing_third(Numlber,Person))},
    [have], 
    adverb_phrase(Adv),
    [been].
 
be_verb_phrase_2(head(presperf(root(be))), singular, third) --> [has], [been].
 
be_verb_phrase_2(*(head(presperf(root(be))),mods(Adv)), singular, third) --> 
    [has],
    adverb_phrase(Adv), 
    [been].
 
% tense: future perfect
be_verb_phrase_2(head(furperf(root(be))), Number, Person) --> [will], [have], [been].
 
be_verb_phrase_2(*(head(past(root(be))),mods(Adv)), Number, Person) --> 
    [will],
    adverb_phrase(Adv),
    [have], [been].
 
 be_verb_phrase_2(*(head(past(root(be))),mods(Adv)), Number, Person) -->
    [will],
    [have],
    adverb_phrase(Adv), 
    [been].
 
be_verb_phrase_2(*(head(past(root(be))),mods(Adv1,Adv2)), Number, Person) -->
    [will],
    adverb_phrase(Advl), 
    [have],
    adverb_phrase(Adv2), 
    [been].
 
% ------------------------------------- 
% terminal rules
% -------------------------------------
noun(comn(N), Number) -->
    [N], {is_common_noun(N, Number)}.
 
determiner(det(Det), Number) --> [Det], {is_determiner(Det, Number)}.
 
adjective(adj(Adj)) --> [Adj], {is_adjective(Adj)}.
adjective(adj(Possadj)) --> [PossAdj], {poss_adj(PossAdj)}.
 
adverb(adv(Adv)) --> [Adv], {is_adverb(Adv)}.
 
preposition(prep(Prp)) --> [Prp], {is_preposition(Prp)}.
 
pronoun(pron(P), Number, Person, Case) --> [P], {is_pronoun(P, Number, Person, Case)}.
 
relative_pronoun(rpron(P), Number, Person, Case) --> [P], {is_rel_pronoun(P, Number, Person, Case)}.
 
subordconj(subconj(Conj)) --> [Conj], {is_subconj(Conj)}.
 
auxiliary(aux(Auxv)) --> [Auxv], {auxmodal(Auxv)}.
 
 
% ----------------------------------------------------------------------------------
% the dictionary
% ----------------------------------------------------------------------------------
 
% ---------------------------------------------------------------
% determiners
% ---------------------------------------------------------------
is_determiner(the, _).
is_determiner(a, singular). 
is_determiner(an, singular).
is_determiner(that, singular). 
is_determiner(this, singular). 
is_determiner(these, plural). 
is_determiner(those, plural). 
is_determiner(all, plural). 
is_determiner(some, plural). 
is_determiner(many, plural). 
is_determiner(most, plural). 
is_determiner(few, plural). 
is_determiner(no, plural). 
is_determiner(every, singular).
is_determiner(any, _).
 
% ---------------------------------------------------------------
% the verb to be; copula
% ---------------------------------------------------------------
beverb(am, singular, first, present). 
beverb(are, singular, second, present).
beverb(is, singular, third, present). 
beverb(was, singular, first, past). 
beverb(vere, singular, second, past). 
beverb(was, singular, third, past).
beverb(are, plural, Person, present). 
beverb(were, plural, Person, past).

% ---------------------------------------------------------------
% other verbs
% ---------------------------------------------------------------

averb(want,wanted,wants,wanting,wanted,transitive).
averb(go,went,goes,going,gone,intransitive).
averb(know,knew,knows,knowing,known,transitive). 
averb(like,liked,likes,liking,liked,transitive).
averb(cross,crossed,crosses,crossing,crossed,transitive). 
averb(beckon,beckoned,beckons,beckoning,beckoned,transitive). 
averb(give, gave, gives, giving, given, bitransitive). 
averb(find, found, finds, finding, found, bitransitive). 
averb(find, found, finds, finding, found, transitive). 
averb(see, saw, sees, seeing, seen, transitive).
averb(eat, ate, eats, eating, eaten, transitive).
averb(eat, ate, eats, eating, eaten, intransitive).
averb(do, did, does, doing, done, transitive).
averb(do, did, does, doing, done, bitransitive).
averb(insist, insisted, insists, insisting, insisted, transitive). 
averb(worry, worried, worries, worrying, worried, transitive). 
averb(think, thought, thinks, thinking, thought, intransitive). 
averb(die,died,dies,dying,died,intransitive). 
averb(have,had,has,having,had,transitive).
averb(need, needed, needs, needing, needed, transitive).
averb(work, worked, works, working, worked, intransitive).
averb(teach, taught, teaches, teaching, taught, bitransitive).
averb(learn, learned, learns, learning, learned, transitive).
averb(speak, spoke, speaks, speaking, spoken, transitive).
averb(love, loved, loves, loving, loved, transitive).
averb(move, moved, moves, moving, moved, intransitive).
averb(duplicate, duplicated, duplicates, duplicating, duplicated, transitive). 
averb(take, took, takes, taking, taken, tansitive).
averb(wait, waited, waits, waiting, waited, intransitive).
averb(get, got, gets, getting, gotten, transitive).
averb(say, said, says, saying, said, transitive).
averb(break, broke, breaks, breaking, broken, transitive).
averb(lose, lost, loses, losing, lost, transitive).
averb(continue, continued, continues, continuing, continued, transitive). 
averb(let, let, lets, letting, let, transitive).
averb(run, ran, runs, running, ran, intransitive).
averb(fill, filled, fills, filling, filled, transitive).
    %averb(V,Num,Root,transitive) :- morphit(V,List,Out), check_list(v,List,Out,Num,Root).
    %averb(V,Num,Root,intransitive) :- morphit(V,List,Out), check_list(v,List,Out,Num,Root).

% ---------------------------------------------------------------
% conjunction
% ---------------------------------------------------------------
conjunction(and). 
conjunction(or).

% ---------------------------------------------------------------
% modal auxiliaries
% ---------------------------------------------------------------
auxmodal(may). 
auxmodal(might). 
auxmodal(could). 
auxmodal(can).
auxmodal(would).
 
% ---------------------------------------------------------------
% adjectives
% ---------------------------------------------------------------
is_adjective(angry).
is_adjective(black).
is_adjective(green).
is_adjective(red).
is_adjective(blue).
is_adjective(white).
is_adjective(large).
is_adjective(active).
is_adjective(nibbled).
is_adjective(good).
is_adjective(alive).
is_adjective(orange).
is_adjective(early).
is_adjective(government).
is_adjective(detense).
is_adjective(frightened).
is_adjective(obvious).
is_adjective(hungry).
is_adjective(frightening).
is_adjective(intimidating).
is_adjective(artificial).
is_adjective(no).
is_adjective(easier).
    is_adjective(A) :- morphit(A,List,Out), check_list(a,List,Out,Num,Root). % s(A,_,_,a,_,_).
    is_adjective(A) :- morphit(A,List,Out), check_list(s,List,Out,Num,Root). % s(A,_,_,s,_,_). % satellite - no antonym
 
 % ---------------------------------------------------------------
 % adverbs
 % ---------------------------------------------------------------
is_adverb(quickly).
is_adverb(shortly).
is_adverb(now).
is_adverb(exactly).
is_adverb(hard).
is_adverb(hungrily).
is_adverb(there).
is_adverb(not).
is_adverb(much).
is_adverb(easy).
is_adverb(slowly).
is_adverb(here).
is_adverb(gone).
    %is_adverb(A) :- morphit(A,List,Out), check_list(r,List,Out,Num,Root). % s(A,_,_,r,_,_).
    %is_adverb(A) :- morphit(A,List,Out), check_list(s,List,Out,Num,Root). % s(A,_,_,s,_,_).
 
% ---------------------------------------------------------------
% proper nouns 
% ---------------------------------------------------------------
proper_noun(Name) :- atom(Name), atom_codes(Name, Codes2), head(Codes2, First), char_type(First,upper), !.

% ---------------------------------------------------------------
% nouns
% ---------------------------------------------------------------
% ---------------------------------------------------------------
% count nouns
% ---------------------------------------------------------------
is_common_noun(force, singular).
is_common_noun(forces, plural).
is_common_noun(convoy, singular).
is_common_noun(convoys, plural). 
is_common_noun(lake, singular). 
is_common_noun(lakes, plural). 
is_common_noun(hill, singular).
is_common_noun(hills, plural). 
is_common_noun(avenuo, singular). 
is_common_noun(avenues, plural).
is_common_noun(avenue, singular).
is_common_noun(approaches, plural).
is_common_noun(area, singular). 
is_common_noun(areas, plural).
is_common_noun(book, singular). 
is_common_noun(books, plural). 
is_common_noun(garden,singular).
is_common_noun(gardens, plural). 
is_common_noun(car, singular).
is_common_noun(cars, plural). 
is_common_noun(truck, singular). 
is_common_noun(trucks, plural). 
is_common_noun(room, singular). 
is_common_noun(rooms, plural). 
is_common_noun(field, singular). 
is_common_noun(fields, plural).
is_common_noun(river, singular).
is_common_noun(rivers, plural). 
is_common_noun(road, singular).
is_common_noun(roads, plural). 
is_common_noun(bridgo, singular). 
is_common_noun(bridges, plural).
is_common_noun(woman, singular). 
is_common_noun(women, plural).
is_common_noun(pizza, singular).
is_common_noun(pizzas, plural). 
is_common_noun(stallions, plural). 
is_common_noun(stallion, singular). 
is_common_noun(men, plural).
is_common_noun(man, singular). 
is_common_noun(life, singular).
is_common_noun(lives, plural).
is_common_noun(agency, singular). 
is_common_noun(agencies, plural). 
is_common_noun(cucumber, singular).
is_common_noun(cucumbers, plural). 
is_common_noun(carrot, singular). 
is_common_noun(carrots, plural). 
is_common_noun(orange, singular).
is_common_noun(oranges, plural). 
is_common_noun(apple,singular).
is_common_noun(apples, plural). 
is_common_noun(cape, singular). 
is_common_noun(capes, plural).
is_common_noun(rabbit, singular). 
is_common_noun(rabbits, plural). 
is_common_noun(saw, singular). 
is_common_noun(saws, plural).
is_common_noun(governments, plural).
is_common_noun(computer, singular).
is_common_noun(computers, plural).
is_common_noun(intelligence, singular).
is_common_noun(enemy, singular).
is_common_noun(enemies, plural).
is_common_noun(element, singular). 
is_common_noun(elements, plural).
is_common_noun(line, singular).
is_common_noun(lines, plural).
is_common_noun(location, singular).
is_common_noun(locations, plural).
is_common_noun(conversation, singular).
is_common_noun(conversations, plural).
is_common_noun(time, singular).
is_common_noun(times, plural).
is_common_noun(end, singular).
is_common_noun(ends, plural).
is_common_noun(beginning, singular).
is_common_noun(beginnings, plural).
is_common_noun(hour, singular).
is_common_noun(hours, plural).
is_common_noun(minute, singular).
is_common_noun(minutes, plural).
is_common_noun(mortal, _).
is_common_noun(mortals, plural).
    is_common_noun(N,Num) :- morphit(N,List,Out), check_list(n,List,Out,Num,Root).


% mass nouns
is_common_noun(ground, mass).
is_common_noun(water, mass).
is_common_noun(fruit, mass).
 
% possessive adjectives 

poss_adj(our).
poss_adj(your).
poss_adj(my).
poss_adj(his).
poss_adj(her).
poss_adj(their).
poss_adj(its).
 
% pronouns

is_pronoun(everyone, singular, third, Case).
is_pronoun(nothing, singular, third, Case).
is_pronoun(i, singular, first, nominative). 
is_pronoun(you,Number, second,  nominative). 
is_pronoun(he, singular, third, nominative). 
is_pronoun(she, singular, third, nominative).
is_pronoun(it, singular, third, Case). 
is_pronoun(we, plural, first, nominative). 
is_pronoun(they, plural, third, nominative). 
is_pronoun(me, singular, first, objective).
is_pronoun(you, Number, second, objective). 
is_pronoun(him, singular, third, objective).
is_pronoun(her, singular, third, objective). 
is_pronoun(us, plural, first, objective).
is_pronoun(them, plural, third, objective).
is_pronoun(mine, singular, first, possessive). 
is_pronoun(yours, Number, second, possessive). 
is_pronoun(his, singular, third, possessive). 
is_pronoun(hers, singular, third, possessive). 
is_pronoun(its, singular, third, possessive). 
is_pronoun(ours, plural, first, possessive).
is_pronoun(theirs, plural, third, possessive). 
is_pronoun(who, Number, Person, nominative). 
is_pronoun(whose, Number, Person, possessive). 
is_pronoun(whom, Number, Person, objective).
 
is_rel_pronoun(who, Number, third, nominative).
is_rel_pronoun(whom, Numbir, third, objective). 
is_rel_pronoun(whose, Number, Person, possessive). 
is_rel_pronoun(what, Number, third, Case). 
is_rel_pronoun(whatever, Number, third, Case).
is_rel_pronoun(that, Number, third, objective).
is_rel_pronoun(which, Number, third, Case). 
is_rel_pronoun(where, singular, third, Case).
 
% ---------------------------------------------------------------------
% prepositions
% -------------------------------------------------------------------
is_preposition(in).
is_preposition(with). 
is_preposition(to).
is_preposition(from).
is_preposition(for).
is_preposition(by).
is_preposition(of).
is_preposition(on).
is_preposition(from).
is_preposition(during).
is_preposition(before).
is_preposition(after).
is_preposition(at).
is_preposition(near).
is_preposition(along).
is_preposition(beside).
is_preposition(around).


% -------------------------------------------------------------------
% subordinating conjunctions: begin adverb phrases
% -------------------------------------------------------------------
is_subconj(after).
is_subconj(before).
is_subconj(when).
is_subconj(while).
is_subconj(because).
is_subconj(although).
is_subconj(if).
is_subconj(unless).
is_subconj(where).

% ---------------------------------------------------------------------
    
morphit(X,List,Out) :- morph_atoms_bag(X, List), morph_bag_lookup(List, Out), nonvar(Out),!.
    
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

s_type([.],statement) :-!.
s_type([?],question) :-!.
s_type([!],imperative) :-!.
s_type(X,X) :-!.

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

pp(X,0) :- writeln(X).
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
       ( % if
             %s_type(Punctuation, S_type), write(S_type), write(': '), writeln(Root),
             sentence(Logical_form, Parse_form, Root, []),
             write('Logical Form: '),writeln(Logical_form),
             writeln('Parse Form: '),pp(Parse_form,1),nl,
             parse;
         % else
            write("Pardon?"),nl,parse
        )
     ).

