#! /Applications/SWI-Prolog.app/Contents/MacOS/swipl

/*
 *
 * Adapted from Gurney et al., Pereira and Warren., McCord, Schlachter, Witzig, Covington.
 *
 */

:- op(100,xfy,'&').
:- op(150,xfx,'==>').

:- set_prolog_flag(history, 50).

/* the WORDNET lexicon and morphology */
:- ensure_loaded('wn_s_convert.pl').
:- ensure_loaded('pronto_morph_engine.pl').
:- ensure_loaded('morph_lookup.pl').
:- ensure_loaded('wn_g.pl').

:-style_check(-singleton).

:-assert(tracing('On')).
:-assert(tracing_parse('On')).
trace_it(X) :- tracing('On'), writeln(X).
trace_it(_) :- !.

% ------------------------------------------------------------------------------------------------
% Sentences and Independent Clauses
% ------------------------------------------------------------------------------------------------
% independent clauses are sentences

% where/what/.. question
sentence(question(LF), question(Phrase,VPhr,OPhrase)) -->
    question_pronoun(X, LF, Phrase, Number, Person, Case),!,{trace_it((question_pronoun,X, Prop1, Phrase, Number, Person, Case))},
    sense_verb_phrase(Y, Prop2, VPhr, Number, Person1),{trace_it((sense_verb_phrase,Y, Prop2, VPhr, Number, Person1))},
pred_nominative(A, B, X, OPhrase, Number, Person2),{(nonvar(A)->A=B;true)},{trace_it((pred_nominative,A,B,Object, LF, Number, Person2))}.

% is X a Y?
sentence(question(Assn2), question(is(VPhr,Object1,Object2))) -->
    sense_verb_phrase(X, Assn, VPhr, Number, Person),
    direct_object(Y, Assn, Assn1, Object1, Number, Person),
    indirect_object(Y, Assn1, Assn2, Object2, Number, Person).

% does X Y?
sentence(question(LF), question(does(VPhr,Object,Object2))) -->
    does_verb_phrase(A, Assn, VPhr1, Number, Person),
    direct_object(X, Assn1, Assn2, Object, Number1, Person1),
    verb_phrase((X,Y), Assn2, VPhr, Number, Person, transitive),
    indirect_object(Y, Assn2, LF, Object2, Number1, Person1).

% imperative
sentence(imperative(LF), imperative(VPhr, Object)) -->
    %preliminaries(Prelims),{trace_it((imperative__preliminaries,Prelims))},
    verb_phrase(X, Assn, VPhr, singular, first, intransitive),{trace_it((imperative__verb_phrase,X, Assn, LF, VPhr, Number, Person))},
    direct_object(X, Assn, LF, Object, Number1, Person1),{trace_it((imperative__direct_object,X, Assn,Object, LF, Number, Person))}.
 
sentence(imperative(LF), imperative(VPhr, Object, Object2)) -->
    verb_phrase((X,Y), Assn, VPhr, singular, first, bitransitive),{trace_it((imperative__verb_phrase,X, Assn, LF, VPhr, Number, Person))},
    direct_object(X, Assn, Assn1, Object, Number1, Person1),{trace_it((imperative__direct_object,X, Assn,Object, LF, Number, Person))},
    indirect_object(Y, Assn1, LF, Object2, Number2, Person2),{trace_it((imperative__indirect_object,X, Assn1,Object2, LF, Number, Person))}.

% statement
sentence(statement(LF), statement(Sent)) -->
    independent_clause(LF, Sent).

% if/then statements
sentence(statement(LF2:-LF1), conditional(Sentl, Sent2)) -->
    [if],
    independent_clause(LF1, Sentl),
    [then],
    independent_clause(LF2, Sent2).
 
sentence(statement(LF2:-LF1), conditional(Sentl, Sent2)) -->
    [if],
    independent_clause(LF1, Sentl),
    independent_clause(LF2, Sent2).
 
% ------------------------------------------------------------------------------------------------
% canonical independent clause
% ------------------------------------------------------------------------------------------------
 
independent_clause(LF, clause(Subj, VPhr)) -->
    subject(X, Assn, LF, Subj, Number, Person),{trace_it((independent_clause__subject,X, Assn, LF, Subj, Number, Person))},
    predicate(X, Assn, VPhr, Number, Person),{trace_it((independent_clause__predicate,X, Assn, LF, Subj, Number, Person))}.
 
% adverb prefix to a sentence
 
independent_clause(Assn1&Assn2, clause(Subj, pred(mods(rtshift(Advphr)), VPhr))) -->
    adverb_phrase(X, Assn, Advphr),
    subject(X, Assn, Assn1, Subj, Number, Person),
    predicate(X, Assn2, VPhr, Number, Person).
 
% independent_clauses using expletive "There" as empty subject ["There are apples"]
 
independent_clause(LF, exist(NPhr)) --> [there, is],
    subject(X, Assn, LF, NPhr, singular, Person).

independent_clause(LF, exist(NPhr)) --> [there, are],
    subject(X, Assn, LF, NPhr, plural, Person).

preliminaries(Prelims1&Prelims) --> prelims(Prelims1), preliminaries(Prelims).
preliminaries(Prelims) --> prelims(Prelims).
prelims(none) --> [].
prelims(please) --> [please].
prelims('Alexa') --> ['Alexa'].

% ------------------------------------------------------------------
% subject of a sentence
% ------------------------------------------------------------------ 
% nominative case noun phrase is a subject
subject(X, Assn, LF, subj(NPhr), Number, Person) -->
    noun_phrase(X,Assn,LF, NPhr, Number, Person, nominative),{trace_it((subject__noun_phrase,X, Assn, LF, NPhr, Number, Person))}.
 
% an infinitive verb phrase: "to run" is a subject 
subject(X, Assn, LF, subj(IVP), singular, third) -->
    inf_verb_phrase(X,Assn,IVP).
 
 %------------------------------------------------------------------
 % other noun type parts
 %------------------------------------------------------------------
 % a nominative case noun phrase is a predicate nominative
pred_nominative(X, Assn, LF, dnom(NPhr), Number, Person) -->
    noun_phrase(X, Assn, LF, NPhr, Number, Person, nominative),{trace_it((pred_nominative__noun_phrase,X, Assn, LF, NPhr, Number, Person))}.

 % any adjective phrase is a predicate adjective
 pred_adjective(X, Assn, pdadj(Adj)) -->
    adjective_phrase(X, Assn, Adj),{trace_it((pred_adjective__adjective_phrase,X, Assn, LF, NPhr, Number, Person))}.
 
 direct_object(X, Assn, LF, do(NPhr), Number, Person) -->
    noun_phrase(X, Assn, LF, NPhr, Number, Person, objective),{trace_it((direct_object__noun_phrase,X, Assn, LF, NPhr, Number, Person))}.

 indirect_object(X, Assn, LF, io(NPhr), Number, Person) -->
    noun_phrase(X, Assn, LF,NPhr, Number, Person, objective),{trace_it((indirect_object__noun_phrase,X, Assn, LF, NPhr, Number, Person))}.
 
 % ------------------------------------------------------------------ 
 % predicates
 % ------------------------------------------------------------------
 
 predicate(X, Assn, pred(Pred2), Number, Person) -->
    predicate_2(X, Assn, Pred2, Number, Person),{trace_it((predicate_predicate_2,X, Assn, LF, Pred2, Number, Person))}.
 
 % verb phrase, prepositions
 % example: [I nibbled the carrot in the garden.]
 predicate(X, Assn&Assn1, pred(Pred2, vcomp(Advs)), Number, Person) -->
    predicate_2(X, Assn, Pred2, Number, Person),
    adverbs(X, Assn1, Advs).
 
 % sense-verb -\- prepositional phrase
 % example: [I am in the garden.]
 predicate(X, Assn&Assn1, pred(VPhr, padv(Advphr)), Number, Person) -->
    sense_verb_phrase(X, Assn, VPhr, Number,Person),
    adverb_phrase(X, Assn1, Advphr).
 
 % an intransitive verb cannot have a direct object 
predicate_2(X, Assn, VPhr, Number, Person) -->
    verb_phrase(X, Assn, VPhr, Number, Person, intransitive).

 predicate_2(X, Assn, Pred3, Number, Person) -->
    predicate_3(X, Assn, Pred3, Number, Person),{trace_it((predicate_2__predicate_3,X, Assn, LF, Pred3, Number, Person))}.
 
 % sense verb -\-predicate nominative 
 % example: [I am a rabbit.]
 predicate_2(X, LF, pred(VPhr, pnom(PredNom)), Number, Person) -->
    sense_verb_phrase(X, Assn, VPhr, Number, Person),{trace_it((predicate_2_sense_verb_phrase,X, Y, LF, Assn, Number, Person))},
    pred_nominative(Y, Assn2, LF, PredNom, Number, Person),{trace_it((predicate_2a__pred_nominative,X, Y,Assn, LF, Assn2, Number, Person))}, {X=Y},{trace_it((xeqy__predicate_2b,X, Assn2, LF, Assn2, Number, Person))}.

% sense verb -\- predicate adjective
% example: [I am angry.]
predicate_2(X, Assn1&Assn2, pred(VPhr, padj(Adj)), Number, Person) -->
    sense_verb_phrase(X, Assn1, VPhr, Number, Person),
    pred_adjective(X, Assn2, Adj).

% verb -\- direct object
predicate_3(X, LF, *(VPhr, DirObj), Number, Person) -->
    verb_phrase((X,Y), Assn, VPhr, Number1, Person1, transitive),
    direct_object(Y, Assn, LF, DirObj, Number2, Person2).

% verb -\- indirect object -\- direct object
predicate_3(X, LF, *(VPhr, IndObj, DirObj), Number, Person) -->
    verb_phrase((X,Y,Z), Assn1, VPhr, Number, Person, bitransitive),
    indirect_object(Y, Assn1, Assn2, IndObj, Number2, Person2),
    direct_object(Z, Assn2, LF, DirObj, Number3, Person3).
 
%--------------------------------------------------------
% The Subordinate Adverb Clause
%--------------------------------------------------------
subord_adv_clause(Prop1, LF1&LF2, sadvcls(Subconj, IndCls)) -->
    subordconj(Prop1, LF1, Subconj),
    independent_clause(LF2,IndCls).

%--------------------------------------------------------
% Infinitives
%--------------------------------------------------------
% intransitive verbs cannot have objects
inf_verb_phrase_2(X, Assn, *(to, head(V))) -->
    [to], [V],
    {averb(X, Assn, V, Past, SingThrd, PresPart, Part, intransitive)}.
 
% transitive verbs must have objects
inf_verb_phrase_2(X, LF, *(to, head(V), NPhr)) -->
    [to], [V],
    direct_object(Y, Assn, LF, NPhr, Number, Person),
    {averb((X,Y), Assn, V, Past, SingThrd, PresPart, Part, transitive)}.
 
% bi-transitive verbs must have indirect and direct objects
inf_verb_phrase_2(X, Assn, *(to, head(V), IndObj, DirObj)) -->
    [to],
    indirect_object(Z, Assn, LF1, IndObj, Number, Person),
    direct_object(Y, Assn, LF2, DirObj, Number2, Person2),
    {averb((X,Y,Z), Assn, V, Past, SingThrd, PresPart, Part, bitransitive)}.
 
% infinitive verb phrases may or may not have adverb modifiers
inf_verb_phrase(X, Assn, infvp(InfPhr, vcomp(Advs))) -->
    inf_verb_phrase_2(X, Assn1, InfPhr),
    adverbs(Assn1, Assn, Advs).
inf_verb_phrase(X, Assn, infvp(InfPhr)) -->
    inf_verb_phrase_2(X, Assn, InfPhr).

%-------------------------------------------------------------------
% adverbial phrases
% ------------------------------------------------------------------ 
adverbs(Prop1,LF, Advp) --> adverb_phrase(Prop1,LF, Advp).
adverbs(Prop1,LF1&LF2, advs(Advp,Preps)) --> adverb_phrase(Prop1,LF1, Advp), prepositions(Prop1,LF2, Props).

adverb_phrase(Prop1,LF, advp(head(Adv))) --> adverb(Prop1,LF, Adv).
adverb_phrase(Prop1,LF, advp(SubAdvCls)) --> subord_adv_clause(Prop1,LF, SubAdvCls).
adverb_phrase(Prop1,LF1&LF2, advp(mod(Adv), Advph)) --> adverb(Prop1,LF1, Adv), adverb_phrase(Prop1,LF2, Advph).
adverb_phrase(Prop1,LF, advp(PrtPhr)) --> participial_phrase(Prop1,LF, PrtPhr).
adverb_phrase(Prop1,LF, advp(Prep)) --> prepositions(Prop1,LF, Prep).
 
%-------------------------------------------------------------------
% adjective phrases
% ------------------------------------------------------------------
adjective_phrase(Prop1,LF, Adj) --> adjective(Prop1,LF, Adj).
 
adjective_phrase(Prop1,LF1&LF2, adjs(Adj, Adjph)) -->
    adjective(Prop1,LF1, Adj),
    adjective_phrase(Prop1,LF2, Adjph).
 
% adverbs can modify adjectives
adjective_phrase(Prop1,LF1&LF2, adjp(Adv, Adj)) -->
    adverb(Prop1,LF1, Adv),
    adjective(Prop1,LF2, Adj).
% ------------------------------------------------------------------
% prepositional phrase
% ------------------------------------------------------------------
prepositions(Prop1,LF, preps(Prphr)) --> prepositional_phrase(Prop1,LF, Prphr).
 
prepositions(Prop1,LF1&LF2, preps(Prphr,Preps)) --> prepositional_phrase(Prop1,LF1, Prphr), prepositions(Prop1,LF2, Preps).
 
prepositional_phrase(Prop1,LF, prepp(head(Prep),(obj(NPhr)))) -->
    preposition(Prop1,Assn, Prep),
    noun_phrase(X,Assn,LF, NPhr, Number2, Person, objective).

% ------------------------------------------------------------------
% Participials and Gerunds
% ------------------------------------------------------------------
participle(X,Assn,part(past(PartPhr)), Type) --> [PartPhr], {averb(X,Assn,Infinitive, Past, SingThrd, PresPart, PartPhr, Type)}.
participle(X,Assn,part(pres(PartPhr)), Type) --> [PartPhr], {averb(X,Assn,Infinitive, Past, SingThrd, PartPhr, PastPart, Type)}.

participial_phrase(X,LF,partp(PrtPhr, NPhr)) -->
    participle(X,Assn,PrtPhr, transitive),
    noun_phrase(X,Assn,LF,NPhr, Number, Person, objective).
 
participial_phrase(X,LF,partp(PrtPhr, AdvPh, NPhr)) -->
    participle(X,Assn1,PrtPhr, transitive),
    adverb_phrase(X,Assn1,AdvPh),
    noun_phrase(X,Assn1&Assn2,LF,NPhr, Number, Person, objective).
 
participial_phrase(X,Assn,partp(PrtPhr)) -->
    participle(X,Assn,PrtPhr, intransitive).
 
participial_phrase(X,Assn1&Assn2,partphr(PrtPhr, Advphr)) -->
    participle(X,Assn1,PrtPhr, intransitive),
    adverb_phrase(X,Assn2,Advphr).

% ------------------------------------------------------------------
% gerund phrases: verbs in their present participle form
% treated as noun phrases
% ------------------------------------------------------------------
gerund(X, Assn, ger(Phrase), Type) -->
    [Part], 
    {averb(X, Assn, Root, Past, SingThrd, Part, PastPart, Type)},
    Phrase=..[Part,root(Root)].
 
gerund_phrase_2(X, LF, gerp(Part, NPhr)) -->
    gerund(X, Assn, Part, transitive),
    noun_phrase(X, Assn, LF, NPhr, Number, Person, objective).
 
gerund_phrase_2(X, Assn, gerp(Part)) -->
    gerund(X, Assn, Part, intransitive).
 
gerund_phrase(X, Assn, gerp(Part)) -->
    gerund_phrase_2(X, Assn, Part).
 
gerund_phrase(X, Assn1&Assn2, gerp(Gerp2,Advphr)) -->
    gerund_phrase_2(X, Assn1, Gerp2),
    adverb_phrase(X, Assn2, Advphr).

% ------------------------------------------------------------------
% noun phrases
% ------------------------------------------------------------------
% a list of proper nouns is a noun phrase

proper_noun_phrase(X, Assn, Assn1, Proper) --> proper_noun_phrase2(X, Assn, Assn1, Proper1), proper_noun_phrase(X, Assn2, Assn3, Proper2), {atomic_list_concat([Proper1, Proper2], ' ', Proper)}.
proper_noun_phrase(X, Assn, Assn, Proper) --> proper_noun_phrase2(X, Assn, Assn, Proper).

proper_noun_phrase2(Proper, Assn, Assn, Unquoted) --> [Proper], {proper_noun(Proper,Unquoted)}.
proper_noun_phrase2(Proper, Assn, Assn, Proper) --> [Proper], {proper_noun(Proper)}.

% a proper noun is a noun phrase
noun_phrase(X,Assn,Assn,np(head(name(Proper))), singular, Person, Case) --> proper_noun_phrase(X, X, X, Proper),{trace_it((noun_phrase__proper_noun_phrase,X, Assn, Number, singular, Person, Case))}.

% infinitive verb phrase is a noun phrase
noun_phrase(X,Assn,Assn,np(head(InfPhr)), singular, third, Case) --> inf_verb_phrase(X,Assn,InfPhr).
 
% gerunds are noun phrases
noun_phrase(X,Assn,Assn,np(head(GerPhr)),singular, third, Case) --> gerund_phrase(X,Assn,GerPhr).
 
% noun with determiner in front
noun_phrase(X, Assn, LF, np(Det, NPhr2), Number, third, Case) -->
    determiner(X, Prop, Assn, LF, Det, Number),{trace_it((noun_phrase__determiner,X, Prop,Assn, LF, Det, Number, Person))},
    noun_phrase_2(X, Prop, Prop2, NPhr2, Number),{trace_it((noun_phrase__det_noun_phrase_2,X, Prop, Prop2, Number, Person))}.

% noun without determiner
noun_phrase(X, Assn, Assn, np(NPhr2), Number, third, Case) -->
    noun_phrase_2(X, Assn, LF, NPhr2, Number),{trace_it((noun_phrase__noun_phrase_2,X, Assn, LF, Number))}.
 
% pronoun is a noun phrase
noun_phrase(X,Assn,Assn,np(head(NPhr)), Number,Person, Case) --> {trace_it((trying__noun_phrase_pronoun,X, Assn, Number, Person,Case))},
    pronoun(X,Assn, NPhr, Number, Person, Case),{trace_it((noun_phrase_pronoun,X, Assn, NPhr, Number, Person,Case))}.
 
noun_phrase(X,Assn,LF, np(NPhr1, conj(Conj), NPhr2), plural, Person, Case) -->
    noun_phrase_2(X,Assn,LF1, NPhr1, Number),
    [Conj],
    {conjunction(Conj)}, 
    noun_phrase_2(X,Assn,LF2, NPhr2, Number),
    LF=..[Conj,LF1,LF2].

% noun with adjective in front
noun_phrase_2(X,Assn,Assn1&Assn2,*(NPhr2, mods(Adj)), Number) -->
    adjective_phrase(X,Assn1,Adj),{trace_it((noun_phrase_2__adjective_phrase,X, Y,Assn1, Adj, Number, Person))},
    noun_phrase_3(X, Assn, Assn2, NPhr2, Number),{trace_it((noun_phrase_2__noun_phrase_3,X, Assn, LF, NPhr3, Number, Person))}.
 
% A noun without adjective
noun_phrase_2(X,Assn,LF,NPhr3, Number) -->
    noun_phrase_3(X,Assn,LF,NPhr3, Number),{trace_it((noun_phrase_2__noun_phrase_3,X, Y,Assn, LF, NPhr3, Number, Person))}.
 
% A noun with prepositional phrase after
noun_phrase_3(X, Assn, LF1&LF2, *(head(N),Pmods), Number) -->
    noun(X, LF1, N, Number),{trace_it((noun_phrase3__noun,X, Assn, LF1, Number, Person))},
    noun_complements(X, LF2, Pmods),{trace_it((noun_phrase3__noun_complements,X, Assn, LF2, Number, Person))}.
 
% plain noun
noun_phrase_3(X, Assn, Assn, head(N), Number) -->
    noun(X, Assn, N, Number),{trace_it((plain_noun_phrase3,X, Assn, Number))}.
 
%--------------------------------------------------------------------
% noun post modifiers can be prepositions, subordinate adjectives, etc.
%--------------------------------------------------------------------
 
noun_complements(X, LF, ncomps(Pnphr)) --> noun_complement(X, LF, Pnphr).
noun_complements(X, LF1&LF2, ncomps(Pnphr,Pnmods)) -->
    noun_complement(X, LF1, Pnphr),
    noun_complements(X, LF2, Pnmods).
noun_complement(X, LF, ncomp(Prphr)) --> prepositional_phrase(X, LF, Prphr).

%--------------------------------------------------------------------
% verb phrases with or without auxiliary verbs
 
verb_phrase(X, LF, vp(Vphr),Number,Person,Type) -->
    verb_phrase_2(X, LF, Vphr,Number,Person,Type).

verb_phrase(X, LF1&LF2, vp(Vphr, mods(Adv)),Number,Person,Type) -->
    adverb_phrase(X, LF1, Adv),
    verb_phrase_2(X, LF2, Vphr,Number,Person,Type).
 
% this predicate tests for third person singular verb forms
sing_third(singular,third).
 
% tense: past simple
verb_phrase_2(X, past(LF), head(past(root(Infinitive))), Number, Person, Type) -->
    [V], 
    {averb(X, LF, Infinitive, V, SingThrd, PresPart, PastPart, Type)}.
 
% tense: past perfect
verb_phrase_2(X, past(LF), head(pastperf(root(Infinitive))), Number, Person, Type) -->
    [had], 
    [V], 
    {averb(X, LF, Infinitive, Past, SingThrd, PresPart, V, Type)}.
 
verb_phrase_2(X, past(Assn1&Assn2), *(head(pastperf(root(Infinitive))),mods(Adv)), Number, Person, Type) -->
    [had],
    adverb_phrase(X, Assn1, Adv),
    [V], 
    {averb(X, Assn2, Infinitive, Past, SingThrd, PresPart, V, Type)}.
 
% tense: present simple
verb_phrase_2(X, LF, head(present(root(Infinitive))), singular, third, Type) -->
    [V], 
    {averb(X, LF, Infinitive, Past, V, PresPart, PastPart, Type)}.
 
verb_phrase_2(X, LF, head(present(root(V))), Number, Person, Type) -->
    {not(sing_third(Number,Person))},
    [V], 
    {averb(X, LF, V, Past, SingThrd, PresPart, PastPart, Type)}.

% tense: future simple
verb_phrase_2(X, future(LF), head(future(root(V))), Number, Person, Type) -->
    [will],
    [V], 
    {averb(X, LF, V, Past, SingThrd, PresPart, PastPart, Type)}.
 
verb_phrase_2(X, future(Assn1&Assn2), *(head(future(root(V))), mods(Adv)), Number, Person, Type) -->
    [will],
    adverb_phrase(X, Assn1, Adv),
    [V], 
    {averb(X, Assn2, V, Past, SingThrd, ProsPart, PastPart, Type)}.
 
% tense: present perfect
verb_phrase_2(X, LF, head(presperf(root(Infinitive))), singular, third, Type) -->
    [has],
    [V], 
    {averb(X, LF, Infinitive, Past, SingThrd, PresPart, V, Type)}.
 
verb_phrase_2(X, Assn1&Assn2, *(head(presperf(root(Infinitive))),mods(Adv)), singular, third, Type) -->
    [has], 
    adverb_phrase(X, Assn1, Adv),
    [V],
    {averb(X, Assn2, Infinitive, Past, SingThrd, PresPart, V, Type)}.
 
verb_phrase_2(X, LF, head(presperf(root(Infinitive))), Number, Person, Type) -->
    {not(sing_third(Number,Person))},
    [have],
    [V], 
    {averb(X, LF, Infinitive, Past, SingThrd, ProsPart, V, Type)}.
 
verb_phrase_2(X, LF1&LF2, *(Adv,head(presperf(root(Infinitive)))), Number, Person, Type) -->
    {not(sing_third(Number, Person))},
    [have], 
    adverb_phrase(X, LF1, Adv),
    [V], 
    {averb(X, LF2, Infinitive, Past, SingThrd, PresPart, V, Type)}.

% tense: future perfect
verb_phrase_2(X, future(LF), head(futperf(root(Infinitive))), Number, Person, Type) -->
    [will], [have],
    [V], 
    {averb(X, LF, Infinitive, Past, SingThrd, PresPart, V, Type)}.
 
verb_phrase_2(X, future(LF1&LF2), *(head(futperf(root(Infinitive))),mods(Adv)), Number, Person, Type) -->
    [will], [have],
    adverb_phrase(X, LF1, Adv),
    [V], 
    {averb(X, LF2, Infinitive, Past, SingThrd, PresPart, V, Type)}.

verb_phrase_2(X, future(LF1&LF2), *(head(futperf(root(Infinitive))),mods(Adv)),Number, Person, Type) -->
    [will],
    adverb_phrase(X, LF1, Adv),
    [have],
    [V], 
    {averb(X, LF2, Infinitive, Past, SingThrd, PresPart, V, Type)}.
 
verb_phrase_2(X, future(LF1&LF2&LF3), *(head(futperf(root(Infinitive))),mods(Advl,Adv2)), Number, Person, Type) -->
    [will],
    adverb_phrase(X, LF1, Adv1),
    [have],
    adverb_phrase(X, LF2, Adv2),
    [V], 
    {averb(X, LF3, Infinitive, Past, SingThrd, PresPart, V, Type)}.

% Tenses for the Verb To Be - verbs of "being"
sense_verb_phrase(X, LF, Vphr,Number,Person) -->
    be_verb_phrase(X, LF, Vphr,Number, Person).
 
be_verb_phrase(X, LF, Vphr,Number,Person) -->
    be_verb_phrase_2(X, LF, Vphr, Number, Person).
 
be_verb_phrase(X, LF1&LF2, vp(Adv,Vphr),Number,Person) -->
    adverb_phrase(X, LF1, Adv),
    be_verb_phrase_2(X, LF2, Vphr, Number,Person).

% tense: past simple
be_verb_phrase_2(X, past(LF), head(past(root(be))), Number, Person) -->
    [V],
    {beverb(X, LF, V, Number, Person, past)},!.

% tense: past perfect
be_verb_phrase_2(X, past(LF), head(pastperf(root(be))), Number, Person) -->
    [had], [been].

be_verb_phrase_2(X, past(LF), *(head(pastperf(root(be))), mods(Adv)), Number, Person) -->
    [had],
    adverb_phrase(X, LF, Adv),
    [been].
 
% tense: present simple
be_verb_phrase_2(X, LF, head(present(root(be))), Number, Person) -->
    [V], 
    {beverb(X, LF, V, Number, Person, present)},!.
 
%. tense: future simple
be_verb_phrase_2(X, future(X), head(future(root(be))), Number, Person) --> [will], [be].
 
be_verb_phrase_2(X, future(LF), *(head(future(root(be))),mods(Adv)), Number, Person) -->
    [will],
    adverb_phrase(X, LF, Adv),
    [be].
 
% tense: present perfect
be_verb_phrase_2(X, X, head(presperf(root(be))), Number, Person) -->
    {not(sing_third(Number,Person))},
    [have], [been].

be_verb_phrase_2(X, LF, *(head(presperf(root(be))), mods(Adv)), Number, Person) -->
    {not(sing_third(Numlber,Person))},
    [have], 
    adverb_phrase(X, LF, Adv),
    [been].
 
be_verb_phrase_2(X, LF, head(presperf(root(be))), singular, third) --> [has], [been].
 
be_verb_phrase_2(X, LF, *(head(presperf(root(be))),mods(Adv)), singular, third) -->
    [has],
    adverb_phrase(X, LF, Adv),
    [been].
 
% tense: future perfect
be_verb_phrase_2(X, future(X), head(furperf(root(be))), Number, Person) --> [will], [have], [been].
 
be_verb_phrase_2(X, future(LF), *(head(past(root(be))),mods(Adv)), Number, Person) -->
    [will],
    adverb_phrase(X, LF, Adv),
    [have], [been].
 
 be_verb_phrase_2(X, past(LF), *(head(past(root(be))),mods(Adv)), Number, Person) -->
    [will],
    [have],
    adverb_phrase(X, LF, Adv),
    [been].
 
be_verb_phrase_2(X, past(LF1&LF2), *(head(past(root(be))),mods(Adv1,Adv2)), Number, Person) -->
    [will],
    adverb_phrase(X, LF1, Advl),
    [have],
    adverb_phrase(X, LF2, Adv2),
    [been].
%
% do / does
%
does_verb_phrase(X, do(X), head(root(do)), Number, Person) --> [V], {doverb(V, Number, Person)}.
doverb(does, singular, first).
doverb(do, plural, third).
doverb(did, _, _).
% -------------------------------------
% terminal rules
% -------------------------------------
noun(X, LF, noun(N), plural) --> [N], {is_common_noun(R, N), LF=..[R,X]}.
noun(X, LF, noun(N), singular) --> [N], {is_common_noun(N,_), LF=..[N,X]}.

determiner(X,Prop,Assn,LF,det(Det),Number) --> [Det], {is_determiner(X, Prop, Assn, LF, Det, Number)}.
 
adjective(Prop,LF,adj(Adj)) --> [Adj], {is_adjective(Adj), LF=..[Adj,Prop]}.

adjective(Prop,LF,adj(Possadj)) --> [PossAdj], {poss_adj(PossAdj), LF=..[PossAdj,Prop]}.
 
adverb(Prop,LF,adv(Adv)) --> [Adv], {is_adverb(Adv), LF=..[Adv,Prop]}.
 
preposition(Prop,LF,prep(Prep)) --> [Prep], {is_preposition(Prep), LF=..[Prep,Prop]}.

pronoun(X, LF, pron(P), Number, Person, Case) --> [P], {is_pronoun(P, Number, Person, Case), LF=..[P,X]}.
 
relative_pronoun(X,LF,rpron(P), Number, Person, Case) --> [P], {is_rel_pronoun(P, Number, Person, Case), LF=..[P,X]}.

question_pronoun(X, LF, qpron(P), Number, Person, Case) --> [P], {is_question_pronoun(P, Number, Person, Case), LF=..[P,X]}.

subordconj(Prop,LF,subconj(Conj)) --> [Conj], {is_subconj(Conj), LF=..[Conj,Prop]}.
 
auxiliary(Prop,LF,aux(Auxv)) --> [Auxv], {auxmodal(Auxv), LF=..[Auxv,Prop]}.
 
 
% ----------------------------------------------------------------------------------
% the dictionary
% ----------------------------------------------------------------------------------
 
% ---------------------------------------------------------------
% determiners
% ---------------------------------------------------------------
is_determiner(X,Prop,Assn,the(X,(Prop)),the, _).
is_determiner(X,Prop,Assn,exist(X,(Prop)),a, singular).
is_determiner(X,Prop,Assn,exist(X,(Prop)),an, singular).
is_determiner(X,Prop,Assn,that(X,(Prop)),that, singular).
is_determiner(X,Prop,Assn,this(X,(Prop)),this, singular).
is_determiner(X,Prop,Assn,this(X,(Prop)),these, plural).
is_determiner(X,Prop,Assn,that(X,(Prop & Assn)),those, plural).
is_determiner(X,Prop,Assn,all(X, (Prop ==> Assn)),all, plural).
is_determiner(X,Prop,Assn,some(X,(Prop & Assn)),some, plural). % skolemize?
is_determiner(X,Prop,Assn,many(X,(Prop & Assn)),many, plural).
is_determiner(X,Prop,Assn,most(X,(Prop & Assn)),most, plural).
is_determiner(X,Prop,Assn,few(X,(Prop & Assn)),few, plural).
is_determiner(X,Prop,Assn,not(X,(Prop & Assn)),no, plural).
is_determiner(X,Prop,Assn,all(X,(Prop ==> Assn)),every, singular).
is_determiner(X,Prop,Assn,all(X,(Prop ==> Assn)),any, _).
 
% ---------------------------------------------------------------
% the verb to be; copula
% ---------------------------------------------------------------
beverb(X, be(X), am, singular, first, present).
beverb(X, be(X), are, singular, second, present).
beverb(X, be(X), is, singular, third, present).
beverb(X, be(X), was, singular, first, past).
beverb(X, be(X), vere, singular, second, past).
beverb(X, be(X), was, singular, third, past).
beverb(X, be(X), are, plural, Person, present).
beverb(X, be(X), were, plural, Person, past).

% ---------------------------------------------------------------
% other verbs
% ---------------------------------------------------------------

averb((X,Y),want(X,Y),want,wanted,wants,wanting,wanted,transitive).
averb(X,go(X),go,went,goes,going,gone,intransitive).
averb((X,Y),know(X,Y),know,knew,knows,knowing,known,transitive).
averb((X,Y),like(X,Y),like,liked,likes,liking,liked,transitive).
averb((X,Y),cross(X,Y),cross,crossed,crosses,crossing,crossed,transitive).
averb((X,Y),beckon(X,Y),beckon,beckoned,beckons,beckoning,beckoned,transitive).
averb((X,Y,Z),give(X,Y,Z),give, gave, gives, giving, given, bitransitive).
averb((X,Y,Z),find(X,Y,Z),find, found, finds, finding, found, bitransitive).
averb((X,Y),find(X,Y),find, found, finds, finding, found, transitive).
averb((X,Y),see(X,Y),see, saw, sees, seeing, seen, transitive).
averb((X,Y),eat(X,Y),eat, ate, eats, eating, eaten, transitive).
averb(X,eat(X),eat, ate, eats, eating, eaten, intransitive).
averb((X,Y),do(X,Y),do, did, does, doing, done, transitive).
averb((X,Y,Z),do(X,Y,Z),do, did, does, doing, done, bitransitive).
averb((X,Y),insist(X,Y),insist, insisted, insists, insisting, insisted, transitive).
averb((X,Y),worry(X,Y),worry, worried, worries, worrying, worried, transitive).
averb(X,think(X),think, thought, thinks, thinking, thought, intransitive).
averb(X,die(X),die,died,dies,dying,died,intransitive).
averb((X,Y),have(X,Y),have,had,has,having,had,transitive).
averb((X,Y),need(X,Y),need, needed, needs, needing, needed, transitive).
averb(X,work(X),work, worked, works, working, worked, intransitive).
averb((X,Y,Z),teach(X,Y,Z),teach, taught, teaches, teaching, taught, bitransitive).
averb((X,Y),learn(X,Y),learn, learned, learns, learning, learned, transitive).
averb((X,Y),speak(X,Y),speak, spoke, speaks, speaking, spoken, transitive).
averb((X,Y),love(X,Y),love, loved, loves, loving, loved, transitive).
averb(X,move(X),move, moved, moves, moving, moved, intransitive).
averb((X,Y),duplicate(X,Y),duplicate, duplicated, duplicates, duplicating, duplicated, transitive).
averb((X,Y),take(X,Y),take, took, takes, taking, taken, transitive).
averb(X,wait(X),wait, waited, waits, waiting, waited, intransitive).
averb((X,Y),get(X,Y),get, got, gets, getting, gotten, transitive).
averb((X,Y),say(X,Y),say, said, says, saying, said, transitive).
averb((X,Y),break(X,Y),break, broke, breaks, breaking, broken, transitive).
averb((X,Y),lose(X,Y),lose, lost, loses, losing, lost, transitive).
averb((X,Y),continue(X,Y),continue, continued, continues, continuing, continued, transitive).
averb((X,Y),let(X,Y),let, let, lets, letting, let, transitive).
averb(X,run(X),run, ran, runs, running, ran, intransitive).
averb(X,show(X),show, showed, shows, showing, showed, intransitive).
averb(X,play(X),play, played, plays, playing, played, intransitive).
averb(X,trace(X),trace, traced, traces, tracing, traced, intransitive).
averb(X,define(X),define, defined, defines, defining, defined, intransitive).
averb((X,Y),fill(X,Y),fill, filled, fills, filling, filled, transitive).

%averb((X,Y),LF, Root,V,_,_,_,transitive) :- atom(V), morphit(V,List,Out), check_list(v,List,Out,Num,Root), LF=..[Root,X,Y].
%averb((X,Y,Z)),LF, Root,V,_,_,_,bitransitive) :- atom(V), morphit(V,List,Out), check_list(v,List,Out,Num,Root), LF=..[Root,X,Y,Z].
%averb(X,LF, Root,V,_,_,_,intransitive) :- atom(V), morphit(V,List,Out), check_list(v,List,Out,Num,Root), LF=..[Root,X].

%averb((X,Y),LF, Root,_,V,_,_,transitive) :- atom(V), morphit(V,List,Out), check_list(v,List,Out,Num,Root), LF=..[Root,X,Y].
%averb((X,Y,Z),LF, Root,_,V,_,_,bitransitive) :- atom(V), morphit(V,List,Out), check_list(v,List,Out,Num,Root), LF=..[Root,X,Y,Z].
%averb(X,LF, Root,_,V,_,_,intransitive) :- atom(V), morphit(V,List,Out), check_list(v,List,Out,Num,Root), LF=..[Root,X].

%averb((X,Y),LF, Root,_,_,V,_,transitive) :- atom(V), morphit(V,List,Out), check_list(v,List,Out,Num,Root), LF=..[Root,X,Y].
%averb((X,Y,Z),LF, Root,_,_,V,_,bitransitive) :- atom(V), morphit(V,List,Out), check_list(v,List,Out,Num,Root), LF=..[Root,X,Y,Z].
%averb(X,LF, Root,_,_,V,_,intransitive) :- atom(V), morphit(V,List,Out), check_list(v,List,Out,Num,Root), LF=..[Root,X].

%averb((X,Y),LF, Root,_,_,_,V,transitive) :- atom(V), morphit(V,List,Out), check_list(v,List,Out,Num,Root), LF=..[Root,X,Y].
%averb((X,Y,Z),LF, Root,_,_,_,V,bitransitive) :- atom(V), morphit(V,List,Out), check_list(v,List,Out,Num,Root), LF=..[Root,X,Y,Z].
%averb(X,LF, Root,_,_,_,V,intransitive) :- atom(V), morphit(V,List,Out), check_list(v,List,Out,Num,Root), LF=..[Root,X].

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
is_adverb(A) :- atom(A), morphit(A,List,Out), check_list(r,List,Out,Num,Root). % s(A,_,_,r,_,_).
is_adverb(A) :- atom(A), morphit(A,List,Out), check_list(s,List,Out,Num,Root). % s(A,_,_,s,_,_).
 
% ---------------------------------------------------------------
% proper nouns 
% ---------------------------------------------------------------
proper_noun(Name) :- atom(Name), atom_codes(Name, Codes2), head(Codes2, First), char_type(First,upper), !.
proper_noun(Name,Unquoted_name) :- atom(Name), atom_codes(Name, Codes2), head(Codes2, First), char_type(First,quote), unquote(Codes2, Codes1),atom_codes(Unquoted_name, Codes1),!.

% ---------------------------------------------------------------
% nouns
% ---------------------------------------------------------------
% ---------------------------------------------------------------
% count nouns
% ---------------------------------------------------------------
%is_common_noun(mortal, mortals).
%is_common_noun(mortal, mortal).
is_common_noun(N,_) :- atom(N), morphit(N,List,Out), check_list(n,List,Out,Num,N).
is_common_noun(Root,N) :- atom(N), morphit(N,List,Out), check_list(n,List,Out,Num,Root).

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
is_pronoun('I', singular, first, nominative).
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

is_question_pronoun(who, singular, third, nominative).
is_question_pronoun(what, singular, third, nominative).
is_question_pronoun(where, singular, third, nominative).
is_question_pronoun(when, singular, third, nominative).
is_question_pronoun(how, singular, third, nominative).
is_question_pronoun(whose, Number, Person, possessive).
is_question_pronoun(whom, Number, Person, objective).
 
is_rel_pronoun(who, Number, third, nominative).
is_rel_pronoun(whom, Number, third, objective).
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
 * Prover
 */

prove(true,RB) :- !,
    %trace_it(('true',RB)),
    true.

prove(A,[A]) :- !,
    %trace_it(('Fact',A)),
    true.

prove(A=A,_) :- !,
    %trace_it(('equality',A)),
    true.

prove((A,B),RB) :-
    %trace_it(('Prove ',B,RB)),
    prove(B,RB),
    %trace_it(('Prove ',A,RB)),
    prove(A,RB).

prove(A,RB) :-
    %trace_it(('Prove ',A,RB)),
    find_clause((A:-B),RB),
    %trace_it(('Found ',A,':-',B)),
    prove(B,RB).

prove(A,RB) :-
    %trace_it(('Prove ',A,RB)),
    find_clause(A,RB),
    true.%trace_it(('Found ',A,'in',RB)).

prove(who(A),RB) :-
    %trace_it(('Prove ',A,RB)),
    atom(A),
    find_clause(C,RB),
    functor(C, F, 1),
    C=..[F|[A]],
    prove(C, RB),
    fail.%trace_it(('Found ',A,'in',RB)).

prove(who(A),RB) :-
    %trace_it(('Prove ',A,RB)),
    functor(A, W, 1),
    prove(A,RB),
    fail.%trace_it(('Found ',A,'in',RB)).

prove(who(A),RB) :- !,true.

prove(_,_) :- !,fail.

find_clause(C,(C:-B)) :-
    true.%trace_it(('find_clause a ',C)).
find_clause(C,C) :-
    true.%trace_it(('find_clause aa ',C)).
find_clause(C,[Head|_]) :-
    %trace_it(('find_clause b ',C)),
    find_clause(C,Head).
find_clause(C,[_|Tail]) :-
    %trace_it(('find_clause c ',C,' rest ',Tail)),
    find_clause(C,Tail).

transform((A,B),[(A:-true)|Rest]) :- !,
    transform(B,Rest).
transform(all(X,Y==>Z),[(Z:-Y)]).
transform(exist(X,Y==>Z),[((Y:-true),(Z:-true))]).
transform(exist(X,Y),[Y]).
transform(exist(X,Y&Z),[((Y:-true),(Z:-true))]).
transform(some(X,Y&Z),[((count(Y,CY)),(count(Z,CZ),(C is CY/CZ, C>0.1)))]).
transform(many(X,Y&Z),[((count(Y,CY)),(count(Z,CZ),(C is CY/CZ, C>0.5)))]).
transform(most(X,Y&Z),[((count(Y,CY)),(count(Z,CZ),(C is CY/CZ, C>0.8)))]).
transform(few(X,Y&Z),[((count(Y,CY)),(count(Z,CZ),(C is CY/CZ, C<0.1)))]).
transform(not(X,Y&Z),[((count(Y,CY)),(count(Z,CZ),(CY=0.0, CZ>0.0)))]).
transform(A&B,(A,B)) :- !.
transform(A,A) :- !.

/*
 * NL generation
 */

% generate sentences
show_answer([]).

show_answer([H|T]) :-
    show_answer(H),
    show_answer(T).

show_answer(Clause) :-
    generate_nl(Clause),writeln('.')
    .%,writeln(Clause).

generate_nl([]) :- !.
generate_nl(true) :- !.
generate_nl([A|T]) :- !,
    write(A),
    generate_nl(T).
generate_nl(A) :- var(A), !,
    A=x,write(A).
generate_nl(A) :- atom(A), !,
    write(A).
generate_nl((A,B)) :- !,
    generate_nl(A),
    generate_nl(B).

generate_nl((A:-true)) :- !,
    generate_nl(A).

generate_nl((A:-B)) :-
    %trace_it(('generate_nl b ',A)),
    generate_nl(A),
    generate_nl(' if '),
    %trace_it(('generate_nl c ',B)),
    generate_nl(B).

% arity one - man('John')
generate_nl(A) :-
    functor(A, F, 1),
    A=..[H|Arg],
    %trace_it(('generate_nl1 d ',A,H,Arg)),
    generate_nl(Arg),
    generate_nl(' is a '),
    %trace_it(('generate_nl1 d2 ',A,H,Arg)),
    generate_nl(H).

% arity two - likes(john,mary)
generate_nl(A) :-
    functor(A, F, 2),
    A=..[H,Arg1,Arg2],
    %trace_it(('generate_nl2 d ',A,H,Arg1,Arg2)),
    averb(_,_,H, _, NewH, _, _, _),
    %trace_it(('generate_nl2 d1 ',A,H,Arg1,Arg2)),
    generate_nl(Arg1),
    %trace_it(('generate_nl2 d2 ',A,H,Arg1,Arg2)),
    generate_nl(' '),
    generate_nl(NewH),
    generate_nl(' '),
    %trace_it(('generate_nl2 d3 ',A,H,Arg1,Arg2)),
    generate_nl(Arg2).

% arity two - likes(john,mary)
generate_nl(A) :-
    functor(A, F, 2),
    A=..[H,Arg1,Arg2],
    %trace_it(('generate_nl2 d ',A,H,Arg1,Arg2)),
    generate_nl(Arg1),
    %trace_it(('generate_nl2 d2 ',A,H,Arg1,Arg2)),
    generate_nl(' '),
    generate_nl(H),
    generate_nl(' '),
    %trace_it(('generate_nl2 d3 ',A,H,Arg1,Arg2)),
    generate_nl(Arg2).

% arity three - gave(mary,john,X) & X=
generate_nl(A) :-
    functor(A, F, 3),
    A=..[H,Arg1,Arg2,Arg3],
    %trace_it(('generate_nl3 d ',A,H,Arg1,Arg2)),
    generate_nl(Arg1),
    %trace_it(('generate_nl3 d2 ',A,H,Arg1,Arg2)),
    generate_nl(' '),
    generate_nl(H),
    %trace_it(('generate_nl3 d3 ',A,H,Arg1,Arg2)),
    generate_nl(' '),
    generate_nl(Arg2),
    %trace_it(('generate_nl3 d4 ',A,H,Arg1,Arg2)),
    generate_nl(' '),
    generate_nl(Arg3).

generate_nl([H|T]) :-
    trace_it(('generate_nl e ',H,T)),
    generate_nl(H),
    generate_nl(T).

% show the rules in the Rule Base in English
show_rules([]).
show_rules([H|T]) :-
    show_rules(H),
    show_rules(T).
show_rules(Rule) :-
    transform(Rule, Clauses),
    show_answer(Clauses).

% execute the logical form

do_it(show('Rules'), RuleBase) :- show_rules(RuleBase).
do_it(LF, RuleBase) :- do_it(LF).

do_it(trace('On')) :- assert(tracing('On')).
do_it(trace('Off')) :- retractall(tracing(_)).
do_it(trace('Parse')) :- assert(tracing_parse('On')).
do_it(trace('Parseoff')) :- retractall(tracing_parse(_)).

do_it(define(X)) :- proper_noun(X,Unquoted_name), definition(Unquoted_name).
do_it(X) :- !, write("Don't know how to "),write(X),nl.

handle_logical_form(question(LF), RuleBase) :-
    transform(LF, Clauses),
    %trace_it(('Proving ',LF,Clauses,'in',RuleBase)),
    prove(Clauses, RuleBase),
    %trace_it(('Proved ',LF,Clauses,'in',RuleBase)),
    show_answer(Clauses).

handle_logical_form(question(LF), RuleBase) :-
    transform(LF, Clauses),
    write("I can't prove "),
    show_answer(Clauses).

handle_logical_form(statement(LF), RuleBase) :-
    transform(LF, Clauses),
    show_answer(Clauses),
    %trace_it(('Adding',Clauses,' to ',RuleBase)),
    nl_shell([Clauses|RuleBase]).

handle_logical_form(imperative(LF), RuleBase) :-
    transform(LF, Clauses),
    do_it(Clauses, RuleBase),!.

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

s_type([.],statement) :- !.
s_type([?],question) :- !.
s_type([!],imperative) :- !.
s_type(X,X) :- !.

split_atom(S, A, L) :- atomic_list_concat(XL, S, A), delete(XL, '', L).

% if tale is ? or ! or . then remove
% A:Atom, R:Removed, T:special mark
tail_not_mark(A, R, T) :- atom_concat(R, T, A), is_terminal_punc(T),!.
tail_not_mark(A, R, '') :- A = R.

headtail([H|T], H, T).
tail([_|T], T).
head([H|_], H).

capitalize([], []).
capitalize([H1|T], [H2|T]) :- code_type(H2, to_upper(H1)).

unquote([], []).
unquote([H1|T], T2) :- char_type(H1,quote), unquote(T,T2).
unquote([H1|T], [H1|T2]) :- unquote(T,T2).

trim_period([.],[]).
trim_period([X|R],[X|T]) :- trim_period(R,T).

% pretty print parse form
nspaces(N) :- N > 0, write(' '), N1 is N - 1, nspaces(N1).
nspaces(_).

pp(X,0) :- writeln(X).
pp(X,_) :- var(X).
pp(X,NN) :- nonvar(X), functor(X, F, N), !, nspaces(NN), writeln(F), NN1 is NN + 1, nspaces(NN1), ppa(X,1,N,NN1).
pp(X,NN) :- nspaces(NN), writeln(X).
ppa(X,N,T,NN) :- N =< T, !, nspaces(NN), arg(N,X,A), pp(A,NN), N1 is N + 1, NN1 is NN + 1, ppa(X,N1,T,NN1).
ppa(_,_,_,_).

definitions([]) :- !.
definitions(H) :- atom(H), definition(H),!.
definitions([H|T]) :- definition(H), !, definitions(T).

cat(n,noun) :- !.
cat(a,verb) :- !.
cat(a,adjective) :- !.
cat(r,adverb) :- !.
cat(pn,proper_noun) :- !.
cat(v,verb) :- !.
cat(X,X) :- !.
    
definition(Word) :-
    s([Word|_],Number,_,Category,_,_),
    cat(Category,Cat),
    write(Word),write('('),write(Cat),write('): '),
    g(Number,Definition),
    writeln(Definition),
    fail.
definition(Word) :- true.

check_for_missing_vocabulary_words([]) :- !.
check_for_missing_vocabulary_words([H|T]) :- !,
    check_for_missing_vocabulary_words2(H),
    check_for_missing_vocabulary_words(T).

check_for_missing_vocabulary_words2(Word) :-
    proper_noun(Word);
    s(Word,_,_,_,_,_);
    is_preposition(Word);
    is_subconj(Word);
    is_pronoun(Word, _, _, _);
    is_rel_pronoun(Word, _, _, _);
    is_common_noun(Word,_);
    is_adverb(Word);
    is_adjective(Word);
    averb(_,_,Word, _, _, _, _, _);
    averb(_,_,_, Word, _, _, _, _);
    averb(_,_,_, _, Word, _, _, _);
    averb(_,_,_, _, _, Word, _, _);
    averb(_,_,_, _, _, _, Word, _);
    beverb(_, _, Word, _, _, _);
    doverb(Word, _, _);
    is_determiner(_,_,_,_,Word, _).


check_for_missing_vocabulary_words2(Word) :-
    write("I don't know the word '"),write(Word),writeln("'.").

/*
 * Main parse entry point
*/

parse :-
    nl_shell([me('Alexa')]).

nl_shell(RuleBase) :-
    %trace_it(('New shell',RuleBase)),
    write(':'),flush,
    input_to_atom_list(Input),
    headtail(Input, Root, Punctuation),
    get_time(T1),
   ( Root == [q] -> halt;
       ( % if
            %s_type(Punctuation, S_type), write(S_type), write(': '), writeln(Root),
            sentence(Logical_form, Parse_form, Root, []), !,
            write('Logical Form: '),writeln(Logical_form),
            ( tracing_parse('On') -> writeln('Parse Form: '),pp(Parse_form,1),nl; true),
            handle_logical_form(Logical_form, RuleBase),
            get_time(T2),
            Msec is (T2 - T1) * 1000,
            format('~2f~w~n', [Msec,msec]),
            nl_shell(RuleBase);
         % else
            get_time(T2),
            Msec is (T2 - T1) * 1000,
            format('~2f~w~n', [Msec,msec]),
            write("Pardon?"),nl,
            check_for_missing_vocabulary_words(Root),
            nl_shell(RuleBase)
        )
     ).

