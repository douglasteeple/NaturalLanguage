/*
 * Interface to Wikipedia
*/
:- use_module(library(http/http_open)).
:- use_module(library(http/http_json)).
:- use_module(library(http/json)).
:- use_module(library(http/json_convert)).
:- use_module(library(uri)).

formatwikiextract(json([(batchcomplete=_), (query=json([_, (pages=json([_=json([_,title=T,missing=_])]))]))]),A) :-
    atomic_list_concat(['Cant find information about ',T],A).

formatwikiextract(json([(batchcomplete=_), (query=json([_, (pages=json([_=json([_,_,title=_,extract=Extract])]))]))]), Extract).

wiki(Q,A) :-
    uri_normalized(Q,QN),
    atom_concat('http://en.wikipedia.org/w/api.php?action=query&prop=revisions&prop=revisions&prop=extracts&format=json&exintro=&titles=',QN,Query),
    http_open(Query, In, [user_agent('NL/1.1 (https://douglasteeple.com/NL/; doug@douglasteeple.com) BasedOnSuperLib/1.4')]),
    json_read(In, Prolog),
    formatwikiextract(Prolog,A),
    close(In).
