# Semantic-based Natural Language Processing in Prolog

A semantic-based NL in Prolog for a discourse-based interface to Alexa.

So, I added an extensive DCG grammar by Gurney et al, based for the most part on Warren and Perriera, added some WORDnet dictionary and morphology interfaces, and added a nod to McCord for the Logical Form ideas.

Came to a conclusion that 1) the grammar is very brittle 2) the semantic logical form is brittle 3) the ontology is brittle and that this approach is not what humans do at all.

So, had the simple idea to add a command to query a word, then get data about that word from Wikipedia, try to parse the information returned and grow the prolog knowledge base. 

Hmmm... still working on this...

## How to Run

nl2.pl is a script that uses SWI Prolog on Mac OSX. To run it:

```
./nl2.pl
```
Then:
```
hi.
```

## Examples

Try: 

```
John is a man.
all men are mortal.
is John mortal?
who is mortal?
John likes Mary.
who does John like?

what does 'dinosaur' mean?

woo hoo! There's a long drawn out disaster as the attempt at assimilating the wiki definition proceeds....

```

There are some handy hooks:

```
wiki 'kangaroo'.            // show wiki entry for kangaroo

trace Off.                  // quiet! Turn off all this debug information!
trace Prover.               // shows the prover steps
trace Finder.               // shows the database finder steps
trace English.              // shows the NL generation steps
trace Grammar.              // traces all the grammar rules
trace Logicalform.          // shows the Logical Form
trace Parser.               // shows the parse tree

play The Beatles.           // Needs to get hooked to Alexa.
show Rules.                 // shows the current RuleBase in English
save Rules.                 // saves the current RuleBase for reload on next startup.

```

# Next Steps

Hmmm.. Perceptrons, Deep Learning... Neural Nets... TDB...

# References

Warren and Perriera: CHAT-80

Winograd: SHRDLU

ProNTo = Prolog Natural Language Tools, Unversity of Georgia, http://ai1.ai.uga.edu/mc/pronto/

WordNET, A lexical database ofr English, https://wordnet.princeton.edu

MODL, Modular Logic Grammars, Michael McCord, IBM T.J. Watson Research Center

