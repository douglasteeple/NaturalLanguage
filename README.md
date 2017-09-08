# Semantic-based Natural Language Processing in Prolog

A semantic-based NL in Prolog for a discourse-based interface to Alexa.

So, I added an extensive DCG grammar by Gurney et al, based for the most part on Warren and Perriera, added some WORDnet dictionary and morphology interfaces, and added a nod to McCord for the Logical Form ideas.

Came to a conclusion that 1) the grammar is very brittle 2) the semantic logical form is brittle 3) the onotology is brittle and that this apparoach is not what humans do at all.

So, had the simple idea to add a command to query a word, get data from Wikipedia, try to parse it to add information to the prolog knowledge base. Hmmm... still working on this...

# References

ProNTo = Prolog Natural Language Tools, Unversity of Georgia, http://ai1.ai.uga.edu/mc/pronto/

WordNET, A lexical database ofr English, https://wordnet.princeton.edu

MODL, Modular Logic Grammars, Michael McCord, IBM T.J. Watson Research Center

