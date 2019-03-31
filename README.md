rlzrs: A coq library for abstract realizability. The only dependency is ssreflect. It is tested with coq version 8.9.0 and ssreflect version 1.7. To install the library, copy its files to a local folder (best you just clone the repository). Then run "make" and "make install" and you are all set.

------------------------------------

This library used to be part of my coqrep library, but I found it also useful in other applications so I decided to separate it. It relies on the mf library that can be found in the mf repository of my github account. It is meant to do abstract realizability and features very intersting names! The main object is a pair of sets Q and A with a surjective multivalued function going from Q to A. This is called an interview. The names Q and A are for "questions" and "answers" and one way to think about this is that the function, called the "conversation" assigns to some questions a set of answers. The interviewed person may not speak without being asked, thus the conversation is surjective. On the other hand the interviewer may not get an answer to all of his questions, so the conversation need not be total and also may get different answers on repeaded questions. Thus the conversation may be multivalued. If it is singlevalued it is called a dictionary. Makes sense, right?

The part about dictionaries assumes Functional extensionality, so if you want to work axiom-free you should avoid it and import only the all_ntrvw.v file instead of all_rlzrs.v file.
