Common Lisp Reasoner, Version 3.6


What is it?
-----------

The Common Lisp Reasoner extends the Common Lisp Object System (CLOS) to
incorporate a powerful rule language suitable for all kinds of reasoning
tasks, vanilla XML and RDF/XML interfaces, and support for a variety of
AI-related applications, such as scheduling, planning and diagnosis.

Status
------

It has been tested in Allegro 10.0, clisp 2.48, ECL 13.5.1, LispWorks 6.1.1
and SBCL 1.3.21.

It should run unmodified in any Lisp that implements the metaobject
protocol, and can be used in conjunction with Closer to MOP
(https://common-lisp.net/project/closer/).

The file compat.lisp may enable it to work (possibly with a little additional
customization) in other Lisps.

Automatically-generated reader methods (i.e., that behave like
slot-value-reduce) work only in SBCL of the above-mentioned Lisps.  Use
Closer to MOP to fill this lacuna.

Changes Since Last Release
--------------------------

A variant of the standard ATMS, basic-atms, which uses less storage, has
been introduced.

The distinguished false node has been incorporated into the ATMS object,
making it easier to create and use multiple ATMSs.  add-contradiction and 
added-assumption now require a tms argument.

Bug fixes:

A non-local exit from a user-supplied method within backtrack caused a
return value of nil to be cached.

Checking of class hierarchy slot type compatibility, once an instance
had been created, thwarted the redefinition of multiple classes.

Installation
------------

Use the .asd files accompanying this file.

The 'p' variants of these files establish a dependency on lparallel
(lparallel.org).  (You will need to force recompilation if you switch
variants, unless you're good at configuring ASDF.)

The files xmlic.lisp and xmlis.lisp interface to the CLLIB and SAX
(CXML, Allegro) XML parsers, respectively.  reasoner-cxml.asd may be
used to load CXML.

Evaluate (in-package :rs-user) to use the demos.

Acknowledgement
---------------

I am indebted to many people (too many to mention individually) whose ideas
have helped shape this work.

Author/Maintainer
-----------------

Dr William Hounslow
whounslo@gmail.com