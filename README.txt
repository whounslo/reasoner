Common Lisp Reasoner, Version 3.5


What is it?
-----------

The Common Lisp Reasoner extends the Common Lisp Object System (CLOS) to
incorporate a powerful rule language suitable for all kinds of reasoning
tasks, vanilla XML and RDF/XML interfaces, and support for a variety of
AI-related applications, such as scheduling, planning and diagnosis.

Status
------

It has been tested in Allegro 9.0, clisp 2.48, ECL 13.5.1, LispWorks 6.1.1
and SBCL 1.1.2 (Win32).

It should run unmodified in any Lisp that implements the metaobject
protocol, and can be used in conjunction with Closer to MOP
(common-lisp.net/project/closer/).

The file compat.lisp may enable it to work (possibly with a little additional
customization) in other Lisps.

Automatically-generated reader methods (i.e., that behave like
slot-value-reduce) work only in SBCL of the above-mentioned Lisps.  Use
Closer to MOP to fill this lacuna.

Changes Since Last Release
--------------------------

During deserialization, if elements contain many subelements, the
variable *count-subelements* may be bound to nil, or the method
count-subelements-p specialized, to eliminate the considerable
overhead of maintaining a count of these values.

Bug fixes:

XML Schema deserialization failed in clisp due to defaulting of
:direct-superclasses argument if class exists.

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