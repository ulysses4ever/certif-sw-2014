# CompCert C compiler

We start with more realistic definition of _compilation_. 

> We consider **compilation** as any automated translation from one language to another. 

There are some additional requirements to a process to be called compilation. E.g.
we want compilation to be an _efficient translation_ from _source language_
(understandable by programmers) to a _machine language_ (understandable by 
programmers). 

We also want the procedure to be _correct_, i.e. free from bugs. But there are
several kind of bugs:

* bugs in software,
* miscompilation (bugs in compiler)
    * crushes in compile-time (“compiler panic”),
    * production of incorrect executable.


Is miscompilation a real problem? For the most cases it is not: **non-critical**
software usually has lots of bugs by itself. One more bug doesn't matter much.

There are cases however when we want **critical** bug-free software. In such
cases many specific techniques are used to be sure that there are no bugs in 
software. This is implemented in special _workflow_ using many sophisticated
tools (model-checking, simulation, etc. via Simulink, Scade, etc. to name some).
In this workflow verified compiler is a tool of necessity. 

## Approaches to trusted compilation

First we want to define what _behaviour_ is. We'll be particular interested in 
_observable behaviour_:

* termination,
* devergence,
* crushing with undefined ops,
* ???

We formulate a notion of **preservation** in its strong form as follows:

    ∀B, S⇓B ⇔ C⇓B

which means:

> For any behaviour _B_ source code has this behaviour _B_ if and only if
> compiled code also has _B_.

In fact this is too restrictive. There are number of cases we can relax it.
We formulate _relaxed form of preservation_ as follows:

    if S — safe ⇒ (C⇓B ⇒ S⇓B)
    
We need to add here deterministic requirements: there should exist only one
behaviour for any compiled program as well as source program.

     ∀B ∉ Wrong ⇒ (S⇓B ⇒ C⇓B)

### Specification

Specification is a predicate of the observable behaviour. We say that compiled
program _C_ satisfies the specification _Spec_, and write _C_ ⊧ _Spec_, if
_C_ cannot go wrong (_C_ is safe) and all its behaviours _B_ satisfy _Spec_.

### Verification and Validation

…

## Overview of CompCert

There are lots of transformation phases inside CompCert. Some of initial and final
are not verified yet. Correctness of every verified step is proved independently. 
They have eight intermediate languages all of which are implemented purely in 
Coq.

Perfomance of CompCert is comparable with optimized GCC (possibly, a little worse).

