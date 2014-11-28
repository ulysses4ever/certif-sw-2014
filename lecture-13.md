# Reasoning about simple programming language

We are going to verify programs on simple imperative programming language called **Imp**
we are going to describe briefly. This is a review of several chapters from
“Software Foundations”.

Consider example on Imp with `while`-loop.

    Z ::= X;;
    Y ::= 1;;
    WHILE not (Z = 0) DO
        Y := Y × Z;;
        Z := Z - 1
    END

Clearly this calculate factorial.

More generally, Imp language has

* expressions
    * arithmetic
    * boolean
* commands
    * sequencing
    * assignments
    * conditions
    * loops

We have three main goals:

* to define a _meaning of a program_,
* to compile a program,
* to reason about program transformation correctness.

Let's see example for definition of an inductive type for identifiers.

    Inductive id : Type :=
        Id nat → id.
    
    Theorem eq_id_dec: \forall id1, id2 : id, {id1 = id2} + {id1 =/= id2}.

In this lecture we're not going to prove theorems but just see what could be done
by means of Coq's proofs.

We have three more inductive types: for program state (a number of variables 
which have assigned values), expressions and commands.

We have to write programs using our Coq-definitions for building Imp programs
because we have no **parser** for the plain Imp programs (as in the very first example).
Nevertheless, we could have build such a parser on Coq following corresponding
discussion in “Software Foundations”.

We can define Imp terms which does not terminate. So far it is completely
legal, though Coq itself does not allow for endless computations.

## Evaluation of Imp terms

Definition for evaluation in our approach is the mapping from Imp terms to
well-known mathematical operations without specifying actual values of variables.
We say that this is **giving semantics** to Imp programs. 

    Fixpoint aeval (st: state) (a: aexp) : nat := match a with
        ANum n => n
        …
    Fixpoint beval (st: state) (b: bexp) : bool := match b with
        BTrue => true
        …
        BEq a1 a2 => …

Trying to specify semantics for while we encounter a problem. We're trying to
define a Coq expression by means of the same expression adding something to it.

    Fixpoint ceval (st: state) (c: com) : state := match c with
        …
        | WHILE b DO c1 END =>
            if (beval st b)
                then ceval st (c1; WHILE b DO c1 END)
                else st

In this case Coq can't prove termination and rejects our definition.

There are two ways to solve the problem.

1. Add hidden index of iterations and limit it to some “large” value.
2. Make definition of evaluation relational (to reflect that `ceval` function
   is _partial function).

We take second approach and end-up with what is called 
**Big-Step Operational Semantics** (or **natural semantics**).

The problem with relational definitions in Coq is that we have to prove every fact 
that we could left for Coq to _compute_ in funcitional approach.

## Compilation

To compile program usually means to transform a program to a sequence of
instruction for particular processor. It differs from evaluation , which
means to transform a program to a value.

We describe hot to transform only arithmetic expressions to some abstract
stack machine. The instruction set of the machine is described in Coq below:

    Inductive sinstr: Type :=
        | SPush  : nat → sinstr
        | SLoad  : id → sinstr
        | SPlus  : sinstr
        | SMinus : sinstr
        | SMult  : sinstr

No we principally can define the correctness of compilation: we can prove that
evaluation of every Imp program will end up just the same as evaluation of
compiled program. But we won't do this. We'll learn such kind of proof on the next
lecture, when exploring certified C compiler **CompCert**.

## Behavioural Equivalence and Program Transformation

To say that two programs are behaviourally equivalent is to state that these two
programs always evaluate to the same.

Note that evaluation is not that usually function so we cannot define behavioural
equivalence as an equality of results of this function. Instead we have to
prove that `ceval` relation for one program with some result holds if and
only if the relation holds for other program with the same result.

One more technical difficulty with stating behavioural equivalence is that a
result of `ceval` is a state i.e. a function. There are ways to prove equality
for the kind of functions.

After defining notion of behavioural equivalence we can define a notion of
program transformation as a function from a `com` to `com` (the type for command
and so for the whole program). We also are able to define which transformations
are **sound** i.e. results in behaviourally equivalent program. One of the 
simplest example of sound transformation is _constant folding_, see slides
for this lecture for the code of it.

## Small-step operational semantics

In big-step operational semantics it is impossible to tell between non-terminating
programs and incorrect programs like those containing things like `3 + Plus`.
This problem is solved in different style of semantics called
**small-step operational semantics**. 

Consider a toy language with just integer constants and plus. BSOS gives
following rule for plus (we call constructor for it `P`).

    t1 => n1, t2 => n2
    ---
    P t1 t2 => C (n1 + n2)

SSOP gives two rules:

    t1 => t1'
    ---
    P t1 t2 => P t1' t2

    
    t2 => t2'
    ---
    P (C n1) t2 => P (C n1) t2'

SSOS enjoys a number of nice properties. First, it has **strong progress**
property: every correct term is either value or could be reduced using our
rules further. We also can prove that SSOS and BSOS agree.

