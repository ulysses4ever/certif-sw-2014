## Intro

There are different notions of being certified. Sometimees you don't even need
to be certified. But there are several classes of SW which we can't afford to
have bugs in. Though this approach is not part of everyday SW development yet
and more part of scientific theory.

It is common to use **typing** to obtain more control on our SW. There are 
languages with either _dynamic_ or _static_ typing. 

    var a: integer of 1..5
    a = 5   // correct
    a = 42  // ERROR!

Either way of using compiler provide
us with some assurance of our SW to be free of bugs.

Another popular way to assure that there is no (not that much) bugs in SW is
**testing**.
    
    f(a, b) = a + b
    ...
    f(3, 5) == 8
    f(-1, -2) == -3

At last, we have about 40 years of **formal methods**: a branch of computer
science which try to establish SW correctness fundamentally. Methods coined by
FM used to be extremely hard to apply inreal-world applications. FM have some 
inherent problems, e.g. if you're proving correctness of a piece of a SW with
assitance of another piece of SW, how can we be sure of the latter to be 
correct. THe role of this very first everyone trusted subject wi wil use
**mathematical logic**.

== Coq proof assistant

Coq provides facility for interactive proving. It is accessible through on of 
the following:

*   coqide (already seen in the lab),
*   coqc (a compiler),
*   proof-general (mode for emacs text editor)    

There are two programming languages inside Coq:

*   _Gallina_ (`Proof`, `Fact`, etc.), 
*   _Vernacular_ (`forall`, `assumption`).

In fact there ar some more PLs inside Coq. E.g. _ltacs_ for defining new tactics.

Coq have two levels:

*   small kernel, consisting only of terms and types
    (“no proofs” as these ARE proofs) ;
*   environment: high level commands (tactics, etc.)

