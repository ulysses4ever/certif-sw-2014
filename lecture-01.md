# Unit 1. Basic Prove and Programming

## Intro

There are different notions of being certified. Sometimes you don't even need
to have your software (SW) certified. But there are several classes of 
SW which we can't afford to
have bugs in. This topic is not part of everyday SW development yet
and more part of scientific theory.

It is common to use **typing** to obtain more control on our SW. There are 
languages with either _dynamic_ or _static_ typing.

    var a: integer of 1..5
    a = 5   // correct
    a = 42  // ERROR!

Either way of using compiler provide us with some assurance of our SW to be free
of bugs.

Another popular way to assure that there is no (not that much) bugs in SW is
**testing**.
    
    f(a, b) = a + b
    ...
    f(3, 5) == 8
    f(-1, -2) == -3

At last, we have about 40 years of **formal methods** (FM): a branch of computer
science which try to establish SW correctness fundamentally. Methods coined by
FM used to be extremely hard to apply in real-world applications. FM have some 
inherent problems, e.g. if we're proving correctness of a piece of a SW with
assistance of another piece of SW, how can we be sure of the latter to be 
correct? The role of this very first everyone trusted subject will be played for
us by **mathematical logic**.

## Coq proof assistant

[Coq](http://coq.inria.fr/) provides facility for interactive proving. It is 
accessible through one of the following:

*   coqide (already seen in the lab),
*   coqc (a compiler),
*   proof-general (mode for Emacs text editor).

There are two programming languages inside Coq:

*   _Vernacular_ (`Proof`, `Fact`, etc.), 
*   _Gallina_ (`forall`, `\/`, etc.).

In fact there are some more PLs inside Coq. E.g. _Ltac_ for defining new tactics.

Coq have two levels:

*   small kernel, consisting only of terms and types
    (“no proofs” as these ARE proofs, see below Curry—Hovard) ;
*   environment: high level commands (tactics, etc.)

### How to use Coq (to get certified SW)

There are several ways…

1.  Write a program `p` in Coq and then state a theorem: “`p` is correct”. E.g.
    
        fun sort: array -> array
        proof: forall a, sort(a) is sorted
        
    More exact statement on what is it to be “correct” is usually quite
    hard to make and more not that efficient. 
    
2.  Include correctness statements in the `p` itself:

        fun sort: array -> sorted array
        
    The proof and the program is the same here. We use a feature called
    **dependent types** here.
    
3.  Write a program in any language, then write an **analyzer** in Coq.

4.  **Program extraction**. Write program in Coq (as in second way) and then
    extract a program in different language from it. At present you may 
    extract programs in _Haskell_ or _Ocaml_.

We will use the second approach, that is programming with dependent types.

## Foundations of Coq

_Disclaimer_: this section has nothing to do with Coq.

It all starts with a try to exit from a number of problems in Mathematics.
Some scientists at the beginning of XX cent. (Brouwer, Kolmogorov, etc.)
came out with idea of so called
**intuitionistic logic** or **intuitionism**. The one generally based on a 
belief that one of the core principle in classic logic (base for that time 
Mathematics), that is the _law of excluded middle_ (`A or ~A is true`, `~` 
stands for negation) is simply unacceptable.

The problem with `A or ~A is true` in short is the 
fact that you (usually) don't actually give a proof for either fact (`A` or
`~A`). And this was thrown away.

Considering another famous law of logic, the 
_law of double negation elimination_: it holds in intuitionism only in a weaker
way: `A follows ~~A` but not vice versa.

### Curry–Hovard correspondence

Let us consider type `A`. We say that

> `A` is **inhabited** if there are the members of this type `A`.

`A` is obviously either inhabited or not. We notice that this notion has some 
connection with the following. Let `A` be proposition. Than `A` is true if there 
is a proof for it.

More generally, the CHC says:

`A` — proposition       |     `A` — type
------------------------|---------------------------------------------------
`A` holds.              | `A` is inhabited.
`A` has a proof.        | There are members (or values) of this type `A`.
`A → B` (A implies B).  | Function types: `A → B`.
`A ∧ B` (conjunction).  | `A × B` (product types: records, `struct`'s, etc.)

And more…


