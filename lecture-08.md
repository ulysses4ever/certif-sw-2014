## Doing type check

We're trying to define `typeCheck` function for simple expression
language, which has `True` and `False`, and all natural constants as
well, and allows building complex terms using `Plus` and `And`
connectivities.

We gave structured proof for `typeCheck` starting with huge `refine`
and ended up with eight subgoals. Not all of them are unique in their
nature.

1.  We have two base cases: `Nat` and `Bool`. We can prove them with
    `constructor` (or `auto` as we added our main constructor `hasType`
    to `auto`-database).

2.  Two “normal” cases: `Plus` and `And` with valid types for
    subexpressions. We can cope with them using `constructor` and
    `rewrite`'ings.

3.  Lots of “irregular” cases. They all look like this:

    > ... [lots of hypotheses] // ~ hasType …

    And we have to do lots of `inversion`'s here.

This looks like a reason for that we have lost last time: we didn't try
to factorize this cases like this.

Second possible source of our problems is letting Coq to control names
of hypotheses.

After doing explicit naming for main hypotheses and applying some
automation (`eauto`, `eapply`) we came up with neat proof analyzing
three above mentioned cases in two lines. This is after our structured,
but huge `refine` still.

Impressive enough, `Print`'ing resulting `typeCheck` function gives
about eight hundred lines of code.

## Evaluating

After we succeed with type checking of our expression language, we want
to be able to evaluate expressions from this language.

Result of the evaluation will be represented with type

    option(nat + bool)

Consider examples of the values of this type:

* `Some (inr true)`,
* `None`,
* `Some (inl 7)`.

First version of evaluation function `evalu` that comes to our mind is
evaluation of completely untyped `exp` term. We have to do two things
simultaneously on this way (and this is unfortunate): evaluate and type
check.

Due to the problem we introduce a type for typed expression `texp t`
(where `t` is a type parameter)
in addition to our initial `exp` untyped expression, as well as function
to convert `ext` to `texp t`, where `t` is an actual type of `exp`
(either `TNat` or `TBool`). We name this function as `exp2texp`.

After this we face with a problem of define return type of evaluation of
typed expression. We can cope with it with dependent type: the return
type actually depends on argument. We introduce simple function `typeDenote`
which analyse `texp t` value and based on a constructor used to create
this particular `texp t` value (`NNat` or `NBool`).

We get **tagless** evaluator `evalt` for typed expression: no need to analyse
`Some` and `inl` / `inr` (“tags”).

Our final task is to define evaluator for untyped expression through
small pieces defined above.

## Home task

* Ch. More Logic (SW Foundations)
