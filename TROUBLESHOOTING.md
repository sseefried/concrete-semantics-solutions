# On `induction` rule

## RULE: Think about universally quantifying certain variables in induction hypothesis

Sometimes the induction hypothesis needs to be universally quantified on a
particular variable. When this happens use `arbitrary`.

    apply (induction x arbitrary: y)

(where `x` and `y` are variables in your lemma)

See p20 - p21 of book for more details. Also see the
*Wed 27 Sep 2017* entry in [LOG.md](LOG.md)

# On simplification rules

## RULE: In equality lemmas order can matter

In lemmas of the form "a = b" the _order can matter_. Try reversing the
order and see if that help your proofs.

# Intermediate lemmas

## RULE: If proving something about a function that relies on helper functions, prove intermediate lemmas on the helper functions

Example. In Exercise 3.9 I needed to prove

    pbval (dnf_of_nnf b) s = pbval b s

`dnf_of_nnf` used a helper function `dist` so it was necessary to prove:

    pbval (dist a b) s = pbval (AND a b) s

Looking at the goals carefully let me realise this.

## RULE: Use your splits

In exercise 3.2 it took me forever to find the "split" theorems
`if_splits` and `option_splits` so that I could get the following theorem
to prove.
