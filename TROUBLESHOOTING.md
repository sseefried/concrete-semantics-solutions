# On `induction` rule

Sometimes the induction hypothesis needs to be univerally quantified on a
particular variable. When this happens use `arbitrary`.

    apply (induction x arbitrary: y)

(where `x` and `y` are variables in your lemma)

See p20 - p21 of book for more details. Also see the
*Wed 27 Sep 2017* entry in [LOG.md](LOG.md)