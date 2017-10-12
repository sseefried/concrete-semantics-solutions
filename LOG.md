# Thu 12 Oct 2017

See `Exercise4p1.thy` for a comment on how unsatisfying it was to use
`rule_tac`.

I think the following is true:

**If a tactic is not smart enough getting Isabelle to behave as you want it
to is fiddly**

The traceability of Isabelle's tactics is always something I have struggled
with. They are black boxes for the most part.

# Tue 10 Oct 2017

## [ERRATA] Exercise 3.12

I'd like to suggest a change to the wording of Exercise 3.12 that makes
it clear that the `r` argument in `comp a r` refers to the top of the stack.
I'd even go so far as to say that register `r` itself shouldn't be touched
since `r = 0` is possible. `comp a r` means that register `r+1` and above
can be freely overwritten.

# Tue 03 Oct 2017

## Exercise 3.9 took me an entire afternoon! Why?

1. It took me a long time to get the definition of distribution correct.
   Originally I was trying to write it inline in `dnf_of_nnf` but I needed
   to pull it out into a separate function `dist`

At one point I was getting the wrong results (as below)

    value "dnf_of_nnf (AND (AND (OR (VAR ''x1'') (VAR ''y1'')) (OR (VAR ''x2'') (VAR ''y2''))) (OR (VAR ''x3'') (VAR ''y3'')))"

is producing (the incorrect value of)

    "OR (OR (AND (OR (AND (VAR ''x1'') (VAR ''x2'')) (AND (VAR ''x1'') (VAR ''y2''))) (VAR ''x3''))
          (AND (OR (AND (VAR ''x1'') (VAR ''x2'')) (AND (VAR ''x1'') (VAR ''y2''))) (VAR ''y3'')))
      (OR (AND (OR (AND (VAR ''y1'') (VAR ''x2'')) (AND (VAR ''y1'') (VAR ''y2''))) (VAR ''x3''))
        (AND (OR (AND (VAR ''y1'') (VAR ''x2'')) (AND (VAR ''y1'') (VAR ''y2''))) (VAR ''y3'')))"
      :: "pbexp"

This example helped me find the correct solution for `dist`.

2. Because I wrote `dist` separately it was necessary to create an intermediate
   lemma to help.

    pbval (dist a b) s = pbval (AND a b) s

The order of the equality in this lemma mattered!
This is going down as a TROUBLESHOOTING rule.

3. I also had another intermediate function called `no_ors` which threw
a spanner in the works. Fortunately, I got a whole lot of left over goals

    1. ⋀va. is_nnf (NOT va) ⟹ no_ors va
    2. ⋀v. is_nnf (NOT v) ⟹ no_ors v
    3. ⋀va v. is_nnf (NOT va) ⟹ is_nnf (NOT v) ⟹ no_ors va
    4. ⋀va v. is_nnf (NOT va) ⟹ is_nnf (NOT v) ⟹ no_ors v
    5. ⋀va vb v. is_nnf (NOT v) ⟹ no_ors va ⟹ no_ors vb ⟹ is_dnf va ⟹ is_dnf vb ⟹ no_ors v
    6. ⋀vb v va. is_nnf (NOT vb) ⟹ no_ors v ⟹ no_ors va ⟹ is_dnf v ⟹ is_dnf va ⟹ no_ors vb

which made it obvious that I needed the following intermediate lemma.

    is_nnf (NOT v) ⟹ no_ors v

This was easy to prove since for `is_nnf` to be true `v` had to be a `VAR`

# Wed 27 Sep 2017


## TROUBLESHOOTING: Using `arbitrary` when applying `induction` rule.

Wow, Exercise 3.6 was hard. I needed to make sure that I was quantifying over an
_arbitrary_ state.

Without "arbitrary: s" I got the following goal:

    ⋀x rhs body. aval (inline rhs) s = lval rhs s ⟹
                 aval (inline body) s = lval body s ⟹
                 aval (inline body) (s(x := lval rhs s)) = lval body (s(x := lval rhs s))

With "arbitrary: s" the goal becomes:

    ⋀x rhs body s. (⋀s. aval (inline rhs) s = lval rhs s) ⟹
                   (⋀s. aval (inline body) s = lval body s) ⟹
                   aval (subst x (inline rhs) (inline body)) s = lval body (s(x := lval rhs s))

The term "aval (subst x (inline rhs) (inline body)) s = lval body (s(x := lval
rhs s))" is first simplified to:

    aval (inline body) (s(x := aval (inline rhs) s)) = lval body (s(x := lval rhs s))

and then to:

    aval (inline body) (s(x := lval rhs s)) = lval body (s(x := lval rhs s))

(by the first assumption above)

The (meta) universal quantification on `s` in the assumptions now helps us. The
second assumption is applied where the quantified `s` is replaced with
`s(x := lval rhs s)` and hence we can discharge this goal.

The book is well written. This issue was already covered in p20-21
when trying to prove some properties about the `itrev` function.
It suggested the heuristic:

> _Generalize goals for induction by replacing constants by variables_

# Tue 26 Sep 2017

## Got things in the assumptions that need simplifying?

**Use your splits!**

In exercise 3.2 it took me forever to find the "split" theorems
`if_splits` and `option_splits` so that I could get the following theorem
to prove.

    fun asimp_constant_total :: "aexp ⇒ int" re
      "asimp_constant_total (N i) = i" |
      "asimp_constant_total (V x) = 0 "|
      "asimp_constant_total (Plus a1 a2) = asimp_constant_total a1 + asimp_constant_total a2"

    fun asimp_remove_constants :: "aexp ⇒ aexp option" where
      "asimp_remove_constants (N i) = None" |
      "asimp_remove_constants (V x) = Some (V x)" |
      "asimp_remove_constants (Plus a1 a2) =
        (case (asimp_remove_constants a1, asimp_remove_constants a2) of
          (Some a1P, Some a2P) ⇒ Some (Plus a1P a2P) |
          (None, Some a2P) ⇒ Some a2P |
          (Some a1P, None) ⇒ Some a1P |
          (None, None) ⇒ None)"

    fun full_asimp :: "aexp ⇒ aexp" where
      "full_asimp a =
         (case (asimp_constant_total a, asimp_remove_constants a) of
            (i, None) ⇒ N i |
            (i, Some a) ⇒ (if i = 0 then a else Plus a (N i)))"

    lemma "aval (full_asimp a) s = aval a s"
      apply (induction a)
        apply (auto split:  aexp.splits option.splits if_splits)
        done

If I left out `if_splits` then I'd get somthing like this:

    1. ⋀a1 a2 x2a.
       asimp_remove_constants a1 = None ⟹
       asimp_constant_total a1 = aval a1 s ⟹
       asimp_remove_constants a2 = Some x2a ⟹
       aval (if asimp_constant_total a2 = 0 then x2a else Plus x2a (N (asimp_constant_total a2))) s = aval a2 s ⟹
       aval a1 s + asimp_constant_total a2 = 0 ⟹ aval x2a s = aval a1 s + aval a2 s

It's clear that there are if-then-else expression in the assumptions. This
is what `if_splits` are for.

If I left out `option.splits` then I'd get something like this:

		 1. ⋀a1 a2. aval (case asimp_remove_constants a1 of None ⇒ N (asimp_constant_total a1)
		                   | Some a ⇒ if asimp_constant_total a1 = 0 then a else Plus a (N (asimp_constant_total a1)))
		              s =
		             aval a1 s ⟹
		             aval (case asimp_remove_constants a2 of None ⇒ N (asimp_constant_total a2)
		                   | Some a ⇒ if asimp_constant_total a2 = 0 then a else Plus a (N (asimp_constant_total a2)))
		              s =
		             aval a2 s ⟹
		             aval (case case asimp_remove_constants a1 of
		                        None ⇒ case asimp_remove_constants a2 of None ⇒ None | Some x ⇒ Some x
		                        | Some a1P ⇒ case asimp_remove_constants a2 of None ⇒ Some a1P | Some a2P ⇒ Some (Plus a1P a2P) of
		                   None ⇒ N (asimp_constant_total a1 + asimp_constant_total a2)
		                   | Some a ⇒
		                       if asimp_constant_total a1 + asimp_constant_total a2 = 0 then a
		                       else Plus a (N (asimp_constant_total a1 + asimp_constant_total a2)))
		              s =
		             aval a1 s + aval a2 s

It's clear there are case-expressions on the `option` type in the assumptions.

This is what `option.splits` are for.
