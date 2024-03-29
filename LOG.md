# Tue 06 Mar 2018

## Colours of variables

The colours of the variables in Isabelle/jEdit matter

blue : free variable
green : bound variable
orange : skolem constant ("free" variables existentially "quantified")
cyan : syntax (not a variable or a constant, like case or if)

## On presenting a counterexample to a theorem.

I has to prove `¬ ( WHILE And b1 b2 DO c ∼ WHILE b1 DO WHILE b2 DO c)`
but I wasn't able to.

This was because b1, b2, and c were free variables which are implicily
quantified with the meta-all operator which means
they cannot be instantiated. The proof relied on being able to instantiate
them with `Bc True`, `Bc False`, and `SKIP` respectively.

Thus I had to rephrase the lemma as:

    lemma "¬ (∀b1 b2 c. WHILE And b1 b2 DO c ∼ WHILE b1 DO WHILE b2 DO c)"

This meant that I was free to instantiate the variables inside the proof
and thus prove it true.

The way I should have read the first formulation was:

"For all `b1`, `b2`, and `c` it is not the case that `WHILE And b1 b2 DO c`
is an equivalent command to `WHILE b1 DO WHILE b2 DO c`"

Read this way it is quite obvious that I could not prove this. For instance
if `b1 = Bc True` and `b2 = Bc True` then it _is_ the case that these two
commands are equivalent.

I always wanted to prove that "It is not the case that for all `b1`, `b2`,
and `c` that  `WHILE And b1 b2 DO c` is an equivalent command to
`WHILE b1 DO WHILE b2 DO c`". This is what the second formulation says.
The first does not!

# Thu 11 Jan 2018

I was having difficulty with what `obtain` was doing

I found a textual substitution from `isar-ref.pdf` (p35) that was _almost_ right.

With some tweaking I found that I could replace

    obtain c1' s1' where a: "y = (c1', s1')" by fastforce

with

    have case1: "⋀thesis. (⋀c1' s1'. y = (c1', s1') ⟹ thesis) ⟹ thesis"
    proof -
      fix thesis
      assume [intro]: "⋀c1' s1'. y = (c1', s1') ⟹ thesis"
      then show thesis by fastforce
    qed
    fix c1' s1'
    presume a: "y = (c1', s1')"

and it did exactly the same thing. This is nice. I've often had
difficult proving the obligations thrown up by `obtain` and that is because
what it is doing is inscrutable to me.

Actually I've come up with something better:

If you can solve the following as a separate lemma (with this skeleton)

    lemma "⋀thesis. (⋀c1' s1'. y = (c1', s1') ⟹ thesis) ⟹ thesis"
    proof -
      fix thesis
      assume [intro]: "⋀c1' s1'. y = (c1', s1') ⟹ thesis"
      then show thesis <<proof>>
    qed

then you can show:

    obtain c1' s1' where a: "y = (c1', s1')" <<proof>>

This will help you in future when you are struggling with an `obtain`.

# Wed 10 Jan 2018
**Pomodoros: 8**


# Sat 06 Jan 2018
**Pomodoros: 4**

Isar

- `from` clause indicates which facts are to be used in the proof
- `have` is used to state intermediate propositions
- `show` is used to state the overall goal
- `fix` is used to introduce ⋀-quantified variables
- `assume` introduces the assumption of an implication
- Propositions are optionally named formuas. They can be referred to in later
  `from` clauses.

Facts
- Fact names can stand for whole lists of facts. If `f` is defined by command
  `fun` then `f.simps` refers to a whole list of recursion equations.
  Individual facts can be selected by writing `f.simps(2)` and sublists with
  e.g. `f.simps(2-4)`

Isar abbreviations
- `then` = `from this`
- `thus` = `then show` = `from this show`
- `hence` = `then have` = `from this have`
- `(have|show) <prop> using <facts>` = `from <facts> (have|show) prop`
- `with <facts>` = `from <facts> <this>`

After `proof` you will sometimes see a hyphen. It is the null method
that does nothing to the goal. If it is left out then some suitable
introduction rule is tried. (It is mysterious to me how it is chosen).

You can refer to the assumptions with `assms(1)`, `assms(2)` etc

# Thu 04 Jan 2018
**Pomodoros: 3**

# Mon 01 Jan 2018
**Pomodoros: 3**

Starting on chapter 7 proofs.

## `print_theorems` is your friend

I'm going to have to start collecting these bits of advice in a separate
"how to use Isabelle" guide.

I had the problem that I was trying to prove rule inversions such as

    (SKIP, s) ⇒ t ⟹ t = s

I didn't want to use the `inductive_cases` magic that the solutions suggested.
I wanted to prove them by hand. In the end I discovered that when
I defined `big_step` with the `inductive` declaration it had brought into
scope `inductive.cases` which was just the theorem I needed. I could then prove
with `apply (erule big_step.cases, auto)`



# Fri 13 Oct 2017

## What can `auto` do?

- rewriting
- linear arithmetic facts (no multiplication)
- simple logic or set-theoretic goals

The key characteristics of both `simp` and `auto`:
- They show you where they got stuck, giving you an idea how to continue.
- They perform the obvious steps but are highly incomplete.

Proof method `fastforce` tries harder than `auto`.
* either succeeds or fails
* only acts of the first subgoal
* can be good on quantifiers where `auto` does not succeed.

Proof method `force` is a slower, more powerful version of `fastforce`.

Proof method `blast` should be used on complex logical goals.
Blast
- is (in principle) complete on first-order formulas.
- does no rewriting!
- covers logic, sets and relations
- either succeeds or fails

`blast` _complements_ `auto`, `fastforce`, `force` etc since it is _weak_
on equality reasoning but good on logic and sets. Has opposite strengths
and weaknesses.

## How does metis prove this?

On p41 the reader is asked to work out how metis proves the following:

    [xs @ ys = ys @ xs; length xs = length ys ] ==> xs = ys

from:

    (xs @ ys = zs) = (xs = take (length xs) zs /\ ys = drop (length xs) zs)

Perhaps like the following?

        xs @ ys = ys @ xs
    ==> xs = take (length xs) (ys @ xs) /\ ys = drop (length xs) (ys @ xs)
    ==> xs = take (length xs) (xs @ ys)

Then we have a new fact

    ?as = take (length ?as (?as @ ?bs))

Using this and using `length xs == length ys` we could deduce

        xs = take (length xs) (ys @ xs)
    ==> xs = take (length ys) (ys @ xs)   -- using length xs == length ys
    ==> xs = ys                           -- using our new fact


# Thu 12 Oct 2017

See `Exercise4p1.thy` for a comment on how unsatisfying it was to use
`rule_tac`.

I think the following is true:

**If a tactic is not smart enough getting Isabelle to behave as you want it
to is fiddly!**

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
