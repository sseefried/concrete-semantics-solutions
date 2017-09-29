theory Chapter3
imports Main
begin

 
type_synonym vname = string
datatype aexp = N int | V vname | Plus aexp aexp
  
type_synonym val = int  
type_synonym state = "vname \<Rightarrow> val"
  
fun aval :: "aexp \<Rightarrow> state \<Rightarrow> val" where
  "aval (N n) s = n" |
  "aval (V x) s = s x" |
  "aval (Plus a1 a2) s = aval a1 s + aval a2 s"
  
value "aval (Plus (N 3) (V ''x'')) (\<lambda>x.0)"
    
fun asimp_const :: "aexp \<Rightarrow> aexp" where
  "asimp_const (N i) = N i" |
  "asimp_const (V x) = V x" |
  "asimp_const (Plus a1 a2) = 
     (case (asimp_const a1, asimp_const a2) of
       (N n1, N n2) \<Rightarrow> N (n1 + n2) |
       (b1, b2)     \<Rightarrow> Plus b1 b2)"

lemma "aval (asimp_const a) s = aval a s"
  by (induction a, auto split: aexp.split)
      
fun plus :: "aexp \<Rightarrow> aexp \<Rightarrow> aexp" where
  "plus (N i1) (N i2) = N (i1 + i2)" | 
  "plus (N i) a = (if i = 0 then a else Plus (N i) a)" |
  "plus a (N i) = (if i = 0 then a else Plus a (N i))" |  
  "plus a1 a2 = Plus a1 a2"

lemma aval_plus: "aval (plus a1 a2) s = aval a1 s + aval a2 s"
  apply (induction a1 a2 rule: plus.induct)
              apply auto
    done

fun asimp :: "aexp \<Rightarrow> aexp" where
  "asimp (N n) = N n" |
  "asimp (V x) = V x" |
  "asimp (Plus a1 a2) = plus (asimp a1) (asimp a2)" 


lemma "aval (asimp a) s = aval a s"
  apply (induction a)
    apply (auto simp: aval_plus)
    done      
      
(* Exercise 3.1

To show that asimp_const really folds all subexpressions of the form Plus (N
i) (N j), define a function optimal :: aexp \<Rightarrow> bool that checks that its
argument does not contain a subexpression of the form Plus (N i) (N j). Then
prove optimal (asimp_const a)

*)
      
fun optimal :: "aexp \<Rightarrow> bool" where
  "optimal (Plus (N _) (N _)) = False" |
  "optimal _ = True"

lemma "optimal (asimp_const a)"
  by (induction a, auto split: aexp.split)

(* Exercise 3.2 *)    
    
fun asimp_constant_total :: "aexp \<Rightarrow> int" where
      "asimp_constant_total (N i) = i" |
      "asimp_constant_total (V x) = 0 "|
      "asimp_constant_total (Plus a1 a2) = asimp_constant_total a1 + asimp_constant_total a2"

fun asimp_remove_constants :: "aexp \<Rightarrow> aexp option" where
      "asimp_remove_constants (N i) = None" |
      "asimp_remove_constants (V x) = Some (V x)" |
      "asimp_remove_constants (Plus a1 a2) =
        (case (asimp_remove_constants a1, asimp_remove_constants a2) of
          (Some a1P, Some a2P) \<Rightarrow> Some (Plus a1P a2P) |
          (None, Some a2P) \<Rightarrow> Some a2P |
          (Some a1P, None) \<Rightarrow> Some a1P |
          (None, None) \<Rightarrow> None)"

fun full_asimp :: "aexp \<Rightarrow> aexp" where
      "full_asimp a =
         (case (asimp_constant_total a, asimp_remove_constants a) of
            (i, None) \<Rightarrow> N i |
            (i, Some a) \<Rightarrow> (if i = 0 then a else Plus a (N i)))"

lemma "aval (full_asimp a) s = aval a s"
      apply (induction a)
        apply (auto split:  aexp.splits option.splits if_splits)
        done
    
(* Exercise 3.3 *)    

fun subst :: "vname \<Rightarrow> aexp \<Rightarrow> aexp \<Rightarrow> aexp" where
  "subst _ _ (N i) = N i" |
  "subst x a (V y) = (if x = y then a else V y)" |
  "subst x a (Plus a1 a2) = Plus (subst x a a1) (subst x a a2)"
          
(* Should evaluate to Plus (N 3) V ''y'' *)
value  "subst ''x'' (N 3) (Plus (V ''x'') (V ''y''))"

lemma aval_subst_eq: "aval (subst x a e) s = aval e (s(x:= aval a s))"  
  by (induction e, auto)

lemma aval_subst_ext: "aval a1 s = aval a2 s \<Longrightarrow> aval (subst x a1 e) s = aval (subst x a2 e) s"
  by (auto simp: aval_subst_eq)

(* Exercise 3.4: see Exercise3p4.thy *)    
    
(* Execise 3.5 

Define a datatype aexp2 of extended arithmetic expressions that has, in
addition to the constructors of aexp, a constructor for modelling a C-like
post-increment operation x++, where x must be a variable. Define an evaluation
function aval2 :: aexp2 \<Rightarrow> state \<Rightarrow> val \<times> state that returns both the value of
the expression and the new state. The latter is required because post-
increment changes the state. 

Extend aexp2 and aval2 with a division operation.
Model partiality of division by changing the return type of aval2 to (val \<times>
state) option. In case of division by 0 let aval2 return None. Division on int
is the infix div

*)
    
datatype aexp2 = N2 int | V2 vname | Plus2 aexp2 aexp2 | PostInc2 vname | Div2 aexp2 aexp2

(* sseefried: It's not mentioned in the exercise but we have to choose an order in
   which to evaluate sub expressions for Plus and Div. We choose left-to-right
   So that, for instance in the expression Plus a1 a2, a1 is first evaluated and the
   state that arises from that is passed in when evaluating a2
 *)
  
fun aval2 :: "aexp2 \<Rightarrow> state \<Rightarrow> (val \<times> state) option" where
  "aval2 (N2 n) s = Some (n, s)" |
  "aval2 (V2 x) s = Some (s x, s)" |
  "aval2 (Plus2 a1 a2) s = 
    (case aval2 a1 s of
       None \<Rightarrow> None |
       Some (n1, s1) \<Rightarrow> 
         (case aval2 a2 s1 of
           None \<Rightarrow> None |
           Some (n2, s2) \<Rightarrow> Some (n1 + n2, s2)
         )
    )" |
  "aval2 (PostInc2 x) s = Some (s x, s (x:= s x + 1))" |
  "aval2 (Div2 a1 a2) s = 
    (case aval2 a1 s of
      None \<Rightarrow> None |
      Some (n1, s1) \<Rightarrow> 
        (case aval2 a2 s1 of
          None \<Rightarrow> None |
          Some (n2, s2) \<Rightarrow> (if n2 = 0 then None else Some (n1 div n2, s2))
        )
    )"

(* Exercise 3.6 
The following type adds a LET construct to arithmetic ex- pressions:

datatype lexp = Nl int | Vl vname | Plusl lexp lexp | LET vname lexp lexp

The LET constructor introduces a local variable: the value of LET x e1 e2 is
the value of e2 in the state where x is bound to the value of e1 in the
original state. Define a function lval :: lexp \<Rightarrow> state \<Rightarrow> int that evaluates
lexp expressions. Remember s(x := i).

Define a conversion inline :: lexp \<Rightarrow>
aexp. The expression LET x e1 e2 is inlined by substituting the converted form
of e1 for x in the converted form of e2. See Exercise 3.3 for more on
substitution. Prove that inline is correct w.r.t. evaluation.

*)                       
  
datatype lexp = Nl int | Vl vname | Plusl lexp lexp | LET vname lexp lexp
  
fun lval :: "lexp \<Rightarrow> state \<Rightarrow> int"  where
  "lval (Nl i) s = i" |
  "lval (Vl x) s = s x" |
  "lval (Plusl l1 l2) s = lval l1 s + lval l2 s" |
  "lval (LET x rhs body) s = lval body (s (x := lval rhs s))" 
 
  
fun inline :: "lexp \<Rightarrow> aexp" where
  "inline (Nl i) = N i" |
  "inline (Vl x) = V x" |
  "inline (Plusl l1 l2) = Plus (inline l1) (inline l2)" |
  "inline (LET x rhs body) = subst x (inline rhs) (inline body)"


value "lval (LET ''x'' (Plusl (Nl 1) (Nl 2)) (Plusl (Vl ''x'') (Nl 3))) (\<lambda>x.0)"
value "inline (LET ''x'' (Plusl (Nl 1) (Nl 2)) (Plusl (Vl ''x'') (Nl 3)))"

    
(* Wow, this one was hard. I needed to make sure that I was quantifying over an _arbitrary_
   state.
   
   Without "arbitrary: s" I got the following goal:

   \<And>x rhs body. aval (inline rhs) s = lval rhs s \<Longrightarrow> 
                 aval (inline body) s = lval body s \<Longrightarrow> 
                 aval (inline body) (s(x := lval rhs s)) = lval body (s(x := lval rhs s))

   With "arbitrary: s" the goal becomes:

   \<And>x rhs body s. (\<And>s. aval (inline rhs) s = lval rhs s) \<Longrightarrow> 
                   (\<And>s. aval (inline body) s = lval body s) \<Longrightarrow> 
                   aval (subst x (inline rhs) (inline body)) s = lval body (s(x := lval rhs s))

  The term "aval (subst x (inline rhs) (inline body)) s = lval body (s(x := lval rhs s))" is
  first simplified to:

  aval (inline body) (s(x := aval (inline rhs) s)) = lval body (s(x := lval rhs s))

  and then to:

  aval (inline body) (s(x := lval rhs s)) = lval body (s(x := lval rhs s))
  (by the first assumption above)

  The universal quantification on "s" in the assumptions now helps us. The second assumption
  is applied where the quantified "s" is replaced with "s(x := lval rhs s)" and hence we
  can discharge this goal.
  
  The book is well written. This issue was already covered in p20-21.

*)
    
lemma "aval (inline l) s = lval l s"
  apply (induction l arbitrary: s rule: inline.induct)
     apply (auto simp: aval_subst_eq)
    done

datatype bexp = Bc bool | Not bexp | And bexp bexp | Less aexp aexp
  
fun bval :: "bexp \<Rightarrow> state \<Rightarrow> bool" where  
  "bval (Bc v) s       = v" |
  "bval (Not b) s      = (\<not> bval b s)" |
  "bval (And b1 b2) s  = (bval b1 s \<and> bval b2 s)" |
  "bval (Less a1 a2) s = (aval a1 s < aval a2 s)"

fun not :: "bexp \<Rightarrow> bexp" where  
  "not (Bc True) = Bc False" |
  "not (Bc False) = Bc True" |
  "not b = Not b"
  
fun "and" :: "bexp \<Rightarrow> bexp \<Rightarrow> bexp" where
  "and (Bc True) b = b" |
  "and b (Bc True) = b" |
  "and (Bc False) b = Bc False" |
  "and b (Bc False) = Bc False" |
  "and b1 b2 = And b1 b2"

fun less :: "aexp \<Rightarrow> aexp \<Rightarrow> bexp" where
  "less (N n1) (N n2) = Bc (n1 < n2)" |
  "less a1 a2 = Less a1 a2"

fun bsimp :: "bexp \<Rightarrow> bexp" where
  "bsimp (Bc v) = Bc v" |
  "bsimp (Not b) = not (bsimp b)" |
  "bsimp (And b1 b2) = and (bsimp b1) (bsimp b2)" |
  "bsimp (Less a1 a2) = less (asimp a1) (asimp a2)"

(* Exercise 3.7

Define functions Eq, Le :: aexp \<Rightarrow> aexp \<Rightarrow> bexp and 
prove bval(Eqa1 a2) s = (aval a1 s = aval a2 s) and
bval (Le a1 a2) s = (aval a1 s \<le> aval a2 s)

*)  

(* I've decided to make these constant-folding, but for this I will
   require some helper theorems
*)  
lemma [simp]: "bval (not b) s = bval (Not b) s"
  by (induction b, auto)

lemma [simp]: "bval (and b1 b2) s = bval (And b1 b2) s" 
  by (induction b1 b2 rule: and.induct, auto)

lemma [simp]: "bval (less a1 a2) s = bval (Less a1 a2) s"
  by (induction a1 a2 rule: less.induct, auto)
        
fun Eq :: "aexp \<Rightarrow> aexp \<Rightarrow> bexp" where
  "Eq a1 a2 = and (not (less a1 a2)) (not (less a2 a1))"
    
lemma "bval (Eq a1 a2) s = (aval a1 s = aval a2 s)"
  by auto

fun Le :: "aexp \<Rightarrow> aexp \<Rightarrow> bexp" where
  "Le a1 a2 = not (less a2 a1)"
 
lemma "bval (Le a1 a2) s = (aval a1 s \<le> aval a2 s)"
  by auto
    
(* Exercise 3.8

Consider an alternative type of boolean expressions featuring a conditional:
datatype ifexp = Bc2 bool | If ifexp ifexp ifexp | Less2 aexp aexp
First define an evaluation function ifval :: ifexp \<Rightarrow> state \<Rightarrow> bool analogously to bval. 
Then define two functions b2ifexp :: bexp \<Rightarrow> ifexp and if2bexp :: ifexp \<Rightarrow> bexp and 
prove their correctness, i.e., that they preserve the value of an expression.

*)

datatype ifexp = Bc2 bool | If ifexp ifexp ifexp | Less2 aexp aexp
  
fun ifval :: "ifexp \<Rightarrow> state \<Rightarrow> bool" where  
  "ifval (Bc2 b) s = b" |
  "ifval (If cond thn els) s = (if (ifval cond s) then (ifval thn s) else (ifval els s))" |
  "ifval (Less2 a1 a2) s = (aval a1 s < aval a2 s)"

fun or :: "bexp \<Rightarrow> bexp \<Rightarrow> bexp" where
  "or b1 b2 = Not (And (Not b1) (Not b2))"  (* de Morgan's Law *)

fun b2ifexp :: "bexp \<Rightarrow> ifexp" where
  "b2ifexp (Bc b) = Bc2 b" |
  "b2ifexp (Not b) = If (b2ifexp b) (Bc2 False) (Bc2 True)" |
  "b2ifexp (And b1 b2) = If (b2ifexp b1) (b2ifexp b2) (Bc2 False)" |
  "b2ifexp (Less a1 a2) = Less2 a1 a2"
  

fun if2bexp :: "ifexp \<Rightarrow> bexp" where  
  "if2bexp (Bc2 b) = Bc b" |
  "if2bexp (If cond thn els) = 
     or (And (if2bexp cond) (if2bexp thn)) (And (Not (if2bexp cond)) (if2bexp els))" |
  "if2bexp (Less2 a1 a2) = Less a1 a2"
  
value "bval (if2bexp (If (Less2 (N 2) (N 2)) (Bc2 True) (Bc2 False))) (\<lambda>x.0)"  

lemma "ifval (b2ifexp b) s = bval b s"
  by (induction b arbitrary: s, auto)

lemma "bval (if2bexp b) s = ifval b s"
  by (induction b arbitrary: s, auto)
  
  
end