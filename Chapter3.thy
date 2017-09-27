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

lemma substitution: "aval (subst x a e) s = aval e (s(x:= aval a s))"  
  by (induction e, auto)

lemma "aval a1 s = aval a2 s \<Longrightarrow> aval (subst x a1 e) s = aval (subst x a2 e) s"
  by (auto simp: substitution)
  
  
end