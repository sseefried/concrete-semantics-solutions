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
  "asimp_const (N n) = N n" |
  "asimp_const (V x) = V x" | 
  "asimp_const (Plus a1 a2) = 
    (case (asimp_const a1, asimp_const a2) of
      (N n1, N n2) \<Rightarrow> N (n1 + n2) |
      (b1, b2) \<Rightarrow> Plus b1 b2)"

lemma "aval (asimp_const a) s = aval a s"
  apply (induction a)
    apply (auto split: aexp.split)
  done
    
 
  
end