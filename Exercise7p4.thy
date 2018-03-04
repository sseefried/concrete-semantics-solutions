theory Exercise7p4
imports 
  Bigstep_sseefried
  Star
begin

(* sseefried: For some reason this does not evaluate number literals i.e. of form N n *)
inductive astep :: "aexp \<times> state \<Rightarrow> aexp \<Rightarrow> bool" (infix "\<leadsto>" 50) where 
    "(V x, s) \<leadsto> N (s x)" 
  | "(Plus (N i) (N j),s) \<leadsto> N (i + j)"
  | "(a1, s) \<leadsto> N i  \<Longrightarrow> (Plus a1 a2, s) \<leadsto> Plus (N i) a2"
  | "(a2, s) \<leadsto> N j  \<Longrightarrow> (Plus (N i) a2, s) \<leadsto> N (i + j)"
  

  
(* The following command tells it to generate code for the predicate  and thus make the 
   predicate available in the "values" command, which is similar to value, but works on 
   inductive definitions and computes a set of possible results. 
 *)
code_pred astep .  

values "{ s. (Plus (V ''x'') (V ''y'') , ((\<lambda>_. 0) (''x'' := 2)) (''y'' := 3)) \<leadsto> s }"

lemmas astep_induct = astep.induct[split_format (complete)]

lemma "(a,s) \<leadsto> a' \<Longrightarrow> aval a s = aval a' s"
proof (induction rule: astep_induct)
  fix x s
  show " aval (V x) s = aval (N (s x)) s" by auto
next
  fix i j s
  show "aval (Plus (N i) (N j)) s = aval (N (i + j)) s" by auto
next
  fix i a1 a2 s
  assume "(a1, s) \<leadsto> N i"
     and "aval a1 s = aval (N i) s"
  thus "aval (Plus a1 a2) s = aval (Plus (N i) a2) s" by auto
next
  fix a2 s j i
  assume "(a2, s) \<leadsto> N j"
     and "aval a2 s = aval (N j) s"
  thus   "aval (Plus (N i) a2) s = aval (N (i + j)) s" by auto
qed


(* Bonus. Create a relation like "star" for this *)  

inductive
  star' :: "('a \<times> state \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a \<times> state \<Rightarrow> 'a \<Rightarrow> bool"
for r where
refl':  "star' r (x, s) x" |
step':  "r (x, s) y \<Longrightarrow> star' r (y, s) z \<Longrightarrow> star' r (x, s) z"

code_pred star' .

abbreviation
  asteps :: "aexp \<times> state \<Rightarrow> aexp \<Rightarrow> bool" (infix "\<leadsto>*" 55)
where "as \<leadsto>* a' \<equiv> star' astep as a'"

values "{ s. (Plus (V ''x'') (V ''y'') , <''x'' := 2, ''y'' := 3>) \<leadsto>* s }"



end