theory BigStep_sseefried
imports Com
begin

(* concrete syntax (_,_) \<Rightarrow> _ is possible becasue we declared the transition arrow \<Rightarrow> as an
   infix symbol below with precendence 55 *)

inductive
  big_step :: "com \<times> state \<Rightarrow> state \<Rightarrow> bool" (infix "\<Rightarrow>" 55)
where

Skip:       "(SKIP,s) \<Rightarrow> s" |
Assign:     "(x ::= a,s) \<Rightarrow> s(x := aval a s)" |
Seq:        "\<lbrakk> (c\<^sub>1,s\<^sub>1) \<Rightarrow> s\<^sub>2; (c\<^sub>2,s\<^sub>2) \<Rightarrow> s\<^sub>3 \<rbrakk> \<Longrightarrow> (c\<^sub>1;;c\<^sub>2, s\<^sub>1) \<Rightarrow> s\<^sub>3" |
IfTrue:     "\<lbrakk> bval b s;   (c\<^sub>1,s) \<Rightarrow> t \<rbrakk> \<Longrightarrow> (IF b THEN c\<^sub>1 ELSE c\<^sub>2, s) \<Rightarrow> t" |
IfFalse:    "\<lbrakk> \<not>bval b s;  (c\<^sub>2,s) \<Rightarrow> t \<rbrakk> \<Longrightarrow> (IF b THEN c\<^sub>1 ELSE c\<^sub>2, s) \<Rightarrow> t" |
WhileFalse: "\<not>bval b s \<Longrightarrow> (WHILE b DO c,s) \<Rightarrow> s" |
WhileTrue:  "\<lbrakk> bval b s\<^sub>1;  (c,s\<^sub>1) \<Rightarrow> s\<^sub>2;  (WHILE b DO c, s\<^sub>2) \<Rightarrow> s\<^sub>3 \<rbrakk>
              \<Longrightarrow> (WHILE b DO c, s\<^sub>1) \<Rightarrow> s\<^sub>3"

(* `print_theorems` is incredibly useful for seeing what certain
   declarations bring into scope *)
print_theorems              

declare big_step.intros [intro]

(* From the textbook:
"This induction schema is almost perfect for our purposes, but
our trick for reusing the tuple syntax means that the induction
schema has two parameters instead of the @{text c}, @{text s},
and @{text s'} that we are likely to encounter. Splitting
the tuple parameter fixes this:"
*)
lemmas big_step_induct = big_step.induct[split_format(complete)]
thm big_step_induct

schematic_goal ex: "(''x'' ::= N 5;; ''y'' ::= V ''x'', s) \<Rightarrow> ?t" 
  apply(rule Seq)
   apply(rule Assign)
  apply simp
  apply(rule Assign)
done             

(* The following command tells Isabelle to generate code for the predicate \<Rightarrow> and thus make the 
predicate available in the `values` command, which is similar to `value`, but works on 
inductive definitions and computes a set of possible results.  *)

code_pred big_step . (* The period is necessary at the end of this line *)

values "{t. (SKIP, \<lambda>_. 0) \<Rightarrow> t}"

values "{map t [''x'', ''y'']| t. (''x'' ::= N 2;; ''y'' ::= plus (V ''x'') (N 1), \<lambda>_.0) \<Rightarrow> t}"

(* 7.2.3 Rule Inversion *)

(* Inductive definitions like above bring into scope automatically generated .induct and .cases theorems *)


(* Now we prove a bunch of rule inversions. I've decided not to use inductive_cases as in
   the official solutions and instead prove the rule inversions as they were expressed in
   the textbook.
   
   I must mention my indebtedness to this particular Isabelle mailing list post:
   https://lists.cam.ac.uk/pipermail/cl-isabelle-users/2013-January/msg00118.html

*)


lemma SkipE[elim!]: "(SKIP, s) \<Rightarrow> t \<Longrightarrow> t = s"
  by (erule big_step.cases, simp+)

lemma AssignE[elim!]:  "(x ::= a,s) \<Rightarrow> t \<Longrightarrow> t = s(x := aval a s)"
  by (erule big_step.cases, simp+)
  
lemma SeqE[elim!]: "(c1;;c2, s1) \<Rightarrow> s3 \<Longrightarrow> \<exists>s2. (c1,s1) \<Rightarrow> s2 \<and> (c2,s2) \<Rightarrow> s3"
  by (erule big_step.cases, auto)

lemma IfE[elim!]: "(IF b THEN c1 ELSE c2,s) \<Rightarrow> t \<Longrightarrow> bval b s \<and> (c1, s) \<Rightarrow> t \<or> \<not>bval b s \<and> (c2, s) \<Rightarrow> t"
  by (erule big_step.cases, simp+)
              
lemma WhileE[elim]: 
  "(WHILE b DO c, s) \<Rightarrow> t 
  \<Longrightarrow>   bval b s \<and> (\<exists>s'. (c, s) \<Rightarrow> s' \<and> (WHILE b DO c, s') \<Rightarrow> t) 
      \<or> \<not>bval b s \<and> t = s"
   by  (erule big_step.cases, auto)


   
inductive_cases SkipE2[elim!]: "(SKIP, s) \<Rightarrow> t"
inductive_cases AssignE2[elim!]: "(x ::= a,s) \<Rightarrow> t"
inductive_cases SeqE2[elim!]: "(c1;;c2,s1) \<Rightarrow> s3"
inductive_cases IfE2[elim!]: "(IF b THEN c1 ELSE c2,s) \<Rightarrow> t"
inductive_cases WhileE2[elim]: "(WHILE b DO c,s) \<Rightarrow> t"

(* Lemma 7.2 *)
lemma seq_assoc_l: "(c1;; c2;; c3, s) \<Rightarrow> s' \<Longrightarrow> (c1;; (c2;; c3), s) \<Rightarrow> s'"
  apply clarify
  apply (rule Seq, simp)
  apply (rule Seq, simp+)
  done

lemma seq_assoc_r: "(c1;; (c2;; c3), s) \<Rightarrow> s' \<Longrightarrow> (c1;; c2;; c3, s) \<Rightarrow> s'"
  apply clarify
  apply (rule Seq, rule Seq, simp+)
  done

lemma seq_assoc: "(c1;; c2;; c3, s) \<Rightarrow> s' \<longleftrightarrow> (c1;; (c2;; c3), s) \<Rightarrow> s'"
  by (auto simp: seq_assoc_l seq_assoc_r)

(* Section 7.2.4 *)
  
abbreviation
  equiv_c :: "com \<Rightarrow> com \<Rightarrow> bool" (infix "\<sim>" 50) where
  "c \<sim> c' \<equiv> (\<forall>s t. (c, s) \<Rightarrow> t = (c', s) \<Rightarrow> t)"
  
lemma "WHILE b DO c \<sim> IF b THEN (c;; WHILE b DO c) ELSE SKIP"
  by blast

lemma "IF b THEN c ELSE c \<sim> c"
  by blast
 
(* Lemma 7.6 *)  
(* Uses advanced rule induction from section 5.4.6 *)

lemma
  assumes "(WHILE b DO c, s) \<Rightarrow> t"
  assumes "c \<sim> c'"
  shows "(WHILE b DO c', s) \<Rightarrow> t"
using assms
  apply (induct "(WHILE b DO c, s)" "t" arbitrary: s)
   apply blast
  apply blast
  done

  (* or you can do *)  
lemma  while_equiv_aux: "(WHILE b DO c, s) \<Rightarrow> t \<Longrightarrow> c \<sim> c' \<Longrightarrow> (WHILE b DO c', s) \<Rightarrow> t"
  apply(induction "(WHILE b DO c)" s t arbitrary: b c rule: big_step_induct)
   apply blast
  apply blast
  done

(* 
  I found the unification that was going on with the advance rule induction to be a bit 
  mysterious. The following theorem is very close to what we get after:

  apply (induction "(WHILE b DO c, s)" t arbitrary: b c s rule: big_step.induct)
*)


thm big_step.induct[of "(WHILE b DO c, s)" "t" "\<lambda>(c,s1) s2. \<forall>b ca. c = WHILE b DO ca \<longrightarrow> ca \<sim> c' \<longrightarrow> (WHILE b DO c', s1) \<Rightarrow> s2"]

(* Peter Gammie showed me how to get exactly what you get after the induction step in the proofs
   above. Not the use of the `for` construct and the `rule_format` attribute (also known as a 
   "directive")
*)

lemmas unified_big_step = big_step.induct[of "(WHILE b DO c, s)" "t" 
  "\<lambda>(c,s1) s2. \<forall>b ca. c = WHILE b DO ca \<longrightarrow> ca \<sim> c' \<longrightarrow> (WHILE b DO c', s1) \<Rightarrow> s2", simplified, 
    rule_format] for b c c' s t

(* We can now prove the lemma again with this new theorem *)
lemma  "(WHILE b DO c, s) \<Rightarrow> t \<Longrightarrow> c \<sim> c' \<Longrightarrow> (WHILE b DO c', s) \<Rightarrow> t"
  apply (erule unified_big_step)
  apply auto
  done

(* We now use Lemma 7.6 to prove the following *)
lemma while_equiv: "c \<sim> c' \<Longrightarrow> WHILE b DO c \<sim> WHILE b DO c'"
  by (auto simp: while_equiv_aux)

(* Lemma 7.8 *)  

lemma sim_refl: "c \<sim> c" by auto
lemma sim_sym: "c \<sim> c' \<Longrightarrow> c' \<sim> c" by auto
lemma sim_trans: "\<lbrakk> c \<sim> c'; c' \<sim> c'' \<rbrakk> \<Longrightarrow> c \<sim> c''" by auto

(* Lemma 7.9 IMP is deterministic*)
lemma imp_deterministic: "\<lbrakk> (c,s) \<Rightarrow> t; (c,s) \<Rightarrow> t' \<rbrakk> \<Longrightarrow> t' = t"
  apply (induction t arbitrary: t' rule: big_step_induct)
  apply blast+
  done
  
(* Here is the "blackboard presentation" *)  
theorem
  "\<lbrakk>(c,s) \<Rightarrow>t;  (c,s) \<Rightarrow> t' \<rbrakk> \<Longrightarrow> t' = t"
proof (induction arbitrary: t' rule: big_step.induct)
  -- "the only interesting case, WhileTrue:"
fix b c s s1 t t'
  -- "The assumptions of the rule:"
assume "bval b s" and "(c,s) \<Rightarrow> s1" and "(WHILE b DO c, s1) \<Rightarrow> t"
-- "Ind.Hyp; note the \<And> because of arbitrary:"
assume IHc: "\<And>t'. (c,s) \<Rightarrow> t' \<Longrightarrow> t' = s1"
assume IHw: "\<And>t'. (WHILE b DO c, s1) \<Rightarrow> t' \<Longrightarrow> t' = t" 
-- "Premise of implication:"
assume "(WHILE b DO c, s) \<Rightarrow> t'"
with `bval b s` obtain s1' where
  c: "(c,s) \<Rightarrow> s1'" and
  w: "(WHILE b DO c, s1') \<Rightarrow> t'" by auto
from c IHc have "s1' = s1" by blast
with w IHw show "t' =t" by blast
qed blast+ 
-- "prove the rest automatically"
  
end