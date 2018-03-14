theory Big_Step_7p10
imports Com_7p10
begin

(* concrete syntax (_,_) \<Rightarrow> _ is possible becasue we declared the transition arrow \<Rightarrow> as an
   infix symbol below with precendence 55 *)

inductive
  big_step :: "com \<times> state \<Rightarrow> com \<times> state \<Rightarrow> bool" (infix "\<Rightarrow>" 55)
where

Skip:       "(SKIP,s) \<Rightarrow> (SKIP, s)" |
Throw:      "(THROW, s) \<Rightarrow> (THROW, s)" |
Assign:     "(x ::= a,s) \<Rightarrow> (SKIP, s(x := aval a s))" |
Seq1:       "\<lbrakk> (c\<^sub>1,s\<^sub>1) \<Rightarrow> (SKIP, s\<^sub>2); (c\<^sub>2,s\<^sub>2) \<Rightarrow> (x, s\<^sub>3) \<rbrakk> \<Longrightarrow> (c\<^sub>1;;c\<^sub>2, s\<^sub>1) \<Rightarrow> (x, s\<^sub>3)" |
Seq2:       "\<lbrakk> (c\<^sub>1,s\<^sub>1) \<Rightarrow> (THROW, s\<^sub>2) \<rbrakk> \<Longrightarrow> (c\<^sub>1;;c\<^sub>2, s\<^sub>1) \<Rightarrow> (THROW, s\<^sub>2)" |
IfTrue:     "\<lbrakk> bval b s;   (c\<^sub>1,s) \<Rightarrow> (x,t) \<rbrakk> \<Longrightarrow> (IF b THEN c\<^sub>1 ELSE c\<^sub>2, s) \<Rightarrow> (x,t)"  |
IfFalse:    "\<lbrakk> \<not>bval b s;  (c\<^sub>2,s) \<Rightarrow> (x,t) \<rbrakk> \<Longrightarrow> (IF b THEN c\<^sub>1 ELSE c\<^sub>2, s) \<Rightarrow> (x,t)" |
WhileFalse: "\<not>bval b s \<Longrightarrow> (WHILE b DO c,s) \<Rightarrow> (SKIP, s)" |
WhileTrue1:  "\<lbrakk> bval b s\<^sub>1;  (c,s\<^sub>1) \<Rightarrow> (SKIP, s\<^sub>2);  (WHILE b DO c, s\<^sub>2) \<Rightarrow> (x,s\<^sub>3) \<rbrakk>
              \<Longrightarrow> (WHILE b DO c, s\<^sub>1) \<Rightarrow> (x,s\<^sub>3)"  |
WhileTrue2:  "\<lbrakk> bval b s\<^sub>1;  (c,s\<^sub>1) \<Rightarrow> (THROW, s\<^sub>2) \<rbrakk> \<Longrightarrow> (WHILE b DO c, s\<^sub>1) \<Rightarrow> (THROW, s\<^sub>2)" |
Try1:        "\<lbrakk> c\<^sub>1 \<noteq> THROW; (c\<^sub>1,s) \<Rightarrow> (x,t) \<rbrakk> \<Longrightarrow> (TRY c\<^sub>1 CATCH c\<^sub>2, s) \<Rightarrow> (x,t)" |
Try2:        "(c\<^sub>2, s) \<Rightarrow> (x,t)                \<Longrightarrow> (TRY THROW CATCH c\<^sub>2, s) \<Rightarrow> (x,t)"

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


schematic_goal ex: "(''x'' ::= N 5;; ''y'' ::= V ''x'', s) \<Rightarrow> (SKIP, ?t)" 
  apply(rule Seq1)
   apply(rule Assign)
    apply simp
   apply(rule Assign)
done

(* The following command tells Isabelle to generate code for the predicate \<Rightarrow> and thus make the 
predicate available in the `values` command, which is similar to `value`, but works on 
inductive definitions and computes a set of possible results.  *)

code_pred big_step . (* The period is necessary at the end of this line *)

values "{t. (SKIP, \<lambda>_. 0) \<Rightarrow> t}"

values "{map t [''x'', ''y'']| t. (''x'' ::= N 2;; ''y'' ::= plus (V ''x'') (N 1), \<lambda>_.0) \<Rightarrow> (SKIP, t)}"

(* 7.2.3 Rule Inversion *)

(* Inductive definitions like above bring into scope automatically generated .induct and .cases theorems *)


(* Now we prove a bunch of rule inversions. I've decided not to use inductive_cases as in
   the official solutions and instead prove the rule inversions as they were expressed in
   the textbook.
   
   I must mention my indebtedness to this particular Isabelle mailing list post:
   https://lists.cam.ac.uk/pipermail/cl-isabelle-users/2013-January/msg00118.html

*)


lemma SkipE[elim!]: "(SKIP, s) \<Rightarrow> (SKIP, t) \<Longrightarrow> t = s"
  by (erule big_step.cases, simp+)

lemma ThrowE[elim!]: "(THROW, s) \<Rightarrow> (THROW, t) \<Longrightarrow> t = s"
  by (erule big_step.cases, simp+)
    
lemma AssignE[elim!]:  "(x ::= a,s) \<Rightarrow> (SKIP, t) \<Longrightarrow> t = s(x := aval a s)"
  by (erule big_step.cases, simp+)
  
lemma SeqE[elim!]: "(c1;;c2, s1) \<Rightarrow> (x,s\<^sub>3) \<Longrightarrow> (\<exists>s2. (c1,s1) \<Rightarrow> (SKIP, s2) \<and> (c2,s2) \<Rightarrow> (x, s\<^sub>3))
                                            \<or> (c1,s1) \<Rightarrow> (THROW, s\<^sub>3)"
  by (erule big_step.cases, auto)

lemma IfE[elim!]: "(IF b THEN c1 ELSE c2,s) \<Rightarrow> (x,t) \<Longrightarrow> bval b s \<and> (c1, s) \<Rightarrow> (x,t) \<or> \<not>bval b s \<and> (c2, s) \<Rightarrow> (x, t)"
  by (erule big_step.cases, simp+)
              
lemma WhileE[elim]: 
  "(WHILE b DO c, s) \<Rightarrow> (x,t) 
  \<Longrightarrow>   bval b s \<and> (\<exists>s'. (c, s) \<Rightarrow> (SKIP, s') \<and> (WHILE b DO c, s') \<Rightarrow> (x, t)) 
      \<or> bval b s \<and> (c,s) \<Rightarrow> (THROW, t)
      \<or> \<not>bval b s \<and> t = s"
  by (erule big_step.cases, auto)
    
lemma TryE[elim!]: "(TRY c\<^sub>1 CATCH c\<^sub>2, s) \<Rightarrow> (x,t) \<Longrightarrow> c\<^sub>1 \<noteq> THROW \<and> (c\<^sub>1, s) \<Rightarrow> (x,t)
                                         \<or> c\<^sub>1 = THROW \<and> (c\<^sub>2, s) \<Rightarrow> (x,t)"
  by (erule big_step.cases, auto)
  
inductive_cases SkipE2[elim!]: "(SKIP, s) \<Rightarrow> xt"
inductive_cases ThrowE2[elim!]: "(THROW, s) \<Rightarrow> xt"
inductive_cases AssignE2[elim!]: "(x ::= a,s) \<Rightarrow> xt"
inductive_cases SeqE2[elim!]: "(c1;;c2,s1) \<Rightarrow> xs3"
inductive_cases IfE2[elim!]: "(IF b THEN c1 ELSE c2,s) \<Rightarrow> xt"
inductive_cases WhileE2[elim]: "(WHILE b DO c,s) \<Rightarrow> xt"
inductive_cases TryE2[elim!]: "(TRY c\<^sub>1 CATCH c\<^sub>2, s) \<Rightarrow> xt"

  
(* Lemma 7.2 *)
lemma seq_assoc_l: "(c1;; c2;; c3, s) \<Rightarrow> (x, s') \<Longrightarrow> (c1;; (c2;; c3), s) \<Rightarrow> (x, s')"
 by auto

lemma seq_assoc_r: "(c1;; (c2;; c3), s) \<Rightarrow> (x, s') \<Longrightarrow> (c1;; c2;; c3, s) \<Rightarrow> (x, s')"
  by auto

lemma seq_assoc: "(c1;; c2;; c3, s) \<Rightarrow> s' \<longleftrightarrow> (c1;; (c2;; c3), s) \<Rightarrow> s'"
  by (auto simp: seq_assoc_l seq_assoc_r)

(* Section 7.2.4 *)
  
abbreviation
  equiv_c :: "com \<Rightarrow> com \<Rightarrow> bool" (infix "\<sim>" 50) where
  "c \<sim> c' \<equiv> (\<forall>s t. (c, s) \<Rightarrow> t = (c', s) \<Rightarrow> t)"

print_theorems
  
lemma while_if_equiv: "WHILE b DO c \<sim> IF b THEN (c;; WHILE b DO c) ELSE SKIP"
  by blast

lemma if_equiv: "IF b THEN c ELSE c \<sim> c"
  by auto
 
(* Lemma 7.6 *)  
(* Uses advanced rule induction from section 5.4.6 *)

lemma
  assumes "(WHILE b DO c, s) \<Rightarrow> (x,t)"
  assumes "c \<sim> c'"
  shows "(WHILE b DO c', s) \<Rightarrow> (x,t)"
using assms
  apply (induct "(WHILE b DO c, s)" "(x,t)" arbitrary: s)
   apply blast
  apply auto
  done

  (* or you can do *)  
lemma  while_equiv_aux: "(WHILE b DO c, s) \<Rightarrow> (x,t) \<Longrightarrow> c \<sim> c' \<Longrightarrow> (WHILE b DO c', s) \<Rightarrow> (x,t)"
  apply(induction "(WHILE b DO c)" s x t arbitrary: b c  rule: big_step_induct)
   apply auto
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
lemma imp_deterministic: "\<lbrakk> (c,s) \<Rightarrow> (x,t); (c,s) \<Rightarrow> (x',t') \<rbrakk> \<Longrightarrow> x' = x \<and> t' = t"
  apply (induction c s x t arbitrary: x' t' rule: big_step_induct)
  apply blast+
  done
    
lemma big_step_to_SKIP_or_THROW: "(c,s) \<Rightarrow> (x,t) \<Longrightarrow>  x = SKIP \<or> x = THROW"  
  by (induction c s x t rule: big_step_induct, blast+)
    
end