theory Small_Step_sseefried
imports 
Star
BigStep_sseefried

begin

subsection "The transition relation"

inductive
  small_step :: "com * state \<Rightarrow> com * state \<Rightarrow> bool" (infix "\<rightarrow>" 55)
where
Assign:  "(x ::= a, s) \<rightarrow> (SKIP, s(x := aval a s))" |

Seq1:    "(SKIP;;c\<^sub>2,s) \<rightarrow> (c\<^sub>2,s)" |
Seq2:    "(c\<^sub>1,s) \<rightarrow> (c\<^sub>1',s') \<Longrightarrow> (c\<^sub>1;;c\<^sub>2,s) \<rightarrow> (c\<^sub>1';;c\<^sub>2,s')" |

IfTrue:  "bval b s \<Longrightarrow> (IF b THEN c\<^sub>1 ELSE c\<^sub>2,s) \<rightarrow> (c\<^sub>1,s)" |
IfFalse: "\<not>bval b s \<Longrightarrow> (IF b THEN c\<^sub>1 ELSE c\<^sub>2,s) \<rightarrow> (c\<^sub>2,s)" |

While:   "(WHILE b DO c,s) \<rightarrow>
            (IF b THEN c;; WHILE b DO c ELSE SKIP,s)"

abbreviation
  small_steps :: "com * state \<Rightarrow> com * state \<Rightarrow> bool" (infix "\<rightarrow>*" 55)
where "x \<rightarrow>* y == star small_step x y"

code_pred small_step .
 
lemmas small_step_induct = small_step.induct[split_format(complete)]

declare small_step.intros[simp,intro]

text{* Rule inversion: *}

inductive_cases SkipE[elim!]: "(SKIP,s) \<rightarrow> ct"
thm SkipE
inductive_cases AssignE[elim!]: "(x::=a,s) \<rightarrow> ct"
thm AssignE
inductive_cases SeqE[elim]: "(c1;;c2,s) \<rightarrow> ct"
thm SeqE
inductive_cases IfE[elim!]: "(IF b THEN c1 ELSE c2,s) \<rightarrow> ct"
inductive_cases WhileE[elim]: "(WHILE b DO c, s) \<rightarrow> ct"

(* Lemma 7.11 *)
  
lemma "cs \<rightarrow> cs' \<Longrightarrow> cs \<rightarrow> cs'' \<Longrightarrow> cs'' = cs'"
  apply (induction cs' arbitrary: cs'' rule: small_step.induct)
  apply blast+
  done
   
(* Lemma 7.13 *)
lemma star_seq2: "(c1, s1) \<rightarrow>* (c, s2) \<Longrightarrow> (c1;;c2, s1) \<rightarrow>* (c;; c2, s2)"
proof (induction "(c1,s1)" "(c,s2)" arbitrary: c1 s1 c s2  rule: star.induct)
  case (refl)
  then show ?case by simp
next
  case (step y)
  fix c1' s1'
  obtain c1' s1' where a: "y = (c1', s1')" by fastforce
  have star: "(c1';;c2, s1') \<rightarrow>* (c;;c2, s2)" using step.hyps(3) a by blast
  have first: "(c1;; c2, s1) \<rightarrow> (c1';;c2, s1')" using step.hyps(1) a  by blast
  show ?case using first star step.hyps by (simp add: star.step)
qed



(* Lemma 7.12 *)
lemma "cs \<Rightarrow> t \<Longrightarrow> cs \<rightarrow>* (SKIP, t)"
  
    
    
end
  
  