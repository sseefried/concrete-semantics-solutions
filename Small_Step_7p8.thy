theory Small_Step_7p8
imports 
Star
Big_Step_7p8

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
            (IF b THEN c;; WHILE b DO c ELSE SKIP,s)" |
Repeat:  "(REPEAT c UNTIL b, s) \<rightarrow> (c ;; IF b THEN REPEAT c UNTIL b ELSE SKIP, s)"

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
thm IfE
inductive_cases WhileE[elim]: "(WHILE b DO c, s) \<rightarrow> ct"
thm WhileE
inductive_cases RepeatE[elim]: "(REPEAT c UNTIL b, s) \<rightarrow> ct"
thm RepeatE
  
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
  obtain c1' s1' where a: "y = (c1', s1')" by fastforce   
  have star: "(c1';;c2, s1') \<rightarrow>* (c;;c2, s2)" using step.hyps(3) a by blast
  have first: "(c1;; c2, s1) \<rightarrow> (c1';;c2, s1')" using step.hyps(1) a  by blast
  thus ?case using first star step.hyps by (simp add: star.step)
qed

(* I was having trouble with proving   
     obtain c1' s1' where a: "y = (c1', s1')" 
  It is equivalent to the following. If you can prove that
  you can prove the "obtain" *)
 
lemma "\<And>thesis. (\<And>c1' s1'. y = (c1', s1') \<Longrightarrow> thesis) \<Longrightarrow> thesis"
proof -
  fix thesis
  assume [intro]: "\<And>c1' s1'. y = (c1', s1') \<Longrightarrow> thesis"
  then show thesis by fastforce
qed 
  
thm big_step.WhileTrue

(* Lemma 7.12 *)

lemma big_step_imp_small_step: "cs \<Rightarrow> t \<Longrightarrow> cs \<rightarrow>* (SKIP, t)"
proof (induction rule: big_step.induct)
  case (Skip s)
  then show ?case by blast
next
  case (Assign x a s)
  then show ?case by blast
next
  case (Seq c\<^sub>1 s\<^sub>1 s\<^sub>2 c\<^sub>2 s\<^sub>3)
  then show ?case by (blast intro: star.step star_seq2 star_trans)
next
  case (IfTrue b s c\<^sub>1 t c\<^sub>2)
  then have "(IF b THEN c\<^sub>1 ELSE c\<^sub>2, s) \<rightarrow> (c\<^sub>1, s)" by blast
  then show ?case using IfTrue.IH by (blast intro: star.step)
next
  case (IfFalse b s c\<^sub>2 t c\<^sub>1)
  then have "(IF b THEN c\<^sub>1 ELSE c\<^sub>2, s) \<rightarrow> (c\<^sub>2, s)" by blast
  then show ?case using IfFalse.IH by (blast intro: star.step)
next
  case (WhileFalse b s c)
  then have a: "(WHILE b DO c,s) \<rightarrow>
            (IF b THEN (c;; WHILE b DO c) ELSE SKIP,s)" by blast
  then have "(IF b THEN (c;; WHILE b DO c) ELSE SKIP,s) \<rightarrow>* (SKIP,s)" using WhileFalse.hyps by blast 
  then show "(WHILE b DO c, s) \<rightarrow>* (SKIP, s)" using a by (blast intro: star.step)
next
  case (WhileTrue b s\<^sub>1 c s\<^sub>2 s\<^sub>3)
  let ?w = "WHILE b DO c"
  let ?if = "IF b THEN c;; ?w ELSE SKIP"
  have 1: "(?w, s\<^sub>1) \<rightarrow>* (?if, s\<^sub>1)" by blast
  have 2: "(?if, s\<^sub>1) \<rightarrow>* (c;;?w, s\<^sub>1)" using WhileTrue(1) by blast
  have 3: "(c;;?w, s\<^sub>1) \<rightarrow>* (SKIP;;?w, s\<^sub>2)" using WhileTrue.IH(1) by (simp add: star_seq2)
  have 4: "(SKIP;;?w, s\<^sub>2) \<rightarrow>* (?w, s\<^sub>2)" by simp 
  then have "(?w, s\<^sub>1) \<rightarrow>* (?w, s\<^sub>2)" using 1 2 3 4 by (blast intro: star_trans)
  then show ?case using WhileTrue.IH by (blast intro: star_trans)
next
  (* It's worth noting that the "blast intro: star_trans" idiom works but 
     "using star_trans by blast" doesn't! *)
  case (RepeatFalse c s t b)
  let ?r  = "REPEAT c UNTIL b"
  let ?if = "IF b THEN REPEAT c UNTIL b ELSE SKIP"
  have "(?r, s) \<rightarrow>* (c ;; ?if, s)" by blast
  moreover have "(c ;; ?if, s) \<rightarrow>* (SKIP;;?if, t)" using RepeatFalse.IH star_seq2 by blast
  moreover have "(SKIP;;?if, t) \<rightarrow>* (SKIP, t)" using RepeatFalse.hyps(2) by (blast intro: star_trans)
  ultimately show ?case by (blast intro: star_trans star.step)
next
  case (RepeatTrue c s\<^sub>1 s\<^sub>2 b s\<^sub>3)
  let ?r  = "REPEAT c UNTIL b"
  let ?if = "IF b THEN REPEAT c UNTIL b ELSE SKIP"
  have "(?r, s\<^sub>1) \<rightarrow>* (c;; ?if, s\<^sub>1)" by blast
  moreover have "(c ;; ?if, s\<^sub>1) \<rightarrow>* (SKIP;;?if,s\<^sub>2)" using RepeatTrue.IH(1) star_seq2 by blast
  moreover have "(SKIP;;?if, s\<^sub>2) \<rightarrow> (?if, s\<^sub>2)" by (rule Seq1)
  moreover have "(?if, s\<^sub>2) \<rightarrow>* (SKIP, s\<^sub>3)" using RepeatTrue.hyps(2) RepeatTrue.IH(2) star_seq2  by (blast intro: star.step star_trans)
  ultimately show ?case by (blast intro: star_trans star.step)
qed 

  
(* I could have got an even smaller proof for the WhileTrue cases above if I'd have proved this 
   I could then have got 
     assume w: "(?w,s') \<rightarrow>* (SKIP,t)"
     assume c: "(c,s) \<rightarrow>* (SKIP,s')"
     have new_3: "(c;; ?w,s) \<rightarrow>* (SKIP,t)" by(rule seq_comp[OF c w])

     Then I could have used 1 2 and new_3

*)
lemma seq_comp: "\<lbrakk> (c\<^sub>1, s\<^sub>1) \<rightarrow>* (SKIP, s\<^sub>2); (c\<^sub>2, s\<^sub>2) \<rightarrow>* (SKIP, s\<^sub>3) \<rbrakk> \<Longrightarrow> (c\<^sub>1;;c\<^sub>2, s\<^sub>1) \<rightarrow>* (SKIP, s\<^sub>3)"
  by (blast intro: star_seq2 star_trans)
    
(* Lemma 7.15 *)
lemma small_big_comp: "\<lbrakk> cs \<rightarrow> cs'; cs' \<Rightarrow> t \<rbrakk> \<Longrightarrow> cs \<Rightarrow> t"    
  apply  (induction arbitrary: t rule: small_step.induct)
       apply blast+
done
   
(* Lemma 7.14 *)

(* The induction here was interesting because we didn't have to use "arbitrary" in
proof (induction "cs" "(SKIP, t)" rule: star.induct *)
lemma small_step_imp_big_step: "cs \<rightarrow>* (SKIP, t) \<Longrightarrow> cs \<Rightarrow> t"
proof (induction "cs" "(SKIP, t)" rule: star.induct)
  case refl
  then show ?case by blast
next
  case (step cs cs')
  assume "cs \<rightarrow> cs'"
     and "cs' \<Rightarrow> t"
  thus ?case by (rule small_big_comp)
qed

(* The textbook got us to prove "(c,s) \<Rightarrow> t \<longleftrightarrow> (c,s) \<rightarrow>* (SKIP, t)" 
   which ended up meaning that the proof for 7.18 did not go through easily.
   The form below, using "cs" instead of "(c,s)" is the same as the form for 
   final_iff_SKIP
 *)

(* Lemma 7.16 *)
lemma big_iff_small: "cs \<Rightarrow> t \<longleftrightarrow> cs \<rightarrow>* (SKIP, t)"  
proof
  show "cs \<Rightarrow> t \<Longrightarrow> cs \<rightarrow>* (SKIP, t)" by (rule big_step_imp_small_step)
next
  show "cs \<rightarrow>* (SKIP, t) \<Longrightarrow> cs \<Rightarrow> t" by (rule small_step_imp_big_step)
qed

definition final :: "com \<times> state \<Rightarrow> bool" where  
  "final cs \<longleftrightarrow> \<not>(\<exists>cs'. cs \<rightarrow> cs')"

(* Lemma 7.17 *)
lemma final_iff_SKIP: "final (c,s) = (c = SKIP)"
proof
  show "c = SKIP \<Longrightarrow> final (c, s)" by (auto simp: final_def)
next
  show "final (c, s) \<Longrightarrow> c = SKIP" 
    apply (simp add: final_def)
    apply (induction c rule: com.induct)
        apply blast+
    done
qed
  
(* Lemma 7.18 *)  
lemma "(\<exists>t. cs \<Rightarrow> t) \<longleftrightarrow> (\<exists>cs'. cs \<rightarrow>* cs' \<and> final cs')"
  apply (simp add: final_iff_SKIP)
  apply (simp add: big_iff_small)
  done
   
end
  
  
  
  