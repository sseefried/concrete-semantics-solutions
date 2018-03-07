theory Exercise7p7
imports Small_Step_sseefried
begin

(*  Exercise 7.7.

Let C :: nat \<Rightarrow> com be an infinite sequence of commands 
and S :: nat \<Rightarrow> state an infinite sequence of states such that 

a) C 0 = c;; d 
b) \<forall>n. (C n, S n) \<longrightarrow> (C (Suc n), S (Suc n)). 

Prove that either all C n are of the form c\<^sub>n;; d and it is always c\<^sub>n that is reduced, or c\<^sub>n
eventually becomes SKIP:
*)
thm small_step_induct
  
lemma 
  fixes
  C :: "nat \<Rightarrow> com" and
  S :: "nat \<Rightarrow> state"
assumes 
  "C 0 = c;;d"
  "\<forall>n. (C n, S n) \<rightarrow> (C (Suc n), S (Suc n))"
shows
  "(\<forall>n. \<exists>c\<^sub>1 c\<^sub>2.
    C n = c\<^sub>1;;d \<and>
    C (Suc n) = c\<^sub>2;;d \<and>
    (c\<^sub>1, S n) \<rightarrow> (c\<^sub>2, S (Suc n))) \<or>
    (\<exists>k. C k = SKIP;;d)" (is "(\<forall>n. ?P n) \<or> ?Q")  

proof cases
    assume "?Q"
    thus ?thesis by blast
 next
    assume "\<not> ?Q"
    have "\<forall>n. ?P n"
    proof 
      fix n
      show "?P n"
      proof (induction n)
      case 0
        from assms obtain c\<^sub>1 where c1: "C 0 = c\<^sub>1;; d" by auto
        from assms have "(C 0, S 0) \<rightarrow> (C (Suc 0), S (Suc 0))" by blast
        with c1 have "(c\<^sub>1;;d, S 0) \<rightarrow> (C (Suc 0), S (Suc 0))" by auto
        then obtain c\<^sub>2 where "C (Suc 0) = c\<^sub>2;;d" 
                         and "(c\<^sub>1, S 0) \<rightarrow> (c\<^sub>2, S (Suc 0))" 
                       using c1 `\<not> ?Q` by blast
        thus ?case using c1 by blast
      next
        case (Suc n)
        (* The trick here is that we set c\<^sub>1 to be the skolem constant for the c\<^sub>2 in the
           existential *)
        then obtain c\<^sub>1 where cn: "C (Suc n) = c\<^sub>1;;d" by blast
        from assms have "(C (Suc n), S (Suc n)) \<rightarrow> (C (Suc (Suc n)), S (Suc (Suc n)))" by blast
        with cn have "(c\<^sub>1;;d, S (Suc n)) \<rightarrow> (C (Suc (Suc n)), S (Suc (Suc n)))" by auto
        then obtain c\<^sub>2 where "C (Suc (Suc n)) = c\<^sub>2;;d"
                         and "(c\<^sub>1, S (Suc n)) \<rightarrow> (c\<^sub>2, (S (Suc (Suc n))))"
          using cn `\<not> ?Q` by blast
        thus ?case using cn by blast
      qed
    qed
    then show ?thesis by blast
qed
    
     
end

