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
  C :: "nat \<Rightarrow> com" and          (* infinite sequence of commands *)
  S :: "nat \<Rightarrow> state"            (* infinite sequence of states   *)
assumes 
  "C 0 = c;;d"                   (* c is first command, d is remaining program *)
  "\<forall>n. (C n, S n) \<rightarrow> (C (Suc n), S (Suc n))" 
  (* ^^^ This assumption ties commands/state to subsequent commands/states. It states that
    the small step reduction sequence is infinite. Not all programs would have an infinite
    reduction sequence.
  *)
shows
  "(\<forall>n. \<exists>c\<^sub>1 c\<^sub>2.
    C n = c\<^sub>1;;d \<and>                (* d is remaining program *)
    C (Suc n) = c\<^sub>2;;d \<and>          (* c1 \<rightarrow> c2 and d remains the same *)
    (c\<^sub>1, S n) \<rightarrow> (c\<^sub>2, S (Suc n))) (* Case where first command c\<^sub>1 never terminates.
                                     d never evaluated *)
 \<or>  (\<exists>k. C k = SKIP;;d)"        (* Case where we get a SKIP, then remaining program d can be
                                   evaluated *)
 (is "(\<forall>n. ?P n) \<or> ?Q")  

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
    

(* 
   The condition "\<forall>n. (C n, S n) \<rightarrow> (C (Suc n), S (Suc n))" got me thinking that 
   if this is true then the first command cannot be SKIP because that "gets stuck".
   and it can't be an assignment since that will "get stuck" after one step   
  
   So I decided to prove it.

   There are many programs that could lead to an infinite sequence of reductions but these two
   are not among them!
 *)
lemma 
  fixes
  C :: "nat \<Rightarrow> com" and          (* infinite sequence of commands *)
  S :: "nat \<Rightarrow> state"            (* infinite sequence of states   *)
assumes 
  "\<forall>n. (C n, S n) \<rightarrow> (C (Suc n), S (Suc n))" (* States that small step eduction occurs infinitely *)
shows 
  "(\<forall>x a. C 0 \<noteq> x ::= a \<and> C 0 \<noteq> SKIP)" (is "\<forall>x a. ?P x a")
proof (rule allI, rule allI)
  fix x a
  from assms have "(C 0, S 0) \<rightarrow> (C (Suc 0), S (Suc 0))" by blast
  moreover from assms have "(C (Suc 0), S (Suc 0)) \<rightarrow> (C (Suc (Suc 0)), S (Suc (Suc 0)))" by blast
  ultimately show "?P x a"
    by (induction "C 0" "S 0" "C (Suc 0)" "S (Suc 0)" rule: small_step_induct, auto)
qed
  
end

