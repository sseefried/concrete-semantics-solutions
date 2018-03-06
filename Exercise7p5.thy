theory Exercise7p5
imports Bigstep_sseefried
begin
  

(* Exercise 7.5 
  Prove or disprove (by giving a counterexample) *) 

(* First   *)
lemma "IF And b1 b2 THEN c1 ELSE c2 \<sim> IF b1 THEN IF b2 THEN c1 ELSE c2 ELSE c2"
  using IfTrue by fastforce

(* Second *)

(* An infinite loop with SKIP as body is not the same as SKIP. This will be required for the 
   the following proof *)
lemma inf_skips_not_eq_skip: "\<not> (WHILE (Bc True) DO SKIP \<sim> SKIP)" (is "\<not> (?while \<sim> ?skip) ")
proof
  fix s
  assume "(?while \<sim> SKIP)"
  hence "\<forall>s t. (?while, s) \<Rightarrow> t = (SKIP, s) \<Rightarrow> t" by blast
  hence "(?while, s) \<Rightarrow> s" by blast
  thus False
    by (induction "?while" s s rule: big_step_induct, auto)
qed
    
(* I really like this one because superficially they are equivalent but
   not in terms of termination behaviour! If b1 is always True and b2
   always False (no matter what the state) then the LHS terminates immediately
   whereas the RHS never does 
*)


(* I originally formulated this as 
   \<not> ( WHILE And b1 b2 DO c \<sim> WHILE b1 DO WHILE b2 DO c) 

  However this implicitly quantified b1, b2, and c with the meta-all operator which means
  they cannot be instantiated. This proof relies on being able to instantiate them with
  Bc True, Bc False, and SKIP respectively.

*)

lemma "\<not> (\<forall>b1 b2 c. WHILE And b1 b2 DO c \<sim> WHILE b1 DO WHILE b2 DO c)" (is "\<not> ?P") 
proof
  fix s
  assume "?P"
  hence counterex: "WHILE And (Bc True) (Bc False) DO SKIP \<sim> WHILE (Bc True) DO WHILE (Bc False) DO SKIP"
           (is "?while1 \<sim> ?while2") by blast
  have lhs_is_SKIP: "?while1 \<sim> SKIP" by auto
  hence "WHILE (Bc False) DO SKIP \<sim> SKIP" by auto 
  hence "?while2 \<sim> WHILE (Bc True) DO SKIP"  by (simp add: while_equiv) 
  (* Now I show that I can derive the following false theorem. An infinite loop of SKIPS
     is not the same as a SKIP *)
  hence "WHILE (Bc True) DO SKIP \<sim> SKIP" using counterex lhs_is_SKIP by auto 
  thus False by (simp add: inf_skips_not_eq_skip)
qed 
(* ^^^
   Finally happy with this proof even though it took me hours to get right *)

abbreviation
  equiv_c :: "com \<Rightarrow> com \<Rightarrow> bool" (infix "notsim" 50) where
  "c notsim c' \<equiv> \<not> (\<forall>s t. (c, s) \<Rightarrow> t = (c', s) \<Rightarrow> t)"


  
end