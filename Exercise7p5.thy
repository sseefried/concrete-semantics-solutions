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

(***********************)
(* Third *)
   
(* The trick with this proof was to structure the proof almost exactly 
   the same as I would have done a pencil and paper proof of the same 
   thing.
*)

abbreviation
  Or :: "bexp \<Rightarrow> bexp \<Rightarrow> bexp" where
  "Or b1 b2 \<equiv> Not (And (Not b1) (Not b2))"
  
lemma while_cond_terminate: "(WHILE b DO c, s) \<Rightarrow> t \<Longrightarrow> \<not> bval b t"
  by (induction "WHILE b DO c" s t rule: big_step_induct, auto)
 
lemma "WHILE Or b1 b2 DO c \<sim> WHILE Or b1 b2 DO c;; WHILE b1 DO c"
proof -
  { fix s t
    assume assm: "(WHILE Or b1 b2 DO c,s ) \<Rightarrow> t" (is "(?while1, s) \<Rightarrow> t")
    hence "\<not> bval (Or b1 b2) t" using while_cond_terminate by blast
    hence "\<not> bval b1 t" by auto
    hence "(?while1;; WHILE b1 DO c, s) \<Rightarrow> t" (is "(?while1;;?while2,s) \<Rightarrow> t") using assm by blast
    hence "(?while1, s) \<Rightarrow> t \<Longrightarrow> (?while1;;?while2, s) \<Rightarrow> t" by blast
  } note forward = this 

  { fix s t
    assume assm1: "(WHILE Or b1 b2 DO c;; WHILE b1 DO c, s) \<Rightarrow> t" (is "(?while1;;?while2,s) \<Rightarrow> t")
    hence ex: "\<exists>s'. (?while1, s) \<Rightarrow> s' \<and> (?while2, s') \<Rightarrow> t" by auto
    then obtain s' where e1: "(?while1, s) \<Rightarrow> s'"
                     and e2: "(?while2, s') \<Rightarrow> t" by blast
    hence "\<not> bval b1 s'" using while_cond_terminate by fastforce
    hence "s' = t" using e2 by blast
    hence "(?while1, s) \<Rightarrow> t" using e1 by blast
    hence "(?while1;; ?while2, s) \<Rightarrow> t \<Longrightarrow> (?while1, s) \<Rightarrow> t" by blast
  } note backward = this
  show ?thesis using forward backward by blast
qed

end