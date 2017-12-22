theory Chapter4
imports Main
begin

value "1 + 2"
value "((\<lambda>x. undefined)(a\<^sub>1 := {a\<^sub>1}, a\<^sub>2 := {a\<^sub>1, a\<^sub>2})) a\<^sub>1" 

lemma "\<lbrakk> \<forall>x y. T x y \<or> T y x;
         \<forall>x y. A x y \<and> A y x \<longrightarrow> x = y;
         \<forall>x y. T x y \<longrightarrow> A x y \<rbrakk> 
       \<Longrightarrow> \<forall> x y. A x y \<longrightarrow> T x y"
  by blast

(* lemma "\<lbrakk> \<forall>x y. T x y \<or> T y x;
         \<forall>x y. A x y \<and> A y x \<longrightarrow> x = y;
         \<forall>x y. T x y \<longrightarrow> A x y \<rbrakk> 
       \<Longrightarrow> \<forall> x y. A x y \<longrightarrow> T x y"
  apply (rule allI, rule allI)
  apply (rule impI)
*)
    
thm conjI[OF refl[of "a"] refl[of "b"]]
  
lemma "Suc(Suc(Suc a)) \<le> b \<Longrightarrow> a \<le> b"
  by (drule Suc_leD, drule Suc_leD, drule Suc_leD, simp)

lemma "Suc(Suc(Suc a)) \<le> b \<Longrightarrow> a \<le> b"
  by (rule Suc_leD, rule Suc_leD, rule Suc_leD, assumption)

inductive ev :: "nat \<Rightarrow> bool" where
  ev0:  "ev 0" |
  evSS: "ev n \<Longrightarrow> ev (n + 2)"
  
fun odd :: "nat \<Rightarrow> bool" where
    "odd 0 = False"
  | "odd (Suc 0) = True"
  | "odd (Suc(Suc n)) = odd n"
    
fun evn :: "nat \<Rightarrow> bool" where
    "evn 0 = True"
  | "evn (Suc 0) = False"
  | "evn (Suc(Suc n)) = evn n"
  
lemma odd_evn_eq: "odd n \<Longrightarrow> \<not>(evn n)"
  apply (induction rule: odd.induct)
    by auto
    
lemma "ev m \<Longrightarrow> \<not>odd m"
  apply (induction rule: ev.induct )
  by simp_all
    
lemma "\<not> ev (Suc 0)"
  apply (rule notI)
  apply (induction rule: ev.induct)
    apply auto


    
end