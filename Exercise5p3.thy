theory Exercise5p3
imports Main
begin

inductive ev :: "nat \<Rightarrow> bool" where
    ev0:  "ev 0" 
  | evSS: "ev n \<Longrightarrow> ev (Suc (Suc n))"


(* Exercise 5.3 *)  
lemma 
  assumes a: "ev (Suc (Suc n))"
  shows "ev n"
proof -
  show ?thesis using a 
  proof cases
    case evSS
    thus ?thesis by auto
  qed
qed  


  
  
end