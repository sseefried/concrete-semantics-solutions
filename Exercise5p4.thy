theory Exercise5p4
imports Main
begin

inductive ev :: "nat \<Rightarrow> bool" where
    ev0:  "ev 0" 
  | evSS: "ev n \<Longrightarrow> ev (Suc (Suc n))"


(* Exercise 5.4 *)  
lemma "\<not> ev (Suc (Suc (Suc 0)))" (is "\<not>?P")
proof
  assume "?P" 
  then have "ev (Suc 0)" by cases (* This is the same as "proof cases qed" because
                                     there is nothing to prove *)
  then show False by cases
qed  



  
  
end