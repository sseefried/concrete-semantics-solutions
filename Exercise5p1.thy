theory Exercise5p1
imports Main
begin 

lemma
  assumes T: "\<forall>x y. T x y \<or> T y x"
  and A:     "\<forall>x y. A x y \<and> A y x \<longrightarrow> x = y"
  and TA:    "\<forall>x y. T x y \<longrightarrow> A x y"
  and        "A x y"
  shows      "T x y"
proof -
  have "T x y \<or> T y x" using T by blast
  then show "T x y"
  proof
    assume "T x y"
    then show  "T x y" by blast
  next
    assume "T y x"
    hence "A y x" using TA        by blast
    hence "x = y" using `A x y` A by blast
    then show "T x y" using T     by blast
  qed
qed

end