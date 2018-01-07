theory Exercise5p5
imports Main
begin

inductive star :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" for r where
    refl: "star r x x"
  | step: "r x y \<Longrightarrow> star r y z \<Longrightarrow> star r x z"

inductive iter :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> nat \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" for r where
    zero: "iter r 0 x x"
  | step: "r x y \<Longrightarrow> iter r n y z \<Longrightarrow> iter r (Suc n) x z"
  
lemma "iter r n x y \<Longrightarrow> star r x y"
proof (induction rule: iter.induct)
  case zero
  fix x
  show "star r x x" by (simp add: star.refl star.step)
next
  case step
  fix x n y z
  assume "r x y"
     and "star r y z"
  then show "star r x z" by (simp add: star.step)
qed

  
  
end