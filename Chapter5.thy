theory Chapter5
imports Main
begin

theorem "\<exists>S. S \<notin> range (f :: 'a \<Rightarrow> 'a set)"
proof
  let ?S = "{x. x \<notin> f x}"
  show "?S \<notin> range f"
  proof
    assume "?S \<in> range f"
    then obtain y where "?S = f y" ..
    then show False
    proof (rule equalityCE)
      assume "y \<in> f y"
      assume "y \<in> ?S"
      then have "y \<notin> f y" ..
      with \<open>y \<in> f y\<close> show ?thesis by contradiction
    next
      assume "y \<notin> ?S"
      assume "y \<notin> f y"
      then have "y \<in> ?S" ..
      with \<open>y \<notin> ?S\<close> show ?thesis by contradiction
    qed
  qed
qed

(* sseefried: After much rewriting and searching online
  (https://isabelle.in.tum.de/library/HOL/HOL-Isar_Examples/Cantor.html)
  I've rewritten then proof so that it makes a whole lot more sense to me 
*)
lemma "\<not> surj (f :: 'a \<Rightarrow> 'a set)"
proof
  assume 0: "surj f"
  from 0 have 1: "\<forall>A. \<exists>a. A = f a" by (simp add: surj_def)
  from 1 have 2: "\<exists>a. { x. x \<notin> f x } = f a" by blast
  then obtain a where "{x. x \<notin> f x } = f a" by blast
  then show False
      proof (rule equalityCE)
      assume "a \<in> f a"
      assume "a \<in> { x. x \<notin> f x }"
      then have "a \<notin> f a" ..
      with \<open>a \<in> f a\<close> show ?thesis by contradiction
    next
      assume "a  \<notin>  { x. x \<notin> f x }"
      assume "a \<notin> f a"
      then have "a \<in> { x. x \<notin> f x } " ..
      with \<open>a \<notin> { x. x \<notin> f x }\<close> show ?thesis by contradiction
    qed
qed

(* Using much shorthand *)
lemma 
  fixes f :: "'a \<Rightarrow> 'a set"
  assumes s: "surj f"
  shows "False"
  proof -
    have "\<exists> a. {x. x \<notin> f x} = f a" using s
      by (auto simp: surj_def)
    thus "False" by blast
  qed

lemma
  fixes a b :: int
  assumes "b dvd (a + b)"
  shows "b dvd a"
proof -
  { fix k 
    assume 1: "a + b = b*k"
    have "\<exists>k'. a = b * k'"
    proof
      show "a = b*(k-1)" using 1 by (simp add: algebra_simps)
   qed}
  then show ?thesis using assms by (auto simp add: dvd_def)
qed


lemma "length (tl xs) = length xs - 1"
proof (cases xs)
  case Nil
  thus ?thesis by simp
next
  case (Cons y ys)
  thus ?thesis by simp
qed

lemma "\<Sum>{ 0..n::nat} = n*(n+1) div 2"
proof (induction n)
  case 0
  show ?case by simp
next
  case (Suc n)
  thus ?case by simp
qed

inductive ev :: "nat \<Rightarrow> bool" where
    ev0: "ev 0" 
  | evSS: "ev n \<Longrightarrow> ev (Suc (Suc n))"
  
fun evn :: "nat \<Rightarrow> bool" where
   "evn 0       = True"
 | "evn (Suc 0) = False"
 | "evn (Suc (Suc n)) = evn n"

lemma "ev n \<Longrightarrow> ev (n - 2)"
proof -
  assume "ev n"
  thus "ev (n - 2)"
  proof cases
    case ev0
    thus "ev (n - 2)" by (simp add: ev.ev0)
  next
    case (evSS k)
    thus "ev (n - 2)" by (simp add: ev.evSS)
  qed
qed

lemma "ev n \<Longrightarrow> n = 0 \<or> (\<exists>k. n = Suc (Suc k) \<and> ev k)"
proof (induction n rule: ev.induct)
  case ev0
  thus ?case by blast
next
  case evSS
  thus ?case by blast
qed




  


end