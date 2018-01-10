theory Exercise5p6
imports Main 
begin

fun elems :: "'a list \<Rightarrow> 'a set" where
    "elems [] = {}"
  | "elems (x#xs) = {x} \<union> elems xs"

value "elems [1,2,3,3,2,4]"

lemma "x \<in> elems xs \<Longrightarrow> \<exists>ys zs. xs = ys @ x # zs \<and> x \<notin> elems ys"  
proof (induction xs)
  case Nil
  then show ?case by auto
next
  case (Cons a xs)
  then show ?case
  proof cases
    assume "a = x"
    obtain ys where ys: "(ys:: 'a list) = []" by auto
    obtain zs where zs: "zs = xs" by auto
    then have "x \<notin> elems ys" using `a = x` ys by auto
    thus ?case using ys zs `a = x` by blast
  next
    (* \<exists>ys zs. a # xs = ys @ x # zs \<and> x \<notin> elems ys *)
    assume prems: "x \<in> elems (a # xs)"
    assume IH: "(x \<in> elems xs \<Longrightarrow> \<exists>ys zs. xs = ys @ x # zs \<and> x \<notin> elems ys)"
    assume "a \<noteq> x"
    then have "x \<in> elems xs" using prems by auto
    then obtain ys old_ys zs where 
      "ys = a # old_ys"
      "xs = old_ys @ x # zs"
      "x \<notin> elems old_ys" 
      using IH by auto
    then have "a # xs = ys @ x # zs \<and> x \<notin> elems ys" using `a \<noteq> x` by auto
    thus ?case by auto
  qed
qed   
  
end