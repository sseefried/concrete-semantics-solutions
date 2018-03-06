theory Exercise7p1
imports Bigstep_sseefried
begin

fun assigned :: "com \<Rightarrow> vname set" where
    "assigned SKIP = {}"
  | "assigned (Assign v _) = {v}"
  | "assigned (Seq c1 c2) = assigned c1 \<union> assigned c2"
  | "assigned (If b c1 c2) = assigned c1 \<union> assigned c2"
  | "assigned (While b c) = assigned c"

lemma "\<lbrakk> (c,s) \<Rightarrow> t; x \<notin> assigned c \<rbrakk> \<Longrightarrow> s x = t x"    
  by (induction rule: big_step_induct, auto)
    
(* lemma "\<lbrakk> (c,s) \<Rightarrow> t; x \<notin> assigned c \<rbrakk> \<Longrightarrow> s x = t x"    
proof (induction arbitrary: s t rule: assigned.induct)
  -- "Seq case"
  fix c1 c2 s t
  assume h1: "(\<And>s t. (c1, s) \<Rightarrow> t \<Longrightarrow> x \<notin> assigned c1 \<Longrightarrow> s x = t x)"
  assume h2: "(\<And>s t. (c2, s) \<Rightarrow> t \<Longrightarrow> x \<notin> assigned c2 \<Longrightarrow> s x = t x)"
  assume h3: "(c1;; c2, s) \<Rightarrow> t"
  assume h4: "x \<notin> assigned (c1;; c2)"
  then have r1: "\<exists>s'. (c1, s) \<Rightarrow> s' \<and> (c2, s') \<Rightarrow> t" using h3 by blast
  obtain s' where x: "(c1, s) \<Rightarrow> s' \<and> (c2, s') \<Rightarrow> t" using r1 by blast
  then have a: "s x = s' x" using x h1 h4 by fastforce
  then have b: "s' x = t x" using x h2 h4 by fastforce
  then show "s x = t x" using a by fastforce
next -- "WHILE case"
  fix b c s t 
  assume h1: "\<And>s t. (c, s) \<Rightarrow> t \<Longrightarrow> x \<notin> assigned c \<Longrightarrow> s x = t x"
  assume h2: "(WHILE b DO c, s) \<Rightarrow> t"
  assume h3: "x \<notin> assigned (WHILE b DO c)"
  then have "(bval b s \<and> (\<exists>s'. (c, s) \<Rightarrow> s' \<and> (WHILE b DO c, s') \<Rightarrow> t)) 
             \<or> (\<not>bval b s \<and> t = s)" using h2 by auto
  then show "s x = t x"
  proof
    assume "bval b s \<and> (\<exists>s'. (c, s) \<Rightarrow> s' \<and> (WHILE b DO c, s') \<Rightarrow> t)"
    then obtain s' where "(c, s) \<Rightarrow> s' \<and> (WHILE b DO c, s') \<Rightarrow> t" by auto
    then show "s x = t x" using h1 h2 h3 sorry
  next
    assume "\<not>bval b s \<and> t = s"
    then show "s x = t x" by blast
  qed
qed auto -- "Rest of the cases are trivial" *)


  
end