theory Exercise7p6
imports Bigstep_sseefried
begin

abbreviation DoWhile :: "com \<Rightarrow> bexp \<Rightarrow> com" ("(DO _/ WHILE _)"  [0, 61] 61) where
  "DoWhile c b \<equiv> c;; WHILE b DO c"

fun dewhile :: "com \<Rightarrow> com" where
    "dewhile SKIP = SKIP"
  | "dewhile (Assign v aexp) = Assign v aexp"
  | "dewhile (Seq c1 c2)     = Seq (dewhile c1) (dewhile c2)"
  | "dewhile (If b c1 c2)    = If b (dewhile c1) (dewhile c2)"
  | "dewhile (While b c)     = IF b THEN (DO c WHILE b) ELSE SKIP"

print_theorems
    
(* c \<sim> c' \<equiv> \<forall>s s'. (c,s) \<Rightarrow> s' = (c',s) \<Rightarrow> s' *)
  
lemma "dewhile c \<sim> c"
proof -
  { fix s t
    have "(dewhile c, s) \<Rightarrow> t \<Longrightarrow> (c, s) \<Rightarrow> t"
    proof (induction c arbitrary: s t)
      case (Seq c1 c2)
      hence "\<exists>s'. (dewhile c1, s) \<Rightarrow> s' \<and> (dewhile c2, s') \<Rightarrow> t" by auto
      then obtain s' where l: "(dewhile c1, s) \<Rightarrow> s'" and r: "(dewhile c2, s') \<Rightarrow> t" by blast
      hence "(c1, s) \<Rightarrow> s'" and "(c2, s') \<Rightarrow> t" using Seq.IH by auto
      thus "(c1;;c2, s) \<Rightarrow> t" by blast
    qed auto+ -- "other cases are trivial"
  } note forward = this
  { fix s t
    have "(c,s) \<Rightarrow> t \<Longrightarrow> (dewhile c, s) \<Rightarrow> t"
    proof (induction c arbitrary: s t)
      case (Seq c1 c2)
      hence "\<exists>s'. (c1, s) \<Rightarrow> s' \<and> (c2, s') \<Rightarrow> t" by auto
      then obtain s' where "(c1, s) \<Rightarrow> s'" and "(c2, s') \<Rightarrow> t" by blast
      hence "(dewhile c1, s) \<Rightarrow> s'" and "(dewhile c2, s') \<Rightarrow> t" using Seq.IH by auto
      hence "(dewhile c1;; dewhile c2, s) \<Rightarrow> t" by blast
      thus  "(dewhile (c1 ;; c2), s) \<Rightarrow> t" by auto
    next
      case (While b c)
      thus "(dewhile (WHILE b DO c), s) \<Rightarrow> t" using while_if_equiv by auto
    qed auto+
  } note backward = this
  show ?thesis using forward backward by blast
qed
      
end
