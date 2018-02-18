theory Exercise7p2
imports Bigstep_sseefried
begin

fun skip :: "com \<Rightarrow> bool" where
    "skip SKIP         = True"
  | "skip (Assign v e) = False"
  | "skip (Seq c1 c2)  = (skip c1 \<and> skip c2)"
  | "skip (If b c1 c2) = (skip c1 \<and> skip c2)"
  | "skip (While b c)  = False"
 
lemma "skip c \<Longrightarrow> c \<sim> SKIP"
proof (induction c)
  case (Seq c1 c2)
  hence  "skip c1" and "skip c2" by auto
  hence "c1 \<sim> SKIP" and "c2 \<sim> SKIP" using Seq.IH by auto
  thus "c1 ;; c2 \<sim> SKIP" by fastforce
next
  case (If b c1 c2)
  hence "skip c1" and "skip c2" by auto
  hence "c1 \<sim> SKIP" and "c2 \<sim> SKIP" and "c1 \<sim> c2" using If.IH by auto
  thus "IF b THEN c1 ELSE c2 \<sim> SKIP" by blast
qed auto+
  
end