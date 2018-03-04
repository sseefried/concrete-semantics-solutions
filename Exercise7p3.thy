theory Exercise7p3
imports Bigstep_sseefried
begin

fun deskip :: "com \<Rightarrow> com" where
    "deskip SKIP          = SKIP"
 |  "deskip (Assign v e)  = Assign v e"
 |  "deskip (Seq c1 c2) = 
      (case (deskip c1, deskip c2) of
         (SKIP, SKIP)  \<Rightarrow> SKIP
       | (SKIP, q)    \<Rightarrow> q
       | (p, SKIP)    \<Rightarrow> p
       | (p, q)      \<Rightarrow> (p;;q))"
 |  "deskip (If b c1 c2)  = 
      (case (deskip c1, deskip c2) of
         (SKIP, SKIP) \<Rightarrow> SKIP
       | (p, q)       \<Rightarrow> If b p q)"
 |  "deskip (While b c)   = While b (deskip c)"

print_theorems 
 
value "deskip (SKIP;; WHILE b DO (x ::= a;; SKIP))"

lemma skip2: "c ;; SKIP \<sim> c"
proof (induction c)
qed auto+

lemma "deskip c \<sim> c"
proof (induction c)
  case (While b c)
  thus "deskip (WHILE b DO c) \<sim> WHILE b DO c" by (simp add: while_equiv)
next 
  case (Seq c1 c2)
  have a: "(deskip c1;; deskip c2) \<sim> c1;; c2" using Seq.IH by auto
  (* Use split any time you have a case inside your function definition. *)
  have "(deskip c1;; deskip c2) \<sim> deskip (c1;;c2)" using Seq.IH by (auto split: com.split)
  thus "deskip (c1 ;; c2) \<sim> c1 ;; c2" using a by auto
next
  case (If b c1 c2)
  have a: "If b (deskip c1) (deskip c2) \<sim> If b c1 c2" using If.IH by auto
  (* Use split any time you have a case inside your function definition *)
  have "If b (deskip c1) (deskip c2) \<sim> deskip (If b c1 c2)" using If.IH if_equiv by (auto split: com.split)
  thus "deskip (If b c1 c2) \<sim> If b c1 c2" using a by auto
qed auto+




  
end