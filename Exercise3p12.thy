theory Exercise3p12
imports AExp
begin

(* Exercise 3.12. 

This is a variation on the previous exercise. Let the instruc-
tion set be 

datatype instr0 = LDI0 val | LD0 vname | MV0 reg | ADD0 reg

All instructions refer implicitly to register 0 as the source (MV0) or target (all others).
 Define a compiler pretty much as explained above except that the compiled code leaves the 
value of the expression in register 0. Prove that 

exec (comp a r) s rs 0 = aval a s. 

*)


type_synonym reg = nat 

datatype instr = LDI0 val | LD0 vname | MV0 reg | ADD0 reg

fun exec1 :: "instr \<Rightarrow> state \<Rightarrow> (reg \<Rightarrow> int) \<Rightarrow> reg \<Rightarrow> int" where
  "exec1 (LDI0 i) s rs = rs (0 := i)"  | 
  "exec1 (LD0 x)  s rs = rs (0 := s x)" |
  "exec1 (MV0 r)  s rs = rs (r := rs 0)" |
  "exec1 (ADD0 r) s rs = rs (0 := rs 0 + rs r)"  
  
fun exec :: "instr list \<Rightarrow> state \<Rightarrow> (reg \<Rightarrow> int) \<Rightarrow> reg \<Rightarrow> int" where
  "exec [] s rs = rs" |
  "exec (i#is) s rs = exec is s (exec1 i s rs)"
  
lemma exec_append[simp]: "exec (is1 @ is2) s rs = exec is2 s (exec is1 s rs)"
  apply (induction is1 arbitrary: rs)
   apply auto
  done

value "exec1 (ADD0 1) <> <0 := 1, 1 := 2> 0"
    
(* r is the top of the stack. Leave registers < r alone *)
fun comp :: "aexp \<Rightarrow> reg \<Rightarrow> instr list" where
  "comp (N n) r = [LDI0 n]" |
  "comp (V x) r = [LD0  x]" |
(* We put intermediate computations in r+1, r+2 so that comp (Plus a1 a2) 0 is valid
   If we didn't then "comp2 a2" overwrites the intermediate result that is sitting in 0 
   Alternatively we could just prove a result where we have r > 0 as a precondition.
 *)
  "comp (Plus a1 a2) r = comp a1 (r+1) @ [MV0 (r+1)] @ comp a2 (r+2) @ [ADD0 (r+1)]"

value "comp (Plus (N 1) (V ''x'')) 0"
value "exec [LDI0 1, MV0 0, LD0 ''x''] <''x'' := 10> <> 0"
value "exec (comp (Plus (N 1) (V ''x'')) 0) <''x'' := 10> <> 0"

lemma [simp]: "r' < r \<and> r' \<noteq> 0 \<Longrightarrow> exec (comp a r) s rs r' = rs r'"
  apply (induction a arbitrary: r rs)
    apply auto
    done

lemma "exec (comp a r) s rs 0 = aval a s"
  apply (induction a arbitrary: r rs)
    apply (auto)
    done
        
end