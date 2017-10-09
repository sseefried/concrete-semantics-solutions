theory Exercise3p11
imports AExp
begin

(*
This exercise is about a register machine and compiler for aexp. The machine instructions are

datatype instr = LDI int reg | LD vname reg | ADD reg reg

where type reg is a synonym for nat. Instruction LDI i r loads i into register r, 
LD x r loads the value of x into register r, and ADD r1 r2 adds register r2 to register r1.

Define the execution of an instruction given a state and a register state (= function from registers to integers); the result is the new register state:

fun exec1 :: instr \<Rightarrow> state \<Rightarrow> (reg \<Rightarrow> int) \<Rightarrow> reg \<Rightarrow> int

Define the execution exec of a list of instructions as for the stack machine. The compiler
takes an arithmetic expression a and a register r and produces a list of instructions whose 
execution places the value of a into r. The registers > r should be used in a stack-like 
fashion for intermediate results, the ones < r should be left alone. Define the compiler 
and prove it correct:

exec (comp a r) s rs r = aval a s.

*)

type_synonym reg = nat  

datatype instr = LDI int reg | LD vname reg | ADD reg reg

fun exec1 :: "instr \<Rightarrow> state \<Rightarrow> (reg \<Rightarrow> int) \<Rightarrow> reg \<Rightarrow> int" where
  "exec1 (LDI i r) s rs = rs (r := i)"  |
  "exec1 (LD x r) s  rs = rs (r := s x)" |
  "exec1 (ADD r1 r2) s rs = rs (r1 := rs r1 + rs r2)"
  
fun exec :: "instr list \<Rightarrow> state \<Rightarrow> (reg \<Rightarrow> int) \<Rightarrow> reg \<Rightarrow> int" where
  "exec [] s rs = rs" |
  "exec (i#is) s rs = exec is s (exec1 i s rs)"
  
lemma exec_append[simp]: "exec (is1 @ is2) s rs = exec is2 s (exec is1 s rs)"
  apply (induction is1 arbitrary: rs)
   apply auto
  done

value "exec1 (ADD 0 1) <> <0 := 1, 1 := 3> 0"
    
fun comp :: "aexp \<Rightarrow> reg \<Rightarrow> instr list" where
  "comp (N n) r = [LDI n r]" |
  "comp (V x) r = [LD  x r]" |
  "comp (Plus a1 a2) r = comp a1 r @ comp a2 (r+1) @ [ ADD r (r+1) ]" 

value "comp (Plus (N 1) (V ''x'')) 0"
value "exec (comp (Plus (N 1) (V ''x'')) 0) <''x'' := 10> <> 0"

lemma [simp]: "r' < r \<Longrightarrow> exec (comp a r) s rs r' = rs r'"
  apply (induction a arbitrary: r rs)
    apply auto
    done

lemma "exec (comp a r) s rs r = aval a s"
  apply (induction a arbitrary: r rs)
    apply (auto)
    done
  
  
      
end