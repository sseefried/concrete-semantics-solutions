theory Exercise3p10
imports AExp
begin

(* Exercise 3.10 

A stack underflow occurs when executing an ADD instruction on a stack of size less than 2.
In our semantics stack underflow leads to a term involving hd [], which is not an error or
exception — HOL does not have those concepts — but some unspecified value. Modify theory
ASM such that stack underflow is modelled by None and normal execution by Some, i.e.,
the execution functions have return type stack option. Modify all theorems and proofs
accordingly. 

*)

   
subsection "Stack Machine"

datatype instr = LOADI val | LOAD vname | ADD

type_synonym stack = "val list"

abbreviation "hd2 xs == hd(tl xs)"
abbreviation "tl2 xs == tl(tl xs)"

text{* \noindent Abbreviations are transparent: they are unfolded after
parsing and folded back again before printing. Internally, they do not
exist.*}


fun exec1 :: "instr \<Rightarrow> state \<Rightarrow> stack \<Rightarrow> stack option" where
"exec1 (LOADI n) _ stk    = Some(n # stk)" |
"exec1 (LOAD x) s stk     = Some(s(x) # stk)"  |
"exec1  ADD _ (v1#v2#stk) = Some((v1 + v2) # stk)" | 
"exec1  ADD _ _           = None"

fun exec :: "instr list \<Rightarrow> state \<Rightarrow> stack \<Rightarrow> stack option" where
"exec [] _ stk = Some(stk)" |
"exec (i#is) s stk = 
  (case exec1 i s stk of
     Some stk2 \<Rightarrow> exec is s stk2 |
     None      \<Rightarrow> None)"


value "exec [LOADI 5, LOAD ''y'', ADD] <''x'' := 42, ''y'' := 43> [50]"

lemma exec_append[simp]:
  "exec (is1@is2) s stk = 
     (case exec is1 s stk of
       Some stk2 \<Rightarrow> exec is2 s stk2 |
       None      \<Rightarrow> None)"
 apply(induction is1 arbitrary: stk)
  apply (auto split: option.splits)
done


subsection "Compilation"

fun comp :: "aexp \<Rightarrow> instr list" where
"comp (N n) = [LOADI n]" |
"comp (V x) = [LOAD x]" |
"comp (Plus e\<^sub>1 e\<^sub>2) = comp e\<^sub>1 @ comp e\<^sub>2 @ [ADD]"

value "comp (Plus (Plus (V ''x'') (N 1)) (V ''z''))"

theorem exec_comp: "exec (comp a) s stk = Some (aval a s # stk)"
apply(induction a arbitrary: stk)
apply (auto)
done
  
end