theory Exercise4p1
imports Main
begin

(* 

Exercise 4.1. Start from the data type of binary trees defined earlier:

datatype 'a tree = Tip | Node "'a tree" 'a "'a tree"

Define a function 

  set :: 'a tree \<Rightarrow> 'a set 

that returns the elements in a tree and a function 

  ord :: int tree \<Rightarrow> bool 

that tests if an int tree is ordered.
Define a function ins that inserts an element into an ordered int tree while maintaining the
order of the tree. If the element is already in the tree, the same tree should be returned.
Prove correctness of ins: 

  set (ins x t) = {x} \<union> set t 

and 

  ord t \<Longrightarrow> ord (ins i t).
*)

datatype 'a tree = Tip | Node "'a tree" 'a "'a tree"


    
fun set :: "'a tree \<Rightarrow> 'a set" where
    "set Tip = {}"
  | "set (Node t1 i t2) = set t1 \<union> {i} \<union> set t2"

fun ord :: "int tree \<Rightarrow> bool" where
    "ord Tip = True"
  | "ord (Node t1 i t2) = (ord t1 \<and> ord t2 \<and> (\<forall>x \<in> set t1. x < i) \<and> (\<forall>x \<in> set t2. i \<le> x))"

fun ins :: "int \<Rightarrow> int tree \<Rightarrow> int tree" where
    "ins x Tip = Node Tip x Tip"  
  | "ins x (Node t1 i t2) = (if x < i then Node (ins x t1) i t2 else Node t1 i (ins x t2))"

value "ins 3 (Node (Node Tip 2 Tip) 3 Tip)"
value "ord (ins 3 (Node (Node Tip 2 Tip) 3 Tip))"
  
value "ord Tip"
value "ord (Node Tip 1 Tip)"
value "ord (Node (Node Tip 3 Tip) 2 Tip)"
  
lemma set_ins: "set (ins x t) = {x} \<union> set t"
  by (induction t, auto)

(* 

I'm presenting my first solution here since it took me quite a while to get.
I was satisfied with the theorems ord_helper1 and ord_helper2 as they were
understandable and seemed to get me where I wanted to go.

However, I had to use rule_tac in order to get the right schematic variables to
unify. This was deeply unsatisfying partly because the book concreate semantics
does not cover rule_tac at all. (I learned its use during my seL4 days.)

More information can be found here:
https://svhol.pbmichel.de/reference/rule_method

*)

lemma ord_helper1: "(\<forall>x \<in> set t. x < y) \<Longrightarrow> i < y \<Longrightarrow> x \<in> set (ins i t) \<Longrightarrow> x < y"
  apply (induction t)
   apply (auto split: if_splits)
  done

lemma ord_helper2: "(\<forall>x \<in> set t. y \<le> x) \<Longrightarrow> y \<le> i \<Longrightarrow> x \<in> set (ins i t) \<Longrightarrow> y \<le> x"
  apply (induction t)
   apply (auto split: if_splits)
    done
    
lemma "ord t \<Longrightarrow> ord (ins i t)"
  apply (induction t, auto)
   apply (rule_tac y="x2" in ord_helper1, simp_all)
  apply (rule_tac y="x2" in ord_helper2, simp_all)
  done

(* The correct solution is to use set_ins above as part of your simp set *)
lemma "ord t \<Longrightarrow> ord (ins i t)"
  apply (induction t, auto simp: set_ins)
    done
     
end