(* Title:     Quantum-Semantics/QSyntax.thy
   Author:    David Sanan, Nanyang Technological University 
   Copyright   2020
   License:     BSD
*)


theory QSyntax
  imports HOL.Complex vars HOL.Orderings  QHLProver.Partial_State
begin                                             

subsection \<open>Syntax\<close>

text \<open>Datatype for quantum programs\<close>
text \<open>State definition\<close>

\<comment>\<open>Following the semantics of Quantum_Sep, the state is composed of 
  a triple (\<delta>,\<sigma>,Q), where \<delta> is a real representing probability, \<sigma> represents
the stack and Q represents the quatum state\<close>

\<comment>\<open>The stack is similar to Quantum_Sep, but this stack does not have
  quantum variables, which have been moved to the quantum state.
 The quantum state is composed of a non-fixed list of quantum variables 
represented by their position index, and a vector of complex number 
  representing the current state of the quibits. 
  Each quantum variable contains a set of address of type 'q that has to be
 a lineal order. These addresses correspond with a quibit of the complex vector.
The vector represents the different components of the base representing
the quibits. Since the quantum state is the result of the tensor product
of the different variables, the vector dimension is the product of the size of each
variable\<close> 

type_synonym 'q q_vars = "(nat \<Rightarrow> 'q set)"
type_synonym 'q qstate = "'q q_vars \<times> complex vec"
type_synonym ('s,'q) state = "real \<times> 's \<times> 'q qstate"
type_synonym 's pred = "'s \<Rightarrow> bool" 
type_synonym 's assn = "'s set"
type_synonym ('s,'q) expr_q = "'s \<Rightarrow> 'q set"
type_synonym ('s) expr_c = "'s \<Rightarrow> complex"
type_synonym ('s) expr_nat = "'s \<Rightarrow> nat"
type_synonym ('s) expr_t = "'s \<Rightarrow> nat"
type_synonym ('s,'q) expr_a = "'s \<Rightarrow> 'q"
type_synonym ('s,'b) expr = "'s \<Rightarrow> 'b"


datatype ('a,'b,'s,'q::linorder) com = 
    Skip
  | SMod "'s \<Rightarrow> 's"
  | QMod "complex Matrix.mat" "('s,'q) expr_q"
  | IF "'s assn" "('a,'b,'s,'q) com" "('a, 'b,'s,'q) com"
  | While "'s assn" "('a, 'b,'s,'q) com"
  | Seq "('a, 'b,'s,'q) com" "('a, 'b,'s,'q) com"  ("_;/ _" [60, 61] 60)
  | Measure "'a"   "('s,'q) expr_q" ("_:=meassure / _" [60, 61] 60)
  | Alloc "'a"  "('s,nat) expr"  "('s,complex list) expr"  ("_:=alloc/[_/]/(_/)" [60, 61] 60)
  | Dispose "'s expr_nat" 
                       
locale h = vars + partial_state2 

context vars 
begin


lemma "(l::('a, 'b,'s, 'q::linorder) com) = l"
  by auto

end

end

