(* Title:     Quantum-Semantics/QSyntax.thy
   Author:    David Sanan, Nanyang Technological University 
   Copyright   2020
   License:     BSD
*)


theory QSyntax
  imports HOL.Complex vars HOL.Orderings   Q_State vars
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

type_synonym q_vars = "(nat \<Rightarrow>nat set)"
type_synonym  qstate = "q_vars \<times> (complex) QState"
type_synonym qheap = "nat set \<times> complex vec"
type_synonym 's state = "real \<times> 's \<times>  qstate"
type_synonym 's pred = "'s \<Rightarrow> bool" 
type_synonym 's assn = "'s set"
type_synonym 's expr_q = "'s\<times>q_vars \<Rightarrow> nat set"
type_synonym 's expr_c = "'s \<Rightarrow> complex"
type_synonym 's expr_nat = "'s \<Rightarrow> nat"
type_synonym 's expr_t = "'s \<Rightarrow> nat"
type_synonym 's expr_a = "'s \<Rightarrow> nat"
type_synonym ('s,'b) expr = "'s \<Rightarrow> 'b"

definition get_prob ::"'s state \<Rightarrow> real"
  where "get_prob \<sigma> = fst \<sigma>"

definition get_qstate ::"'s state \<Rightarrow> qstate"
  where "get_qstate \<sigma> = snd (snd \<sigma>)"

definition get_stack::"'s state \<Rightarrow> 's"
  where "get_stack \<sigma> = fst (snd \<sigma>)"

definition set_prob ::"'s state \<Rightarrow> real \<Rightarrow> 's state"
  where "set_prob \<sigma> v = (v, get_stack \<sigma>, get_qstate \<sigma>)"

definition set_qstate ::"'s state \<Rightarrow> qstate \<Rightarrow> 's state"
  where "set_qstate \<sigma> v = (get_prob \<sigma>, get_stack \<sigma>, v)"

definition set_stack::"'s state \<Rightarrow> 's \<Rightarrow> 's state"
  where "set_stack \<sigma> v = (get_prob \<sigma>, v, get_qstate \<sigma>)"


datatype 's XQState = Normal "'s state" | Fault 

datatype ('a, 's) com = 
    Skip
  | SMod "'s \<Rightarrow> 's"
  | QMod "complex Matrix.mat" "'s expr_q"
  | IF "'s assn" "('a, 's) com" "('a, 's) com"
  | While "'s assn" "('a, 's) com"
  | Seq "('a, 's) com" "('a, 's) com"  ("_;;/ _" [60, 61] 60)
  | Measure "'a"   "'s expr_q" ("_:=meassure / _" [60, 61] 60)
  | Alloc "'a"  "('s,nat) expr"  "('s,complex list) expr"  ("_:=alloc[_] (_)" [60, 61] 60)
  | Dispose "('s,nat) expr" 



type_synonym ('v,'b,'s) QConf = "('v,'s) com \<times> 's XQState"



definition Q_domain::"q_vars \<Rightarrow> nat set" 
  where "Q_domain q_vars \<equiv> \<Union> (q_vars ` UNIV)"

definition ket_dim ::"q_vars \<Rightarrow> nat"
  where "ket_dim q_vars \<equiv>  card (Q_domain q_vars)"


definition new_q_addr::"('s \<Rightarrow> nat) \<Rightarrow> 's state \<Rightarrow> (nat set) set"
  where "new_q_addr f \<sigma>  \<equiv> {s.  card s = (f (get_stack \<sigma>)) \<and> (Min s > Max (Q_domain (fst (get_qstate \<sigma>))))}"  

lemma all_gt: "finite s' \<Longrightarrow> finite s \<Longrightarrow> 
       Min s > Max s' \<Longrightarrow> e \<in> s \<Longrightarrow> e' \<in> s' \<Longrightarrow> e > e'"
  using Max_less_iff less_le_trans by fastforce

lemma neq_q_addr_finites:"f (get_stack \<sigma>)\<noteq>0 \<Longrightarrow> S \<in> new_q_addr f \<sigma> \<Longrightarrow> finite S"
  unfolding new_q_addr_def
  using card_infinite by force

lemma new_q_addr_gt_old_q_addr:
  "f (get_stack \<sigma>)\<noteq>0 \<Longrightarrow> finite (Q_domain (fst (get_qstate \<sigma>))) \<Longrightarrow> 
   S \<in> new_q_addr f \<sigma> \<Longrightarrow> e \<in> S \<Longrightarrow>
   e' \<in> (Q_domain (fst (get_qstate \<sigma>))) \<Longrightarrow> e > e'"
  unfolding new_q_addr_def using all_gt 
  by (metis (mono_tags, lifting) card_infinite mem_Collect_eq)

lemma new_q_addr_ortho_old_q_addr:
  assumes a0:"f (get_stack \<sigma>)\<noteq>0" and a1:"finite  (Q_domain (fst (get_qstate \<sigma>)))" and a2:"S \<in> new_q_addr f \<sigma>" 
  shows "S \<subseteq> - (Q_domain (fst (get_qstate \<sigma>)))"
proof - 
  have f4: "card S = f (get_stack \<sigma>) \<and> Max (Q_domain (fst (get_qstate \<sigma>))) < Min S"
    using a2 unfolding new_q_addr_def  by fastforce
  then have "card S \<noteq> 0"
    using a0 by simp
  then have "finite S"
    by (meson card_infinite)
  then show ?thesis
    using f4 a1 by (meson ComplI Max.coboundedI Min.coboundedI le_less_trans 
                    less_le_not_le subsetI)
qed 

(* definition list_dims_set::"'q set \<Rightarrow> nat list"
  where "list_dims_set qvars \<equiv> if qvars = {} then [1] 
                            else replicate (card qvars) 2"

definition list_dims::"'q::linorder set \<Rightarrow> nat list"
  where "list_dims qvars \<equiv> replicate (card qvars) 2" *)

definition dom_q_vars::"q_vars \<Rightarrow> nat set"
  where "dom_q_vars q_vars \<equiv> Set.filter (\<lambda>e. q_vars e\<noteq>{}) UNIV"
                                                  
definition dims_heap::"q_vars \<Rightarrow> nat list"
  where "dims_heap q_vars \<equiv> (list_dims o Q_domain) q_vars"

definition qvars_lin_set::"q_vars \<Rightarrow> nat set"
  where "qvars_lin_set q_vars \<equiv> {0 ..< (ket_dim q_vars)}"

definition qvars_lin_sets::"q_vars \<Rightarrow> q_vars \<Rightarrow> nat set"
  where "qvars_lin_sets q_vars q_vars' \<equiv> {(ket_dim q_vars) ..< (ket_dim q_vars')}"

(* definition top_lin_set::"'q set \<Rightarrow> nat" where
  "top_lin_set qset \<equiv> if qset = {} then 1 else card qset"

definition lin_set_alt::"'q set \<Rightarrow> nat set"
  where "lin_set_alt qset \<equiv> if qset = {} then {0} else {0 ..< (card qset)}"

definition lin_sets_alt::"nat \<Rightarrow> 'q set \<Rightarrow> nat set"
  where "lin_sets_alt n q_vars' \<equiv> if q_vars' = {} then  {n}
                                   else  {n ..< card (q_vars')}"

definition lin_set::"'q::linorder set \<Rightarrow> nat set"
  where "lin_set qset \<equiv> {0 ..< (card qset)}"

definition lin_sets::"'q::linorder set \<Rightarrow> 'q::linorder set \<Rightarrow> nat set"
  where "lin_sets q_vars q_vars' \<equiv> {card (q_vars) ..< card (q_vars')}"
*)

definition sorted_list_from_set::"'q::linorder set \<Rightarrow> 'q::linorder list"
  where "sorted_list_from_set s \<equiv> THE l. strict_sorted l \<and> set l = s"

definition to_heap::"qstate \<Rightarrow> (complex) QState"
  where "to_heap q \<equiv> (snd q)"



definition projection1::"nat \<Rightarrow> nat \<Rightarrow> 'a::comm_ring_1 mat" ("1\<^sub>_ _") where
  "projection1 k n \<equiv> mat n n (\<lambda> (i,j). if i = k \<and> j = k then 1 else 0)"


locale h = vars + partial_state2 

context h 
begin


lemma "(l::('a, 's) com) = l"
  by auto

end

end

