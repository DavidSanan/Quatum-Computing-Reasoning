(* Title:     Quantum-Semantics/QSemantics.thy
   Author:    David Sanan, Singapore Institute of Technology 
   Copyright   2023
   License:     BSD
*)

theory QSemantics
  imports QSemanticsBig
begin

subsection \<open>Syntax\<close>

text \<open>Semantics for quantum programs\<close>

primrec redex:: "('a,'s) com \<Rightarrow> ('a,'s) com"
where
"redex Skip = Skip" |
"redex (SMod f) = (SMod f)" |
"redex (QMod m q) = (QMod m q)" |
"redex (Seq c\<^sub>1 c\<^sub>2) = redex c\<^sub>1" |
"redex (IF b c\<^sub>1 c\<^sub>2) = (IF b c\<^sub>1 c\<^sub>2)" |
"redex (While b c) = (While b c)" |
"redex (Measure v q) = Measure v q" |
"redex (Alloc var v) = Alloc var v " |
"redex (Dispose v q) = Dispose v q"


(* m = partial_state2.ptensor_mat (dims_heap \<vv>) (q \<sigma>) ((Q_domain \<vv>)-(q \<sigma>)) (M::complex mat) (1\<^sub>m (card ((Q_domain \<vv>) - (q \<sigma>))))*)
(* abbreviation "tensor_vec \<equiv> partial_state2.ptensor_vec" *)

(* definition
  unit_vecl :: "nat \<Rightarrow> nat \<Rightarrow> complex list"
  where "unit_vecl n i = list_of_vec (unit_vec n i)" *)



context vars
begin

inductive step::"('v,'s) QConf \<Rightarrow> ('v,'s) QConf \<Rightarrow> bool" 
  ("\<turnstile> _ \<rightarrow> _" [81,81] 80)  
  where 
\<comment>\<open>SMod  modifies the stack of non-qubits variables \<sigma> with f \<sigma>, where f is a 
  function modifying the stack\<close>
  StackMod: "\<turnstile> (SMod f, Normal (\<delta>,\<sigma>,\<Q>)) \<rightarrow> (Skip, Normal (\<delta>,f \<sigma>,\<Q>))"

\<comment>\<open>QMod modifies the set of qubits of the Quantum State given by q \<sigma> with the 
  transformation matrix M, any qubit not included in q \<sigma> remains the same\<close>

 | QMod:"\<forall>e \<in> (q \<sigma>). (QStateM_map \<Q>) e \<noteq> {}  \<Longrightarrow> unitary M \<Longrightarrow>
         \<Q>' = matrix_sep_QStateM (q \<sigma>) \<Q> M \<Longrightarrow>  
         M \<in> carrier_mat m m  \<Longrightarrow>           
         \<turnstile> (QMod M q, Normal (\<delta>,\<sigma>, \<Q>)) \<rightarrow> (Skip,Normal (\<delta>, \<sigma>,  \<Q>'))"

\<comment>\<open>QMod fails if the set of qubits to be modified is not included in the quantum state\<close>
 | QMod_F:"\<exists>e. e \<in> q \<sigma> \<and> (QStateM_map \<Q>) e = {}  \<or>  \<not> unitary M  \<or> 
         M \<notin> carrier_mat m m   \<Longrightarrow>        
          \<turnstile> (QMod M q, Normal (\<delta>,\<sigma>, \<Q>)) \<rightarrow> (Skip, Fault)"

\<comment>\<open>Alloc takes a normal variable "q" representing the variable where the index to the qubits is store
   an function e from the state \<sigma> to a natural number representing the number of qubits to allocate
  and an initialization value for the allocated qubits 


  We will require that a program is well formed, meaning that the types are correct.
  A call to Alloc is well formed if the ty"'s state"pe of q is a natural number\<close>

 | Alloc:"q' \<notin> (dom_q_vars (QStateM_map \<Q>)) \<Longrightarrow> (length (v \<sigma>) > 1) \<Longrightarrow> 
              \<vv>' = (\<lambda>i. {})(q' := q'_addr) \<and>  \<sigma>' = set_value \<sigma> q (from_nat q') \<Longrightarrow> 
          q'_addr \<in> new_q_addr v \<sigma> (QStateM_map \<Q>)  \<Longrightarrow> vec_norm (vec_of_list (v \<sigma>)) = 1 \<Longrightarrow>
          \<turnstile> (Alloc q v, Normal (\<delta>,\<sigma>, \<Q>))\<rightarrow> (Skip, Normal (\<delta>, \<sigma>', \<Q> + Q_State.QStateM(\<vv>', QState (q'_addr,(v \<sigma>)) )))"
\<comment>\<open>Alloc will fail if the length of the initial value is not equal to the number of qubits allocated \<close>


 | Alloc_F:"length (v \<sigma>) \<le> 1 \<or>  vec_norm (vec_of_list (v \<sigma>)) \<noteq> 1 \<Longrightarrow>                    
          \<turnstile> (Alloc q v, Normal (\<delta>,\<sigma>,\<Q>)) \<rightarrow> (Skip, Fault)"

\<comment>\<open>the conditional, while, and seq statements follow the standard definitions\<close>

 | CondTrue:"\<sigma>\<in>b  \<Longrightarrow> \<turnstile> (IF b c1 c2, Normal (\<delta>,\<sigma>,\<Q>)) \<rightarrow> (c1, Normal (\<delta>,\<sigma>,\<Q>))"

 | CondFalse:"\<sigma>\<notin>b  \<Longrightarrow> \<turnstile> (IF b c1 c2, Normal (\<delta>,\<sigma>,\<Q>)) \<rightarrow> (c2, Normal (\<delta>,\<sigma>,\<Q>))"

 | WhileTrue: "\<sigma>\<in>b \<Longrightarrow> 
                \<turnstile> (While b c,Normal (\<delta>,\<sigma>,\<Q>)) \<rightarrow> (Seq c (While b c), Normal (\<delta>,\<sigma>,\<Q>))"

 | WhileFalse: "\<sigma>\<notin>b \<Longrightarrow> 
                 \<turnstile> (While b c, Normal (\<delta>,\<sigma>,\<Q>)) \<rightarrow> (Skip, Normal (\<delta>,\<sigma>,\<Q>))"

 | Seq:"\<lbrakk>\<turnstile> (C1, \<sigma>) \<rightarrow> (C1', \<sigma>')\<rbrakk> \<Longrightarrow> \<turnstile> (Seq C1 C2, \<sigma>) \<rightarrow> (Seq C1' C2, \<sigma>')"

| SeqSkip: "\<turnstile> (Seq Skip C2,\<sigma>) \<rightarrow> (C2, \<sigma>)"

\<comment>\<open>Dispose takes an expression from the stack to a natural number and removes those qubits
  from the quantum state if they are not entangled with the rest of qubits in the current
  Quantum state. The entanglement condition is that it is possible to find a vector \<qq>1 such that
  \<qq> =  \<qq>' +  \<qq>''\<close>

| Dispose: "  \<Q>' ## \<Q>'' \<Longrightarrow> \<Q> =  \<Q>' + \<Q>'' \<Longrightarrow> 
              QStateM_vars \<Q>' \<noteq> {} \<Longrightarrow> Zero \<Q>' \<Longrightarrow>
              QStateM_vars \<Q>' = (Q_domain_var (the (var_set q i \<sigma>)) (QStateM_map \<Q>')) \<Longrightarrow>                                      
              \<forall>e \<in> (the (var_set q i \<sigma>)). (QStateM_map \<Q>') e \<noteq> {} \<Longrightarrow>
             \<turnstile> (Dispose q i, Normal (\<delta>,\<sigma>,\<Q>)) \<rightarrow> (Skip, Normal (\<delta>,\<sigma>,  \<Q>''))"
\<comment>\<open>Dispose dispose will fail if it is not possible to find such states \<qq>',  \<qq>''\<close>


 | Dispose_F:  "(\<nexists>\<Q>' \<Q>''.  \<Q> = \<Q>' + \<Q>'' \<and> \<Q>' ## \<Q>'' \<and> QStateM_vars \<Q>' \<noteq> {} \<and> Zero \<Q>' \<and> 
               QStateM_vars \<Q>' = (Q_domain_var (the (var_set q i \<sigma>)) (QStateM_map \<Q>')) \<and>
               (\<forall>e \<in> (the (var_set q i \<sigma>)). (QStateM_map \<Q>') e \<noteq> {})) \<Longrightarrow>
               \<turnstile> (Dispose q i, Normal (\<delta>,\<sigma>,\<Q>)) \<rightarrow> (Skip, Fault)"

\<comment>\<open>Measure measures the value of the set of qubits given by q \<sigma> and it stores the result in 
  the stack variable v. Similar to allocate, we will require that the construct is well formed
 and that the type of v is a real number\<close>

 | Measure: "addr1 = \<Union>((QStateM_map \<Q>) ` (q \<sigma>)) \<Longrightarrow> \<forall>e \<in> (q \<sigma>). (QStateM_map \<Q>) e \<noteq> {} \<Longrightarrow>                      
            k \<in> {0..<2^(card addr1)} \<Longrightarrow>          
            (\<delta>k, \<Q>') = measure_vars k (q \<sigma>) \<Q> \<Longrightarrow>             
            \<delta>k > 0 \<Longrightarrow> \<delta>' = \<delta> * \<delta>k \<Longrightarrow> \<sigma>' = set_value \<sigma> v (from_nat k) \<Longrightarrow>
            \<turnstile> (Measure v q, Normal (\<delta>,\<sigma>,\<Q>)) \<rightarrow> (Skip, Normal (\<delta>',\<sigma>', \<Q>'))"
\<comment>\<open>Since Measure access to the values of the qubits given by q \<sigma> as QMod, 
  Measure will similarly fail if the set of qubits to be mesured does not
  belong to the set of allocated qubits\<close>

 | Measure_F: "\<exists>e. e \<in> q \<sigma> \<and> (QStateM_map \<Q>) e = {}  \<Longrightarrow> 
              \<turnstile> (Measure v q, Normal (\<delta>,\<sigma>,\<Q>)) \<rightarrow> (Skip, Fault)" 

| Fault_Prop:"\<lbrakk>c\<noteq>Skip; redex c = c\<rbrakk> \<Longrightarrow>  \<turnstile> (c, Fault) \<rightarrow> (Skip, Fault)"

thm step.intros

thm Fault_Prop

inductive_cases QStep_elim_cases [cases set]:
 "\<turnstile>(c,Fault) \<rightarrow>  t"  
  "\<turnstile>(Skip,s) \<rightarrow>  t"
  "\<turnstile>(SMod f,s) \<rightarrow>  t"
  "\<turnstile>(QMod m q,s) \<rightarrow>  t"
  "\<turnstile>(Seq c1 c2,s) \<rightarrow> t"
  "\<turnstile>(While b c,s) \<rightarrow>  t"
  "\<turnstile>(IF b c1 c2,s) \<rightarrow>  t"
  "\<turnstile>(Measure v q,s) \<rightarrow>  t"
  "\<turnstile>(Alloc v  e,s) \<rightarrow>  t"
  "\<turnstile>(Dispose q i,s) \<rightarrow>  t"

inductive_cases QStep_Normal_elim_cases [cases set]:
 "\<turnstile>(c,Fault) \<rightarrow>  t"  
  "\<turnstile>(Skip,Normal s) \<rightarrow>  t"
  "\<turnstile>(SMod f,Normal s) \<rightarrow>  t"
  "\<turnstile>(QMod m q,Normal s) \<rightarrow>  t"
  "\<turnstile>(Seq c1 c2,Normal s) \<rightarrow>  t"
  "\<turnstile>(While b c1,Normal s) \<rightarrow>  t"
  "\<turnstile>(IF b c1 c2,Normal s) \<rightarrow>  t"
  "\<turnstile>(Measure v q,Normal s) \<rightarrow>  t"
  "\<turnstile>(Alloc v  e,Normal s) \<rightarrow>  t"
  "\<turnstile>(Dispose q v,Normal s) \<rightarrow>  t"

inductive_cases QStep_Fault_elim_cases [cases set]:
 "\<turnstile>(c,Fault) \<rightarrow>  (c',Fault)"  
  "\<turnstile>(Skip,Normal s) \<rightarrow>  (c', Fault)"
  "\<turnstile>(SMod f,Normal s) \<rightarrow>  (c', Fault)"
  "\<turnstile>(QMod m q,Normal s) \<rightarrow> (c', Fault)"
  "\<turnstile>(Seq c1 c2,Normal s) \<rightarrow> (c', Fault)"
  "\<turnstile>(While b c1,Normal s) \<rightarrow> (c', Fault)"
  "\<turnstile>(IF b c1 c2,Normal s) \<rightarrow>  (c', Fault)"
  "\<turnstile>(Measure v q,Normal s) \<rightarrow>  (c', Fault)"
  "\<turnstile>(Alloc v  e,Normal s) \<rightarrow>  (c', Fault)"
  "\<turnstile>(Dispose q v,Normal s) \<rightarrow>  (c', Fault)"

lemmas step_induct = step.induct [of "(c,s)" "(c',s')", split_format (complete), OF vars_axioms, case_names
StackMod QMod QMod_F Alloc Alloc_F CondTrue CondFalse WhileTrue WhileFalse Seq SeqSkip Dispose
Dispose_F Measure Measure_F Fault_Prop,induct set] 



definition final:: "('v,'s) QConf \<Rightarrow> bool" where
"final cfg \<equiv> (fst cfg=Skip)"

abbreviation
 "step_rtrancl" :: "[('v,'s) QConf,('v,'s) QConf] \<Rightarrow> bool"
                                ("\<turnstile> (_ \<rightarrow>\<^sup>*/ _)" [81,81] 100)
 where
  "\<turnstile>cf0 \<rightarrow>\<^sup>* cf1 \<equiv> (CONST step)\<^sup>*\<^sup>* cf0 cf1"

abbreviation
 "step_trancl" :: "[('v,'s) QConf,('v,'s) QConf] \<Rightarrow> bool"
                                ("\<turnstile> (_ \<rightarrow>\<^sup>+/ _)" [81,81] 100)
 where
  "\<turnstile>cf0 \<rightarrow>\<^sup>+ cf1 \<equiv> (CONST step)\<^sup>+\<^sup>+ cf0 cf1"


lemma redex_not_Seq: "redex c = Seq c1 c2 \<Longrightarrow> P"
  apply (induct c)
  apply auto
  done

lemma no_step_final:
  assumes step: "\<turnstile>(c,s) \<rightarrow> (c',s')"
  shows "final (c,s) \<Longrightarrow> P"
  using step
  by (induct, auto simp add: final_def)

thm no_step_final

lemma no_step_final':
  assumes step: "\<turnstile>cfg \<rightarrow> cfg'"
  shows "final cfg \<Longrightarrow> P"
using step by (cases cfg', cases cfg) (auto intro: no_step_final )


lemma step_Fault': 
  assumes step: "\<turnstile> (c,s) \<rightarrow>  (c',s')" and s1:"snd (c,s) = Fault"
  shows "snd (c',s') = Fault"
  using step s1 by (induct, auto)

lemma step_Fault: 
  assumes step: "\<turnstile> (c,s) \<rightarrow>  (c',s')"
  shows "s = Fault \<Longrightarrow> s' = Fault"
  using step_Fault'[OF step] by auto

lemma SeqSteps:
  assumes steps: "\<turnstile>cfg\<^sub>1\<rightarrow>\<^sup>* cfg\<^sub>2"
  shows "\<And> c\<^sub>1 s c\<^sub>1' s'. \<lbrakk>cfg\<^sub>1 = (c\<^sub>1,s);cfg\<^sub>2=(c\<^sub>1',s')\<rbrakk>
          \<Longrightarrow> \<turnstile>(Seq c\<^sub>1 c\<^sub>2,s) \<rightarrow>\<^sup>* (Seq c\<^sub>1' c\<^sub>2, s')"
using steps
proof (induct rule: converse_rtranclp_induct [case_names Refl Trans])
  case Refl
  thus ?case
    by simp
next
  case (Trans cfg\<^sub>1 cfg'')
  have step: "\<turnstile> cfg\<^sub>1 \<rightarrow> cfg''" by fact
  have steps: "\<turnstile> cfg'' \<rightarrow>\<^sup>* cfg\<^sub>2" by fact
  have cfg\<^sub>1: "cfg\<^sub>1 = (c\<^sub>1, s)" and cfg\<^sub>2: "cfg\<^sub>2 = (c\<^sub>1', s')"  by fact+
  obtain c\<^sub>1'' s'' where cfg'': "cfg''=(c\<^sub>1'',s'')"
    by (cases cfg'') auto
  from step cfg\<^sub>1 cfg''
  have "\<turnstile> (c\<^sub>1,s) \<rightarrow> (c\<^sub>1'',s'')"
    by simp
  hence "\<turnstile> (Seq c\<^sub>1 c\<^sub>2,s) \<rightarrow> (Seq c\<^sub>1'' c\<^sub>2,s'')"
    by (rule step.Seq)
  also from Trans.hyps (3) [OF cfg'' cfg\<^sub>2]
  have "\<turnstile> (Seq c\<^sub>1'' c\<^sub>2, s'') \<rightarrow>\<^sup>* (Seq c\<^sub>1' c\<^sub>2, s')" .
  finally show ?case .
qed

lemma steps_Fault: "\<turnstile> (c, Fault) \<rightarrow>\<^sup>* (Skip, Fault )"
proof (induct c)
  case (Seq c\<^sub>1 c\<^sub>2)
  have steps_c\<^sub>1: "\<turnstile> (c\<^sub>1, Fault) \<rightarrow>\<^sup>* (Skip, Fault)" by fact
  have steps_c\<^sub>2: "\<turnstile> (c\<^sub>2, Fault) \<rightarrow>\<^sup>* (Skip, Fault)" by fact
  from SeqSteps [OF steps_c\<^sub>1 refl refl]
  have "\<turnstile> (Seq c\<^sub>1 c\<^sub>2, Fault) \<rightarrow>\<^sup>* (Seq Skip c\<^sub>2, Fault)".
  also
  have "\<turnstile> (Seq Skip c\<^sub>2, Fault) \<rightarrow> (c\<^sub>2, Fault)" by (rule SeqSkip)
  also note steps_c\<^sub>2
  finally show ?case by simp
qed (fastforce intro: step.intros)+

lemma step_Fault_prop:
  assumes step: "\<turnstile> (c, s) \<rightarrow> (c', s')"
  shows "s=Fault  \<Longrightarrow> s'=Fault"
  using step step_Fault  by blast 

lemma steps_Fault_prop:
  assumes step: "\<turnstile> (c, s) \<rightarrow>\<^sup>* (c', s')"
  shows "s=Fault  \<Longrightarrow> s'=Fault "
  using step
proof (induct rule: converse_rtranclp_induct2 [case_names Refl Trans])
  case Refl thus ?case by simp
next
  case (Trans c s c'' s'')
  thus ?case
    by (auto intro: step_Fault)
qed

(* ************************************************************************ *)
subsection \<open>Equivalence between Small-Step and Big-Step Semantics\<close>
(* ************************************************************************ *)

theorem exec_impl_steps:
  assumes exec: "\<turnstile>\<langle>c,s\<rangle> \<Rightarrow> t"
  shows "\<exists>c' t'. \<turnstile>(c,s) \<rightarrow>\<^sup>* (c',t') \<and> c'=Skip \<and> t'=t"
using exec
proof (induct) 
  case (CondTrue \<sigma> b c1 \<delta> \<Q> \<sigma>' c2)
  then show ?case
    by (meson converse_rtranclp_into_rtranclp step.CondTrue)
next
  case (CondFalse \<sigma> b c2 \<delta> \<Q> \<sigma>' c1)
  then show ?case by (meson converse_rtranclp_into_rtranclp step.CondFalse)
next
  case (WhileTrue \<sigma> b c \<delta> \<Q> \<sigma>' \<sigma>'')
  then show ?case 
    by (meson SeqSkip SeqSteps converse_rtranclp_into_rtranclp rtranclp_trans step.WhileTrue) 
next
  case (WhileFalse \<sigma> b c \<delta> \<Q>)
  then show ?case
    by (meson r_into_rtranclp step.WhileFalse)
next
  case (Seq C1 \<sigma> \<sigma>' C2 \<sigma>'')
  then show ?case
    by (meson SeqSkip SeqSteps rtranclp.rtrancl_into_rtrancl rtranclp_trans) 
next
  case (Fault_Prop C)
  then show ?case
    using steps_Fault by blast 
qed (auto simp add: r_into_rtranclp step.intros)

corollary exec_impl_steps_Normal:
  assumes exec: "\<turnstile>\<langle>c,s\<rangle> \<Rightarrow> Normal t"
  shows "\<turnstile>(c,s) \<rightarrow>\<^sup>* (Skip, Normal t)"
using exec_impl_steps [OF exec]
by auto

corollary exec_impl_steps_Fault:
  assumes exec: "\<turnstile>\<langle>c,s\<rangle> \<Rightarrow> Fault"
  shows "\<turnstile>(c,s) \<rightarrow>\<^sup>* (Skip, Fault)"
using exec_impl_steps [OF exec]
by auto

(* lemma step_Fault_end:
  assumes step: "\<turnstile> (c\<^sub>1, s) \<rightarrow> (c\<^sub>1', s')"
  shows "s'=Fault \<Longrightarrow> s=Fault" sorry
(* proof (induct rule: step_induct[OF step],auto) 
  
end *) *)


lemma step_extend:
  assumes step: "\<turnstile>(c,s) \<rightarrow> (c', s')"
  shows "\<And>t. \<turnstile>\<langle>c',s'\<rangle> \<Rightarrow> t \<Longrightarrow> \<turnstile>\<langle>c,s\<rangle> \<Rightarrow> t"
  using step
proof (induct)
  case (StackMod f \<delta> \<sigma> \<Q>)
  then show ?case 
    using QExec.StackMod QSemanticsBig.vars.QExec_Normal_elim_cases(2) vars_axioms by blast 
next
  case (QMod q \<sigma> \<Q> M \<Q>' \<delta>)
  then show ?case
    by (metis QExec.QMod QSemanticsBig.vars.QExec_Normal_elim_cases(2) vars_axioms) 
next
  case (QMod_F q \<sigma> \<Q> M \<delta>)
  then show ?case
    by (metis QExec.QMod_F exec_Fault_end) 
next
  case (Alloc q' \<Q> v \<sigma> \<vv>' q'_addr \<sigma>' q \<delta>)
  then show ?case
    by (smt (verit, best) QSemanticsBig.vars.QExec_Normal_elim_cases(2) vars.QExec.Alloc vars_axioms) 
next
  case (Alloc_F v \<sigma> q \<delta> \<Q>)
  then show ?case
    using QExec.Alloc_F exec_Fault_end by blast 
next
  case (CondTrue \<sigma> b c1 c2 \<delta> \<Q>)
  then show ?case
    using QExec.CondTrue by auto 
next
  case (CondFalse \<sigma> b c1 c2 \<delta> \<Q>)
  then show ?case
    using QExec.CondFalse by blast 
next
  case (WhileTrue \<sigma> b c \<delta> \<Q>)
  then show ?case using QExec.WhileTrue  vars_axioms
    by (meson QSemanticsBig.vars.QExec_Normal_elim_cases(5))
    
next
  case (WhileFalse \<sigma> b c \<delta> \<Q>)
  then show ?case
    by (metis QExec.WhileFalse QSemanticsBig.vars.QExec_Normal_elim_cases(2) vars_axioms) 
next
  case (Seq C1 \<sigma> C1' \<sigma>' C2)
  then show ?case
    by (smt (verit, ccfv_threshold) QExec.Fault_Prop QExec.Seq QSemanticsBig.vars.QExec_elim_cases(5) XQState.exhaust step_Fault_prop vars_axioms)
next
  case (SeqSkip C2 \<sigma>)
  then show ?case
    by (metis QExec.Fault_Prop QExec.Seq Skip XQState.exhaust exec_Fault_end) 
next
  case (Dispose \<Q>' \<Q>'' \<Q> q i \<sigma> \<delta>)
  then show ?case
    by (metis QExec.Dispose QSemanticsBig.vars.QExec_Normal_elim_cases(2) vars_axioms) 
next
  case (Dispose_F \<Q> q i \<sigma> \<delta>)
  then show ?case
    using QExec.Dispose_F exec_Fault_end by blast 
next
  case (Measure addr1 \<Q> q \<sigma> k \<delta>k \<Q>' \<delta>' \<delta> \<sigma>' v)
  then show ?case
    by (metis (mono_tags, lifting) QSemanticsBig.vars.QExec_Normal_elim_cases(2) vars.QExec.Measure vars_axioms) 
next
  case (Measure_F q \<sigma> \<Q> v \<delta>)
  then show ?case
    using QExec.Measure_F exec_Fault_end by blast 
next
  case (Fault_Prop c)
  then show ?case
    using QExec.Fault_Prop exec_Fault_end by blast 
qed


theorem steps_Skip_impl_exec:
  assumes steps: "\<turnstile>(c,s) \<rightarrow>\<^sup>* (Skip,t)"
  shows "\<turnstile>\<langle>c,s\<rangle> \<Rightarrow> t"
using steps
proof (induct rule: converse_rtranclp_induct2 [case_names Refl Trans])
  case Refl thus ?case
    by (cases t) (auto intro: QExec.intros)
next
  case (Trans c s c' s')
  have "\<turnstile> (c, s) \<rightarrow> (c', s')" and "\<turnstile> \<langle>c',s'\<rangle> \<Rightarrow> t" by fact+
  thus ?case
    by (rule step_extend)
qed

(*lemma not_stuck:"\<turnstile>\<langle>c,Normal (p, \<sigma>, Q)\<rangle> \<Rightarrow> Fault \<or> 
                 (\<exists> p' \<sigma>' Q'. \<turnstile>\<langle>c,Normal (p, \<sigma>, Q)\<rangle> \<Rightarrow> Normal (p',\<sigma>',Q'))"
proof(induct c arbitrary: p \<sigma> Q)
  case Skip
  then show ?case
    using QExec.Skip by blast 
next
  case (SMod x)
  then show ?case
    by (meson QExec.StackMod) 
next
  case (QMod x1 x2a)
  then show ?case
    by (metis vars.QExec.intros(3) vars.QExec.intros(4) vars_axioms) 
next
  case (IF x1 c1 c2)
  then show ?case
    by (metis QExec.CondFalse QExec.CondTrue) 
next
  case (While x1 c)
  then show ?case sorry
next
  case (Seq c1 c2)
  then show ?case
    using QExec.Fault_Prop QExec.Seq by blast 
next
  case (Measure x1 x2a)
  then show ?case sorry
next
  case (Alloc x1 x2a)
  then show ?case sorry
next
  case (Dispose x1 x2a)
  then show ?case
    by (metis vars.QExec.intros(12) vars.QExec.intros(13) vars_axioms) 
qed
*)
fun while_unfold::"nat \<Rightarrow> ('v, 's) com \<Rightarrow> 's assn \<Rightarrow> 's XQState \<Rightarrow> bool"
  where "while_unfold 0 c b s = (s = Fault \<or> (\<exists>p \<sigma> Q. s = Normal (p, \<sigma>, Q) \<and> \<sigma>\<notin>b))" 
  | "while_unfold (Suc n) c b s = 
       (\<exists>p \<sigma> Q s'. s = Normal (p, \<sigma>, Q) \<and> \<sigma>\<in>b \<and> \<turnstile>\<langle>c,Normal (p, \<sigma>, Q)\<rangle> \<Rightarrow> s' \<and> while_unfold n c b s')"

inductive QExec\<^sub>n::"nat \<Rightarrow> ('v, 's) com \<Rightarrow> 's assn \<Rightarrow> 's XQState \<Rightarrow> 's XQState \<Rightarrow> bool"
  where "(s = Normal (p,\<sigma>,Q) \<and> \<sigma>\<notin>b) \<or> s = Fault \<Longrightarrow>  QExec\<^sub>n 0 c b s s"
        | "s = Normal (p, \<sigma>, Q)  \<Longrightarrow> \<sigma>\<in>b \<Longrightarrow> \<turnstile>\<langle>c,s\<rangle> \<Rightarrow> s' \<Longrightarrow> QExec\<^sub>n n c b s' s'' \<Longrightarrow> 
         QExec\<^sub>n (Suc n) c b s s''" 

lemma QExec_QExec_n_aux:
  assumes a0:"\<turnstile>\<langle>v,s\<rangle> \<Rightarrow> s'"
  shows "v = While b c \<Longrightarrow> s1 = s \<Longrightarrow> s1' = s' \<Longrightarrow> \<exists>n. QExec\<^sub>n n c b s1 s1'"
  using a0 
proof(induct arbitrary: s1 s1')
  case (WhileTrue \<sigma> b c \<delta> \<Q> \<sigma>' \<sigma>'')
  have "\<exists>n. QExec\<^sub>n n c b \<sigma>'  \<sigma>''"
    using WhileTrue.hyps(5) WhileTrue.prems(1) by force
  then show ?case
    using QExec\<^sub>n.intros(2) WhileTrue.hyps(1) WhileTrue.hyps(2) WhileTrue.prems(1) WhileTrue.prems(2) WhileTrue.prems(3) by blast 
next
  case (WhileFalse \<sigma> b c \<delta> \<Q>)
  then show ?case
    using QExec\<^sub>n.intros(1) by blast 
next
  case (Fault_Prop C)
  then show ?case
    using QExec\<^sub>n.intros(1) by blast 
qed(auto)


lemma QExec_QExec_n: assumes a0:"\<turnstile>\<langle>While b c,s\<rangle> \<Rightarrow> s'" 
  shows "\<exists>n. QExec\<^sub>n n c b s s'"
  using QExec_QExec_n_aux[OF a0] by auto

lemma QExec_n_QExec: 
  assumes a0: "QExec\<^sub>n n c b s s'"
  shows "\<turnstile>\<langle>While b c,s\<rangle> \<Rightarrow> s'"
  using a0
proof(induct n arbitrary: s s')
  case 0
  then have "s = s'"
    using QExec\<^sub>n.cases by blast
  { assume "s = Fault"
    then have ?case
      using QExec.Fault_Prop \<open>s = s'\<close> by presburger 
  } 
  moreover{
    fix p \<sigma> Q
    assume "s = Normal (p, \<sigma>, Q)"
    then have ?case
      by (metis "0" QExec.WhileFalse QExec\<^sub>n.simps calculation old.nat.distinct(2))
  }
  ultimately show ?case
    by (metis "0" QExec\<^sub>n.simps) 
next
  case (Suc n)
  then obtain s'' p \<sigma> Q where 
   "s = Normal (p, \<sigma>, Q)" and  "\<sigma>\<in>b" and "\<turnstile>\<langle>c,s\<rangle> \<Rightarrow> s''" and "QExec\<^sub>n n c b s'' s'"
    by (smt (verit, ccfv_SIG) QExec\<^sub>n.simps nat.inject old.nat.distinct(2))
  then show ?case
    using QExec.WhileTrue Suc.hyps by blast 
qed

theorem QExec_n_eq_QExec: 
  shows "(\<exists>n. QExec\<^sub>n n c b s s') = \<turnstile>\<langle>While b c,s\<rangle> \<Rightarrow> s'"
  using QExec_n_QExec QExec_QExec_n by auto


end

end

