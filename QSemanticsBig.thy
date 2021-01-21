(* Title:     Quantum-Semantics/QSemantics.thy
   Author:    David Sanan, Nanyang Technological University 
   Copyright   2020
   License:     BSD
*)

theory QSemanticsBig
  imports QSyntax  
begin           

subsection \<open>Syntax\<close>

text \<open>Semantics for quantum programs\<close>

(* m = partial_state2.ptensor_mat (dims_heap \<vv>) (q \<sigma>) ((Q_domain \<vv>)-(q \<sigma>)) (M::complex mat) (1\<^sub>m (card ((Q_domain \<vv>) - (q \<sigma>))))*)
(* abbreviation "tensor_vec \<equiv> partial_state2.ptensor_vec" *)

definition
  unit_vecl :: "nat \<Rightarrow> nat \<Rightarrow> complex list"
  where "unit_vecl n i = list_of_vec (unit_vec n i)"

definition matrix_sep :: "nat set \<Rightarrow> qstate \<Rightarrow> complex mat \<Rightarrow> qstate" 
  where "matrix_sep sep_vars q M \<equiv>
           let qs = snd q in
           let var_d = QState_vars qs in 
           let var_r = var_d - sep_vars in
           let v = QState_vector qs in           
           let m = partial_state2.ptensor_mat sep_vars var_r
                                        (M::complex mat) (1\<^sub>m (2^(card var_r)))  in           
             (fst q, QState (var_d, list_of_vec (m *\<^sub>v v)))
        "

definition measure_vars1::"nat \<Rightarrow>  nat set \<Rightarrow> qstate  \<Rightarrow> (real \<times> qstate)"
  where "measure_vars1 k  sep_vars q \<equiv>
   let qs = snd q in
   let vars_dom = QState_vars qs in
    let v =   QState_vector qs in
    let vars= (vars_dom - sep_vars) in    
    let mk = partial_state2.ptensor_mat  vars_dom vars (1\<^sub>k (2^(card vars_dom))) (1\<^sub>m (2^(card vars))) in
    let qn' =  mk  *\<^sub>v v in 
    let \<delta>k =  Re (((mat_adjoint (mat_of_rows (dim_vec v) [v]) *\<^sub>v qn') $ 0) div vec_norm qn') in    
    let qnprod = list_of_vec (((sqrt \<delta>k)::complex) \<cdot>\<^sub>v qn') in
       (\<delta>k, (fst q, QState (vars_dom, qnprod)))" 

definition measure_vars::"nat \<Rightarrow>  nat set \<Rightarrow> qstate  \<Rightarrow> (real \<times> qstate)"
  where "measure_vars k  sep_vars q \<equiv>
   let qs = snd q in
   let vars_dom = QState_vars qs in
    let v =   QState_vector qs in
    let vars= (vars_dom - sep_vars) in        
    let mk = partial_state2.ptensor_mat  sep_vars vars (1\<^sub>k (2^(card sep_vars))) (1\<^sub>m (2^(card vars))) in
    let v' =  mk  *\<^sub>v v in 
    let \<delta>k =  Re ((vec_norm v')^2 div (vec_norm v)^2) in    
    let qnprod = list_of_vec (((sqrt \<delta>k)::complex) \<cdot>\<^sub>v v') in
       (\<delta>k, (fst q, QState (vars_dom, qnprod)))" 

context vars
begin


inductive QExec::"('v, 's) com \<Rightarrow> 's XQState \<Rightarrow> 's XQState \<Rightarrow> bool" 
  ("\<turnstile> \<langle>_,_\<rangle> \<Rightarrow> _"  [20,98,98] 89)  
  where 
  Skip : "\<turnstile>  \<langle>Skip, Normal \<sigma>\<rangle> \<Rightarrow> Normal \<sigma>" 
\<comment>\<open>SMod  modifies the stack of non-qubits variables \<sigma> with f \<sigma>, where f is a 
  function modifying the stack\<close>
 | StackMod: "\<turnstile> \<langle>SMod f, Normal (\<delta>,\<sigma>,\<Q>)\<rangle> \<Rightarrow>  Normal (\<delta>,f \<sigma>,\<Q>)"

\<comment>\<open>QMod modifies the set of qubits of the Quantum State given by q \<sigma> with the 
  transformation matrix M, any qubit not included in q \<sigma> remains the same\<close>

 | QMod:"(q (\<sigma>,\<vv>)) \<subseteq> (QState_vars \<qq>) \<Longrightarrow> 
         \<qq>' = matrix_sep (q (\<sigma>,\<vv>)) (\<vv>,\<qq>) m \<Longrightarrow>
         \<turnstile> \<langle>QMod M q, Normal (\<delta>,\<sigma>,(\<vv>,\<qq>))\<rangle> \<Rightarrow> Normal (\<delta>, \<sigma>, \<qq>')"

\<comment>\<open>QMod fails if the set of qubits to be modified is not included in the quantum state\<close>
 | QMod_F:"\<not> ((q (\<sigma>,\<vv>)) \<subseteq> (QState_vars \<qq>)) \<Longrightarrow>          
          \<turnstile> \<langle>QMod M q, Normal (\<delta>,\<sigma>,(\<vv>,\<qq>))\<rangle> \<Rightarrow> Fault"

\<comment>\<open>Alloc takes a normal variable "q" representing the variable where the index to the qubits is store
   an function e from the state \<sigma> to a natural number representing the number of qubits to allocate
  and an initialization value for the allocated qubits 


  We will require that a program is well formed, meaning that the types are correct.
  A call to Alloc is well formed if the type of q is a natural number\<close>

 | Alloc:"q' \<notin> (dom_q_vars \<vv>) \<Longrightarrow> q'_addr \<in> new_q_addr e (\<delta>,\<sigma>,(\<vv>,\<qq>)) \<Longrightarrow> e \<sigma> \<noteq> 0 \<Longrightarrow> 
          \<vv>' = \<vv>(q' := q'_addr)  \<Longrightarrow> length (v \<sigma>) = (e \<sigma>) \<Longrightarrow> \<sigma>' = set_value \<sigma> q (from_nat q') \<Longrightarrow>                    
          \<turnstile> \<langle>Alloc q e v, Normal (\<delta>,\<sigma>,(\<vv>,\<qq>))\<rangle> \<Rightarrow> Normal (\<delta>, \<sigma>',(\<vv>',\<qq> + QState (q'_addr,(v \<sigma>)) ))"

\<comment>\<open>Alloc will fail if the length of the initial value is not equal to the number of qubits allocated \<close>


 | Alloc_F:"length (v \<sigma>) \<noteq> (e \<sigma>) \<or> e \<sigma> = 0 \<Longrightarrow>                    
          \<turnstile> \<langle>Alloc q e v, Normal (\<delta>,\<sigma>,(\<vv>,\<qq>))\<rangle> \<Rightarrow> Fault"

\<comment>\<open>the conditional, while, and seq statements follow the standard definitions\<close>

 | CondTrue:"\<sigma>\<in>b \<Longrightarrow>  \<turnstile> \<langle>c1, Normal (\<delta>,\<sigma>,\<Q>)\<rangle> \<Rightarrow> \<sigma>' \<Longrightarrow> \<turnstile> \<langle>IF b c1 c2, Normal  (\<delta>,\<sigma>,\<Q>)\<rangle> \<Rightarrow> \<sigma>'"

| CondFalse:"\<sigma>\<notin>b  \<Longrightarrow>  \<turnstile> \<langle>c2, Normal (\<delta>,\<sigma>,\<Q>)\<rangle> \<Rightarrow> \<sigma>' \<Longrightarrow> 
           \<turnstile> \<langle>IF b c1 c2, Normal (\<delta>,\<sigma>,\<Q>)\<rangle> \<Rightarrow> \<sigma>'"

 | WhileTrue: "\<sigma>\<in>b \<Longrightarrow> \<turnstile> \<langle>c, Normal (\<delta>,\<sigma>,\<Q>)\<rangle> \<Rightarrow> \<sigma>' \<Longrightarrow> \<turnstile> \<langle>While b c,\<sigma>'\<rangle> \<Rightarrow>  \<sigma>'' \<Longrightarrow>
                \<turnstile> \<langle>While b c,Normal (\<delta>,\<sigma>,\<Q>)\<rangle> \<Rightarrow> \<sigma>''"

 | WhileFalse: "\<sigma>\<notin>b \<Longrightarrow> 
                 \<turnstile> \<langle>While b c,Normal  (\<delta>,\<sigma>,\<Q>)\<rangle> \<Rightarrow> Normal  (\<delta>,\<sigma>,\<Q>)"

 | Seq:"\<lbrakk>\<turnstile> \<langle>C1, Normal \<sigma>\<rangle> \<Rightarrow> \<sigma>'; \<turnstile> \<langle>C2, \<sigma>'\<rangle> \<Rightarrow> \<sigma>'' \<rbrakk> \<Longrightarrow> \<turnstile> \<langle>Seq C1 C2, Normal \<sigma>\<rangle> \<Rightarrow> \<sigma>''"


\<comment>\<open>Dispose takes an expression from the stack to a natural number and removes those qubits
  from the quantum state if they are not entangled with the rest of qubits in the current
  Quantum state. The entanglement condition is that it is possible to find a vector \<qq>1 such that
  \<qq> =  \<qq>' +  \<qq>''\<close>

 | Dispose: "\<vv> (q \<sigma>) \<noteq> {} \<Longrightarrow> \<vv>' = \<vv>((q \<sigma>):={}) \<Longrightarrow> \<qq>' ## \<qq>''  \<Longrightarrow> 
            \<vv> (q \<sigma>) = QState_vars \<qq>'' \<Longrightarrow> \<qq> =   \<qq>' +  \<qq>'' \<Longrightarrow> 
            n = vec_norm (QState_vector \<qq>'') \<Longrightarrow>                       
             \<turnstile> \<langle>Dispose q, Normal (\<delta>,\<sigma>,(\<vv>,\<qq>))\<rangle> \<Rightarrow> Normal (\<delta>,\<sigma>,(\<vv>',n \<cdot>\<^sub>q \<qq>'))"                                  

\<comment>\<open>Dispose dispose will fail if it is not possible to find such states \<qq>',  \<qq>''\<close>


 | Dispose_F: "\<nexists>\<qq>' \<qq>''. \<vv> (q \<sigma>) \<noteq> {} \<and> \<vv> (q \<sigma>) = QState_vars \<qq>'' \<and> 
               \<qq> =   \<qq>' +  \<qq>'' \<and> \<qq>' ## \<qq>'' \<Longrightarrow>
               \<turnstile> \<langle>Dispose q, Normal (\<delta>,\<sigma>,(\<vv>,\<qq>))\<rangle> \<Rightarrow> Fault"

\<comment>\<open>Measure measures the value of the set of qubits given by q \<sigma> and it stores the result in 
  the stack variable v. Similar to allocate, we will require that the construct is well formed
 and that the type of v is a real number\<close>

 | Measure: "q (\<sigma>,\<vv>) = (QState_vars \<qq>1) \<Longrightarrow> k \<in> {0.. 2^(card (q (\<sigma>,\<vv>)))} \<Longrightarrow>
            (\<delta>k, (\<vv>',\<qq>')) = measure_vars k (q (\<sigma>,\<vv>)) (\<vv>,\<qq>) \<Longrightarrow> \<qq> =   \<qq>1 +  \<qq>2 \<and> \<qq>1 ## \<qq>2 \<Longrightarrow>            
            \<delta>k > 0 \<Longrightarrow> \<delta>' = \<delta> * \<delta>k \<Longrightarrow> \<sigma>' = set_value \<sigma> v (from_nat k) \<Longrightarrow>
            \<turnstile> \<langle>Measure v q, Normal (\<delta>,\<sigma>,(\<vv>,\<qq>))\<rangle> \<Rightarrow> Normal (\<delta>',\<sigma>',(\<vv>',\<qq>'))" 

\<comment>\<open>Since Measure access to the values of the qubits given by q \<sigma> as QMod, 
  Measure will similarly fail if the set of qubits to be mesured does not
  belong to the set of allocated qubits\<close>

 | Measure_F: "\<not> (q (\<sigma>,\<vv>) \<subseteq> (QState_vars \<qq>)) \<Longrightarrow>  
              \<turnstile> \<langle>Measure v q, Normal (\<delta>,\<sigma>,(\<vv>,\<qq>))\<rangle> \<Rightarrow> Fault" 

| Fault_Prop:"\<turnstile> \<langle>C, Fault\<rangle> \<Rightarrow> Fault"



inductive_cases QExec_elim_cases [cases set]:
 "\<turnstile>\<langle>c,Fault\<rangle> \<Rightarrow>  t"  
  "\<turnstile>\<langle>Skip,s\<rangle> \<Rightarrow>  t"
  "\<turnstile>\<langle>SMod f,s\<rangle> \<Rightarrow>  t"
  "\<turnstile>\<langle>QMod m q,s\<rangle> \<Rightarrow>  t"
  "\<turnstile>\<langle>Seq c1 c2,s\<rangle> \<Rightarrow>  t"
  "\<turnstile>\<langle>While b c,s\<rangle> \<Rightarrow>  t"
  "\<turnstile>\<langle>IF b c1 c2,s\<rangle> \<Rightarrow>  t"
  "\<turnstile>\<langle>Measure v q,s\<rangle> \<Rightarrow>  t"
  "\<turnstile>\<langle>Alloc v q e,s\<rangle> \<Rightarrow>  t"
  "\<turnstile>\<langle>Dispose q,s\<rangle> \<Rightarrow>  t"

inductive_cases QExec_Normal_elim_cases [cases set]:
 "\<turnstile>\<langle>c,Fault\<rangle> \<Rightarrow>  t"  
  "\<turnstile>\<langle>Skip,Normal s\<rangle> \<Rightarrow>  t"
  "\<turnstile>\<langle>SMod f,Normal s\<rangle> \<Rightarrow>  t"
  "\<turnstile>\<langle>QMod m q,Normal s\<rangle> \<Rightarrow>  t"
  "\<turnstile>\<langle>Seq c1 c2,Normal s\<rangle> \<Rightarrow>  t"
  "\<turnstile>\<langle>While b c1,Normal s\<rangle> \<Rightarrow>  t"
  "\<turnstile>\<langle>IF b c1 c2,Normal s\<rangle> \<Rightarrow>  t"
  "\<turnstile>\<langle>Measure v q,Normal s\<rangle> \<Rightarrow>  t"
  "\<turnstile>\<langle>Alloc v q e,Normal s\<rangle> \<Rightarrow>  t"
  "\<turnstile>\<langle>Dispose q,Normal s\<rangle> \<Rightarrow>  t"

primrec modify_locals :: "('v, 's) com  \<Rightarrow> 'v set" where 
  "modify_locals  Skip = {}"
| "modify_locals (SMod f) = {v. modify_v f v = True}"
| "modify_locals (QMod _ _) = {}"
| "modify_locals (IF b c1 c2) = modify_locals c1 \<union> modify_locals c2"
| "modify_locals (While b c) = modify_locals c"
| "modify_locals (Seq c1 c2) = modify_locals c1 \<union> modify_locals c2"
| "modify_locals (Measure v e) = {v}"
| "modify_locals (Alloc v e val) = {v}"
| "modify_locals (Dispose e) = {}"

thm QExec_Normal_elim_cases

end 

end

