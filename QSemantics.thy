(* Title:     Quantum-Semantics/QSemantics.thy
   Author:    David Sanan, Nanyang Technological University 
   Copyright   2020
   License:     BSD
*)

theory QSemantics
  imports QSyntax vars 
begin

subsection \<open>Syntax\<close>

text \<open>Semantics for quantum programs\<close>

primrec redex:: "('a,'b,'s) com \<Rightarrow> ('a,'b,'s) com"
where
"redex Skip = Skip" |
"redex (SMod f) = (SMod f)" |
"redex (QMod m e) = (QMod m e)" |
"redex (Seq c\<^sub>1 c\<^sub>2) = redex c\<^sub>1" |
"redex (IF b c\<^sub>1 c\<^sub>2) = (IF b c\<^sub>1 c\<^sub>2)" |
"redex (While b c) = (While b c)" |
"redex (Measure v q) = Measure v q" |
"redex (Alloc v e l) = Alloc v e l" |
"redex (Dispose e) = Dispose e"



(* m = partial_state2.ptensor_mat (dims_heap \<vv>) (q \<sigma>) ((Q_domain \<vv>)-(q \<sigma>)) (M::complex mat) (1\<^sub>m (card ((Q_domain \<vv>) - (q \<sigma>))))*)
(* abbreviation "tensor_vec \<equiv> partial_state2.ptensor_vec" *)


definition matrix_sep :: "nat set \<Rightarrow> (complex) QState \<Rightarrow> complex mat \<Rightarrow> complex vec" 
  where "matrix_sep sep_vars qs M \<equiv>
           let var_d = QState_vars qs in 
           let var_r = var_d - sep_vars in
           let v = QState_vector qs in           
           let m = partial_state2.ptensor_mat sep_vars var_r
                                        (M::complex mat) (1\<^sub>m (2^(card var_r)))  in           
               (m *\<^sub>v v)
        "

(* definition alloc_vars :: "'q::linorder set \<Rightarrow> ('q, complex) QState \<Rightarrow> complex vec \<Rightarrow> complex vec"
  where "alloc_vars sep_vars qs v \<equiv>            
           partial_state2.ptensor_vec (list_dims (QState_vars qs)@list_dims sep_vars)
                  (lin_set (QState_vars qs)) (lin_sets (top_lin_set ((QState_vars qs))) sep_vars)
                  ( QState_vector qs) v" *)

(* definition dispose_vars:: " 'q::linorder set \<Rightarrow> ('q, complex) QState \<Rightarrow> complex vec set"
  where "dispose_vars sep_vars qs \<equiv> 
   let vars_dom = QState_vars qs in
   let v =   QState_vector qs in
   let qv = (sorted_list_of_set vars_dom) in
   let t = sorted_list_of_set sep_vars in
   let l =  sorted_list_of_set (vars_dom - sep_vars) in
   let qv' = t @ l in
   let qn =  v.\<^sub>qv \<^sub>\<leadsto> \<^sub>qv' in 
   let vars_dom' = vars_dom \<union> sep_vars in
    {q. (\<exists>q2. qn = partial_state.tensor_vec (list_dims vars_dom) {0..<card sep_vars} q q2)}" *)

(* definition measure_vars::"nat \<Rightarrow>  nat set \<Rightarrow> (complex) QState  \<Rightarrow> (real\<times>complex vec)"
  where "measure_vars k  sep_vars qs \<equiv>
   let vars_dom = QState_vars qs in
    let v =   QState_vector qs in
    let vars= (vars_dom - sep_vars) in
    let l = (sorted_list_of_set sep_vars) in
    let t = (sorted_list_of_set vars) in
    let qv = (sorted_list_of_set vars_dom) in
    let qv' = l @ t in 
    let qn = v.\<^sub>qv \<^sub>\<leadsto> \<^sub>qv'  in
    let mk = partial_state2.ptensor_mat  vars_dom vars (1\<^sub>k (2^(length l))) (1\<^sub>m (2^(length t))) in
    let qn' =  mk  *\<^sub>v v in 
    let \<delta>k =  Re (((mat_adjoint (mat_of_rows (dim_vec v) [v]) *\<^sub>v qn') $ 0) div vec_norm qn') in    
    let qnprod = ((sqrt \<delta>k)::complex) \<cdot>\<^sub>v qn' in
       (\<delta>k, qnprod.\<^sub>qv' \<^sub>\<leadsto> \<^sub>qv)" *)

definition measure_vars::"nat \<Rightarrow>  nat set \<Rightarrow> (complex) QState  \<Rightarrow> (real\<times>complex vec)"
  where "measure_vars k  sep_vars qs \<equiv>
   let vars_dom = QState_vars qs in
    let v =   QState_vector qs in
    let vars= (vars_dom - sep_vars) in    
    let mk = partial_state2.ptensor_mat  vars_dom vars (1\<^sub>k (2^(card vars_dom))) (1\<^sub>m (2^(card vars))) in
    let qn' =  mk  *\<^sub>v v in 
    let \<delta>k =  Re (((mat_adjoint (mat_of_rows (dim_vec v) [v]) *\<^sub>v qn') $ 0) div vec_norm qn') in    
    let qnprod = ((sqrt \<delta>k)::complex) \<cdot>\<^sub>v qn' in
       (\<delta>k, qnprod)" 

context vars
begin

inductive QStep::"('v,'b,'s) QConf \<Rightarrow> ('v,'b,'s) QConf \<Rightarrow> bool" 
  ("\<turnstile> _ \<rightarrow> _" [81,81] 80)  
  where 
  Skip : "\<turnstile> (Skip, Normal \<sigma>) \<rightarrow> (Skip, Normal \<sigma>)" 
\<comment>\<open>SMod  modifies the stack of non-qubits variables \<sigma> with f \<sigma>, where f is a 
  function modifying the stack\<close>
 | StackMod: "\<turnstile> (SMod f, Normal (\<delta>,\<sigma>,\<Q>)) \<rightarrow> (Skip, Normal (\<delta>,f \<sigma>,\<Q>))"

\<comment>\<open>QMod modifies the set of qubits of the Quantum State given by q \<sigma> with the 
  transformation matrix M, any qubit not included in q \<sigma> remains the same\<close>

 | QMod:"(q \<sigma>)\<noteq>{} \<Longrightarrow> (q \<sigma>) \<subseteq> (QState_vars \<qq>) \<Longrightarrow> 
         \<qq>' = matrix_sep (q \<sigma>) \<qq> m \<Longrightarrow>
         \<turnstile> (QMod M q, Normal (\<delta>,\<sigma>,(\<vv>,\<qq>))) \<rightarrow> (Skip, Normal (\<delta>, \<sigma>,(\<vv>,QState(QState_vars \<qq>, list_of_vec  \<qq>'))))"

\<comment>\<open>QMod fails if the set of qubits to be modified is not included in the quantum state\<close>
 | QMod_F:"\<not> ((q \<sigma>) \<subseteq> (QState_vars \<qq>)) \<Longrightarrow>          
          \<turnstile> (QMod M q, Normal (\<delta>,\<sigma>,(\<vv>,\<qq>))) \<rightarrow> (Skip, Fault)"

\<comment>\<open>Alloc takes a normal variable "q" representing the variable where the index to the qubits is store
   an function e from the state \<sigma> to a natural number representing the number of qubits to allocate
  and an initialization value for the allocated qubits 


  We will require that a program is well formed, meaning that the types are correct.
  A call to Alloc is well formed if the ty"'s state"pe of q is a natural number\<close>

 | Alloc:"q' \<notin> (dom_q_vars \<vv>) \<Longrightarrow> q'_addr \<in> new_q_addr (e \<sigma>) \<vv> \<Longrightarrow>
          \<vv>' = \<vv>(q' := q'_addr)  \<Longrightarrow> length (v \<sigma>) = (e \<sigma>) \<Longrightarrow> \<sigma>' = set_value \<sigma> q (nat_to_typ q') \<Longrightarrow>                    
          \<turnstile> (Alloc q e v, Normal (\<delta>,\<sigma>,(\<vv>,\<qq>))) \<rightarrow> (Skip, Normal (\<delta>, \<sigma>',(\<vv>',\<qq> + QState (q'_addr,(v \<sigma>)) )))"

\<comment>\<open>Alloc will fail if the length of the initial value is not equal to the number of qubits allocated \<close>


 | Alloc_F:"length (v \<sigma>) \<noteq> (e \<sigma>) \<Longrightarrow>                    
          \<turnstile> (Alloc q e v, Normal (\<delta>,\<sigma>,(\<vv>,\<qq>))) \<rightarrow> (Skip, Fault)"

\<comment>\<open>the conditional, while, and seq statements follow the standard definitions\<close>

 | CondTrue:"\<sigma>\<in>b  \<Longrightarrow> \<turnstile> (IF b c1 c2, Normal (\<delta>,\<sigma>,\<Q>)) \<rightarrow> (c1, Normal (\<delta>,\<sigma>,\<Q>))"

 | CondFalse:"\<sigma>\<notin>b  \<Longrightarrow> \<turnstile> (IF b c1 c2, Normal (\<delta>,\<sigma>,\<Q>)) \<rightarrow> (c2, Normal (\<delta>,\<sigma>,\<Q>))"

 | WhileTrue: "\<sigma>\<in>b \<Longrightarrow> 
                \<turnstile> (While b c,Normal (\<delta>,\<sigma>,\<Q>)) \<rightarrow> (Seq c (While b c), Normal (\<delta>,\<sigma>,\<Q>))"

 | WhileFalse: "\<sigma>\<notin>b \<Longrightarrow> 
                 \<turnstile> (While b c, Normal (\<delta>,\<sigma>,\<Q>)) \<rightarrow> (Skip, Normal (\<delta>,\<sigma>,\<Q>))"

 | Seq:"\<lbrakk>\<turnstile> (C1, \<sigma>) \<rightarrow> (C1', \<sigma>')\<rbrakk> \<Longrightarrow> \<turnstile> (Seq C1 C2, \<sigma>) \<rightarrow> (C1'C2, \<sigma>')"

| SeqSkip: "\<turnstile> (Seq Skip C2,\<sigma>) \<rightarrow> (C2, \<sigma>)"

\<comment>\<open>Dispose takes an expression from the stack to a natural number and removes those qubits
  from the quantum state if they are not entangled with the rest of qubits in the current
  Quantum state. The entanglement condition is that it is possible to find a vector \<qq>1 such that
  \<qq> =  \<qq>' +  \<qq>''\<close>

 | Dispose: "\<vv> (q \<sigma>) \<noteq> {} \<Longrightarrow> \<vv>' = \<vv>((q \<sigma>):={}) \<Longrightarrow> \<qq>' ## \<qq>''  \<Longrightarrow> 
            \<vv> (q \<sigma>) = QState_vars \<qq>'' \<Longrightarrow> \<qq> =   \<qq>' +  \<qq>'' \<Longrightarrow>            
             \<turnstile> (Dispose q, Normal (\<delta>,\<sigma>,(\<vv>,\<qq>))) \<rightarrow> (Skip,Normal (\<delta>,\<sigma>,(\<vv>',\<qq>')))"

\<comment>\<open>Dispose dispose will fail if it is not possible to find such states \<qq>',  \<qq>''\<close>


 | Dispose_F: "\<nexists>\<qq>' \<qq>''. \<vv> (q \<sigma>) \<noteq> {} \<and> \<vv> (q \<sigma>) = QState_vars \<qq>'' \<and> 
               \<qq> =   \<qq>' +  \<qq>'' \<and> \<qq>' ## \<qq>'' \<Longrightarrow>
               \<turnstile> (Dispose q, Normal (\<delta>,\<sigma>,(\<vv>,\<qq>))) \<rightarrow> (Skip,Fault)"

\<comment>\<open>Measure measures the value of the set of qubits given by q \<sigma> and it stores the result in 
  the stack variable v. Similar to allocate, we will require that the construct is well formed
 and that the type of v is a real number\<close>

 | Measure: "q \<sigma> \<subseteq> (QState_vars \<qq>) \<Longrightarrow> 
            (\<delta>k, \<qq>') = measure_vars k (q \<sigma>) \<qq> \<Longrightarrow>
            \<delta>k > 0 \<Longrightarrow> \<delta>' = \<delta> * \<delta>k \<Longrightarrow> 
            \<turnstile> (Measure v q, Normal (\<delta>,\<sigma>,(\<vv>,\<qq>))) \<rightarrow> (Skip,Normal (\<delta>',\<sigma>,(\<vv>,QState(Q_domain \<vv>', list_of_vec  \<qq>'))))" 

\<comment>\<open>Since Measure access to the values of the qubits given by q \<sigma> as QMod, 
  Measure will similarly fail if the set of qubits to be mesured does not
  belong to the set of allocated qubits\<close>

 | Measure_F: "\<not> (q \<sigma> \<subseteq> (QState_vars \<qq>)) \<Longrightarrow>  
              \<turnstile> (Measure v q, Normal (\<delta>,\<sigma>,(\<vv>,\<qq>))) \<rightarrow> (Skip, Fault)" 

| Fault_Prop:" C\<noteq>Skip \<Longrightarrow> \<turnstile> (C, Fault) \<rightarrow> (Skip, Fault)"


lemmas step_induct = QStep.induct [of "(c,s)" "(c',s')", split_format (complete), case_names
StackMod QMod QMod_F Alloc Alloc_F CondTrue CondFalse WhileTrue WhileFalse Seq SeqSkip Dispose
Dispose Dispose_F Measure Measure_F Fault_Prop, induct set]
end 

end

