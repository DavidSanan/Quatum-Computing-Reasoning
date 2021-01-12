(* Title:     Quantum-Semantics/QSemantics.thy
   Author:    David Sanan, Nanyang Technological University 
   Copyright   2020
   License:     BSD
*)

theory QSemantics
  imports QSyntax vars "HOL-Library.Permutations" "List_Inversions.List_Inversions"
begin

subsection \<open>Syntax\<close>

text \<open>Semantics for quantum programs\<close>

lemma "(1,2) \<in> inversions [0::nat,7,3,4] \<and> (1,3)\<in>inversions [0::nat,7,3,4]"
  by (simp add: inversions.simps) 
  


context vars
begin

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
                                                             
inductive QSemantics::"'v set \<Rightarrow> ('v,'b,'s) QConf \<Rightarrow> ('v,'b,'s) QConf \<Rightarrow> bool" 
  ("_ \<turnstile> _ \<rightarrow> _" [81,81] 80) for \<Gamma>::"'v set" 
where 
\<comment>\<open>SMod  modifies the stack of non-qubits variables \<sigma> with f \<sigma>, where f is a 
  function modifying the stack\<close>
   StackMod:"\<Gamma> \<turnstile> (SMod f, Normal (\<delta>,\<sigma>,\<Q>)) \<rightarrow> (Skip, Normal (\<delta>,f \<sigma>,\<Q>))"

\<comment>\<open>QMod modifies the set of qubits of the Quantum State given by q \<sigma> with the 
  transformation matrix M, any qubit not included in q \<sigma> remains the same\<close>

| QMod:"(q \<sigma>)\<noteq>{} \<Longrightarrow> (q \<sigma>) \<subseteq> (QState_vars \<qq>) \<Longrightarrow> 
         \<qq>' = matrix_sep (q \<sigma>) \<qq> m \<Longrightarrow>
         \<Gamma> \<turnstile> (QMod M q, Normal (\<delta>,\<sigma>,(\<vv>,\<qq>))) \<rightarrow> (Skip, Normal (\<delta>, \<sigma>,(\<vv>,QState(QState_vars \<qq>, list_of_vec  \<qq>'))))"

\<comment>\<open>QMod fails if the set of qubits to be modified is not included in the quantum state\<close>
| QMod_F:"\<not> ((q \<sigma>) \<subseteq> (QState_vars \<qq>)) \<Longrightarrow>          
         \<Gamma> \<turnstile> (QMod M q, Normal (\<delta>,\<sigma>,(\<vv>,\<qq>))) \<rightarrow> (Skip, Fault)"

\<comment>\<open>Alloc takes a normal variable "q" representing the variable where the index to the qubits is store
   an function e from the state \<sigma> to a natural number representing the number of qubits to allocate
  and an initialization value for the allocated qubits 


  We will require that a program is well formed, meaning that the types are correct.
  A call to Alloc is well formed if the type of q is a natural number\<close>

| Alloc:"q' \<notin> (dom_q_vars \<vv>) \<Longrightarrow> q'_addr \<in> new_q_addr (e \<sigma>) \<vv> \<Longrightarrow>
          \<vv>' = \<vv>(q' := q'_addr)  \<Longrightarrow> length (v \<sigma>) = (e \<sigma>) \<Longrightarrow> \<sigma>' = set_value \<sigma> q (nat_to_typ q') \<Longrightarrow>                    
          \<Gamma> \<turnstile> (Alloc q e v, Normal (\<delta>,\<sigma>,(\<vv>,\<qq>))) \<rightarrow> (Skip, Normal (\<delta>, \<sigma>',(\<vv>',\<qq> + QState (q'_addr,(v \<sigma>)) )))"

\<comment>\<open>Alloc will fail if the length of the initial value is not equal to the number of qubits allocated \<close>


 | Alloc_F:"length (v \<sigma>) \<noteq> (e \<sigma>) \<Longrightarrow>                    
          \<Gamma> \<turnstile> (Alloc q e v, Normal (\<delta>,\<sigma>,(\<vv>,\<qq>))) \<rightarrow> (Skip, Fault)"

\<comment>\<open>the conditional, while, and seq statements follow the standard definitions\<close>

| CondTrueQ:"\<sigma>\<in>b  \<Longrightarrow> \<Gamma> \<turnstile> (IF b c1 c2, Normal (\<delta>,\<sigma>,\<Q>)) \<rightarrow> (c1, Normal (\<delta>,\<sigma>,\<Q>))"

 | CondFalseQ:"\<sigma>\<notin>b  \<Longrightarrow> \<Gamma> \<turnstile> (IF b c1 c2, Normal (\<delta>,\<sigma>,\<Q>)) \<rightarrow> (c2, Normal (\<delta>,\<sigma>,\<Q>))"

 | WhileTruec: "s\<in>b \<Longrightarrow> 
                \<Gamma>\<turnstile> (While b c,Normal (\<delta>,\<sigma>,\<Q>)) \<rightarrow> (Seq c (While b c), Normal (\<delta>,\<sigma>,\<Q>))"

 | WhileFalsec: "s\<notin>b \<Longrightarrow> 
                 \<Gamma>\<turnstile> (While b c, Normal (\<delta>,\<sigma>,\<Q>)) \<rightarrow> (Skip, Normal (\<delta>,\<sigma>,\<Q>))"

| Seqc:"\<lbrakk>\<Gamma> \<turnstile> (C1, \<sigma>) \<rightarrow> (C1', \<sigma>')\<rbrakk> \<Longrightarrow> \<Gamma> \<turnstile> (C1;C2, \<sigma>) \<rightarrow> (C1'C2, \<sigma>')"

| SeqSkipc: "\<Gamma>\<turnstile> (Skip;C2,\<sigma>) \<rightarrow> (C2, \<sigma>)"

\<comment>\<open>Dispose takes an expression from the stack to a natural number and removes those qubits
  from the quantum state if they are not entangled with the rest of qubits in the current
  Quantum state. The entanglement condition is that it is possible to find a vector \<qq>1 such that
  \<qq> =  \<qq>' +  \<qq>''\<close>

| Dispose: "\<vv> (q \<sigma>) \<noteq> {} \<Longrightarrow> \<vv>' = \<vv>((q \<sigma>):={}) \<Longrightarrow> \<qq>' ## \<qq>''  \<Longrightarrow> 
            \<vv> (q \<sigma>) = QState_vars \<qq>'' \<Longrightarrow> \<qq> =   \<qq>' +  \<qq>'' \<Longrightarrow>            
             \<Gamma> \<turnstile> (Dispose q, Normal (\<delta>,\<sigma>,(\<vv>,\<qq>))) \<rightarrow> (Skip,Normal (\<delta>,\<sigma>,(\<vv>',\<qq>')))"

\<comment>\<open>Dispose dispose will fail if it is not possible to find such states \<qq>',  \<qq>''\<close>


| Dispose_F: "\<nexists>\<qq>' \<qq>''. \<vv> (q \<sigma>) \<noteq> {} \<and> \<vv> (q \<sigma>) = QState_vars \<qq>'' \<and> 
               \<qq> =   \<qq>' +  \<qq>'' \<and> \<qq>' ## \<qq>'' \<Longrightarrow>
               \<Gamma> \<turnstile> (Dispose q, Normal (\<delta>,\<sigma>,(\<vv>,\<qq>))) \<rightarrow> (Skip,Fault)"

\<comment>\<open>Measure measures the value of the set of qubits given by q \<sigma> and it stores the result in 
  the stack variable v. Similar to allocate, we will require that the construct is well formed
 and that the type of v is a real number\<close>

| Measure: "q \<sigma> \<subseteq> (QState_vars \<qq>) \<Longrightarrow> 
            (\<delta>k, \<qq>') = measure_vars k (q \<sigma>) \<qq> \<Longrightarrow>
            \<delta>k > 0 \<Longrightarrow> \<delta>' = \<delta> * \<delta>k \<Longrightarrow> 
            \<Gamma> \<turnstile> (Measure v q, Normal (\<delta>,\<sigma>,(\<vv>,\<qq>))) \<rightarrow> (Skip,Normal (\<delta>',\<sigma>,(\<vv>,QState(Q_domain \<vv>', list_of_vec  \<qq>'))))" 

\<comment>\<open>Since Measure access to the values of the qubits given by q \<sigma> as QMod, 
  Measure will similarly fail if the set of qubits to be mesured does not
  belong to the set of allocated qubits\<close>

| Measure_F: "\<not> (q \<sigma> \<subseteq> (QState_vars \<qq>)) \<Longrightarrow>  
            \<Gamma> \<turnstile> (Measure v q, Normal (\<delta>,\<sigma>,(\<vv>,\<qq>))) \<rightarrow> (Skip, Fault)" 


(* | Dispose: "\<vv> (q \<sigma>) \<noteq> {} \<Longrightarrow> \<vv>' = \<vv>((q \<sigma>):={}) \<Longrightarrow> \<qq>1 ## \<qq>2  \<Longrightarrow> 
            \<vv> (q \<sigma>) = QState_vars \<qq>2 \<Longrightarrow> \<qq> =   \<qq>1 +  \<qq>2 \<Longrightarrow>
            \<qq>' \<in> dispose_vars (\<vv> (q \<sigma>)) \<qq> \<Longrightarrow>
             \<Gamma> \<turnstile> (Dispose q, (\<delta>,\<sigma>,(\<vv>,\<qq>))) \<rightarrow> (Skip,(\<delta>,\<sigma>,(\<vv>',QState(Q_domain \<vv>', list_of_vec  \<qq>'))))" *)

end

end

